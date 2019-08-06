'use-strict';
import util = require('util');
import { strict } from 'assert';
import { access } from 'fs';
import { ADDRGETNETWORKPARAMS } from 'dns';
const exec_glob = util.promisify(require('child_process').exec);

const WORKDIR: string = "_____WORKDIR"

const exec_wd = (cmd: string) => exec_glob(cmd, { cwd: `./${WORKDIR}` })


const createWorkdir = async () => exec_glob(`mkdir ${WORKDIR}`)
const cleanUp = async () => {
    try {
        await exec_glob(`rm -rf ${WORKDIR}`)
    } catch{ }
}

interface ProgramAttributes {
    allFuns: string[]
    parents: FunctionMappings
    assertFuns: string[]
}


const extractMLC = async (filename: string): Promise<ProgramAttributes> => {
    const { stdout, stderr } = await exec_wd(`cilly --gcc=/usr/bin/gcc-6 --save-temps --load=../_build/src/extractMLC.cmxs  ../${filename}`)
    await exec_wd(`cat ${filename.slice(0, -1)}cil.c | grep -v '^#line' >| output.c`)
    return {
        assertFuns: await getAssertFuns(),
        allFuns: await getAllFuns(),
        parents: await getParents()
    }
}

type FunctionMappings = Record<string, string>

const getAssertFuns = async (): Promise<string[]> => {
    const { stdout, stderr } = await exec_wd(`export FIND_COMMAND=GET_ASSERT_FUNCS && cilly --gcc=/usr/bin/gcc-6 --save-temps --load=../_build/src/findFuncs.cmxs  ./output.c`)
    return stdout.split("\n").filter((str: string) => str !== '');
}

const getAllFuns = async (): Promise<string[]> => {
    const { stdout, stderr } = await exec_wd(`export FIND_COMMAND=GET_ALL_FUNCS && cilly --gcc=/usr/bin/gcc-6 --save-temps --load=../_build/src/findFuncs.cmxs  ./output.c`)
    return stdout.split("\n").filter((str: string) => str !== '');
}

const getParents = async (): Promise<FunctionMappings> => {
    const { stdout, stderr } = await exec_wd(`export FIND_COMMAND=GET_PARENTS && cilly --gcc=/usr/bin/gcc-6 --save-temps --load=../_build/src/findFuncs.cmxs  ./output.c`)
    return stdout
        .split("\n")
        .filter((str: string) => str.startsWith("!!CHILDOF"))
        .map((str: string) => str.split(" "))
        .map((arr: string[]) => ({ [arr[1]]: arr[2] }))
        .reduce((acc: FunctionMappings, curr: FunctionMappings) => ({ ...acc, ...curr }))
}



// const parseExtractMLC = (stdout: string): FunctionMappings => {
//     return stdout
//         .split("\n")
//         .filter((str: string) => str.startsWith("!!CHILDOF"))
//         .map((str: string) => str.split(" "))
//         .map((arr: string[]) => ({ [arr[1]]: arr[2] }))
//         .reduce((acc: FunctionMappings, curr: FunctionMappings) => ({ ...acc, ...curr }))
// }


enum ProofStatus {
    success,
    fail,
    unattempted
}

interface LatticeNode {
    function: string
    proofLocal: ProofStatus
    proofActual: ProofStatus
    provenParent: LatticeNode | null
}


type Status = Record<string, LatticeNode>

interface Result {
    provedAt: string | null
    isTrue: boolean
}

const verify = async (atts: ProgramAttributes) => {
    let status: Status = atts.allFuns
        .map((fun: string) => ({
            [fun]: {
                function: fun,
                proofLocal: ProofStatus.unattempted,
                proofActual: ProofStatus.unattempted,
                provenParent: null
            }
        } as Status))
        .reduce((acc: Status, curr: Status) => ({ ...acc, ...curr }), {})

    const prove = async (fun: LatticeNode, previous: LatticeNode | null): Promise<void> => {
        switch (fun.proofActual) {
            case ProofStatus.unattempted: {
                try {
                    await exec_wd(`cbmc output.c --unwind 200 --function ${fun.function}`)
                    fun.proofActual = ProofStatus.success
                    fun.proofLocal = ProofStatus.success
                    fun.provenParent = fun
                } catch {
                    fun.proofLocal = ProofStatus.fail
                    if (atts.parents[fun.function]) await prove(status[atts.parents[fun.function]], fun)
                    else {
                        fun.proofLocal = ProofStatus.fail
                    }
                }
                // fall through 
            }
            case ProofStatus.success:
            case ProofStatus.fail: {
                if(previous) {
                    previous.provenParent = fun.provenParent
                    previous.proofActual = fun.proofActual
                }
            }
        }
    }

    //have to use imperitive for loop to enforce no concurrnecy
    //may be performed concurrently only when sub-CFGs do not overlap
    for (let fun of atts.assertFuns){
        await prove(status[fun], null)
    }
    


    return atts.assertFuns.map((fun: string) => ({
        [fun]: {
            isTrue: status[fun].proofActual === ProofStatus.success,
            provedAt: status[fun].provenParent ? status[fun].provenParent!.function : null
        } as Result
    }));
}

module.exports = {
    createWorkdir,
    cleanUp,
    extractMLC,
    verify
}