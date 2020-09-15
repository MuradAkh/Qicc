'use-strict';
const util = require('util');
import Mutex from './mutex'

const exec_glob = util.promisify(require('child_process').exec);

const WORKDIR: string = "_____WORKDIR"

const exec_wd = (cmd: string) => exec_glob(`cd ${WORKDIR} && ${cmd}`)


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
    funcLocations: FunctionMappings
}


const extractMLC = async (filepath: string): Promise<ProgramAttributes> => {
    const filename = filepath.split('/').pop()!
    const { stdout, stderr } = await exec_wd(`cilly --gcc=/usr/bin/gcc-6 --save-temps --load=../_build/src/findLoops.cmxs --load=../_build/src/tututil.cmxs --load=../_build/src/extractMLC.cmxs ../${filepath}`)
    await exec_wd(`cat ${filename.slice(0, -1)}cil.c | grep -v '^#line' >| output.c`)
    await exec_wd(`cat ${filename.slice(0, -1)}i | grep -v '^#line' >| original.c`)
    return {
        assertFuns: await getAssertFuns(),
        allFuns: await getAllFuns(),
        parents: await getParents(),
        funcLocations: getLocs(stdout)
    }
}

type FunctionMappings = Record<string, string>

const getAssertFuns = async (): Promise<string[]> => {
    const { stdout } = await exec_wd(`export FIND_COMMAND=GET_ASSERT_FUNCS && cilly --gcc=/usr/bin/gcc-6 --load=../_build/src/tututil.cmxs --load=../_build/src/findFuncs.cmxs  ./output.c`)
    return stdout.split("\n").filter((str: string) => str !== '');
}

const getAllFuns = async (): Promise<string[]> => {
    const { stdout } = await exec_wd(`export FIND_COMMAND=GET_ALL_FUNCS && cilly --gcc=/usr/bin/gcc-6 --load=../_build/src/tututil.cmxs --load=../_build/src/findFuncs.cmxs  ./output.c`)
    return stdout.split("\n").filter((str: string) => str !== '');
}

const getParents = async (): Promise<FunctionMappings> => {
    const { stdout } = await exec_wd(`export FIND_COMMAND=GET_PARENTS && cilly --gcc=/usr/bin/gcc-6  --load=../_build/src/tututil.cmxs --load=../_build/src/findFuncs.cmxs  ./output.c`)
    return stdout
        .split("\n")
        .filter((str: string) => str.startsWith("!!CHILDOF"))
        .map((str: string) => str.split(" "))
        .map((arr: string[]) => ({ [arr[1]]: arr[2] }))
        .reduce((acc: FunctionMappings, curr: FunctionMappings) => ({ ...acc, ...curr }), {})
}

const getLocs = (stdout: string): FunctionMappings => {
    return stdout
        .split("\n")
        .filter((str: string) => str.startsWith("!!FUNCLOC"))
        .map((str: string) => str.split(" "))
        .map((arr: string[]) => ({ [arr[1]]: arr[2] }))
        .reduce((acc: FunctionMappings, curr: FunctionMappings) => ({ ...acc, ...curr }), {})
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
    mutex: Mutex
    provenParent: LatticeNode | null
}


type Status = Record<string, LatticeNode>

interface Result {
    loc: string
    provedAt: string | null
    isTrue: boolean
    // solveTime: number
}

const verify = async (atts: ProgramAttributes) => {
    let status: Status = atts.allFuns
        .map((fun: string) => ({
            [fun]: {
                function: fun,
                proofLocal: ProofStatus.unattempted,
                proofActual: ProofStatus.unattempted,
                provenParent: null,
                mutex: new Mutex()
            } as LatticeNode
        } as Status))
        .reduce((acc: Status, curr: Status) => ({ ...acc, ...curr }), {})

    const prove = async (fun: LatticeNode, previous: LatticeNode | null): Promise<void> => {
        await fun.mutex.lock()
        switch (fun.proofActual) {
            case ProofStatus.unattempted: {
                try {
                    const targetfile =  fun.function === "main" ? "original.c" : "output.c"
                    console.log(fun.function)
                    await exec_wd(`cbmc ${targetfile} --unwinding-assertions --unwind 201 --function ${fun.function} > /dev/null`)
                    fun.proofActual = ProofStatus.success
                    fun.proofLocal = ProofStatus.success
                    fun.provenParent = fun
                } catch(e) {
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
                if (previous) {
                    previous.provenParent = fun.provenParent
                    previous.proofActual = fun.proofActual
                }
            }
        }
        fun.mutex.release()
    }

    await Promise.all(atts.assertFuns.map((fun: string) => prove(status[fun], null)))


    return atts.assertFuns.map((fun: string) => {
        const getLOC = (fun: string) => {
            return  atts.funcLocations[fun] ? atts.funcLocations[fun] : fun
        }


        return {
                loc: getLOC(fun),
                isTrue: status[fun].proofActual === ProofStatus.success,
                provedAt: status[fun].provenParent ? getLOC(status[fun].provenParent!.function) : null,
                // solveTime: 0
            } as Result
    
    });
}

module.exports = {
    createWorkdir,
    cleanUp,
    extractMLC,
    verify
}