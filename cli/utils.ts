'use-strict';
const util = require('util');
import Mutex from './mutex'
import { readFileSync, writeFileSync, fstat } from 'fs';

const exec_glob = util.promisify(require('child_process').exec);

const WORKDIR: string = "_____WORKDIR"
const QICC_ASSERT_DEF = /int \_\_QICC_assert\(int ?a ?, ?char ?\*b ?\) ?(\n)? ?\{/g
const QICC_ASSERT_DEF_AFTER = "int __QICC_assert(int a , char *b ) { __CPROVER_assert(a, \"postcondition\");"
const BASE_ASSERT_DEF = /int __CPROVER_assert\(int a ?, ?char \*b ?\) ?(\n)? ?{/g
const BASE_ASSUME_DEF = /int __CPROVER_assume\(int a ?\) ?(\n)? ?{/g
const BASE_ASSERT_DEF_UA = "int __CPROVER_assert(int a, char *b) { if(a == 0){__VERIFIER_error();} "
const BASE_ASSUME_DEF_UA = "int __CPROVER_assume(int a) { if(a == 0){exit();} "

const exec_wd = (cmd: string) => exec_glob(`cd ${WORKDIR} && ${cmd}`)


const createWorkdir = async () => await exec_glob(`mkdir ${WORKDIR}`)
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


const extractMLC = async (filepath: string, verifier: string, v2: boolean): Promise<ProgramAttributes> => {
    const filename = filepath.split('/').pop()!
    const extractor = v2 ? "copy" : "extract";
    const { stdout, stderr } = await exec_wd(`cilly --gcc=/usr/bin/gcc-6 --save-temps --load=../_build/src/findLoops.cmxs --load=../_build/src/tututil.cmxs --load=../_build/src/${extractor}MLC.cmxs ../${filepath}`)
    await exec_wd(`cat ${filename.slice(0, -1)}cil.c | grep -v '^#line' >| output.c`)
    await exec_wd(`cat ${filename.slice(0, -1)}i | grep -v '^#line' >| original.c`)
    
    const out = await (async () => {
        if(!v2) return {
            assertFuns: await getAssertFuns(),
            allFuns: await getAllFuns(),
            parents: await getParents("output"),
            funcLocations: getLocs(stdout)
        } as ProgramAttributes
        else{ 
            const cParentPairs = getCopiedParents(stdout);
            return {
                assertFuns: await getAssertFuns(),
                allFuns: await getAllFuns(),
                parents: await getParents("original").then(ps => Object.assign(ps, cParentPairs)),
                funcLocations: getLocs(stdout)
            } as ProgramAttributes
        }
    })();
    if(v2){
        writeFileSync(`${WORKDIR}/output.c`, readFileSync(`${WORKDIR}/output.c`).toString().replace(QICC_ASSERT_DEF, QICC_ASSERT_DEF_AFTER))
        writeFileSync(`${WORKDIR}/original.c`, readFileSync(`${WORKDIR}/original.c`).toString().replace(QICC_ASSERT_DEF, QICC_ASSERT_DEF_AFTER))
    }


    if(verifier === "ua"){
        writeFileSync(`${WORKDIR}/output.c`, readFileSync(`${WORKDIR}/output.c`).toString().replace(BASE_ASSUME_DEF, BASE_ASSUME_DEF_UA))
        writeFileSync(`${WORKDIR}/output.c`, readFileSync(`${WORKDIR}/output.c`).toString().replace(BASE_ASSERT_DEF, BASE_ASSERT_DEF_UA))
        writeFileSync(`${WORKDIR}/original.c`, readFileSync(`${WORKDIR}/original.c`).toString().replace(BASE_ASSUME_DEF, BASE_ASSUME_DEF_UA))
        writeFileSync(`${WORKDIR}/original.c`, readFileSync(`${WORKDIR}/original.c`).toString().replace(BASE_ASSERT_DEF, BASE_ASSERT_DEF_UA))
    }

    return out;
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

const getParents = async (file: string): Promise<FunctionMappings> => {
    const { stdout } = await exec_wd(`export FIND_COMMAND=GET_PARENTS && cilly --gcc=/usr/bin/gcc-6  --load=../_build/src/tututil.cmxs --load=../_build/src/findFuncs.cmxs  ./${file}.c`)
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

const getCopiedParents = (stdout: string): FunctionMappings => {
    return stdout
        .split("\n")
        .filter((str: string) => str.startsWith("!!CHILDOF"))
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

const verify = async (atts: ProgramAttributes, verifier : string, sync: boolean) => {
    const globlock = new Mutex();
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
                    let targetfile =  !fun.function.includes("newfun") ? "original.c" : "output.c"
                    console.log(fun.function)
                    if(verifier == "cbmc"){
                        await exec_wd(`cbmc ${targetfile} --unwinding-assertions --unwind 201 --function ${fun.function} > /dev/null`)
                    }else if(verifier == "ua"){
                        // throw Error;
                        // targetfile = "output.c"

                        const pwd = await exec_wd(`pwd`)
                            .then((r: any) => r.stdout.trim())
                            .catch((err: any) => console.log(err))
                        
                        await exec_wd(`mkdir ${fun.function}`)
                        writeFileSync(`${pwd}/${fun.function}/PropertyUnreachCall.prp`, `CHECK( init(${fun.function}()), LTL(G ! call(__VERIFIER_error())) )`);
                        const ua = await exec_glob(`cd ~/uauto && ./Ultimate.py --spec ${pwd}/${fun.function}/PropertyUnreachCall.prp --architecture 64bit --file ${pwd}/${targetfile} | grep -E -- 'TRUE|FALSE'`,)

                        console.log(fun.function + ua.stdout)
                        if(!ua.stdout.includes("TRUE")){
                            throw Error;
                        }
                    }
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
       
        fun.mutex.release();
        
    }

    if(sync){
        for (const fun of atts.assertFuns) {
            await prove(status[fun], null);
        }
    }
    else{
        await Promise.all(atts.assertFuns.map((fun: string) => prove(status[fun], null)))
    }

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
    verify,
}