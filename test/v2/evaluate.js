const fs = require('fs');
const {performance} = require('perf_hooks');
const util = require('util');
const exec = util.promisify(require('child_process').exec);

const cases = fs.readFileSync('./test/v2/cases.txt', 'utf-8').split('\n');
const benchmarks = fs.readFileSync('./test/v2/benchmarks.txt', 'utf-8').split('\n');

async function evaluate() {
    for (const benchmark of benchmarks) {
        for (const casepath of cases) {
            const t0 = performance.now()
            const qicc = await exec(`node cli/cli.js --file ${casepath}/${benchmark}.gen.c`);
            const t1 = performance.now()
            const cbmc = await exec(`cbmc --unwind 201 --unwinding-assertions ${casepath}/${benchmark}.gen.c > /dev/null`);
            const t2 = performance.now()
            const qicctime = t1 - t0
            const cbmctime = t2 - t1
            console.log(`${qicctime}, ${cbmctime}`)
            
        }
    }
}

evaluate()