const fs = require('fs');
const {performance} = require('perf_hooks');
const util = require('util');
const exec = util.promisify(require('child_process').exec);

const cases = fs.readFileSync('./test/v2/cases.txt', 'utf-8').split('\n');
const benchmarks = fs.readFileSync('./test/v2/benchmarks.txt', 'utf-8').split('\n');
const benchmark = process.argv[2]
const timeout = 1000 * process.argv[3]

parseCli = (stdout) => {
    const json = stdout.match(/\[[\s\S]*\]/g)[0].replace('\\', '');
    return JSON.parse(json)
}


async function evaluate() {
    const log = []
    
    for (const casepath of cases) {
        const t0 = performance.now()
        const qicc = false;
        
        // const qicc = await exec(`node cli/cli.js --ua --file ${casepath}/${benchmark}.gen.c`, {timeout})
        //     .then(r => r.stdout)
        //     .then(parseCli)
        //     .then(r => {
        //         console.log(r)
        //         return r.reduce((acc, curr) => curr.isTrue && acc, true)
        //     })
        //     .catch(err => {
        //         console.log(err)
        //         return false
        //     })

        const t1 = performance.now()
        const pwd = await exec(`pwd`)
            .then(r => r.stdout.trim())
            .catch(err => console.log(err))

        const cbmc = await exec(`cd ~/uauto && ./Ultimate.py --spec ~/uauto/PropertyUnreachCall.prp --architecture 64bit --file ${pwd}/${casepath}/${benchmark}.ua.gen.c`, {timeout})
            .then((res) => true)
            .catch((err) => {
                console.log(err);
                return false;
            })


        const t2 = performance.now()

        const casename = casepath.replace("./test/v2/target/", "")
        const qicctime = qicc ? t1 - t0 : "f"
        const cbmctime = cbmc ? t2 - t1 : "f"
        console.log(`${casename}: ${qicctime}, ${cbmctime}`)
        log.push(`${casename}: ${qicctime}, ${cbmctime}`)
        await exec("killall -9 java").catch(() => {});
        
    }

    return log;
    
}

evaluate()
    .then(l => fs.writeFileSync(`./results/${benchmark}.result`, l.join("\n")))
    .catch(console.log)