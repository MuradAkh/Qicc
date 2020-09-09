const fs = require('fs');
const {performance} = require('perf_hooks');
const util = require('util');
const exec = util.promisify(require('child_process').exec);

const BASE_KOWLEDGE = "int x = 0;"
const BASE_ASSERT = "__CPROVER_assert(x == 0, \"postcondition\");"

const filename = process.argv[2]
const knowledge = fs.readFileSync(`./test/v2/benchmarks/${filename}.knowledge`, 'utf-8');
const assert = fs.readFileSync(`./test/v2/benchmarks/${filename}.assert`, 'utf-8');

const cases = fs.readFileSync('./test/v2/cases.txt', 'utf-8').split('\n');

for(const casepath of cases){
    const file = fs.readFileSync(`${casepath}/baseline.c`, 'utf-8');
    fs.writeFileSync(`${casepath}/${filename}.gen.c`, file.replace(BASE_KOWLEDGE, knowledge).replace(BASE_ASSERT, assert));
}
