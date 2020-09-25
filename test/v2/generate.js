const fs = require('fs');

const BASE_KOWLEDGE = "int x = 0;"
const BASE_ASSERT = "__CPROVER_assert(x == 0, \"postcondition\");"
const BASE_ASSERT_DEF = "int __CPROVER_assert(int a, char *b) {}"
const BASE_ASSUME_DEF = "int __CPROVER_assume(int a ){}"
const BASE_ASSERT_DEF_UA = "int __CPROVER_assert(int a, char *b) { if(a == 0){__VERIFIER_error();} }"
const BASE_ASSUME_DEF_UA = "int __CPROVER_assume(int a) { if(a == 0){exit();} }"

const filename = process.argv[2]
const knowledge = fs.readFileSync(`./test/v2/benchmarks/${filename}.knowledge`, 'utf-8');
const assert = fs.readFileSync(`./test/v2/benchmarks/${filename}.assert`, 'utf-8');

const cases = fs.readFileSync('./test/v2/cases.txt', 'utf-8').split('\n');

for(const casepath of cases){
    const file = fs.readFileSync(`${casepath}/baseline.c`, 'utf-8');
    const rfile = file.replace(BASE_KOWLEDGE, knowledge).replace(BASE_ASSERT, assert);
    fs.writeFileSync(`${casepath}/${filename}.gen.c`, rfile);
    fs.writeFileSync(`${casepath}/${filename}.ua.gen.c`, 
        rfile.replace(BASE_ASSERT_DEF, BASE_ASSERT_DEF_UA)
        .replace(BASE_ASSUME_DEF, BASE_ASSUME_DEF_UA)
    );
}
