// int __CPROVER_assert(int a, char *b) {if(a == 0){__VERIFIER_error();}}
int __CPROVER_assert(int a, char *b) {}
int __CPROVER_assume(int a) {}
// int __CPROVER_assume(int a) {if(a == 0){exit();}}
int __QICC_assert(int a, char *b) {}

#define MAXSUM 40
#define MINSUM 10
int main() {
    int i; //nondet
    __CPROVER_assume(i >= 0);
    for (; i < MAXSUM - MINSUM; i++)
    {
        int nm, sum, k;
        __CPROVER_assume(1 <= nm && nm <= i + MINSUM);
        sum = 0;
        for(k = 1; k <= nm; k++) {
            sum = sum + k;
        }  
        __CPROVER_assert(2*sum == nm*(nm+1), "postcondition");
    }
}