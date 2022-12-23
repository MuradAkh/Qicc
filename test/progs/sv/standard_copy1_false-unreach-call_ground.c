int __CPROVER_assert(int a, char *b) {if(a == 0){__VERIFIER_error();}}
// int __CPROVER_assert(int a, char *b) {}
// int __CPROVER_assume(int a) {}
int __CPROVER_assume(int a) {if(a == 0){exit();}}
int __QICC_assert(int a, char *b) {}

#define N 5
float pi = 3.14159 ;
int main() {
  int i,pvlen ;
  int tmp___1 ;
  int k = 0;
  int n;

  i = 0;
  pvlen = __VERIFIER_nondet_int();

  //  pkt = pktq->tqh_first;
  while ( __VERIFIER_nondet_int() && i <= 100) {
    i = i + 1;
  }


  if (i > pvlen) {
    pvlen = i;
  }
  i = 0;

  while ( __VERIFIER_nondet_int() && i <= 100) {
    tmp___1 = i;
    i = i + 1;
    k = k + 1;
  }

  int j = 0;
  n = i;
  while (1) {

    __CPROVER_assert(k >= 0, "");
    k = k -1;
    i = i - 1;
    j = j + 1;
    if (j >= n) {
      break;
    }
  }
  return 0;
  
  
}
       


 

