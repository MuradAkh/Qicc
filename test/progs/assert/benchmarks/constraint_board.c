int __CPROVER_assert(int a, char *b) {}
int __CPROVER_assume(int a ){}

int main(){
    int n;
    client(n);
}

int client(int n){
       while (n < 0){
            n--;
       }

   while ( n >= 1 & n < 100){
        int sum = 0;
        int k = 0;
        while ( k >= 0 & k < 100){
            sum += k;
            k += n;
            __CPROVER_assert( sum  >= 0 & k == 0 | n > 0, "postcondition");
        }
        n = 2 * n;
   }

    return 0;
}
