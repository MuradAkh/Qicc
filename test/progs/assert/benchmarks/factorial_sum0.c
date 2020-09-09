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

    int i = 0;
    int sum = 0;
    while (i<=n & i < 100){
        int j = 2;
        int count =0;
        while (j < i){
            if ((i % j ) != 0){
                count += j;
            }
            __CPROVER_assert(count >= 0, "postcondition");
            j++;
        }
        sum += count;
        i++;
    }

    return sum;
}
