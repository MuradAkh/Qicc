int __CPROVER_assert(int a, char *b) {}
int __CPROVER_assume(int a ){}

int main(){
    int n;
    fib(n);
}

int fib(int n){
    int first = 0;
    int second = 1;
    int i = 0;
    int next = 0;
    while (i < n){
        if (i <= 1){
            next = i;
        }else{
            //relevant context
            int old_first = first;
            next = first + second;
            first = second;
            second = next;
            __CPROVER_assert(second - first == old_first, "postcondition");
            //relevant context
        }
        i++;
    }

    return next;
}