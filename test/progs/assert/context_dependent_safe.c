int __CPROVER_assert(int a, char *b) {}
int __CPROVER_assume(int a ){}

int main(){
    int n;
    client(n);
}

int client(int n){
    int i = 0;
    int sum = 0;
    while (i<=n){
        if (lib(i) == 0){
            sum +=i;
        }
        i++;
    }
    return sum;
}

int lib(int a){
    int i = 2;
    int count = 0;
    while (i < a){
        __CPROVER_assert(a  >= 0, "postcondition");
        if ((a % i ) != 0){
            count = 1;
        }
        i++;
    }
    return count;
}