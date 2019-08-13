int __CPROVER_assert(int a, char *b) {}


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

    //relevant context
    int j = 0;
    int sum_alt = 0;
    while (j > 0 && j < 100){
        j ++;
        __CPROVER_assert(j < 0, "postcondition");
    }
    //relevant context

    return sum_alt;
}

int lib(int a){
    int i = 2;
    int count = 0;
    while (i < a){
        if ((a % i ) != 0){
            count = 1;
        }
        i++;
    }
    return count;
}