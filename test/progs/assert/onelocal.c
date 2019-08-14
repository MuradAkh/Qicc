int __CPROVER_assert(int a, char *b) {}
int __CPROVER_assume(int a ){}


int main()
{
    
    int x = 1;

    while(x < 10){
        int y = 2;
        __CPROVER_assert(y > 0, "postcondition");
        x++;

    }


    return 0;
}
