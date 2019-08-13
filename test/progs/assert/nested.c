int __CPROVER_assert(int a, char *b) {}
int assume(int a ){}


int main()
{

    int x = 1;
    int z = 9;

    while (x < 10)
    {
        int y = 2;
        __CPROVER_assert(x > 0, "postcondition");
        x++;
    }

    while (z < 7)
    {
        __CPROVER_assert(z > 0, "postcondition");
        z++;

        while (x < 4)
        {
            int y = 2;
            __CPROVER_assert(y > 0, "postcondition");
            x++;
        }
    }

    return 0;
}