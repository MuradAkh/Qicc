int __CPROVER_assert(int a, char *b) {}
int __CPROVER_assume(int a ){}


int main(){
    int x;
    client(x);
}

int client(int x) {
	if (x>=18 && x<22){
		int a = x;
		int b = 20;
		int c=0;
        for (int i=1;i<=a;++i){
            c+=b;
            __CPROVER_assert( (c == i * b), "postcondition");
        }

        return c;
		}
	else
	    return 0;
}

int lib(int a, int b) {
	int c=0;
	for (int i=1;i<=a;++i){
		c+=b;
		__CPROVER_assert( (c == i * b), "postcondition");
	}

	return c;
}
