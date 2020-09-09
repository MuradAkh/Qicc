int __CPROVER_assert(int a, char *b) {}
int __CPROVER_assume(int a ){}

typedef struct walker_list {
	char *end;
	char *cur;
	struct walker_list *prev;
	char wbuf[1];
} walker_list;

int main(){
    int x;
    client(x);
}

int client(int x) {
	if (x>=18 && x<22){
	int a = x;
	int b = 20;
	int c=0;
	int d=0;
	for (int i=1;i<=a;++i){
		c+=b;
	}
	for (int i=1;i<=b;++i){
		d+=a;
		__CPROVER_assert (d <= c, "postcondition");
	}
    __CPROVER_assert( c == d, "postcondition" );
	return c;

	}
	else{
	    return 0;
	  }
}
