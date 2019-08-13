int assert(int a){}

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
        }
        assert( (c == a * b));
        return c;
	}
	else{
	    return 0;
	}
}

