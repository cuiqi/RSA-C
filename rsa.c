#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>
#include <string.h>
#include <math.h>

#define maxlen 150
#define base 28

unsigned long long int primes[20][10] = {
    {9, 19, 21, 55, 61, 69, 105, 111, 121, 129},
    {3, 17, 27, 33, 57, 87, 105, 113, 117, 123},
    {15, 21, 27, 37, 61, 69, 135, 147, 157, 159},
    {3, 17, 33, 63, 75, 77, 89, 95, 117, 167},
    {39, 49, 61, 85, 91, 115, 141, 159, 165, 183},
    {5, 27, 45, 87, 101, 107, 111, 117, 125, 135},
    {39, 79, 111, 115, 135, 187, 199, 219, 231, 235},
    {57, 89, 95, 119, 125, 143, 165, 183, 213, 273},
    {3, 33, 43, 63, 73, 75, 93, 99, 121, 133},
    {35, 41, 83, 101, 105, 107, 135, 153, 161, 173},
    {1, 19, 61, 69, 85, 99, 105, 151, 159, 171},
    {5, 17, 65, 99, 107, 135, 153, 185, 209, 267},
    {9, 25, 49, 79, 105, 285, 301, 303, 321, 355},
    {41, 77, 113, 131, 143, 165, 185, 207, 227, 281},
    {31, 49, 61, 69, 79, 121, 141, 247, 309, 325},
    {5, 17, 23, 65, 117, 137, 159, 173, 189, 233},
    {25, 31, 45, 69, 123, 141, 199, 201, 351, 375},
    {45, 87, 107, 131, 153, 185, 191, 227, 231, 257},
    {7, 19, 67, 91, 135, 165, 219, 231, 241, 301},
    {87, 167, 195, 203, 213, 285, 293, 299, 389, 437}
};

typedef struct bignum bignum;

struct bignum {
    int place[maxlen];
};

void copyBignum(bignum * a, bignum * b) {
    int i;
    for(i=0;i<maxlen;i++) a->place[i] = b->place[i];
}

void shiftleft(bignum * n, int d) {
    int c;

    for(c=maxlen-1-d;c>=0;c--) n->place[c+d] = n->place[c];
    for(c=0;c<d;c++) n->place[c] = 0;
}

void shiftRight(bignum * n) {
    int c;
    for(c=0;c<=maxlen-2;c++) n->place[c] = n->place[c+1];
    n->place[maxlen-1] = 0;
}

bignum * initBignum() {
    bignum * newbignum = (struct bignum*)malloc(sizeof(bignum));
    int c;
    for(c=0;c<maxlen;c++) newbignum->place[c] = 0;
    return newbignum;
}

void intToBignum(unsigned long long int i, bignum * a) {
    unsigned long long int x = i;
    int c;
    for(c=0;c<maxlen;c++) a->place[c] = 0;
    for(c=0;x>0 && c<maxlen;x/=base, c++) a->place[c] = x % base;
}

void printBignum(bignum * a) {
    int c;
    for(c=maxlen-1;c>0 && a->place[c]==0;c--);
    for(;c>=0;c--) printf("%d", a->place[c]);
    printf("\n");
}

bool isNotZero(bignum * n){
    int c;
    for(c=0;c<maxlen;c++) if(n->place[c]!=0) return true;
    return false;
}

bool equals(bignum * a, bignum * b) {
    int c;
    for(c=0;c<maxlen;c++) if(a->place[c]!=b->place[c]) return false;
    return true;
}

bool isGreaterThan(bignum * a, bignum * b) {
    int c;
    for(c=maxlen-1;c>0 && a->place[c] == b->place[c];c--);
    if(a->place[c]>b->place[c]) return true;
    return false;
}

bool isLessThan(bignum * a, bignum * b) {
    int c;
    for(c=maxlen-1;c>0 && a->place[c] == b->place[c];c--);
    if(a->place[c]<b->place[c]) return true;
    return false;
}

bool isLessThanOrEqualTo(bignum * a, bignum * b) {
    if(isLessThan(a, b)) return true;
    if(equals(a, b)) return true;
    return false;
}

bool isGreaterThanOrEqualTo(bignum * a, bignum * b) {
    if(isGreaterThan(a, b)) return true;
    if(equals(a, b)) return true;
    return false;
}

bignum * plus(bignum * a, bignum * b) {
    bignum * sum = initBignum();
    int carry = 0, p;

    for(p=0;p<maxlen;p++) {
        sum->place[p] = (a->place[p] + b->place[p] + carry) % base;        
        carry = (a->place[p] + b->place[p] + carry) / base;
    }

    return sum;
}

bignum * minus(bignum * a, bignum * b) {
    bignum * diff = initBignum();
    int borrow = 0, p, d;

    for(p=0;p<maxlen;p++) {
        diff->place[p] = a->place[p] - borrow - b->place[p];
        borrow = 0;
        if(diff->place[p]<0) {
            diff->place[p] += base;
            borrow = 1;
        }
    }

    return diff;
}

bignum * times(bignum * a, bignum * b) {
    bignum r;
    bignum * product = initBignum();
    bignum * temp;
    int c, c2;

    r = *a;

    for(c=0;c<maxlen;c++) {
        for(c2=1;c2<=b->place[c];c2++){
            temp = plus(product, &r);
            copyBignum(product, temp);
            free(temp);
        }
        shiftleft(&r, 1);
    }

    return product;
}

bignum * divide(bignum * a, bignum * b) {
    bignum * r = initBignum(), * temp = initBignum(), * quotient = initBignum();
    int c, c2;

    for(c=maxlen-1;c>=0;c--) {
        shiftleft(r, 1);
        r->place[0] = a->place[c];
        quotient->place[c] = 0;
        while(isGreaterThanOrEqualTo(r, b)) {
            quotient->place[c]++;
            temp = minus(r, b);
            copyBignum(r,temp);
            free(temp);
        }
    }

    free(r);
    return quotient;
}

bignum * modBignum(bignum * a, bignum * b){
    bignum * temp = divide(a, b);
    bignum * temp2 = times(b, temp);
    free(temp);
    temp = minus(a, temp2);
    free(temp2);
    
    return temp;
}

bignum * gcdBignum(bignum * a, bignum * b) {
    bignum * temp = initBignum();
    if(equals(b, temp)) {
        free(temp);
        return a;
    } else {
        free(temp);
        return gcdBignum(b, modBignum(a,b));
    }
}

bignum * raiseTo(bignum * a, bignum * b){
    bignum counter = *b;
    bignum * temp2;
    bignum * product = initBignum();
    intToBignum(1, product);
    bignum * one = initBignum();
    intToBignum(1, one);

    while(isNotZero(&counter)) {
        temp2 = times(product, a);
        copyBignum(product,temp2);
        free(temp2);

        temp2 = minus(&counter, one);
        copyBignum(&counter, temp2);
        free(temp2);
    }

    free(one);

    return product;
}


bignum *  randomBignumPrime() {
    bignum * prime;
    bignum * two = initBignum();
    bignum * n = initBignum();
    bignum * k = initBignum();
    bignum * temp;

    int intn = rand() % 20;
    intToBignum(2, two);
    intToBignum(intn+21, n);
    intToBignum(primes[intn][rand() % 10], k);

    prime = raiseTo(two, n);
    temp = minus(prime, k);
    copyBignum(prime, temp);

    free(temp);
    free(k);
    free(n);
    free(two);

    return prime;
}

bignum * modInverseBignum(bignum * e, bignum * phi) {
    bignum * a = initBignum();
    bignum * b = initBignum();
    bignum * q = initBignum();

    bignum * x = initBignum();
    bignum * lastx = initBignum();
    intToBignum(1, lastx);

    bignum * temp;
    bignum * tempp;
    bignum * temp2 = initBignum();
    copyBignum(a, e);
    copyBignum(b, phi);

    while(isNotZero(b)) {
        temp = divide(a, b);
        copyBignum(q, temp);
        free(temp);

        copyBignum(temp2, b);
        temp = modBignum(a, b);
        copyBignum(b, temp);
        free(temp);
        copyBignum(a, temp2);

        copyBignum(temp2, x);
        temp = times(q, x);
        tempp = minus(lastx, temp);
        free(temp);
        copyBignum(x, tempp); 
        free(tempp);
        copyBignum(lastx, temp2);
    }

    temp = plus(lastx, phi);
    free(a);
    free(b);
    free(q);
    free(x);
    free(lastx);
    free(temp2);

    return temp;

}

bignum * modExpoBignum(bignum * b, bignum * exp, bignum * mod) {
    bignum * temp;
    bignum * tempp;

    bignum * c = initBignum();
    intToBignum(1, c);
    bignum * e = initBignum();
    intToBignum(1, e);
    bignum * one = initBignum();
    intToBignum(1, one);

    while(isLessThanOrEqualTo(e,exp))  {
        temp = times(c,b);
        tempp = modBignum(temp,mod);
        copyBignum(c, tempp);
        free(tempp);
        free(temp);
        temp = plus(e, one);
        copyBignum(e, temp);
        free(temp);
    }

    return c;
}

bignum * modExpoBignumEx(bignum * b, bignum * exp, bignum * mod) {
    bignum * temp;
    bignum * temp2;

    bignum * c = initBignum();
    intToBignum(1, c);
    bignum * e = initBignum();
    copyBignum(e, exp);
    bignum * bb = initBignum();
    copyBignum(bb, b);

    bignum * two = initBignum();
    intToBignum(2, two);

    while(isNotZero(e)) {
        if(e->place[0]%2 == 1) {
            temp = times(c, bb);
            temp2 = modBignum(temp, mod);
            free(temp);
            copyBignum(c, temp2);
            free(temp2);
        }
        temp = divide(e, two);
        copyBignum(e, temp);
        free(temp);
        temp = times(bb, bb);
        temp2 = modBignum(temp, mod);
        copyBignum(bb, temp2);
        free(temp);
        free(temp2);
    }

    free(two);
    free(bb);
    free(e);

    return c;
}

bignum * stringToBignum(char * s) {
    int i;
    bignum * c = initBignum();
    for(i=0;i<10;i++) {
        if(s[i]=='a')c->place[i]=1;
        else if(s[i]=='b')c->place[i] =2;
        else if(s[i]=='c')c->place[i] =3;
        else if(s[i]=='d')c->place[i] =4;
        else if(s[i]=='e')c->place[i] =5;
        else if(s[i]=='f')c->place[i] =6;
        else if(s[i]=='g')c->place[i] =7;
        else if(s[i]=='h')c->place[i] =8;
        else if(s[i]=='i')c->place[i] =9;
        else if(s[i]=='j')c->place[i] =10;
        else if(s[i]=='k')c->place[i] =11;
        else if(s[i]=='l')c->place[i] =12;
        else if(s[i]=='m')c->place[i] =13;
        else if(s[i]=='n')c->place[i] =14;
        else if(s[i]=='o')c->place[i] =15;
        else if(s[i]=='p')c->place[i] =16;
        else if(s[i]=='q')c->place[i] =17;
        else if(s[i]=='r')c->place[i] =18;
        else if(s[i]=='s')c->place[i] =19;
        else if(s[i]=='t')c->place[i] =20;
        else if(s[i]=='u')c->place[i] =21;
        else if(s[i]=='v')c->place[i] =22;
        else if(s[i]=='w')c->place[i] =23;
        else if(s[i]=='x')c->place[i] =24;
        else if(s[i]=='y')c->place[i] =25;
        else if(s[i]=='z')c->place[i] =26;
        else if(s[i]=='\n') break;
    }
    return c;
}

void printBigNumToString(bignum * s) {
    int i;
    for(i=0;i<maxlen;i++) {
        if(s->place[i]==1) printf("a");
        else if(s->place[i]==2) printf("b");
        else if(s->place[i]==3) printf("c");
        else if(s->place[i]==4) printf("d");
        else if(s->place[i]==5) printf("e");
        else if(s->place[i]==6) printf("f");
        else if(s->place[i]==7) printf("g");
        else if(s->place[i]==8) printf("h");
        else if(s->place[i]==9) printf("i");
        else if(s->place[i]==10) printf("j");
        else if(s->place[i]==11) printf("k");
        else if(s->place[i]==12) printf("l");
        else if(s->place[i]==13) printf("m");
        else if(s->place[i]==14) printf("n");
        else if(s->place[i]==15) printf("o");
        else if(s->place[i]==16) printf("p");
        else if(s->place[i]==17) printf("q");
        else if(s->place[i]==18) printf("r");
        else if(s->place[i]==19) printf("s");
        else if(s->place[i]==20) printf("t");
        else if(s->place[i]==21) printf("u");
        else if(s->place[i]==22) printf("v");
        else if(s->place[i]==23) printf("w");
        else if(s->place[i]==24) printf("x");
        else if(s->place[i]==25) printf("y");
        else if(s->place[i]==26) printf("z");
        else if(s->place[i]==0) printf("");
    }
    printf("\n");
}



unsigned long long int main() {
    srand(time(NULL));

    unsigned long long int input;

    bignum * p = randomBignumPrime();
    bignum * q = randomBignumPrime();
    bignum * n = times(p,q);

    bignum * one = initBignum();
    intToBignum(1, one);

    bignum * temp = minus(p, one);
    bignum * temp2 = minus(q, one);
    bignum * phin = times(temp,temp2);

    free(temp);
    free(temp2);
    free(one);

    bignum * e = initBignum();
    intToBignum(65537, e);

    bignum * d = modInverseBignum(e, phin);

    bignum * inputinput = initBignum();

    printf("p: ");
    printBignum(p);
    printf("q: ");
    printBignum(q);
    printf("n: ");
    printBignum(n);
    printf("phin: ");
    printBignum(phin);
    printf("e: ");
    printBignum(e);
    printf("d: ");
    printBignum(d);

    //printf("\nEnter input: ");
    //scanf("%llu", &input);
    //intToBignum(input, inputinput);

    char stringinput[10];
    printf("Enter 10 character string: ");
    scanf("%s", stringinput);
    inputinput = stringToBignum(stringinput);


    printf("\nEncrypted: ");
    bignum * encrypted = modExpoBignumEx(inputinput, e, n);
    printBignum(encrypted);
    printf("Decrypted: ");
    bignum * decrypted = modExpoBignumEx(encrypted, d, n);
    printBignum(decrypted);
    printf("\nDecrypted String: ");
    printBigNumToString(decrypted);

    free(p);
    free(q);
    free(n);
    free(phin);
    free(e);
    free(d);
    free(encrypted);
    free(decrypted);

    return 0;
}
