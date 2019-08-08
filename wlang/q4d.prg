havoc x,y;
assume y >= 0;
c := 0;
r := x;
d := x;
while  c < y
inv (c <= y and r = x - c) and (d = x + c)
do
{
    r := r - 2;
    c := c + 2;
    d := d + 2
}