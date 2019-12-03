%Pizza Coupon Problem

int: n; %number of pizzas
set of int: Pizza = 1 .. n;
array[Pizza] of int: price; %price is giving the price for each of the n pizzas

int: m; %number of pizza coupons
set of int: Coupon = 1 .. m;
array[Coupon] of int: buy; %buy is giving the number of paid pizzas required to justify using each of the m coupons
array[Coupon] of int: free; %free is giving the number of free pizzas that can be obtained by using each of the m coupons

array[Coupon, Pizza] of var bool: UsedFor; %UsedFor(c, p) hold if p is one of the pizzas received for free by using coupon c
array[Coupon, Pizza] of var bool: Justifies; %Justifies(c, p) hold if pizza p is one of the pizzas is paid for to justify using coupon c

var set of Pizza: Paid; %Set of pizzas will be paid for
var set of Coupon: Used; %Set of coupons that will be used

var int: cost = sum (i in Pizza) (bool2int(i in Paid) * price[i]);

%We pay for exactly the pizzas that we don’t get free by using coupons:
constraint forall(p in Pizza)((p in Paid) <-> not exists (c in Used)(UsedFor[c, p]));

%Used is the set of coupons that is used:
constraint forall(c in Coupon)((c in Used) <-> exists (p in Pizza)(UsedFor[c, p]));

%Any coupon that is used must be justified by sufficiently many purchased pizzas:
constraint forall(c in Coupon)((c in Used) -> sum(p in Pizza)(bool2int (Justifies[c,p])) >= buy[c]);

%The number of pizzas any coupon is used for is not more than the number it allows us to get free:
constraint forall(c in Coupon)((c in Used) -> (sum(p in Pizza)(bool2int (UsedFor[c,p])) <= free[c]));

%Each free pizza costs at most as much as the cheapest pizza used to justify use of the relevant coupon:
constraint forall(c in Coupon) (
  forall (p,q in Pizza where p!=q) (
    ((UsedFor[c,p] /\ Justifies[c,q]) -> (price[p] <= price[q]))
   ));
   
%Every pizza used to justify use of a coupon is paid for:
constraint forall (p in Pizza) (
  forall (c in Coupon) (
    Justifies[c,p] -> (p in Paid)));

%The total cost is not too large:   
constraint cost <= sum(p in Pizza)(price[p]);

%Justifies(c, p) and UsedFor(c, p) hold only of pairs consisting of a coupon and a pizza
constraint forall(c in Coupon) (
    forall(p in Pizza) (
      (Justifies[c,p]) -> (
         ((1 <= c ) /\ (c<=m)) /\ ((1 <= p) /\ (p<=n)))
    ));
    
constraint forall(c in Coupon) (
    forall(p in Pizza) (
      (UsedFor[c,p]) -> (
         ((1 <= c ) /\ (c<=m)) /\ ((1 <= p) /\ (p<=n)))
    ));  
    
%Any pizza used to justify a coupon is used once
constraint forall(c in Coupon) (
  forall(p in Pizza)
    (Justifies[c,p] -> not exists(d in Coupon where c != d)(Justifies[d,p])
));
   
solve minimize cost;
output ["cost(" ++ show(cost) ++ ")\n"
    ];  

