int: n; % number of pizzas
set of int: Pizza = 1..n;
array[Pizza] of int: price;   % price of each pizza

int: m; % number of coupons
set of int: Coupon = 1..m;
array[Coupon] of int: buy;   % buy this many pizzas to use coupon
array[Coupon] of int: free;  % get this many pizzas free

set of int: UsedFor = -m .. m; % -i pizza is assigned to buy of coupon i
                              %  i pizza is assigned to free of coupon i
                              %  0 - no coupon used on pizza

array[Pizza] of var UsedFor: how;
array[Coupon] of var bool: used;

% assign right number of pizzas to buy order
constraint forall(c in Coupon)(used[c] <-> sum(p in Pizza)(how[p] = -c) >= buy[c]);
constraint forall(c in Coupon)(sum(p in Pizza)(how[p] = -c) <= used[c]*buy[c]);
% assign not too many pizzas to free order
constraint forall(c in Coupon)(sum(p in Pizza)(how[p] = c) <= used[c]*free[c]);

constraint forall(p1, p2 in Pizza)((how[p1] < how[p2] /\ how[p1] = -how[p2]) 
                                   -> price[p2] <= price[p1]);
% symmetry breaking
constraint forall(c1, c2 in Coupon where c1 < c2 /\ buy[c1] = buy[c2] /\ free[c1] = free[c2])
                 (forall(p1, p2 in Pizza where price[p1] < price[p2])
                        (how[p1] = -c2 -> how[p2] != -c1));

                  




int: total = sum(price);
var 0..total: cost = sum(p in Pizza)((how[p] <= 0)*price[p]);

solve :: int_search(how, input_order, indomain_min, complete)
      minimize cost;

output  
  ["\ncost("++show(cost)++");\n"];