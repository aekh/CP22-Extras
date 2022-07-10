%% Author: Alexander Ek <alexander.ek@monash.edu>
%% Modes: -2 = Decomposition as in paper.
%%         0 = Propagate variance when X fixed.
%%         9 = Variance Lb Propagator as in paper.
int: mode;


%%% 
%%% vers: 0 = variance
%%% vers: 1 = gini
{0,1}: vers;

%%% SPREAD

predicate spread(var int: v, array [int] of var int: X, var int: S, int: scale) =
  if mode = -1 then
    spread_decomp(v, X, S, scale)
  elseif mode = -2 then
    spread_decomp2(X, S, v, scale)
  elseif mode = -3 then
    spread_decomp2(X, S, v, scale) /\ variance_int(v, X, S, scale, mode)
  else
    variance_int(v, X, S, scale, mode)
  endif;

predicate spread_decomp(var int: v, array [int] of var int: X, var int: S, int: scale) =
  let {int: N = card(index_set(X));
       array [int] of var 0..infinity: sq = [ abs(N*X[i] - S) * abs(N*X[i] - S) | i in index_set(X) ]}
  in v = (sum(sq)*scale) div (N*N*N);

predicate spread_decomp2(array[int] of var int:X, var int: M, var int: v, int:s) =
  let { int: n=length(X);
        array[int] of var 0..infinity: sq = [X[i]*X[i] | i in index_set(X)];
        %array[int] of var 0..infinity: sq2 = [ (n*X[i] - S) * (n*X[i] - S) | i in index_set(X) ];
        var 0..n*ub(sum(sq)): v_ = n*sum(sq);
        var lb(M)..infinity: Msq = M*M;
        var 0..ub(v_): v__ = v_ - Msq;
        var 0..infinity: v___ = v__*s;
        %constraint n*v_ = sum(sq2)*s;
        }
  in v = v___ div (n*n);

predicate variance_int(var int: y, array [int] of var int: x, var int: sum, int: s, int: mode);

%%%
%%% GINI

predicate gini(var int: v, array [int] of var int: X, var int: S, int: scale) =
  if mode = -1 \/ mode = -2 then
    gini_decomp(X, S, v, scale)
  else
    gini_int(v, X, S, scale, mode)
  endif;
  
predicate gini_decomp(array[int] of var int: X, var int: M, var int: v, int: s) =
  let { int: n=length(X);
        array[int] of var 0..500000000: diffs = [ abs(X[i]-X[j]) | i,j in index_set(X) where i<j];
        var 0..500000000: tot_diff = sum(diffs) * s; 
        var 0..500000000: result_ = tot_diff div n;
        var 0..500000000: result = abs(result_) div abs(M)}
  in v = result;

predicate gini_int(var int: y, array [int] of var int: x, var int: sum, int: s, int: mode);


int: n;
array [1..n,1..2] of int: lu;

% constraint v <= ( sum(x in X) ( max([(n*lb(x)-max([ub(x) | x in X]))^2,
%                                      (n*ub(x)-min([lb(x) | x in X]))^2,
%                                      (n*lb(x)-min([lb(x) | x in X]))^2,
%                                      (n*ub(x)-max([ub(x) | x in X]))^2]) ) * 100 ) div (n*n*n);

array [1..n] of var int: X :: add_to_output;
var int: S :: add_to_output;
var 0..infinity: v :: add_to_output;

%%%

constraint if vers = 0 
             then forall ( i in 1..n )
               ( lu[i,1] <= X[i] /\ X[i] <= lu[i,2] )
             else let {int: pad = -min([0,min(lu[..,1])])+1}
                  in forall ( i in 1..n )
                    (lu[i,1]+pad <= X[i] /\ X[i] <= lu[i,2]+pad)
             endif;

constraint S = sum(X);
% constraint forall (i in index_set(X) diff {min(index_set(X))}) (
%   X[i] > X[i-1]
% );

constraint if vers = 0
             then spread(v, X, S, 100)
             else gini(v, X, S, 10000)
             endif;
%constraint 
%mode = 0;
%vers = 1;
%constraint v <= 1000;
%constraint -299 <= S /\ S <= 299;

%%%

% solve minimize v :: seq_search([int_search([S], input_order, indomain_min)
%                                ,int_search( X , input_order, indomain_min)]);

solve :: seq_search([%int_search([v], input_order, indomain_min),
                     int_search(X, input_order, indomain_split),
                     int_search([v,S], input_order, indomain_min)]) minimize v;

%solve minimize v;

%solve :: seq_search([int_search([v], input_order, indomain_min),
%                     int_search(X, input_order, indomain_split)])
%         minimize v;
