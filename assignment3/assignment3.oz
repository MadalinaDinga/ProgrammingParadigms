%------------ ASSIGNMENT 3

%------------ PROBL. 1
% Search in list
declare
fun {Member Xs Y}
   case Xs
   of nil then false
   [] H|T then
      if H == Y then
	 true
      else
	 {Member T Y}
      end
   end
end

%{Browse {Member [3 4 5] 5}}

%------------ PROBL. 2
local
   fun {Take Xs N}
      case Xs
      of nil then nil 
      [] H|T then
	 if N>0 then
	    H|{Take T N-1}
	 else
	    {Take T N-1}
	 end
      end
   end
   
fun {Drop Xs N}
   case Xs
   of nil then nil
   [] H|T then
      if N>0 then
	 {Drop T N-1}
      else
	 H|{Drop T N-1}
      end
   end
end
in
   {Browse {Take [2 3 4] 2}}
   {Browse {Drop [2 3 4] 2}}
end

%------------- PROBL. 3:
% ZIP/ UNZIP
% assume the lists have equal sizes
local
   fun {Zip L1 L2}
      case L1#L2
      of nil#nil then nil
      [] (H1|T1)#(H2|T2) then
	 (H1#H2)|{Zip T1 T2}
      end
   end

   fun {Unzip L}
      case L
      of nil then nil#nil
      [] (H1#H2)|T then
	 T1#T2 = {Unzip T} in
	 (H1|T1)#(H2|T2)
      end
   end
in
   % input: pair of lists [a b c]#[1 2 3]
   % output: list of pairs  [a#1 b#2 c#3]
   {Browse {Zip [a b c] [1 2 3]}}
   % input: list of pairs [a#1 b#2 c#3]
   % output: pair of lists [a b c]#[1 2 3]
   {Browse {Unzip [a#1 b#2 c#3]}}
end

%------------- PROBL. 4:
local
   fun {Position Xs Y P}
      case Xs
      of nil then 0 % return 0 if Y does not occur in Xs
      [] H|T then
	 if Y == H then
	    P
	 else
	    {Position T Y P+1}
	 end
	 
      end
   end
in
   {Browse {Position [2 3 4] 4 1}}
end

%------- PROBL. 5: ARITHMETIC EXPRESSIONS EVALUATION
% An arithmetic expression can be represented using an AST
% AST constructed from tuples
declare
fun {Eval Expr}
   case Expr
   of int(N) then N
   [] mul(X Y) then
      {Eval X} * {Eval Y}
   [] add(X Y) then
      {Eval X} + {Eval Y}
   end
end

{Browse {Eval add(int(1) mul(int(3) int(4)))}}
