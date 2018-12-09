% Library of functions that can be used to manipulate lambda terms
% The terms of lambda calculus can be represented using an AST
% AST constructed from tuples

%------- PROBL. 1: FREE VARIABLES //TODO
% Write a function called FreeSet which would return all free variables in an expression

declare
fun {FreeSet Expr}
   case Expr
   of apply(E1 E2) then	 
      %{Browse 'apply'}
      {Append {FreeSet E1} {FreeSet E2}}
   [] Id andthen {IsAtom Id} then [Id]
   [] let(Id#E1 E2) then
      %{Browse 'let'}
      local X = {FreeSet E1}
	 Y = {FreeSet E2} in
	 if {List.member Id Y} then
	    if {List.member Id X} then
	       {Append {DropElem Id Y} {DropElem Id X}} % X, Y without Id
	    else
	       {Append {DropElem Id Y} X} %Y without Id
	    end
	 else
	    if {List.member Id X} then
	       {Append Y {DropElem Id X}} % X without Id
	    else
	       {Append Y X}
	    end
	 end
      end
   [] lam(Id E2) then
      %{Browse 'lam'}
      local X = {FreeSet E2} in
	 if {List.member Id X} then
	       {DropElem Id X}
	    else
	       X
	    end
	 end
   end
end

% Removes all occurrences of the element E from the list L
fun {DropElem E L}
   case L
   of nil then nil
   [] H|T then
      if (H == E) then
	 {DropElem E T}
      else
	 H|{DropElem E T}
      end
   end
end

%{Browse {FreeSet apply(x let(x#y x))}} %returns [x y]
%{Browse {FreeSet apply(y apply(let(x#x x) y))}} %returns [y] or [y y]
%{Browse {FreeSet apply(x let(x#y x))}} %returns [x y]
%{Browse {FreeSet lam(x apply(y x))}}

%------- PROBL. 2: ENVIRONMENT/MAPPING
% list of pairs id (given variable)-expr (corresponding argument)
declare
E1 = 3
E3 = 7
Env = [a#E1 b#y c#E3]

% IsMember :: {<Env> <Id>} -> <Boolean>
% Checks if a given identifier is present in the current environment.
declare
fun {IsMember Env Id}
   
   case Env
   of nil then
      {Browse Id#'is member'}
      false
   [] HId#HEx|T then
      if HId == Id then
	 {Browse Id#'is member'}
	 true
      else
	 {IsMember T Id}
      end
   end
end

%{Browse {IsMember Env c}} %returns true
%{Browse {IsMember Env y}} %returns false

% Fetch :: {<Env> <Id>} -> <Expr>
% Returns the expression of the present identifier from the environment.
declare
fun {Fetch Env Id}
   case Env
   of nil then
      {Browse 'Value for'#Id}
      Id
   [] HId#HEx|T then
      if HId == Id then
	 {Browse 'Value for'#Id}
	 HEx
      else
	 {Fetch T Id}
      end
   end
end

%{Browse {Fetch Env c}} %returns E3
%{Browse {Fetch Env d}} %returns d

% Adjoin :: {<Env> <Id>#<Expr>} -> <Expr>
% Add a new pair into the environment that overrides a previous mapping of the identifier, if it exists.

declare
fun {Adjoin Env Id#Expr}
   case Env
   of nil then {Append Env Id#Expr} %add new element
   [] HId#HEx|T then
      if HId == Id then %override
	HId#Expr|{Adjoin T Id#Expr}
      else
	 HId#HEx|{Adjoin T Id#Expr}
      end
   end
end

%{Browse {Adjoin Env d#E3}}
%{Browse {Adjoin Env c#E1}}

% RENAMING

% use a number that is incremented after each invocation to NewId
% generate new identifiers
Cnt = {NewCell 0}
fun {NewId}
   Cnt :=@Cnt +1
   {String.toAtom {Append "id<" {Append {Int.toString @Cnt} ">"}}}
end

% % function Rename returns a new lambda term where the bound variables are uniquely renamed
% fun {Rename Expr}
   
% end

% {Rename lam(z lam(x z))}
% %returns lam(id<1> lam(id<2> id<1>y))
% {Rename let(id#lam(z z) apply(id y))}
% %returns let(id<3>#lam(id<4> id<4>) apply(id<3> y))

% SUBSTITUTION
% for lambda evaluation
%fun {Subs Id#Ex Expr}
   
%end

%{Browse {Subs x#lam(x x) apply(x y)}}