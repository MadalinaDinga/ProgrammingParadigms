% Library of functions that can be used to manipulate lambda terms
% The terms of lambda calculus can be represented using an AST
% AST constructed from tuples

%------- PROBL. 1: FREE VARIABLES
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

% RENAMING   //TODO: rethink it

% use a number that is incremented after each invocation to NewId
% generate new identifiers
Cnt = {NewCell 0}
fun {NewId}
   Cnt :=@Cnt +1
   {String.toAtom {Append "id<" {Append {Int.toString @Cnt} ">"}}}
end

% function Rename returns a new lambda term where the bound variables are uniquely renamed
% Id: if not free, rename: if in dictionary name#newName => newName, otherwise create new name and add to dictionary
%	if free, keep name

fun {RenameImpl E RenVars FreeVars Renamed} 
   {Browse E#RenVars}
   case E
   of Id andthen {IsAtom Id} then 
      if {List.member Id FreeVars} == false then % if not free (bound)
      % return the new name of the id
	 local NewName = {GetRenamedVar RenVars Id} in
	    local RenVarsNew X in
		  RenVarsNew = {AppendRenamed RenVars Id false}
	       if  NewName \= nil then
		  {RenameImpl Id#NewName RenVarsNew FreeVars true}
	       else
	       %append new variable and call Rename again, using the new name as the expression param E
		  X = {List.last RenVarsNew}
		  {RenameImpl X RenVarsNew FreeVars true}
	       end
	    end
	 end
      else 
	 Id
      end
   [] K#V then
      V
   [] lam(X Y) then
      local X1 in
	 X1 = {RenameImpl X RenVars FreeVars Renamed}
	 lam(X1 {RenameImpl Y RenVars FreeVars Renamed})
      end
   [] let(Id#X Y) then
      let({RenameImpl Id RenVars FreeVars Renamed}#{RenameImpl X RenVars FreeVars Renamed} {RenameImpl Y RenVars FreeVars Renamed})
   [] apply(X Y) then
      apply({RenameImpl X RenVars FreeVars Renamed} {RenameImpl Y RenVars FreeVars Renamed})
   end
end

fun {AppendRenamed RenamedVars VarName Found}
   %{Browse 'Renamed'#RenamedVars}
   %{Browse 'VarName'#VarName}
   case RenamedVars
   of nil then
      if (Found) then
	 nil
      else
	 [VarName#{NewId}]
      end
   [] HV#HN|T then
      if (HV == VarName) then %return the already generated new name
	 HV#HN|{AppendRenamed T VarName true}
      else
	 HV#HN|{AppendRenamed T VarName Found}
      end
   end
end

fun {GetRenamedVar RenamedVars VarName}
   case RenamedVars
   of nil then
      nil
   [] HV#HN|T then
      if (HV == VarName) then
	 HN
      else
	 {GetRenamedVar T VarName}
      end
   end
end

fun {Rename E}
   local VarRenamed = nil
   Renamed = false in
   %{Browse {FreeSet E}}
   %{Browse {List.last {AppendRenamed VarRenamed x}}}
   {RenameImpl E VarRenamed {FreeSet E} Renamed}
   end
end

% local E = lam(x lam(y x)) in
%    {Browse {Rename E}}
% end

%returns lam(id<1> lam(id<2> id<1>))
%{Browse {Rename let(id#lam(z z) apply(id y))}}
%returns let(id<3>#lam(id<4> id<4>) apply(id<3> y))

% SUBSTITUTION for lambda evaluation
% substitute only free occurences
%free variables must not clash with the bound variables of the latter arguments => rename each lambda term whose bound variable clashes with the free variables of the argument being substituted.

fun {SubsImpl Id#Ex Expr FreeS}
case Expr
   of T andthen {IsAtom T} then 
   if (Id == T) andthen ({List.member T FreeS}) then
         Ex
      else 
	 T
      end
   [] lam(X Y) then
      lam({SubsImpl Id#Ex X {FreeSet Expr}} {SubsImpl Id#Ex Y {FreeSet Expr}})
   [] let(Id#X Y) then
      let({SubsImpl Id#Ex Id {FreeSet Expr}}#{SubsImpl Id#Ex X {FreeSet Expr}} {SubsImpl Id#Ex Y {FreeSet Expr}})
   [] apply(X Y) then
      apply({SubsImpl Id#Ex X FreeS} {SubsImpl Id#Ex Y FreeS})
   end   
end

fun {Subs X#Y Z}
   % resolve clashing problem by renaming each lambda term whose bound variable clashes with the free variables of the argument being substituted
   % the Rename function renames all bound variables in an expression
   {SubsImpl X#Y {Rename Z} {FreeSet Z}}
end

{Browse {Subs x#lam(x x) apply(x y)}}
% check free occurances substitution
{Browse {Subs x#lam(z z) apply(x lam(x apply(x z)))}}
% check clashing
{Browse {Subs x#lam(y z) apply(x lam(z apply(x z)))}}
