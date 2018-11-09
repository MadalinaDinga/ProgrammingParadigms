% ---- 1
declare
fun {Fact N}
if N==1 then N
  else
      Out={Fact N-1}in N*Out
  end
end

declare
fun {Comb N K}
   {Fact N} div ({Fact K}*{Fact N-K})
end

% --- (A)

declare
fun {Numerator N K}
   if K==1 then N
   else
      Out={Numerator N K-1} in (N-K+1)*Out
   end
end

declare
fun {Denominator K}
   if K==1 then K
   else
      Out={Denominator K-1} in Out*K
   end
end

declare
fun {Comb2 N K}
   if K==0 then 1
   else
      {Numerator N K} div {Denominator K}
   end
end

% ---- (B)
declare
fun {Comb3 N K}
   if K==0 then 1
   elseif K==1 then N
   else 
      Out= {Comb3 N K-1} in Out*(N-K+1) div K
   end
end

% --- 2

% declare
% fun {Reverse List}
  % case List of nil then nil
  % [] H|T then {Reverse T}|H
  % end
% end

declare
fun {SecondaryReverse L1 L2}
   case L1 of nil then L2
   [] H|T then {SecondaryReverse T H|L2}
   end
end

declare
fun {Reverse List}
   {SecondaryReverse List nil}
end

%{Browse {Reverse [1 2 3 7]}}

%---- 3 //TODO:
%Lazy evaluation => infinite data structures

fun {Sieve L}
   case L of
      nil then nil
   [] H|T then H|{Sieve {Filter T H}}
   end
end

fun {Filter L H}
   case L of
      nil then nil
   [] A|As then if (A mod H) == 0 then
		   {Filter As H}
		else
		   A|{Filter As H}
		end
   end
end

fun {Prime} {Sieve {Gen 2}} end
fun {Gen N} N|{Gen N+1} end

%{Browse {Prime}}
