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

