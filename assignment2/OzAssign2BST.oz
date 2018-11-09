% ----- 4
%THIS IS A RECORD DECLARATION REPRESENTING A BST
% FEATURES: left, right, value
declare
Root=node(left:N1 right:N2 value:3)
N1=node(left:nil right:nil value:2)
N2=node(left:nil right:nil value:5)
%{Browse Root}

%not sorted BST
declare
Root1=node(left:N1 right:N2 value:1)
N1=node(left:N3 right:N4 value:2)
N2=node(left:nil right:nil value:3)
N3=node(left:nil right:nil value:4)
N4=node(left:nil right:nil value:5)
%{Browse Root1}

proc {Preorder X}
   if X\=nil then
      {Browse X.value}
      if X.left \=nil then
	 {Preorder X.left}
      end
      if X.right \=nil then
	 {Preorder X.right}
      end
   end
end
%{Browse 'Preorder:'}
%{Preorder Root}

proc {Postorder X}
   if X\=nil then
      if X.left \=nil then
      {Postorder X.left}
      end
      if X.right \=nil then
      {Postorder X.right}
      end
      {Browse X.value}
   end
end
%{Browse 'Postorder:'}
%{Postorder Root}

proc {Inorder X}
   if X\=nil then 
      if X.left\=nil then
	 {Inorder X.left}
      end
      {Browse X.value}
      if X.right\=nil then
	 {Inorder X.right}
      end
   end
end
%{Browse 'Inorder:'}
%{Inorder Root}


% THIS IS A TUPLE DECLARATION, REPRESENTING A BST
declare
Tree = tree(5
	    tree(1 nil nil)
            nil)
 
  fun {Concat Xs}
     {FoldR Xs Append nil}
  end
 
  fun {Preorder T}
     case T of
	nil then nil       % base case: empty node
     [] tree(V L R) then    % recursive call
        {Concat [[V]
                 {Preorder L}
                 {Preorder R}]}
     end
  end

%------------------------PROBL. 1:
%insert an integer into a BST
% Insert :: {<BTree>, <Int>} -> <BTree>
declare
proc {Insert Key TreeIn ?TreeOut}
   case TreeIn
   of nil then TreeOut = tree(Key nil nil) % insert value
   [] tree(K1 T1 T2) then 
      if Key ==  K1 then 
	 TreeOut = tree(Key T1 T2)
      elseif Key < K1 then T in % parse left subtree
        TreeOut = tree(K1 T T2)
        {Insert Key T1 T}
      else T in % parse right subtree
        TreeOut = tree(K1 T1 T)
        {Insert Key T2 T}
      end 
   end 
end
/* 
% -------------- Call:
local
   R
in
   {Browse 'before insert: '#{Preorder Tree}}
   {Insert 2 Tree R}
   {Browse 'after insert: '#{Preorder R}}
end
*/

%-------------------------PROBL. 2:
%The smallest element of the given BST
% Smallest :: <BTree> -> <Int>
%{Browse 'Search smallest in tree: '#{Preorder Tree}}
%{Browse 'Smallest: '#{Max Tree}}
declare
fun {Smallest T LocM}
   case T of nil then LocM
   [] tree(V L R) then
      if V < LocM then
	 {Smallest L V}
      else
	 {Smallest L LocM}
     
      end
   end
end

% ----------- Call:
% Suppose that the maximum possible value in the tree is 100
% {Browse {Smallest Tree 100}}

%-----------------------PROBL. 3:
%The largest element of the given BST
% Biggest :: <BTree> -> <Int>
declare
fun {Max T LocM}
   case T of nil then LocM
   [] tree(V L R) then
      if V > LocM then
	 {Max L V}
      else
	 {Max L LocM}
     
      end
   end
end

% ----------- Call:
%{Browse {Max Tree 0}}
  
%----------------------- PROBL. 4:  
% Check if the given tree has the sortedness property
% Use Smallest/Biggest functions
% IsSortedBST :: <BTree> -> <Bool>
% max value in left subtree is smaller than the node
% min value in right subtree greater than the node

fun {IsSortedBST T}
    case T of nil then true  
    [] tree(V L R) then
      if {Max L 0} > V orelse {Smallest R 100} < V then
	  false
      else
	{IsSortedBST L} andthen {IsSortedBST R}
      end
    end
end

%---------- Call:
/* 
local
Tr1 = tree(10
	   tree(1 nil nil)
	   tree(12 nil nil))
   Tr2 = tree(100
	      tree(102 nil nil)
	      nil)
in
{Browse {IsSortedBST Tr1}}
{Browse {IsSortedBST Tr2}}
end
*/

%-------------------------PROBL. 5:
% Check if the tree is a binary search tree
% uses lazy version of the Boolean operator AND
% only evaluates the then if the first argument evaluates to true
fun {IsBST T}
    case T of nil then true  
    [] tree(V L R) then  
       {IsBST L} andthen {IsBST R}  
    else false end  
end

%--------- Call:
/*
local
Tr1 = tree(5
	   tree(1 nil nil)
	   tree(3 nil nil))
Tr2 = tree(1
	   tree(5 nil nil)
	   tree(0 nil 3))
in
{Browse {IsBST Tr1}}
{Browse {IsBST Tr2}}
end
*/