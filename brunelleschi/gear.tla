-------------------------------- MODULE gear --------------------------------
EXTENDS Integers, Reals, TLAPS
(* 
    Without loss of generality, see our figures, the point of view vector z 
    is <<0, 0, 1>>, as the gear wheel lies in the plane (O, X, Y); 
    where O is the center of the gear wheel. 
    
    Still without loss of generality, such wheel has constant radius 1.
    
*)
VARIABLES x, y (* 3D vectors of the physical space.*)

(* 
    Without loss of generality, we only pick x, y in the following Circle; 
    see above assumptions.
*)
abs[t \in Int] ==  IF t > -t THEN t ELSE -t

(*
    Circle is a subset of Int \X Int \X {0}; which is infinite…
    This works (slowly!) IF you add additional constraints in
    InvX, InvY (See the "Unecessay if.." comment).
    IF NOT, then it fails: TLAPS will not solve any polynomial equation
    for you. 
    
    Note that TLC will not like it either and will raise 
    the usual "non-enumerable set" exception.
 *)

Circle == {
    w \in Int \X Int \X {0}: 
        (* Manhattan norm:*)
        /\ abs[w[1]] + abs[w[2]] = 1 
        (* Euclidian norm:*)
        /\ abs[w[1]]*abs[w[1]] + abs[w[2]]*abs[w[2]] = 1
}

(* 
    Better use this Circle if you want TLC be nice to your spec.
    You can drop the additional constaints in InvX, InvY 
    (see above), since CircleTLC is now a subset of a FINITE set.
    
*)
CircleTLC == {
    w \in {-1, 0, 1} \X {-1, 0, 1} \X {0}: abs[w[1]] + abs[w[2]] = 1
}

(* Simpler is better:  Straighforward definition of Circle:*)
CircleEnum == {
    <<1, 0, 0>>, <<-1, 0, 0>>,
    <<0, 1, 0>>, <<0, -1, 0>>
}
(*You may drop "BY DEF … abs" whether you use it.*)


(* InnerProd is the usual inner product x\cdot y. Hence *)
InnerProd == x[1]*y[1] + x[2]*y[2] 

(* 
    Our assumption z = <<0, 0, 1>> implies that the matrix [x y z] 
    has determinant 
        Det:=  x[1]*y[2] - x[2]*y[1]. 
    Hence the following 
    operator Det 
 *)
Det == IF (x \in Circle /\ y \in Circle) THEN x[1]*y[2] - x[2]*y[1] ELSE 0

(* InvX: x is picked in Circle*; now x is fixed and MUST NOT change.*)
InvX == 
    /\ x \in Circle 
    (* Unnecessary if Circle is explicitely defined as a finite set:*)
    /\ x[1] \in {-1, 1}
    /\ x[2] = 0 

(* InvY y is picked in Circle as well. *)
InvY == 
    /\ y \in Circle
    /\ y[1] = 0 
    (* Unnecessary if Circle is explicitely defined as a finite set:*)
    /\ y[2] \in {-1, 1}
    
(* InvXY: x and y MUST BE nontrivially orthogonal.*)
InvXY == 
    /\ x \in Circle
    /\ y \in Circle
    /\ InnerProd = 0

(* Our invariant []Inv is now "controlled" by the follwing Inv.*)
Inv == 
    /\ InvX 
    /\ InvY 
    /\ InvXY 

(* The Next action:*)
Next == 
    (* Boundaries*)
    /\ y \in Circle
    /\ x \in Circle
    (* So, x  no action will ever change x:*)
    /\ UNCHANGED x
    /\ y' \in Circle (* You want to request that.*)
    (* y is flipped in the sense that y':= -y :*)
    /\ y' = [y  EXCEPT ![1] = -y[1] , ![2] = -y[2]]

(* Our spec Spec, then. Remark that Inv is also the initial condition.*)
Spec == Inv /\ [][Next]_<<x, y>>

(* Typing variables: Relevant type is Circle.*)
Typing(v) == v \in Circle

(* The following lemma states that Next preserves Inv.*) 
LEMMA LemInv == Inv /\ Next => Inv'
<1> SUFFICES ASSUME Inv, Next
PROVE Inv'
OBVIOUS
<1>1 Inv /\ Next => InvX'  
    BY DEF InvX, InvXY, Inv, Next
<1>2 Inv /\ Next => InvY'  
    BY DEF InvY, InvXY, Inv, Next, Circle
<1>3 Inv /\ Next => InvXY' 
    BY DEF InvXY, Inv, Next, Circle, InnerProd
<1>4 QED BY <1>1, <1>2, <1>3 DEF Inv

(* Equivalently, the invariant []Inv is true under specs Spec.*)
THEOREM ThInv == Spec => []Inv
<1>1 Inv /\ UNCHANGED <<x, y>>  => Inv' 
    BY DEF Circle, InnerProd, InvX, InvY, InvXY, Inv
<1>2 Inv /\ [][Next]_<<x, y>>  => []Inv 
    BY PTL, LemInv, <1>1
<1> QED BY PTL, <1>1, <1>2 DEF Spec 


(* 
    ThInv straightforwardly establishes that, under specification 
    Spec, x, y, have always type Circle.

    ThType: Stephan Merz' version.
*)
THEOREM ThTypeCompactVersion == Spec => []Typing(x) /\ []Typing(y)
<1>. Inv => Typing(x) /\ Typing(y)
  BY DEF Inv, InvX, InvY, Typing
<1>. QED
  BY ThInv, PTL
 
(* 
     ThType: Stephan Merz' version, with a SUFFICES ASSUME - PROVE.
 *)
THEOREM ThType == Spec => []Typing(x) /\ []Typing(y) 
<1> SUFFICES ASSUME Spec 
    PROVE 
    /\ Spec => []Inv 
    /\ Inv => Typing(x) /\ Typing(y) 
    BY PTL DEF Inv, InvX, InvY, Typing
<1> Inv => Typing(x) /\ Typing(y)  
    BY DEF Inv, InvX, InvY, Typing
<1> QED BY ThInv, PTL 


(* 
    The following theorem asserts that there are only three options for 
    the step det(x, y, z) -> det(x', y', z): 
    
    1. det(x, y, z) = det(x', y', z)  /\ UNCHANGED <<x, y>>
    2. det(x, y, z) = 1  /\ det(x', y', z) = -1 /\ Next
    3. det(x, y, z) = -1 /\ det(x', y', z) = 1  /\ Next; 

    which establishes that our spec is correct. QED 
*) 
THEOREM ThOscillatingDet == Inv /\ Next => 
    /\ Det  \in {-1, 1} 
    /\ Det' \in {-1, 1} 
    /\ Det' = -Det
<1> SUFFICES ASSUME Inv, Next 
PROVE 
    /\ Det \in {-1, 1} 
    /\ Det' = -Det
    OBVIOUS
<1>1 Inv /\ Next => Det \in {-1,1} 
    BY DEF InvX, InvY, Inv, Next, Det, Circle, abs
<1>2 Inv /\ Next => Det' = - Det   
    BY DEF InvX, InvY, Inv, Next, Det, Circle
<1>3 QED BY <1>1, <1>2


=============================================================================
\* Modification History
\* Last modified Fri Aug 04 17:17:23 CEST 2023 by gcordier
\* Created Wed Aug 01 13:07:52 CEST 2023 by gcordier
