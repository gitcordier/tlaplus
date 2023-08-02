-------------------------------- MODULE gear --------------------------------
EXTENDS Reals, TLAPS
(* Without loss of generality, see our figures, the point of view vector Z 
is <<0, 0, 1>>, as the gear wheel lies in the plane (O, X, Y); where O is the 
center of the gear wheel. Still without loss of generality, such wheel has
constant radius 1.*)
CONSTANT Z (* Z MUST BE the constant vector <<0, 0, 1>>*)
VARIABLES x, y (* 3D vectors of the physical space.*)

(* Without loss of generality, we only pick x, y in the following Vect; 
see above assumptions.*)
Vect == {
    <<1, 0, 0>>, <<-1, 0, 0>>,
    <<0, 1, 0>>, <<0, -1, 0>>
}

(* InnerProd is the inner product x\cdot y. Hence *)
InnerProd == 
        x[1] * y[1] + 
        x[2] * y[2] + 
        x[3] * y[3] 

(* Our assumption Z = <<0, 0, 1>> implies that the matrix [x y z] has determi-
-nant Det:=  x[1]*y[2] - x[2]*y[1]. Hence the following operator Det *)
Det ==  x[1]*y[2] - x[2]*y[1] 

(* InvX: x is a picked in Vect*: now x is fixed here and MUST NOT change.*)
InvX == 
    /\ x \in Vect 
    /\ x[1] \in {-1, 1} 
    /\ x[2] = 0 
    /\ x[3] = 0

(* InvY y is a picked in Vect as well. *)
InvY == 
    /\ y \in Vect
    /\ y[1] = 0 
    /\ y[2] \in {-1, 1} 
    /\ y[3] = 0 
    
(* InvXY: x and y MUST BE nontrivially orthogonal*)
InvXY == 
    /\ x # << 0, 0, 0 >>  (* Redundant whether InvX is enabled.*)
    /\ y # << 0, 0, 0 >>  (* Redundant whether InvY is enabled.*)
    /\ InnerProd = 0

(* Let us repeat that Z = <<0, 0, 1 >>*)
InvZ == Z = <<0, 0, 1>>

(* Our invariant []Inv is now "controlled" by the follwing Inv *)
Inv == 
    /\ InvX 
    /\ InvY 
    /\ InvXY 
    /\ InvZ 

(* The Next action*)
Next == 
    (* So, x  no action will ever change x:*)
    /\ UNCHANGED x
    (* y is flipped in the sense that y':= -y :*)
    /\ y' = [y  EXCEPT ![1] = -y[1] , ![2] = -y[2]]

(* Our spec Spec, then. Remark that Inv is also the initial condition*)
Spec == Inv /\ [][Next]_<<x, y>>

(* Typing variables: Relevant type is Vect.*)
Typing(v) == v \in Vect

(* The following lemma states that Next preserves Inv.*) 
LEMMA LemInv == Inv /\ Next => Inv'
<1> SUFFICES ASSUME Inv /\ Next
PROVE Inv'
OBVIOUS
<1> USE DEF Vect, InnerProd, InvX, InvY, InvXY, InvZ, Inv, Next
<1>1 Inv /\ Next => Inv' OBVIOUS
<1>4 QED BY <1>1

(* Equivalently, the invariant []Inv is true under specs Spec.*)
THEOREM ThInv == Spec => []Inv
<1> USE DEF Vect, InnerProd, InvX, InvY, InvXY, InvZ, Inv
<1>1 Inv /\ UNCHANGED <<x, y>>  => Inv' BY DEF Inv
<1>2 Inv /\ [][Next]_<<x, y>>  => []Inv BY PTL, LemInv, <1>1 
<1> QED BY <1>1, <1>2 DEF Spec


(* ThInv straightforwardly establishes that, under specification Spec, x, y, 
have always type Vect.*)
THEOREM ThType == Spec => []Typing(x) /\ []Typing(y) 
<1> SUFFICES ASSUME Spec
PROVE []Typing(x) /\ []Typing(y) 
OBVIOUS
<1> USE DEF 
    Vect, InnerProd, Det, InvX, InvY, InvXY, InvZ, Inv, Next, Spec, Typing
<1>1 Spec => []Inv BY ThInv
<1>2 Inv => Typing(x) /\ Typing(y)  OBVIOUS
<1>3 QED BY PTL, <1>1, <1>2 DEF Inv, Typing

(* The following theorem asserts that there are only three options for 
the step det(x, y, z) -> det(x', y', z'): 

1. det(x, y, Z) = det(x', y', Z)  /\ UNCHANGED <<x, y>>
2. det(x, y, Z) = 1  /\ det(x', y', Z) = -1 /\ Next
3. det(x, y, Z) = -1 /\ det(x', y', Z) = 1  /\ Next 

which establishes that our spec is correct. QED *) 
THEOREM ThOscillatingDet == Inv /\ Next => 
    /\ Det  \in {-1, 1} 
    /\ Det' \in {-1, 1} 
    /\ Det' = -Det
<1> SUFFICES ASSUME Inv /\ Next 
PROVE 
    /\ Det \in {-1, 1} 
    /\ Det' \in {-1, 1} 
    /\ Det' = -Det
OBVIOUS
<1> USE DEF 
    Vect, InnerProd, Det, InvX, InvY, InvXY, InvZ, Inv, Next, Spec
<1>1 Inv /\ Next => Det \in {-1,1} OBVIOUS
<1>2 Inv /\ Next => Det'\in {-1,1} OBVIOUS
<1>3 Inv /\ Next => Det' = - Det   OBVIOUS
<1>4 QED BY <1>1, <1>2, <1>3

=============================================================================


