import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Adequacy
import Iris.ProgramLogic.Lifting
import Iris.BI.Lib.GenHeap
import Iris.Std.GenSetsInstances
import Iris.ProofMode
import Std.Data.ExtTreeMap
import CN_Lib.CN_Lib
import Lean.Elab
import Lean

open Lean Elab Tactic Qq
open Iris ProgramLogic Language.Notation Std FromMathlib BI

namespace CN_Lib

-- Library for things needed by CN lemma exports.

-- 1, Resource algebra for heaps that are maps from integers
--  to integers.

abbrev myHeapF := fun V => Std.ExtTreeMap Int V compare

-- Pointers are just integers for now
abbrev Ptr := Int
-- Values are option integers for now
abbrev Val := Option Int

-- class MyHeap (hlc : outParam HasLC) (GF : BundledGFunctors) where
--   heap : genHeapGS Ptr Val GF myHeapF

class MyHeap (hlc : outParam HasLC) (GF : BundledGFunctors) extends genHeapGS Ptr Val GF myHeapF

-- attribute [reducible, instance] MyHeap.heap

variable [MyHeap hlc GF]


-- 2, CN-style ownership predicates.
-- Every ownership predicate reduces to ownership of unsigned
-- bytes and a proof that the value is within bounds for that type.

-- Ownership of unsigned C integer types
def Owned_UChar (l : Ptr) (v : Int) : IProp GF := iprop%
    (l ↦ some v) -- Pointsto predicate
  ∗ ⌜l ≠ 0⌝ -- Pointer is non-null
  ∗ ⌜ min_UChar ≤ v ∧ v ≤ max_UChar ⌝ -- Value is within bounds
def Owned_UShort (l : Ptr) (v : Int) : IProp GF :=
  let bytes := UShort_bytes v
    iprop% Owned_UChar l (bytes 0)
  ∗ Owned_UChar (l + 1) (bytes 1)
  ∗ ⌜ min_UShort ≤ v ∧ v ≤ max_UShort ⌝
def Owned_UInt (l : Ptr) (v : Int) : IProp GF :=
  let bytes := UInt_bytes v
  iprop%
    ([∗list] i ↦ b ∈ List.ofFn bytes, Owned_UChar (l + i) b)
  ∗ ⌜ min_UInt ≤ v ∧ v ≤ max_UInt ⌝
def Owned_ULong (l : Ptr) (v : Int) : IProp GF :=
  let bytes := ULong_bytes v
  iprop%
    ([∗list] i ↦ b ∈ List.ofFn bytes, Owned_UChar (l + i) b)
  ∗ ⌜ min_ULong ≤ v ∧ v ≤ max_ULong ⌝

-- Ownership of signed C integer types
def Owned_Char (l : Ptr) (v : Int) : IProp GF :=
  let byte := wrapI min_UChar max_UChar v
  iprop%
    Owned_UChar l byte
  ∗ ⌜ min_Char ≤ v ∧ v ≤ max_Char ⌝
def Owned_Short (l : Ptr) (v : Int) : IProp GF :=
  let bytes := UShort_bytes (wrapI min_UShort max_UShort v)
  iprop%
    Owned_UChar l (bytes 0)
  ∗ Owned_UChar (l + 1) (bytes 1)
  ∗ ⌜ min_Short ≤ v ∧ v ≤ max_Short ⌝
def Owned_Int (l : Ptr) (v : Int) : IProp GF :=
  let bytes := UInt_bytes (wrapI min_UInt max_UInt v)
  iprop%
    ([∗list] i ↦ b ∈ List.ofFn bytes, Owned_UChar (l + i) b)
  ∗ ⌜ min_Int ≤ v ∧ v ≤ max_Int ⌝
def Owned_Long (l : Ptr) (v : Int) : IProp GF :=
  let bytes := ULong_bytes (wrapI min_ULong max_ULong v)
  iprop%
    ([∗list] i ↦ b ∈ List.ofFn bytes, Owned_UChar (l + i) b)
  ∗ ⌜ min_Long ≤ v ∧ v ≤ max_Long ⌝


-- 3, Array ownership

def Block (l : Ptr) : IProp GF := iprop% (l ↦ none) ∧ ⌜l ≠ 0⌝

def arrayshift (l : Ptr) (pos : Int) (size : Int) : Ptr := l + pos * size

def padding (l : Ptr) (n : Nat) : IProp GF :=
  match n with
  | 0 => l ↦ none
  | Nat.succ n' => iprop% (Block l ∗ padding (l + 1) n')


-- 4, Pointer non-null theorems
theorem ptr_nonnull {l : Ptr} {v : Int} :
  ⊢@{IProp GF} Owned_UChar l v → ⌜l ≠ 0⌝ :=
by
  unfold Owned_UChar
  iintro ⟨_ , ⟨HOwn, _⟩⟩; iframe

-- Owned integer pointers can't be null
theorem ptr_int_nonnull {l : Ptr} {v : Int} :
  ⊢@{IProp GF} Owned_Int l v → ⌜l ≠ 0⌝ :=
by
  unfold Owned_Int Owned_UChar
  iintro ⟨H , _⟩
  simp
  icases H with ⟨⟨_ , ⟨H , _⟩⟩ , _⟩; iframe

-- TODO: fill these in

-- 5, Equality theorems for ownership predicates

theorem Owned_UChar_eq {l : Ptr} {v v' : Int} :
  ⊢@{IProp GF} Owned_UChar l v -∗ Owned_UChar l v' -∗ ⌜v = v'⌝ :=
by
  unfold Owned_UChar min_UChar max_UChar
  iintro ⟨H1 , ⟨_ , ⟨%h1, %h1'⟩⟩⟩ ⟨H2 , ⟨_ , ⟨%h2 , %h2'⟩⟩⟩
  ihave %H := pointsTo_agree $$ [$]
  ipureintro; injection H with val_eq; lia

theorem Owned_Char_eq {l : Ptr} {v v' : Int} :
  ⊢@{IProp GF} Owned_Char l v -∗ Owned_Char l v' -∗ ⌜v = v'⌝ :=
by
  unfold Owned_Char min_Char max_Char
  iintro ⟨H1 , %H2⟩ ⟨H3 , %H4⟩
  ihave %HEq := Owned_UChar_eq $$ H1 H3
  ipureintro
  apply wrapI_Char_cong H2 H4 HEq

theorem Owned_UShort_eq {l : Ptr} {v v' : Int} :
  ⊢@{IProp GF} Owned_UShort l v -∗ Owned_UShort l v' -∗ ⌜v = v'⌝ :=
by
  unfold Owned_UShort min_UShort max_UShort
  iintro ⟨H1 , ⟨H2 , ⟨%H⟩⟩⟩ ⟨H5 , ⟨H6 , ⟨%H'⟩⟩⟩
  ihave %HEq := Owned_UChar_eq $$ H1 H5
  ihave %HEq' := Owned_UChar_eq $$ H2 H6
  ipureintro
  have Hbytes : UShort_bytes v = UShort_bytes v' := by
    funext i
    repeat refine Fin.lastCases ?_ ?_ i; lia; intro i
    apply Fin.elim0; assumption
  have H := UShort_eq H H' Hbytes
  assumption

theorem Owned_Short_eq {l : Ptr} {v v' : Int} :
  ⊢@{IProp GF} Owned_Short l v -∗ Owned_Short l v' -∗ ⌜v = v'⌝ :=
by
  unfold Owned_Short
  iintro ⟨H1 , ⟨H2 , %H⟩⟩ ⟨H3 , ⟨H4 , %H'⟩⟩
  ihave %HEq := Owned_UChar_eq $$ H1 H3
  ihave %HEq' := Owned_UChar_eq $$ H2 H4
  ipureintro
  have Hbytes : UShort_bytes (wrapI min_UShort max_UShort v) = UShort_bytes (wrapI min_UShort max_UShort v') := by
    funext i
    repeat refine Fin.lastCases ?_ ?_ i; lia; intro i
    apply Fin.elim0; assumption
  have Hv := wrapI_within_bounds (x := v) (min := min_UShort) (max := max_UShort) (by lia)
  have Hv' := wrapI_within_bounds (x := v') (min := min_UShort) (max := max_UShort) (by lia)
  have H1 := UShort_eq Hv Hv' Hbytes
  apply wrapI_Short_cong H H' H1

theorem Owned_UInt_eq {l : Ptr} {v v' : Int} :
  ⊢@{IProp GF} Owned_UInt l v -∗ Owned_UInt l v' -∗ ⌜v = v'⌝ :=
by
  unfold Owned_UInt
  iintro ⟨HOwn, %H⟩ ⟨HOwn', %H'⟩
  simp [-UInt_bytes]
  icases HOwn with ⟨H1 , ⟨H2 , ⟨H3 , ⟨H4 , _⟩⟩⟩⟩
  icases HOwn' with ⟨H1' , ⟨H2' , ⟨H3' , ⟨H4' , _⟩⟩⟩⟩
  ihave %H1 := Owned_UChar_eq $$ H1 H1'
  ihave %H2 := Owned_UChar_eq $$ H2 H2'
  ihave %H3 := Owned_UChar_eq $$ H3 H3'
  ihave %H4 := Owned_UChar_eq $$ H4 H4'
  ipureintro
  have Hbytes : UInt_bytes v = UInt_bytes v' := by
    funext i
    repeat refine Fin.lastCases ?_ ?_ i; lia; intro i
    apply Fin.elim0; assumption
  have H1 := UInt_eq H H' Hbytes
  assumption

theorem Owned_Int_eq {l : Ptr} {v v' : Int} :
  ⊢@{IProp GF} Owned_Int l v -∗ Owned_Int l v' -∗ ⌜v = v'⌝ :=
by
  unfold Owned_Int
  iintro ⟨HOwn, %H⟩ ⟨HOwn', %H'⟩
  simp [-UInt_bytes]
  icases HOwn with ⟨H1 , ⟨H2 , ⟨H3 , ⟨H4 , _⟩⟩⟩⟩
  icases HOwn' with ⟨H1' , ⟨H2' , ⟨H3' , ⟨H4' , _⟩⟩⟩⟩
  ihave %H1 := Owned_UChar_eq $$ H1 H1'
  ihave %H2 := Owned_UChar_eq $$ H2 H2'
  ihave %H3 := Owned_UChar_eq $$ H3 H3'
  ihave %H4 := Owned_UChar_eq $$ H4 H4'
  ipureintro
  have Hbytes : UInt_bytes (wrapI min_UInt max_UInt v) = UInt_bytes (wrapI min_UInt max_UInt v') := by
    funext i
    repeat refine Fin.lastCases ?_ ?_ i; lia; intro i
    apply Fin.elim0; assumption
  have Hv := wrapI_within_bounds (x := v) (min := min_UInt) (max := max_UInt) (by lia)
  have Hv' := wrapI_within_bounds (x := v') (min := min_UInt) (max := max_UInt) (by lia)
  have H1 := UInt_eq Hv Hv' Hbytes
  apply wrapI_Int_cong H H' H1

theorem Owned_ULong_eq {l : Ptr} {v v' : Int} :
  ⊢@{IProp GF} Owned_ULong l v -∗ Owned_ULong l v' -∗ ⌜v = v'⌝ :=
by
  unfold Owned_ULong
  iintro ⟨HOwn, %H⟩ ⟨HOwn', %H'⟩
  simp [-ULong_bytes]
  icases HOwn with ⟨H1 , ⟨H2 , ⟨H3 , ⟨H4 , HOwn⟩⟩⟩⟩
  icases HOwn with ⟨H5 , ⟨H6 , ⟨H7 , ⟨H8 , _⟩⟩⟩⟩
  icases HOwn' with ⟨H1' , ⟨H2' , ⟨H3' , ⟨H4' , HOwn'⟩⟩⟩⟩
  icases HOwn' with ⟨H5' , ⟨H6' , ⟨H7' , ⟨H8' , _⟩⟩⟩⟩
  ihave %H1 := Owned_UChar_eq $$ H1 H1'
  ihave %H2 := Owned_UChar_eq $$ H2 H2'
  ihave %H3 := Owned_UChar_eq $$ H3 H3'
  ihave %H4 := Owned_UChar_eq $$ H4 H4'
  ihave %H5 := Owned_UChar_eq $$ H5 H5'
  ihave %H6 := Owned_UChar_eq $$ H6 H6'
  ihave %H7 := Owned_UChar_eq $$ H7 H7'
  ihave %H8 := Owned_UChar_eq $$ H8 H8'
  ipureintro
  have Hbytes : ULong_bytes v = ULong_bytes v' := by
    funext i
    repeat refine Fin.lastCases ?_ ?_ i; lia; intro i
    apply Fin.elim0; assumption
  have H1 := ULong_eq H H' Hbytes
  assumption
