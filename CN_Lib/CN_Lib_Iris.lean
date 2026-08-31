import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Adequacy
import Iris.ProgramLogic.Lifting
import Iris.BI.Lib.GenHeap
import Iris.Std.GenSetsInstances
import Iris.ProofMode
import Std.Data.ExtTreeMap

open Iris ProgramLogic Language.Notation Std FromMathlib

namespace CN_Lib

-- Library for things needed by CN lemma exports.

-- 1, Resource algebra for heaps that are maps from integers
--  to integers. Nothing fancy and copied from HeapLang.

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


-- 2, Now we add basic CN-style ownership predicates.

-- Placeholder for int to bytes conversion
abbrev byte := Int × Int × Int × Int
def int_to_bytes (v : Int) : byte := sorry

-- Generic ownership
def Owned (l : Ptr) (v : Int) : IProp GF := iprop% (l ↦ some v) ∧ ⌜l ≠ 0⌝
def Block (l : Ptr) : IProp GF := iprop% (l ↦ none) ∧ ⌜l ≠ 0⌝

-- Ownership of C types
def Owned_char (l : Ptr) (v : Int) : IProp GF := Owned l v
def Owned_int (l : Ptr) (v : Int) : IProp GF :=
  let (b1, b2, b3, b4) := int_to_bytes v
    iprop% Owned l b1
    ∗ Owned (l + 1) b2
    ∗ Owned (l + 2) b3
    ∗ Owned (l + 3) b4
-- TODO: more C types, e.g. struct, array, etc.

-- 3, Array ownership

-- Arrayshift
def arrayshift (l : Ptr) (pos : Int) (size : Int) : Ptr := l + pos * size
def padding (l : Ptr) (n : Nat) : IProp GF :=
  match n with
  | 0 => l ↦ none
  | Nat.succ n' => iprop% (Block l ∗ padding (l + 1) n')


-- 4, Useful lemmas

-- Owned pointers can't be null
theorem ptr_nonnull {l : Ptr} {v : Int} :
  ⊢@{IProp GF} Owned l v → ⌜l ≠ 0⌝ :=
by
  unfold Owned
  iintro ⟨_ , HOwn⟩; iframe

-- Owned integer pointers can't be null
theorem ptr_int_nonnull {l : Ptr} {v : Int} :
  ⊢@{IProp GF} Owned_int l v → ⌜l ≠ 0⌝ :=
by
  unfold Owned_int Owned
  iintro ⟨⟨ _ , H⟩ , _⟩; iframe

-- Two owned pointers must be different
theorem owned_neq {l l' : Ptr} {v v' : Int} :
  ⊢@{IProp GF} Owned l v -∗ Owned l' v' -∗ ⌜l ≠ l'⌝ :=
by
  unfold Owned
  iintro ⟨H1 , _⟩ ⟨H2 , _⟩
  iapply pointsTo_ne $$ H1 H2

-- Two owned char pointers must be different
theorem owned_char_neq {l l' : Ptr} {v v' : Int} :
  ⊢@{IProp GF} Owned_char l v -∗ Owned_char l' v' -∗ ⌜l ≠ l'⌝ :=
by
  unfold Owned_char
  iintro H1 H2
  iapply owned_neq $$ H1 H2

-- Two owned int pointers must be different
theorem owned_int_neq {l l' : Ptr} {v v' : Int} :
  ⊢@{IProp GF} Owned_int l v -∗ Owned_int l' v' -∗ ⌜l ≠ l'⌝ :=
by
  unfold Owned_int; simp
  iintro ⟨H1 , _⟩ ⟨H2 , _⟩
  iapply owned_neq $$ H1 H2

-- Two copies of ownership of the same pointer must have the same value
theorem owned_eq {l : Ptr} {v v' : Int} :
  ⊢@{IProp GF} Owned l v -∗ Owned l v' -∗ ⌜v = v'⌝ :=
by
  unfold Owned
  iintro ⟨H1 , _⟩ ⟨H2 , _⟩
  ihave %H := pointsTo_agree $$ [$]
  ipureintro; injection H; omega

-- Two copies of ownership of the same char pointer must have the same value
theorem owned_char_eq {l : Ptr} {v v' : Int} :
  ⊢@{IProp GF} Owned_char l v -∗ Owned_char l v' -∗ ⌜v = v'⌝ :=
by
  unfold Owned_char
  iintro H1 H2
  iapply owned_eq $$ H1 H2

-- Two copies of ownership of the same int pointer must have the same value
theorem owned_int_eq {l : Ptr} {v v' : Int} :
  ⊢@{IProp GF} Owned_int l v -∗ Owned_int l v' -∗ ⌜v = v'⌝ :=
by
  sorry
-- TODO: Omitted until int_to_bytes is implemented

end CN_Lib
