/-
  AMO-Lean: GF(2) Field Implementation
  The binary field: {0, 1} with XOR as addition and AND as multiplication.

  GF(2) is the smallest finite field. Characteristic 2.
  - Addition: XOR (a ⊕ b)
  - Multiplication: AND (a ∧ b)
  - Negation: identity (-a = a in char 2)
  - Inverse: identity (only 1 is nonzero, 1⁻¹ = 1)

  Used for Morton bit-interleaving and branchless comparison masks
  in the BVH spatial oracle pipeline.
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Defs

namespace AmoLean.Field.GF2

/-! ## Part 1: GF(2) Field Type -/

/-- GF(2) field element: a single bit. -/
structure GF2Field where
  value : Bool
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace GF2Field

/-- Zero element (false) -/
def zero : GF2Field := ⟨false⟩

/-- One element (true) -/
def one : GF2Field := ⟨true⟩

/-! ## Part 2: Core Arithmetic -/

/-- Addition: XOR -/
def add (a b : GF2Field) : GF2Field := ⟨xor a.value b.value⟩

/-- Multiplication: AND -/
def mul (a b : GF2Field) : GF2Field := ⟨a.value && b.value⟩

/-- Negation: identity (char 2) -/
def neg (a : GF2Field) : GF2Field := a

/-- Subtraction = addition in char 2 -/
def sub (a b : GF2Field) : GF2Field := add a b

/-- Inverse: 0⁻¹ = 0 (sentinel), 1⁻¹ = 1 -/
def inv (a : GF2Field) : GF2Field := a

/-- Natural number coercion -/
def ofNat (n : Nat) : GF2Field := ⟨n % 2 == 1⟩

/-- To natural number -/
def toNat (a : GF2Field) : Nat := if a.value then 1 else 0

/-! ## Part 3: Algebraic Properties -/

-- All proofs by exhaustive Bool case split (2 or 4 or 8 cases).
-- Pattern: unfold defs, split on all Bool values, each case is rfl.

@[ext]
theorem ext {a b : GF2Field} (h : a.value = b.value) : a = b := by
  cases a; cases b; simp_all

private theorem bool2 (P : GF2Field → Prop) (h0 : P ⟨false⟩) (h1 : P ⟨true⟩) :
    ∀ a, P a := fun ⟨b⟩ => b.casesOn h0 h1

theorem add_comm : ∀ a b : GF2Field, add a b = add b a :=
  bool2 _ (bool2 _ rfl rfl) (bool2 _ rfl rfl)
theorem add_assoc : ∀ a b c : GF2Field, add (add a b) c = add a (add b c) :=
  bool2 _ (bool2 _ (bool2 _ rfl rfl) (bool2 _ rfl rfl))
    (bool2 _ (bool2 _ rfl rfl) (bool2 _ rfl rfl))
theorem add_zero : ∀ a : GF2Field, add a zero = a := bool2 _ rfl rfl
theorem zero_add : ∀ a : GF2Field, add zero a = a := bool2 _ rfl rfl
theorem add_neg : ∀ a : GF2Field, add a (neg a) = zero := bool2 _ rfl rfl
theorem mul_comm : ∀ a b : GF2Field, mul a b = mul b a :=
  bool2 _ (bool2 _ rfl rfl) (bool2 _ rfl rfl)
theorem mul_assoc : ∀ a b c : GF2Field, mul (mul a b) c = mul a (mul b c) :=
  bool2 _ (bool2 _ (bool2 _ rfl rfl) (bool2 _ rfl rfl))
    (bool2 _ (bool2 _ rfl rfl) (bool2 _ rfl rfl))
theorem mul_one : ∀ a : GF2Field, mul a one = a := bool2 _ rfl rfl
theorem one_mul : ∀ a : GF2Field, mul one a = a := bool2 _ rfl rfl
theorem mul_zero : ∀ a : GF2Field, mul a zero = zero := bool2 _ rfl rfl
theorem zero_mul : ∀ a : GF2Field, mul zero a = zero := bool2 _ rfl rfl
theorem left_distrib : ∀ a b c : GF2Field, mul a (add b c) = add (mul a b) (mul a c) :=
  bool2 _ (bool2 _ (bool2 _ rfl rfl) (bool2 _ rfl rfl))
    (bool2 _ (bool2 _ rfl rfl) (bool2 _ rfl rfl))
theorem right_distrib : ∀ a b c : GF2Field, mul (add a b) c = add (mul a c) (mul b c) :=
  bool2 _ (bool2 _ (bool2 _ rfl rfl) (bool2 _ rfl rfl))
    (bool2 _ (bool2 _ rfl rfl) (bool2 _ rfl rfl))

/-! ## Part 4: Characteristic-2 identities (E-graph rules) -/

/-- a + a = 0 in GF(2) (XOR self-cancellation) -/
theorem add_self : ∀ a : GF2Field, add a a = zero := bool2 _ rfl rfl

/-- a * a = a in GF(2) (AND idempotence) -/
theorem mul_self : ∀ a : GF2Field, mul a a = a := bool2 _ rfl rfl

/-! ## Part 5: CommRing instance -/

instance : Zero GF2Field := ⟨zero⟩
instance : One GF2Field := ⟨one⟩
instance : Add GF2Field := ⟨add⟩
instance : Mul GF2Field := ⟨mul⟩
instance : Neg GF2Field := ⟨neg⟩
instance : Sub GF2Field := ⟨sub⟩

instance : NatCast GF2Field := ⟨ofNat⟩
instance : IntCast GF2Field := ⟨fun
  | .ofNat n => ofNat n
  | .negSucc n => neg (ofNat (n + 1))⟩

instance : CommRing GF2Field where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_comm := mul_comm
  neg_add_cancel a := add_neg a
  nsmul := nsmulRec
  zsmul := zsmulRec
  natCast_zero := rfl
  natCast_succ n := by
    simp only [NatCast.natCast, GF2Field.ofNat, GF2Field.add, GF2Field.one]
    apply GF2Field.ext
    show ((n + 1) % 2 == 1) = xor (n % 2 == 1) true
    have h := Nat.mod_two_eq_zero_or_one n
    have hs := Nat.mod_two_eq_zero_or_one (n + 1)
    rcases h with h | h <;> rcases hs with hs | hs <;> simp_all <;> omega
  intCast_ofNat _ := rfl
  intCast_negSucc n := by
    simp only [IntCast.intCast, neg, ofNat]
    rfl

end GF2Field
end AmoLean.Field.GF2
