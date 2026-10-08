import Mathlib
import Submission.Work.BSLit.Defs
import Submission.Work.Models.Port.Sz.Basic
import Submission.Work.Models.Port.Sz.Weyl
import Submission.Work.Models.Port.Sz.Involutions
import Submission.Work.Models.Port.Sz.TwoTransitive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSLit.BenderFacts2.Facts2SzDefs` — small vocabulary for the Suzuki clause of
`BenderModelFacts2Prop`

This module records the two elements of the Suzuki model `SzModel n` (`n ≥ 1`,
`SzModel n = Sz(2^(2n+1)) ⊆ GL(4, GF(2^(2n+1)))`) that the Suzuki leaf of
`BenderModelFacts2Prop` is built from:

* `szUgS n a b` — the root element `u(a,b)` of the Suzuki `2`-group, viewed inside `SzModel n`;
* `szWgMS n` — the Weyl element `w`, viewed inside `SzModel n`.

and the elementary facts relating them (`orderOf`, the parametrisation of the involutions of
the Suzuki `2`-group, `2`-elements of the Borel).

The point of collecting them here is that both the main leaf
(`Work.BSLit.BenderFacts2.sz_benderModelFacts2`) and the auxiliary lemmas it consumes can be
stated against these definitions without dragging in the whole ream of existing Suzuki modules.
-/

set_option autoImplicit false

namespace Work.BSLit.BenderFacts2

open LeanEval.GroupTheory.Defs

/-- The Weyl element `w` of `Sz(2^(2n+1))`, as a member of `SzModel n`. -/
noncomputable abbrev szWgMS (n : ℕ) : SzModel n := Submission.Sz.szWgM n

/-- The root element `u(a,b)` of the Suzuki `2`-group, as a member of `SzModel n`. -/
noncomputable def szUgS (n : ℕ) (a b : Submission.Sz.SzField n) : SzModel n :=
  ⟨Submission.Sz.szUg n a b, Submission.Sz.szUg_mem_szModel n a b⟩

@[simp] lemma szUgS_coe (n : ℕ) (a b : Submission.Sz.SzField n) :
    ((szUgS n a b : SzModel n) : GL (Fin 4) (Submission.Sz.SzField n)) =
      Submission.Sz.szUg n a b := rfl

lemma szUgS_zero (n : ℕ) : szUgS n 0 0 = (1 : SzModel n) := by
  apply Subtype.ext
  rw [szUgS_coe, Subgroup.coe_one, Submission.Sz.szUg_zero]

lemma szUgS_inv (n : ℕ) (a b : Submission.Sz.SzField n) :
    (szUgS n a b)⁻¹ = szUgS n a (b + a ^ (1 + 2 ^ (n + 1))) := by
  apply Subtype.ext
  rw [Subgroup.coe_inv, szUgS_coe, szUgS_coe]
  exact (Submission.Sz.szUg_inv n a b).symm

lemma szUgS_mul (n : ℕ) (a b c d : Submission.Sz.SzField n) :
    szUgS n a b * szUgS n c d
      = szUgS n (a + c) (b + d + a * c ^ (2 ^ (n + 1))) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, szUgS_coe, szUgS_coe, szUgS_coe]
  exact Submission.Sz.szUg_mul n a b c d

lemma szUgS_mem_U (n : ℕ) (a b : Submission.Sz.SzField n) :
    szUgS n a b ∈ Submission.Sz.szTwoGroupS n :=
  Subgroup.mem_subgroupOf.mpr ⟨a, b, rfl⟩

/-- A root element `u(0,b)` with `b ≠ 0` is an involution. -/
lemma orderOf_szUgS_zero (n : ℕ) {b : Submission.Sz.SzField n} (hb : b ≠ 0) :
    orderOf (szUgS n 0 b) = 2 := by
  refine orderOf_eq_prime_iff.mpr ⟨?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, szUgS_coe, Subgroup.coe_one, Submission.Sz.szUg_sq,
      zero_pow (by positivity), Submission.Sz.szUg_zero]
  · intro h
    have h1 : Submission.Sz.szUg n 0 b = 1 := by
      have := congrArg (fun z : SzModel n =>
        (z : GL (Fin 4) (Submission.Sz.SzField n))) h
      simpa [szUgS_coe] using this
    have h2 : ((0 : Submission.Sz.SzField n), b) = ((0 : Submission.Sz.SzField n), 0) :=
      Submission.Sz.szUg_injective n (by
        show Submission.Sz.szUg n 0 b = Submission.Sz.szUg n 0 0
        rw [h1, Submission.Sz.szUg_zero])
    exact hb (Prod.ext_iff.mp h2).2

/-- The square of a root element inside `SzModel n`. -/
lemma szUgS_sq (n : ℕ) (a b : Submission.Sz.SzField n) :
    (szUgS n a b) ^ 2 = szUgS n 0 (a ^ (1 + 2 ^ (n + 1))) := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, szUgS_coe, szUgS_coe]
  exact Submission.Sz.szUg_sq n a b

/-- The involutions of the Suzuki `2`-group are the elements `u(0,b)`, `b ≠ 0`. -/
lemma szUgS_sq_eq_one_iff (n : ℕ) (a b : Submission.Sz.SzField n) :
    (szUgS n a b) ^ 2 = 1 ↔ a = 0 := by
  constructor
  · intro h
    have h' : (Submission.Sz.szUg n a b) ^ 2 = 1 := by
      have h2 := congrArg (fun z : SzModel n =>
        (z : GL (Fin 4) (Submission.Sz.SzField n))) h
      simpa [szUgS_coe, Subgroup.coe_pow, Subgroup.coe_one] using h2
    exact (Submission.Sz.szUg_sq_eq_one_iff n a b).mp h'
  · intro ha
    have h'' : (Submission.Sz.szUg n a b) ^ 2 = 1 :=
      (Submission.Sz.szUg_sq_eq_one_iff n a b).mpr ha
    apply Subtype.ext
    rw [Subgroup.coe_pow, szUgS_coe, Subgroup.coe_one]
    exact h''

end Work.BSLit.BenderFacts2
