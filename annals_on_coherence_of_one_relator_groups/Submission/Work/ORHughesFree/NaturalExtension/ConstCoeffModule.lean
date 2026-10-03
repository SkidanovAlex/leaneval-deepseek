/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The module of constant coefficients of a submodule of `(R[t^{±1};τ])^m`

For `K ≤ (SkewL R)^m` a left `SkewL R`-submodule, `ctModule K ⊆ R^m` is the `R`-submodule
spanned by the vectors of degree-`0` coefficients of the elements of `K`, and `pctModule K` is
the same for the *polynomial* elements of `K`:

* `ctModule K = {x : Fin m → R | ∃ w ∈ K, ∀ j, x j = coeffElt (w j) 0}`;
* `pctModule K = {x : Fin m → R | ∃ w ∈ K, (∀ j k, k < 0 → coeffElt (w j) k = 0) ∧
    ∀ j, x j = coeffElt (w j) 0}`.

These are the "constant-term modules" of `K`; the whole point of the duality
`sup_const_left_add_sup_const_right` is the comparison of the module dimension of `pctModule K`
with that of `K` (the "matricial" form of [JZLA20, Proposition 7.2]).
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.subDimDefs
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular

set_option autoImplicit false
universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix

section CoeffLemmas

variable {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]

/-- Coefficient extraction is additive. -/
lemma coeffElt_add' (f g : SkewL U) (k : ℤ) :
    coeffElt (f + g) k = coeffElt f k + coeffElt g k := by simp [coeffElt]

/-- Coefficients of a scalar multiple (the `U`-module structure on `SkewL U` is coefficientwise
multiplication). -/
lemma coeffElt_smul' (c : U) (f : SkewL U) (k : ℤ) :
    coeffElt (c • f) k = c * coeffElt f k := by simp [coeffElt]

/-- The `U`-scalar action on `SkewL U` is left multiplication by the corresponding constant. -/
lemma smul_eq_single_mul' (c : U) (f : SkewL U) :
    c • f = SkewMonoidAlgebra.single (1 : Multiplicative ℤ) c * f := by
  ext g
  simp [SkewMonoidAlgebra.smul_single, SkewMonoidAlgebra.single_mul_single]

end CoeffLemmas

variable {R : Type u} [Ring R] [VonNeumannRegularRing R] [MulSemiringAction (Multiplicative ℤ) R]

/-- The `R`-submodule of `R^m` of vectors of degree-`0` coefficients of elements of `K`. -/
def ctModule {m : ℕ} (K : Submodule (SkewL R) (Fin m → SkewL R)) : Submodule R (Fin m → R) where
  carrier := {x | ∃ w ∈ K, ∀ j, x j = coeffElt (w j) 0}
  zero_mem' := ⟨0, K.zero_mem, by intro j; simp [coeffElt]⟩
  add_mem' := by
    rintro x y ⟨w, hw, hx⟩ ⟨w', hw', hy⟩
    refine ⟨w + w', K.add_mem hw hw', ?_⟩
    intro j
    show x j + y j = coeffElt (w j + w' j) 0
    rw [hx j, hy j, coeffElt_add']
  smul_mem' := by
    rintro c x ⟨w, hw, hx⟩
    refine ⟨c • w, ?_, ?_⟩
    · have h : c • w = (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) c) • w := by
        funext j; exact smul_eq_single_mul' c (w j)
      rw [h]; exact K.smul_mem _ hw
    · intro j
      show c * x j = coeffElt (c • (w j)) 0
      rw [hx j, coeffElt_smul']

/-- The `R`-submodule of `R^m` of vectors of degree-`0` coefficients of *polynomial* elements
of `K`. -/
def pctModule {m : ℕ} (K : Submodule (SkewL R) (Fin m → SkewL R)) : Submodule R (Fin m → R) where
  carrier := {x | ∃ w ∈ K, (∀ j, ∀ k : ℤ, k < 0 → coeffElt (w j) k = 0) ∧ ∀ j, x j = coeffElt (w j) 0}
  zero_mem' := ⟨0, K.zero_mem, by intro j k _; simp [coeffElt], by intro j; simp [coeffElt]⟩
  add_mem' := by
    rintro x y ⟨w, hw, hpx, hx⟩ ⟨w', hw', hpx', hx'⟩
    refine ⟨w + w', K.add_mem hw hw', ?_, ?_⟩
    · intro j k hk
      rw [Pi.add_apply, coeffElt_add', hpx j k hk, hpx' j k hk, add_zero]
    · intro j
      show x j + y j = coeffElt (w j + w' j) 0
      rw [hx j, hx' j, coeffElt_add']
  smul_mem' := by
    rintro c x ⟨w, hw, hpx, hx⟩
    refine ⟨c • w, ?_, ?_, ?_⟩
    · have h : c • w = (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) c) • w := by
        funext j; exact smul_eq_single_mul' c (w j)
      rw [h]; exact K.smul_mem _ hw
    · intro j k hk
      show coeffElt (c • (w j)) k = 0
      rw [coeffElt_smul', hpx j k hk, mul_zero]
    · intro j
      show c * x j = coeffElt (c • (w j)) 0
      rw [hx j, coeffElt_smul']

/-- The *row module* of a matrix `A : n × m` over `SkewL R`: the image of `v ↦ v ᵥ* A`. -/
noncomputable def rowModule {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL R)) :
    Submodule (SkewL R) (Fin m → SkewL R) :=
  LinearMap.range A.vecMulLinear

/-- `ctModule` is monotone. -/
theorem ctModule_mono {m : ℕ} {K K' : Submodule (SkewL R) (Fin m → SkewL R)} (h : K ≤ K') :
    ctModule K ≤ ctModule K' := by
  rintro x ⟨w, hw, hx⟩
  exact ⟨w, h hw, hx⟩

/-- `pctModule` is monotone. -/
theorem pctModule_mono {m : ℕ} {K K' : Submodule (SkewL R) (Fin m → SkewL R)} (h : K ≤ K') :
    pctModule K ≤ pctModule K' := by
  rintro x ⟨w, hw, hp, hx⟩
  exact ⟨w, h hw, hp, hx⟩

end Work.ORHughesFree.NaturalExtension
