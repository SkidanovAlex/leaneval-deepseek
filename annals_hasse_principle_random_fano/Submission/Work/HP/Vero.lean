import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs

/-!
# Auxiliary definitions for the Veronese-key node (N04)

This file is owned by the `veronese_key` author.  It introduces

* `orthLat`, the lattice of integral vectors orthogonal to a sublattice of `ℤ^ι`;
* `IsSat`, the saturation condition;
* `realify`, the change of scalars `ℤ^ι → ℝ^ι`;
* `dualLat`, the dual lattice (inside its real span) of a `ℤ`-lattice in `ℝ^ι`;
* `lamR`, the successive minima of such a lattice with respect to the Euclidean norm.

Everything here is meant to be imported by the delegated lemmas that feed into
`Work.HP.veronese_key`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP

variable {ι : Type*} [Fintype ι]


/-- A sublattice of `ℤ^ι` is saturated when the quotient is torsion free. -/
def IsSat (L : Submodule ℤ (ι → ℤ)) : Prop :=
  ∀ y : ι → ℤ, (∃ n : ℤ, n ≠ 0 ∧ n • y ∈ L) → y ∈ L

/-- The change of scalars `ℤ^ι → ℝ^ι`. -/
def intCastPi : (ι → ℤ) →ₗ[ℤ] (ι → ℝ) where
  toFun v := fun i => (v i : ℝ)
  map_add' := by
    intro a b
    ext i
    simp
  map_smul' := by
    intro c a
    ext i
    simp

/-- The realification of an integral lattice. -/
def realify (L : Submodule ℤ (ι → ℤ)) : Submodule ℤ (ι → ℝ) := L.map intCastPi

@[simp] theorem intCastPi_apply {v : ι → ℤ} (i : ι) : (intCastPi v) i = (v i : ℝ) := rfl

/-- The dual lattice of `L ⊆ ℝ^ι`, inside its real span: the vectors of `span L` pairing
integrally with every element of `L`. -/
def dualLat (L : Submodule ℤ (ι → ℝ)) : Submodule ℤ (ι → ℝ) where
  carrier := {y | y ∈ Submodule.span ℝ (L : Set (ι → ℝ)) ∧ ∀ z ∈ L, ∃ k : ℤ, ∑ i, y i * z i = k}
  zero_mem' := ⟨Submodule.zero_mem _, fun z _ => ⟨0, by simp⟩⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨Submodule.add_mem _ ha1 hb1, fun z hz => ?_⟩
    obtain ⟨ka, hka⟩ := ha2 z hz
    obtain ⟨kb, hkb⟩ := hb2 z hz
    exact ⟨ka + kb, by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hka, hkb]
      norm_num⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    have hmem : c • a ∈ Submodule.span ℝ (L : Set (ι → ℝ)) := by
      rw [show c • a = (c : ℝ) • a from by ext i; simp [zsmul_eq_mul]]
      exact Submodule.smul_mem _ (c : ℝ) ha1
    refine ⟨hmem, fun z hz => ?_⟩
    obtain ⟨k, hk⟩ := ha2 z hz
    exact ⟨c * k, by
      have h1 : (∑ i, (c • a) i * z i) = (c : ℝ) * ∑ i, a i * z i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.smul_apply, zsmul_eq_mul]; ring)
      rw [h1, hk, Int.cast_mul]⟩

/-- Successive minima of a lattice in `ι → ℝ` with respect to the Euclidean norm. -/
def lamR (L : Submodule ℤ (ι → ℝ)) (i : ℕ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (ι → ℝ),
    (∀ j, f j ∈ L) ∧ LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r}

/-- The rank of an integral lattice. -/
abbrev rkZ (L : Submodule ℤ (ι → ℤ)) : ℕ := Module.finrank ℤ L

end Work.HP
