import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.relation_lattice_defs
import Submission.Work.BW.relation_lattice_Vrel_finrank_le_two

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The torsion-relation lattice and its weighted `ℓ¹`-norm

Structure theory for the torsion-relation lattice

`Γ = {y : Fin m → ℤ | IsOfFinOrder (∏ i, α i ^ (y i))}`

of a family `α : Fin m → K` in a number field, together with the weighted `ℓ¹`-norm
`F c y = ∑ i, |y i| · c i`.  Everything here is elementary (submodule/lattice algebra and real
arithmetic); the quantitative input (Waldschmidt's relation bound) lives elsewhere.
-/

namespace Work.BW

open Complex

variable {K : Type*} [Field K] [NumberField K]

/-- The torsion-relation lattice `Γ = {y | ∏ i, α i ^ (y i) ∈ μ(K)}` as a `ℤ`-submodule of `ℤ^m`. -/
def GammaSub {m : ℕ} (α : Fin m → K) (hα : ∀ i, α i ≠ 0) : Submodule ℤ (Fin m → ℤ) where
  carrier := {y | MuRelC α y}
  zero_mem' := MuRelC_zero α
  add_mem' := fun hy hz => MuRelC_add hα hy hz
  smul_mem' := fun k _ hy => MuRelC_smul hα k hy

@[simp] lemma mem_GammaSub {m : ℕ} {α : Fin m → K} {hα : ∀ i, α i ≠ 0} {y : Fin m → ℤ} :
    y ∈ GammaSub α hα ↔ MuRelC α y := Iff.rfl

/-- Membership in `Γ` is exactly `θ y ∈ 2πiℚ`. -/
lemma mem_GammaSub_iff_exists_rat {m : ℕ} (φ : K →+* ℂ) (α : Fin m → K)
    (hα : ∀ i, α i ≠ 0) (ℓ : Fin m → ℂ) (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i))
    (y : Fin m → ℤ) :
    y ∈ GammaSub α hα ↔ ∃ q : ℚ, thetaC ℓ y = (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) :=
  muRelC_iff_exists_rat φ α ℓ hℓ y

/-- `Γ` consists of the lattice points of the rational subspace `Vrel ℓ`. -/
lemma GammaSub_mem_Vrel {m : ℕ} (φ : K →+* ℂ) (α : Fin m → K) (hα : ∀ i, α i ≠ 0)
    (ℓ : Fin m → ℂ) (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i)) {y : Fin m → ℤ}
    (hy : y ∈ GammaSub α hα) : (fun i => (y i : ℚ)) ∈ Vrel ℓ :=
  (muRelC_iff_mem_Vrel φ α ℓ hℓ y).mp hy

section WNorm

/-- The weighted `ℓ¹`-norm `F c y = ∑ i, |y i| * c i` on exponent vectors. -/
noncomputable def wn {m : ℕ} (c : Fin m → ℝ) (y : Fin m → ℤ) : ℝ :=
  ∑ i, |(y i : ℝ)| * c i

lemma wn_nonneg {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (y : Fin m → ℤ) :
    0 ≤ wn c y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hc i)

@[simp] lemma wn_zero {m : ℕ} (c : Fin m → ℝ) : wn c 0 = 0 := by
  simp [wn]

lemma wn_neg {m : ℕ} (c : Fin m → ℝ) (y : Fin m → ℤ) : wn c (-y) = wn c y := by
  simp [wn]

lemma wn_smul {m : ℕ} (c : Fin m → ℝ) (a : ℤ) (y : Fin m → ℤ) :
    wn c (a • y) = |(a : ℝ)| * wn c y := by
  simp only [wn, Pi.smul_apply, smul_eq_mul, Int.cast_mul, abs_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma wn_add_le {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (y z : Fin m → ℤ) :
    wn c (y + z) ≤ wn c y + wn c z := by
  simp only [wn, Pi.add_apply, Int.cast_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ =>
    calc |(y i : ℝ) + (z i : ℝ)| * c i
        ≤ (|(y i : ℝ)| + |(z i : ℝ)|) * c i :=
          mul_le_mul_of_nonneg_right (abs_add_le _ _) (hc i)
      _ = |(y i : ℝ)| * c i + |(z i : ℝ)| * c i := by ring

lemma wn_sub_le {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (y z : Fin m → ℤ) :
    wn c (y - z) ≤ wn c y + wn c z := by
  have h := wn_add_le c hc y (-z)
  simpa [sub_eq_add_neg, wn_neg] using h

lemma wn_single_le {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (y : Fin m → ℤ)
    (i : Fin m) : |(y i : ℝ)| * c i ≤ wn c y :=
  Finset.single_le_sum (f := fun i => |(y i : ℝ)| * c i)
    (fun i _ => mul_nonneg (abs_nonneg _) (hc i)) (Finset.mem_univ i)

end WNorm

end Work.BW
