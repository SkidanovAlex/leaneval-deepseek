import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.Spaces.GammaW_Prelim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Auxiliary definitions for the proof that `Γ(θ)·z/(1+z)²` belongs to `𝒲^{l,∞}`
uniformly in `α ∈ (0,1]` (the paper's Proposition "ΓRegularity").
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- The angular coefficient `q(θ) = cos(2θ) - 1/3 = (2/3)·(cos²θ - 2 sin²θ)`.
It is the logarithmic angular derivative of `Γ`: on `(0, π/2)`,
`D_θ Γ = α · q · Γ`. -/
noncomputable def qfun (θ : ℝ) : ℝ := Real.cos (2 * θ) - 1/3

/-- Univariate version of `D_θ`: `dthU φ = sin(2θ) · φ'`. -/
noncomputable def dthU (φ : ℝ → ℝ) : ℝ → ℝ := fun θ => Real.sin (2 * θ) * deriv φ θ

/-- The coefficient sequence with `D_θ^{j+1} Γ = α · Tfun j α · Γ` (on `(0,π/2)`),
defined by `Tfun 0 = q` and `Tfun (j+1) = D_θ (Tfun j) + α · q · Tfun j`. -/
noncomputable def Tfun : ℕ → ℝ → ℝ → ℝ
  | 0, _α, θ => qfun θ
  | (j + 1), α, θ => Real.sin (2 * θ) * deriv (fun t => Tfun j α t) θ
      + α * qfun θ * Tfun j α θ

/-- The radial factor `z ↦ z/(1+z)²`. -/
noncomputable def hKer (z : ℝ) : ℝ := z / (1 + z) ^ 2

@[simp] theorem qfun_apply (θ : ℝ) : qfun θ = Real.cos (2 * θ) - 1/3 := rfl
@[simp] theorem dthU_apply (φ : ℝ → ℝ) (θ : ℝ) : dthU φ θ = Real.sin (2 * θ) * deriv φ θ := rfl
@[simp] theorem Tfun_zero (α θ : ℝ) : Tfun 0 α θ = qfun θ := rfl
theorem Tfun_succ (j : ℕ) (α θ : ℝ) :
    Tfun (j + 1) α θ = Real.sin (2 * θ) * deriv (fun t => Tfun j α t) θ
      + α * qfun θ * Tfun j α θ := rfl
@[simp] theorem hKer_apply (z : ℝ) : hKer z = z / (1 + z) ^ 2 := rfl

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.HkSq_terms =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- The second (mixed, `i ≥ 1`) sum inside `HkIntegrand` is nonnegative. -/
theorem hkMixedSum_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (mixed j i f z θ * Wt α z θ) ^ 2 else 0 :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl 0

/-- The first (pure `D_z`) sum inside `HkIntegrand` is nonnegative. -/
theorem hkZSum_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ ∑ i ∈ Finset.range (k + 1),
        (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- A single `D_z`-term of `HkIntegrand` is bounded by the whole integrand. -/
theorem sq_le_HkIntegrand_z (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) (i : ℕ) (hi : i ≤ k) :
    (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
      ≤ HkIntegrand α k f z θ := by
  have hmem : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  have h1 : (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
      ≤ ∑ a ∈ Finset.range (k + 1),
          (DzIter a f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 :=
    Finset.single_le_sum
      (f := fun a => (DzIter a f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
      (fun a _ => sq_nonneg _) hmem
  rw [HkIntegrand]
  exact le_trans h1 (le_add_of_nonneg_right (hkMixedSum_nonneg α k f z θ))

/-- A single mixed term of `HkIntegrand` is bounded by the whole integrand. -/
theorem sq_le_HkIntegrand_mixed (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ)
    (i j : ℕ) (hi1 : 1 ≤ i) (hij : i + j ≤ k) :
    (mixed j i f z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α k f z θ := by
  have hmi : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega))
  have hmj : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega))
  have hinner : (if 1 ≤ i ∧ i + j ≤ k then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
      ≤ ∑ b ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + b ≤ k then (mixed b i f z θ * Wt α z θ) ^ 2 else 0) :=
    Finset.single_le_sum
      (f := fun b => if 1 ≤ i ∧ i + b ≤ k then (mixed b i f z θ * Wt α z θ) ^ 2 else 0)
      (fun b _ => by split_ifs with h <;> simp [sq_nonneg]) hmj
  rw [if_pos ⟨hi1, hij⟩] at hinner
  have houter : (∑ b ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + b ≤ k then (mixed b i f z θ * Wt α z θ) ^ 2 else 0))
      ≤ ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
          (if 1 ≤ a ∧ a + b ≤ k then (mixed b a f z θ * Wt α z θ) ^ 2 else 0) :=
    Finset.single_le_sum
      (f := fun a => ∑ b ∈ Finset.range (k + 1),
        if 1 ≤ a ∧ a + b ≤ k then (mixed b a f z θ * Wt α z θ) ^ 2 else 0)
      (fun a _ => Finset.sum_nonneg fun b _ => by split_ifs with h <;> simp [sq_nonneg]) hmi
  rw [HkIntegrand]
  exact le_trans hinner (le_trans houter (le_add_of_nonneg_left (hkZSum_nonneg α k f z θ)))

/-- The `L²`-square of the weighted `i`-th pure `D_z`-derivative is bounded by `HkSq`. -/
theorem L2Sq_DzIter_le_HkSq (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hmem : HkMem α k g)
    (i : ℕ) (hi : i ≤ k) :
    L2Sq (fun z θ => DzIter i g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ≤
      HkSq α k g := by
  rw [L2Sq, HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hmem.2 ?_
  show ∀ᵐ z ∂(volume.restrict Iz),
    (∫ θ in Iθ, (DzIter i g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
      ≤ ∫ θ in Iθ, HkIntegrand α k g z θ
  exact MeasureTheory.ae_restrict_of_forall_mem (show MeasurableSet Iz from measurableSet_Ici)
    fun z hz => MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 z hz)
      (Eventually.of_forall fun θ => sq_le_HkIntegrand_z α k g z θ i hi)

/-- The `L²`-square of a weighted mixed derivative is bounded by `HkSq`. -/
theorem L2Sq_mixed_le_HkSq (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (hmem : HkMem α k g)
    (i j : ℕ) (hi1 : 1 ≤ i) (hij : i + j ≤ k) :
    L2Sq (fun z θ => mixed j i g z θ * Wt α z θ) ≤ HkSq α k g := by
  rw [L2Sq, HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hmem.2 ?_
  show ∀ᵐ z ∂(volume.restrict Iz),
    (∫ θ in Iθ, (mixed j i g z θ * Wt α z θ) ^ 2)
      ≤ ∫ θ in Iθ, HkIntegrand α k g z θ
  exact MeasureTheory.ae_restrict_of_forall_mem (show MeasurableSet Iz from measurableSet_Ici)
    fun z hz => MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 z hz)
      (Eventually.of_forall fun θ => sq_le_HkIntegrand_mixed α k g z θ i j hi1 hij)

end Work.Spaces
end
end
