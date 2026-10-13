/-
# `Work.H2.T1Q.SlotOpen` — the pairing lemma with an *open-quadrant* bound on the `f`-factor

The generic Cauchy–Schwarz pairing bound of the template
`Submission/Work/FTS/H2/T1EasyBound.lean` (`Work.FTS.H2.term_of_slot`) asks its "`V`-factor" to be
bounded by `K` on the **closed** quadrant `Iz × Iθ`.  In the *interior* class
`Work.FTS.LocData.SmoothQuad` — the class of the target `Work.H2.T1Q.EasyBoundQ` — the only
available bounds (`|mixed b a f| ≤ Kf`, `|mixed b a g| ≤ Kg` for `a + b ≤ 2`) hold on the
**open** quadrant `0 < z`, `0 < θ < π/2`; nothing constrains the values on the boundary lines
`θ = 0`, `θ = π/2`, where the weights `Whz = w/sin(2θ)^{η/2}` and `Wm = w/sin(2θ)^{γ/2}` are
`0` (Lean's `0^{-c} = 0`).

This file provides the two ingredients that every per-summand estimate of the interior class
needs:

* `ae_pm_theta_mem_Ioo` — `pm` (the product of the two restricted Lebesgue measures) is carried
  by the open angular interval, so modifying a function on the boundary lines does not change
  its integrals;
* `term_of_slot_open` — `Work.FTS.H2.term_of_slot` with the hypothesis `|V| ≤ K` only on the
  open quadrant.  The proof replaces `V` by its truncation `V' = V · 1_{(0,π/2)}(θ)`, which does
  satisfy the closed-quadrant bound and agrees with `V` almost everywhere;
* `aesm_prod_three_qd` — the interior-class replacement of the template's
  `Work.FTS.H2.aesm_prod_three` (`SmoothQuad` factors and continuous weights).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.H2.T1EasyBound
import Submission.Work.FTS.H2.HQ.Glue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 800000

open Work.FTS.H2

/-! ## `pm` is carried by the open quadrant -/

/-- Almost every point of the product measure `pm` has its angular coordinate in the *open*
interval `(0, π/2)`: the boundary lines `θ = 0` and `θ = π/2` are null for `pm`. -/
theorem ae_pm_theta_mem_Ioo : ∀ᵐ p ∂pm, p.2 ∈ Set.Ioo 0 (π / 2) := by
  rw [MeasureTheory.ae_iff]
  have hset : {p : ℝ × ℝ | ¬ p.2 ∈ Set.Ioo 0 (π / 2)}
      = Set.univ ×ˢ (Set.Ioo 0 (π / 2))ᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, true_and]
  rw [hset, pm, MeasureTheory.Measure.prod_prod]
  have hS : (volume.restrict Work.Spaces.Iθ) (Set.Ioo 0 (π / 2))ᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo.compl]
    have hsub : (Set.Ioo 0 (π / 2))ᶜ ∩ Work.Spaces.Iθ ⊆ ({0, π / 2} : Set ℝ) := by
      intro θ hθ
      rw [Set.mem_inter_iff, Set.mem_compl_iff] at hθ
      obtain ⟨hn, hI⟩ := hθ
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hI
      rw [Set.mem_Ioo] at hn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases le_or_gt θ 0 with h | h
      · exact Or.inl (le_antisymm h hI.1)
      · exact Or.inr (le_antisymm hI.2 (not_lt.mp (not_and.mp hn h)))
    refine MeasureTheory.measure_mono_null hsub ?_
    exact Set.Finite.measure_zero (by simp : ({0, π / 2} : Set ℝ).Finite) volume
  rw [hS, mul_zero]

/-! ## Continuity of the two weights on the open quadrant -/

/-- The `η`-weight `Whz z θ = w z / sin(2θ)^{η/2}` is continuous on the open quadrant. -/
theorem continuousOn_Whz_quad :
    ContinuousOn (fun p : ℝ × ℝ => Whz p.1 p.2) Work.FTS.H2.HQ.quadQ := by
  have hfun : (fun p : ℝ × ℝ => Whz p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) := rfl
  rw [hfun]
  exact Work.FTS.H2.HQ.continuousOn_light_quad

/-- The `γ`-weight `Wm α z θ = w z · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wm_quad (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Wm α p.1 p.2) Work.FTS.H2.HQ.quadQ :=
  Work.FTS.H2.HQ.continuousOn_Wt_quad α

/-! ## Strong measurability of a triple product of slots -/

/-- The interior-class replacement of `Work.FTS.H2.aesm_prod_three`: the product
`|u₁ · (|u₂| · ρ) · (|u₃| · σ)|` of three `SmoothQuad` slots and two weights continuous on the
open quadrant is a.e. strongly measurable for `pm`. -/
theorem aesm_prod_three_qd (u₁ u₂ u₃ : ℝ → ℝ → ℝ)
    (hu₁ : Work.FTS.LocData.SmoothQuad u₁) (hu₂ : Work.FTS.LocData.SmoothQuad u₂)
    (hu₃ : Work.FTS.LocData.SmoothQuad u₃)
    {ρ σ : ℝ → ℝ → ℝ} (hρ : ContinuousOn (Function.uncurry ρ) Work.FTS.H2.HQ.quadQ)
    (hσ : ContinuousOn (Function.uncurry σ) Work.FTS.H2.HQ.quadQ) :
    AEStronglyMeasurable
      (Function.uncurry (fun z θ => |u₁ z θ * (|u₂ z θ| * ρ z θ) * (|u₃ z θ| * σ z θ)|)) pm := by
  have h1 : ContinuousOn (Function.uncurry u₁) Work.FTS.H2.HQ.quadQ :=
    hu₁.continuousOn.mono Work.FTS.H2.HQ.quadQ_subset_quadU
  have h2 : ContinuousOn (Function.uncurry u₂) Work.FTS.H2.HQ.quadQ :=
    hu₂.continuousOn.mono Work.FTS.H2.HQ.quadQ_subset_quadU
  have h3 : ContinuousOn (Function.uncurry u₃) Work.FTS.H2.HQ.quadQ :=
    hu₃.continuousOn.mono Work.FTS.H2.HQ.quadQ_subset_quadU
  have hfun : (Function.uncurry (fun z θ => |u₁ z θ * (|u₂ z θ| * ρ z θ) * (|u₃ z θ| * σ z θ)|))
      = fun p : ℝ × ℝ => |u₁ p.1 p.2 * (|u₂ p.1 p.2| * ρ p.1 p.2) * (|u₃ p.1 p.2| * σ p.1 p.2)| :=
    rfl
  rw [hfun]
  exact aesm_of_Qd (((h1.mul (h2.abs.mul hρ)).mul (h3.abs.mul hσ)).abs)

/-! ## The pairing lemma with an open-quadrant bound -/

/-- **The pairing lemma of the interior class.**  Same conclusion as
`Work.FTS.H2.term_of_slot`, but the `V`-factor only has to be bounded by `K` on the *open*
quadrant `0 < z`, `0 < θ < π/2`.

Route: truncate `V` to `V' = V · 1_{(0,π/2)}(θ)` (zero on the two boundary lines, where the
`V`-bound is unavailable), apply `Work.FTS.H2.term_of_slot` to `V'` (the closed-quadrant
hypothesis now holds), and observe that `V'` agrees with `V` `pm`-almost everywhere
(`ae_pm_theta_mem_Ioo`), so the integrability and the value of the integral are unchanged. -/
theorem term_of_slot_open (α : ℝ) (u v : ℝ → ℝ → ℝ) (hmu : Work.Spaces.HkMem α 4 u)
    (hmv : Work.Spaces.HkMem α 4 v) (A B V : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hV : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2), |V z θ| ≤ K)
    (hA0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ A z θ)
    (hB0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ B z θ)
    (hA : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 u z θ)
    (hB : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (B z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 v z θ)
    (hAmeas : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => A z θ) (volume.restrict Work.Spaces.Iθ))
    (hBmeas : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => B z θ) (volume.restrict Work.Spaces.Iθ))
    (hVABmeas : AEStronglyMeasurable
      (Function.uncurry (fun z θ => |V z θ * A z θ * B z θ|)) pm) :
    MeasureTheory.Integrable (Function.uncurry (fun z θ => |V z θ * A z θ * B z θ|)) pm ∧
      (∫ p, |V p.1 p.2 * A p.1 p.2 * B p.1 p.2| ∂pm)
        ≤ K * Work.Spaces.HkNorm α 4 u * Work.Spaces.HkNorm α 4 v := by
  set V' : ℝ → ℝ → ℝ := fun z θ => if θ ∈ Set.Ioo 0 (π / 2) then V z θ else 0 with hV'def
  have hV' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |V' z θ| ≤ K := by
    intro z hz θ hθ
    by_cases h : θ ∈ Set.Ioo 0 (π / 2)
    · simpa only [hV'def, h, ite_true] using hV z hz θ h
    · simp only [hV'def, h, ite_false, abs_zero]
      exact hK
  have hae : (fun p : ℝ × ℝ => |V p.1 p.2 * A p.1 p.2 * B p.1 p.2|)
      =ᵐ[pm] (fun p : ℝ × ℝ => |V' p.1 p.2 * A p.1 p.2 * B p.1 p.2|) := by
    filter_upwards [ae_pm_theta_mem_Ioo] with p hp
    simp only [hV'def, hp, ite_true]
  have hV'ABmeas : AEStronglyMeasurable
      (Function.uncurry (fun z θ => |V' z θ * A z θ * B z θ|)) pm :=
    hVABmeas.congr hae
  obtain ⟨hint, hbd⟩ := term_of_slot α u v hmu hmv A B V' K hK hV' hA0 hB0 hA hB hAmeas
    hBmeas hV'ABmeas
  exact ⟨hint.congr hae.symm, by rw [← integral_congr_ae hae.symm]; exact hbd⟩

end Work.H2.T1Q
