import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Aux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Aux2
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Common
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AbndInts
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12slotLe7
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T3RowAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# `T45aRow` — the level-six transport row with the coefficient `L₁₂(f)·A`

The pairing `slotPairing ρ a b (fun z θ => L₁₂(f)(z)·A(z,θ)) f` is a slot of the transport term
of the modulated equation in which the *coefficient* is the product of the radial primitive
`L₁₂(f)` of the datum and an independent `𝒲^{6,∞}`-bounded perturbation `A`.

**Route.**  `L₁₂(f)` is θ-independent, so the Leibniz rule for a radial factor
(`leibniz_radial_mul`) expands the slot into
`∑_{k ≤ b} C(b,k)·(D_z^k L₁₂ f)(z)·(D_z^{b-k}D_θ^a A)(z,θ)`, and each `A`-slot is bounded
pointwise by `C·K·Abnd α a θ` (`T45AslotLe`).  The angular factor `Abnd` is what makes the
leftover angular weight integrable against the leaf weight of the slot: for `a = 0` it is `1`
and the leaf weight is `w²·sin(2θ)^{-η}`, while for `a ≥ 1` the exponent
`-γ(α) + 2α/5 = -1 + 3α/10 > -1` keeps `∫ sin(2θ)^{-γ}·Abnd²` finite and `≤ D/α`
(`T45AbndInts`).  Cauchy–Schwarz on the angular slice produces `√(∫_θ σ·V²)`, which is
`Λ/w`, and the weighted slot bound `∫_z (D_z^k L₁₂ f)² w² ≤ C_L·|f|²_{ℋ⁶}` (`L12slotLe7`)
together with an AM–GM in `z` closes the estimate (`T45Common`).  The `α^{-1/2}` accumulated
from `D/α` is absorbed into the `α^{-3}` of the statement.
-/

/-- **The level-six transport row with the coefficient `L₁₂(f)·A`.** -/
theorem T45aRow : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f A : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.Spaces.HkMem α 7 f → Work.Spaces.VanishTheta f →
      (∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0) →
      Work.Construction.L12 f 0 = 0 →
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => Work.Construction.L12 f z * A z θ) f|
        ≤ C * K * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
            * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨CL, hCLpos, hL12⟩ := L12slotLe7
  obtain ⟨CA, hCApos, hAslot⟩ := T45AslotLe
  obtain ⟨D, hDpos, hD⟩ := T45AbndInts
  refine ⟨CA * Real.sqrt D * (10000000 * CL + 1) / 2 + 1, by positivity, ?_⟩
  intro α hα f A a b ρ K hso hm6 hm7 hvanish haxis hl12 hAso hAmem hAle hab hleaf
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hb : b ≤ 6 := by omega
  have hCA0 : 0 ≤ CA := le_of_lt hCApos
  have hD0 : 0 ≤ D := le_of_lt hDpos
  have hCL0 : 0 ≤ CL := le_of_lt hCLpos
  have hHknn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hK0 : 0 ≤ K := by
    have h1 : 0 ≤ Work.Spaces.WlInf α 6 A := by
      rw [Work.Spaces.WlInf]
      exact add_nonneg (Work.Spaces.wlZSum_nonneg α 6 A hAmem)
        (Work.Spaces.wlThSum_nonneg α 6 A hAmem)
    linarith
  have hAop : ∀ (j i : ℕ), i + j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ CA * K * Abnd α i θ :=
    fun j i hji z θ hz h1 h2 => hAslot α hα A K hAso hAmem hAle j i hji z θ hz h1 h2
  have hXsm : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
    have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 7 f hso hm7
      (by norm_num : 2 ≤ 7)).1
    rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
    exact h
  have hXint : ∀ k : ℕ, k ≤ 6 → MeasureTheory.IntegrableOn (fun z =>
      (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := fun k hk =>
    (hL12 α f hα0 hα1 hso hm6 hm7 hl12 k (le_trans hk (by norm_num))).1
  have hXbd : ∀ k : ℕ, k ≤ 6 → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z) ^ 2
        * (Work.Spaces.w z) ^ 2) ≤ CL * Work.Spaces.HkSq α 6 f := fun k hk =>
    (hL12 α f hα0 hα1 hso hm6 hm7 hl12 k (le_trans hk (by norm_num))).2
  have hXaesm : ∀ k : ℕ, k ≤ 6 → AEStronglyMeasurable (fun z =>
      Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z)
      (volume.restrict Work.Spaces.Iz) := by
    intro k hk
    have hcont : ContinuousOn (fun z => Work.Elliptic.DzdIter k
        (fun z => Work.Construction.L12 f z) z) (Set.Ioi 0) :=
      (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial
        (r := fun z => Work.Construction.L12 f z) (n := 6)
        (fun m hm => hXsm.of_le (by exact_mod_cast hm)) (a := k) (t := 0)
        (by omega)).continuousOn
    have h1 : AEStronglyMeasurable (fun z => Work.Elliptic.DzdIter k
        (fun z => Work.Construction.L12 f z) z) (volume.restrict (Set.Ioi 0)) :=
      hcont.aestronglyMeasurable measurableSet_Ioi
    rw [restrict_Ioi_eq_restrict_Iz] at h1
    exact h1
  have hfin : CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(1 / 2 : ℝ))
        * (1 + Work.Spaces.HkSq α 6 f)
      ≤ (CA * Real.sqrt D * (10000000 * CL + 1) / 2 + 1) * K * α ^ (-(3 : ℝ))
        * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
    have hCfin0 : 0 ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 := by positivity
    have h3 : 0 ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K := mul_nonneg hCfin0 hK0
    have h4 : 0 ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith [hHknn]
    have h5 : 0 ≤ α ^ (-(3 : ℝ)) := Real.rpow_nonneg hα0.le _
    have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    have hpow : (1 : ℝ) ≤ (1 + Work.FTS.Nonlin.Xn α f) ^ 4 :=
      one_le_pow₀ (by linarith)
    have hαp : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
    have hst1 : CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(1 / 2 : ℝ))
          * (1 + Work.Spaces.HkSq α 6 f)
        ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkSq α 6 f) := by
      refine mul_le_mul_of_nonneg_right ?_ h4
      exact mul_le_mul_of_nonneg_left hαp h3
    have hst2 : CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(3 : ℝ))
          * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (CA * Real.sqrt D * (10000000 * CL + 1) / 2 + 1) * K * α ^ (-(3 : ℝ))
          * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
      have h6 : (1 + Work.Spaces.HkSq α 6 f)
          ≤ (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
        calc (1 + Work.Spaces.HkSq α 6 f) = 1 * (1 + Work.Spaces.HkSq α 6 f) := by ring
          _ ≤ (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) :=
              mul_le_mul_of_nonneg_right hpow h4
      have h7 : 0 ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(3 : ℝ)) :=
        mul_nonneg h3 h5
      refine (mul_le_mul_of_nonneg_left h6 h7).trans ?_
      have h8 : CA * Real.sqrt D * (10000000 * CL + 1) / 2
          ≤ CA * Real.sqrt D * (10000000 * CL + 1) / 2 + 1 := by linarith
      have h9 : 0 ≤ K * α ^ (-(3 : ℝ))
          * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) :=
        mul_nonneg (mul_nonneg hK0 h5) (mul_nonneg (pow_nonneg (by linarith) 4) h4)
      calc CA * Real.sqrt D * (10000000 * CL + 1) / 2 * K * α ^ (-(3 : ℝ))
              * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))
          = (CA * Real.sqrt D * (10000000 * CL + 1) / 2) * (K * α ^ (-(3 : ℝ))
              * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))) := by ring
        _ ≤ (CA * Real.sqrt D * (10000000 * CL + 1) / 2 + 1) * (K * α ^ (-(3 : ℝ))
              * ((1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f))) :=
            mul_le_mul_of_nonneg_right h8 h9
        _ = (CA * Real.sqrt D * (10000000 * CL + 1) / 2 + 1) * K * α ^ (-(3 : ℝ))
              * (1 + Work.FTS.Nonlin.Xn α f) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by ring
    exact hst1.trans hst2
  rcases hleaf with rfl | rfl | ⟨ha1, rfl⟩
  · exact (T45common hα0 hα1 hso hAso hm6 hCL0 hCA0 hD0 hK0 hHknn hAop (fun z θ => rfl)
      (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
      ((hD α hα).1 a).1 ((hD α hα).1 a).2 (Or.inl rfl) hab hb hXsm hXint hXbd hXaesm).trans hfin
  · refine (T45common hα0 hα1 hso hAso hm6 hCL0 hCA0 hD0 hK0 hHknn hAop
      (fun z θ => by simp [Work.FTS.TransportS.leafOne]) (fun θ hθ => zero_le_one)
      ?_ ?_ (Or.inr (Or.inl rfl)) hab hb hXsm hXint hXbd hXaesm).trans hfin
    · simpa only [one_mul] using ((hD α hα).2.1 a).1
    · simpa only [one_mul] using ((hD α hα).2.1 a).2
  · exact (T45common hα0 hα1 hso hAso hm6 hCL0 hCA0 hD0 hK0 hHknn hAop (fun z θ => rfl)
      (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)
      ((hD α hα).2.2 a ha1).1 ((hD α hα).2.2 a ha1).2 (Or.inr (Or.inr ⟨ha1, rfl⟩)) hab hb
      hXsm hXint hXbd hXaesm).trans hfin

end Work.FTS.StrongPersist.H6Pair6Aux
