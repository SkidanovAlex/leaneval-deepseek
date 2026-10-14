import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.STEasyId
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS_EllLimOK.Decay.DecayTools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## Monotonicity of the level index -/

/-- One step of the monotonicity of the `ℋ^k`-integrand in the level. -/
theorem HkIntegrand_succ (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand α (k + 1) f z θ := by
  unfold Work.Spaces.HkIntegrand
  have hA : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ (∑ i ∈ Finset.range (k + 1 + 1),
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    calc (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + (Work.Spaces.DzIter (k + 1) f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
          le_add_of_nonneg_right (sq_nonneg _)
      _ = (∑ i ∈ Finset.range (k + 1 + 1),
          (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
          (Finset.sum_range_succ _ (k + 1)).symm
  have hB : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (∑ i ∈ Finset.range (k + 1 + 1), ∑ j ∈ Finset.range (k + 1 + 1),
        (if 1 ≤ i ∧ i + j ≤ k + 1 then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
    have h1 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k + 1 then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
      refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc, if_pos ⟨hc.1, by omega⟩]
      · rw [if_neg hc]
        by_cases hc' : 1 ≤ i ∧ i + j ≤ k + 1
        · rw [if_pos hc']
          exact sq_nonneg _
        · rw [if_neg hc']
    have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k + 1 then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 + 1),
          (if 1 ≤ i ∧ i + j ≤ k + 1 then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
      refine Finset.sum_le_sum fun i hi => ?_
      calc (∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k + 1 then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k + 1 then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            + (if 1 ≤ i ∧ i + (k + 1) ≤ k + 1 then
              (Work.Spaces.mixed (k + 1) i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
            le_add_of_nonneg_right (by
              by_cases hc : 1 ≤ i ∧ i + (k + 1) ≤ k + 1
              · rw [if_pos hc]; exact sq_nonneg _
              · rw [if_neg hc])
        _ = (∑ j ∈ Finset.range (k + 1 + 1),
            (if 1 ≤ i ∧ i + j ≤ k + 1 then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
            (Finset.sum_range_succ _ (k + 1)).symm
    have h3 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 + 1),
          (if 1 ≤ i ∧ i + j ≤ k + 1 then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ (∑ i ∈ Finset.range (k + 1 + 1), ∑ j ∈ Finset.range (k + 1 + 1),
          (if 1 ≤ i ∧ i + j ≤ k + 1 then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
      calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 + 1),
            (if 1 ≤ i ∧ i + j ≤ k + 1 then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1 + 1),
            (if 1 ≤ i ∧ i + j ≤ k + 1 then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            + (∑ j ∈ Finset.range (k + 1 + 1),
              (if 1 ≤ k + 1 ∧ (k + 1) + j ≤ k + 1 then
                (Work.Spaces.mixed j (k + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
            le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => by
              by_cases hc : 1 ≤ k + 1 ∧ (k + 1) + j ≤ k + 1
              · rw [if_pos hc]; exact sq_nonneg _
              · rw [if_neg hc])
        _ = (∑ i ∈ Finset.range (k + 1 + 1), ∑ j ∈ Finset.range (k + 1 + 1),
              (if 1 ≤ i ∧ i + j ≤ k + 1 then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
            (Finset.sum_range_succ _ (k + 1)).symm
    linarith
  linarith

/-- A summand of the `ℋ^k`-integrand is a summand of the `ℋ^{k'}`-integrand for `k ≤ k'`. -/
theorem HkIntegrand_mono (α : ℝ) {k k' : ℕ} (h : k ≤ k') (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand α k' f z θ := by
  revert h
  refine Nat.le_induction (le_refl _) ?_ k'
  intro n hn ih
  exact ih.trans (HkIntegrand_succ α n f z θ)

/-- At `z = 0` the radial weight vanishes, hence so does the `ℋ^k`-integrand. -/
theorem HkIntegrand_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  unfold Work.Spaces.HkIntegrand
  have hw : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  have h1 : ∀ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f 0 θ * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = 0 := by
    intro i _
    rw [hw]
    ring
  have h2 : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then
        (Work.Spaces.mixed j i f 0 θ * Work.Spaces.Wt α 0 θ) ^ 2 else 0) = 0 := by
    intro i _ j _
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc]
      have : Work.Spaces.Wt α 0 θ = 0 := by
        rw [Work.Spaces.Wt]
        simp [hw]
      rw [this]
      ring
    · rw [if_neg hc]
  rw [Finset.sum_eq_zero h1, Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (h2 i hi))]
  ring

/-- The `ℋ^k`-squared functional is monotone in the level. -/
theorem HkSq_mono (α : ℝ) {k k' : ℕ} (h : k ≤ k') {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k' f) : Work.Spaces.HkSq α k f ≤ Work.Spaces.HkSq α k' f := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine int2_mono (fun z => Filter.Eventually.of_forall fun θ => HkIntegrand_mono α h f z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k f z θ) ?_ hmem.2
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hmem.1 z hz

/-- The `ℋ^k`-membership is monotone in the level (the smaller integrand is a.s. measurable
because the datum is `C^∞` on the open quadrant). -/
theorem HkMem_of_le {α : ℝ} {k k' : ℕ} (h : k ≤ k') {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k' f) :
    Work.Spaces.HkMem α k f := by
  obtain ⟨h1, h2⟩ := hmem
  refine ⟨fun z hz => ?_, ?_⟩
  · rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ) = fun _ => (0 : ℝ) from by
        funext θ
        rw [← hz0]
        exact HkIntegrand_zero α k f θ]
      exact integrableOn_zero
    · refine MeasureTheory.Integrable.mono' (h1 z hz) ?_ ?_
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
          ((hsm.continuousOn_HkIntegrand α k)) hzpos
      · exact Filter.Eventually.of_forall fun θ => by
          rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
          exact HkIntegrand_mono α h f z θ
  · refine MeasureTheory.Integrable.mono' h2 ?_ ?_
    · have hjoint : AEStronglyMeasurable
          (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α k f z θ))
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
        Work.Spaces.aesm_of_continuousOn_Qd _
          ((hsm.continuousOn_HkIntegrand α k))
      exact hjoint.integral_prod_right'
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (MeasureTheory.integral_nonneg
        fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)]
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
      · rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ) = fun _ => (0 : ℝ) from by
          funext θ
          rw [← hz0]
          exact HkIntegrand_zero α k f θ]
        simp only [MeasureTheory.integral_zero]
        exact MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k' f z θ
      · exact MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
          (h1 z hz)
          (Filter.Eventually.of_forall fun θ => HkIntegrand_mono α h f z θ)

/-! ## The `σ`-gain of the leaf weights -/

theorem eta_le_gam {α : ℝ} (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam, Work.Spaces.eta]; linarith

/-- `sin(2θ) · sin(2θ)^{-q} = sin(2θ)^{1-q}` on the open interval. -/
theorem sin_mul_sin_rpow_neg {θ q : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-q) = (Real.sin (2 * θ)) ^ (1 + -q) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [Real.rpow_add hs, Real.rpow_one]

/-- **The `σ`-gain of the leaf weights.**  For every leaf weight `ρ` of the slot `a`, the
product `sin(2θ)·ρ` is dominated by `w²·sin(2θ)^{-(γ-1)}`. -/
theorem sigma_mul_leaf_le {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sin (2 * θ) * ρ z θ
      ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hkey : ∀ {q : ℝ}, q ≤ Work.Spaces.gam α →
      (Real.sin (2 * θ)) ^ (1 + -q)
        ≤ (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) := by
    intro q hq
    refine Real.rpow_le_rpow_of_exponent_ge hs hs1 ?_
    linarith
  have hcanon : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α))
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) := by
    congr 1
    ring_nf
  rcases hleaf with h | h | ⟨_, h⟩
  · subst h
    calc Real.sin (2 * θ) * Work.FTS.TransportS.leafEta z θ
        = (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          rw [Work.FTS.TransportS.leafEta]; ring
      _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.eta)) := by
          rw [sin_mul_sin_rpow_neg hθ]
      _ ≤ (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_left (hkey (eta_le_gam hα)) (sq_nonneg _)
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) :=
          le_of_eq hcanon
  · subst h
    have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) := by
      have h1 := Work.FTS.TransportS.one_le_rpow_neg (q := Work.Spaces.gam α - 1)
        (by linarith [Work.Spaces.one_lt_gam hα]) hθ
      rwa [show -(Work.Spaces.gam α - 1) = 1 + -(Work.Spaces.gam α) by ring] at h1
    calc Real.sin (2 * θ) * Work.FTS.TransportS.leafOne z θ
        = (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) := by
          rw [Work.FTS.TransportS.leafOne]; ring
      _ ≤ (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_left (le_trans hs1 hone) (sq_nonneg _)
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) :=
          le_of_eq hcanon
  · subst h
    calc Real.sin (2 * θ) * Work.FTS.TransportS.leafGam α z θ
        = (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
          rw [Work.FTS.TransportS.leafGam]; ring
      _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) := by
          rw [sin_mul_sin_rpow_neg hθ]
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) :=
          le_of_eq hcanon

/-- **The weight `w²·sin(2θ)^{-(γ-1)}` is dominated by the slot weight of *every* slot.** -/
theorem gm1_le_slotW {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (a' : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
      ≤ Work.FTS.TransportS.slotW α a' z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hA : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    refine Real.rpow_le_rpow_of_exponent_ge hs hs1 ?_
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  have hB : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    refine Real.rpow_le_rpow_of_exponent_ge hs hs1 ?_
    linarith
  rcases eq_or_ne a' 0 with ha' | ha'
  · subst ha'
    rw [Work.FTS.TransportS.slotW_zero_eq α hθ]
    exact mul_le_mul_of_nonneg_left hA (sq_nonneg _)
  · rw [Work.FTS.TransportS.slotW_of_pos_eq α (Nat.one_le_iff_ne_zero.mpr ha') hθ]
    exact mul_le_mul_of_nonneg_left hB (sq_nonneg _)

/-! ## The weight identities -/

/-- `(w z / sin(2θ)^{η/2})² = w z²·sin(2θ)^{-η}`. -/
theorem wdivSq (z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [div_pow, div_eq_mul_inv]
  have h2 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    calc ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ ((2 : ℝ)) :=
          (Real.rpow_natCast _ 2).symm
      _ = (Real.sin (2 * θ)) ^ ((Work.Spaces.eta / 2) * 2) := (Real.rpow_mul hs _ _).symm
      _ = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
          congr 1
          norm_num [Work.Spaces.eta]
  rw [h2, ← Real.rpow_neg hs]

/-- `Wt α z θ² = w z²·sin(2θ)^{-γ}`. -/
theorem WtSq (α z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  have h2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    calc ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) :=
          (Real.rpow_natCast _ 2).symm
      _ = (Real.sin (2 * θ)) ^ ((-(Work.Spaces.gam α / 2)) * 2) := (Real.rpow_mul hs _ _).symm
      _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
          congr 1
          ring
  rw [h2]

/-! ## The pointwise slot dominations -/

/-- **The slot domination at level `n`.**  For `a + b' ≤ n` the slot weight of `a` times the
square of the slot `(a,b')` is dominated by the `ℋ^n`-integrand. -/
theorem slotW_dom {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} {a b' n : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (h : a + b' ≤ n) :
    Work.FTS.TransportS.slotW α a z θ * (Work.Spaces.mixed b' a f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α n f z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rw [Work.FTS.TransportS.slotW_zero_eq α hθ]
    have h1 := Work.Spaces.sq_le_HkIntegrand_z α n f z θ b' (by omega)
    rw [mul_pow, wdivSq z θ hs] at h1
    rw [Work.Spaces.mixed_zero_right]
    simpa only [mul_comm] using h1
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    rw [Work.FTS.TransportS.slotW_of_pos_eq α ha1 hθ]
    have h1 := Work.Spaces.sq_le_HkIntegrand_mixed α n f z θ a b' ha1 (by omega)
    rw [mul_pow, WtSq α z θ hs] at h1
    simpa only [mul_comm] using h1


/-- The `sin(2θ)^{-(γ-1)}`-weighted slot domination at level `n`. -/
theorem domGm1 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ} {a' b' n : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (h : a' + b' ≤ n) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
        * (Work.Spaces.mixed b' a' f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α n f z θ :=
  (mul_le_mul_of_nonneg_right (gm1_le_slotW hα hα1 a' hθ) (sq_nonneg _)).trans
    (slotW_dom hα hθ h)

/-! ## The `D_z`-shift of a slot on the open quadrant -/

/-- `D_z^bD_θ^a(D_z f) = D_z^{b+1}D_θ^a f` on the open quadrant. -/
theorem mixedDzShift {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (b a : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (b + 1) a f z θ := by
  have h := Work.FTS.TransportS.mixed_dz_eqOn hf b a
    (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)
  simpa only [Function.uncurry] using h

/-! ## The leaf weight is dominated by its own slot weight, at *every* `z` -/

/-- Every leaf weight of the slot `a` is dominated by the slot weight of `a` (no positivity of
`z` is needed: the comparison is a pure `sin(2θ)`-comparison). -/
theorem leaf_le_slotW_any {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ z θ ≤ Work.FTS.TransportS.slotW α a z θ := by
  rcases hleaf with h | h | ⟨ha1, h⟩
  · subst h
    rcases eq_or_ne a 0 with ha | ha
    · subst ha
      rw [Work.FTS.TransportS.leafEta, Work.FTS.TransportS.slotW_zero_eq α hθ]
    · rw [Work.FTS.TransportS.leafEta,
        Work.FTS.TransportS.slotW_of_pos_eq α (Nat.one_le_iff_ne_zero.mpr ha) hθ]
      exact mul_le_mul_of_nonneg_left
        (Work.FTS.H2.rpow_eta_le_gam hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (sq_nonneg _)
  · subst h
    rw [Work.FTS.TransportS.leafOne]
    rcases eq_or_ne a 0 with ha | ha
    · subst ha
      rw [Work.FTS.TransportS.slotW_zero_eq α hθ]
      calc (Work.Spaces.w z) ^ 2 = (Work.Spaces.w z) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_left
              (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ) (sq_nonneg _)
    · rw [Work.FTS.TransportS.slotW_of_pos_eq α (Nat.one_le_iff_ne_zero.mpr ha) hθ]
      calc (Work.Spaces.w z) ^ 2 = (Work.Spaces.w z) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            mul_le_mul_of_nonneg_left
              (Work.FTS.TransportS.one_le_rpow_neg (le_of_lt (Work.Spaces.gam_pos hα)) hθ)
              (sq_nonneg _)
  · subst h
    rw [Work.FTS.TransportS.leafGam,
      Work.FTS.TransportS.slotW_of_pos_eq α ha1 hθ]

/-- The `ρ`-weighted slot domination at level `n`, at *every* `z`. -/
theorem domLeaf_all {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) {f : ℝ → ℝ → ℝ} {b' n : ℕ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (h : a + b' ≤ n) :
    ρ z θ * (Work.Spaces.mixed b' a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n f z θ :=
  (mul_le_mul_of_nonneg_right (leaf_le_slotW_any hα hleaf hθ) (sq_nonneg _)).trans
    (slotW_dom hα hθ h)

/-- Every leaf weight is nonnegative on `Iθ`. -/
theorem leaf_nonneg {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ ρ z θ := by
  rcases hleaf with h | h | ⟨_, h⟩
  · subst h
    exact Work.FTS.TransportS.leafEta_nonneg (sin_two_nonneg_Iθ hθ)
  · subst h
    exact Work.FTS.TransportS.leafOne_nonneg z θ
  · subst h
    exact Work.FTS.TransportS.leafGam_nonneg α (sin_two_nonneg_Iθ hθ)

/-! ## The Leibniz summands of the row -/

/-- The `(k,i)`-th summand of the Leibniz expansion in `z` of
`D_z^bD_θ^a(c₂ₘ(θ)·L₁₂(f)(z)·D_z f)`, paired with `D_z^bD_θ^a f` and weighted by `ρ`. -/
def t5bPiece (f : ℝ → ℝ → ℝ) (ρ : ℝ → ℝ → ℝ) (a b k i : ℕ) (p : ℝ × ℝ) : ℝ :=
  ρ p.1 p.2 * (Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) p.1)
    * (Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) p.1 p.2)
    * (Work.Spaces.mixed (b - k + 1) (a - i) f p.1 p.2)
    * (Work.Spaces.mixed b a f p.1 p.2)

end Work.FTS.StrongPersist.H6Pair6Aux
