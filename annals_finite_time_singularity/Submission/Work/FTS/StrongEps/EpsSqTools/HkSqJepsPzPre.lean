/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSqTools/HkSq_JepsPz_le.lean`

**The counterflow `J_ε : X → ℋ^k` for `k ≤ 6` in the projected, weighted space `X`:**

  `HkSq α k (Pz (J_ε f)) ≤ C (C/ε)^{2k} EpsSq α f`,

with a constant `C > 0` depending only on the kernel `ρ`.

## Route

* `Pz h = h − c·bump` with `c = L₁₂ h 0 / pzNorm`, `h = J_ε f`.  The `ℋᵏ`-integrand of a sum
  obeys the *pointwise* Euclidean triangle inequality for its slot vector
  (`HkIntegrand_sqrt_add_le`), so with the homogeneity `HkIntegrand_const_mul`
  `HkIntegrand α k (Pz h) ≤ 2 HkIntegrand α k h + 2 c² HkIntegrand α k bump`.
* The level-`k` slot sum of `h` is dominated slot-by-slot by the *level-zero* weighted energy
  against `epsW α = w·sin(2θ)^{-γ/2}`: `w·sin(2θ)^{-η/2} ≤ epsW α` since `η ≤ γ` and
  `sin(2θ) ≤ 1` on `Iθ`, and the mixed slots carry exactly the weight `Wt α = epsW α` there.
* The level-zero slot bound for each `D_z^jD_θ^i (J_ε f)`, `j + i ≤ 6`, is
  `EpsSqIter_mixed_Jeps_le6` (obtained from the routed kernel identity of
  `mixed_Jeps_kernel_partial` + weighted Cauchy–Schwarz).
* The correction is controlled by `|L₁₂ h 0| ≤ 3 √(EpsSq α h) ≤ 3 √(K EpsSq α f)`
  (`L12_zero_le_EpsSq`, which needs `EpsMem α h`) and `HkSq α k bump ≤ B²`
  (`exists_HkNorm_bump_le`).

Everything is carried out in `ℝ≥0∞`: `ofReal (HkSq α k g) ≤ ∫⁻ ofReal (HkIntegrand α k g)`
holds with *no* integrability hypothesis, so no `HkMem` assumption on the left is needed.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_mixed_Jeps_le
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_Pz_sub_le
import Submission.Work.FTS.StrongEps.EpsSqTools.L12_zero_le_EpsSq
import Submission.Work.FTS.StrongEps.EpsE4Thr.HkIntegrand_sqrt_add_le
import Submission.Work.FTS.StrongEps.PZeroAux.hkNorm_Pz_le
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.StrongEps.StepFacts.OfRealTools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. Elementary facts about the two weights -/

/-- `sin (2θ) ≥ 0` on the angular interval. -/
theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem gam_pos_of_pos {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

theorem eta_le_gam_of_pos {α : ℝ} (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam, Work.Spaces.eta]; linarith

/-- The pure-`z` slot weight `w z / sin(2θ)^{η/2}` is nonnegative on `Iθ`. -/
theorem wdiv_eta_nonneg {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
  div_nonneg (Work.FTS.StrongEps.w_nonneg z)
    (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _)

/-- **The pure-`z` slot weight is dominated by `epsW`** (the mixed-slot weight): both share the
radial factor `w z`, and `sin(2θ)^{γ/2} ≤ sin(2θ)^{η/2}` because `η ≤ γ` and `sin(2θ) ≤ 1`
on `Iθ`. -/
theorem wdiv_eta_le_epsW {α z θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ epsW α z θ := by
  have hsin : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hgam : 0 < Work.Spaces.gam α := gam_pos_of_pos hα
  rcases eq_or_lt_of_le hsin with h0 | hpos
  · have h1 : Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [← h0, Real.zero_rpow (by norm_num [Work.Spaces.eta]), div_zero]
    have h2 : epsW α z θ = 0 := by
      have h3 : epsW α z θ
          = Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := rfl
      rw [h3, ← h0, Real.zero_rpow (by positivity), div_zero]
    rw [h1, h2]
  · have hle : Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2)
        ≤ Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hpos (Real.sin_le_one _)
        (by linarith [eta_le_gam_of_pos hα])
    have hpos' : 0 < Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hpos _
    calc Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
        ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.gam α / 2) :=
          div_le_div_of_nonneg_left (Work.FTS.StrongEps.w_nonneg z) hpos' hle
      _ = epsW α z θ := rfl

/-- `ContinuousOn` of the pointwise square, in the `fun`-form used by the measurability
route (`ContinuousOn.pow` produces the `Pi`-form `f ^ 2`). -/
theorem continuousOn_sq' {X : Type*} [TopologicalSpace X] {f : X → ℝ} {s : Set X}
    (hc : ContinuousOn f s) : ContinuousOn (fun q => (f q) ^ 2) s := by
  have h : (fun q => (f q) ^ 2) = f ^ 2 := by funext q; rw [Pi.pow_apply]
  rw [h]; exact hc.pow 2

/-! ## 2. The `epsW`-slot sum dominating the `ℋᵏ`-integrand -/

/-- The level-`k` slot sum of `g` with the *mixed-slot* weight `epsW α` replacing every weight of
`HkIntegrand`. -/
noncomputable def EpsSlotSum (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ a ∈ Finset.range (k + 1), (Work.Spaces.DzIter a g z θ * epsW α z θ) ^ 2)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i g z θ * epsW α z θ) ^ 2 else 0

/-- **The `ℋᵏ`-integrand is dominated by the `epsW`-slot sum** on `Iθ`. -/
theorem HkIntegrand_le_EpsSlotSum {α : ℝ} (hα : 0 < α) (k : ℕ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k g z θ ≤ EpsSlotSum α k g z θ := by
  have hle := wdiv_eta_le_epsW (α := α) (z := z) (θ := θ) hα hθ
  have h0 := wdiv_eta_nonneg (z := z) (θ := θ) hθ
  rw [Work.Spaces.HkIntegrand, EpsSlotSum]
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum fun a _ => ?_
    have hsq : (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        ≤ (epsW α z θ) ^ 2 := pow_le_pow_left₀ h0 hle 2
    calc (Work.Spaces.DzIter a g z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.DzIter a g z θ) ^ 2
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 := by ring
      _ ≤ (Work.Spaces.DzIter a g z θ) ^ 2 * (epsW α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = (Work.Spaces.DzIter a g z θ * epsW α z θ) ^ 2 := by ring
  · refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, ← epsW_eq_Wt_of_mem_Iθ (α := α) (z := z) hθ]
    · rw [if_neg hc, if_neg hc]

/-- The `ofReal` of the slot sum is the sum of the `ofReal`s of its slots. -/
theorem ofReal_EpsSlotSum {α : ℝ} (k : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    ENNReal.ofReal (EpsSlotSum α k g z θ)
      = (∑ a ∈ Finset.range (k + 1),
          ENNReal.ofReal ((Work.Spaces.DzIter a g z θ * epsW α z θ) ^ 2))
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ENNReal.ofReal (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i g z θ * epsW α z θ) ^ 2 else 0) := by
  rw [EpsSlotSum]
  rw [ENNReal.ofReal_add
    (Finset.sum_nonneg fun a _ => sq_nonneg _)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs <;> positivity)]
  congr 1
  · exact ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)
  · rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs <;> positivity)]
    exact Finset.sum_congr rfl fun i _ =>
      ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> positivity)

/-! ## 3. The product measure of the two domains, and the `ofReal` bridge -/

/-- The product of the two restricted measures, i.e. Lebesgue measure restricted to `Iz × Iθ`. -/
noncomputable abbrev nu : Measure (ℝ × ℝ) :=
  (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)

theorem nu_eq : (nu : Measure (ℝ × ℝ)) = (volume.prod volume).restrict
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
  Measure.prod_restrict _ _

/-- The iterated `lintegral` over `Iz`, `Iθ` equals the product-measure `lintegral`. -/
theorem iter_eq_nu {F : ℝ × ℝ → ℝ≥0∞} (hF : AEMeasurable F nu) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, F (z, θ))
      = ∫⁻ q, F q ∂nu := by
  rw [nu_eq]
  refine (MeasureTheory.setLIntegral_prod F ?_).symm
  rw [← Measure.prod_restrict (μ := volume) (ν := volume)
    (Work.Spaces.Iz) (Work.Spaces.Iθ)]
  exact hF

/-- The joint `ℋᵏ`-integrand of a profile smooth on the open quadrant is a.e. strongly
measurable for the product measure. -/
theorem aesm_HkIntegrand_nu {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k g q.1 q.2) nu :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad α k hsm)

/-- **`ofReal (HkSq α k g)` is bounded by the product-measure `lintegral` of `ofReal` of the
`ℋᵏ`-integrand.**  No integrability hypothesis is needed. -/
theorem ofReal_HkSq_le_nuLint {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad) :
    ENNReal.ofReal (Work.Spaces.HkSq α k g)
      ≤ ∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2) ∂nu := by
  have hψ : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ :=
    fun z => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ
  have h1 : ENNReal.ofReal (Work.Spaces.HkSq α k g)
      ≤ ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) :=
    Work.FTS.StrongEps.StepFacts.ofReal_integral_le_lintegral_ofReal hψ
  have h2 : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ) :=
    lintegral_mono fun z => Work.FTS.StrongEps.StepFacts.ofReal_integral_le_lintegral_ofReal
      (fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
  have hAe : AEMeasurable
      (fun q : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2))
      ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [← Measure.prod_restrict (μ := volume) (ν := volume)
      (Work.Spaces.Iz) (Work.Spaces.Iθ)]
    exact ENNReal.measurable_ofReal.comp_aemeasurable (aesm_HkIntegrand_nu hsm).aemeasurable
  have h3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      = ∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2) ∂nu := by
    rw [nu_eq]
    exact (MeasureTheory.setLIntegral_prod
      (fun q : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2)) hAe).symm
  exact h1.trans (h2.trans (le_of_eq h3))

/-- **The same, as an equality, when the profile is in `ℋᵏ`.** -/
theorem ofReal_HkSq_eq_nuLint {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α k g)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad) :
    ENNReal.ofReal (Work.Spaces.HkSq α k g)
      = ∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2) ∂nu := by
  have hψ : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ :=
    fun z => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ
  have h1 : ENNReal.ofReal (Work.Spaces.HkSq α k g)
      = ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2 (Eventually.of_forall hψ)
  have h2 : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
  have hAe : AEMeasurable
      (fun q : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2))
      ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [← Measure.prod_restrict (μ := volume) (ν := volume)
      (Work.Spaces.Iz) (Work.Spaces.Iθ)]
    exact ENNReal.measurable_ofReal.comp_aemeasurable (aesm_HkIntegrand_nu hsm).aemeasurable
  have h3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      = ∫⁻ q, ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2) ∂nu := by
    rw [nu_eq]
    exact (MeasureTheory.setLIntegral_prod
      (fun q : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g q.1 q.2)) hAe).symm
  exact h1.trans (h2.trans h3)

/-! ## 4. Additivity of the `lintegral` over finite sums of a.e. measurable terms -/

theorem lintegral_finset_sum_aemeasurable {ι α : Type*} [DecidableEq ι] {m : MeasurableSpace α}
    {μ : Measure α} (s : Finset ι) {f : ι → α → ℝ≥0∞} (h : ∀ i ∈ s, AEMeasurable (f i) μ) :
    ∫⁻ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫⁻ a, f i a ∂μ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      have hi' : AEMeasurable (f i) μ := h i (Finset.mem_insert_self _ _)
      have hs' : ∀ j ∈ s, AEMeasurable (f j) μ := fun j hj => h j (Finset.mem_insert_of_mem hj)
      calc ∫⁻ a, ∑ x ∈ insert i s, f x a ∂μ
          = ∫⁻ a, (f i a + ∑ x ∈ s, f x a) ∂μ := by
              refine lintegral_congr fun a => ?_
              exact Finset.sum_insert hi
        _ = ∫⁻ a, f i a ∂μ + ∫⁻ a, (∑ x ∈ s, f x a) ∂μ :=
              MeasureTheory.lintegral_add_left' hi' _
        _ = ∫⁻ a, f i a ∂μ + ∑ x ∈ s, ∫⁻ a, f x a ∂μ := by rw [ih hs']
        _ = ∑ x ∈ insert i s, ∫⁻ a, f x a ∂μ := by rw [Finset.sum_insert hi]


end Work.FTS.StrongEps.EpsSqTools
