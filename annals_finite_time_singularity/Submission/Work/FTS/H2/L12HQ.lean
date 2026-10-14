import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.Vocab
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Preliminary facts about the domain and the operators -/

/-- `Work.Construction.L12 g = Work.FM.L12 Work.Spaces.K g` (the form used by N4's `N₀` and `N`)
and `Work.Elliptic.L12 g = Work.FM.L12 Work.FM.Kpaper g` (the form of the elliptic chapter) are
the same function, because `Work.Spaces.K = Work.FM.Kpaper = Work.Elliptic.Ktheta`. -/
theorem constructionL12_eq_ellipticL12 (g : ℝ → ℝ → ℝ) :
    Work.Construction.L12 g = Work.Elliptic.L12 g := by
  have hKK : Work.Spaces.K = Work.FM.Kpaper :=
    Work.Elliptic.Ktheta_eq_K.symm.trans Work.Elliptic.Ktheta_eq_Kpaper
  funext z
  show Work.FM.L12 Work.Spaces.K g z = Work.Elliptic.L12 g z
  rw [Work.Elliptic.L12_eq_FM]
  show Work.FM.L12 Work.Spaces.K g z = Work.FM.L12 Work.FM.Kpaper g z
  rw [hKK]

/-- The `ℋ^k`-energy is nonnegative. -/
theorem HkSq_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq]
  exact integral_nonneg fun z =>
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ

/-- The `θ`-integrand of a *radial* function: rewriting the `ℋ^k`-integrand of
`(z,θ) ↦ u z` as the constant `(∑_i (D_z^i u)² w²)` times `sin(2θ)^{-η}`. -/
theorem HkIntegrand_rad' (α : ℝ) (k : ℕ) (u : ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => u z) z θ
      = (∑ i ∈ Finset.range (k + 1), (Work.Elliptic.DzdIter i u z) ^ 2
            * (Work.Spaces.w z) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  rw [Work.Elliptic.HkIntegrand_rad α k u z hθ, Finset.sum_mul]

/-! ## The main estimate in the spelling of the elliptic chapter -/

/-- The content of `L12HQ`, phrased for the elliptic chapter's spelling `Work.Elliptic.L12`
of the operator.  The proof is the paper's: `L₁₂(g)` is radial, so only the pure `D_z`-summands
of `HkSq α 4 (L₁₂ g)` survive; the `k = 0` one is the weighted Hardy inequality applied to
`L₁₂(g)` (which vanishes at `0` and at `∞`), and the `k ≥ 1` ones are the Cauchy–Schwarz
inequality `(Qang g j z)² ≤ (∫_θ K²)·∫_θ (D_z^j g)²` for the angular moments, together with
`D_z^{j+1}(L₁₂ g)(z) = -Qang g j z` (both in the *interior* class, where the analyticity
hypothesis `SmoothNbhd` is replaced by `SmoothQuad`). -/
theorem L12HQ_elliptic : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem α 4 g →
    Work.Elliptic.L12 g 0 = 0 →
    Work.Spaces.HkMem α 4 (fun z θ => Work.Elliptic.L12 g z) ∧
      Work.Spaces.HkNorm α 4 (fun z θ => Work.Elliptic.L12 g z)
        ≤ C * Work.Spaces.HkNorm α 4 g := by
  refine ⟨Real.sqrt ((∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      * (111 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2))) + 1, by positivity, ?_⟩
  intro α g hα hα1 hsm hmem h0
  set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθ
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAK
  have hK2nn : 0 ≤ AK := by
    rw [hAK]; exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hCθnn : 0 ≤ Cθ := by
    rw [hCθ]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  have hHkSqnn : 0 ≤ Work.Spaces.HkSq α 4 g := HkSq_nonneg α 4 g
  -- ## the density
  have hint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) :=
    L12densIntegrable α g hα hα1 hsm hmem
  obtain ⟨hval, htend, hcont⟩ := Work.Elliptic.L12_values g hint h0
  -- ## the angular moments
  obtain ⟨hQang_deriv, hQang_cont⟩ := QangDiff α g hα hα1 hsm hmem
  have hQang0cont : ContinuousOn (Work.Elliptic.Qang g 0) (Set.Ioi 0) := hQang_cont 0 (by norm_num)
  have hdens_contOn : ContinuousOn (Work.Elliptic.L12dens g) (Set.Ioi 0) := by
    have hdiv : ContinuousOn (fun z => Work.Elliptic.Qang g 0 z / z) (Set.Ioi 0) :=
      hQang0cont.div continuousOn_id (fun z hz => ne_of_gt hz)
    exact hdiv.congr (fun z _ => Work.Elliptic.L12dens_eq_Qang_div g z)
  have hdens_contAt : ∀ z : ℝ, 0 < z → ContinuousAt (Work.Elliptic.L12dens g) z :=
    fun z hz => hdens_contOn.continuousAt (isOpen_Ioi.mem_nhds hz)
  -- ## the derivative of `L₁₂(g)`
  have hderiv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.L12 g z) (-(Work.Elliptic.L12dens g z)) z := by
    intro z hz
    have hintv : IntervalIntegrable (Work.Elliptic.L12dens g) volume (0 : ℝ) z := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hz.le]
      exact hint.mono_set Set.Ioc_subset_Ioi_self
    have hprim := intervalIntegral.integral_hasDerivAt_right hintv
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hdens_contOn z hz)
      (hdens_contAt z hz)
    refine hprim.neg.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact hval y hy.le
  -- ## the iterated `D_z`-derivatives of `L₁₂(g)`
  have hgen : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (fun z => Work.Elliptic.L12 g z) z
        = - Work.Elliptic.Qang g k z := by
    intro k
    induction k with
    | zero =>
        intro _ z hz
        have hd : deriv (fun z => Work.Elliptic.L12 g z) z = -(Work.Elliptic.L12dens g z) :=
          (hderiv z hz).deriv
        change z * deriv (fun z => Work.Elliptic.L12 g z) z = - Work.Elliptic.Qang g 0 z
        rw [hd, Work.Elliptic.L12dens_eq_Qang_div, mul_neg, neg_inj,
          mul_div_cancel₀ _ (ne_of_gt hz)]
    | succ n ih =>
        intro hn z hz
        have hev : Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)
            =ᶠ[𝓝 z] (fun z' => - Work.Elliptic.Qang g n z') := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
          exact ih (by omega) z' hz'
        have hdv : deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)) z
            = - deriv (fun z' => Work.Elliptic.Qang g n z') z := by
          rw [hev.deriv_eq]
          exact deriv.neg
        change z * deriv (Work.Elliptic.DzdIter (n + 1) (fun z => Work.Elliptic.L12 g z)) z
            = - Work.Elliptic.Qang g (n + 1) z
        rw [hdv, mul_neg, neg_inj, (hQang_deriv n (by omega) z hz).deriv,
          mul_div_cancel₀ _ (ne_of_gt hz)]
  -- ## the high-order terms
  have hhigh : ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      MeasureTheory.IntegrableOn
        (fun z => (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.L12 g z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.L12 g z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ AK * Work.Spaces.HkSq α 4 g := by
    intro i hi hi4
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    have hj : j ≤ 3 := by omega
    have hpt : ∀ z : ℝ, 0 < z →
        Work.Elliptic.DzdIter (j + 1) (fun z => Work.Elliptic.L12 g z) z
          = - Work.Elliptic.Qang g j z := by
      intro z hz
      exact hgen j hj z hz
    have hmeas : MeasureTheory.AEStronglyMeasurable (fun z =>
        (Work.Elliptic.DzdIter (j + 1) (fun z => Work.Elliptic.L12 g z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have h1 : Measurable (fun z =>
          Work.Elliptic.DzdIter (j + 1) (fun z => Work.Elliptic.L12 g z) z) := by
        simp only [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
        exact measurable_id.mul (measurable_deriv _)
      have h2 : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
        simp only [Work.Spaces.w]; fun_prop
      exact ((h1.pow_const 2).mul h2).aestronglyMeasurable
    have hDom : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2)) Work.Spaces.Iz :=
      (integrableOn_w_sq_mul_int_sqQ α g hα hα1 hsm hmem (by omega : j ≤ 4)).1
    have hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        ‖(Work.Elliptic.DzdIter (j + 1) (fun z => Work.Elliptic.L12 g z) z) ^ 2
            * (Work.Spaces.w z) ^ 2‖
          ≤ AK * ((Work.Spaces.w z) ^ 2
              * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by
      change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))), _
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
      filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with z hz0 hzI
      have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
      have hcs := Qang_sq_leQ α g hsm hmem j (by omega) hzpos
      rw [← hAK] at hcs
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      rw [hpt z hzpos, neg_sq, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) hw2)]
      calc (Work.Elliptic.Qang g j z) ^ 2 * (Work.Spaces.w z) ^ 2
          ≤ (AK * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2))
              * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hcs hw2
        _ = AK * ((Work.Spaces.w z) ^ 2
              * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by ring
    have hFint : MeasureTheory.IntegrableOn (fun z =>
        (Work.Elliptic.DzdIter (j + 1) (fun z => Work.Elliptic.L12 g z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
      MeasureTheory.Integrable.mono' (hDom.const_mul AK) hmeas hbound
    refine ⟨hFint, ?_⟩
    have hle : (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (j + 1) (fun z => Work.Elliptic.L12 g z) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ ∫ z in Work.Spaces.Iz, AK * ((Work.Spaces.w z) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := by
      refine MeasureTheory.integral_mono_ae hFint (hDom.const_mul AK) ?_
      filter_upwards [hbound] with z hz
      rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))] at hz
    calc (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (j + 1) (fun z => Work.Elliptic.L12 g z) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ ∫ z in Work.Spaces.Iz, AK * ((Work.Spaces.w z) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) := hle
      _ = AK * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j g z θ) ^ 2) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ AK * Work.Spaces.HkSq α 4 g :=
          mul_le_mul_of_nonneg_left
            (integrableOn_w_sq_mul_int_sqQ α g hα hα1 hsm hmem (by omega : j ≤ 4)).2 hK2nn
  -- ## the angular term `(Qang g 0)²w²`
  have hQDom : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 g z θ) ^ 2)) Work.Spaces.Iz :=
    (integrableOn_w_sq_mul_int_sqQ α g hα hα1 hsm hmem (j := 0) (by norm_num)).1
  have hQpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ AK * ((Work.Spaces.w z) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 g z θ) ^ 2) := by
    change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))), _
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with z hz0 hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    have hcs := Qang_sq_leQ α g hsm hmem 0 (by norm_num) hzpos
    rw [← hAK] at hcs
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    calc (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (AK * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 g z θ) ^ 2))
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hcs hw2
      _ = AK * ((Work.Spaces.w z) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 0 g z θ) ^ 2) := by ring
  have hQint : MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' (hQDom.const_mul AK) ?_ ?_
    · refine aestronglyMeasurable_restrict_Iz ?_
      refine ContinuousOn.mul (hQang0cont.pow 2) ?_
      simp only [Work.Spaces.w]
      exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2
    · filter_upwards [hQpt] with z hz
      rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hQbound : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ AK * Work.Spaces.HkSq α 4 g := by
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (hQDom.const_mul AK) hQpt) ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integrableOn_w_sq_mul_int_sqQ α g hα hα1 hsm hmem (j := 0) (by norm_num)).2 hK2nn
  -- ## the `k = 0` Hardy term
  obtain ⟨hInt0, hBound0⟩ := L12k0Q α g hmem hint hderiv hdens_contOn hcont htend h0 hQint
  -- ## assembling the `ℋ⁴`-energy
  have hsum_int : ∀ i ∈ Finset.range 5, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.L12 g z) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    intro i hi
    rw [Finset.mem_range] at hi
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; exact hInt0
    · exact (hhigh i h (by omega)).1
  have hsum_bound : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
        (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.L12 g z) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ 111 * (AK * Work.Spaces.HkSq α 4 g) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 5) hsum_int, Finset.sum_range_succ']
    have hsum4 : (∑ i ∈ Finset.range 4, (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (i + 1) (fun z => Work.Elliptic.L12 g z) z) ^ 2
            * (Work.Spaces.w z) ^ 2)) ≤ ∑ _i ∈ Finset.range 4, AK * Work.Spaces.HkSq α 4 g := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact (hhigh (i + 1) (by omega) (by omega)).2
    have h0b : (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 0 (fun z => Work.Elliptic.L12 g z) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ 107 * (AK * Work.Spaces.HkSq α 4 g) :=
      le_trans hBound0 (mul_le_mul_of_nonneg_left hQbound (by norm_num))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum4
    refine le_trans (add_le_add hsum4 h0b) (le_of_eq ?_)
    ring
  have hHkSq : Work.Spaces.HkSq α 4 (fun z θ => Work.Elliptic.L12 g z)
      ≤ (Cθ * (111 * AK)) * Work.Spaces.HkSq α 4 g := by
    rw [Work.Elliptic.HkSq_rad]
    calc (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
            (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.L12 g z) z) ^ 2
              * (Work.Spaces.w z) ^ 2) * Cθ
        ≤ (111 * (AK * Work.Spaces.HkSq α 4 g)) * Cθ :=
          mul_le_mul_of_nonneg_right hsum_bound hCθnn
      _ = (Cθ * (111 * AK)) * Work.Spaces.HkSq α 4 g := by ring
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)).1
  have hHkMem : Work.Spaces.HkMem α 4 (fun z θ => Work.Elliptic.L12 g z) := by
    constructor
    · intro z hz
      refine MeasureTheory.Integrable.congr
        (f := fun θ => (∑ i ∈ Finset.range 5,
            (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.L12 g z) z) ^ 2
              * (Work.Spaces.w z) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ?_ ?_
      · exact hsinI.const_mul _
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (HkIntegrand_rad' α 4 (fun z => Work.Elliptic.L12 g z) z hθ).symm)
    · refine MeasureTheory.Integrable.congr
        (f := fun z => (∑ i ∈ Finset.range 5,
            (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.L12 g z) z) ^ 2
              * (Work.Spaces.w z) ^ 2) * Cθ) ?_ ?_
      · exact (MeasureTheory.integrable_finsetSum (Finset.range 5) hsum_int).mul_const Cθ
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
        simp only [Work.Spaces.Iθ, hCθ]
        rw [setIntegral_congr_fun (f := fun θ => Work.Spaces.HkIntegrand α 4
            (fun z θ => Work.Elliptic.L12 g z) z θ)
          (g := fun θ => (∑ i ∈ Finset.range 5,
              (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.L12 g z) z) ^ 2
                * (Work.Spaces.w z) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          measurableSet_Icc
          (fun θ hθ => HkIntegrand_rad' α 4 (fun z => Work.Elliptic.L12 g z) z hθ)]
        rw [MeasureTheory.integral_const_mul]
  refine ⟨hHkMem, ?_⟩
  have hXnn : 0 ≤ Cθ * (111 * AK) := mul_nonneg hCθnn (mul_nonneg (by norm_num) hK2nn)
  have hstep : Work.Spaces.HkNorm α 4 (fun z θ => Work.Elliptic.L12 g z)
      ≤ Real.sqrt (Cθ * (111 * AK)) * Work.Spaces.HkNorm α 4 g := by
    calc Work.Spaces.HkNorm α 4 (fun z θ => Work.Elliptic.L12 g z)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => Work.Elliptic.L12 g z)) := rfl
      _ ≤ Real.sqrt ((Cθ * (111 * AK)) * Work.Spaces.HkSq α 4 g) := Real.sqrt_le_sqrt hHkSq
      _ = Real.sqrt (Cθ * (111 * AK)) * Work.Spaces.HkNorm α 4 g := by
          rw [Real.sqrt_mul hXnn, Work.Spaces.HkNorm]
  calc Work.Spaces.HkNorm α 4 (fun z θ => Work.Elliptic.L12 g z)
      ≤ Real.sqrt (Cθ * (111 * AK)) * Work.Spaces.HkNorm α 4 g := hstep
    _ ≤ (Real.sqrt (Cθ * (111 * AK)) + 1) * Work.Spaces.HkNorm α 4 g :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.sqrt_nonneg _)

/-! ## Elgindi's Proposition `L12H` (tex 1276) in the *interior* class -/

/-- Elgindi's Proposition `L12H` (tex 1276) in the *interior* class
`Work.FTS.Nonlin.RegQ` of the frozen `Submission/Work/FTS/Vocab.lean`: for `RegQ α 4 g` with
`L₁₂(g)(0) = 0`, `L₁₂(g) ∈ ℋ⁴` and `|L₁₂(g)|_{ℋ⁴} ≤ C|g|_{ℋ⁴}`, `C` universal.  This is the
design document's `L12HQ` (§3.3 L-N4.5); the operator is `Work.Construction.L12` (the form used
by N4's `N₀` and `N`), which is the same as `Work.Elliptic.L12` (bridge: `Elliptic.L12_eq_FM`,
`Elliptic.Ktheta_eq_K`).

`RegQ α 4 g = SmoothQuad g ∧ HkMem α 4 g ∧ BdryTraces α 4 g` replaces the `Spaces.SmoothNbhd`
hypothesis of `Work.Elliptic.L12H` (analyticity on a neighbourhood of the closed quadrant, false
for the perturbation `g` of the bootstrap, whose profile is only `C^{2α/3}` in `θ` at the
boundary).  The proof is the delivered one: `L₁₂(g)` is radial, so only the `D_z`-summands of
`HkSq α 4 (L₁₂ g)` are non-zero, and each is bounded by integration by parts (the zero mode
`L₁₂(g)(0) = 0` makes the weight `(1+z)⁴/z²` harmless at `z = 0`) exactly as in the paper. -/
theorem L12HQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
    Work.FTS.Nonlin.RegQ α 4 g → Work.Construction.L12 g 0 = 0 →
    Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
        ≤ C * Work.FTS.Nonlin.Xn α g := by
  obtain ⟨C, hCpos, hmain⟩ := L12HQ_elliptic
  refine ⟨C, hCpos, ?_⟩
  intro α g hα hα1 hreg h0
  obtain ⟨hsm, hmem, -⟩ := hreg
  have h0' : Work.Elliptic.L12 g 0 = 0 := by
    rw [← constructionL12_eq_ellipticL12 g]; exact h0
  obtain ⟨hHkMem, hNorm⟩ := hmain α g hα hα1 hsm hmem h0'
  have hfun : (fun z θ : ℝ => Work.Construction.L12 g z)
      = fun z θ : ℝ => Work.Elliptic.L12 g z := by
    funext z θ
    rw [constructionL12_eq_ellipticL12]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact hHkMem
  · rw [hfun]
    exact hNorm

end Work.FTS.H2
