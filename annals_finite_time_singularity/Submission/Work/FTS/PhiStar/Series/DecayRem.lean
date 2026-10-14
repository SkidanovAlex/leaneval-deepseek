import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.Cutoff
-- ===== merged: Submission.Work.FTS.ClassCHon.CmpSupp.cmode_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.ClassCHon.CmpSupp

/-!
# `cmode_facts` — the elementary facts about the angular mode coefficients

For a source `F` which is `C^∞` jointly and compactly supported in the radial variable
(`F z θ = 0` for `z ∉ [a,b]`, with `a > 0`), the angular mode coefficient

  `cmode m F z = (∫_0^{π/2} F z θ · e_m θ · cos θ dθ) / (∫_0^{π/2} e_m θ² cos θ dθ)`

is `C^n` on `(0,∞)` for every `n`, vanishes off `[a,b]`, is square-integrable on `(1,∞)`
and (divided by `t^4`) on `(0,1)`, and is bounded on `[a,b]` by a *mode-independent*
constant times `1/√(eNorm m)`.

* Smoothness: `cmode m F ·` is the parametric integral of `F` against the continuous
  angular weight `θ ↦ e_m θ cos θ`; because `F` is jointly `C^∞` on all of `ℝ²`
  (`Work.Stability.smoothOrder` is genuine `C^∞`, not analyticity), differentiating under
  the integral sign `k` times is legitimate and an induction on the order gives `C^n`.
  This is `cmf_parametric_smooth`, proved here from the toolbox
  of `Work.Coercivity.contDiffOn_infty_integral_Itheta`.
* Support: the numerator vanishes pointwise off `[a,b]`, so `cmode m F z = 0` there.
* Integrability: `cmode m F` is continuous on the compact interval `[a,b]` and vanishes
  outside it, and `t^4 ≥ a^4 > 0` there, so `IntegrableOn.of_forall_sdiff_eq_zero`
  transfers integrability from `[a,b]`.
* The bound is Cauchy–Schwarz / Bessel's inequality in the weight `cos θ dθ`
  (`Work.FTS.ClassC.bessel_cmode`, single mode): `(cmode m F z)² eNorm m ≤ ∫ F z θ² cos θ`,
  and the slice energy is bounded on `[a,b]` by continuity of `F` on the compact rectangle.
-/

/-- `cmode m F z`, written with the set integral over `Iθ = [0,π/2]` and the explicit
denominator `eNorm m = ∫_θ e_m θ² cos θ`. -/
private lemma cmode_eq_setIntegral_div (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.cmode m F z
      = (∫ θ in Work.Spaces.Iθ,
          F z θ * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ))
          / Work.EllipticEst.ModalSolution.eNorm m := by
  rw [Work.FTS.PhiStar.Series.cmode,
    Work.EllipticEst.ModalSolution.intervalIntegral_eq_setIntegral
      (fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ),
    Work.EllipticEst.ModalSolution.intervalIntegral_eq_setIntegral
      (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ),
    Work.EllipticEst.ModalSolution.eNorm]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  ring

/-- `cmode m F z`, with the numerator written in the left-associated form used by the
Bessel inequality `Work.FTS.ClassC.bessel_cmode`. -/
private lemma cmode_eq_interval_div (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.cmode m F z
      = (∫ θ in Work.Spaces.Iθ,
          F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
          / Work.EllipticEst.ModalSolution.eNorm m := by
  rw [Work.FTS.PhiStar.Series.cmode,
    Work.EllipticEst.ModalSolution.intervalIntegral_eq_setIntegral
      (fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ),
    Work.EllipticEst.ModalSolution.intervalIntegral_eq_setIntegral
      (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ),
    Work.EllipticEst.ModalSolution.eNorm]

/-- **Smoothness of the angular parametric integral.**  If `F` is jointly `C^∞` on `ℝ²` and
`φ` is continuous on `Iθ`, then `z ↦ ∫_θ F z θ · φ θ` is `C^n` on `(0,∞)` for every `n`.

This is the version of `Work.Coercivity.contDiffOn_infty_integral_Itheta` with no
neighbourhood hypothesis: joint continuity of `∂_z^k F` holds on all of `ℝ²`, so the
domination for the differentiation step is available at every point of `(0,∞)`. -/
private theorem cmf_parametric_smooth {F : ℝ → ℝ → ℝ} {φ : ℝ → ℝ}
    (hF : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry F))
    (hφ : ContinuousOn φ Work.Spaces.Iθ) (n : ℕ) :
    ContDiffOn ℝ n (fun z => ∫ θ in Work.Spaces.Iθ, F z θ * φ θ) (Set.Ioi 0) := by
  have hle : ∀ N : ℕ, ((N : ℕ) : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    intro N
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top
  -- joint continuity of the integrands `(z,θ) ↦ ∂_z^k F (z,θ) · φ θ`
  have hcont : ∀ k : ℕ, ContinuousOn
      (Function.uncurry fun z θ => Work.Spaces.pzIter k F z θ * φ θ)
      (Set.univ ×ˢ Work.Spaces.Iθ) := by
    intro k
    have h0 : ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Function.uncurry F) Set.univ :=
      (hF.contDiffOn).of_le (hle k)
    have h1 : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞)
        (Function.uncurry (Work.Spaces.pzIter k F)) Set.univ :=
      Work.FTS.GalBasis.contDiffOn_uncurry_pzIter_le isOpen_univ h0 k 0 (by omega)
    have h1c : ContinuousOn (Function.uncurry (Work.Spaces.pzIter k F)) Set.univ :=
      contDiffOn_zero.mp h1
    have h2 : ContinuousOn (fun p : ℝ × ℝ => φ p.2) (Set.univ ×ˢ Work.Spaces.Iθ) :=
      hφ.comp continuousOn_snd (fun p hp => hp.2)
    exact (h1c.mono (Set.subset_univ _)).mul h2
  -- differentiation under the integral sign: the derivative of the `k`-th moment is the
  -- `(k+1)`-st moment
  have hderiv : ∀ (k : ℕ) (s : ℝ),
      HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k F s θ * φ θ)
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter (k + 1) F s θ * φ θ) s := by
    intro k s
    refine Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt (V := Set.univ)
      isOpen_univ (Set.mem_univ s) (hcont k) (hcont (k + 1)) ?_
    intro θ hθ s' hs'
    have h0 : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry F) Set.univ :=
      (hF.contDiffOn).of_le (hle (k + 1))
    have hsl : DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k F z' θ) s' :=
      Work.FTS.GalBasis.differentiableAt_slice_pzIter isOpen_univ h0 (i := k) (by omega)
        (Set.mem_univ (s', θ))
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      using hsl.hasDerivAt.mul_const (φ θ)
  -- `C^n` for all the iterated moments, by induction on `n`
  have hmain : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k F s θ * φ θ) Set.univ := by
    intro n
    induction n with
    | zero =>
      intro k
      exact (contDiffOn_zero (𝕜 := ℝ)).2
        (Work.Coercivity.continuousOn_integral_Itheta_of_continuousOn isOpen_univ (hcont k))
    | succ n ih =>
      intro k
      rw [Nat.cast_add, Nat.cast_one]
      refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
        (f := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k F s θ * φ θ)
        (n := ((n : ℕ) : WithTop ℕ∞)) (s := Set.univ) isOpen_univ).2 ⟨?_, ?_, ?_⟩
      · intro s _
        exact (hderiv k s).differentiableAt.differentiableWithinAt
      · intro h; exact absurd h (by simp)
      · exact (ih (k + 1)).congr (fun s _ => (hderiv k s).deriv)
  exact (hmain n 0).mono (Set.subset_univ _)

/-- **Smoothness of `cmode`.**  For a jointly `C^∞` source `F`, the mode coefficient
`cmode m F` is `C^n` on `(0,∞)`. -/
private theorem cmode_contDiffOn {F : ℝ → ℝ → ℝ}
    (hFsm : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry F)) (m n : ℕ) :
    ContDiffOn ℝ n (Work.FTS.PhiStar.Series.cmode m F) (Set.Ioi 0) := by
  have hφ : ContinuousOn
      (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) Work.Spaces.Iθ :=
    ((Work.EllipticEst.ModalSolution.continuous_eFam m).mul Real.continuous_cos).continuousOn
  have h := cmf_parametric_smooth (F := F)
    (φ := fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) hFsm hφ n
  have h2 : ContDiffOn ℝ n
      (fun z => ∫ θ in Work.Spaces.Iθ,
        F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) (Set.Ioi 0) :=
    h.congr (fun z _ =>
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring))
  exact (h2.div_const (Work.EllipticEst.ModalSolution.eNorm m)).congr
    (fun z _ => cmode_eq_interval_div m F z)

/-- **The uniform bound on the modes.**  If `F` is jointly continuous, then on the compact
interval `[a,b]` all the mode coefficients are bounded by a single constant times
`1/√(eNorm m)`.  (Only continuity of `F` is used, not the support hypothesis of
`cmode_facts`; the "Cauchy–Schwarz" content is Bessel's inequality in the weight
`cos θ dθ`, applied to the single mode `m`.) -/
private theorem cmode_abs_le_aux {a b : ℝ} {F : ℝ → ℝ → ℝ}
    (hFc : Continuous (Function.uncurry F)) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, ∀ t ∈ Set.Icc a b,
        |Work.FTS.PhiStar.Series.cmode m F t|
          ≤ K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
  -- `F` is bounded on the compact rectangle `[a,b] × Iθ`
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hFc.continuousOn.mono (Set.subset_univ _))
  have hC' : ∀ p ∈ Set.Icc a b ×ˢ Work.Spaces.Iθ, ‖Function.uncurry F p‖ ≤ max C 0 :=
    fun p hp => le_trans (hC p hp) (le_max_left _ _)
  have hC'nn : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro m t ht
  have hslice : Continuous (fun θ => F t θ) :=
    hFc.comp (continuous_const.prodMk continuous_id)
  have hFbd : ∀ θ ∈ Work.Spaces.Iθ, |F t θ| ≤ max C 0 := by
    intro θ hθ
    have := hC' (t, θ) ⟨ht, hθ⟩
    simpa [Function.uncurry, Real.norm_eq_abs] using this
  -- the slice energy is bounded by `(max C 0)^2`
  have hfint : IntegrableOn (fun θ => (F t θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    (((hslice.pow 2).mul Real.continuous_cos).continuousOn).integrableOn_compact isCompact_Icc
  have hgint : IntegrableOn (fun θ => (max C 0) ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    (((continuous_const.mul Real.continuous_cos).continuousOn)).integrableOn_compact
      isCompact_Icc
  have hcos : (∫ θ in Work.Spaces.Iθ, Real.cos θ) = 1 := by
    rw [← Work.EllipticEst.ModalSolution.intervalIntegral_eq_setIntegral Real.cos]
    rw [integral_cos, Real.sin_pi_div_two, Real.sin_zero, sub_zero]
  have hE : (∫ θ in Work.Spaces.Iθ, (F t θ) ^ 2 * Real.cos θ) ≤ (max C 0) ^ 2 := by
    have hpt : ∀ θ ∈ Work.Spaces.Iθ,
        (F t θ) ^ 2 * Real.cos θ ≤ (max C 0) ^ 2 * Real.cos θ := by
      intro θ hθ
      have h1 : (F t θ) ^ 2 ≤ (max C 0) ^ 2 :=
        sq_le_sq' (abs_le.mp (hFbd θ hθ)).1 (abs_le.mp (hFbd θ hθ)).2
      have hc : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      exact mul_le_mul_of_nonneg_right h1 hc
    have hmono := MeasureTheory.setIntegral_mono_on hfint hgint measurableSet_Icc hpt
    rw [MeasureTheory.integral_const_mul, hcos, mul_one] at hmono
    exact hmono
  -- Bessel's inequality, restricted to the single mode `m`
  have hb := Work.FTS.ClassC.bessel_cmode F t m hslice.aestronglyMeasurable hfint
  have hnn : ∀ i ∈ Finset.range (m + 1), 0 ≤
      (∫ θ in Work.Spaces.Iθ,
          F t θ * Work.FTS.PhiStar.Gegenbauer.eFam i θ * Real.cos θ) ^ 2
        / (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam i θ ^ 2 * Real.cos θ) := by
    intro i _
    exact div_nonneg (sq_nonneg _) (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos i))
  have hsingle := Finset.single_le_sum hnn (Finset.mem_range.mpr (Nat.lt_succ_self m))
  have hterm : (∫ θ in Work.Spaces.Iθ,
        F t θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
      / (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
      ≤ (max C 0) ^ 2 := le_trans hsingle (le_trans hb hE)
  have hden : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  have hD : Work.EllipticEst.ModalSolution.eNorm m
      = ∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ := by
    rw [Work.EllipticEst.ModalSolution.eNorm]
  have hkey : (Work.FTS.PhiStar.Series.cmode m F t) ^ 2
      * Work.EllipticEst.ModalSolution.eNorm m ≤ (max C 0) ^ 2 := by
    have hDpos : 0 < ∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ := by
      rw [← hD]; exact hden
    have harith : ((∫ θ in Work.Spaces.Iθ,
            F t θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
          / (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)) ^ 2
        * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
        = (∫ θ in Work.Spaces.Iθ,
            F t θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
          / (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
      field_simp
    rw [cmode_eq_interval_div, hD, harith]
    exact hterm
  -- pass from `cmode² · eNorm m ≤ (max C 0)²` to the stated bound
  have hX : (Work.FTS.PhiStar.Series.cmode m F t
      * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) ^ 2 ≤ (max C 0 + 1) ^ 2 := by
    have h1 : (Work.FTS.PhiStar.Series.cmode m F t
        * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) ^ 2
        = (Work.FTS.PhiStar.Series.cmode m F t) ^ 2
          * Work.EllipticEst.ModalSolution.eNorm m := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hden)]
    rw [h1]
    nlinarith [hkey, hC'nn]
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hden)]
  have h2 : |Work.FTS.PhiStar.Series.cmode m F t
      * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)| ≤ max C 0 + 1 := by
    have := (sq_le_sq.mp hX)
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ max C 0 + 1)] at this
  simpa [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using h2

theorem cmode_facts {a b : ℝ} (ha : 0 < a) {F : ℝ → ℝ → ℝ}
    (hFsm : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry F))
    (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → F z θ = 0) :
    (∀ m : ℕ, ∀ n : ℕ, ContDiffOn ℝ n (Work.FTS.PhiStar.Series.cmode m F) (Set.Ioi 0))
    ∧ (∀ m : ℕ, ∀ z : ℝ, z ∉ Set.Icc a b → Work.FTS.PhiStar.Series.cmode m F z = 0)
    ∧ (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ioi 1))
    ∧ (∀ m : ℕ, MeasureTheory.IntegrableOn
        (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    ∧ (∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, ∀ t ∈ Set.Icc a b,
        |Work.FTS.PhiStar.Series.cmode m F t|
          ≤ K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) := by
  -- (2) the support condition descends to `cmode`
  have hzero : ∀ m : ℕ, ∀ z : ℝ,
      z ∉ Set.Icc a b → Work.FTS.PhiStar.Series.cmode m F z = 0 := by
    intro m z hz
    have hfun : (fun θ : ℝ => F z θ
          * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)) = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [hsupp z θ hz, zero_mul]
    rw [cmode_eq_setIntegral_div, hfun]
    simp
  -- `[a,b] ⊆ (0,∞)`, and `cmode m F` is continuous on `[a,b]`
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun t ht => lt_of_lt_of_le ha ht.1
  have hcont : ∀ m : ℕ, ContinuousOn (Work.FTS.PhiStar.Series.cmode m F) (Set.Icc a b) :=
    fun m => ((cmode_contDiffOn hFsm m 1).continuousOn).mono hsub
  refine ⟨fun m n => cmode_contDiffOn hFsm m n, hzero, ?_, ?_, ?_⟩
  · -- (3) square-integrability on `(1,∞)`
    intro m
    have h2 : IntegrableOn (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
        (Set.Icc a b) := ((hcont m).pow 2).integrableOn_compact isCompact_Icc
    refine h2.of_forall_sdiff_eq_zero measurableSet_Ioi (fun t ht => ?_)
    rw [hzero m t ht.2]
    norm_num
  · -- (4) integrability of `t ↦ cmode m F t ² / t⁴` on `(0,1)`
    intro m
    have h2 : IntegrableOn (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 / t ^ 4)
        (Set.Icc a b) := by
      have hn : ContinuousOn
          (fun t : ℝ => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 / t ^ 4) (Set.Icc a b) := by
        refine ((hcont m).pow 2).div (continuous_pow 4 |>.continuousOn) (fun t ht => ?_)
        exact pow_ne_zero 4 (ne_of_gt (lt_of_lt_of_le ha ht.1))
      exact hn.integrableOn_compact isCompact_Icc
    refine h2.of_forall_sdiff_eq_zero measurableSet_Ioo (fun t ht => ?_)
    rw [hzero m t ht.2]
    simp
  · -- (5) the uniform Cauchy–Schwarz bound
    exact cmode_abs_le_aux hFsm.continuous

end Work.FTS.ClassCHon.CmpSupp
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.WtDerivTsum =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology BigOperators

namespace Work.FTS.PhiStar.FlatWAux

set_option maxHeartbeats 1000000

/-- The majorant `(2m+1)/(λ_m √(2m+1))` is summable: `(2m+1)/(λ_m √(2m+1)) = √(2m+1)/λ_m` is
asymptotic to `(√2/4) m^{-3/2}`, and `Σ m^{-3/2}` converges.  (At `m = 0` the quotient is `0`
because Lean's division by zero is total, so that term causes no difficulty.) -/
lemma summable_lam_sqrt_aux :
    Summable (fun m : ℕ => (2 * (m : ℝ) + 1)
      / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
  have hbase : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(3 / 2 : ℝ))) :=
      (Real.summable_nat_rpow (p := (-(3 / 2 : ℝ)))).mpr (by norm_num)
    have h' := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(3 / 2 : ℝ))) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  refine Summable.of_norm_bounded (hbase.mul_left (Real.sqrt 2)) (fun m => ?_)
  rw [Real.norm_eq_abs]
  by_cases hm : m = 0
  · subst hm
    have h0 : (2 * ((0 : ℕ) : ℝ) + 1)
        / (Gegenbauer.lam 0 * Real.sqrt (2 * ((0 : ℕ) : ℝ) + 1)) = 0 := by
      rw [show Gegenbauer.lam 0 = 0 by norm_num [Gegenbauer.lam]]
      norm_num
    rw [h0, abs_zero]
    positivity
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hlam_pos : 0 < Gegenbauer.lam m := by
      simp only [Gegenbauer.lam]; nlinarith
    have hA : (0 : ℝ) ≤ (2 * (m : ℝ) + 1)
        / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
      div_nonneg (by positivity) (mul_nonneg hlam_pos.le (Real.sqrt_nonneg _))
    rw [abs_of_nonneg hA]
    have hsne : Real.sqrt (2 * (m : ℝ) + 1) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hsq : Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)
        = 2 * (m : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
    -- divide numerator and denominator by `√(2m+1)`
    have hstep : (2 * (m : ℝ) + 1) / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
        = Real.sqrt (2 * (m : ℝ) + 1) / Gegenbauer.lam m := by
      rw [div_eq_iff (mul_ne_zero (ne_of_gt hlam_pos) hsne)]
      have h1 : Real.sqrt (2 * (m : ℝ) + 1) / Gegenbauer.lam m
          * (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          = Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1) := by
        rw [div_mul_eq_mul_div,
          show Real.sqrt (2 * (m : ℝ) + 1) * (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            = Gegenbauer.lam m
                * (Real.sqrt (2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)) by ring,
          mul_div_cancel_left₀ _ (ne_of_gt hlam_pos)]
      rw [h1, hsq]
    rw [hstep]
    -- `√(2m+1) ≤ √2·√(m+1)`
    have hsle : Real.sqrt (2 * (m : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (by linarith)
    -- `(m+1)^2 ≤ λ_m`
    have hlam2 : ((m : ℝ) + 1) ^ 2 ≤ Gegenbauer.lam m := by
      simp only [Gegenbauer.lam]; nlinarith
    have hb2pos : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 := by positivity
    have hnum : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1) := by positivity
    -- the `rpow` identity `√(m+1)/(m+1)^2 = (m+1)^{-3/2}`
    have hcore : Real.sqrt ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2
        = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
      have hx : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_natCast ((m : ℝ) + 1) 2,
        ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
      have hexp : (1 : ℝ) / 2 + -(((2 : ℕ)) : ℝ) = -(3 / 2) := by norm_num
      exact congrArg (fun e : ℝ => ((m : ℝ) + 1) ^ e) hexp
    calc Real.sqrt (2 * (m : ℝ) + 1) / Gegenbauer.lam m
        ≤ (Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1)) / Gegenbauer.lam m :=
          div_le_div_of_nonneg_right hsle hlam_pos.le
      _ = Real.sqrt 2 * (Real.sqrt ((m : ℝ) + 1) / Gegenbauer.lam m) := by ring
      _ ≤ Real.sqrt 2 * (Real.sqrt ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_left (Real.sqrt_nonneg ((m : ℝ) + 1)) hb2pos hlam2
      _ = Real.sqrt 2 * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by rw [hcore]

theorem WtDerivTsum (ψ : ℝ → ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hQ0 : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ θ : ℝ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.FlatWAux.Qm m θ| ≤ C * (2 * (m : ℝ) + 1) ^ 2)
    (hL : ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.PhiStar.Linv
        (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') y|
        ≤ K * (Work.FTS.PhiStar.Gegenbauer.lam m * (2 * (m : ℝ) + 1))) :
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      deriv (Work.FTS.PhiStar.FlatWAux.Wt ψ j) θ
        = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j
            * Work.FTS.PhiStar.Linv
                (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
                  * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ := by
  obtain ⟨C, hC, hdec⟩ := hdec
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  obtain ⟨K, hK, hL⟩ := hL
  intro θ hθ
  obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hj'' : j = j' + 1 := hj'
  rw [hj'']
  -- the summable majorant of the differentiated series
  have hu : Summable (fun m : ℕ => C * K * ((2 * (m : ℝ) + 1)
      / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))) :=
    summable_lam_sqrt_aux.mul_left (C * K)
  -- the `m`-th summand and its derivative
  have hQdiff : ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      HasDerivAt (Qm m)
        (Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') y) y := by
    intro m y hy
    have h1 : HasDerivAt (fun z : ℝ => Gegenbauer.eFam m z) (deriv (Gegenbauer.eFam m) y) y :=
      (((contDiff_eFam_fam m).differentiable (by norm_num)).differentiableAt).hasDerivAt
    have h2 : HasDerivAt Work.Construction.s2 (deriv Work.Construction.s2 y) y :=
      (differentiable_s2_fam.differentiableAt).hasDerivAt
    have h3 := h1.div h2 (linv_s2_ne_zero hy)
    have h4 : deriv (fun z : ℝ => Gegenbauer.eFam m z / Work.Construction.s2 z) y
        = (deriv (Gegenbauer.eFam m) y * Work.Construction.s2 y
            - Gegenbauer.eFam m y * deriv Work.Construction.s2 y)
              / Work.Construction.s2 y ^ 2 := h3.deriv
    refine h3.congr_deriv ?_
    rw [← h4]
    exact FamDerivDivLinv m hy
  have hderiv : ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      HasDerivAt (fun z => Work.FTS.PhiStar.Series.bmode m ψ
          * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Qm m z)
        (Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
          * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') y) y :=
    fun m y hy => (hQdiff m y hy).const_mul _
  -- the uniform bound on the derivatives
  have hbdd : ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      ‖Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
        * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') y‖
      ≤ C * K * ((2 * (m : ℝ) + 1)
          / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
    intro m y hy
    rw [Real.norm_eq_abs]
    by_cases hm : m = 0
    · subst hm
      have hz : ((Gegenbauer.lam 0)⁻¹) ^ (j' + 1) = 0 := by
        rw [show Gegenbauer.lam 0 = 0 by norm_num [Gegenbauer.lam], inv_zero]
        exact zero_pow (Nat.succ_ne_zero j')
      have hzero : Work.FTS.PhiStar.Series.bmode 0 ψ * ((Gegenbauer.lam 0)⁻¹) ^ (j' + 1)
          * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam 0 * Gegenbauer.eFam 0 θ') y = 0 := by
        rw [hz, mul_zero, zero_mul]
      rw [hzero, abs_zero]
      have hl0 : (0 : ℝ) ≤ Gegenbauer.lam 0 := by norm_num [Gegenbauer.lam]
      exact mul_nonneg (mul_nonneg hC.le hK.le)
        (div_nonneg (by norm_num) (mul_nonneg hl0 (Real.sqrt_nonneg _)))
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hlam_pos : 0 < Gegenbauer.lam m := by
        simp only [Gegenbauer.lam]; nlinarith
      have hlam1 : (1 : ℝ) ≤ Gegenbauer.lam m := by
        simp only [Gegenbauer.lam]; nlinarith
      have hinvnn : (0 : ℝ) ≤ (Gegenbauer.lam m)⁻¹ := inv_nonneg.mpr hlam_pos.le
      have hpownn : (0 : ℝ) ≤ ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) := pow_nonneg hinvnn _
      -- `(λ_m⁻¹)^{j'+1}·λ_m ≤ 1`
      have hcancel : ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Gegenbauer.lam m ≤ 1 := by
        calc ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Gegenbauer.lam m
            = ((Gegenbauer.lam m)⁻¹) ^ j' * (Gegenbauer.lam m)⁻¹ * Gegenbauer.lam m := by
              rw [pow_succ]
          _ = ((Gegenbauer.lam m)⁻¹) ^ j' := by
              rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hlam_pos), mul_one]
          _ ≤ 1 := pow_le_one₀ hinvnn ((inv_le_one₀ hlam_pos).mpr hlam1)
      have hK21 : (0 : ℝ) ≤ K * (2 * (m : ℝ) + 1) := by positivity
      rw [abs_mul, abs_mul, abs_of_nonneg hpownn]
      calc |Work.FTS.PhiStar.Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
            * |Work.FTS.PhiStar.Linv
                (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') y|
          ≤ |Work.FTS.PhiStar.Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
              * (K * (Gegenbauer.lam m * (2 * (m : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left (hL m y hy) (mul_nonneg (abs_nonneg _) hpownn)
        _ = |Work.FTS.PhiStar.Series.bmode m ψ| * ((((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
              * Gegenbauer.lam m) * (K * (2 * (m : ℝ) + 1))) := by ring
        _ ≤ |Work.FTS.PhiStar.Series.bmode m ψ| * (1 * (K * (2 * (m : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcancel hK21) (abs_nonneg _)
        _ ≤ (C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
              * (K * (2 * (m : ℝ) + 1)) := by
            calc |Work.FTS.PhiStar.Series.bmode m ψ| * (1 * (K * (2 * (m : ℝ) + 1)))
                = |Work.FTS.PhiStar.Series.bmode m ψ| * (K * (2 * (m : ℝ) + 1)) := by ring
              _ ≤ (C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
                    * (K * (2 * (m : ℝ) + 1)) :=
                  mul_le_mul_of_nonneg_right (hdec m hm1) hK21
        _ = C * K * ((2 * (m : ℝ) + 1)
              / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by ring
  -- summability of the series at the base point `π/4`
  have hsum0 : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
      * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Qm m (Real.pi / 4)) := by
    refine Summable.of_norm_bounded (hu.mul_left (Cg / K)) (fun m => ?_)
    rw [Real.norm_eq_abs]
    by_cases hm : m = 0
    · subst hm
      have hz : ((Gegenbauer.lam 0)⁻¹) ^ (j' + 1) = 0 := by
        rw [show Gegenbauer.lam 0 = 0 by norm_num [Gegenbauer.lam], inv_zero]
        exact zero_pow (Nat.succ_ne_zero j')
      have hzero : Work.FTS.PhiStar.Series.bmode 0 ψ * ((Gegenbauer.lam 0)⁻¹) ^ (j' + 1)
          * Qm 0 (Real.pi / 4) = 0 := by
        rw [hz, mul_zero, zero_mul]
      rw [hzero, abs_zero]
      have hl0 : (0 : ℝ) ≤ Gegenbauer.lam 0 := by norm_num [Gegenbauer.lam]
      exact mul_nonneg (div_nonneg hCg.le hK.le)
        (mul_nonneg (mul_nonneg hC.le hK.le)
          (div_nonneg (by norm_num) (mul_nonneg hl0 (Real.sqrt_nonneg _))))
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hlam_pos : 0 < Gegenbauer.lam m := by
        simp only [Gegenbauer.lam]; nlinarith
      have hlam1 : (1 : ℝ) ≤ Gegenbauer.lam m := by
        simp only [Gegenbauer.lam]; nlinarith
      have hinvnn : (0 : ℝ) ≤ (Gegenbauer.lam m)⁻¹ := inv_nonneg.mpr hlam_pos.le
      have hpownn : (0 : ℝ) ≤ ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) := pow_nonneg hinvnn _
      have hpow1 : ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) ≤ 1 :=
        pow_le_one₀ hinvnn ((inv_le_one₀ hlam_pos).mpr hlam1)
      have hQ : Qm m (Real.pi / 4) = Gegenbauer.eFam m (Real.pi / 4) := by
        have hs : Work.Construction.s2 (Real.pi / 4) = 1 := by
          rw [Work.Construction.s2_eq, show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
            Real.sin_pi_div_two]
        simp only [Qm, hs, div_one]
      have he : |Gegenbauer.eFam m (Real.pi / 4)| ≤ Cg * (2 * (m : ℝ) + 1) :=
        hgr m (Real.pi / 4) (by constructor <;> linarith [Real.pi_pos])
      rw [abs_mul, abs_mul, abs_of_nonneg hpownn, hQ]
      calc |Work.FTS.PhiStar.Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
            * |Gegenbauer.eFam m (Real.pi / 4)|
          = (|Work.FTS.PhiStar.Series.bmode m ψ| * |Gegenbauer.eFam m (Real.pi / 4)|)
              * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) := by ring
        _ ≤ (C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
              * (Cg * (2 * (m : ℝ) + 1))) * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (hdec m hm1) he (abs_nonneg _) (by positivity)) hpownn
        _ = C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
              * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * (Cg * (2 * (m : ℝ) + 1)) := by ring
        _ ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) * 1
              * (Cg * (2 * (m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow1 (by positivity))
              (by positivity)
        _ = C * Cg * ((2 * (m : ℝ) + 1)
              / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by ring
        _ = (Cg / K) * (C * K * ((2 * (m : ℝ) + 1)
              / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))) := by
            have hnum : Cg * (C * K * ((2 * (m : ℝ) + 1)
                / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))))
                = (C * Cg * ((2 * (m : ℝ) + 1)
                    / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))) * K := by ring
            rw [div_mul_eq_mul_div, hnum, mul_div_cancel_right₀ _ (ne_of_gt hK)]
  have hmain : HasDerivAt
      (fun z : ℝ => ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Qm m z)
      (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
        * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') θ) θ :=
    hasDerivAt_tsum_of_isPreconnected
      (u := fun m : ℕ => C * K * ((2 * (m : ℝ) + 1)
        / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))))
      (g := fun m z => Work.FTS.PhiStar.Series.bmode m ψ
        * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Qm m z)
      (g' := fun m z => Work.FTS.PhiStar.Series.bmode m ψ
        * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
        * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') z)
      hu isOpen_Ioo isPreconnected_Ioo hderiv hbdd
      (show Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩) hsum0 hθ
  simp only [Wt]
  exact hmain.deriv

end Work.FTS.PhiStar.FlatWAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.DecayRem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-- **Conjunct 4 of the target** (conditionally on the crux estimates): for every `θ ∈ Iθ` the
`tsum` defining `psiSeries` of the remainder source tends to `0` as `z → ∞`. -/
theorem psiSeries_tendsto_zero_RemSource (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α)
    (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (hbig : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ z : ℝ, 1 ≤ z →
      |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        ≤ C / (z * ((m : ℝ) + 1)))
    (hsum : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Summable (fun m : ℕ => ‖acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ‖)) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ)
        Filter.atTop (nhds 0) := by
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  obtain ⟨Cb, hCb, hbig⟩ := hbig
  have hzero : bmode 0 ψ = 0 := bmode_zero ψ hψ.moment
  intro θ hθ
  set K : ℝ := α ^ 2 * Cd * Cb * Cg with hK
  have hmaj : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(2 : ℝ))) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) :=
      (Real.summable_nat_rpow (p := (-(2 : ℝ)))).mpr (by norm_num)
    have h' := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  have hterm : ∀ z : ℝ, 1 ≤ z → ∀ m : ℕ,
      ‖acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
        ≤ (K / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)) := by
    intro z hz m
    by_cases hm : m = 0
    · subst hm
      have h0 : acoeff α 0 (Work.FTS.PhiStar.RemSource α ψ) z *
          Work.FTS.PhiStar.Gegenbauer.eFam 0 θ = 0 := by
        rw [acoeff_RemSource, hzero]
        simp
      rw [h0, norm_zero]
      have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
      have : 0 < K / z := by
        rw [hK]
        have h1 : 0 < 1 / z := one_div_pos.mpr hz0
        positivity
      exact mul_nonneg (le_of_lt this) (by positivity)
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      rw [Real.norm_eq_abs, acoeff_RemSource]
      calc |α ^ 2 * bmode m ψ
              * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          = |α ^ 2| * |bmode m ψ|
              * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
              * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by rw [abs_mul, abs_mul, abs_mul]
        _ = α ^ 2 * |bmode m ψ|
              * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
              * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by
            rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
        _ ≤ (α ^ 2 * (Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))))
              * (Cb / (z * ((m : ℝ) + 1)))
              * (Cg * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ))) := by
            have hb := hdec m hm1
            have hr := hbig m hm1 z hz
            have he := hgr m θ hθ
            gcongr
        _ = (K / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)) := by
            have hp : ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) * ((m : ℝ) + 1) ^ (-(1 : ℝ))
                * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) = ((m : ℝ) + 1) ^ (-(2 : ℝ)) := by
              rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
              norm_num
            have hinv : Cb / (z * ((m : ℝ) + 1))
                = (Cb / z) * ((m : ℝ) + 1) ^ (-(1 : ℝ)) := by
              rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1), Real.rpow_one,
                div_eq_mul_inv]
              field_simp
            rw [hinv, ← hp, hK]
            ring
  have hbound : ∀ z : ℝ, 1 ≤ z →
      ‖psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ‖
        ≤ (K * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-(2 : ℝ)))) / z := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
    have hs := hsum z hz0 θ hθ
    calc ‖psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ‖
        = ‖∑' m : ℕ, acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ := rfl
      _ ≤ ∑' m : ℕ, ‖acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' m : ℕ, (K / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)) :=
          Summable.tsum_le_tsum (fun m => hterm z hz m) hs (hmaj.mul_left (K / z))
      _ = (K * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-(2 : ℝ)))) / z := by
          rw [Summable.tsum_mul_left _ hmaj]
          ring
  have hlim : Filter.Tendsto
      (fun z : ℝ => (K * (∑' m : ℕ, ((m : ℝ) + 1) ^ (-(2 : ℝ)))) / z)
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hnorm : Filter.Tendsto
      (fun z : ℝ => ‖psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ‖)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall (fun z => norm_nonneg _))
      (eventually_atTop.mpr ⟨1, fun z hz => hbound z hz⟩)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

end Work.FTS.PhiStar.Series
end
end
