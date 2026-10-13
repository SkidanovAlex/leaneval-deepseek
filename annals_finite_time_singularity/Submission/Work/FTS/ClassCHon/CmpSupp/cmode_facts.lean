import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.ClassC.bessel_cmode
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Coercivity.contDiffOn_infty_integral_Itheta
import Submission.Work.FTS.GalBasis.exists_mixed_bound
import Submission.Work.Stability.Cutoff

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
