/-
# `ModalSolR/PerModeInner` — the inner `θ`-integral of the mode-`m` operator
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.H2.ModalSolR.PerModeDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR
/-! ## The inner `θ`-integral -/

/-- **The inner `θ`-integral of the mode-`m` operator.**  For a smooth test function supported in
the box `(a,b) × (c,d)` and `z ∈ [a,b]`, the pairing of `bslOp α φ` with the mode `e_m` is the
mode-`m` radial operator applied to the angular moment `Θ`. -/
theorem inner_theta_eq (α : ℝ) (m : ℕ) {φ : ℝ → ℝ → ℝ}
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    {a b c d : ℝ} (ha : 0 < a) (hab : a < b) (hc0 : 0 < c) (hcd : c < d) (hd : d < π / 2)
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0)
    {z : ℝ} (hz : z ∈ Set.Icc a b) :
    (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Elliptic.bslOp α φ z θ * Real.cos θ)
      = -(α ^ 2) * z ^ 2 * deriv (deriv (Theta m φ)) z
        - (α * (5 + α) * z) * deriv (Theta m φ) z
        + Work.FTS.PhiStar.Gegenbauer.lam m * Theta m φ z := by
  have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
  have hφsm : Work.FTS.EllipticEst.SmoothOpen φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall φ).mpr (fun n => (hφ n).contDiffOn)
  -- ## vanishing of each summand off `(c,d)`
  have hvan1 : ∀ θ ∉ Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Work.Spaces.pzIter 2 φ z θ * Real.cos θ = 0 := by
    intro θ hθ
    rw [pzIter_eq_zero_of_slice_zero (φ := φ) (θ := θ)
      (fun z' => test_vanishes_off_theta hbox (fun hm => hθ (Set.Ioo_subset_Icc_self hm))) 2 z]
    ring
  have hvan2 : ∀ θ ∉ Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Work.Spaces.pz φ z θ * Real.cos θ = 0 := by
    intro θ hθ
    have h := pzIter_eq_zero_of_slice_zero (φ := φ) (θ := θ)
      (fun z' => test_vanishes_off_theta hbox (fun hm => hθ (Set.Ioo_subset_Icc_self hm))) 1 z
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] at h
    rw [h]
    ring
  have hvan3 : ∀ θ ∉ Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Work.Elliptic.Lzero φ z θ * Real.cos θ = 0 := by
    intro θ hθ
    rw [Lzero_eq_zero_of_theta_not_mem hbox hθ]
    ring
  -- ## the slices of `φ` at fixed `z` are continuous
  have hslice : ∀ {f : ℝ → ℝ → ℝ}, ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
        Work.FTS.EllipticEst.Q0 → ContinuousOn (fun θ => f z θ) (Set.Icc c d) := by
    intro f hf
    refine hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun θ hθ => ?_)
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨hz0, lt_of_lt_of_le hc0 hθ.1, lt_of_le_of_lt hθ.2 hd⟩
  have hcont1 : ContinuousOn (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Work.Spaces.pzIter 2 φ z θ * Real.cos θ) (Set.Icc c d) :=
    ((Work.FTS.H2.ModalSol.ModeIdent.continuous_eFam m).continuousOn.mul
      (hslice (hφsm.pzIter 2).continuousOn)).mul Real.continuous_cos.continuousOn
  have hcont2 : ContinuousOn (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Work.Spaces.pz φ z θ * Real.cos θ) (Set.Icc c d) :=
    ((Work.FTS.H2.ModalSol.ModeIdent.continuous_eFam m).continuousOn.mul
      (hslice hφsm.pz.continuousOn)).mul Real.continuous_cos.continuousOn
  have hcont3 : ContinuousOn (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Work.Elliptic.Lzero φ z θ * Real.cos θ) (Set.Icc c d) :=
    ((Work.FTS.H2.ModalSol.ModeIdent.continuous_eFam m).continuousOn.mul
      (hslice (Work.EllipticEst.ModalSolution.continuousOn_Lzero hφsm))).mul
        Real.continuous_cos.continuousOn
  have hInt1 : IntegrableOn (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Work.Spaces.pzIter 2 φ z θ * Real.cos θ) (Set.Icc c d) :=
    hcont1.integrableOn_compact isCompact_Icc
  have hInt2 : IntegrableOn (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Work.Spaces.pz φ z θ * Real.cos θ) (Set.Icc c d) :=
    hcont2.integrableOn_compact isCompact_Icc
  have hInt3 : IntegrableOn (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Work.Elliptic.Lzero φ z θ * Real.cos θ) (Set.Icc c d) :=
    hcont3.integrableOn_compact isCompact_Icc
  -- ## expansion of the operator
  have hexp : ∀ θ : ℝ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Work.Elliptic.bslOp α φ z θ * Real.cos θ
      = (-(α ^ 2 * z ^ 2)) * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.Spaces.pzIter 2 φ z θ * Real.cos θ)
        + (-(α * (5 + α) * z)) * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.Spaces.pz φ z θ * Real.cos θ)
        + Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.Lzero φ z θ * Real.cos θ := by
    intro θ
    rw [Work.Elliptic.bslOp_apply]
    ring
  have hP : IntegrableOn (fun θ => (-(α ^ 2 * z ^ 2)) * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Spaces.pzIter 2 φ z θ * Real.cos θ)
      + (-(α * (5 + α) * z)) * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Spaces.pz φ z θ * Real.cos θ)) (Set.Icc c d) :=
    (hInt1.const_mul (-(α ^ 2 * z ^ 2))).add (hInt2.const_mul (-(α * (5 + α) * z)))
  rw [setIntegral_congr_fun measurableSet_Icc (fun θ _ => hexp θ),
    MeasureTheory.integral_add hP hInt3,
    MeasureTheory.integral_add (hInt1.const_mul (-(α ^ 2 * z ^ 2)))
      (hInt2.const_mul (-(α * (5 + α) * z))),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- ## identification of the `Iθ`-integrals with the moments
  have hA1 : deriv (Theta m φ) z
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Work.Spaces.pz φ z θ * Real.cos θ := by
    rw [show deriv (Theta m φ) z = deriv (fun z' => ∫ θ in Work.Spaces.Iθ,
        φ z' θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) z from rfl,
      ((thetaMomentSmooth hφ hφc hφs m).2.1 z hz0).deriv]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  have hA2 : deriv (deriv (Theta m φ)) z
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Work.Spaces.pzIter 2 φ z θ * Real.cos θ := by
    have hΘ1 : deriv (Theta m φ) =ᶠ[𝓝 z] fun z' =>
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz φ z' θ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
      filter_upwards [isOpen_Ioi.mem_nhds hz0] with z' hz'
      show deriv (fun z' => ∫ θ in Work.Spaces.Iθ,
          φ z' θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) z' = _
      exact ((thetaMomentSmooth hφ hφc hφs m).2.1 z' hz').deriv
    rw [show deriv (deriv (Theta m φ)) z = deriv (fun z' =>
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz φ z' θ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) z from hΘ1.deriv_eq,
      ((thetaMomentSmooth hφ hφc hφs m).2.2 z hz0).deriv]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  have hA3 : (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Elliptic.Lzero φ z θ * Real.cos θ)
      = Work.FTS.PhiStar.Gegenbauer.lam m * Theta m φ z := by
    rw [Theta]
    rw [show (∫ θ in Work.Spaces.Iθ, φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * φ z θ * Real.cos θ from
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
    exact angularEigenIdentity hφ hφc hφs m hz0
  rw [show (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Spaces.pzIter 2 φ z θ * Real.cos θ) = deriv (deriv (Theta m φ)) z from
      (setIntegral_Icc_cd_eq_Iθ hc0.le hd.le hvan1).trans hA2.symm,
    show (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Spaces.pz φ z θ * Real.cos θ) = deriv (Theta m φ) z from
      (setIntegral_Icc_cd_eq_Iθ hc0.le hd.le hvan2).trans hA1.symm,
    show (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.Elliptic.Lzero φ z θ * Real.cos θ)
        = Work.FTS.PhiStar.Gegenbauer.lam m * Theta m φ z from
      (setIntegral_Icc_cd_eq_Iθ hc0.le hd.le hvan3).trans hA3]
  ring


/-! ## The per-mode identity on the box -/

/-- **The per-mode weak identity, on the box containing the support of `φ`.** -/
theorem perMode_box (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) (hm : 1 ≤ m)
    {F φ : ℝ → ℝ → ℝ}
    (hc2 : MeasureTheory.IntegrableOn (fun t => Work.FTS.PhiStar.Series.cmode m F t ^ 2)
      (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (Work.FTS.PhiStar.Series.cmode m F)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφs : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    {a b c d : ℝ} (ha : 0 < a) (hab : a < b) (hc0 : 0 < c) (hcd : c < d) (hd : d < π / 2)
    (hbox : ∀ p : ℝ × ℝ, p ∉ Set.Ioo a b ×ˢ Set.Ioo c d → φ p.1 p.2 = 0) :
    (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
        (Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.Elliptic.bslOp α φ z θ) * (z ^ ((5 - α) / α) * Real.cos θ))
      = ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
          (Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * φ z θ * (z ^ ((5 - α) / α) * Real.cos θ) := by
  set q : ℝ := (5 - α) / α with hq
  set A : ℝ → ℝ := Work.FTS.PhiStar.Series.acoeff α m F with hA
  set CM : ℝ → ℝ := Work.FTS.PhiStar.Series.cmode m F with hCM
  set RΘ : ℝ → ℝ := fun z => -(α ^ 2) * z ^ 2 * deriv (deriv (Theta m φ)) z
    - (α * (5 + α) * z) * deriv (Theta m φ) z with hRΘ
  -- continuity and integrability of the pieces
  have hΘ2c : ContDiff ℝ 2 (Theta m φ) := (thetaMomentSmooth hφ hφc hφs m).1
  have hΘ'cont : Continuous (fun z => deriv (Theta m φ) z) := by
    have h := hΘ2c.continuous_iteratedDeriv 1 (by norm_num)
    simpa only [iteratedDeriv_one, iteratedDeriv_zero, Function.iterate_zero] using h
  have hΘ''cont : Continuous (fun z => deriv (deriv (Theta m φ)) z) := by
    have h := hΘ2c.continuous_iteratedDeriv 2 (by norm_num)
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero, Function.iterate_zero]
      using h
  have hAcont : ContinuousOn A (Set.Icc a b) := by
    rw [hA]
    simp only [Work.FTS.PhiStar.Series.acoeff]
    exact (radGreenContinuousOn hα hα1 m hc2 hcm).mono
      (fun z hz => lt_of_lt_of_le ha hz.1)
  have hzq : ContinuousOn (fun z : ℝ => z ^ q) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt (lt_of_lt_of_le ha hz.1)))
  have hRcont : ContinuousOn RΘ (Set.Icc a b) := by
    rw [hRΘ]
    exact ((continuous_const.mul (continuous_id.pow 2)).continuousOn.mul hΘ''cont.continuousOn).sub
      ((continuous_const.mul continuous_id).continuousOn.mul hΘ'cont.continuousOn)
  have hI1 : IntegrableOn (fun z => A z * RΘ z * z ^ q) (Set.Icc a b) :=
    (((hAcont.mul hRcont).mul hzq)).integrableOn_compact isCompact_Icc
  have hI2 : IntegrableOn (fun z => A z * Theta m φ z * z ^ q) (Set.Icc a b) :=
    (((hAcont.mul hΘ2c.continuous.continuousOn).mul hzq)).integrableOn_compact isCompact_Icc
  -- ## the inner `θ`-integrals
  have hinner : ∀ z ∈ Set.Icc a b,
      (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * Work.Elliptic.bslOp α φ z θ * Real.cos θ)
        = RΘ z + Work.FTS.PhiStar.Gegenbauer.lam m * Theta m φ z := by
    intro z hz
    rw [hRΘ]
    exact inner_theta_eq α m hφ hφc hφs ha hab hc0 hcd hd hbox hz
  have hkey : ∀ z ∈ Set.Icc a b,
      (∫ θ in Set.Icc c d, (A z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.Elliptic.bslOp α φ z θ) * (z ^ q * Real.cos θ))
        = A z * (z ^ q * (RΘ z + Work.FTS.PhiStar.Gegenbauer.lam m * Theta m φ z)) := by
    intro z hz
    rw [show (∫ θ in Set.Icc c d, (A z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.Elliptic.bslOp α φ z θ) * (z ^ q * Real.cos θ))
        = ∫ θ in Set.Icc c d, A z * (z ^ q * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.Elliptic.bslOp α φ z θ * Real.cos θ)) from
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      hinner z hz]
  have hkeyR : ∀ z : ℝ,
      (∫ θ in Set.Icc c d, (CM z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * φ z θ * (z ^ q * Real.cos θ))
        = CM z * (z ^ q * Theta m φ z) := by
    intro z
    rw [show (∫ θ in Set.Icc c d, (CM z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * φ z θ * (z ^ q * Real.cos θ))
        = ∫ θ in Set.Icc c d, CM z * (z ^ q * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * φ z θ * Real.cos θ)) from
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    congr 1
    congr 1
    have h1 : (∫ θ in Set.Icc c d, Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * φ z θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * φ z θ * Real.cos θ :=
      setIntegral_Icc_cd_eq_Iθ hc0.le hd.le (fun θ hθ => by
        rw [test_vanishes_off_theta hbox (fun hm => hθ (Set.Ioo_subset_Icc_self hm))]
        ring)
    rw [h1, Theta]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [setIntegral_congr_fun measurableSet_Icc hkey,
    setIntegral_congr_fun measurableSet_Icc (fun z _ => hkeyR z)]
  -- ## the `z`-integral
  have hLsplit : (∫ z in Set.Icc a b, A z * (z ^ q
        * (RΘ z + Work.FTS.PhiStar.Gegenbauer.lam m * Theta m φ z)))
      = (∫ z in Set.Icc a b, A z * RΘ z * z ^ q)
        + Work.FTS.PhiStar.Gegenbauer.lam m
            * (∫ z in Set.Icc a b, A z * Theta m φ z * z ^ q) := by
    rw [show (∫ z in Set.Icc a b, A z * (z ^ q
          * (RΘ z + Work.FTS.PhiStar.Gegenbauer.lam m * Theta m φ z)))
        = ∫ z in Set.Icc a b, (A z * RΘ z * z ^ q
            + Work.FTS.PhiStar.Gegenbauer.lam m * (A z * Theta m φ z * z ^ q)) from
      setIntegral_congr_fun measurableSet_Icc (fun z _ => by ring)]
    rw [MeasureTheory.integral_add hI1 (hI2.const_mul _),
      MeasureTheory.integral_const_mul]
  rw [hLsplit]
  -- ## conversion of the two `z`-integrals to `(0,∞)`
  have hconv1 : (∫ z in Set.Icc a b, A z * RΘ z * z ^ q)
      = ∫ z in Set.Ioi 0, A z * RΘ z * z ^ q :=
    setIntegral_Icc_ab_eq_Ioi ha (fun z hz => by
      rw [hRΘ]
      simp only [deriv2_Theta_eq_zero_of_not_mem hbox hz,
        deriv_Theta_eq_zero_of_not_mem hbox hz]
      ring)
  have hconv2 : (∫ z in Set.Icc a b, A z * Theta m φ z * z ^ q)
      = ∫ z in Set.Ioi 0, A z * Theta m φ z * z ^ q :=
    setIntegral_Icc_ab_eq_Ioi ha (fun z hz => by
      rw [Theta_eq_zero_of_not_mem hbox hz]
      ring)
  rw [hconv1, hconv2]
  -- ## the radial weak ODE
  have hΘc : HasCompactSupport (Theta m φ) := (thetaMomentCompactSupport hφ hφc hφs m).1
  have hΘs : tsupport (Theta m φ) ⊆ Set.Ioi 0 := (thetaMomentCompactSupport hφ hφc hφs m).2
  have hode := radGreenWeakOdeMeas (α := α) hα hα1 m hc2 hcm hΘ2c hΘc hΘs
  have hstep : (∫ z in Set.Ioi 0, A z * RΘ z * z ^ q)
        + Work.FTS.PhiStar.Gegenbauer.lam m * (∫ z in Set.Ioi 0, A z * Theta m φ z * z ^ q)
      = ∫ z in Set.Ioi 0, CM z * Theta m φ z * z ^ q := hode
  rw [hstep]
  -- ## back to the box
  have hRconv : (∫ z in Set.Icc a b, CM z * (z ^ q * Theta m φ z))
      = ∫ z in Set.Ioi 0, CM z * Theta m φ z * z ^ q := by
    rw [show (∫ z in Set.Icc a b, CM z * (z ^ q * Theta m φ z))
        = ∫ z in Set.Icc a b, CM z * Theta m φ z * z ^ q from
      setIntegral_congr_fun measurableSet_Icc (fun z _ => by ring)]
    exact setIntegral_Icc_ab_eq_Ioi ha (fun z hz => by
      rw [Theta_eq_zero_of_not_mem hbox hz]
      ring)
  rw [← hRconv]



end Work.FTS.H2.ModalSolR
