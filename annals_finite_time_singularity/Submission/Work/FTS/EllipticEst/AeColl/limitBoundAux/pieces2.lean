import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeColl.Defs
import Submission.Work.FTS.EllipticEst.AeColl.limitBoundAux.pieces
import Submission.Work.FTS.EllipticEst.AngSecond.cut_deriv_uniform
import Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
import Submission.Work.FTS.EllipticEst.H2W.SlotA.cwPairBound
import Submission.Work.FTS.EllipticEst.AngAWeak.AeEnergyMain
-- (`AngClean/I1_ibp.lean` declares the same names as `AngSecond/I1_ibp.lean` under the same
-- namespace; this file used to get them transitively through `AngSecond.I1_ibp` via
-- `H2W/SlotA/cwPairBound.lean`, whose import of that module was dropped (its declarations clash
-- with the `AngClean/I1_cut_alt` copy for consumers that need both).  Import the `AngClean` side
-- explicitly here.)
import Submission.Work.FTS.EllipticEst.AngClean.I1_ibp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeColl.limitBoundAux.pieces2` — shared ingredients for `AeColl.limitBound` (part 2)

The identifications of `Pcut u n`, `Vfull u`, `Dcut u n`, `Trcut u n` with `z`-integrals of
`z`-only slice functions, together with the integrability / measurability / monotonicity facts
about those marginals, and the nonnegativity of `Acut`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeColl

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 5. The `z`-marginal of `V = z∂_z∂_θu`, and `Pcut`/`Vfull` -/

/-- The angular slice energy of `V = z∂_z∂_θu`, as a function of `z` alone. -/
def Gcut (u : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, (Vz u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ

theorem Gcut_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Gcut u z :=
  setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ))

theorem Gcut_integrable {u : ℝ → ℝ → ℝ}
    (h4 : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (Gcut u) Work.Spaces.Iz := h4

/-- The inner `θ`-integral of `Vfull` (over `(0,π/2)`) equals the `Iθ`-version. -/
theorem integral_Ioo_Vz_sq (u : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Vz u z θ) ^ 2) = Gcut u z := by
  rw [Gcut]
  rw [MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [sigθ_eq]
  ring

theorem Vfull_eq_integral (u : ℝ → ℝ → ℝ) :
    Vfull u = ∫ z in Set.Ioi 0, wt z * Gcut u z := by
  rw [Vfull]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  rw [integral_Ioo_Vz_sq]

theorem Pcut_eq_integral (u : ℝ → ℝ → ℝ) (n : ℕ) :
    Pcut u n = ∫ z in Set.Ioi 0,
      Work.FTS.EllipticEst.cut n z * (wt z * Gcut u z) := by
  rw [Pcut]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  rw [integral_Ioo_Vz_sq]
  ring

/-- On the support of `cut n` the squared weight `wt` is bounded by an explicit constant. -/
def wtB (n : ℕ) : ℝ := ((1 + 3 * ((n : ℝ) + 1)) ^ 2 * ((n : ℝ) + 1) ^ 2) ^ 2

theorem wt_le_wtB {n : ℕ} {z : ℝ} (hc : Work.FTS.EllipticEst.cut n z ≠ 0) :
    wt z ≤ wtB n := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlo : 1 / ((n : ℝ) + 1) < z := by
    by_contra h
    push_neg at h
    exact hc (Work.FTS.EllipticEst.cut_apply_zero_of_le n h)
  have hhi : z < 3 * ((n : ℝ) + 1) := by
    by_contra h
    push_neg at h
    exact hc (Work.FTS.EllipticEst.cut_apply_zero_of_ge n h)
  have hzpos : 0 < z := lt_trans (div_pos one_pos hn) hlo
  have hzp : (1 : ℝ) < ((n : ℝ) + 1) ^ 2 * z ^ 2 := by
    have h1 : 1 < ((n : ℝ) + 1) * z := by
      rw [div_lt_iff₀ hn] at hlo
      linarith
    nlinarith [h1, hn, hzpos]
  have h1 : (1 + z) ^ 2 ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hw : Work.Spaces.w z ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 * ((n : ℝ) + 1) ^ 2 := by
    rw [Work.Spaces.w, div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
    have hB0 : (0 : ℝ) ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 := sq_nonneg _
    calc (1 + z) ^ 2 ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 := h1
      _ = (1 + 3 * ((n : ℝ) + 1)) ^ 2 * 1 := by ring
      _ ≤ (1 + 3 * ((n : ℝ) + 1)) ^ 2 * (((n : ℝ) + 1) ^ 2 * z ^ 2) :=
          mul_le_mul_of_nonneg_left (le_of_lt hzp) hB0
      _ = (1 + 3 * ((n : ℝ) + 1)) ^ 2 * ((n : ℝ) + 1) ^ 2 * z ^ 2 := by ring
  rw [wt, wtB]
  exact pow_le_pow_left₀ (Work.FTS.EllipticEst.AngSecond.w_nonneg z) hw 2

theorem cut_mul_wt_bdd (n : ℕ) (z : ℝ) :
    |Work.FTS.EllipticEst.cut n z * wt z| ≤ wtB n := by
  have hB0 : 0 ≤ wtB n := by rw [wtB]; positivity
  have hwt0 : 0 ≤ wt z := by rw [wt]; positivity
  rcases eq_or_ne (Work.FTS.EllipticEst.cut n z) 0 with h | h
  · rw [h, zero_mul, abs_zero]; exact hB0
  · have h1 := wt_le_wtB h
    have h2 : 0 ≤ Work.FTS.EllipticEst.cut n z := Work.FTS.EllipticEst.cut_nonneg n z
    have h3 : Work.FTS.EllipticEst.cut n z ≤ 1 := Work.FTS.EllipticEst.cut_le_one n z
    rw [abs_of_nonneg (mul_nonneg h2 hwt0)]
    calc Work.FTS.EllipticEst.cut n z * wt z ≤ 1 * wt z := mul_le_mul_of_nonneg_right h3 hwt0
      _ ≤ 1 * wtB n := mul_le_mul_of_nonneg_left h1 zero_le_one
      _ = wtB n := one_mul _

theorem integrable_cut_wt_Gcut {u : ℝ → ℝ → ℝ}
    (hG : MeasureTheory.IntegrableOn (Gcut u) Work.Spaces.Iz) (n : ℕ) :
    MeasureTheory.Integrable (fun z => Work.FTS.EllipticEst.cut n z * (wt z * Gcut u z))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hG' : MeasureTheory.Integrable (Gcut u) (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hG.mono_set Set.Ioi_subset_Ici_self
  have hdom : MeasureTheory.Integrable (fun z => wtB n * Gcut u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hG'.const_mul (wtB n)
  have hG'' : MeasureTheory.AEStronglyMeasurable (Gcut u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hG'.aestronglyMeasurable
  have hwt : MeasureTheory.AEStronglyMeasurable wt
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    continuousOn_wt.aestronglyMeasurable measurableSet_Ioi
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => Work.FTS.EllipticEst.cut n z * (wt z * Gcut u z))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    ((Work.FTS.EllipticEst.cut_contDiff n).continuous.aestronglyMeasurable).mul (hwt.mul hG'')
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  filter_upwards with z
  rw [Real.norm_eq_abs]
  have hG0 : 0 ≤ Gcut u z := Gcut_nonneg u z
  have hwt0 : 0 ≤ wt z := by rw [wt]; positivity
  have hrewrite : |Work.FTS.EllipticEst.cut n z * (wt z * Gcut u z)|
      = |Work.FTS.EllipticEst.cut n z * wt z| * Gcut u z := by
    simp only [abs_mul, abs_of_nonneg hG0, abs_of_nonneg hwt0]
    ring
  rw [hrewrite]
  exact mul_le_mul_of_nonneg_right (cut_mul_wt_bdd n z) hG0

theorem aesm_wt_Gcut {u : ℝ → ℝ → ℝ}
    (hG : MeasureTheory.IntegrableOn (Gcut u) Work.Spaces.Iz) :
    MeasureTheory.AEStronglyMeasurable (fun z => wt z * Gcut u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hG' : MeasureTheory.Integrable (Gcut u) (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hG.mono_set Set.Ioi_subset_Ici_self
  have hwt : MeasureTheory.AEStronglyMeasurable wt
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    continuousOn_wt.aestronglyMeasurable measurableSet_Ioi
  exact hwt.mul hG'.aestronglyMeasurable

/-- `Pcut u ·` is monotone in `n`. -/
theorem Pcut_mono {u : ℝ → ℝ → ℝ} (hG : MeasureTheory.IntegrableOn (Gcut u) Work.Spaces.Iz) :
    Monotone (fun n : ℕ => Pcut u n) := by
  have hpt : ∀ n z, Work.FTS.EllipticEst.cut n z * (wt z * Gcut u z)
      ≤ Work.FTS.EllipticEst.cut (n + 1) z * (wt z * Gcut u z) := by
    intro n z
    exact mul_le_mul_of_nonneg_right (Work.FTS.EllipticEst.AngAWeak.AeMain.cut_mono n z)
      (mul_nonneg (by rw [wt]; positivity) (Gcut_nonneg u z))
  intro m n hmn
  change Pcut u m ≤ Pcut u n
  rw [Pcut_eq_integral u m, Pcut_eq_integral u n]
  refine MeasureTheory.setIntegral_mono (integrable_cut_wt_Gcut hG m)
    (integrable_cut_wt_Gcut hG n) ?_
  exact Nat.le_induction le_rfl (fun k _ hk z => le_trans (hk z) (hpt k z)) n hmn

/-- `ofReal (∫ f) ≤ ∫⁻ ofReal f` for a nonnegative a.e.-strongly-measurable `f`. -/
theorem ofReal_integral_le_lintegral' (μ : MeasureTheory.Measure ℝ) (f : ℝ → ℝ)
    (hf : MeasureTheory.AEStronglyMeasurable f μ) (h0 : ∀ x, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  rcases eq_or_ne (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ⊤ with h | h
  · rw [h]; exact le_top
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hf
        (Filter.Eventually.of_forall h0)).mp h) (Filter.Eventually.of_forall h0)]

/-! ## 6. The `z`-marginals of the mixed bilinear slots `Dcut`, `Trcut` -/

/-- The `z`-marginal of the pairing of `Az = z²∂_z²u` with `∂_θθu`. -/
def ZI (u : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, Az u z θ * Work.Spaces.pthIter 2 u z θ
    * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ

/-- The `z`-marginal of the pairing of `Uz = z∂_zu` with `∂_θθu`. -/
def YI (u : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, Uz u z θ * Work.Spaces.pthIter 2 u z θ
    * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ

theorem ZI_slice {u : ℝ → ℝ → ℝ}
    (hm : Work.FTS.EllipticEst.AngSecond.IPMem (Az u) (Work.Spaces.pthIter 2 u))
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun θ => Az u z θ * Work.Spaces.pthIter 2 u z θ
      * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ := hm.1 z hz

theorem YI_slice {u : ℝ → ℝ → ℝ}
    (hm : Work.FTS.EllipticEst.AngSecond.IPMem (Uz u) (Work.Spaces.pthIter 2 u))
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun θ => Uz u z θ * Work.Spaces.pthIter 2 u z θ
      * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
      Work.Spaces.Iθ := hm.1 z hz

theorem ZI_integrable {u : ℝ → ℝ → ℝ}
    (hm : Work.FTS.EllipticEst.AngSecond.IPMem (Az u) (Work.Spaces.pthIter 2 u)) :
    MeasureTheory.IntegrableOn (ZI u) Work.Spaces.Iz := hm.2

theorem YI_integrable {u : ℝ → ℝ → ℝ}
    (hm : Work.FTS.EllipticEst.AngSecond.IPMem (Uz u) (Work.Spaces.pthIter 2 u)) :
    MeasureTheory.IntegrableOn (YI u) Work.Spaces.Iz := hm.2

/-- The `z`-integral of the marginal `ZI` is the pairing `IP (Az u) (∂_θθu)`. -/
theorem integral_ZI_eq_IP (u : ℝ → ℝ → ℝ) :
    (∫ z in Set.Ioi 0, ZI u z) = Work.FTS.EllipticEst.AngSecond.IP (Az u)
      (Work.Spaces.pthIter 2 u) := by
  rw [Work.FTS.EllipticEst.AngSecond.IP]
  exact MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))

theorem integral_YI_eq_IP (u : ℝ → ℝ → ℝ) :
    (∫ z in Set.Ioi 0, YI u z) = Work.FTS.EllipticEst.AngSecond.IP (Uz u)
      (Work.Spaces.pthIter 2 u) := by
  rw [Work.FTS.EllipticEst.AngSecond.IP]
  exact MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))

/-- `Dcut u n` is the `z`-integral of `χ_n · ZI`. -/
theorem Dcut_eq_integral (u : ℝ → ℝ → ℝ) (n : ℕ) :
    Dcut u n = ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * ZI u z := by
  have h1 : ∀ z : ℝ, (∫ θ in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.cut n z * wt z * sigθ θ * (Az u z θ)
          * (Work.Spaces.pthIter 2 u z θ))
      = Work.FTS.EllipticEst.cut n z * ZI u z := by
    intro z
    have h2 : (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.cut n z * wt z
          * sigθ θ * (Az u z θ) * (Work.Spaces.pthIter 2 u z θ))
        = Work.FTS.EllipticEst.cut n z
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), wt z * (sigθ θ * (Az u z θ)
              * (Work.Spaces.pthIter 2 u z θ))) := by
      rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.cut n z * wt z
            * sigθ θ * (Az u z θ) * (Work.Spaces.pthIter 2 u z θ))
          = ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.cut n z
              * (wt z * (sigθ θ * (Az u z θ) * (Work.Spaces.pthIter 2 u z θ))) from
        setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)]
      rw [MeasureTheory.integral_const_mul]
    have h3 : (∫ θ in Set.Ioo 0 (Real.pi / 2), wt z * (sigθ θ * (Az u z θ)
          * (Work.Spaces.pthIter 2 u z θ))) = ZI u z := by
      rw [MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2))]
      rw [ZI]
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      rw [sigθ_eq, wt_eq]
      ring
    rw [h2, h3]
  rw [Dcut]
  exact setIntegral_congr_fun measurableSet_Ioi (fun z _ => h1 z)

/-- `Dcut u ·` converges to `IP (Az u) (∂_θθu)`. -/
theorem Dcut_tendsto_of_integrable {u : ℝ → ℝ → ℝ}
    (hZ : MeasureTheory.IntegrableOn (ZI u) Work.Spaces.Iz) :
    Filter.Tendsto (fun n : ℕ => ∫ z in Set.Ioi 0, Work.FTS.EllipticEst.cut n z * ZI u z)
      Filter.atTop (nhds (∫ z in Set.Ioi 0, ZI u z)) := by
  have hsub : (∫ z in Work.Spaces.Iz, ZI u z) = ∫ z in Set.Ioi 0, ZI u z :=
    MeasureTheory.setIntegral_congr_set
      ((MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ))).symm)
  have h := Work.FTS.EllipticEst.AngSecond.tendsto_setIntegral_cut_mul hZ
  rw [hsub] at h
  refine h.congr' ?_
  filter_upwards with n
  exact MeasureTheory.setIntegral_congr_set
    ((MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0:ℝ))).symm)

theorem Dcut_tendsto {u : ℝ → ℝ → ℝ}
    (hm : Work.FTS.EllipticEst.AngSecond.IPMem (Az u) (Work.Spaces.pthIter 2 u)) :
    Filter.Tendsto (fun n : ℕ => Dcut u n) Filter.atTop
      (nhds (Work.FTS.EllipticEst.AngSecond.IP (Az u) (Work.Spaces.pthIter 2 u))) := by
  have h := Dcut_tendsto_of_integrable (ZI_integrable hm)
  rw [integral_ZI_eq_IP u] at h
  refine h.congr' ?_
  filter_upwards with n
  exact (Dcut_eq_integral u n).symm

/-- The transfer coefficient `c_n(z) = z·(χ_n)'(z) + χ_n(z)·cw(z)`. -/
def cfun (n : ℕ) (z : ℝ) : ℝ :=
  deriv (Work.FTS.EllipticEst.cut n) z * z + Work.FTS.EllipticEst.cut n z * cwf z

/-- Derivative of the squared weight. -/
theorem deriv_wt {z : ℝ} (hz : 0 < z) :
    deriv wt z = -4 * wt z / ((1 + z) * z) :=
  Work.FTS.EllipticEst.AngSecond.deriv_w2_eq' hz

/-- The rescaled derivative of the truncation weight:
`(χ w² z²)'(z)/z = (zχ'(z) + χ(z)·cw(z))·w²(z)`. -/
theorem deriv_cut_wt_zsq {n : ℕ} {z : ℝ} (hz : 0 < z) :
    deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z
      = cfun n z * wt z := by
  have hcut : HasDerivAt (Work.FTS.EllipticEst.cut n)
      (deriv (Work.FTS.EllipticEst.cut n) z) z :=
    (((Work.FTS.EllipticEst.cut_contDiff n).differentiable (by simp)).differentiableAt).hasDerivAt
  have hwt : HasDerivAt wt (deriv wt z) z := by
    have h1 : wt = fun z' : ℝ => ((1 + z') ^ 2 / z' ^ 2) ^ 2 := by
      funext z'; simp only [wt, Work.Spaces.w]
    have h2 : DifferentiableAt ℝ (fun z' : ℝ => ((1 + z') ^ 2 / z' ^ 2) ^ 2) z := by
      have h3 : DifferentiableAt ℝ (fun z' : ℝ => ((1 + z') ^ 2 / z' ^ 2) ^ 2) z := by
        have h4 := (((differentiableAt_const (1:ℝ)).add differentiableAt_id).pow 2).div
          (differentiableAt_id.pow 2) (pow_ne_zero 2 (ne_of_gt hz))
        convert h4.pow 2 using 1
        funext y
        simp only [Pi.add_apply, Pi.pow_apply, Pi.div_apply, id_eq]
      exact h3
    rw [h1]
    exact h2.hasDerivAt
  have hz2 : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hderiv : deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z
      = (deriv (Work.FTS.EllipticEst.cut n) z * wt z + Work.FTS.EllipticEst.cut n z * deriv wt z)
          * z ^ 2 + (Work.FTS.EllipticEst.cut n z * wt z) * (2 * z) :=
    ((hcut.mul hwt).mul hz2).deriv
  rw [hderiv, deriv_wt hz]
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by positivity
  unfold cfun cwf
  field_simp
  ring

/-- Uniform bound for the transfer coefficient. -/
theorem abs_cfun_le {n : ℕ} {K : ℝ}
    (hK : ∀ z : ℝ, |z * deriv (Work.FTS.EllipticEst.cut n) z| ≤ K) {z : ℝ}
    (hz : 0 ≤ z) : |cfun n z| ≤ K + 2 := by
  have h1 : |deriv (Work.FTS.EllipticEst.cut n) z| * |z| ≤ K := by
    simpa only [abs_mul, mul_comm] using hK z
  have h2 : |Work.FTS.EllipticEst.cut n z| ≤ 1 := by
    rw [abs_of_nonneg (Work.FTS.EllipticEst.cut_nonneg n z)]
    exact Work.FTS.EllipticEst.cut_le_one n z
  have h3 : |cwf z| ≤ 2 := Work.FTS.EllipticEst.AngSecond.abs_cw_le_two hz
  calc |cfun n z| = |deriv (Work.FTS.EllipticEst.cut n) z * z
        + Work.FTS.EllipticEst.cut n z * cwf z| := by rfl
    _ ≤ |deriv (Work.FTS.EllipticEst.cut n) z * z| + |Work.FTS.EllipticEst.cut n z * cwf z| :=
        abs_add_le _ _
    _ = |deriv (Work.FTS.EllipticEst.cut n) z| * |z| + |Work.FTS.EllipticEst.cut n z| * |cwf z| := by
        simp only [abs_mul]
    _ ≤ K + 1 * 2 := add_le_add h1 (mul_le_mul h2 h3 (abs_nonneg _) zero_le_one)
    _ = K + 2 := by ring

/-- `Trcut u n` is the `z`-integral of `c_n · YI`. -/
theorem Trcut_eq_integral (u : ℝ → ℝ → ℝ) (n : ℕ) :
    Trcut u n = ∫ z in Set.Ioi 0, cfun n z * YI u z := by
  have h1 : ∀ z : ℝ, (∫ θ in Set.Ioo 0 (Real.pi / 2),
        deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z
          * sigθ θ * (Uz u z θ) * (Work.Spaces.pthIter 2 u z θ))
      = deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 u z θ * Uz u z θ)
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    intro z
    have h2 : (∫ θ in Set.Ioo 0 (Real.pi / 2),
          deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z
            * sigθ θ * (Uz u z θ) * (Work.Spaces.pthIter 2 u z θ))
        = deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Uz u z θ)
              * (Work.Spaces.pthIter 2 u z θ)) := by
      rw [show (∫ θ in Set.Ioo 0 (Real.pi / 2),
            deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z
              * sigθ θ * (Uz u z θ) * (Work.Spaces.pthIter 2 u z θ))
          = ∫ θ in Set.Ioo 0 (Real.pi / 2),
              (deriv (fun z' => Work.FTS.EllipticEst.cut n z' * wt z' * z' ^ 2) z / z)
                * (sigθ θ * (Uz u z θ) * (Work.Spaces.pthIter 2 u z θ)) from
        setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by ring)]
      rw [MeasureTheory.integral_const_mul]
    have h3 : (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Uz u z θ)
          * (Work.Spaces.pthIter 2 u z θ))
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 u z θ * Uz u z θ)
            * Work.FTS.EllipticEst.AngSecond.sig θ := by
      rw [MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2))]
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      rw [sigθ_eq]
      ring
    rw [h2, h3]
  rw [Trcut]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
  rw [h1 z, deriv_cut_wt_zsq hz, mul_assoc]
  rw [← MeasureTheory.integral_const_mul]
  rw [YI]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [wt_eq]
  ring

/-! ## 7. Nonnegativity of the truncated angular energy -/

theorem Acut_nonneg (u : ℝ → ℝ → ℝ) (n : ℕ) : 0 ≤ Acut u n := by
  rw [Acut]
  refine setIntegral_nonneg measurableSet_Ioi (fun z _ => ?_)
  refine mul_nonneg (mul_nonneg (Work.FTS.EllipticEst.cut_nonneg n z)
    (by rw [wt]; positivity)) ?_
  exact setIntegral_nonneg measurableSet_Ioo (fun θ hθ =>
    mul_nonneg (by
      rw [sigθ]
      exact Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))) _) (sq_nonneg _))

end Work.FTS.EllipticEst.AeColl
