/-
Copyright: work module for the Elgindi finite-time singularity project.

# Vocabulary for the logarithmic-cut truncation of the mixed weighted interpolation

This module sets up the objects used by `Work.Blocks.interp_truncation`, the "reduction to
the compactly supported case" of the mixed weighted interpolation estimate

  `α² mixInt G ≤ C (α⁴ ddInt G + ttInt G + α² dInt G)`.

The truncation is `G ↦ cut φ k G = ζ_k · G`, where `ζ_k = zc φ k` is the *logarithmic*
cut-off of `Submission/Work/FTS/EllipticEst/Alpha4/Cut.lean`.  Everything here is elementary:
the support and bound facts for `ζ_k`, `D_zζ_k`, `D_z²ζ_k`, the Leibniz rules for the product
`ζ(z)·G(z,θ)`, the nonnegativity of the weighted slice integrals, and the identification of
the four functionals with the integrals of the `z`-slice functions `sl`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.interpol_defs
import Submission.Work.FTS.EllipticEst.Alpha4.Cut
import Submission.Work.FTS.EllipticEst.Alpha4.Assembly
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false

/-! ## The basic objects -/

/-- The half-strip `(0,∞) × (-1, π/2+1)` on which the data are `C^∞`. -/
abbrev strip : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)

theorem mem_strip {z θ : ℝ} :
    (z, θ) ∈ strip ↔ 0 < z ∧ θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := Iff.rfl

/-- The logarithmic cut-off `ζ_k = zc φ k` of the workspace, as a function of `z` alone. -/
abbrev zeta (φ : ℝ → ℝ) (k : ℕ) : ℝ → ℝ := Work.FTS.EllipticEst.Alpha4.zc φ k

/-- The truncated function `ζ_k · G`. -/
def cut (φ : ℝ → ℝ) (k : ℕ) (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => zeta φ k z * G z θ

/-- `D_z ζ_k = z · ζ_k'`, a function of `z` alone. -/
def zE (φ : ℝ → ℝ) (k : ℕ) : ℝ → ℝ := fun z => z * deriv (zeta φ k) z

/-- `D_z² ζ_k`, a function of `z` alone. -/
def zF (φ : ℝ → ℝ) (k : ℕ) : ℝ → ℝ := fun z => z * deriv (zE φ k) z

/-- The weighted angular slice integral `∫_θ (F z θ)² σ θ`, `σ = sin(2θ)^{-η}`. -/
def inn (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (F z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ

/-- The `z`-integrand `w(z)² ∫_θ (F z θ)² σ θ` of the four functionals. -/
def sl (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2 * inn F z

/-! ## The four functionals as integrals of the slice functions -/

theorem mixInt_eq_int_sl (G : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.mixInt G
      = ∫ z in Work.Spaces.Iz, sl (Work.Spaces.Dz (Work.Spaces.pth G)) z := by
  rw [Work.FTS.EllipticEst.Alpha4.mixInt_eq]
  rfl

theorem ddInt_eq_int_sl (G : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.ddInt G
      = ∫ z in Work.Spaces.Iz, sl (Work.Spaces.Dz (Work.Spaces.Dz G)) z := by
  rw [Work.FTS.EllipticEst.Alpha4.ddInt_eq]
  rfl

theorem ttInt_eq_int_sl (G : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.ttInt G
      = ∫ z in Work.Spaces.Iz, sl (Work.Spaces.pth (Work.Spaces.pth G)) z := by
  rw [Work.FTS.EllipticEst.Alpha4.ttInt_eq]
  rfl

theorem dInt_eq_int_sl (G : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.dInt G = ∫ z in Work.Spaces.Iz, sl (Work.Spaces.Dz G) z := by
  rw [Work.FTS.EllipticEst.Alpha4.dInt_eq]
  rfl

/-- The `z`-integrand form of the slice function: `sl F z = ∫_θ (F z θ)² w(z)² σ θ`. -/
theorem sl_eq_integrand (F : ℝ → ℝ → ℝ) (z : ℝ) :
    sl F z = ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  rw [sl, inn]
  rw [show (fun θ : ℝ => (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = fun θ => ((F z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) * (Work.Spaces.w z) ^ 2
      from by funext θ; ring]
  rw [MeasureTheory.integral_mul_const]
  ring

/-- The four clauses of `FourInt` in the `sl`-vocabulary. -/
theorem fourInt_iff (G : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.FourInt G ↔
      MeasureTheory.IntegrableOn (sl (Work.Spaces.Dz (Work.Spaces.pth G))) Work.Spaces.Iz ∧
      MeasureTheory.IntegrableOn (sl (Work.Spaces.Dz (Work.Spaces.Dz G))) Work.Spaces.Iz ∧
      MeasureTheory.IntegrableOn (sl (Work.Spaces.pth (Work.Spaces.pth G))) Work.Spaces.Iz ∧
      MeasureTheory.IntegrableOn (sl (Work.Spaces.Dz G)) Work.Spaces.Iz := by
  simp only [Work.FTS.EllipticEst.FourInt]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  all_goals
    refine ⟨fun h => ?_, fun h => ?_⟩
    · refine h.congr (Filter.Eventually.of_forall fun z => ?_)
      exact (sl_eq_integrand _ z).symm
    · refine h.congr (Filter.Eventually.of_forall fun z => ?_)
      exact (sl_eq_integrand _ z)

/-! ## Nonnegativity of the slice integrals -/

theorem inn_nonneg (F : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ inn F z := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
    with θ hθ
  exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)

theorem sl_nonneg (F : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ sl F z :=
  mul_nonneg (sq_nonneg _) (inn_nonneg F z)

theorem mixInt_nonneg (G : ℝ → ℝ → ℝ) : 0 ≤ Work.FTS.EllipticEst.mixInt G := by
  rw [mixInt_eq_int_sl]
  exact MeasureTheory.integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun z => sl_nonneg _ z)

theorem ddInt_nonneg (G : ℝ → ℝ → ℝ) : 0 ≤ Work.FTS.EllipticEst.ddInt G := by
  rw [ddInt_eq_int_sl]
  exact MeasureTheory.integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun z => sl_nonneg _ z)

theorem ttInt_nonneg (G : ℝ → ℝ → ℝ) : 0 ≤ Work.FTS.EllipticEst.ttInt G := by
  rw [ttInt_eq_int_sl]
  exact MeasureTheory.integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun z => sl_nonneg _ z)

theorem dInt_nonneg (G : ℝ → ℝ → ℝ) : 0 ≤ Work.FTS.EllipticEst.dInt G := by
  rw [dInt_eq_int_sl]
  exact MeasureTheory.integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun z => sl_nonneg _ z)

/-! ## Support and value facts for `ζ_k` -/

theorem zeta_nonneg {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) (k : ℕ) (z : ℝ) :
    0 ≤ zeta φ k z :=
  Work.FTS.EllipticEst.Alpha4.zc_nonneg
    (fun t => (hφ.2.2.2.1 (Real.log t / Real.log (k : ℝ))).1) z

theorem zeta_le_one {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) (k : ℕ) (z : ℝ) :
    zeta φ k z ≤ 1 :=
  Work.FTS.EllipticEst.Alpha4.zc_le_one
    (fun t => (hφ.2.2.2.1 (Real.log t / Real.log (k : ℝ))).2) z

theorem zeta_eq_zero_of_notMem {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K)
    {k : ℕ} (hk : 2 ≤ k) {z : ℝ}
    (hz : z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2)) : zeta φ k z = 0 :=
  Work.FTS.EllipticEst.Alpha4.zc_eq_zero_of_notMem (le_trans (by norm_num) hk)
    (fun z' hz' hz'' =>
      (Work.FTS.EllipticEst.ZCuts.zCut_props hφ k hk).2.1 z' hz' hz'') hz

theorem zeta_eq_one_of_mem {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K)
    {k : ℕ} (hk : 2 ≤ k) {z : ℝ} (h1 : 1 / (k : ℝ) ≤ z) (h2 : z ≤ (k : ℝ)) :
    zeta φ k z = 1 :=
  Work.FTS.EllipticEst.Alpha4.zc_eq_one_of_mem (le_trans (by norm_num) hk)
    (fun z' hz' hz'' hz''' =>
      (Work.FTS.EllipticEst.ZCuts.zCut_props hφ k hk).2.2.1 z' hz' hz'' hz''') h1 h2

theorem zeta_eq_zero_of_nonpos {φ : ℝ → ℝ} {k : ℕ} {z : ℝ} (hz : z ≤ 0) :
    zeta φ k z = 0 :=
  Work.FTS.EllipticEst.Alpha4.zc_of_nonpos hz

/-- `ζ_k` is `C^∞` on `(0,∞)`. -/
theorem zeta_contDiffOn {φ : ℝ → ℝ} {k : ℕ}
    (hcd : ContDiffOn ℝ Work.FTS.EllipticEst.smoothOrder
      (Work.FTS.EllipticEst.psiFun φ k) (Set.Ioi 0)) :
    ContDiffOn ℝ Work.FTS.EllipticEst.smoothOrder (zeta φ k) (Set.Ioi 0) :=
  hcd.congr (fun z hz => Work.FTS.EllipticEst.Alpha4.zc_of_pos hz)

theorem zeta_contDiffOn_of_isZCut {φ : ℝ → ℝ} {K : ℝ}
    (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ} (hk : 2 ≤ k) :
    ContDiffOn ℝ Work.FTS.EllipticEst.smoothOrder (zeta φ k) (Set.Ioi 0) :=
  zeta_contDiffOn (Work.FTS.EllipticEst.ZCuts.psiFun_contDiffOn hφ.1 hk)

theorem smoothOrder_ne_zero : Work.FTS.EllipticEst.smoothOrder ≠ 0 := by
  simp [Work.FTS.EllipticEst.smoothOrder]

theorem one_le_smoothOrder : (1 : WithTop ℕ∞) ≤ Work.FTS.EllipticEst.smoothOrder := by
  simp [Work.FTS.EllipticEst.smoothOrder]

theorem one_add_one_le_smoothOrder :
    (1 : WithTop ℕ∞) + 1 ≤ Work.FTS.EllipticEst.smoothOrder := by
  simp [Work.FTS.EllipticEst.smoothOrder]

theorem zeta_differentiableAt {φ : ℝ → ℝ} {K : ℝ}
    (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ} (hk : 2 ≤ k) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (zeta φ k) z :=
  ((zeta_contDiffOn_of_isZCut hφ hk).contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt
    smoothOrder_ne_zero

/-- `D_z ζ_k` vanishes off the support `[1/k², k²]` of the cut-off. -/
theorem zE_eq_zero_of_notMem {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K)
    {k : ℕ} (hk : 2 ≤ k) {z : ℝ}
    (hz : z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2)) : zE φ k z = 0 := by
  have hnot : z < 1 / (k : ℝ) ^ 2 ∨ (k : ℝ) ^ 2 < z := by
    by_contra hc
    push_neg at hc
    exact hz ⟨hc.1, hc.2⟩
  have hev : zeta φ k =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    rcases hnot with hlt | hgt
    · by_cases hz0 : z < 0
      · filter_upwards [Metric.ball_mem_nhds z (show 0 < -z by linarith)] with y hy
        rw [Metric.mem_ball, Real.dist_eq] at hy
        exact zeta_eq_zero_of_nonpos (le_of_lt (by linarith [(abs_lt.mp hy).2]))
      · have hpos : 0 < 1 / (k : ℝ) ^ 2 - z := by
          have hk2 : (0 : ℝ) < 1 / (k : ℝ) ^ 2 := by positivity
          linarith [not_lt.mp hz0]
        filter_upwards [Metric.ball_mem_nhds z hpos] with y hy
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have hy' : y < 1 / (k : ℝ) ^ 2 := by linarith [(abs_lt.mp hy).2]
        by_cases hy0 : y ≤ 0
        · exact zeta_eq_zero_of_nonpos hy0
        · exact zeta_eq_zero_of_notMem hφ hk (fun hc => absurd hc.1 (not_le_of_gt hy'))
    · filter_upwards [Metric.ball_mem_nhds z
        (show 0 < (z - (k : ℝ) ^ 2) / 2 by linarith)] with y hy
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have hy' : (k : ℝ) ^ 2 < y := by linarith [(abs_lt.mp hy).1]
      exact zeta_eq_zero_of_notMem hφ hk (fun hc => absurd hc.2 (not_le_of_gt hy'))
  rw [zE, hev.deriv_eq, deriv_const, mul_zero]

/-- `D_z ζ_k` vanishes where `ζ_k ≡ 1`, i.e. on `(1/k, k)`. -/
theorem zE_eq_zero_of_mem {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ}
    (hk : 2 ≤ k) {z : ℝ} (h1 : 1 / (k : ℝ) < z) (h2 : z < (k : ℝ)) : zE φ k z = 0 := by
  have hev : zeta φ k =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨h1, h2⟩] with y hy
    exact zeta_eq_one_of_mem hφ hk hy.1.le hy.2.le
  rw [zE, hev.deriv_eq, deriv_const, mul_zero]

/-- `D_z² ζ_k` vanishes off the support `[1/k², k²]` of the cut-off. -/
theorem zF_eq_zero_of_notMem {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K)
    {k : ℕ} (hk : 2 ≤ k) {z : ℝ}
    (hz : z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2)) : zF φ k z = 0 := by
  have hnot : z < 1 / (k : ℝ) ^ 2 ∨ (k : ℝ) ^ 2 < z := by
    by_contra hc
    push_neg at hc
    exact hz ⟨hc.1, hc.2⟩
  have hE : zE φ k =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    rcases hnot with hlt | hgt
    · by_cases hz0 : z < 0
      · filter_upwards [Metric.ball_mem_nhds z (show 0 < -z by linarith)] with y hy
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have hy' : y < 1 / (k : ℝ) ^ 2 := by
          have hk2 : (0 : ℝ) < 1 / (k : ℝ) ^ 2 := by positivity
          linarith [le_of_lt (by linarith [(abs_lt.mp hy).2] : y < 0)]
        exact zE_eq_zero_of_notMem hφ hk (fun hc => absurd hc.1 (not_le_of_gt hy'))
      · have hpos : 0 < 1 / (k : ℝ) ^ 2 - z := by
          have hk2 : (0 : ℝ) < 1 / (k : ℝ) ^ 2 := by positivity
          linarith [not_lt.mp hz0]
        filter_upwards [Metric.ball_mem_nhds z hpos] with y hy
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have hy' : y < 1 / (k : ℝ) ^ 2 := by linarith [(abs_lt.mp hy).2]
        exact zE_eq_zero_of_notMem hφ hk (fun hc => absurd hc.1 (not_le_of_gt hy'))
    · filter_upwards [Metric.ball_mem_nhds z
        (show 0 < (z - (k : ℝ) ^ 2) / 2 by linarith)] with y hy
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have hy' : (k : ℝ) ^ 2 < y := by linarith [(abs_lt.mp hy).1]
      exact zE_eq_zero_of_notMem hφ hk (fun hc => absurd hc.2 (not_le_of_gt hy'))
  rw [zF, hE.deriv_eq, deriv_const, mul_zero]

/-- The commutator bound `|D_z ζ_k| ≤ K / log k`. -/
theorem zE_abs_le {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ}
    (hk : 2 ≤ k) (z : ℝ) : |zE φ k z| ≤ K / Real.log k := by
  rcases le_or_gt z 0 with hz | hz
  · have h0 : zE φ k z = 0 :=
      zE_eq_zero_of_notMem hφ hk (fun hc => absurd hc.1 (not_le_of_gt (by
        have : (0 : ℝ) < 1 / (k : ℝ) ^ 2 := by positivity
        linarith)))
    rw [h0, abs_zero]
    exact div_nonneg hφ.2.2.2.2.1
      (Real.log_nonneg (by exact_mod_cast le_trans (by norm_num) hk))
  · exact Work.FTS.EllipticEst.Alpha4.zc_deriv_bound
      (fun z' hz' => (Work.FTS.EllipticEst.ZCuts.zCut_props hφ k hk).2.2.2.2 z' hz') z hz

/-- `zE` is continuous on `(0,∞)`. -/
theorem zE_continuousOn_of_isZCut {φ : ℝ → ℝ} {K : ℝ}
    (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ} (hk : 2 ≤ k) :
    ContinuousOn (zE φ k) (Set.Ioi 0) :=
  continuousOn_id.mul
    (((zeta_contDiffOn_of_isZCut hφ hk).deriv_of_isOpen isOpen_Ioi
      one_add_one_le_smoothOrder).continuousOn)

/-! ## The Leibniz rules for `ζ_k · G` -/

/-- `∂_θ (ζ_k G) = ζ_k ∂_θ G`. -/
theorem cut_pth {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ}
    (hk : 2 ≤ k) {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.pth (cut φ k G) z θ = zeta φ k z * Work.Spaces.pth G z θ := by
  have hd : DifferentiableAt ℝ (fun θ' : ℝ => G z θ') θ :=
    Work.FTS.EllipticEst.ThetaU.SmoothOpenθ.differentiableAt_slice hG hz hθ
  show deriv (fun θ' : ℝ => cut φ k G z θ') θ
      = zeta φ k z * deriv (fun θ' : ℝ => G z θ') θ
  exact deriv_const_mul _ hd

/-- `∂_θ² (ζ_k G) = ζ_k ∂_θ² G`. -/
theorem cut_pthPth {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ}
    (hk : 2 ≤ k) {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.pth (Work.Spaces.pth (cut φ k G)) z θ
      = zeta φ k z * Work.Spaces.pth (Work.Spaces.pth G) z θ := by
  show deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => cut φ k G z θ'') θ') θ
      = zeta φ k z * deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => G z θ'') θ') θ
  have hev : (fun θ' : ℝ => deriv (fun θ'' : ℝ => cut φ k G z θ'') θ') =ᶠ[𝓝 θ]
      (fun θ' => zeta φ k z * deriv (fun θ'' : ℝ => G z θ'') θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact cut_pth hφ hk hG hz hθ'
  rw [hev.deriv_eq]
  exact deriv_const_mul _
    (Work.FTS.EllipticEst.ThetaU.SmoothOpenθ.differentiableAt_slice (hG.pthIter 1) hz hθ)

/-- `D_z (ζ_k G) = (D_zζ_k) G + ζ_k D_zG`. -/
theorem cut_Dz {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ}
    (hk : 2 ≤ k) {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.Dz (cut φ k G) z θ
      = zE φ k z * G z θ + zeta φ k z * Work.Spaces.Dz G z θ := by
  have h1 : DifferentiableAt ℝ (fun z' : ℝ => zeta φ k z') z := zeta_differentiableAt hφ hk hz
  have h2 : DifferentiableAt ℝ (fun z' : ℝ => G z' θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      ((hG.contDiffAt 2 hz hθ).differentiableAt (by norm_num))
  have hmain : deriv (fun z' : ℝ => zeta φ k z' * G z' θ) z
      = deriv (zeta φ k) z * G z θ + zeta φ k z * deriv (fun z' : ℝ => G z' θ) z := by
    rw [show (fun z' : ℝ => zeta φ k z' * G z' θ)
        = (fun z' : ℝ => zeta φ k z') * (fun z' : ℝ => G z' θ) from rfl]
    exact deriv_mul h1 h2
  show z * deriv (fun z' : ℝ => zeta φ k z' * G z' θ) z
      = z * deriv (zeta φ k) z * G z θ + zeta φ k z * (z * deriv (fun z' : ℝ => G z' θ) z)
  rw [hmain]
  ring

/-- `D_z ∂_θ (ζ_k G) = (D_zζ_k) ∂_θG + ζ_k D_z∂_θG`. -/
theorem cut_DzPth {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ}
    (hk : 2 ≤ k) {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.Dz (Work.Spaces.pth (cut φ k G)) z θ
      = zE φ k z * Work.Spaces.pth G z θ
        + zeta φ k z * Work.Spaces.Dz (Work.Spaces.pth G) z θ := by
  have h1 : DifferentiableAt ℝ (fun z' : ℝ => zeta φ k z') z := zeta_differentiableAt hφ hk hz
  have h2 : DifferentiableAt ℝ (fun z' : ℝ => deriv (fun θ' : ℝ => G z' θ') θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      (((hG.pthIter 1).contDiffAt 2 hz hθ).differentiableAt (by norm_num))
  have hev : (fun z' : ℝ => deriv (fun θ' : ℝ => cut φ k G z' θ') θ) =ᶠ[𝓝 z]
      (fun z' => zeta φ k z' * deriv (fun θ' : ℝ => G z' θ') θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact cut_pth hφ hk hG hz' hθ
  have hmain : deriv (fun z' : ℝ => deriv (fun θ' : ℝ => cut φ k G z' θ') θ) z
      = deriv (zeta φ k) z * deriv (fun θ' : ℝ => G z θ') θ
        + zeta φ k z * deriv (fun z' : ℝ => deriv (fun θ' : ℝ => G z' θ') θ) z := by
    rw [hev.deriv_eq]
    rw [show (fun z' : ℝ => zeta φ k z' * deriv (fun θ' : ℝ => G z' θ') θ)
        = (fun z' : ℝ => zeta φ k z')
          * (fun z' : ℝ => deriv (fun θ' : ℝ => G z' θ') θ) from rfl]
    exact deriv_mul h1 h2
  show z * deriv (fun z' : ℝ => deriv (fun θ' : ℝ => cut φ k G z' θ') θ) z
      = z * deriv (zeta φ k) z * deriv (fun θ' : ℝ => G z θ') θ
        + zeta φ k z * (z * deriv (fun z' : ℝ => deriv (fun θ' : ℝ => G z' θ') θ) z)
  rw [hmain]
  ring

/-- `D_z² (ζ_k G) = (D_z²ζ_k) G + 2 (D_zζ_k) D_zG + ζ_k D_z²G`. -/
theorem cut_DzDz {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ}
    (hk : 2 ≤ k) {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.Dz (Work.Spaces.Dz (cut φ k G)) z θ
      = zF φ k z * G z θ + 2 * (zE φ k z * Work.Spaces.Dz G z θ)
        + zeta φ k z * Work.Spaces.Dz (Work.Spaces.Dz G) z θ := by
  have hζ1 : ContDiffOn ℝ 1 (deriv (zeta φ k)) (Set.Ioi 0) :=
    (zeta_contDiffOn_of_isZCut hφ hk).deriv_of_isOpen isOpen_Ioi one_add_one_le_smoothOrder
  have h1 : DifferentiableAt ℝ (fun z' : ℝ => zE φ k z') z := by
    show DifferentiableAt ℝ (fun z' : ℝ => z' * deriv (zeta φ k) z') z
    exact differentiableAt_id.mul
      ((hζ1.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num))
  have h2 : DifferentiableAt ℝ (fun z' : ℝ => G z' θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      ((hG.contDiffAt 2 hz hθ).differentiableAt (by norm_num))
  have h3 : DifferentiableAt ℝ (fun z' : ℝ => zeta φ k z') z := zeta_differentiableAt hφ hk hz
  have h4 : DifferentiableAt ℝ (fun z' : ℝ => z' * deriv (fun z'' : ℝ => G z'' θ) z') z :=
    Work.Spaces.differentiableAt_slice_fst
      (F := Function.uncurry (Work.Spaces.DzIter 1 G)) (z := z) (θ := θ)
      (((hG.DzIter 1).contDiffAt 2 hz hθ).differentiableAt (by norm_num))
  have hev : (fun z' : ℝ => z' * deriv (fun z'' : ℝ => cut φ k G z'' θ) z') =ᶠ[𝓝 z]
      (fun z' => zE φ k z' * G z' θ
        + zeta φ k z' * (z' * deriv (fun z'' : ℝ => G z'' θ) z')) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact cut_Dz hφ hk hG hz' hθ
  have hmain : deriv (fun z' : ℝ => z' * deriv (fun z'' : ℝ => cut φ k G z'' θ) z') z
      = deriv (fun z' : ℝ => zE φ k z') z * G z θ + zE φ k z * deriv (fun z' : ℝ => G z' θ) z
        + (deriv (fun z' : ℝ => zeta φ k z') z * (z * deriv (fun z'' : ℝ => G z'' θ) z)
          + zeta φ k z * deriv (fun z' : ℝ => z' * deriv (fun z'' : ℝ => G z'' θ) z') z) := by
    rw [hev.deriv_eq]
    have e1 : deriv (fun z' : ℝ => zE φ k z' * G z' θ
          + zeta φ k z' * (z' * deriv (fun z'' : ℝ => G z'' θ) z')) z
        = deriv (fun z' : ℝ => zE φ k z' * G z' θ) z
          + deriv (fun z' : ℝ => zeta φ k z' * (z' * deriv (fun z'' : ℝ => G z'' θ) z')) z := by
      rw [show (fun z' : ℝ => zE φ k z' * G z' θ
            + zeta φ k z' * (z' * deriv (fun z'' : ℝ => G z'' θ) z'))
          = (fun z' : ℝ => zE φ k z' * G z' θ)
            + (fun z' : ℝ => zeta φ k z' * (z' * deriv (fun z'' : ℝ => G z'' θ) z')) from rfl]
      exact deriv_add (h1.mul h2) (h3.mul h4)
    rw [e1]
    have e2 : deriv (fun z' : ℝ => zE φ k z' * G z' θ) z
        = deriv (fun z' : ℝ => zE φ k z') z * G z θ
          + zE φ k z * deriv (fun z' : ℝ => G z' θ) z := by
      rw [show (fun z' : ℝ => zE φ k z' * G z' θ)
          = (fun z' : ℝ => zE φ k z') * (fun z' : ℝ => G z' θ) from rfl]
      exact deriv_mul h1 h2
    have e3 : deriv (fun z' : ℝ => zeta φ k z' * (z' * deriv (fun z'' : ℝ => G z'' θ) z')) z
        = deriv (fun z' : ℝ => zeta φ k z') z * (z * deriv (fun z'' : ℝ => G z'' θ) z)
          + zeta φ k z * deriv (fun z' : ℝ => z' * deriv (fun z'' : ℝ => G z'' θ) z') z := by
      rw [show (fun z' : ℝ => zeta φ k z' * (z' * deriv (fun z'' : ℝ => G z'' θ) z'))
          = (fun z' : ℝ => zeta φ k z')
            * (fun z' : ℝ => z' * deriv (fun z'' : ℝ => G z'' θ) z') from rfl]
      exact deriv_mul h3 h4
    rw [e2, e3]
  show z * deriv (fun z' : ℝ => z' * deriv (fun z'' : ℝ => cut φ k G z'' θ) z') z
      = z * deriv (fun z' : ℝ => zE φ k z') z * G z θ
        + 2 * (z * deriv (zeta φ k) z * (z * deriv (fun z' : ℝ => G z' θ) z))
        + zeta φ k z * (z * deriv (fun z' : ℝ => z' * deriv (fun z'' : ℝ => G z'' θ) z') z)
  rw [hmain]
  simp only [zE, zF]
  ring

end Work.Blocks.InterpTrunc
