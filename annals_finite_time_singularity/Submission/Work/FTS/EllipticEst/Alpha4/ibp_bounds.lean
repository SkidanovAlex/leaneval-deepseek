/-
Integration-by-parts bounds for the logarithmic cut-off of the mixed weighted interpolation
estimate of the elliptic chapter (paper §EllipticEstimates).

The three bounds collected here are steps (b) and (c) of the assembly of
`ThetaU.interpol_mixed_weighted_alpha4`: the cut-off `ζ = zc φ k` is inserted into the
`z`-integration by parts

  `- ∫_z ζ w² ∫_θ (D_zG)(∂_θ²G) σ = ∫_z (∂_zζ) w² z (D_zG)(∂_θ²G) σ
      + ∫_z ζ w² (D_z²G + b D_zG)(∂_θ²G) σ`

(`radial_ibp_weight`), and each of the three pieces is bounded by the *uncut* weighted
integrals `dInt`, `ttInt`, `ddInt`:

* the commutator piece `∫_z (∂_zζ) w² z (D_zG)(∂_θ²G) σ` is small, `≤ (K/log k)·½(dInt+ttInt)`,
  because `|z ζ'(z)| ≤ K/log k` (`ZCuts.zCut_props`);
* the "linearised" piece `∫_z ζ w² (D_z²G + b D_zG)(∂_θ²G) σ` is `≤ ddInt + 9 dInt + ½ ttInt`
  (the constant `9 = 3²` comes from `|b| ≤ 3`, `ThetaU.bcoef_abs_le`);
* the term with the *same* `∂_θ²G`-slot as the uncut quantity is simply `≤ dInt`, since
  `0 ≤ ζ ≤ 1`.

Everything is reduced to the *product measure* by `ThetaU.fubini_w_thEta` /
`ThetaU.integrable_outer_of_bound` (the test functions are compactly supported in `z` and
continuous on the quadrant), and to the a.e. angular-slice integrability
`Alpha4.integrable_slice_pthDz_sigma`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Alpha4.Cut
import Submission.Work.FTS.EllipticEst.Alpha4.Assembly
import Submission.Work.FTS.EllipticEst.Alpha4.radial_ibp_weight
import Submission.Work.FTS.EllipticEst.Alpha4.integrable_slice_pthDz_sigma
import Submission.Work.FTS.EllipticEst.Alpha4.zouter_abs_le
import Submission.Work.FTS.EllipticEst.Alpha4.deriv_zc_eq_zero_of_notMem
import Submission.Work.FTS.EllipticEst.interpol_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst
open Work.Spaces

namespace Work.FTS.EllipticEst.Alpha4

set_option maxHeartbeats 2000000

/-! ## The two test functions of the integration by parts -/

/-- The test function of the commutator piece: `(∂_zζ)(z) · z · D_zG · ∂_θ²G`. -/
def ibpF1 (φ : ℝ → ℝ) (k : ℕ) (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => deriv (zc φ k) z * z * Work.Spaces.Dz G z θ
    * Work.Spaces.pth (Work.Spaces.pth G) z θ

/-- The test function of the "linearised" piece:
`ζ(z) · (D_z²G + b(z)·D_zG) · ∂_θ²G`. -/
def ibpF2 (φ : ℝ → ℝ) (k : ℕ) (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => zc φ k z * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
      + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ)
    * Work.Spaces.pth (Work.Spaces.pth G) z θ

/-! ## The angular and radial pieces of the dominating functions -/

/-- The slice `(D_zG)² σ`. -/
def ibp_th (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ :=
  fun θ => (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ

/-- The slice `(∂_θ²G)² σ`. -/
def ibp_tt (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ :=
  fun θ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ

/-- The slice `(D_z²G)² σ`. -/
def ibp_tdd (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ :=
  fun θ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ

/-- The slice `9 (D_zG)² σ`. -/
def ibp_td9 (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ :=
  fun θ => 9 * ibp_th G z θ

/-- The slice `½ (∂_θ²G)² σ`. -/
def ibp_tt2 (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ :=
  fun θ => (1 / 2) * ibp_tt G z θ

/-- The radial slice `w² ∫_θ (D_zG)² σ`. -/
def ibp_zh (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, ibp_th G z θ

/-- The radial slice `w² ∫_θ (∂_θ²G)² σ`. -/
def ibp_zt (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, ibp_tt G z θ

/-- The radial slice `w² ∫_θ (D_z²G)² σ`. -/
def ibp_zdd (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, ibp_tdd G z θ

/-- The `D_zG`-piece of the radial dominating function of the first bound. -/
def ibpKA1 (k : ℕ) (K : ℝ) (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ((K / Real.log k) * (1 / 2)) * ibp_zh G z

/-- The `∂_θ²G`-piece of the radial dominating function of the first bound. -/
def ibpKA2 (k : ℕ) (K : ℝ) (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ((K / Real.log k) * (1 / 2)) * ibp_zt G z

/-- The `D_z²G`-piece of the radial dominating function of the second bound. -/
def ibpKB1 (G : ℝ → ℝ → ℝ) : ℝ → ℝ := ibp_zdd G

/-- The `D_zG`-piece of the radial dominating function of the second bound. -/
def ibpKB2 (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => 9 * ibp_zh G z

/-- The `∂_θ²G`-piece of the radial dominating function of the second bound. -/
def ibpKB3 (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => (1 / 2) * ibp_zt G z

/-! ## Elementary numerical and linearity lemmas -/

/-- The arithmetic-geometric mean inequality `|a| |b| ≤ (a² + b²)/2`. -/
lemma ibp_abs_mul_le_half_sq (a b : ℝ) : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-- `(a + b) c ≤ a² + b² + c²/2` for `a, b, c ≥ 0`. -/
lemma ibp_add_mul_le (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a + b) * c ≤ a ^ 2 + b ^ 2 + c ^ 2 / 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - c)]

/-- Splitting an integral of a sum of two functions. -/
lemma ibp_int_add2 {a b : ℝ → ℝ}
    (ha : MeasureTheory.Integrable a (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hb : MeasureTheory.Integrable b (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (∫ θ in Work.Spaces.Iθ, (a + b) θ)
      = (∫ θ in Work.Spaces.Iθ, a θ) + ∫ θ in Work.Spaces.Iθ, b θ :=
  MeasureTheory.integral_add ha hb

/-- Splitting an integral of a sum of three functions. -/
lemma ibp_int_add3 {a b c : ℝ → ℝ}
    (ha : MeasureTheory.Integrable a (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hb : MeasureTheory.Integrable b (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hc : MeasureTheory.Integrable c (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (∫ θ in Work.Spaces.Iθ, (a + (b + c)) θ)
      = (∫ θ in Work.Spaces.Iθ, a θ)
        + ((∫ θ in Work.Spaces.Iθ, b θ) + ∫ θ in Work.Spaces.Iθ, c θ) := by
  have h1 : (∫ θ in Work.Spaces.Iθ, (a + (b + c)) θ)
      = (∫ θ in Work.Spaces.Iθ, a θ) + ∫ θ in Work.Spaces.Iθ, (b + c) θ :=
    MeasureTheory.integral_add ha (hb.add hc)
  have h2 : (∫ θ in Work.Spaces.Iθ, (b + c) θ)
      = (∫ θ in Work.Spaces.Iθ, b θ) + ∫ θ in Work.Spaces.Iθ, c θ :=
    MeasureTheory.integral_add hb hc
  rw [h1, h2]

/-- Splitting a radial integral of a sum of two functions. -/
lemma ibp_intz_add2 {A B : ℝ → ℝ}
    (hA : MeasureTheory.Integrable A (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hB : MeasureTheory.Integrable B (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    (∫ z in Work.Spaces.Iz, (A + B) z)
      = (∫ z in Work.Spaces.Iz, A z) + ∫ z in Work.Spaces.Iz, B z :=
  MeasureTheory.integral_add hA hB

/-- Splitting a radial integral of a sum of three functions. -/
lemma ibp_intz_add3 {A B C : ℝ → ℝ}
    (hA : MeasureTheory.Integrable A (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hB : MeasureTheory.Integrable B (MeasureTheory.volume.restrict Work.Spaces.Iz))
    (hC : MeasureTheory.Integrable C (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    (∫ z in Work.Spaces.Iz, (A + (B + C)) z)
      = (∫ z in Work.Spaces.Iz, A z)
        + ((∫ z in Work.Spaces.Iz, B z) + ∫ z in Work.Spaces.Iz, C z) := by
  have h1 : (∫ z in Work.Spaces.Iz, (A + (B + C)) z)
      = (∫ z in Work.Spaces.Iz, A z) + ∫ z in Work.Spaces.Iz, (B + C) z :=
    MeasureTheory.integral_add hA (hB.add hC)
  have h2 : (∫ z in Work.Spaces.Iz, (B + C) z)
      = (∫ z in Work.Spaces.Iz, B z) + ∫ z in Work.Spaces.Iz, C z :=
    MeasureTheory.integral_add hB hC
  rw [h1, h2]

/-- The commutator bound of the logarithmic cut-off: `|z ζ'(z)| ≤ K / log k` for `z ∈ Iz`. -/
lemma ibp_zc_deriv_mul_le {k : ℕ} (hk2 : 2 ≤ k) {φ : ℝ → ℝ} {K : ℝ}
    (hφK : Work.FTS.EllipticEst.IsZCut φ K) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    |z * deriv (zc φ k) z| ≤ K / Real.log k := by
  have hlog : 0 < Real.log (k : ℝ) :=
    Real.log_pos (Work.FTS.EllipticEst.ZCuts.one_lt_natCast_of_two_le hk2)
  have hz' : (0 : ℝ) ≤ z := hz
  rcases le_or_gt z 0 with h | h
  · have hz0 : z = 0 := le_antisymm h hz'
    rw [hz0]; simp only [zero_mul, abs_zero]
    exact div_nonneg hφK.2.2.2.2.1 hlog.le
  · rw [zc_deriv_eq h]
    exact Work.FTS.EllipticEst.ZCuts.abs_mul_deriv_psiFun_le hφK.1 hφK.2.2.2.2.2 hk2 h

/-- Pointwise bound of the commutator test function. -/
lemma ibp_abs_F1_le {k : ℕ} (hk2 : 2 ≤ k) {φ : ℝ → ℝ} {K : ℝ}
    (hφK : Work.FTS.EllipticEst.IsZCut φ K) {G : ℝ → ℝ → ℝ} {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (θ : ℝ) :
    |ibpF1 φ k G z θ|
      ≤ (K / Real.log k) * (1 / 2)
        * ((Work.Spaces.Dz G z θ) ^ 2 + (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2) := by
  have hlog : 0 < Real.log (k : ℝ) :=
    Real.log_pos (Work.FTS.EllipticEst.ZCuts.one_lt_natCast_of_two_le hk2)
  have hK : 0 ≤ K / Real.log k := div_nonneg hφK.2.2.2.2.1 hlog.le
  have hkey := ibp_zc_deriv_mul_le hk2 hφK hz
  have h1 : |ibpF1 φ k G z θ| = |z * deriv (zc φ k) z| * |Work.Spaces.Dz G z θ|
      * |Work.Spaces.pth (Work.Spaces.pth G) z θ| := by
    simp only [ibpF1]
    rw [abs_mul, abs_mul, mul_comm (deriv (zc φ k) z) z]
  rw [h1]
  have h2 : |z * deriv (zc φ k) z| * |Work.Spaces.Dz G z θ|
        * |Work.Spaces.pth (Work.Spaces.pth G) z θ|
      ≤ (K / Real.log k)
        * (|Work.Spaces.Dz G z θ| * |Work.Spaces.pth (Work.Spaces.pth G) z θ|) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hkey (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have h3 : |Work.Spaces.Dz G z θ| * |Work.Spaces.pth (Work.Spaces.pth G) z θ|
      ≤ ((Work.Spaces.Dz G z θ) ^ 2 + (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2) / 2 :=
    ibp_abs_mul_le_half_sq _ _
  calc |z * deriv (zc φ k) z| * |Work.Spaces.Dz G z θ|
        * |Work.Spaces.pth (Work.Spaces.pth G) z θ|
      ≤ (K / Real.log k)
          * (|Work.Spaces.Dz G z θ| * |Work.Spaces.pth (Work.Spaces.pth G) z θ|) := h2
    _ ≤ (K / Real.log k)
          * (((Work.Spaces.Dz G z θ) ^ 2
            + (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left h3 hK
    _ = (K / Real.log k) * (1 / 2)
          * ((Work.Spaces.Dz G z θ) ^ 2
            + (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2) := by ring

/-- Pointwise bound of the "linearised" test function. -/
lemma ibp_abs_F2_le {k : ℕ} (hk2 : 2 ≤ k) {φ : ℝ → ℝ} {K : ℝ}
    (hφK : Work.FTS.EllipticEst.IsZCut φ K) {G : ℝ → ℝ → ℝ} {z : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (θ : ℝ) :
    |ibpF2 φ k G z θ|
      ≤ (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
        + 9 * (Work.Spaces.Dz G z θ) ^ 2
        + (1 / 2) * (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 := by
  have hζnn : 0 ≤ zc φ k z :=
    zc_nonneg (fun y => (Work.FTS.EllipticEst.ZCuts.psiFun_mem_Icc hφK.2.2.2.1 y).1) z
  have hζle : zc φ k z ≤ 1 :=
    zc_le_one (fun y => (Work.FTS.EllipticEst.ZCuts.psiFun_mem_Icc hφK.2.2.2.1 y).2) z
  have hb : |Work.FTS.EllipticEst.ThetaU.bcoef z| ≤ 3 :=
    Work.FTS.EllipticEst.ThetaU.bcoef_abs_le hz
  have h1 : |ibpF2 φ k G z θ| = zc φ k z
      * |Work.Spaces.Dz (Work.Spaces.Dz G) z θ
          + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ|
      * |Work.Spaces.pth (Work.Spaces.pth G) z θ| := by
    simp only [ibpF2]
    rw [abs_mul, abs_mul, abs_of_nonneg hζnn]
  have h4 : |Work.Spaces.Dz (Work.Spaces.Dz G) z θ
        + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ|
      ≤ |Work.Spaces.Dz (Work.Spaces.Dz G) z θ| + 3 * |Work.Spaces.Dz G z θ| := by
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul]
    have hb' : |Work.FTS.EllipticEst.ThetaU.bcoef z| * |Work.Spaces.Dz G z θ|
        ≤ 3 * |Work.Spaces.Dz G z θ| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    linarith
  calc |ibpF2 φ k G z θ|
      = zc φ k z * |Work.Spaces.Dz (Work.Spaces.Dz G) z θ
          + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ|
        * |Work.Spaces.pth (Work.Spaces.pth G) z θ| := h1
    _ ≤ 1 * |Work.Spaces.Dz (Work.Spaces.Dz G) z θ
          + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ|
        * |Work.Spaces.pth (Work.Spaces.pth G) z θ| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hζle (abs_nonneg _))
          (abs_nonneg _)
    _ = |Work.Spaces.Dz (Work.Spaces.Dz G) z θ
          + Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ|
        * |Work.Spaces.pth (Work.Spaces.pth G) z θ| := by ring
    _ ≤ (|Work.Spaces.Dz (Work.Spaces.Dz G) z θ| + 3 * |Work.Spaces.Dz G z θ|)
        * |Work.Spaces.pth (Work.Spaces.pth G) z θ| :=
        mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
    _ ≤ |Work.Spaces.Dz (Work.Spaces.Dz G) z θ| ^ 2
        + (3 * |Work.Spaces.Dz G z θ|) ^ 2
        + (|Work.Spaces.pth (Work.Spaces.pth G) z θ|) ^ 2 / 2 :=
        ibp_add_mul_le _ _ _ (abs_nonneg _)
          (mul_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _)
    _ = (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
        + 9 * (Work.Spaces.Dz G z θ) ^ 2
        + (1 / 2) * (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 := by
        nlinarith [sq_abs (Work.Spaces.Dz (Work.Spaces.Dz G) z θ),
          sq_abs (Work.Spaces.Dz G z θ), sq_abs (Work.Spaces.pth (Work.Spaces.pth G) z θ)]

/-! ## The three bounds -/

theorem ibp_bounds {k : ℕ} (hk2 : 2 ≤ k) {φ : ℝ → ℝ} {K : ℝ}
    (hφK : Work.FTS.EllipticEst.IsZCut φ K) {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    (hd : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz)
    (ht : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz)
    (hdd : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz) :
    |∫ θ in Work.Spaces.Iθ,
        (∫ z in Work.Spaces.Iz, deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) z
          * (Work.Spaces.w z) ^ 2 * z * (Work.Spaces.Dz G z θ)
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
        * Work.FTS.EllipticEst.thEta θ|
      ≤ K / Real.log k * ((1 / 2) * (Work.FTS.EllipticEst.dInt G
          + Work.FTS.EllipticEst.ttInt G))
    ∧ (∫ θ in Work.Spaces.Iθ,
        (∫ z in Work.Spaces.Iz, (Work.FTS.EllipticEst.Alpha4.zc φ k z)
          * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
            + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
        * Work.FTS.EllipticEst.thEta θ)
      ≤ Work.FTS.EllipticEst.ddInt G + 9 * Work.FTS.EllipticEst.dInt G
        + (1 / 2) * Work.FTS.EllipticEst.ttInt G
    ∧ (∫ z in Work.Spaces.Iz, (Work.FTS.EllipticEst.Alpha4.zc φ k z)
        * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ))
      ≤ Work.FTS.EllipticEst.dInt G := by
  -- ## the elementary facts
  have hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G := hsm
  have hφcd : ContDiff ℝ Work.FTS.EllipticEst.smoothOrder φ := hφK.1
  have hφzero : ∀ t, 2 ≤ |t| → φ t = 0 := hφK.2.2.1
  have hφbdd : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1 := hφK.2.2.2.1
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk2
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk4 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [hkR]
  have hδ : 0 < 1 / (k : ℝ) ^ 2 := by positivity
  have hδR : 1 / (k : ℝ) ^ 2 < (k : ℝ) ^ 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)]
    nlinarith [hk4]
  have hζcd : ContDiffOn ℝ 1 (zc φ k) (Set.Ioi 0) :=
    zc_contDiffOn (Work.FTS.EllipticEst.ZCuts.psiFun_contDiffOn hφcd hk2)
  have hζnn : ∀ z, 0 ≤ zc φ k z :=
    fun z => zc_nonneg (fun y => (Work.FTS.EllipticEst.ZCuts.psiFun_mem_Icc hφbdd y).1) z
  have hζle : ∀ z, zc φ k z ≤ 1 :=
    fun z => zc_le_one (fun y => (Work.FTS.EllipticEst.ZCuts.psiFun_mem_Icc hφbdd y).2) z
  have hζsupp : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) → zc φ k z = 0 :=
    fun z hz => zc_eq_zero_of_notMem hk1
      (fun z' hz' hz'' => Work.FTS.EllipticEst.ZCuts.psiFun_eq_zero hφzero hk2 hz' hz'') hz
  have hζ'supp : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) →
      deriv (zc φ k) z = 0 :=
    fun z hz => deriv_zc_eq_zero_of_notMem hk2 hφK hz
  -- ## the two test functions: continuity, support, boundedness
  have hF₁c : ContinuousOn (Function.uncurry (ibpF1 φ k G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hder : ContinuousOn (fun p : ℝ × ℝ => deriv (zc φ k) p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (hζcd.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).comp continuousOn_fst
        (fun p hp => hp.1)
    have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz G p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      continuousOn_quad_mixed hG 1 0
    have hT : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      continuousOn_quad_pthDz hG 0 2
    have hmain : ContinuousOn (fun p : ℝ × ℝ => deriv (zc φ k) p.1 * p.1
        * Work.Spaces.Dz G p.1 p.2 * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := ((hder.mul continuousOn_fst).mul hD).mul hT
    refine hmain.congr (fun p hp => ?_)
    simp only [Function.uncurry, ibpF1]
  have hF₁0 : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) → ∀ θ,
      ibpF1 φ k G z θ = 0 := by
    intro z hz θ
    simp only [ibpF1]
    rw [hζ'supp z hz]; ring
  have hF₁box : ContinuousOn (Function.uncurry (ibpF1 φ k G))
      (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) := by
    have hder : ContinuousOn (fun p : ℝ × ℝ => deriv (zc φ k) p.1)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      (hζcd.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).comp continuousOn_fst
        (fun p hp => lt_of_lt_of_le hδ hp.1.1)
    have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz G p.1 p.2)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      continuousOn_box_mixed hG 1 0 hδ
    have hT : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      continuousOn_box_pthDz hG 0 2 hδ
    have hmain : ContinuousOn (fun p : ℝ × ℝ => deriv (zc φ k) p.1 * p.1
        * Work.Spaces.Dz G p.1 p.2 * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      ((hder.mul continuousOn_fst).mul hD).mul hT
    refine hmain.congr (fun p hp => ?_)
    simp only [Function.uncurry, ibpF1]
  obtain ⟨M₁, -, hM₁b⟩ :=
    Work.FTS.EllipticEst.ThetaU.exists_bound_box hδ hδR hF₁box
  have hF₁b : ∃ Mb : ℝ, ∀ z ∈ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2),
      ∀ θ ∈ Work.Spaces.Iθ, |ibpF1 φ k G z θ| ≤ Mb := ⟨M₁, hM₁b⟩
  have hF₂c : ContinuousOn (Function.uncurry (ibpF2 φ k G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hzc : ContinuousOn (fun p : ℝ × ℝ => zc φ k p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hζcd.continuousOn.comp continuousOn_fst (fun p hp => hp.1)
    have hb : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.ThetaU.bcoef p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      bcoef_continuousOn.comp continuousOn_fst (fun p hp => hp.1)
    have hDD : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_quad_mixed hG 2 0
    have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz G p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_quad_mixed hG 1 0
    have hT : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_quad_pthDz hG 0 2
    have hmain : ContinuousOn (fun p : ℝ × ℝ => zc φ k p.1
        * (Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
          + Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
        * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (hzc.mul (hDD.add (hb.mul hD))).mul hT
    refine hmain.congr (fun p hp => ?_)
    simp only [Function.uncurry, ibpF2]
  have hF₂0 : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) → ∀ θ,
      ibpF2 φ k G z θ = 0 := by
    intro z hz θ
    simp only [ibpF2]
    rw [hζsupp z hz]; ring
  have hF₂box : ContinuousOn (Function.uncurry (ibpF2 φ k G))
      (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) := by
    have hzc : ContinuousOn (fun p : ℝ × ℝ => zc φ k p.1)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      hζcd.continuousOn.comp continuousOn_fst (fun p hp => lt_of_lt_of_le hδ hp.1.1)
    have hb : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.ThetaU.bcoef p.1)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      bcoef_continuousOn.comp continuousOn_fst (fun p hp => lt_of_lt_of_le hδ hp.1.1)
    have hDD : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      continuousOn_box_mixed hG 2 0 hδ
    have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz G p.1 p.2)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      continuousOn_box_mixed hG 1 0 hδ
    have hT : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      continuousOn_box_pthDz hG 0 2 hδ
    have hmain : ContinuousOn (fun p : ℝ × ℝ => zc φ k p.1
        * (Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
          + Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
        * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
      (hzc.mul (hDD.add (hb.mul hD))).mul hT
    refine hmain.congr (fun p hp => ?_)
    simp only [Function.uncurry, ibpF2]
  obtain ⟨M₂, -, hM₂b⟩ :=
    Work.FTS.EllipticEst.ThetaU.exists_bound_box hδ hδR hF₂box
  have hF₂b : ∃ Mb : ℝ, ∀ z ∈ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2),
      ∀ θ ∈ Work.Spaces.Iθ, |ibpF2 φ k G z θ| ≤ Mb := ⟨M₂, hM₂b⟩
  -- ## a.e. angular-slice integrability of the three dominating slices
  have hIntD : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (ibp_th G z) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    integrable_slice_pthDz_sigma hG 1 0
  have hIntT : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (ibp_tt G z) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    integrable_slice_pthDz_sigma hG 0 2
  have hIntDD : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (ibp_tdd G z) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    integrable_slice_pthDz_sigma hG 2 0
  -- ## the `z`-outer integrability of the uncut integrands
  have hd' : MeasureTheory.Integrable (ibp_zh G) (MeasureTheory.volume.restrict
      Work.Spaces.Iz) := by
    refine hd.congr (Filter.Eventually.of_forall fun z => ?_)
    show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) = ibp_zh G z
    simp only [ibp_zh]
    rw [show (fun θ : ℝ => (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = fun θ : ℝ => ((Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            * (Work.Spaces.w z) ^ 2 from by funext θ; ring,
      MeasureTheory.integral_mul_const]
    simp only [ibp_th]
    ring
  have ht' : MeasureTheory.Integrable (ibp_zt G) (MeasureTheory.volume.restrict
      Work.Spaces.Iz) := by
    refine ht.congr (Filter.Eventually.of_forall fun z => ?_)
    show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) = ibp_zt G z
    simp only [ibp_zt]
    rw [show (fun θ : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        = fun θ : ℝ => ((Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) * (Work.Spaces.w z) ^ 2 from by funext θ; ring,
      MeasureTheory.integral_mul_const]
    simp only [ibp_tt]
    ring
  have hdd' : MeasureTheory.Integrable (ibp_zdd G) (MeasureTheory.volume.restrict
      Work.Spaces.Iz) := by
    refine hdd.congr (Filter.Eventually.of_forall fun z => ?_)
    show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
        * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) = ibp_zdd G z
    simp only [ibp_zdd]
    rw [show (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        = fun θ : ℝ => ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) * (Work.Spaces.w z) ^ 2 from by funext θ; ring,
      MeasureTheory.integral_mul_const]
    simp only [ibp_tdd]
    ring
  -- ## the third bound: the cut-off is `≤ 1`
  have hc : (∫ z in Work.Spaces.Iz, (zc φ k z) * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)) ≤ Work.FTS.EllipticEst.dInt G := by
    rw [dInt_eq G]
    refine MeasureTheory.integral_mono_of_nonneg ?_ hd' ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact mul_nonneg (mul_nonneg (hζnn z) (sq_nonneg _))
        (MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      have hX : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ :=
        MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
      calc (zc φ k z) * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)
          ≤ 1 * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hζle z) (sq_nonneg _)) hX
        _ = (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := by ring
  -- ## the first bound
  have hA_split : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, ibpF1 φ k G z θ * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz, deriv (zc φ k) z
          * (Work.Spaces.w z) ^ 2 * z * Work.Spaces.Dz G z θ
          * Work.Spaces.pth (Work.Spaces.pth G) z θ) * Work.FTS.EllipticEst.thEta θ := by
    rw [Work.FTS.EllipticEst.ThetaU.fubini_w_thEta (F := ibpF1 φ k G) hδ hF₁c hF₁0 hF₁b]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    simp only [ibpF1]; ring
  have hzabA := zouter_abs_le hδ hF₁c hF₁0 hM₁b
  have hInnerDT : ∀ z, MeasureTheory.Integrable (ibp_th G z)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) →
      MeasureTheory.Integrable (ibp_tt G z) (MeasureTheory.volume.restrict Work.Spaces.Iθ) →
      (∫ θ in Work.Spaces.Iθ, ((K / Real.log k) * (1 / 2)
          * ((Work.Spaces.Dz G z θ) ^ 2
            + (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2))
          * Work.FTS.EllipticEst.thEta θ)
        = ((K / Real.log k) * (1 / 2))
          * ((∫ θ in Work.Spaces.Iθ, ibp_th G z θ)
            + (∫ θ in Work.Spaces.Iθ, ibp_tt G z θ)) := by
    intro z hD hT
    have hlin : (∫ θ in Work.Spaces.Iθ, ((K / Real.log k) * (1 / 2)
          * ((Work.Spaces.Dz G z θ) ^ 2 + (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2))
          * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ,
            (fun θ : ℝ => ((K / Real.log k) * (1 / 2)) * (ibp_th G z + ibp_tt G z) θ) θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [Pi.add_apply, ibp_th, ibp_tt]; ring
    rw [hlin]
    have hmul : (∫ θ in Work.Spaces.Iθ,
          (fun θ : ℝ => ((K / Real.log k) * (1 / 2)) * (ibp_th G z + ibp_tt G z) θ) θ)
        = ((K / Real.log k) * (1 / 2))
          * (∫ θ in Work.Spaces.Iθ, (ibp_th G z + ibp_tt G z) θ) :=
      MeasureTheory.integral_const_mul ((K / Real.log k) * (1 / 2)) (ibp_th G z + ibp_tt G z)
    rw [hmul, ibp_int_add2 (a := ibp_th G z) (b := ibp_tt G z) hD hT]
  have hIntDT : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => ((K / Real.log k) * (1 / 2)
        * ((Work.Spaces.Dz G z θ) ^ 2 + (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2))
        * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hIntD, hIntT] with z hD hT
    refine ((hD.add hT).const_mul ((K / Real.log k) * (1 / 2))).congr ?_
    filter_upwards with θ
    simp only [Pi.add_apply, ibp_th, ibp_tt]
    ring
  have hNegA : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2
      * ∫ θ in Work.Spaces.Iθ, ((K / Real.log k) * (1 / 2)
        * ((Work.Spaces.Dz G z θ) ^ 2 + (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2))
        * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine ((hd'.const_mul ((K / Real.log k) * (1 / 2))).add
      (ht'.const_mul ((K / Real.log k) * (1 / 2)))).congr ?_
    filter_upwards [hIntD, hIntT] with z hD hT
    simp only [Pi.add_apply, ibp_zh, ibp_zt]
    rw [hInnerDT z hD hT]
    ring
  have hFinA : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, ((K / Real.log k) * (1 / 2)
          * ((Work.Spaces.Dz G z θ) ^ 2 + (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2))
          * Work.FTS.EllipticEst.thEta θ)
      = K / Real.log k * ((1 / 2) * (Work.FTS.EllipticEst.dInt G
          + Work.FTS.EllipticEst.ttInt G)) := by
    have step1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, ((K / Real.log k) * (1 / 2)
            * ((Work.Spaces.Dz G z θ) ^ 2 + (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2))
            * Work.FTS.EllipticEst.thEta θ)
        = ∫ z in Work.Spaces.Iz, (ibpKA1 k K G + ibpKA2 k K G) z := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hIntD, hIntT] with z hD hT
      simp only [Pi.add_apply, ibpKA1, ibpKA2, ibp_zh, ibp_zt]
      rw [hInnerDT z hD hT]
      ring
    have step2 : (∫ z in Work.Spaces.Iz, (ibpKA1 k K G + ibpKA2 k K G) z)
        = (∫ z in Work.Spaces.Iz, ibpKA1 k K G z)
          + (∫ z in Work.Spaces.Iz, ibpKA2 k K G z) :=
      ibp_intz_add2 (A := ibpKA1 k K G) (B := ibpKA2 k K G)
        (hd'.const_mul ((K / Real.log k) * (1 / 2)))
        (ht'.const_mul ((K / Real.log k) * (1 / 2)))
    have step3 : (∫ z in Work.Spaces.Iz, ibpKA1 k K G z)
        = ((K / Real.log k) * (1 / 2))
          * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
      MeasureTheory.integral_const_mul ((K / Real.log k) * (1 / 2)) (ibp_zh G)
    have step4 : (∫ z in Work.Spaces.Iz, ibpKA2 k K G z)
        = ((K / Real.log k) * (1 / 2))
          * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) :=
      MeasureTheory.integral_const_mul ((K / Real.log k) * (1 / 2)) (ibp_zt G)
    rw [step1, step2, step3, step4, ← dInt_eq G, ← ttInt_eq G]
    ring
  have ha : |∫ θ in Work.Spaces.Iθ,
        (∫ z in Work.Spaces.Iz, deriv (zc φ k) z
          * (Work.Spaces.w z) ^ 2 * z * Work.Spaces.Dz G z θ
          * Work.Spaces.pth (Work.Spaces.pth G) z θ)
        * Work.FTS.EllipticEst.thEta θ|
      ≤ K / Real.log k * ((1 / 2) * (Work.FTS.EllipticEst.dInt G
          + Work.FTS.EllipticEst.ttInt G)) := by
    rw [← hA_split]
    refine le_trans hzabA ?_
    refine le_trans ?_ (le_of_eq hFinA)
    refine MeasureTheory.integral_mono_of_nonneg ?_ hNegA ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact mul_nonneg (sq_nonneg _)
        (MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (abs_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))
    · filter_upwards [hIntDT, MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hIT hz
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine MeasureTheory.integral_mono_of_nonneg ?_ hIT ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_nonneg (abs_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_le_mul_of_nonneg_right (ibp_abs_F1_le hk2 hφK hz θ)
          (Work.FTS.EllipticEst.thEta_nonneg hθ)
  -- ## the second bound
  have hB_split : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, ibpF2 φ k G z θ * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ, (∫ z in Work.Spaces.Iz, zc φ k z * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
            + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ)) * Work.FTS.EllipticEst.thEta θ := by
    rw [Work.FTS.EllipticEst.ThetaU.fubini_w_thEta (F := ibpF2 φ k G) hδ hF₂c hF₂0 hF₂b]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    simp only [ibpF2]; ring
  have hzabB := zouter_abs_le hδ hF₂c hF₂0 hM₂b
  have hInnerDTb : ∀ z, MeasureTheory.Integrable (ibp_tdd G z)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) →
      MeasureTheory.Integrable (ibp_th G z) (MeasureTheory.volume.restrict Work.Spaces.Iθ) →
      MeasureTheory.Integrable (ibp_tt G z) (MeasureTheory.volume.restrict Work.Spaces.Iθ) →
      (∫ θ in Work.Spaces.Iθ, ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
          + 9 * (Work.Spaces.Dz G z θ) ^ 2
          + (1 / 2) * (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2)
          * Work.FTS.EllipticEst.thEta θ)
        = ((∫ θ in Work.Spaces.Iθ, ibp_tdd G z θ)
            + 9 * (∫ θ in Work.Spaces.Iθ, ibp_th G z θ))
          + (1 / 2) * (∫ θ in Work.Spaces.Iθ, ibp_tt G z θ) := by
    intro z hDD hD hT
    have hlin : (∫ θ in Work.Spaces.Iθ, ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
          + 9 * (Work.Spaces.Dz G z θ) ^ 2
          + (1 / 2) * (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2)
          * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ, (ibp_tdd G z + (ibp_td9 G z + ibp_tt2 G z)) θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [Pi.add_apply, ibp_tdd, ibp_td9, ibp_tt2, ibp_th, ibp_tt]; ring
    rw [hlin, ibp_int_add3 (a := ibp_tdd G z) (b := ibp_td9 G z) (c := ibp_tt2 G z)
      hDD (hD.const_mul 9) (hT.const_mul (1 / 2))]
    have h9 : (∫ θ in Work.Spaces.Iθ, ibp_td9 G z θ)
        = 9 * (∫ θ in Work.Spaces.Iθ, ibp_th G z θ) :=
      MeasureTheory.integral_const_mul 9 (ibp_th G z)
    have h2 : (∫ θ in Work.Spaces.Iθ, ibp_tt2 G z θ)
        = (1 / 2) * (∫ θ in Work.Spaces.Iθ, ibp_tt G z θ) :=
      MeasureTheory.integral_const_mul (1 / 2) (ibp_tt G z)
    rw [h9, h2]
    ring
  have hIntDTb : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
        + 9 * (Work.Spaces.Dz G z θ) ^ 2
        + (1 / 2) * (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2)
        * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hIntDD, hIntD, hIntT] with z hDD hD hT
    refine (((hDD.add (hD.const_mul 9)).add (hT.const_mul (1 / 2)))).congr ?_
    filter_upwards with θ
    simp only [Pi.add_apply, ibp_tdd, ibp_td9, ibp_tt2, ibp_th, ibp_tt]
    ring
  have hNegB : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2
      * ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
        + 9 * (Work.Spaces.Dz G z θ) ^ 2
        + (1 / 2) * (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2)
        * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine (hdd'.add ((hd'.const_mul 9).add (ht'.const_mul (1 / 2)))).congr ?_
    filter_upwards [hIntDD, hIntD, hIntT] with z hDD hD hT
    simp only [Pi.add_apply, ibp_zdd, ibp_zh, ibp_zt]
    rw [hInnerDTb z hDD hD hT]
    ring
  have hFinB : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
          + 9 * (Work.Spaces.Dz G z θ) ^ 2
          + (1 / 2) * (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2)
          * Work.FTS.EllipticEst.thEta θ)
      = Work.FTS.EllipticEst.ddInt G + 9 * Work.FTS.EllipticEst.dInt G
        + (1 / 2) * Work.FTS.EllipticEst.ttInt G := by
    have step1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
            + 9 * (Work.Spaces.Dz G z θ) ^ 2
            + (1 / 2) * (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2)
            * Work.FTS.EllipticEst.thEta θ)
        = ∫ z in Work.Spaces.Iz, (ibpKB1 G + (ibpKB2 G + ibpKB3 G)) z := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hIntDD, hIntD, hIntT] with z hDD hD hT
      simp only [Pi.add_apply, ibpKB1, ibpKB2, ibpKB3, ibp_zdd, ibp_zh, ibp_zt]
      rw [hInnerDTb z hDD hD hT]
      ring
    have step2 : (∫ z in Work.Spaces.Iz, (ibpKB1 G + (ibpKB2 G + ibpKB3 G)) z)
        = (∫ z in Work.Spaces.Iz, ibpKB1 G z)
          + (∫ z in Work.Spaces.Iz, (ibpKB2 G + ibpKB3 G) z) :=
      ibp_intz_add2 (A := ibpKB1 G) (B := ibpKB2 G + ibpKB3 G) hdd'
        ((hd'.const_mul 9).add (ht'.const_mul (1 / 2)))
    have step3 : (∫ z in Work.Spaces.Iz, (ibpKB2 G + ibpKB3 G) z)
        = (∫ z in Work.Spaces.Iz, ibpKB2 G z) + (∫ z in Work.Spaces.Iz, ibpKB3 G z) :=
      ibp_intz_add2 (A := ibpKB2 G) (B := ibpKB3 G) (hd'.const_mul 9)
        (ht'.const_mul (1 / 2))
    have step4 : (∫ z in Work.Spaces.Iz, ibpKB2 G z)
        = 9 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
      MeasureTheory.integral_const_mul 9 (ibp_zh G)
    have step5 : (∫ z in Work.Spaces.Iz, ibpKB3 G z)
        = (1 / 2) * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) :=
      MeasureTheory.integral_const_mul (1 / 2) (ibp_zt G)
    have hun : (∫ z in Work.Spaces.Iz, ibpKB1 G z) = ∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [ibpKB1, ibp_zdd, ibp_tdd]
    rw [step1, step2, step3, step4, step5, hun, ← ddInt_eq G, ← dInt_eq G, ← ttInt_eq G]
    ring
  have hb : (∫ θ in Work.Spaces.Iθ,
        (∫ z in Work.Spaces.Iz, (zc φ k z) * (Work.Spaces.w z) ^ 2
          * (Work.Spaces.Dz (Work.Spaces.Dz G) z θ
            + Work.FTS.EllipticEst.ThetaU.bcoef z * (Work.Spaces.Dz G z θ))
          * (Work.Spaces.pth (Work.Spaces.pth G) z θ))
        * Work.FTS.EllipticEst.thEta θ)
      ≤ Work.FTS.EllipticEst.ddInt G + 9 * Work.FTS.EllipticEst.dInt G
        + (1 / 2) * Work.FTS.EllipticEst.ttInt G := by
    rw [← hB_split]
    refine le_trans (le_trans (le_abs_self _) hzabB) ?_
    refine le_trans ?_ (le_of_eq hFinB)
    refine MeasureTheory.integral_mono_of_nonneg ?_ hNegB ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact mul_nonneg (sq_nonneg _)
        (MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (abs_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))
    · filter_upwards [hIntDTb, MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hIT hz
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine MeasureTheory.integral_mono_of_nonneg ?_ hIT ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_nonneg (abs_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_le_mul_of_nonneg_right (ibp_abs_F2_le hk2 hφK hz θ)
          (Work.FTS.EllipticEst.thEta_nonneg hθ)
  exact ⟨ha, hb, hc⟩

end Work.FTS.EllipticEst.Alpha4
