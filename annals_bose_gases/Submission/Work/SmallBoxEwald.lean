import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Commons.Analysis.Integral.integral_Ioi_four_pi_rpow
import Submission.Commons.Analysis.Integral.integral_heat_coulomb_three
import Submission.Work.SmallBoxBoxGreen
import Submission.Work.SmallBoxSharpMass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-270 — the Ewald splitting of the box-Neumann Green deviation

`SmallBoxBoxGreen.boxGreen3Tail_le` closes the LARGE-`t` half of the kernel
deviation estimate required by the D1 sharp-mass step
(`SmallBoxSharpMass.sharpMass_le_of_kernel_dev`).  This module closes the
SMALL-`t` half:

    `|∫_0^{s²}(p_N^{(3)}(t,x,y) − K_t(x,y))dt| ≤ C/δ`

on the `δ`-inner region `|x_j|, |y_j| ≤ s/2 − δ`, and assembles the two halves
into the deviation bound

    `|boxGreenDev s x y| ≤ C/δ`,

where `boxGreenDev s x y` is `∫_0^{s²}(p_N − K) − ∫_{s²}^∞ K − s⁻¹ +
∫_{s²}^∞(p_N − s^{-3})`, which for `x ≠ y` is the deviation of the box
Neumann Green function `G_s(x,y)` from the free Newtonian kernel
`(4π‖x−y‖)⁻¹` (see the module docstring of `SmallBoxSharpMass`).

The engine is the CUT theta sum `neumann_image_gap_le`: on the `δ`-inner
region every displacement in the 1-D Neumann image representation is at least
`2δ`, and the lattice spacing `2s` controls the count of near points, so the
whole image-sum gap is `O(e^{−δ²/t})`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Submission
open _root_.BoseGases
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary geometric input -/

/-- `exp(−1) < 1`. -/
private lemma exp_neg_one_lt_one : Real.exp (-1 : ℝ) < 1 := by
  rw [Real.exp_lt_one_iff]; norm_num

/-- the geometric series with ratio `exp(−1)`. -/
private lemma summable_geom_exp_neg_one :
    Summable (fun n : ℕ => (Real.exp (-1 : ℝ)) ^ n) :=
  summable_geometric_of_lt_one (Real.exp_pos (-1 : ℝ)).le exp_neg_one_lt_one

private lemma tsum_geom_exp_neg_one :
    (∑' n : ℕ, (Real.exp (-1 : ℝ)) ^ n) = (1 - Real.exp (-1 : ℝ))⁻¹ :=
  tsum_geometric_of_lt_one (Real.exp_pos (-1 : ℝ)).le exp_neg_one_lt_one

private lemma one_sub_exp_neg_one_pos : (0 : ℝ) < 1 - Real.exp (-1 : ℝ) := by
  linarith [exp_neg_one_lt_one]

private lemma inv_one_sub_exp_neg_one_lt_two :
    (1 - Real.exp (-1 : ℝ))⁻¹ < 2 := by
  have hlt : Real.exp (-1 : ℝ) < 1 / 2 := by
    have h2 : Real.exp (-1 : ℝ) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    rw [h2]
    have := (inv_lt_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr Real.exp_one_gt_two
    simpa using this
  have hpos : (0 : ℝ) < 1 - Real.exp (-1 : ℝ) := by linarith
  rw [inv_lt_comm₀ hpos (by norm_num : (0 : ℝ) < 2)]
  have : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [this]
  linarith

/-- the two-sided elementary shift inequality for Gaussians:
`exp(−a(y+c)²) ≤ exp(a c²)·exp(−(a/2) y²)`. -/
private lemma exp_neg_sq_shift_le' {a c y : ℝ} (ha : 0 < a) :
    Real.exp (-(a * (y + c) ^ 2)) ≤ Real.exp (a * c ^ 2) * Real.exp (-(a / 2 * y ^ 2)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (y + 2 * c), ha]

/-! ## 2. The cut Gaussian bounds -/

/-- `exp(-(n:ℝ)) = (exp(-1))^n`. -/
private lemma exp_neg_nat_eq_pow (n : ℕ) :
    Real.exp (-(n : ℝ)) = (Real.exp (-1 : ℝ)) ^ n := by
  rw [show (-(n : ℝ)) = (n : ℝ) * (-1) by ring, Real.exp_nat_mul]

/-- **Type I numeric core** (denominators cleared): if `s(2n+1) + 2δ ≤ d` and
`t ≤ s²` then `4δ² + 4tn ≤ d²`. -/
private lemma cut_core_I {s t δ d : ℝ} (ht : 0 < t) (hs : 0 < s) (hδ : 0 < δ)
    (hδs : 2 * δ ≤ s) (hts : t ≤ s ^ 2) (n : ℕ)
    (hd : s * (2 * (n : ℝ) + 1) + 2 * δ ≤ d) :
    4 * δ ^ 2 + 4 * t * (n : ℝ) ≤ d ^ 2 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc0 : 0 ≤ s * (2 * (n : ℝ) + 1) + 2 * δ := by positivity
  have hsq : (s * (2 * (n : ℝ) + 1) + 2 * δ) ^ 2 ≤ d ^ 2 :=
    pow_le_pow_left₀ hc0 hd 2
  have he : (s * (2 * (n : ℝ) + 1) + 2 * δ) ^ 2
      = s ^ 2 * (2 * (n : ℝ) + 1) ^ 2 + 4 * δ ^ 2 + 4 * δ * s * (2 * (n : ℝ) + 1) := by ring
  rw [he] at hsq
  have hpos : 0 ≤ 4 * δ * s * (2 * (n : ℝ) + 1) := by positivity
  have h4n : 4 * t * (n : ℝ) ≤ s ^ 2 * (2 * (n : ℝ) + 1) ^ 2 := by
    have h1 : 4 * (n : ℝ) ≤ (2 * (n : ℝ) + 1) ^ 2 := by nlinarith [hn]
    have h2 : t * (4 * (n : ℝ)) ≤ s ^ 2 * (4 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hts (by positivity)
    have h3 : s ^ 2 * (4 * (n : ℝ)) ≤ s ^ 2 * (2 * (n : ℝ) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    calc 4 * t * (n : ℝ) = t * (4 * (n : ℝ)) := by ring
      _ ≤ s ^ 2 * (4 * (n : ℝ)) := h2
      _ ≤ s ^ 2 * (2 * (n : ℝ) + 1) ^ 2 := h3
  linarith [hsq, h4n, hpos]

/-- **Type II numeric core** (denominators cleared): if `2δ + 2sn ≤ d` and
`t ≤ s²` then `4δ² + 4tn ≤ d²`. -/
private lemma cut_core_II {s t δ d : ℝ} (ht : 0 < t) (hs : 0 < s) (hδ : 0 < δ)
    (hts : t ≤ s ^ 2) (n : ℕ)
    (hd : 2 * δ + 2 * s * (n : ℝ) ≤ d) :
    4 * δ ^ 2 + 4 * t * (n : ℝ) ≤ d ^ 2 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc0 : 0 ≤ 2 * δ + 2 * s * (n : ℝ) := by positivity
  have hsq : (2 * δ + 2 * s * (n : ℝ)) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hc0 hd 2
  have he : (2 * δ + 2 * s * (n : ℝ)) ^ 2
      = 4 * δ ^ 2 + 4 * s ^ 2 * (n : ℝ) ^ 2 + 8 * δ * s * (n : ℝ) := by ring
  rw [he] at hsq
  have hpos : 0 ≤ 8 * δ * s * (n : ℝ) := by positivity
  have h4n : 4 * t * (n : ℝ) ≤ 4 * s ^ 2 * (n : ℝ) ^ 2 := by
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
        nlinarith
    have h2 : t * (n : ℝ) ≤ s ^ 2 * (n : ℝ) := mul_le_mul_of_nonneg_right hts hn
    calc 4 * t * (n : ℝ) = 4 * (t * (n : ℝ)) := by ring
      _ ≤ 4 * (s ^ 2 * (n : ℝ)) := by linarith
      _ ≤ 4 * (s ^ 2 * (n : ℝ) ^ 2) := by
          have : s ^ 2 * (n : ℝ) ≤ s ^ 2 * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
          linarith
      _ = 4 * s ^ 2 * (n : ℝ) ^ 2 := by ring
  linarith [hsq, h4n, hpos]

/-- **Type I cut bound**: if the displacement `d` satisfies
`s(2n+1) + 2δ ≤ |d|` then `exp(-d²/(4t)) ≤ exp(-δ²/t)·exp(-1)^n`. -/
private lemma exp_le_geom_typeI {s t δ d : ℝ} (ht : 0 < t) (hs : 0 < s) (hδ : 0 < δ)
    (hδs : 2 * δ ≤ s) (hts : t ≤ s ^ 2) (n : ℕ)
    (hd : s * (2 * (n : ℝ) + 1) + 2 * δ ≤ |d|) :
    Real.exp (-(d ^ 2) / (4 * t)) ≤ Real.exp (-(δ ^ 2) / t) * (Real.exp (-1 : ℝ)) ^ n := by
  have hcore : 4 * δ ^ 2 + 4 * t * (n : ℝ) ≤ d ^ 2 := by
    rw [← sq_abs d]
    exact cut_core_I ht hs hδ hδs hts n hd
  have hmain : δ ^ 2 / t + (n : ℝ) ≤ d ^ 2 / (4 * t) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * t)]
    rw [show (δ ^ 2 / t + (n : ℝ)) * (4 * t) = 4 * δ ^ 2 + 4 * t * (n : ℝ) by
      field_simp]
    exact hcore
  have h1 : -(d ^ 2) / (4 * t) ≤ -(δ ^ 2) / t + -(n : ℝ) := by
    rw [show -(d ^ 2) / (4 * t) = -(d ^ 2 / (4 * t)) by ring,
        show -(δ ^ 2) / t = -(δ ^ 2 / t) by ring]
    linarith
  calc Real.exp (-(d ^ 2) / (4 * t)) ≤ Real.exp (-(δ ^ 2) / t + -(n : ℝ)) :=
        Real.exp_le_exp.mpr h1
    _ = Real.exp (-(δ ^ 2) / t) * Real.exp (-(n : ℝ)) := Real.exp_add _ _
    _ = Real.exp (-(δ ^ 2) / t) * (Real.exp (-1 : ℝ)) ^ n := by rw [exp_neg_nat_eq_pow]

/-- **Type II cut bound**: if the displacement satisfies `2δ + 2sn ≤ |d|` then
`exp(-d²/(4t)) ≤ exp(-δ²/t)·exp(-1)^n`. -/
private lemma exp_le_geom_typeII {s t δ d : ℝ} (ht : 0 < t) (hs : 0 < s) (hδ : 0 < δ)
    (hts : t ≤ s ^ 2) (n : ℕ)
    (hd : 2 * δ + 2 * s * (n : ℝ) ≤ |d|) :
    Real.exp (-(d ^ 2) / (4 * t)) ≤ Real.exp (-(δ ^ 2) / t) * (Real.exp (-1 : ℝ)) ^ n := by
  have hcore : 4 * δ ^ 2 + 4 * t * (n : ℝ) ≤ d ^ 2 := by
    rw [← sq_abs d]
    exact cut_core_II ht hs hδ hts n hd
  have hmain : δ ^ 2 / t + (n : ℝ) ≤ d ^ 2 / (4 * t) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * t)]
    rw [show (δ ^ 2 / t + (n : ℝ)) * (4 * t) = 4 * δ ^ 2 + 4 * t * (n : ℝ) by
      field_simp]
    exact hcore
  have h1 : -(d ^ 2) / (4 * t) ≤ -(δ ^ 2) / t + -(n : ℝ) := by
    rw [show -(d ^ 2) / (4 * t) = -(d ^ 2 / (4 * t)) by ring,
        show -(δ ^ 2) / t = -(δ ^ 2 / t) by ring]
    linarith
  calc Real.exp (-(d ^ 2) / (4 * t)) ≤ Real.exp (-(δ ^ 2) / t + -(n : ℝ)) :=
        Real.exp_le_exp.mpr h1
    _ = Real.exp (-(δ ^ 2) / t) * Real.exp (-(n : ℝ)) := Real.exp_add _ _
    _ = Real.exp (-(δ ^ 2) / t) * (Real.exp (-1 : ℝ)) ^ n := by rw [exp_neg_nat_eq_pow]

/-- the absolute-value displacement estimate for the difference family. -/
private lemma abs_shift_ge {s δ x : ℝ} (hs : 0 < s) (n : ℕ) (hx : |x| ≤ s - 2 * δ) :
    s * (2 * (n : ℝ) + 1) + 2 * δ ≤ |x + 2 * s * ((n : ℝ) + 1)| := by
  have h1 : 2 * s * ((n : ℝ) + 1) - |x| ≤ |x + 2 * s * ((n : ℝ) + 1)| := by
    have h := abs_sub_abs_le_abs_sub (2 * s * ((n : ℝ) + 1)) (-x)
    rw [abs_neg] at h
    have h2 : |2 * s * ((n : ℝ) + 1)| = 2 * s * ((n : ℝ) + 1) :=
      abs_of_nonneg (by positivity)
    rw [h2] at h
    have h3 : 2 * s * ((n : ℝ) + 1) - (-x) = x + 2 * s * ((n : ℝ) + 1) := by ring
    rwa [h3] at h
  have h4 : s * (2 * (n : ℝ) + 1) + 2 * δ = 2 * s * ((n : ℝ) + 1) - (s - 2 * δ) := by ring
  calc s * (2 * (n : ℝ) + 1) + 2 * δ = 2 * s * ((n : ℝ) + 1) - (s - 2 * δ) := h4
    _ ≤ 2 * s * ((n : ℝ) + 1) - |x| := by linarith [hx]
    _ ≤ |x + 2 * s * ((n : ℝ) + 1)| := h1

/-! ## 3. Absolute-value displacement estimates -/

/-- displacement estimate for the reflection family (positive displacement). -/
private lemma abs_shift_reflect_pos {s δ W : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    (hW : 2 * δ ≤ W) (n : ℕ) :
    2 * δ + 2 * s * (n : ℝ) ≤ |W + 2 * s * (n : ℝ)| := by
  rw [abs_of_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) n])]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- displacement estimate for the reflection family (negative displacement). -/
private lemma abs_shift_reflect_neg {s δ W : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ)
    (hW : W ≤ -2 * δ) (n : ℕ) :
    s * (2 * (n : ℝ) + 1) + 2 * δ ≤ |W - 2 * s * ((n : ℝ) + 1)| := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : W - 2 * s * ((n : ℝ) + 1) ≤ 0 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  rw [abs_of_nonpos h1]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- displacement estimate for the difference family (minus sign). -/
private lemma abs_shift_ge_neg {s δ x : ℝ} (hs : 0 < s) (n : ℕ) (hx : |x| ≤ s - 2 * δ) :
    s * (2 * (n : ℝ) + 1) + 2 * δ ≤ |x - 2 * s * ((n : ℝ) + 1)| := by
  have h1 : 2 * s * ((n : ℝ) + 1) - |x| ≤ |x - 2 * s * ((n : ℝ) + 1)| := by
    have h := abs_sub_abs_le_abs_sub (2 * s * ((n : ℝ) + 1)) x
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * s * ((n : ℝ) + 1))] at h
    rw [show 2 * s * ((n : ℝ) + 1) - x = -(x - 2 * s * ((n : ℝ) + 1)) by ring, abs_neg] at h
    exact h
  have h4 : s * (2 * (n : ℝ) + 1) + 2 * δ = 2 * s * ((n : ℝ) + 1) - (s - 2 * δ) := by ring
  calc s * (2 * (n : ℝ) + 1) + 2 * δ = 2 * s * ((n : ℝ) + 1) - (s - 2 * δ) := h4
    _ ≤ 2 * s * ((n : ℝ) + 1) - |x| := by linarith [hx]
    _ ≤ |x - 2 * s * ((n : ℝ) + 1)| := h1

/-! ## 4. Summability of the shifted Gaussian families -/

private lemma summable_exp_neg_sq_shift_int {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (w : ℝ) :
    Summable (fun m : ℤ => Real.exp (-((w + 2 * s * (m : ℝ)) ^ 2) / (4 * t))) := by
  have hc : 0 < s ^ 2 / (2 * t) := by positivity
  have hg : Summable (fun m : ℤ => Real.exp (w ^ 2 / (4 * t))
      * Real.exp (-(s ^ 2 / (2 * t)) * (m : ℝ) ^ 2)) :=
    (Commons.Analysis.Fourier.summable_exp_neg_mul_sq_int hc).mul_left _
  refine Summable.of_nonneg_of_le (fun m => (Real.exp_pos _).le) (fun m => ?_) hg
  have hsne : s ≠ 0 := ne_of_gt hs
  have htne : t ≠ 0 := ne_of_gt ht
  have hpt : ((w + 2 * s * (m : ℝ)) ^ 2) / (4 * t)
      = (s ^ 2 / t) * ((m : ℝ) + w / (2 * s)) ^ 2 := by
    field_simp
    ring
  rw [show -((w + 2 * s * (m : ℝ)) ^ 2) / (4 * t)
        = -(((w + 2 * s * (m : ℝ)) ^ 2) / (4 * t)) by ring, hpt]
  have h := exp_neg_sq_shift_le' (a := s ^ 2 / t) (c := w / (2 * s)) (y := (m : ℝ))
    (by positivity)
  refine le_trans h (le_of_eq ?_)
  have h1 : s ^ 2 / t * (w / (2 * s)) ^ 2 = w ^ 2 / (4 * t) := by
    field_simp
    ring
  have h2 : s ^ 2 / t / 2 * (m : ℝ) ^ 2 = s ^ 2 / (2 * t) * (m : ℝ) ^ 2 := by ring
  simp only [h1, h2, neg_mul]

/-! ## 5. The cut image-sum gap -/

/-- **The cut image-sum gap.**  On the `δ`-inner region, the 1-D Neumann
image representation has, apart from the `m = 0` term of the difference
family, only exponentially small contributions:

`Σ_{m≠0} e^{−(u−v+2sm)²/4t} + Σ_m e^{−(u+v−s+2sm)²/4t} ≤ 12 e^{−δ²/t}`. -/
private lemma neumann_image_gap_le {s t δ u v : ℝ} (hs : 0 < s) (ht : 0 < t) (hδ : 0 < δ)
    (hδs : 2 * δ ≤ s) (hts : t ≤ s ^ 2)
    (hu : |u| ≤ s / 2 - δ) (hv : |v| ≤ s / 2 - δ) :
    (∑' m : ℤ, (Real.exp (-((u - v + 2 * s * (m : ℝ)) ^ 2) / (4 * t))
          + Real.exp (-((u + v - s + 2 * s * (m : ℝ)) ^ 2) / (4 * t))))
        - Real.exp (-((u - v) ^ 2) / (4 * t))
      ≤ 12 * Real.exp (-(δ ^ 2) / t) := by
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  have huv : |u - v| ≤ s - 2 * δ := by
    rw [abs_le]; constructor <;> nlinarith [hu'.1, hu'.2, hv'.1, hv'.2]
  have hWlo : 2 * δ ≤ u + v + s := by nlinarith [hu'.1, hv'.1]
  have hWhi : u + v - s ≤ -2 * δ := by nlinarith [hu'.2, hv'.2]
  set A : ℤ → ℝ := fun m => Real.exp (-((u - v + 2 * s * (m : ℝ)) ^ 2) / (4 * t)) with hA
  set B : ℤ → ℝ := fun m => Real.exp (-((u + v - s + 2 * s * (m : ℝ)) ^ 2) / (4 * t)) with hB
  have hAsum : Summable A := by rw [hA]; exact summable_exp_neg_sq_shift_int hs ht (u - v)
  have hBsum : Summable B := by rw [hB]; exact summable_exp_neg_sq_shift_int hs ht (u + v - s)
  set q : ℝ := Real.exp (-1 : ℝ) with hq
  set c : ℝ := Real.exp (-(δ ^ 2) / t) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq, Real.exp_lt_one_iff]; norm_num
  have hgsum : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hq_tsum : (∑' n : ℕ, q ^ n) = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1
  have keyApos : ∀ n : ℕ, A ((n : ℤ) + 1) ≤ c * q ^ n := by
    intro n
    have hcoe : ((((n : ℤ) + 1 : ℤ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hmain := exp_le_geom_typeI ht hs hδ hδs hts n (abs_shift_ge hs n huv)
    rw [hA]
    simp only [hcoe, hc, hq]
    exact hmain
  have keyAneg : ∀ n : ℕ, A (-((n : ℤ) + 1)) ≤ c * q ^ n := by
    intro n
    have hcoe : (((-((n : ℤ) + 1) : ℤ)) : ℝ) = -((n : ℝ) + 1) := by push_cast; ring
    have hd : s * (2 * (n : ℝ) + 1) + 2 * δ ≤ |u - v + 2 * s * (-((n : ℝ) + 1))| := by
      rw [show u - v + 2 * s * (-((n : ℝ) + 1)) = u - v - 2 * s * ((n : ℝ) + 1) by ring]
      exact abs_shift_ge_neg hs n huv
    have hmain := exp_le_geom_typeI ht hs hδ hδs hts n hd
    rw [hA]
    simp only [hcoe, hc, hq]
    exact hmain
  have keyBpos : ∀ n : ℕ, B ((n : ℤ) + 1) ≤ c * q ^ n := by
    intro n
    have hcoe : ((((n : ℤ) + 1 : ℤ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hd : 2 * δ + 2 * s * (n : ℝ) ≤ |u + v - s + 2 * s * ((n : ℝ) + 1)| := by
      rw [show u + v - s + 2 * s * ((n : ℝ) + 1) = (u + v + s) + 2 * s * (n : ℝ) by ring]
      exact abs_shift_reflect_pos hs.le hδ.le hWlo n
    have hmain := exp_le_geom_typeII ht hs hδ hts n hd
    rw [hB]
    simp only [hcoe, hc, hq]
    exact hmain
  have keyBneg : ∀ n : ℕ, B (-((n : ℤ) + 1)) ≤ c * q ^ n := by
    intro n
    have hcoe : (((-((n : ℤ) + 1) : ℤ)) : ℝ) = -((n : ℝ) + 1) := by push_cast; ring
    have hd : s * (2 * (n : ℝ) + 1) + 2 * δ ≤ |u + v - s + 2 * s * (-((n : ℝ) + 1))| := by
      rw [show u + v - s + 2 * s * (-((n : ℝ) + 1)) = (u + v - s) - 2 * s * ((n : ℝ) + 1) by
        ring]
      exact abs_shift_reflect_neg hs hδ.le hWhi n
    have hmain := exp_le_geom_typeI ht hs hδ hδs hts n hd
    rw [hB]
    simp only [hcoe, hc, hq]
    exact hmain
  have hB0 : B 0 ≤ c := by
    have hd : 2 * δ ≤ |u + v - s| := by
      rw [abs_of_nonpos (by linarith : u + v - s ≤ 0)]
      linarith
    have h4 : (2 * δ) ^ 2 ≤ (u + v - s) ^ 2 := by
      have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 * δ by positivity) hd 2
      rwa [sq_abs] at h
    have hexp : -((u + v - s) ^ 2) / (4 * t) ≤ -(δ ^ 2) / t := by
      rw [show -((u + v - s) ^ 2) / (4 * t) = -(((u + v - s) ^ 2) / (4 * t)) by ring,
          show -(δ ^ 2) / t = -(δ ^ 2 / t) by ring, neg_le_neg_iff,
          le_div_iff₀ (by positivity : (0 : ℝ) < 4 * t),
          show δ ^ 2 / t * (4 * t) = 4 * δ ^ 2 by field_simp]
      linarith
    rw [hB]
    simp only [Int.cast_zero, mul_zero, add_zero, hc]
    exact Real.exp_le_exp.mpr hexp
  have hbApos : (∑' n : ℕ, A ((n : ℤ) + 1)) ≤ c * (1 - q)⁻¹ := by
    have hsum : Summable (fun n : ℕ => A ((n : ℤ) + 1)) :=
      Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) keyApos (hgsum.mul_left c)
    calc (∑' n : ℕ, A ((n : ℤ) + 1)) ≤ ∑' n : ℕ, c * q ^ n :=
          Summable.tsum_le_tsum keyApos hsum (hgsum.mul_left c)
      _ = c * (∑' n : ℕ, q ^ n) := tsum_mul_left
      _ = c * (1 - q)⁻¹ := by rw [hq_tsum]
  have hbAneg : (∑' n : ℕ, A (-((n : ℤ) + 1))) ≤ c * (1 - q)⁻¹ := by
    have hsum : Summable (fun n : ℕ => A (-((n : ℤ) + 1))) :=
      Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) keyAneg (hgsum.mul_left c)
    calc (∑' n : ℕ, A (-((n : ℤ) + 1))) ≤ ∑' n : ℕ, c * q ^ n :=
          Summable.tsum_le_tsum keyAneg hsum (hgsum.mul_left c)
      _ = c * (∑' n : ℕ, q ^ n) := tsum_mul_left
      _ = c * (1 - q)⁻¹ := by rw [hq_tsum]
  have hbBpos : (∑' n : ℕ, B ((n : ℤ) + 1)) ≤ c * (1 - q)⁻¹ := by
    have hsum : Summable (fun n : ℕ => B ((n : ℤ) + 1)) :=
      Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) keyBpos (hgsum.mul_left c)
    calc (∑' n : ℕ, B ((n : ℤ) + 1)) ≤ ∑' n : ℕ, c * q ^ n :=
          Summable.tsum_le_tsum keyBpos hsum (hgsum.mul_left c)
      _ = c * (∑' n : ℕ, q ^ n) := tsum_mul_left
      _ = c * (1 - q)⁻¹ := by rw [hq_tsum]
  have hbBneg : (∑' n : ℕ, B (-((n : ℤ) + 1))) ≤ c * (1 - q)⁻¹ := by
    have hsum : Summable (fun n : ℕ => B (-((n : ℤ) + 1))) :=
      Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) keyBneg (hgsum.mul_left c)
    calc (∑' n : ℕ, B (-((n : ℤ) + 1))) ≤ ∑' n : ℕ, c * q ^ n :=
          Summable.tsum_le_tsum keyBneg hsum (hgsum.mul_left c)
      _ = c * (∑' n : ℕ, q ^ n) := tsum_mul_left
      _ = c * (1 - q)⁻¹ := by rw [hq_tsum]
  have hAsplit : (∑' m : ℤ, A m)
      = A 0 + (∑' n : ℕ, A ((n : ℤ) + 1)) + (∑' n : ℕ, A (-((n : ℤ) + 1))) := by
    have hnat : Summable (fun n : ℕ => A (n : ℤ)) :=
      hAsum.comp_injective (fun a b h => by exact_mod_cast h)
    have hneg : Summable (fun n : ℕ => A (-((n : ℤ) + 1))) :=
      hAsum.comp_injective (fun a b h => by
        have h2 : ((a : ℤ) + 1) = ((b : ℤ) + 1) := neg_injective h
        omega)
    have hcong : (∑' n : ℕ, A (↑(n + 1) : ℤ)) = (∑' n : ℕ, A ((n : ℤ) + 1)) := by
      apply tsum_congr; intro n
      congr 1
    rw [tsum_of_nat_of_neg_add_one hnat hneg, hnat.tsum_eq_zero_add, hcong]
    ring
  have hBsplit : (∑' m : ℤ, B m)
      = B 0 + (∑' n : ℕ, B ((n : ℤ) + 1)) + (∑' n : ℕ, B (-((n : ℤ) + 1))) := by
    have hnat : Summable (fun n : ℕ => B (n : ℤ)) :=
      hBsum.comp_injective (fun a b h => by exact_mod_cast h)
    have hneg : Summable (fun n : ℕ => B (-((n : ℤ) + 1))) :=
      hBsum.comp_injective (fun a b h => by
        have h2 : ((a : ℤ) + 1) = ((b : ℤ) + 1) := neg_injective h
        omega)
    have hcong : (∑' n : ℕ, B (↑(n + 1) : ℤ)) = (∑' n : ℕ, B ((n : ℤ) + 1)) := by
      apply tsum_congr; intro n
      congr 1
    rw [tsum_of_nat_of_neg_add_one hnat hneg, hnat.tsum_eq_zero_add, hcong]
    ring
  have hAB : (∑' m : ℤ, (A m + B m)) = (∑' m : ℤ, A m) + (∑' m : ℤ, B m) :=
    Summable.tsum_add hAsum hBsum
  have hA0 : A 0 = Real.exp (-((u - v) ^ 2) / (4 * t)) := by
    rw [hA]; simp
  rw [hAB, hAsplit, hBsplit, ← hA0]
  have hb1 : (1 - q)⁻¹ < 2 := by rw [hq]; exact inv_one_sub_exp_neg_one_lt_two
  nlinarith [hbApos, hbAneg, hbBpos, hbBneg, hB0, hc0, hb1]

/-- nonnegativity of the cut image-sum gap (companion of
`neumann_image_gap_le`). -/
private lemma neumann_image_gap_nonneg {s t δ u v : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hδ : 0 < δ) (hδs : 2 * δ ≤ s) (hts : t ≤ s ^ 2)
    (hu : |u| ≤ s / 2 - δ) (hv : |v| ≤ s / 2 - δ) :
    0 ≤ (∑' m : ℤ, (Real.exp (-((u - v + 2 * s * (m : ℝ)) ^ 2) / (4 * t))
          + Real.exp (-((u + v - s + 2 * s * (m : ℝ)) ^ 2) / (4 * t))))
        - Real.exp (-((u - v) ^ 2) / (4 * t)) := by
  set A : ℤ → ℝ := fun m => Real.exp (-((u - v + 2 * s * (m : ℝ)) ^ 2) / (4 * t)) with hA
  set B : ℤ → ℝ := fun m => Real.exp (-((u + v - s + 2 * s * (m : ℝ)) ^ 2) / (4 * t)) with hB
  have hAsum : Summable A := by rw [hA]; exact summable_exp_neg_sq_shift_int hs ht (u - v)
  have hBsum : Summable B := by rw [hB]; exact summable_exp_neg_sq_shift_int hs ht (u + v - s)
  have hnat : Summable (fun n : ℕ => A (n : ℤ)) :=
    hAsum.comp_injective (fun a b h => by exact_mod_cast h)
  have hneg : Summable (fun n : ℕ => A (-((n : ℤ) + 1))) :=
    hAsum.comp_injective (fun a b h => by
      have h2 : ((a : ℤ) + 1) = ((b : ℤ) + 1) := neg_injective h
      omega)
  have hAsplit : (∑' m : ℤ, A m)
      = A 0 + (∑' n : ℕ, A ((n : ℤ) + 1)) + (∑' n : ℕ, A (-((n : ℤ) + 1))) := by
    have hcong : (∑' n : ℕ, A (↑(n + 1) : ℤ)) = (∑' n : ℕ, A ((n : ℤ) + 1)) := by
      apply tsum_congr; intro n; congr 1
    rw [tsum_of_nat_of_neg_add_one hnat hneg, hnat.tsum_eq_zero_add, hcong]
    ring
  have hA0 : A 0 = Real.exp (-((u - v) ^ 2) / (4 * t)) := by rw [hA]; simp
  have h1 : 0 ≤ (∑' n : ℕ, A ((n : ℤ) + 1)) := tsum_nonneg (fun n => (Real.exp_pos _).le)
  have h2 : 0 ≤ (∑' n : ℕ, A (-((n : ℤ) + 1))) := tsum_nonneg (fun n => (Real.exp_pos _).le)
  have h3 : 0 ≤ (∑' m : ℤ, B m) := tsum_nonneg (fun m => (Real.exp_pos _).le)
  rw [Summable.tsum_add hAsum hBsum, hAsplit, ← hA0]
  linarith

/-! ## 6. The 1-D Neumann heat kernel versus the free Gaussian -/

/-- **the 1-D image sum differs from the free Gaussian by
`O((4πt)^{-1/2}e^{−δ²/t})`** on the `δ`-inner region. -/
lemma neuHeat1_sub_free_le {s t δ u v : ℝ} (hs : 0 < s) (ht : 0 < t) (hδ : 0 < δ)
    (hδs : 2 * δ ≤ s) (hts : t ≤ s ^ 2)
    (hu : |u| ≤ s / 2 - δ) (hv : |v| ≤ s / 2 - δ) :
    |neuHeat1 s t u v - (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
        * Real.exp (-((u - v) ^ 2) / (4 * t))|
      ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * (12 * Real.exp (-(δ ^ 2) / t)) := by
  have hcpos : 0 < (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have himg : neuHeat1 s t u v = (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
      * (∑' m : ℤ, (Real.exp (-((u - v + 2 * s * (m : ℝ)) ^ 2) / (4 * t))
          + Real.exp (-((u + v - s + 2 * s * (m : ℝ)) ^ 2) / (4 * t)))) := by
    rw [neuHeat1_eq_image (s := s) (t := t) (u := u) (v := v) hs ht, tsum_mul_left]
  rw [himg, ← mul_sub, abs_mul, abs_of_pos hcpos,
      abs_of_nonneg (neumann_image_gap_nonneg hs ht hδ hδs hts hu hv)]
  nlinarith [neumann_image_gap_le hs ht hδ hδs hts hu hv, hcpos]

/-! ## 7. The free 3-D heat kernel and the product-expansion bound -/

/-- the free (Gaussian) 3-D heat kernel, in the product form adapted to the box -/
noncomputable def freeHeat3 (t : ℝ) (x y : ℝ³) : ℝ :=
  ∏ j : Fin 3, (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((x j - y j) ^ 2) / (4 * t))

/-- **product-difference bound for three factors**: if `b i = a i - d i` with
`|d i| ≤ m` and `|a i|, |b i| ≤ A` then `|∏a − ∏b| ≤ 3 m A²`. -/
private lemma abs_prod_three_sub_le {a b d : Fin 3 → ℝ}
    (hd : ∀ i, b i = a i - d i) {m A : ℝ} (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hmb : ∀ i, |d i| ≤ m) (ha : ∀ i, |a i| ≤ A) (hb : ∀ i, |b i| ≤ A) :
    |∏ i, a i - ∏ i, b i| ≤ 3 * m * A ^ 2 := by
  have h0 : b 0 = a 0 - d 0 := hd 0
  have h1 : b 1 = a 1 - d 1 := hd 1
  have h2 : b 2 = a 2 - d 2 := hd 2
  rw [Fin.prod_univ_three a, Fin.prod_univ_three b, h0, h1, h2]
  have he : a 0 * a 1 * a 2 - (a 0 - d 0) * (a 1 - d 1) * (a 2 - d 2)
      = d 0 * (a 1 * a 2) + (a 0 - d 0) * (d 1 * a 2) + (a 0 - d 0) * (a 1 - d 1) * d 2 := by
    ring
  rw [he]
  have hb0 : |a 0 - d 0| ≤ A := by rw [← h0]; exact hb 0
  have hb1 : |a 1 - d 1| ≤ A := by rw [← h1]; exact hb 1
  have hAA : |a 1| * |a 2| ≤ A * A := mul_le_mul (ha 1) (ha 2) (abs_nonneg _) hA
  have hAA' : |a 0 - d 0| * |a 1 - d 1| ≤ A * A :=
    mul_le_mul hb0 hb1 (abs_nonneg _) hA
  have e1 : |d 0 * (a 1 * a 2)| ≤ m * A ^ 2 := by
    rw [abs_mul, abs_mul]
    calc |d 0| * (|a 1| * |a 2|) ≤ m * (A * A) :=
          mul_le_mul (hmb 0) hAA (by positivity) hm
      _ = m * A ^ 2 := by ring
  have e2 : |(a 0 - d 0) * (d 1 * a 2)| ≤ m * A ^ 2 := by
    rw [abs_mul, abs_mul]
    have hdm : |d 1| * |a 2| ≤ m * A := mul_le_mul (hmb 1) (ha 2) (abs_nonneg _) hm
    calc |a 0 - d 0| * (|d 1| * |a 2|) ≤ A * (m * A) := mul_le_mul hb0 hdm (by positivity) hA
      _ = m * A ^ 2 := by ring
  have e3 : |(a 0 - d 0) * (a 1 - d 1) * d 2| ≤ m * A ^ 2 := by
    rw [show (a 0 - d 0) * (a 1 - d 1) * d 2 = ((a 0 - d 0) * (a 1 - d 1)) * d 2 by ring,
        abs_mul, abs_mul]
    calc (|a 0 - d 0| * |a 1 - d 1|) * |d 2| ≤ (A * A) * m :=
          mul_le_mul hAA' (hmb 2) (abs_nonneg _) (by positivity)
      _ = m * A ^ 2 := by ring
  have htri : |d 0 * (a 1 * a 2) + (a 0 - d 0) * (d 1 * a 2) + (a 0 - d 0) * (a 1 - d 1) * d 2|
      ≤ |d 0 * (a 1 * a 2)| + |(a 0 - d 0) * (d 1 * a 2)|
        + |(a 0 - d 0) * (a 1 - d 1) * d 2| := by
    have h := abs_add_le
      (d 0 * (a 1 * a 2) + (a 0 - d 0) * (d 1 * a 2))
      ((a 0 - d 0) * (a 1 - d 1) * d 2)
    have h2' := abs_add_le (d 0 * (a 1 * a 2)) ((a 0 - d 0) * (d 1 * a 2))
    rw [show d 0 * (a 1 * a 2) + (a 0 - d 0) * (d 1 * a 2) + (a 0 - d 0) * (a 1 - d 1) * d 2
        = (d 0 * (a 1 * a 2) + (a 0 - d 0) * (d 1 * a 2))
          + (a 0 - d 0) * (a 1 - d 1) * d 2 by ring]
    linarith
  have hfin : |d 0 * (a 1 * a 2)| + |(a 0 - d 0) * (d 1 * a 2)|
      + |(a 0 - d 0) * (a 1 - d 1) * d 2| ≤ 3 * m * A ^ 2 := by
    nlinarith [e1, e2, e3]
  linarith [htri, hfin]

/-- **the 3-D product expansion bound**: on the `δ`-inner region and for
`0 < t ≤ s²`, the box-Neumann heat kernel differs from the free heat kernel
by at most `7000 (4πt)^{-3/2} e^{−δ²/t}`. -/
lemma boxHeat3_sub_freeHeat3_le {s t δ : ℝ} (hs : 0 < s) (ht : 0 < t) (hδ : 0 < δ)
    (hδs : 2 * δ ≤ s) (hts : t ≤ s ^ 2) (x y : ℝ³)
    (hx : ∀ j, |x j| ≤ s / 2 - δ) (hy : ∀ j, |y j| ≤ s / 2 - δ) :
    |boxHeat3 s t x y - freeHeat3 t x y|
      ≤ 7000 * (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(δ ^ 2 / t)) := by
  have hcpos : 0 < (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hc0 : 0 ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := hcpos.le
  have he1 : Real.exp (-(δ ^ 2 / t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg δ) ht.le))
  have harg : ∀ i : Fin 3, -((x i - y i) ^ 2) / (4 * t) ≤ 0 := fun i =>
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  have hexp_le : ∀ i : Fin 3, Real.exp (-((x i - y i) ^ 2) / (4 * t)) ≤ 1 := fun i =>
    Real.exp_le_one_iff.mpr (harg i)
  have hb_c : ∀ i : Fin 3,
      |(4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((x i - y i) ^ 2) / (4 * t))|
        ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by
    intro i
    rw [abs_of_nonneg (by positivity)]
    nlinarith [hc0, hexp_le i]
  have hmb : ∀ i : Fin 3,
      |neuHeat1 s t (x i) (y i) - (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
        * Real.exp (-((x i - y i) ^ 2) / (4 * t))|
        ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * (12 * Real.exp (-(δ ^ 2 / t))) := by
    intro i
    have h := neuHeat1_sub_free_le hs ht hδ hδs hts (hx i) (hy i)
    rw [show -(δ ^ 2) / t = -(δ ^ 2 / t) by ring] at h
    exact h
  have ha : ∀ i : Fin 3, |neuHeat1 s t (x i) (y i)|
      ≤ 13 * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by
    intro i
    have h2 := hmb i
    have h3 : |neuHeat1 s t (x i) (y i)|
        ≤ |neuHeat1 s t (x i) (y i) - (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
            * Real.exp (-((x i - y i) ^ 2) / (4 * t))|
          + |(4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
            * Real.exp (-((x i - y i) ^ 2) / (4 * t))| := by
      have h := abs_add_le
        (neuHeat1 s t (x i) (y i) - (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
          * Real.exp (-((x i - y i) ^ 2) / (4 * t)))
        ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((x i - y i) ^ 2) / (4 * t)))
      rwa [sub_add_cancel] at h
    have h4 := hb_c i
    nlinarith [h2, h3, h4, hc0, he1]
  have hb13 : ∀ i : Fin 3,
      |(4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((x i - y i) ^ 2) / (4 * t))|
        ≤ 13 * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by
    intro i
    have := hb_c i
    nlinarith [this, hc0]
  have hmain := abs_prod_three_sub_le
    (a := fun i : Fin 3 => neuHeat1 s t (x i) (y i))
    (b := fun i : Fin 3 => (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
      * Real.exp (-((x i - y i) ^ 2) / (4 * t)))
    (d := fun i : Fin 3 => neuHeat1 s t (x i) (y i) - (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
      * Real.exp (-((x i - y i) ^ 2) / (4 * t)))
    (m := (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * (12 * Real.exp (-(δ ^ 2 / t))))
    (A := 13 * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)))
    (fun i => by ring) (by positivity) (by positivity) hmb ha hb13
  have hcube : ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ))) ^ 3
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 4 * Real.pi * t)]
    norm_num
  have hval : 3 * ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * (12 * Real.exp (-(δ ^ 2 / t))))
      * (13 * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))) ^ 2
      = 6084 * (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(δ ^ 2 / t)) := by
    rw [← hcube]; ring
  have hfin : |boxHeat3 s t x y - freeHeat3 t x y|
      ≤ 6084 * (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(δ ^ 2 / t)) := by
    rw [hval] at hmain
    exact hmain
  have hnn : 0 ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(δ ^ 2 / t)) := by
    positivity
  linarith [hfin, hnn]

/-! ## 8. Integrability of the heat majorants, and the small-`t` integral -/

private lemma integrableOn_heat_majorant {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(c / t)))
      (Set.Ioi 0) := by
  have hval := Commons.Analysis.Integral.integral_heat_exp_neg hc
  by_contra h
  rw [integral_undef h] at hval
  have hpos : 0 < 1 / (8 * Real.pi * Real.sqrt c) := by positivity
  linarith

private lemma integrableOn_four_pi_rpow_tail {t₀ : ℝ} (ht₀ : 0 < t₀) :
    IntegrableOn (fun t : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))) (Set.Ioi t₀) := by
  have hval := Commons.Analysis.Integral.integral_Ioi_four_pi_rpow ht₀
  by_contra h
  rw [integral_undef h] at hval
  have hpos : 0 < (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * 2 / Real.sqrt t₀ := by positivity
  linarith

/-- the small-`t` half of the box-Green deviation. -/
lemma integral_small_t_le {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδs : 2 * δ ≤ s)
    (x y : ℝ³) (hx : ∀ j, |x j| ≤ s / 2 - δ) (hy : ∀ j, |y j| ≤ s / 2 - δ) :
    |∫ t in Set.Ioc 0 (s ^ 2), (boxHeat3 s t x y - freeHeat3 t x y)|
      ≤ 7000 * (1 / (8 * Real.pi * δ)) := by
  have hc2 : 0 < δ ^ 2 := pow_pos hδ 2
  have hFint : IntegrableOn (fun t : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
      * Real.exp (-(δ ^ 2 / t))) (Set.Ioi 0) := integrableOn_heat_majorant hc2
  have hFval : (∫ t in Set.Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
      * Real.exp (-(δ ^ 2 / t))) = 1 / (8 * Real.pi * δ) := by
    rw [Commons.Analysis.Integral.integral_heat_exp_neg hc2, Real.sqrt_sq hδ.le]
  have hInt : IntegrableOn (fun t : ℝ => 7000 * ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
      * Real.exp (-(δ ^ 2 / t)))) (Set.Ioc 0 (s ^ 2)) :=
    (hFint.mono_set Set.Ioc_subset_Ioi_self).const_mul 7000
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) (s ^ 2))),
      ‖boxHeat3 s t x y - freeHeat3 t x y‖
        ≤ 7000 * ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(δ ^ 2 / t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    simpa only [mul_assoc] using boxHeat3_sub_freeHeat3_le hs ht.1 hδ hδs ht.2 x y hx hy
  have h := norm_integral_le_of_norm_le hInt hae
  rw [Real.norm_eq_abs] at h
  refine le_trans h ?_
  rw [MeasureTheory.integral_const_mul]
  have hFnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun t : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(δ ^ 2 / t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  have hle : (∫ t in Set.Ioc (0 : ℝ) (s ^ 2), (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
      * Real.exp (-(δ ^ 2 / t)))
      ≤ ∫ t in Set.Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
      * Real.exp (-(δ ^ 2 / t)) :=
    setIntegral_mono_set (s := Set.Ioc 0 (s ^ 2)) (t := Set.Ioi 0) hFint hFnn
      Set.Ioc_subset_Ioi_self.eventuallyLE
  calc 7000 * (∫ t in Set.Ioc (0 : ℝ) (s ^ 2), (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
        * Real.exp (-(δ ^ 2 / t)))
      ≤ 7000 * (∫ t in Set.Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
        * Real.exp (-(δ ^ 2 / t))) := mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = 7000 * (1 / (8 * Real.pi * δ)) := by rw [hFval]

/-! ## 9. The free heat kernel is dominated by the bare heat kernel -/

lemma freeHeat3_nonneg (t : ℝ) (ht : 0 < t) (x y : ℝ³) : 0 ≤ freeHeat3 t x y := by
  rw [freeHeat3]
  exact Finset.prod_nonneg fun j _ => by positivity

private lemma rpow_half_cube {t : ℝ} (ht : 0 ≤ t) :
    ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ))) ^ 3 = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 4 * Real.pi * t)]
  norm_num

lemma freeHeat3_le (t : ℝ) (ht : 0 < t) (x y : ℝ³) :
    freeHeat3 t x y ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by
  have hc : 0 ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) :=
    (Real.rpow_pos_of_pos (by positivity) _).le
  have hexp : ∀ j : Fin 3, Real.exp (-((x j - y j) ^ 2) / (4 * t)) ≤ 1 := fun j =>
    Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  calc freeHeat3 t x y ≤ ∏ _j : Fin 3, (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by
        rw [freeHeat3]
        exact Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => by
          have := hexp j
          nlinarith [hc])
    _ = ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ))) ^ 3 := by
        rw [Finset.prod_const]
        norm_num
    _ = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := rpow_half_cube ht.le

/-! ## 10. The assembled box-Green deviation -/

/-- **the deviation of the box Neumann Green function from the free
Newtonian kernel**, in the `t`-splitting form used by the Ewald estimate:

`boxGreenDev s x y = ∫_0^{s²}(p_N − K) − ∫_{s²}^∞ K − s⁻¹ + ∫_{s²}^∞(p_N − s^{-3})`.

For `x ≠ y` this equals `G_s(x,y) − (4π‖x−y‖)⁻¹`, where `G_s` is the Neumann
Green function of the box and `K_t = (4πt)^{-3/2}e^{−‖x−y‖²/4t}` the free
heat kernel (the three `x = y`-singular improper integrals are replaced by
manifestly convergent ones). -/
noncomputable def boxGreenDev (s : ℝ) (x y : ℝ³) : ℝ :=
  (∫ t in Set.Ioc (0 : ℝ) (s ^ 2), (boxHeat3 s t x y - freeHeat3 t x y))
    - (∫ t in Set.Ioi (s ^ 2), freeHeat3 t x y)
    - s⁻¹
    + (∫ t in Set.Ioi (s ^ 2), (boxHeat3 s t x y - (s ^ 3)⁻¹))

/-- `96 e^{−π²} ≤ 1`. -/
private lemma exp_neg_pi_sq_mul_le : 96 * Real.exp (-(Real.pi ^ 2)) ≤ 1 := by
  have hpi9 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
  have h1 : Real.exp (-(Real.pi ^ 2)) ≤ Real.exp (-9 : ℝ) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-9 : ℝ) = ((Real.exp 1) ^ 9)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h3 : (512 : ℝ) < (Real.exp 1) ^ 9 := by
    have h : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
    calc (512 : ℝ) = 2 ^ 9 := by norm_num
      _ < (Real.exp 1) ^ 9 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  have h4 : Real.exp (-9 : ℝ) ≤ (512 : ℝ)⁻¹ := by
    rw [h2]
    exact (inv_le_inv₀ (by positivity) (by norm_num : (0 : ℝ) < 512)).mpr h3.le
  nlinarith [h1, h4]

/-- the scaled decay `s⁻¹ ≤ 2/δ` from `2δ ≤ s`. -/
private lemma inv_s_le {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδs : 2 * δ ≤ s) :
    s⁻¹ ≤ 2 / δ := by
  have h2d : (0 : ℝ) < 2 * δ := by linarith
  have h5 : s⁻¹ ≤ (2 * δ)⁻¹ := (inv_le_inv₀ hs h2d).mpr hδs
  have h6 : (2 * δ)⁻¹ ≤ 2 / δ := by
    rw [mul_inv, div_eq_mul_inv]
    nlinarith [inv_pos.mpr hδ]
  linarith

private lemma four_pi_rpow_mul_two_le_half :
    (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * 2 ≤ 1 / 2 := by
  have hx1 : (1 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hle := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
  rw [Real.rpow_one] at hle
  have h2 : (4 : ℝ) ≤ (4 * Real.pi) ^ (3 / 2 : ℝ) := by nlinarith [hle, Real.pi_gt_three]
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 * Real.pi), inv_mul_eq_div,
    div_le_iff₀ (by positivity : (0 : ℝ) < (4 * Real.pi) ^ (3 / 2 : ℝ))]
  linarith [h2]

/-- **the box-Green kernel deviation bound** — the analytic input of the D1
sharp-mass step (`SmallBoxSharpMass.sharpMass_le_of_kernel_dev`).  On the
`δ`-inner region the box Neumann Green function deviates from
`(4π‖x−y‖)⁻¹` by at most `400/δ`. -/
theorem boxGreenDev_le {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδs : 2 * δ ≤ s)
    (x y : ℝ³) (hx : ∀ j, |x j| ≤ s / 2 - δ) (hy : ∀ j, |y j| ≤ s / 2 - δ) :
    |boxGreenDev s x y| ≤ 400 / δ := by
  have hs2 : 0 < s ^ 2 := pow_pos hs 2
  rw [boxGreenDev]
  set I1 : ℝ := ∫ t in Set.Ioc (0 : ℝ) (s ^ 2), (boxHeat3 s t x y - freeHeat3 t x y) with hI1
  set I2 : ℝ := ∫ t in Set.Ioi (s ^ 2), freeHeat3 t x y with hI2
  set I3 : ℝ := ∫ t in Set.Ioi (s ^ 2), (boxHeat3 s t x y - (s ^ 3)⁻¹) with hI3
  have hA : |I1| ≤ 300 / δ := by
    rw [hI1]
    refine le_trans (integral_small_t_le hs hδ hδs x y hx hy) ?_
    have h1 : 7000 / (8 * Real.pi) ≤ 300 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * Real.pi)]
      nlinarith [Real.pi_gt_three]
    calc 7000 * (1 / (8 * Real.pi * δ)) = (7000 / (8 * Real.pi)) * (1 / δ) := by ring
      _ ≤ 300 * (1 / δ) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 300 / δ := by ring
  have hB : |I2| ≤ 1 / δ := by
    rw [hI2]
    have hg : IntegrableOn (fun t : ℝ => (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))) (Set.Ioi (s ^ 2)) :=
      integrableOn_four_pi_rpow_tail hs2
    have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioi (s ^ 2))),
        ‖freeHeat3 t x y‖ ≤ (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := by
        have h : s ^ 2 < t := ht
        linarith [hs2, h]
      rw [Real.norm_eq_abs, abs_of_nonneg (freeHeat3_nonneg t ht0 x y)]
      exact freeHeat3_le t ht0 x y
    have hBt := norm_integral_le_of_norm_le hg hae
    rw [Real.norm_eq_abs] at hBt
    refine le_trans hBt ?_
    rw [Commons.Analysis.Integral.integral_Ioi_four_pi_rpow hs2, Real.sqrt_sq hs.le]
    have h2 : s⁻¹ ≤ 2 / δ := inv_s_le hs hδ hδs
    calc (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * 2 / s
        = ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) * 2) * s⁻¹ := by ring
      _ ≤ (1 / 2) * (2 / δ) :=
          mul_le_mul four_pi_rpow_mul_two_le_half h2 (by positivity) (by norm_num)
      _ = 1 / δ := by ring
  have hC : |s⁻¹| ≤ 2 / δ := by
    rw [abs_of_pos (inv_pos.mpr hs)]
    exact inv_s_le hs hδ hδs
  have hD : |I3| ≤ 1 / δ := by
    rw [hI3]
    have hD0 := boxGreen3Tail_le (s := s) (t₀ := s ^ 2) hs le_rfl x y
    have hexp : s ^ 2 * (Real.pi / s) ^ 2 = Real.pi ^ 2 := by
      rw [div_pow]; field_simp
    rw [hexp] at hD0
    refine le_trans hD0 ?_
    have h1 : s⁻¹ ≤ 2 / δ := inv_s_le hs hδ hδs
    have h2 : 48 * s⁻¹ * Real.exp (-(Real.pi ^ 2))
        ≤ 48 * (2 / δ) * Real.exp (-(Real.pi ^ 2)) := by
      have h : 0 ≤ 48 * Real.exp (-(Real.pi ^ 2)) := by positivity
      nlinarith [h1, h]
    have h3 : 48 * (2 / δ) * Real.exp (-(Real.pi ^ 2)) ≤ 1 / δ := by
      calc 48 * (2 / δ) * Real.exp (-(Real.pi ^ 2))
          = 96 * Real.exp (-(Real.pi ^ 2)) / δ := by ring
        _ ≤ 1 / δ := by
            rw [div_le_div_iff_of_pos_right hδ]
            linarith [exp_neg_pi_sq_mul_le]
    linarith [h2, h3]
  have htri : |I1 - I2 - s⁻¹ + I3| ≤ |I1| + |I2| + |s⁻¹| + |I3| := by
    have h1 := abs_add_le (I1 - I2 - s⁻¹) I3
    have h2 := abs_add_le (I1 - I2) (-(s⁻¹))
    have h3 := abs_add_le I1 (-I2)
    rw [abs_neg] at h2 h3
    have e2 : |I1 - I2| ≤ |I1| + |I2| := by
      rw [sub_eq_add_neg]; exact h3
    have e3 : |I1 - I2 - s⁻¹| ≤ |I1 - I2| + |s⁻¹| := by
      rw [sub_eq_add_neg] at h2 ⊢
      exact h2
    linarith
  have hsum : |I1| + |I2| + |s⁻¹| + |I3| ≤ 300 / δ + 1 / δ + 2 / δ + 1 / δ := by
    linarith [hA, hB, hC, hD]
  calc |I1 - I2 - s⁻¹ + I3| ≤ |I1| + |I2| + |s⁻¹| + |I3| := htri
    _ ≤ 300 / δ + 1 / δ + 2 / δ + 1 / δ := hsum
    _ = 304 / δ := by ring
    _ ≤ 400 / δ := by rw [div_le_div_iff_of_pos_right hδ]; norm_num


/-! ## 11. The free 3-D heat kernel in norm form, and its time integral -/

/-- the free heat kernel's product form equals the norm form. -/
lemma freeHeat3_eq {t : ℝ} (ht : 0 ≤ t) (x y : ℝ³) :
    freeHeat3 t x y = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
      * Real.exp (-(‖x - y‖ ^ 2 / (4 * t))) := by
  have hnorm : ‖x - y‖ ^ 2 = ∑ j : Fin 3, (x j - y j) ^ 2 := by
    simpa using EuclideanSpace.real_norm_sq_eq (x - y)
  have h1 : ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ))) ^ 3
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) := rpow_half_cube ht
  have h2 : (∑ j : Fin 3, -(x j - y j) ^ 2 / (4 * t))
      = -(‖x - y‖ ^ 2 / (4 * t)) := by
    rw [← Finset.sum_div, Finset.sum_neg_distrib, hnorm]
    ring
  rw [freeHeat3, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum, h1, h2]

/-- **the free heat kernel integrates to the Newtonian kernel**:
`∫_0^∞ K_t(x,y)dt = (4π‖x−y‖)^{−1}` for `x ≠ y`. -/
theorem integral_freeHeat3 {x y : ℝ³} (hxy : x ≠ y) :
    (∫ t in Set.Ioi (0 : ℝ), freeHeat3 t x y) = (4 * Real.pi * ‖x - y‖)⁻¹ := by
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), freeHeat3 t x y
      = (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(‖x - y‖ ^ 2 / (4 * t))) :=
    fun t ht => freeHeat3_eq ht.le x y
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    Commons.Analysis.Integral.integral_heat_coulomb_three hpos]
  rw [one_div]

/-- integrability of the free heat kernel on the positive half-line. -/
lemma integrableOn_freeHeat3 {x y : ℝ³} (hxy : x ≠ y) :
    IntegrableOn (fun t : ℝ => freeHeat3 t x y) (Set.Ioi 0) := by
  have hval := integral_freeHeat3 hxy
  by_contra h
  rw [integral_undef h] at hval
  have hxy' : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hpos : 0 < (4 * Real.pi * ‖x - y‖)⁻¹ := inv_pos.mpr (by positivity)
  linarith

/-! ## 12. `boxGreenDev` is the deviation of the box Neumann Green function -/

private lemma aemeasurable_neuHeat1 (s u v : ℝ) :
    AEMeasurable (fun t : ℝ => neuHeat1 s t u v) volume := by
  apply AEMeasurable.tsum
  intro k
  fun_prop

private lemma aemeasurable_freeHeat3 (x y : ℝ³) :
    AEMeasurable (fun t : ℝ => freeHeat3 t x y) volume := by
  have h : (fun t : ℝ => freeHeat3 t x y)
      = fun t : ℝ => ∏ j : Fin 3, (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
          * Real.exp (-((x j - y j) ^ 2) / (4 * t)) := rfl
  rw [h]
  have hf : ∀ j ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable
      (fun t : ℝ => (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
        * Real.exp (-((x j - y j) ^ 2) / (4 * t))) volume := fun j _ =>
    (by fun_prop : Measurable (fun t : ℝ => (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
      * Real.exp (-((x j - y j) ^ 2) / (4 * t)))).aemeasurable
  have hfun : (fun t : ℝ => ∏ j : Fin 3, (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
        * Real.exp (-((x j - y j) ^ 2) / (4 * t)))
      = ∏ j : Fin 3, fun t : ℝ => (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
        * Real.exp (-((x j - y j) ^ 2) / (4 * t)) := by
    funext t
    simp [Finset.prod_apply]
  rw [hfun]
  exact Finset.aemeasurable_prod (μ := volume) Finset.univ hf

private lemma aemeasurable_boxHeat3 (s : ℝ) (x y : ℝ³) :
    AEMeasurable (fun t : ℝ => boxHeat3 s t x y) volume := by
  have h : (fun t : ℝ => boxHeat3 s t x y)
      = fun t : ℝ => ∏ j : Fin 3, neuHeat1 s t (x j) (y j) := rfl
  rw [h]
  have hf : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      AEMeasurable (fun t : ℝ => neuHeat1 s t (x j) (y j)) volume :=
    fun j _ => aemeasurable_neuHeat1 s (x j) (y j)
  have hfun : (fun t : ℝ => ∏ j : Fin 3, neuHeat1 s t (x j) (y j))
      = ∏ j : Fin 3, fun t : ℝ => neuHeat1 s t (x j) (y j) := by
    funext t
    simp [Finset.prod_apply]
  rw [hfun]
  exact Finset.aemeasurable_prod (μ := volume) Finset.univ hf

/-- integrability of the heat-kernel gap on `(0,s²]`, on the `δ`-inner region. -/
private lemma integrableOn_boxHeat3_gap {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδs : 2 * δ ≤ s) (x y : ℝ³) (hx : ∀ j, |x j| ≤ s / 2 - δ)
    (hy : ∀ j, |y j| ≤ s / 2 - δ) :
    IntegrableOn (fun t : ℝ => boxHeat3 s t x y - freeHeat3 t x y) (Set.Ioc 0 (s ^ 2)) := by
  have hc2 : 0 < δ ^ 2 := pow_pos hδ 2
  have hInt : IntegrableOn (fun t : ℝ => 7000 * ((4 * Real.pi * t) ^ (-(3 / 2 : ℝ))
      * Real.exp (-(δ ^ 2 / t)))) (Set.Ioc 0 (s ^ 2)) :=
    ((integrableOn_heat_majorant hc2).mono_set Set.Ioc_subset_Ioi_self).const_mul 7000
  refine hInt.mono' ?_ ?_
  · exact aestronglyMeasurable_iff_aemeasurable.mpr
      (((aemeasurable_boxHeat3 s x y).sub (aemeasurable_freeHeat3 x y)).mono_measure
        Measure.restrict_le_self)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    simpa only [mul_assoc] using boxHeat3_sub_freeHeat3_le hs ht.1 hδ hδs ht.2 x y hx hy

/-- integrability of the box-Green deviation on `(s²,∞)`. -/
private lemma integrableOn_boxHeat3_sub_tail {s : ℝ} (hs : 0 < s) (x y : ℝ³) :
    IntegrableOn (fun t : ℝ => boxHeat3 s t x y - (s ^ 3)⁻¹) (Set.Ioi (s ^ 2)) := by
  have hs2 : 0 < s ^ 2 := pow_pos hs 2
  have hb : 0 < (Real.pi / s) ^ 2 := by positivity
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-(t * (Real.pi / s) ^ 2)))
      (Set.Ioi (s ^ 2)) := by
    have h := exp_neg_integrableOn_Ioi (s ^ 2) hb
    simpa [mul_comm, neg_mul] using h
  have hInt : IntegrableOn (fun t : ℝ => 48 * (s ^ 3)⁻¹
      * Real.exp (-(t * (Real.pi / s) ^ 2))) (Set.Ioi (s ^ 2)) := hexp.const_mul _
  refine hInt.mono' ?_ ?_
  · exact aestronglyMeasurable_iff_aemeasurable.mpr
      (((aemeasurable_boxHeat3 s x y).sub aemeasurable_const).mono_measure
        Measure.restrict_le_self)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hts : s ^ 2 ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs]
    simpa only [mul_assoc] using boxHeat3_sub_le hs hts x y

/-- integrability of the box-Green deviation on `(0,s²]`. -/
private lemma integrableOn_boxHeat3_sub_head {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδs : 2 * δ ≤ s) {x y : ℝ³} (hxy : x ≠ y) (hx : ∀ j, |x j| ≤ s / 2 - δ)
    (hy : ∀ j, |y j| ≤ s / 2 - δ) :
    IntegrableOn (fun t : ℝ => boxHeat3 s t x y - (s ^ 3)⁻¹) (Set.Ioc 0 (s ^ 2)) := by
  have h1 := integrableOn_boxHeat3_gap hs hδ hδs x y hx hy
  have hfF : IntegrableOn (fun t : ℝ => freeHeat3 t x y) (Set.Ioc 0 (s ^ 2)) :=
    (integrableOn_freeHeat3 hxy).mono_set Set.Ioc_subset_Ioi_self
  have h2 : IntegrableOn (fun t : ℝ => freeHeat3 t x y - (s ^ 3)⁻¹) (Set.Ioc 0 (s ^ 2)) :=
    hfF.sub (integrableOn_const (C := (s ^ 3)⁻¹) (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
  have hcongr : (fun t : ℝ => boxHeat3 s t x y - (s ^ 3)⁻¹)
      = fun t : ℝ => (boxHeat3 s t x y - freeHeat3 t x y) + (freeHeat3 t x y - (s ^ 3)⁻¹) := by
    funext t; ring
  rw [hcongr]
  exact h1.add h2

/-- **the box-Green deviation identity**: for `x ≠ y` on the `δ`-inner region,

`∫_0^∞(p_N^{(3)}(t,x,y) − s^{−3})dt = (4π‖x−y‖)^{−1} + boxGreenDev s x y`.

This is the modelling interface of the D1 sharp-mass step: the (improper)
integral of the box Neumann heat kernel minus its stationary weight is the
box Neumann Green function, which differs from the free Newtonian kernel
exactly by `boxGreenDev`.  The diagonal is `volume`-null
(`SmallBoxSharpMass.volume_diagonal_eq_zero`), so the `x ≠ y` restriction is
harmless in the double-integral application. -/
theorem integral_boxHeat3_eq {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) (hδs : 2 * δ ≤ s)
    {x y : ℝ³} (hxy : x ≠ y) (hx : ∀ j, |x j| ≤ s / 2 - δ) (hy : ∀ j, |y j| ≤ s / 2 - δ) :
    (∫ t in Set.Ioi (0 : ℝ), (boxHeat3 s t x y - (s ^ 3)⁻¹))
      = (4 * Real.pi * ‖x - y‖)⁻¹ + boxGreenDev s x y := by
  have hs2 : 0 < s ^ 2 := pow_pos hs 2
  have hP1 := integrableOn_boxHeat3_sub_head hs hδ hδs hxy hx hy
  have hP2 := integrableOn_boxHeat3_sub_tail hs x y
  have hgap := integrableOn_boxHeat3_gap hs hδ hδs x y hx hy
  have hfF : IntegrableOn (fun t : ℝ => freeHeat3 t x y) (Set.Ioc 0 (s ^ 2)) :=
    (integrableOn_freeHeat3 hxy).mono_set Set.Ioc_subset_Ioi_self
  have hfG : IntegrableOn (fun t : ℝ => freeHeat3 t x y) (Set.Ioi (s ^ 2)) :=
    (integrableOn_freeHeat3 hxy).mono_set fun t ht => lt_trans hs2 ht
  have hconst : (∫ t in Set.Ioc (0 : ℝ) (s ^ 2), (s ^ 3)⁻¹) = s⁻¹ := by
    rw [MeasureTheory.setIntegral_const, Measure.real_def, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ s ^ 2), smul_eq_mul]
    field_simp
  have hsplit : (∫ t in Set.Ioi (0 : ℝ), (boxHeat3 s t x y - (s ^ 3)⁻¹))
      = (∫ t in Set.Ioc 0 (s ^ 2), (boxHeat3 s t x y - (s ^ 3)⁻¹))
        + (∫ t in Set.Ioi (s ^ 2), (boxHeat3 s t x y - (s ^ 3)⁻¹)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hs2.le]
    exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hP1 hP2
  have hline : (∫ t in Set.Ioc 0 (s ^ 2), (boxHeat3 s t x y - (s ^ 3)⁻¹))
      = (∫ t in Set.Ioc 0 (s ^ 2), (boxHeat3 s t x y - freeHeat3 t x y))
        + (∫ t in Set.Ioc 0 (s ^ 2), freeHeat3 t x y) - s⁻¹ := by
    have hcongr : (fun t : ℝ => boxHeat3 s t x y - (s ^ 3)⁻¹)
        = fun t : ℝ => (boxHeat3 s t x y - freeHeat3 t x y)
          + (freeHeat3 t x y - (s ^ 3)⁻¹) := by
      funext t; ring
    have hcst : IntegrableOn (fun _ : ℝ => (s ^ 3)⁻¹) (Set.Ioc 0 (s ^ 2)) :=
      integrableOn_const (C := (s ^ 3)⁻¹) (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hadd : (∫ t in Set.Ioc 0 (s ^ 2), ((boxHeat3 s t x y - freeHeat3 t x y)
        + (freeHeat3 t x y - (s ^ 3)⁻¹)))
        = (∫ t in Set.Ioc 0 (s ^ 2), (boxHeat3 s t x y - freeHeat3 t x y))
          + (∫ t in Set.Ioc 0 (s ^ 2), (freeHeat3 t x y - (s ^ 3)⁻¹)) :=
      integral_add hgap (hfF.sub hcst)
    rw [hcongr, hadd, integral_sub hfF hcst, hconst]
    ring
  have hsplit2 : (∫ t in Set.Ioi (0 : ℝ), freeHeat3 t x y)
      = (∫ t in Set.Ioc 0 (s ^ 2), freeHeat3 t x y)
        + (∫ t in Set.Ioi (s ^ 2), freeHeat3 t x y) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hs2.le]
    exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hfF hfG
  have hfree := integral_freeHeat3 hxy
  rw [hsplit, hline, boxGreenDev]
  linarith [hfree, hsplit2]


/-! ## 13. The packaged D1 sharp-mass comparison -/

/-- **the box-mode sharp-mass comparison** — the D1 sharp-mass step, fully
assembled from the two Session-270 results:

if `W ≥ 0` is integrable, supported in `ball 0 R`, and `δ`-inner in the box
(`|x_j| ≤ s/2 − δ` on `supp W`, `2δ ≤ s`), then the box Neumann Newtonian
double energy `∬W(x)W(y)·G_s(x,y)` — represented here through the Green
deviation `boxGreenDev` (the spectral identification `Σ_k λ_k^{-1}⟨W,ê_k⟩² =
∬WWG_s` being the only remaining input) — is at most `(1 + 8π·400·R/δ)`
times the free Newtonian energy `∬W(x)W(y)/(4π‖x−y‖)`.

With `δ ≳ s` (the corpus's `hsR : R0 ≤ s·chiR0`) this is the
`(1 + C·R/s)` slack that the box-mode transcription of FS's sharp mass costs
(Session-268/269). -/
theorem boxSharpMass_continuum_le {W : ℝ³ → ℝ} {s δ R : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hδs : 2 * δ ≤ s) (hR : 0 < R) (hWnn : 0 ≤ W) (hWint : Integrable W)
    (hWsupp : tsupport W ⊆ ball (0 : ℝ³) R)
    (hinner : ∀ x ∈ tsupport W, ∀ j : Fin 3, |x j| ≤ s / 2 - δ)
    (hintC : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹))
    (hintD : Integrable (fun p : ℝ³ × ℝ³ => W p.1 * W p.2 * boxGreenDev s p.1 p.2)) :
    (∫ p : ℝ³ × ℝ³, W p.1 * W p.2
        * ((4 * π * ‖p.1 - p.2‖ : ℝ)⁻¹ + boxGreenDev s p.1 p.2))
      ≤ (1 + 8 * π * 400 * R / δ)
          * ∫ p : ℝ³ × ℝ³, W p.1 * W p.2 * (4 * π * ‖p.1 - p.2‖ : ℝ)⁻¹ :=
  sharpMass_le_of_kernel_dev (W := W) (Dev := fun x y => boxGreenDev s x y)
    (R := R) (C := 400) (δ := δ) hR hδ (by norm_num) hWnn hWint hWsupp
    (fun x y hx' hy' => boxGreenDev_le hs hδ hδs x y (hinner x hx') (hinner y hy'))
    hintC hintD
