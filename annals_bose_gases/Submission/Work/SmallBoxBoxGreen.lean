import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import ChallengeDeps
import Submission.Commons.Analysis.Fourier.neumann_heat_one_dim_images
import Submission.Commons.Analysis.Fourier.neumann_heat_one_dim_sub_le
import Submission.Commons.Analysis.Fourier.theta_shift_real
import Submission.Commons.Analysis.Integral.integral_heat_exp_neg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-269 — the box-Neumann heat kernel and the LARGE-`t` half of the
Ewald estimate of the sharp-mass kernel deviation

The sharp-mass step of the D1 layer (see `SmallBoxSharpMass`) needs, in the
box-mode route, the kernel deviation estimate

    `|G_s(x,y) − (4π‖x−y‖)⁻¹| ≤ C/δ`,   `δ := dist(supp W, ∂B)`

on the `δ`-inner region (`G_s` = the box Neumann Green function; numerics
Session-269: the deviation is NEGATIVE, `|·| ≤ 0.3/s` in the box interior, and
POSITIVE of size `~1/(4π·2·dist(y,∂B))` near a face).  The Ewald route splits
the `t`-integral of the heat-kernel difference at `t₀ = s²`:

    `G_s − free = ∫_0^{t₀}(p_N^{(3)} − K_t)dt + ∫_{t₀}^∞(p_N^{(3)} − K_t − s^{-3})dt`,

and this module closes the SECOND (large-`t`) piece:

  * `neuHeat1` — the 1-D box Neumann heat kernel (spectral form; the LHS of
    the commons `neumann_heat_one_dim_images` / `neumann_heat_one_dim_sub_le`);
  * `neuHeat1_sub_le` — the uniform large-`t` estimate
    `|p_N^{(1)}(t,u,v) − 1/s| ≤ (2/s)·r/(1−r)`, `r = exp(−t(π/s)²)`;
  * `boxHeat3` — the 3-D box Neumann heat kernel as the PRODUCT of the 1-D
    ones (the box is a product, so `p_N^{(3)}(t,x,y) = ∏_j p_N^{(1)}(t,x_j,y_j)`);
  * `exp_neg_pi_sq_le_eighth` — `exp(−π²) ≤ 1/8`;
  * `boxHeat3_sub_le` — `|p_N^{(3)}(t,x,y) − s^{-3}| ≤ 48 s^{-3}e^{−t(π/s)²}`
    for `t ≥ s²`;
  * `integral_exp_neg_mul_Ioi` — `∫_{t>t₀}e^{−bt}dt = e^{−bt₀}/b`;
  * `boxGreen3Tail_le` — the large-`t` half of the kernel deviation:
    `|∫_{t₀}^∞(p_N^{(3)} − s^{-3})dt| ≤ 48 s⁻¹e^{−t₀(π/s)²}` for
    `max(1,s²) ≤ t₀`, hence `O(1/s)` at `t₀ = s²`.

The remaining (small-`t`) half uses the image form of the heat kernel
(commons `neumann_heat_one_dim_images`) together with the displacement bounds
(commons `theta_shift_reflect_ge` / `theta_image_sum_le`) on the product
expansion `∏p_N^{(1)} − ∏K^{(1)} = Σ_{∅≠S}∏_{j∈S}(p_N^{(1)}−K^{(1)})∏_{j∉S}K^{(1)}`;
the plan and target estimates are recorded in `Submission/STATUS.md`
(Session-269 parts 3 and 6) and `SmallBoxDesignNote.md` (Session-269 add. 2).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Submission
open _root_.BoseGases
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **the 1-D box Neumann heat kernel** (spectral form) on `[−s/2, s/2]`:
`p_N^{(1)}(t,u,v) = Σ_k cos(kπ(u+s/2)/s)cos(kπ(v+s/2)/s)e^{−t(πk/s)²}·(k=0 ? 1/s : 2/s)`.
The commons `Commons.Analysis.Fourier.neumann_heat_one_dim_images` identifies
it with the Gaussian IMAGE sum. -/
noncomputable def neuHeat1 (s t u v : ℝ) : ℝ :=
  ∑' k : ℕ, Real.cos (Real.pi * k * (u + s / 2) / s) * Real.cos (Real.pi * k * (v + s / 2) / s)
    * Real.exp (-(t * (Real.pi * k / s) ^ 2)) * (if k = 0 then s else s / 2)⁻¹

/-- **uniform large-`t` deviation of the 1-D Neumann heat kernel** from its
limit `1/s` (the commons `neumann_heat_one_dim_sub_le`): with
`r = exp(−t(π/s)²)`, `|p_N^{(1)}(t,u,v) − 1/s| ≤ (2/s)·r/(1−r)`. -/
lemma neuHeat1_sub_le {s t u v : ℝ} (hs : 0 < s) (ht : 0 < t) :
    |neuHeat1 s t u v - s⁻¹|
      ≤ 2 * s⁻¹ * (Real.exp (-(t * (Real.pi / s) ^ 2))
          / (1 - Real.exp (-(t * (Real.pi / s) ^ 2)))) :=
  Commons.Analysis.Fourier.neumann_heat_one_dim_sub_le (s := s) (t := t) (u := u) (v := v) hs ht

/-- **the 1-D Neumann heat kernel in IMAGE form** (the commons
`Commons.Analysis.Fourier.neumann_heat_one_dim_images`): the spectral sum
equals the Gaussian image sum.  Every small-`t` estimate of the Ewald route
starts from this identity. -/
lemma neuHeat1_eq_image {s t u v : ℝ} (hs : 0 < s) (ht : 0 < t) :
    neuHeat1 s t u v = ∑' m : ℤ, (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
      (Real.exp (-((u - v + 2 * s * m) ^ 2) / (4 * t))
        + Real.exp (-((u + v - s + 2 * s * m) ^ 2) / (4 * t))) :=
  Commons.Analysis.Fourier.neumann_heat_one_dim_images hs ht

/-- **the 3-D box Neumann heat kernel** as the product of the 1-D kernels
(the box is a product, so `p_N^{(3)} = ∏_j p_N^{(1)}(·, x_j, y_j)`). -/
noncomputable def boxHeat3 (s t : ℝ) (x y : ℝ³) : ℝ :=
  ∏ j : Fin 3, neuHeat1 s t (x j) (y j)

/-- `exp(−π²) ≤ 1/8` (from `π² > 3` and `exp 1 > 2`). -/
lemma exp_neg_pi_sq_le_eighth : Real.exp (-(Real.pi ^ 2)) ≤ 1 / 8 := by
  have hpi2 : (3 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three, Real.pi_pos]
  have h1 : Real.exp (-(Real.pi ^ 2)) ≤ Real.exp (-(3 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(3 : ℝ)) = ((Real.exp 1) ^ 3)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    have h := Real.exp_nat_mul (n := 3) (x := 1)
    simp only [Nat.cast_ofNat, mul_one] at h
    exact h
  rw [h2] at h1
  have h3 : (8 : ℝ) < (Real.exp 1) ^ 3 := by
    have h : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ < (Real.exp 1) ^ 3 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  have h5 : ((Real.exp 1) ^ 3)⁻¹ ≤ 1 / 8 := by
    have h6 : ((Real.exp 1) ^ 3)⁻¹ ≤ (8 : ℝ)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by norm_num : (0 : ℝ) < 8)).2 h3.le
    simpa using h6
  exact le_trans h1 h5

/-- **the large-`t` deviation of the 3-D box Neumann heat kernel** from its
limit `s^{-3}`: for `t ≥ s²`,
`|p_N^{(3)}(t,x,y) − s^{-3}| ≤ 48·(s^3)⁻¹·exp(−t(π/s)²)`. -/
lemma boxHeat3_sub_le {s t : ℝ} (hs : 0 < s) (hT : s ^ 2 ≤ t) (x y : ℝ³) :
    |boxHeat3 s t x y - (s ^ 3)⁻¹| ≤ 48 * (s ^ 3)⁻¹ * Real.exp (-(t * (Real.pi / s) ^ 2)) := by
  set a : ℝ := s⁻¹ with ha
  set b : ℝ := (Real.pi / s) ^ 2 with hbdef
  set r : ℝ := Real.exp (-(t * b)) with hrdef
  have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs 2
  have hb : 0 < b := by rw [hbdef]; positivity
  have ha_pos : 0 < a := by rw [ha]; positivity
  have hr_pos : 0 < r := Real.exp_pos _
  have ht_pos : 0 < t := by nlinarith [hs2, hT]
  have hle : r ≤ Real.exp (-(Real.pi ^ 2)) := by
    rw [hrdef]
    apply Real.exp_le_exp.mpr
    have htb : t * b = t * Real.pi ^ 2 / s ^ 2 := by rw [hbdef]; rw [div_pow]; ring
    rw [htb, neg_le_neg_iff, le_div_iff₀ hs2]
    nlinarith [Real.pi_pos, hT, hs2]
  have hr_le_8 : r ≤ 1 / 8 := le_trans hle exp_neg_pi_sq_le_eighth
  set m : ℝ := 4 * a * r with hm
  have hmnn : 0 ≤ m := by rw [hm]; positivity
  have hm_le : m ≤ a / 2 := by rw [hm]; nlinarith [ha_pos, hr_le_8]
  have hm_le_a : m ≤ a := by linarith [hm_le, ha_pos]
  have hfac : ∀ j : Fin 3, |neuHeat1 s t (x j) (y j) - a| ≤ m := by
    intro j
    have h := neuHeat1_sub_le (s := s) (t := t) (u := x j) (v := y j) hs ht_pos
    rw [← ha] at h
    refine le_trans h ?_
    have h3 : Real.exp (-(t * (Real.pi / s) ^ 2)) / (1 - Real.exp (-(t * (Real.pi / s) ^ 2)))
        = r / (1 - r) := by rw [hrdef, hbdef]
    rw [h3]
    have hr1 : r < 1 := by linarith
    have h4 : r / (1 - r) ≤ 2 * r := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hr_le_8, hr_pos]
    calc 2 * a * (r / (1 - r)) ≤ 2 * a * (2 * r) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = m := by rw [hm]; ring
  have hprod_ub : boxHeat3 s t x y ≤ (a + m) ^ 3 := by
    have h : ∏ j : Fin 3, neuHeat1 s t (x j) (y j) ≤ ∏ _j : Fin 3, (a + m) := by
      apply Finset.prod_le_prod₀
      · intro j _
        have h1 := (abs_le.mp (hfac j)).1
        linarith [hm_le_a]
      · intro j _
        linarith [(abs_le.mp (hfac j)).2]
    simpa [boxHeat3, Finset.prod_const, Fintype.card_fin] using h
  have hprod_lb : (a - m) ^ 3 ≤ boxHeat3 s t x y := by
    have h : ∏ _j : Fin 3, (a - m) ≤ ∏ j : Fin 3, neuHeat1 s t (x j) (y j) := by
      apply Finset.prod_le_prod₀
      · intro j _
        linarith [hm_le_a]
      · intro j _
        linarith [(abs_le.mp (hfac j)).1]
    simpa [boxHeat3, Finset.prod_const, Fintype.card_fin] using h
  have h3 : (a + m) ^ 3 - a ^ 3 ≤ 27 * a ^ 3 * r := by
    have hfac2 : (a + 4 * a * r) ^ 3 - a ^ 3 - 27 * a ^ 3 * r
        = a ^ 3 * r * (48 * r + 64 * r ^ 2 - 15) := by ring
    have hle0 : a ^ 3 * r * (48 * r + 64 * r ^ 2 - 15) ≤ 0 := by
      have h1 : 48 * r + 64 * r ^ 2 - 15 ≤ 0 := by nlinarith [hr_le_8, hr_pos]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
    rw [hm]; linarith [hfac2, hle0]
  have h4 : a ^ 3 - (a - m) ^ 3 ≤ 27 * a ^ 3 * r := by
    have hfac2 : a ^ 3 - (a - 4 * a * r) ^ 3 - 27 * a ^ 3 * r
        = a ^ 3 * r * (64 * r ^ 2 - 48 * r - 15) := by ring
    have hle0 : a ^ 3 * r * (64 * r ^ 2 - 48 * r - 15) ≤ 0 := by
      have h1 : 64 * r ^ 2 - 48 * r - 15 ≤ 0 := by nlinarith [hr_le_8, hr_pos]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
    rw [hm]; linarith [hfac2, hle0]
  have hs3 : (s ^ 3)⁻¹ = a ^ 3 := by rw [ha, inv_pow]
  rw [hs3, abs_le]
  constructor
  · have h5 : a ^ 3 ≤ boxHeat3 s t x y + 27 * a ^ 3 * r := by linarith [hprod_lb, h4]
    have h6 : 27 * a ^ 3 * r ≤ 48 * a ^ 3 * r := by
      nlinarith [pow_pos ha_pos 3, hr_pos]
    linarith [h5, h6]
  · have h5 : boxHeat3 s t x y ≤ a ^ 3 + 27 * a ^ 3 * r := by linarith [hprod_ub, h3]
    have h6 : 27 * a ^ 3 * r ≤ 48 * a ^ 3 * r := by
      nlinarith [pow_pos ha_pos 3, hr_pos]
    linarith [h5, h6]

/-- `∫_{t > t₀} exp(−b t) dt = exp(−b t₀)/b` for `b > 0` (substitution +
`Real.integral_exp_neg_Ioi`). -/
lemma integral_exp_neg_mul_Ioi {b t₀ : ℝ} (hb : 0 < b) :
    (∫ t in Set.Ioi t₀, Real.exp (-(b * t))) = Real.exp (-(b * t₀)) / b := by
  rw [← integral_indicator measurableSet_Ioi]
  have hcomp := Measure.integral_comp_mul_left
    (fun y : ℝ => (Set.Ioi (b * t₀)).indicator (fun y => Real.exp (-y)) y) b
  rw [show (fun x : ℝ => (Set.Ioi (b * t₀)).indicator (fun y => Real.exp (-y)) (b * x))
      = fun x : ℝ => (Set.Ioi t₀).indicator (fun t => Real.exp (-(b * t))) x from by
    funext x
    simp only [Set.indicator_apply, Set.mem_Ioi]
    by_cases hx : t₀ < x
    · have h1 : b * t₀ < b * x := by nlinarith [hb, hx]
      simp [hx, h1]
    · have hle : x ≤ t₀ := le_of_not_gt hx
      have h1 : ¬ (b * t₀ < b * x) := by nlinarith [hb, hle]
      simp [hx, h1]] at hcomp
  rw [hcomp, integral_indicator measurableSet_Ioi, integral_exp_neg_Ioi,
    abs_of_pos (inv_pos.mpr hb), smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- **the large-`t` half of the box-Green deviation**: for `s² ≤ t₀`,
`|∫_{t > t₀}(p_N^{(3)}(t,x,y) − (s^3)⁻¹)dt| ≤ 48·s⁻¹·exp(−t₀(π/s)²)`. -/
lemma boxGreen3Tail_le {s t₀ : ℝ} (hs : 0 < s) (hT : s ^ 2 ≤ t₀)
    (x y : ℝ³) :
    |∫ t in Set.Ioi t₀, (boxHeat3 s t x y - (s ^ 3)⁻¹)|
      ≤ 48 * s⁻¹ * Real.exp (-(t₀ * (Real.pi / s) ^ 2)) := by
  set b : ℝ := (Real.pi / s) ^ 2 with hbdef
  have hb : 0 < b := by rw [hbdef]; positivity
  have hb_eq : b = Real.pi ^ 2 / s ^ 2 := by rw [hbdef, div_pow]
  have hg : IntegrableOn (fun t : ℝ => 48 * (s ^ 3)⁻¹ * Real.exp (-(b * t))) (Set.Ioi t₀) := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-(b * t))) (Set.Ioi t₀) := by
      have h := exp_neg_integrableOn_Ioi t₀ hb
      simpa [mul_comm, neg_mul] using h
    exact h1.const_mul _
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioi t₀)),
      ‖boxHeat3 s t x y - (s ^ 3)⁻¹‖ ≤ 48 * (s ^ 3)⁻¹ * Real.exp (-(b * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : s ^ 2 ≤ t := le_trans hT ht.out.le
    have h := boxHeat3_sub_le (s := s) (t := t) hs ht' x y
    rw [Real.norm_eq_abs, hbdef, mul_comm ((Real.pi / s) ^ 2) t]
    exact h
  have h := norm_integral_le_of_norm_le hg hae
  rw [Real.norm_eq_abs] at h
  refine le_trans h ?_
  rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_Ioi hb]
  have hexp : Real.exp (-(t₀ * (Real.pi / s) ^ 2)) = Real.exp (-(b * t₀)) := by
    rw [hbdef]; congr 1; ring
  rw [hexp]
  have hX : 0 ≤ Real.exp (-(b * t₀)) := (Real.exp_pos _).le
  have hkey : (s ^ 3)⁻¹ * b⁻¹ ≤ s⁻¹ := by
    rw [← mul_inv, inv_le_inv₀ (by positivity) (by positivity), hb_eq]
    field_simp
    nlinarith [Real.pi_gt_three, hs]
  have h1 : (s ^ 3)⁻¹ * (Real.exp (-(b * t₀)) / b) ≤ s⁻¹ * Real.exp (-(b * t₀)) := by
    rw [div_eq_mul_inv]
    calc (s ^ 3)⁻¹ * (Real.exp (-(b * t₀)) * b⁻¹)
        = (s ^ 3)⁻¹ * b⁻¹ * Real.exp (-(b * t₀)) := by ring
      _ ≤ s⁻¹ * Real.exp (-(b * t₀)) := mul_le_mul_of_nonneg_right hkey hX
  nlinarith [h1]

end BoseGases
end Submission
