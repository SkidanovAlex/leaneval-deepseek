import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS_RegExport.RXT.SysAux.PieceDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.SysAux.piece_z_bounds_rho`

The `ρ`-weighted `z`-jet bounds for the two explicit radial profiles of the forcing
(`explicit_piece_bounds`): for `j ≤ 2` and `z > 0`,

* `|(z∂_z)^j (z²/(1+z)³)| ≤ 10 z²/(1+z)²`  and  `≤ 10 z/(1+z)²`,
* `|(z∂_z)^j (z²/(1+z)⁴)| ≤ 10 z²/(1+z)²`.

The strategy is to compute the two-derivative jets explicitly and then pass to the
substitution `u = z/(1+z) ∈ (0,1)`, in which every one of the six rational functions becomes
`u²(1-u)^d · c(u)` with `d ∈ {1,2}` and a *bounded* polynomial factor `c` (explicitly
`1`, `2-3u`, `4-15u+12u²`, `2(1-2u)`, `4(1-5u+5u²)`).  The two targets are then exactly `10u²`
and `10u(1-u)`, and the bounds reduce to `(1-u)^d ≤ 1` and `|c(u)| ≤ 10`.
-/

namespace Work.FTS_RegExport.RXT.SysAux

/-! ## Derivatives of the explicit radial pieces -/

private theorem deriv_zsq (z : ℝ) : deriv (fun z : ℝ => z ^ 2) z = 2 * z := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id 2
  rw [show (fun z' : ℝ => z') ^ 2 = (fun z' : ℝ => z' ^ 2) from rfl] at h
  have h1 : deriv (fun z' : ℝ => z') z = 1 := deriv_id z
  rw [h, h1]
  ring

private theorem deriv_one_add_pow (k : ℕ) (z : ℝ) :
    deriv (fun z : ℝ => (1 + z) ^ k) z = (k : ℝ) * (1 + z) ^ (k - 1) := by
  have h := deriv_pow (f := fun z : ℝ => 1 + z) (x := z) (by fun_prop) k
  rw [show (fun z : ℝ => 1 + z) ^ k = (fun z : ℝ => (1 + z) ^ k) from rfl] at h
  rw [h]
  have h1 : deriv (fun z : ℝ => 1 + z) z = 1 := by
    rw [deriv_const_add (1 : ℝ)]
    exact deriv_id z
  rw [h1, mul_one]

private theorem deriv_rho3 (z : ℝ) (hz : 0 < z) :
    deriv (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z = (2 * z - z ^ 2) / (1 + z) ^ 4 := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rw [deriv_fun_div (c := fun z : ℝ => z ^ 2) (d := fun z : ℝ => (1 + z) ^ 3)
    (by fun_prop) (by fun_prop) (by positivity)]
  rw [deriv_zsq z, deriv_one_add_pow 3 z]
  field_simp
  ring

private theorem deriv_num_b (z : ℝ) :
    deriv (fun z : ℝ => z ^ 2 * (2 - z)) z = 4 * z - 3 * z ^ 2 := by
  rw [deriv_fun_mul (c := fun z : ℝ => z ^ 2) (d := fun z : ℝ => 2 - z)
    (by fun_prop) (by fun_prop)]
  rw [deriv_zsq z]
  have h2 : deriv (fun z : ℝ => 2 - z) z = -1 := by
    rw [deriv_const_sub (2 : ℝ)]
    simp
  rw [h2]
  ring

private theorem deriv_3b (z : ℝ) (hz : 0 < z) :
    deriv (fun z : ℝ => z ^ 2 * (2 - z) / (1 + z) ^ 4) z
      = z * (4 - 7 * z + z ^ 2) / (1 + z) ^ 5 := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rw [deriv_fun_div (c := fun z : ℝ => z ^ 2 * (2 - z)) (d := fun z : ℝ => (1 + z) ^ 4)
    (by fun_prop) (by fun_prop) (by positivity)]
  rw [deriv_num_b z, deriv_one_add_pow 4 z]
  field_simp
  ring

private theorem deriv_rho4 (z : ℝ) (hz : 0 < z) :
    deriv (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) z = 2 * z * (1 - z) / (1 + z) ^ 5 := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rw [deriv_fun_div (c := fun z : ℝ => z ^ 2) (d := fun z : ℝ => (1 + z) ^ 4)
    (by fun_prop) (by fun_prop) (by positivity)]
  rw [deriv_zsq z, deriv_one_add_pow 4 z]
  field_simp
  ring

private theorem deriv_num_d (z : ℝ) :
    deriv (fun z : ℝ => 2 * z ^ 2 * (1 - z)) z = 4 * z - 6 * z ^ 2 := by
  rw [deriv_fun_mul (c := fun z : ℝ => 2 * z ^ 2) (d := fun z : ℝ => 1 - z)
    (by fun_prop) (by fun_prop)]
  rw [deriv_const_mul_field (2 : ℝ), deriv_zsq z]
  have h2 : deriv (fun z : ℝ => 1 - z) z = -1 := by
    rw [deriv_const_sub (1 : ℝ)]
    simp
  rw [h2]
  ring

private theorem deriv_4b (z : ℝ) (hz : 0 < z) :
    deriv (fun z : ℝ => 2 * z ^ 2 * (1 - z) / (1 + z) ^ 5) z
      = 4 * z * (1 - 3 * z + z ^ 2) / (1 + z) ^ 6 := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rw [deriv_fun_div (c := fun z : ℝ => 2 * z ^ 2 * (1 - z)) (d := fun z : ℝ => (1 + z) ^ 5)
    (by fun_prop) (by fun_prop) (by positivity)]
  rw [deriv_num_d z, deriv_one_add_pow 5 z]
  field_simp
  ring

/-! ## The explicit jets of the two profiles -/

private theorem ZIter_rho3_one (z : ℝ) (hz : 0 < z) :
    ZIter 1 (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z = z ^ 2 * (2 - z) / (1 + z) ^ 4 := by
  rw [ZIter_succ_apply, ZIter_zero, deriv_rho3 z hz]
  ring

private theorem ZIter_rho3_two (z : ℝ) (hz : 0 < z) :
    ZIter 2 (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z
      = z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 := by
  rw [ZIter_succ_apply]
  have heq : Set.EqOn (ZIter 1 (fun z : ℝ => z ^ 2 / (1 + z) ^ 3))
      (fun z : ℝ => z ^ 2 * (2 - z) / (1 + z) ^ 4) (Set.Ioi 0) :=
    fun w hw => ZIter_rho3_one w hw
  have hderiv : deriv (ZIter 1 (fun z : ℝ => z ^ 2 / (1 + z) ^ 3)) z
      = deriv (fun z : ℝ => z ^ 2 * (2 - z) / (1 + z) ^ 4) z :=
    heq.deriv isOpen_Ioi hz
  rw [hderiv, deriv_3b z hz]
  ring

private theorem ZIter_rho4_one (z : ℝ) (hz : 0 < z) :
    ZIter 1 (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) z = 2 * z ^ 2 * (1 - z) / (1 + z) ^ 5 := by
  rw [ZIter_succ_apply, ZIter_zero, deriv_rho4 z hz]
  ring

private theorem ZIter_rho4_two (z : ℝ) (hz : 0 < z) :
    ZIter 2 (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) z
      = 4 * z ^ 2 * (z ^ 2 - 3 * z + 1) / (1 + z) ^ 6 := by
  rw [ZIter_succ_apply]
  have heq : Set.EqOn (ZIter 1 (fun z : ℝ => z ^ 2 / (1 + z) ^ 4))
      (fun z : ℝ => 2 * z ^ 2 * (1 - z) / (1 + z) ^ 5) (Set.Ioi 0) :=
    fun w hw => ZIter_rho4_one w hw
  have hderiv : deriv (ZIter 1 (fun z : ℝ => z ^ 2 / (1 + z) ^ 4)) z
      = deriv (fun z : ℝ => 2 * z ^ 2 * (1 - z) / (1 + z) ^ 5) z :=
    heq.deriv isOpen_Ioi hz
  rw [hderiv, deriv_4b z hz]
  ring

/-! ## The substituted variable `u = z/(1+z)` and the bounded polynomial factors -/

private lemma abs_c2 (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) : |2 - 3 * u| ≤ 10 := by
  rw [abs_le]; constructor <;> nlinarith

private lemma abs_c3 (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) : |4 - 15 * u + 12 * u ^ 2| ≤ 10 := by
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (u - 5 / 8), mul_nonneg (le_of_lt hu0) (by linarith : (0 : ℝ) ≤ 1 - u)]
  · nlinarith [sq_nonneg (u - 5 / 8), mul_nonneg (le_of_lt hu0) (by linarith : (0 : ℝ) ≤ 1 - u)]

private lemma abs_c4 (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) : |2 * (1 - 2 * u)| ≤ 10 := by
  rw [abs_le]; constructor <;> nlinarith

private lemma abs_c5 (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    |4 * (1 - 5 * u + 5 * u ^ 2)| ≤ 10 := by
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (u - 1 / 2), mul_nonneg (le_of_lt hu0) (by linarith : (0 : ℝ) ≤ 1 - u)]
  · nlinarith [sq_nonneg (u - 1 / 2), mul_nonneg (le_of_lt hu0) (by linarith : (0 : ℝ) ≤ 1 - u)]

/-- `|u²(1-u)c| ≤ 10u²` for `u ∈ (0,1)`, `|c| ≤ 10`. -/
private lemma bound_u_sq_d1 {u c : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hc : |c| ≤ 10) :
    |u ^ 2 * (1 - u) * c| ≤ 10 * u ^ 2 := by
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have habs : |u ^ 2 * (1 - u) * c| = u ^ 2 * ((1 - u) * |c|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 2), abs_of_pos h1u]
    ring
  rw [habs]
  have hle : (1 - u) * |c| ≤ 10 := by
    have := mul_le_mul (by linarith : (1 - u) ≤ 1) hc (abs_nonneg c) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using this
  calc u ^ 2 * ((1 - u) * |c|) ≤ u ^ 2 * 10 := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 10 * u ^ 2 := by ring

/-- `|u²(1-u)²c| ≤ 10u²` for `u ∈ (0,1)`, `|c| ≤ 10`. -/
private lemma bound_u_sq_d2 {u c : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hc : |c| ≤ 10) :
    |u ^ 2 * (1 - u) ^ 2 * c| ≤ 10 * u ^ 2 := by
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have h1u2 : (1 - u) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (le_of_lt hu0) (by linarith : (0 : ℝ) ≤ 2 - u)]
  have habs : |u ^ 2 * (1 - u) ^ 2 * c| = u ^ 2 * ((1 - u) ^ 2 * |c|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 - u) ^ 2)]
    ring
  rw [habs]
  have hle : (1 - u) ^ 2 * |c| ≤ 10 := by
    have := mul_le_mul h1u2 hc (abs_nonneg c) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using this
  calc u ^ 2 * ((1 - u) ^ 2 * |c|) ≤ u ^ 2 * 10 := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 10 * u ^ 2 := by ring

/-- `|u²(1-u)c| ≤ 10u(1-u)` for `u ∈ (0,1)`, `|c| ≤ 10`. -/
private lemma bound_u_lin_d1 {u c : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hc : |c| ≤ 10) :
    |u ^ 2 * (1 - u) * c| ≤ 10 * (u * (1 - u)) := by
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have huc : u * |c| ≤ 10 := by
    have h1 : u * |c| ≤ 1 * |c| := mul_le_mul_of_nonneg_right (le_of_lt hu1) (abs_nonneg c)
    linarith
  have habs : |u ^ 2 * (1 - u) * c| = (u * (1 - u)) * (u * |c|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 2), abs_of_pos h1u]
    ring
  rw [habs]
  calc (u * (1 - u)) * (u * |c|) ≤ (u * (1 - u)) * 10 :=
        mul_le_mul_of_nonneg_left huc (by positivity)
    _ = 10 * (u * (1 - u)) := by ring

/-! ## The nine bounds -/

private lemma b3_0_sq (z : ℝ) (hz : 0 < z) :
    |z ^ 2 / (1 + z) ^ 3| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 / (1 + z) ^ 3 = u ^ 2 * (1 - u) * 1 := by rw [hu]; field_simp; try ring
  have hrhs : z ^ 2 / (1 + z) ^ 2 = u ^ 2 := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_sq_d1 hu0 hu1 (by norm_num)

private lemma b3_0_lin (z : ℝ) (hz : 0 < z) :
    |z ^ 2 / (1 + z) ^ 3| ≤ 10 * (z / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 / (1 + z) ^ 3 = u ^ 2 * (1 - u) * 1 := by rw [hu]; field_simp; try ring
  have hrhs : z / (1 + z) ^ 2 = u * (1 - u) := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_lin_d1 hu0 hu1 (by norm_num)

private lemma b3_1_sq (z : ℝ) (hz : 0 < z) :
    |z ^ 2 * (2 - z) / (1 + z) ^ 4| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 * (2 - z) / (1 + z) ^ 4 = u ^ 2 * (1 - u) * (2 - 3 * u) := by
    rw [hu]; field_simp; try ring
  have hrhs : z ^ 2 / (1 + z) ^ 2 = u ^ 2 := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_sq_d1 hu0 hu1 (abs_c2 u hu0 hu1)

private lemma b3_1_lin (z : ℝ) (hz : 0 < z) :
    |z ^ 2 * (2 - z) / (1 + z) ^ 4| ≤ 10 * (z / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 * (2 - z) / (1 + z) ^ 4 = u ^ 2 * (1 - u) * (2 - 3 * u) := by
    rw [hu]; field_simp; try ring
  have hrhs : z / (1 + z) ^ 2 = u * (1 - u) := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_lin_d1 hu0 hu1 (abs_c2 u hu0 hu1)

private lemma b3_2_sq (z : ℝ) (hz : 0 < z) :
    |z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5
      = u ^ 2 * (1 - u) * (4 - 15 * u + 12 * u ^ 2) := by
    rw [hu]; field_simp; try ring
  have hrhs : z ^ 2 / (1 + z) ^ 2 = u ^ 2 := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_sq_d1 hu0 hu1 (abs_c3 u hu0 hu1)

private lemma b3_2_lin (z : ℝ) (hz : 0 < z) :
    |z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5| ≤ 10 * (z / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5
      = u ^ 2 * (1 - u) * (4 - 15 * u + 12 * u ^ 2) := by
    rw [hu]; field_simp; try ring
  have hrhs : z / (1 + z) ^ 2 = u * (1 - u) := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_lin_d1 hu0 hu1 (abs_c3 u hu0 hu1)

private lemma b4_0_sq (z : ℝ) (hz : 0 < z) :
    |z ^ 2 / (1 + z) ^ 4| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : z ^ 2 / (1 + z) ^ 4 = u ^ 2 * (1 - u) ^ 2 * 1 := by rw [hu]; field_simp; try ring
  have hrhs : z ^ 2 / (1 + z) ^ 2 = u ^ 2 := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_sq_d2 hu0 hu1 (by norm_num)

private lemma b4_1_sq (z : ℝ) (hz : 0 < z) :
    |2 * z ^ 2 * (1 - z) / (1 + z) ^ 5| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : 2 * z ^ 2 * (1 - z) / (1 + z) ^ 5 = u ^ 2 * (1 - u) ^ 2 * (2 * (1 - 2 * u)) := by
    rw [hu]; field_simp; try ring
  have hrhs : z ^ 2 / (1 + z) ^ 2 = u ^ 2 := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_sq_d2 hu0 hu1 (abs_c4 u hu0 hu1)

private lemma b4_2_sq (z : ℝ) (hz : 0 < z) :
    |4 * z ^ 2 * (z ^ 2 - 3 * z + 1) / (1 + z) ^ 6| ≤ 10 * (z ^ 2 / (1 + z) ^ 2) := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  set u : ℝ := z / (1 + z) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u < 1 := by rw [hu]; rw [div_lt_one hz1]; linarith
  have hkey : 4 * z ^ 2 * (z ^ 2 - 3 * z + 1) / (1 + z) ^ 6
      = u ^ 2 * (1 - u) ^ 2 * (4 * (1 - 5 * u + 5 * u ^ 2)) := by
    rw [hu]; field_simp; try ring
  have hrhs : z ^ 2 / (1 + z) ^ 2 = u ^ 2 := by rw [hu]; field_simp; try ring
  rw [hkey, hrhs]
  exact bound_u_sq_d2 hu0 hu1 (abs_c5 u hu0 hu1)

theorem piece_z_bounds_rho : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
    (|ZIter j (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z| ≤ 10 * (z ^ 2 / (1 + z) ^ 2)) ∧
    (|ZIter j (fun z : ℝ => z ^ 2 / (1 + z) ^ 3) z| ≤ 10 * (z / (1 + z) ^ 2)) ∧
    (|ZIter j (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) z| ≤ 10 * (z ^ 2 / (1 + z) ^ 2)) := by
  intro j hj z hz
  interval_cases j
  · exact ⟨b3_0_sq z hz, b3_0_lin z hz, b4_0_sq z hz⟩
  · rw [ZIter_rho3_one z hz, ZIter_rho4_one z hz]
    exact ⟨b3_1_sq z hz, b3_1_lin z hz, b4_1_sq z hz⟩
  · rw [ZIter_rho3_two z hz, ZIter_rho4_two z hz]
    exact ⟨b3_2_sq z hz, b3_2_lin z hz, b4_2_sq z hz⟩

end Work.FTS_RegExport.RXT.SysAux
