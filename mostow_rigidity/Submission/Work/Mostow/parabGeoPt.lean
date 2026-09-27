import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.poAux

/-!
# The point of the geodesic joining two boundary points: the explicit formula

Let `ξ ≠ η` be two points of the boundary sphere `Sph n ⊂ E n` (the chart of `ℍⁿ`), and put
`c = ⟪ξ, η⟫`, so that `q = √((1 - c)/2) = sin(θ/2)` where `θ` is the angle between `ξ` and `η`.
The vector

`u = (2q)⁻¹ • (exp t • ξ + exp (-t) • η)`

is the point of the (chord) geodesic joining `ξ` and `η` at hyperbolic distance `t` from the
"midpoint" side of `ξ`; the explicit computation gives

* `tpart u = cosh t / q` (the time coordinate of the hyperboloid point over `u`),
* `busemann ξ u = log q - t`,
* `busemann η u = log q + t`.

The proof is elementary chart algebra: writing `a = exp t`, `b = exp (-t)` (so `a * b = 1`) and
`c = ⟪ξ, η⟫`, bilinearity of the inner product and `‖ξ‖ = ‖η‖ = 1` give

`⟪u, u⟫ = (2q)⁻² (a² + b² + 2c)`,  `⟪u, ξ⟫ = (2q)⁻¹ (a + b c)`,  `⟪u, η⟫ = (2q)⁻¹ (a c + b)`,

and since `q² = (1 - c)/2`, `cosh t = (a + b)/2` and `a * b = 1` one gets

`1 + ⟪u, u⟫ = (cosh t / q)²`,  `tpart u - ⟪u, ξ⟫ = q * exp (-t)`,  `tpart u - ⟪u, η⟫ = q * exp t`,

which is exactly what is needed after taking a square root and a logarithm.
-/

open Submission.Mostow

namespace Work.Mostow

/-- The inner product of `exp t • ξ + exp (-t) • η` with itself, for unit vectors `ξ, η`. -/
lemma parab_inner_self {n : ℕ} (ξ η : E n) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (t : ℝ) :
    inner ℝ (Real.exp t • ξ + Real.exp (-t) • η) (Real.exp t • ξ + Real.exp (-t) • η)
      = (Real.exp t) ^ 2 + (Real.exp (-t)) ^ 2 + 2 * inner ℝ ξ η := by
  rw [inner_add_left]
  rw [inner_add_right, inner_add_right]
  simp only [real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hξ, hη, real_inner_comm ξ η]
  simp only [mul_one, pow_two]
  have h3 : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h4 : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [show Real.exp (-t) * (Real.exp t * inner ℝ ξ η) = inner ℝ ξ η by
        rw [← mul_assoc, h4, one_mul],
      show Real.exp t * (Real.exp (-t) * inner ℝ ξ η) = inner ℝ ξ η by
        rw [← mul_assoc, h3, one_mul]]
  ring

/-- The inner product of `exp t • ξ + exp (-t) • η` with `ξ`, for unit vectors `ξ, η`. -/
lemma parab_inner_xi {n : ℕ} (ξ η : E n) (hξ : ‖ξ‖ = 1) (_hη : ‖η‖ = 1) (t : ℝ) :
    inner ℝ (Real.exp t • ξ + Real.exp (-t) • η) ξ = Real.exp t + Real.exp (-t) * inner ℝ ξ η := by
  rw [inner_add_left]
  simp only [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hξ,
    one_pow, mul_one]
  rw [show inner ℝ η ξ = inner ℝ ξ η from (real_inner_comm η ξ).symm]

/-- The inner product of `exp t • ξ + exp (-t) • η` with `η`, for unit vectors `ξ, η`. -/
lemma parab_inner_eta {n : ℕ} (ξ η : E n) (_hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (t : ℝ) :
    inner ℝ (Real.exp t • ξ + Real.exp (-t) • η) η = Real.exp t * inner ℝ ξ η + Real.exp (-t) := by
  rw [inner_add_left]
  simp only [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hη,
    one_pow, mul_one]

/-- Chart algebra for the time coordinate: with `a * b = 1`, `q² = (1 - c)/2` and `q ≠ 0`,
`1 + (2q)⁻² (a² + b² + 2c) = (((a + b)/2)/q)²`. -/
lemma parab_key_tpart (a b c q : ℝ) (hab : a * b = 1) (hq : q ^ 2 = (1 - c) / 2) (hq0 : q ≠ 0) :
    1 + ((2 * q)⁻¹) ^ 2 * (a ^ 2 + b ^ 2 + 2 * c) = ((a + b) / 2 / q) ^ 2 := by
  field_simp
  ring_nf
  nlinarith [hab, hq]

/-- Chart algebra for the Busemann function at `ξ`: with `q² = (1 - c)/2`, `(a + b)/2/q - (2q)⁻¹ (a + b c) = q b`. -/
lemma parab_key_diff_xi (a b c q : ℝ) (_hab : a * b = 1) (hq : q ^ 2 = (1 - c) / 2)
    (_hq0 : q ≠ 0) :
    (a + b) / 2 / q - (2 * q)⁻¹ * (a + b * c) = q * b := by
  have h2q : 2 * q ^ 2 = 1 - c := by linarith
  field_simp
  rw [show b * 2 * q ^ 2 = b * (2 * q ^ 2) by ring, h2q]
  ring

/-- Chart algebra for the Busemann function at `η`: with `q² = (1 - c)/2`, `(a + b)/2/q - (2q)⁻¹ (a c + b) = q a`. -/
lemma parab_key_diff_eta (a b c q : ℝ) (_hab : a * b = 1) (hq : q ^ 2 = (1 - c) / 2)
    (_hq0 : q ≠ 0) :
    (a + b) / 2 / q - (2 * q)⁻¹ * (a * c + b) = q * a := by
  have h2q : 2 * q ^ 2 = 1 - c := by linarith
  field_simp
  rw [show a * 2 * q ^ 2 = a * (2 * q ^ 2) by ring, h2q]
  ring

theorem parabGeoPt (n : ℕ) (ξ η : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (hη : η ∈ Submission.Mostow.Sph n) (hne : ξ ≠ η) (t : ℝ) : let q := Real.sqrt ((1 - inner ℝ ξ η) / 2); let u := (2 * q)⁻¹ • (Real.exp t • ξ + Real.exp (-t) • η); Submission.Mostow.tpart u = Real.cosh t / q ∧ Submission.Mostow.busemann ξ u = Real.log q - t ∧ Submission.Mostow.busemann η u = Real.log q + t := by
  dsimp only
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have hηn : ‖η‖ = 1 := (mem_Sph_iff η).mp hη
  -- `ξ ≠ η` with `‖ξ‖ = ‖η‖ = 1` forces `⟪ξ, η⟫ < 1`
  have hclt : inner ℝ ξ η < 1 := by
    have hle : inner ℝ ξ η ≤ 1 := by
      have h := real_inner_le_norm ξ η
      rwa [hξn, hηn, mul_one] at h
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      apply hne
      have hz : inner ℝ (ξ - η) (ξ - η) = 0 := by
        rw [inner_sub_left, inner_sub_right, inner_sub_right,
          real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hξn, hηn]
        rw [show inner ℝ η ξ = inner ℝ ξ η from (real_inner_comm η ξ).symm, h]
        norm_num
      exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  set q : ℝ := Real.sqrt ((1 - inner ℝ ξ η) / 2) with hqdef
  set v : E n := Real.exp t • ξ + Real.exp (-t) • η with hvdef
  set u : E n := (2 * q)⁻¹ • v with hudef
  have hq2 : q ^ 2 = (1 - inner ℝ ξ η) / 2 := by
    rw [hqdef]; exact Real.sq_sqrt (by linarith)
  have hqpos : 0 < q := by rw [hqdef]; exact Real.sqrt_pos.mpr (by linarith)
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hab : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hvv : inner ℝ v v = (Real.exp t) ^ 2 + (Real.exp (-t)) ^ 2 + 2 * inner ℝ ξ η := by
    rw [hvdef]; exact parab_inner_self ξ η hξn hηn t
  have hvxi : inner ℝ v ξ = Real.exp t + Real.exp (-t) * inner ℝ ξ η := by
    rw [hvdef]; exact parab_inner_xi ξ η hξn hηn t
  have hveta : inner ℝ v η = Real.exp t * inner ℝ ξ η + Real.exp (-t) := by
    rw [hvdef]; exact parab_inner_eta ξ η hξn hηn t
  have hiuu : inner ℝ u u = ((2 * q)⁻¹) ^ 2 * inner ℝ v v := by
    rw [hudef, real_inner_smul_left, real_inner_smul_right]
    ring
  have htu : tpart u = Real.sqrt (1 + inner ℝ u u) := by
    rw [tpart, ← real_inner_self_eq_norm_sq u]
  have hkey : 1 + inner ℝ u u = (Real.cosh t / q) ^ 2 := by
    rw [hiuu, hvv, Real.cosh_eq t]
    exact parab_key_tpart (Real.exp t) (Real.exp (-t)) (inner ℝ ξ η) q hab hq2 hqne
  have htpart : tpart u = Real.cosh t / q := by
    rw [htu, hkey, Real.sqrt_sq_eq_abs, abs_of_pos (div_pos (Real.cosh_pos t) hqpos)]
  have hiu_xi : inner ℝ u ξ = (2 * q)⁻¹ * (Real.exp t + Real.exp (-t) * inner ℝ ξ η) := by
    rw [hudef, real_inner_smul_left, hvxi]
  have hiu_eta : inner ℝ u η = (2 * q)⁻¹ * (Real.exp t * inner ℝ ξ η + Real.exp (-t)) := by
    rw [hudef, real_inner_smul_left, hveta]
  have hdiff_xi : tpart u - inner ℝ u ξ = q * Real.exp (-t) := by
    rw [htpart, hiu_xi, Real.cosh_eq t]
    exact parab_key_diff_xi (Real.exp t) (Real.exp (-t)) (inner ℝ ξ η) q hab hq2 hqne
  have hdiff_eta : tpart u - inner ℝ u η = q * Real.exp t := by
    rw [htpart, hiu_eta, Real.cosh_eq t]
    exact parab_key_diff_eta (Real.exp t) (Real.exp (-t)) (inner ℝ ξ η) q hab hq2 hqne
  refine ⟨htpart, ?_, ?_⟩
  · rw [busemann_eq_log, hdiff_xi, Real.log_mul hqne (Real.exp_ne_zero (-t)), Real.log_exp]
    ring
  · rw [busemann_eq_log, hdiff_eta, Real.log_mul hqne (Real.exp_ne_zero t), Real.log_exp]

end Work.Mostow
