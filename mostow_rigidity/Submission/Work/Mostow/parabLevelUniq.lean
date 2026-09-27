import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.poAux

/-!
# Uniqueness of the point with prescribed Busemann levels at two boundary points

For two distinct points `ξ ≠ η` of the boundary sphere, the pair of Busemann functions
`(busemann ξ ·, busemann η ·)` determines a point of `ℍⁿ` uniquely once the two prescribed
values sum appropriately: writing `q = √((1 - ⟪ξ,η⟫)/2)` (so that `q ∈ (0,1]`, and
`‖ξ + η‖² = 4 (1 - q²)`), the only `x` with

`busemann ξ x = log q - t`, `busemann η x = log q + t`

is the point `(2q)⁻¹ • (eᵗ • ξ + e⁻ᵗ • η)` on the hypercycle through `ξ` and `η`.

## Proof

In the chart, `lev ξ x = exp (busemann ξ x) = tpart x - ⟪x,ξ⟫` (this is `exp_busemann`), so the two
hypotheses give

`A := tpart x - ⟪x,ξ⟫ = q e^{-t}`, `B := tpart x - ⟪x,η⟫ = q e^{t}`.

Put `u = eᵗ • ξ + e⁻ᵗ • η`, `u₀ = (2q)⁻¹ • u`, `w = x - u₀` and `σ = tpart x - tpart u₀`.  Direct
expansion (`tpart u₀ = cosh t / q`, from `⟪ξ,η⟫ = 1 - 2q²` and `‖u‖² = (eᵗ+e⁻ᵗ)² - 4q²`) shows the
three identities

`⟪w,ξ⟫ = σ`, `⟪w,η⟫ = σ`, `‖w‖² = σ²`.

Hence `⟪w, ξ+η⟫ = 2σ` and Cauchy–Schwarz together with `‖ξ+η‖² = 4(1-q²)` gives
`4σ² ≤ ‖w‖² ‖ξ+η‖² = 4σ²(1-q²)`, i.e. `4σ²q² ≤ 0`; as `q > 0` this forces `σ = 0`, and then
`‖w‖² = σ² = 0`, so `w = 0` and `x = u₀`.  (The case `ξ = -η`, where `‖ξ+η‖ = 0` and `q = 1`, is
covered by the same argument: Cauchy–Schwarz already yields `2σ = ⟪w,ξ+η⟫ = 0`.)
-/

namespace Work.Mostow

open Submission.Mostow

set_option maxHeartbeats 2000000
open scoped Real

theorem parabLevelUniq (n : ℕ) (ξ η x : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (hη : η ∈ Submission.Mostow.Sph n) (hne : ξ ≠ η) (t : ℝ) (h1 : Submission.Mostow.busemann ξ x = Real.log (Real.sqrt ((1 - inner ℝ ξ η) / 2)) - t) (h2 : Submission.Mostow.busemann η x = Real.log (Real.sqrt ((1 - inner ℝ ξ η) / 2)) + t) : x = (2 * Real.sqrt ((1 - inner ℝ ξ η) / 2))⁻¹ • (Real.exp t • ξ + Real.exp (-t) • η) := by
  set q : ℝ := Real.sqrt ((1 - inner ℝ ξ η) / 2) with hqdef
  have hnsq1 : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have hnsq2 : ‖η‖ = 1 := (mem_Sph_iff η).mp hη
  have hle1 : inner ℝ ξ η ≤ 1 := by
    have h := real_inner_le_norm ξ η
    rw [hnsq1, hnsq2, mul_one] at h
    exact h
  have hlt1 : inner ℝ ξ η < 1 := by
    rcases lt_or_eq_of_le hle1 with h | h
    · exact h
    · exfalso; apply hne
      have hz : ‖ξ - η‖ ^ 2 = 0 := by
        rw [norm_sub_sq_real, hnsq1, hnsq2, h]; norm_num
      have h0 : ‖ξ - η‖ = 0 := sq_eq_zero_iff.mp hz
      exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have hq2 : q ^ 2 = (1 - inner ℝ ξ η) / 2 := by
    rw [hqdef]; exact Real.sq_sqrt (by linarith)
  have hqpos : 0 < q := by
    rw [hqdef]; rw [Real.sqrt_pos]; linarith
  have hA' : tpart x - inner ℝ x ξ = q * Real.exp (-t) := by
    calc tpart x - inner ℝ x ξ = Real.exp (busemann ξ x) := (exp_busemann ξ hξ x).symm
      _ = Real.exp (Real.log q - t) := by rw [h1]
      _ = Real.exp (Real.log q) * Real.exp (-t) := by rw [sub_eq_add_neg, Real.exp_add]
      _ = q * Real.exp (-t) := by rw [Real.exp_log hqpos]
  have hB' : tpart x - inner ℝ x η = q * Real.exp t := by
    calc tpart x - inner ℝ x η = Real.exp (busemann η x) := (exp_busemann η hη x).symm
      _ = Real.exp (Real.log q + t) := by rw [h2]
      _ = Real.exp (Real.log q) * Real.exp t := by rw [Real.exp_add]
      _ = q * Real.exp t := by rw [Real.exp_log hqpos]
  set p : ℝ := tpart x with hpdef
  set s : ℝ := Real.exp t with hsdef
  have hspos : 0 < s := by rw [hsdef]; exact Real.exp_pos t
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hsit : Real.exp (-t) = s⁻¹ := by rw [Real.exp_neg, ← hsdef]
  have h2qpos : 0 < 2 * q := by positivity
  have hA : p - inner ℝ x ξ = q * s⁻¹ := by rw [hA', hsit]
  have hB : p - inner ℝ x η = q * s := hB'
  have hx1 : inner ℝ x ξ = p - q * s⁻¹ := by linarith
  have hx2 : inner ℝ x η = p - q * s := by linarith
  have hpx : ‖x‖ ^ 2 = p ^ 2 - 1 := by
    rw [hpdef]; have := tpart_sq x; linarith
  have hξξ : inner ℝ ξ ξ = 1 := by rw [real_inner_self_eq_norm_sq, hnsq1]; norm_num
  have hηη : inner ℝ η η = 1 := by rw [real_inner_self_eq_norm_sq, hnsq2]; norm_num
  have hξη : inner ℝ ξ η = 1 - 2 * q ^ 2 := by linarith
  set u : E n := s • ξ + s⁻¹ • η with hudef
  have hnormu : ‖u‖ ^ 2 = (s + s⁻¹) ^ 2 - 4 * q ^ 2 := by
    have h1' : ‖s • ξ‖ = s := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos, hnsq1, mul_one]
    have h2' : ‖s⁻¹ • η‖ = s⁻¹ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspos), hnsq2, mul_one]
    have h3' : inner ℝ (s • ξ) (s⁻¹ • η) = 1 - 2 * q ^ 2 := by
      rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hsne, one_mul, hξη]
    rw [hudef, norm_add_sq_real, h1', h2', h3', add_sq]
    nlinarith [mul_inv_cancel₀ hsne]
  have huξ : inner ℝ u ξ = s + s⁻¹ * (1 - 2 * q ^ 2) := by
    rw [hudef, inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_comm ξ η,
        hξξ, hξη, mul_one]
  have huη : inner ℝ u η = s * (1 - 2 * q ^ 2) + s⁻¹ := by
    rw [hudef, inner_add_left, real_inner_smul_left, real_inner_smul_left, hξη, hηη, mul_one]
  set u0 : E n := (2 * q)⁻¹ • u with hu0def
  have hnormu0 : ‖u0‖ ^ 2 = (s + s⁻¹) ^ 2 / (4 * q ^ 2) - 1 := by
    rw [hu0def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h2qpos), mul_pow, inv_pow, hnormu]
    field_simp
    ring
  have htpartu0 : tpart u0 = (s + s⁻¹) / (2 * q) := by
    rw [tpart]
    have hkey : 1 + ‖u0‖ ^ 2 = ((s + s⁻¹) / (2 * q)) ^ 2 := by
      rw [hnormu0]; field_simp; ring
    rw [hkey, Real.sqrt_sq (by positivity)]
  have hu0ξ : inner ℝ u0 ξ = tpart u0 - q * s⁻¹ := by
    rw [hu0def, real_inner_smul_left, huξ, htpartu0]; field_simp; ring
  have hu0η : inner ℝ u0 η = tpart u0 - q * s := by
    rw [hu0def, real_inner_smul_left, huη, htpartu0]; field_simp; ring
  have hxu0 : inner ℝ x u0 = p * tpart u0 - 1 := by
    rw [hu0def, real_inner_smul_right, hudef, inner_add_right, real_inner_smul_right,
        real_inner_smul_right, hx1, hx2, htpartu0]; field_simp; ring
  have hwξ : inner ℝ (x - u0) ξ = p - tpart u0 := by rw [inner_sub_left, hx1, hu0ξ]; ring
  have hwη : inner ℝ (x - u0) η = p - tpart u0 := by rw [inner_sub_left, hx2, hu0η]; ring
  have hu0norm : ‖u0‖ ^ 2 = tpart u0 ^ 2 - 1 := by
    have := tpart_sq u0; linarith
  have hwnorm : ‖x - u0‖ ^ 2 = (p - tpart u0) ^ 2 := by
    rw [norm_sub_sq_real, hpx, hxu0, hu0norm]; ring
  have hsum : inner ℝ (x - u0) (ξ + η) = 2 * (p - tpart u0) := by
    rw [inner_add_right, hwξ, hwη]; ring
  have hnormξη : ‖ξ + η‖ ^ 2 = 4 * (1 - q ^ 2) := by
    rw [norm_add_sq_real, hnsq1, hnsq2, hξη]; ring
  have hcs : (inner ℝ (x - u0) (ξ + η)) ^ 2 ≤ ‖x - u0‖ ^ 2 * ‖ξ + η‖ ^ 2 := by
    have h := abs_real_inner_le_norm (x - u0) (ξ + η)
    have h2 : (inner ℝ (x - u0) (ξ + η)) ^ 2 ≤ (‖x - u0‖ * ‖ξ + η‖) ^ 2 := by
      rw [sq_le_sq]
      rwa [abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc (inner ℝ (x - u0) (ξ + η)) ^ 2 ≤ (‖x - u0‖ * ‖ξ + η‖) ^ 2 := h2
      _ = ‖x - u0‖ ^ 2 * ‖ξ + η‖ ^ 2 := by ring
  have hkey : (p - tpart u0) ^ 2 * (4 * q ^ 2) ≤ 0 := by
    have h := hcs
    rw [hsum, hwnorm, hnormξη] at h
    nlinarith [h]
  have hsq_sigma : (p - tpart u0) ^ 2 = 0 := by
    have h : (p - tpart u0) ^ 2 * (4 * q ^ 2) = 0 := le_antisymm hkey (by positivity)
    exact (mul_eq_zero.mp h).resolve_right (by positivity)
  have hwu : x = u0 := by
    have hnormw : ‖x - u0‖ ^ 2 = 0 := by rw [hwnorm, hsq_sigma]
    have h0 : ‖x - u0‖ = 0 := sq_eq_zero_iff.mp hnormw
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  rw [hwu, hu0def, hudef, ← hsit]

end Work.Mostow
