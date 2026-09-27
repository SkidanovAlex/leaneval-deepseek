import Mathlib
import Submission.Work.Mostow.BaryBase

/-!
# `BaryEquality` (area T4, equality case of the barycentre argument)

Let `y ≠ z` be points of the chart `E n = ℍⁿ`, and suppose `m` satisfies the hyperbolic-midpoint
identity in Busemann form

`tpart m - ⟪m, η⟫ = ((tpart y - ⟪y, η⟫) + (tpart z - ⟪z, η⟫)) / (2 cosh (hdist y z / 2))`
for every `η ∈ Sph n`.

If `ξ ∈ Sph n` satisfies the Busemann equality `2 · busemann ξ m = busemann ξ y + busemann ξ z`,
then `ξ` is one of the four ideal endpoints

`± (e^d z - y)/‖e^d z - y‖`,   `± (e^d y - z)/‖e^d y - z‖`,   `d = hdist y z`.

This is the equality case of the computation used in `convex_midpoint` (see
`Submission/Work/Mostow/barycentre.lean` and `BaryMidpoint.lean`).  The proof runs as follows.
Write `a = tpart y - ⟪y,ξ⟫`, `b = tpart z - ⟪z,ξ⟫`, `A = tpart m - ⟪m,ξ⟫` and `c = e^d`.  The
identity `Real.exp (busemann ξ u) = tpart u - ⟪u,ξ⟫` turns the two hypotheses into

`A = (a + b)/(2 cosh(d/2))`   and   `A ^ 2 = a * b`,

whence `a ^ 2 + b ^ 2 - 2 cosh d · a b = 0`, i.e. `(a - c b)(a - c⁻¹ b) = 0`.  Both roots are
then translated into statements about `ξ` through the Minkowski-null identity

`‖e^d z - y‖ ^ 2 = (e^d tpart z - tpart y) ^ 2`   (and its transpose),

combined with the equality case of Cauchy–Schwarz: a unit vector making the right pairing with
`V` is `±‖V‖⁻¹ • V`.
-/

namespace Work.Mostow

open Submission.Mostow

noncomputable section

/-! Elementary identities used by `BaryEquality`.  Kept in a private namespace so that the names
do not collide with the parallel developments of the same area. -/
namespace BaryEq

variable {n : ℕ}

/-- `hdist` is symmetric (re-proved here to keep the file self-contained). -/
theorem hdist_comm (u v : E n) : hdist u v = hdist v u := by
  rw [hdist, hdist, ← real_inner_comm v u, mul_comm (tpart v)]

/-- The Minkowski-null identity: the lift `(e^d z - y, e^d · tpart z - tpart y)` is a null vector
of the Minkowski form. -/
theorem norm_sq_exp_smul_sub (u v : E n) :
    ‖Real.exp (hdist u v) • v - u‖ ^ 2
      = (Real.exp (hdist u v) * tpart v - tpart u) ^ 2 := by
  set c := Real.exp (hdist u v) with hc
  have hcpos : 0 < c := by rw [hc]; exact Real.exp_pos _
  have hcosh : 2 * Real.cosh (hdist u v) = c + Real.exp (-(hdist u v)) := by
    rw [Real.cosh_eq, ← hc, Real.exp_neg]; ring
  have hce : c * Real.exp (-(hdist u v)) = 1 := by
    rw [hc, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hkey : c ^ 2 - 2 * c * Real.cosh (hdist u v) + 1 = 0 := by
    have h : 2 * c * Real.cosh (hdist u v) = c ^ 2 + 1 := by
      have h2 : 2 * c * Real.cosh (hdist u v) = c * (2 * Real.cosh (hdist u v)) := by ring
      rw [h2, hcosh, mul_add, hce]; ring
    linarith
  have hu : ‖u‖ ^ 2 = tpart u ^ 2 - 1 := by linarith [tpart_sq u]
  have hv : ‖v‖ ^ 2 = tpart v ^ 2 - 1 := by linarith [tpart_sq v]
  have hin : inner ℝ u v = tpart u * tpart v - Real.cosh (hdist u v) := by
    have h := cosh_hdist u v; linarith
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, real_inner_smul_left,
    ← real_inner_comm v u, mul_pow, hv, hu, hin]
  nlinarith [hkey]

/-- `e^{hdist u v} v - u` vanishes exactly when `u = v`. -/
theorem exp_smul_sub_ne_zero (u v : E n) :
    Real.exp (hdist u v) • v - u ≠ 0 ↔ u ≠ v := by
  constructor
  · intro h0 huv
    rw [huv] at h0
    exact h0 (by rw [hdist_self, Real.exp_zero, one_smul, sub_self])
  · intro huv h0
    set c := Real.exp (hdist u v) with hc
    have hcv : c • v = u := by
      have : c • v - u = 0 := h0
      exact sub_eq_zero.mp this
    have ht : tpart u = c * tpart v := by
      have hnorm : ‖c • v - u‖ ^ 2 = (c * tpart v - tpart u) ^ 2 := by
        rw [hc]; exact norm_sq_exp_smul_sub u v
      rw [hcv, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hnorm
      have := sq_eq_zero_iff.mp hnorm.symm
      linarith
    have hnormu : ‖u‖ = c * ‖v‖ := by
      rw [← hcv, norm_smul, Real.norm_eq_abs, abs_of_pos (by rw [hc]; exact Real.exp_pos _)]
    have h1 : ‖u‖ ^ 2 = c ^ 2 * ‖v‖ ^ 2 := by rw [hnormu]; ring
    have h2 : tpart u ^ 2 = c ^ 2 * tpart v ^ 2 := by rw [ht]; ring
    have h3 : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := tpart_sq u
    have h4 : tpart v ^ 2 = 1 + ‖v‖ ^ 2 := tpart_sq v
    have hc2 : c ^ 2 = 1 := by nlinarith [h1, h2, h3, h4]
    have hcpos : 0 < c := by rw [hc]; exact Real.exp_pos _
    have hc1 : c = 1 := by
      rcases sq_eq_one_iff.mp hc2 with h | h
      · exact h
      · rw [h] at hcpos; linarith
    exact huv (by rw [← hcv, hc1, one_smul])

/-- Equality case of Cauchy–Schwarz for a unit vector: if `⟪V,ξ⟫ ^ 2 = ‖V‖ ^ 2`, `‖ξ‖ = 1` and
`V ≠ 0`, then `ξ = ±‖V‖⁻¹ • V`. -/
theorem eq_or_neg_eq_inv_norm_smul (V ξ : E n) (hV : V ≠ 0) (hξ : ‖ξ‖ = 1)
    (h : (inner ℝ V ξ) ^ 2 = ‖V‖ ^ 2) :
    ξ = ‖V‖⁻¹ • V ∨ ξ = -(‖V‖⁻¹ • V) := by
  have hVn : ‖V‖ ≠ 0 := norm_ne_zero_iff.mpr hV
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with hh | hh
  · left
    have hmul : inner ℝ V ξ = ‖V‖ * ‖ξ‖ := by rw [hξ, mul_one]; exact hh
    have hsm : ‖V‖ • ξ = V := by
      have h' := (inner_eq_norm_mul_iff (𝕜 := ℝ) (x := V) (y := ξ)).mp hmul
      simpa [hξ] using h'.symm
    exact (eq_inv_smul_iff₀ hVn).mpr hsm
  · right
    have hneg : inner ℝ V (-ξ) = ‖V‖ := by rw [inner_neg_right, hh, neg_neg]
    have hmul : inner ℝ V (-ξ) = ‖V‖ * ‖-ξ‖ := by rw [norm_neg, hξ, mul_one]; exact hneg
    have hsm : ‖V‖ • (-ξ) = V := by
      have h' := (inner_eq_norm_mul_iff (𝕜 := ℝ) (x := V) (y := -ξ)).mp hmul
      simpa [norm_neg, hξ] using h'.symm
    have hthis : -ξ = ‖V‖⁻¹ • V := (eq_inv_smul_iff₀ hVn).mpr hsm
    rw [← hthis, neg_neg]

end BaryEq

theorem BaryEquality (n : ℕ) (y z m : Submission.Mostow.E n) (hyz : y ≠ z)
    (hW : Real.exp (Submission.Mostow.hdist y z) • z - y ≠ 0)
    (hm : ∀ η ∈ Submission.Mostow.Sph n, Submission.Mostow.tpart m - inner ℝ m η =
      ((Submission.Mostow.tpart y - inner ℝ y η) + (Submission.Mostow.tpart z - inner ℝ z η)) /
        (2 * Real.cosh (Submission.Mostow.hdist y z / 2)))
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (h : 2 * Submission.Mostow.busemann ξ m = Submission.Mostow.busemann ξ y + Submission.Mostow.busemann ξ z) :
    ξ = (‖Real.exp (Submission.Mostow.hdist y z) • z - y‖)⁻¹ • (Real.exp (Submission.Mostow.hdist y z) • z - y) ∨
    ξ = -((‖Real.exp (Submission.Mostow.hdist y z) • z - y‖)⁻¹ • (Real.exp (Submission.Mostow.hdist y z) • z - y)) ∨
    ξ = (‖Real.exp (Submission.Mostow.hdist y z) • y - z‖)⁻¹ • (Real.exp (Submission.Mostow.hdist y z) • y - z) ∨
    ξ = -((‖Real.exp (Submission.Mostow.hdist y z) • y - z‖)⁻¹ • (Real.exp (Submission.Mostow.hdist y z) • y - z)) := by
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  set c := Real.exp (hdist y z) with hc
  have hcne : c ≠ 0 := by rw [hc]; exact Real.exp_ne_zero _
  set a := tpart y - inner ℝ y ξ with ha
  set b := tpart z - inner ℝ z ξ with hb
  -- the midpoint identity at `ξ`, in terms of `a`, `b`
  have hmξ : tpart m - inner ℝ m ξ = (a + b) / (2 * Real.cosh (hdist y z / 2)) := by
    have hh := hm ξ hξ
    rw [← ha, ← hb] at hh
    exact hh
  -- the Busemann equality at `ξ`, exponentiated
  have hA2 : (tpart m - inner ℝ m ξ) ^ 2 = a * b := by
    have hL : Real.exp (2 * busemann ξ m) = (tpart m - inner ℝ m ξ) ^ 2 := by
      rw [show (2 : ℝ) * busemann ξ m = busemann ξ m + busemann ξ m from by ring, Real.exp_add,
        exp_busemann ξ hξ m]
      ring
    have hR : Real.exp (busemann ξ y + busemann ξ z) = a * b := by
      rw [Real.exp_add, exp_busemann ξ hξ y, exp_busemann ξ hξ z, ← ha, ← hb]
    rw [h] at hL
    rw [← hL, hR]
  -- hence the quadratic relation `a² + b² - 2 cosh d · ab = 0`
  have hquad : a ^ 2 + b ^ 2 - 2 * Real.cosh (hdist y z) * (a * b) = 0 := by
    have h2C : (2 * Real.cosh (hdist y z / 2)) ^ 2 = 2 + 2 * Real.cosh (hdist y z) := by
      have hh2 := Real.cosh_two_mul (hdist y z / 2)
      rw [show 2 * (hdist y z / 2) = hdist y z from by ring, Real.sinh_sq] at hh2
      nlinarith [hh2]
    have hsq : (a + b) ^ 2 = (2 + 2 * Real.cosh (hdist y z)) * (a * b) := by
      have hh := hA2
      rw [hmξ, div_pow] at hh
      rw [div_eq_iff (by positivity : (2 * Real.cosh (hdist y z / 2)) ^ 2 ≠ 0)] at hh
      rw [h2C, mul_comm] at hh
      exact hh
    nlinarith [hsq]
  -- which factors as `(a - c b)(a - c⁻¹ b) = 0`
  have hfac : (a - c * b) * (a - c⁻¹ * b) = 0 := by
    have h2cosh : 2 * Real.cosh (hdist y z) = c + c⁻¹ := by
      rw [Real.cosh_eq, Real.exp_neg, ← hc]; ring
    have hq : a ^ 2 + b ^ 2 - (c + c⁻¹) * (a * b) = 0 := by
      rw [← h2cosh]; linarith [hquad]
    have hid : (a - c * b) * (a - c⁻¹ * b) = a ^ 2 + b ^ 2 - (c + c⁻¹) * (a * b) := by
      calc (a - c * b) * (a - c⁻¹ * b)
          = a ^ 2 + b ^ 2 - (c + c⁻¹) * (a * b) + (c * c⁻¹ - 1) * b ^ 2 := by ring
        _ = a ^ 2 + b ^ 2 - (c + c⁻¹) * (a * b) := by rw [mul_inv_cancel₀ hcne]; ring
    rw [hid, hq]
  rcases mul_eq_zero.mp hfac with hcase | hcase
  · -- `a = c b`: the ideal point is `-‖e^d z - y‖⁻¹ • (e^d z - y)` up to sign
    have hab : a = c * b := by linarith [hcase]
    have hinner : inner ℝ (c • z - y) ξ = c * tpart z - tpart y := by
      rw [ha, hb] at hab
      rw [inner_sub_left, real_inner_smul_left]
      linarith [hab]
    have hVnorm : ‖c • z - y‖ ^ 2 = (c * tpart z - tpart y) ^ 2 := by
      rw [hc]; exact BaryEq.norm_sq_exp_smul_sub y z
    have hVne : c • z - y ≠ 0 := by rw [hc]; exact hW
    have hsq : (inner ℝ (c • z - y) ξ) ^ 2 = ‖c • z - y‖ ^ 2 := by rw [hinner, hVnorm]
    rcases BaryEq.eq_or_neg_eq_inv_norm_smul (c • z - y) ξ hVne hξn hsq with hh | hh
    · left; rw [hh, hc]
    · right; left; rw [hh, hc]
  · -- `a = c⁻¹ b`: the ideal point is `±‖e^d y - z‖⁻¹ • (e^d y - z)`
    have hab : c * a = b := by
      have h1 : c * a = c * (c⁻¹ * b) := by
        congr 1
        rw [ha, hb] at hcase
        linarith [hcase]
      rw [← mul_assoc, mul_inv_cancel₀ hcne, one_mul] at h1
      exact h1
    have hinner : inner ℝ (c • y - z) ξ = c * tpart y - tpart z := by
      rw [ha, hb] at hab
      rw [inner_sub_left, real_inner_smul_left]
      linarith [hab]
    have hVnorm : ‖c • y - z‖ ^ 2 = (c * tpart y - tpart z) ^ 2 := by
      rw [hc, BaryEq.hdist_comm y z]; exact BaryEq.norm_sq_exp_smul_sub z y
    have hVne : c • y - z ≠ 0 := by
      rw [hc, BaryEq.hdist_comm y z]
      exact (BaryEq.exp_smul_sub_ne_zero z y).mpr (Ne.symm hyz)
    have hsq : (inner ℝ (c • y - z) ξ) ^ 2 = ‖c • y - z‖ ^ 2 := by rw [hinner, hVnorm]
    rcases BaryEq.eq_or_neg_eq_inv_norm_smul (c • y - z) ξ hVne hξn hsq with hh | hh
    · right; right; left; rw [hh, hc]
    · right; right; right; rw [hh, hc]

end

end Work.Mostow
