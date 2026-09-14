import Submission.NBody.LYZGeometry
import Mathlib

/-!
# The collision-free cone around the asymptotic direction

This module formalises Liu--Yan--Zhou's Lemma 3.4 (`cofree`): if `a` is collision free with
pairwise separation `ν`, `x* = x + s • a` with `s` large compared with `‖x‖_[m]/ν`, and `b` is a
unit vector with `‖b - a‖_[m] ≤ θ` small (in the mass norm), then the whole ray `x* + ℝ₊ b` is
collision free.

The two ingredients are `findxast_euclidean` (the *Euclidean* form of Liu--Yan--Zhou's Lemma 2.2
(1), which is needed because the separation `ν` is measured by the *Euclidean* pair distances
while the direction estimates are measured in the mass norm) and `separated_add_smul_of_close_direction`
(Lemma 2.4).
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Euclidean form of Liu--Yan--Zhou's Lemma 2.2 (1).**  If `‖a‖_[m] = 1` and `s` is large
compared with `K ‖x‖_[m] / ν` (where `K` bounds the Euclidean norm by the mass norm), then the
direction of `x + s • a` is within `ν/20` of `a` *in the Euclidean norm*. -/
lemma findxast_euclidean {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {x a : EN E N} {ν s K : ℝ}
    (hK : 0 < K) (hKn : ∀ y : EN E N, ‖y‖ ≤ K * ‖y‖_[m])
    (hν : 0 < ν) (ha : ‖a‖_[m] = 1) (hs0 : 0 < s)
    (hs : ‖x‖_[m] + 40 * K * ‖x‖_[m] / ν ≤ s) :
    ‖(‖x + s • a‖_[m])⁻¹ • (x + s • a) - a‖ ≤ ν / 20 := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hx0 : 0 ≤ ‖x‖_[m] := weightedNorm_nonneg m x
  have hlow : s - ‖x‖_[m] ≤ ‖x + s • a‖_[m] := by
    have h := weightedNorm_add_le hm0 (-x) (x + s • a)
    have h2 : (-x) + (x + s • a) = s • a := by rw [neg_add_cancel_left]
    rw [h2, weightedNorm_smul hm0 s a, ha, mul_one, abs_of_pos hs0] at h
    have h3 : ‖-x‖_[m] = ‖x‖_[m] := by
      have h4 : (-x : EN E N) = (-1 : ℝ) • x := by simp
      rw [h4]
      simpa using weightedNorm_smul hm0 (-1) x
    rw [h3] at h
    linarith
  have hupper : ‖x + s • a‖_[m] ≤ s + ‖x‖_[m] := by
    calc ‖x + s • a‖_[m] ≤ ‖x‖_[m] + ‖s • a‖_[m] := weightedNorm_add_le hm0 _ _
      _ = ‖x‖_[m] + s := by rw [weightedNorm_smul hm0 s a, ha, mul_one, abs_of_pos hs0]
      _ = s + ‖x‖_[m] := by ring
  have hdiff : ‖x + s • a - ‖x + s • a‖_[m] • a‖ ≤ 2 * K * ‖x‖_[m] := by
    have han : ‖a‖ ≤ K := by
      have h := hKn a
      rwa [ha, mul_one] at h
    have habs : |s - ‖x + s • a‖_[m]| ≤ ‖x‖_[m] := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
    have h1 : x + s • a - ‖x + s • a‖_[m] • a = x + (s - ‖x + s • a‖_[m]) • a := by module
    rw [h1]
    calc ‖x + (s - ‖x + s • a‖_[m]) • a‖
        ≤ ‖x‖ + ‖(s - ‖x + s • a‖_[m]) • a‖ := norm_add_le _ _
      _ = ‖x‖ + |s - ‖x + s • a‖_[m]| * ‖a‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ K * ‖x‖_[m] + ‖x‖_[m] * K := by
          have hxK : ‖x‖ ≤ K * ‖x‖_[m] := hKn x
          have h4 : |s - ‖x + s • a‖_[m]| * ‖a‖ ≤ ‖x‖_[m] * K :=
            mul_le_mul habs han (norm_nonneg _) hx0
          linarith
      _ = 2 * K * ‖x‖_[m] := by ring
  rcases eq_or_lt_of_le hx0 with hx | hx
  · have hxzero : x = 0 := (weightedNorm_eq_zero_iff hm x).mp hx.symm
    subst hxzero
    rw [zero_add]
    have hz : (‖s • a‖_[m])⁻¹ • (s • a) - a = 0 := by
      rw [weightedNorm_smul hm0 s a, ha, mul_one, abs_of_pos hs0, smul_smul,
        inv_mul_cancel₀ (ne_of_gt hs0), one_smul, sub_self]
    rw [hz, norm_zero]
    positivity
  · have hden : 0 < ‖x + s • a‖_[m] := by
      have h1 : 40 * K * ‖x‖_[m] / ν ≤ s - ‖x‖_[m] := by linarith
      have h3 : 0 < 40 * K * ‖x‖_[m] / ν := by positivity
      linarith
    have hsplit : (‖x + s • a‖_[m])⁻¹ • (x + s • a) - a
        = (‖x + s • a‖_[m])⁻¹ • (x + s • a - ‖x + s • a‖_[m] • a) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hden), one_smul]
    rw [hsplit, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden)]
    have hden2 : 40 * K * ‖x‖_[m] / ν ≤ ‖x + s • a‖_[m] := by linarith
    have hpos : 0 < 40 * K * ‖x‖_[m] / ν := by positivity
    calc (‖x + s • a‖_[m])⁻¹ * ‖x + s • a - ‖x + s • a‖_[m] • a‖
        ≤ (‖x + s • a‖_[m])⁻¹ * (2 * K * ‖x‖_[m]) :=
          mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hden.le)
      _ ≤ (40 * K * ‖x‖_[m] / ν)⁻¹ * (2 * K * ‖x‖_[m]) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact inv_anti₀ (by positivity) hden2
      _ = ν / 20 := by
          rw [inv_div]
          field_simp
          ring

/-- **Liu--Yan--Zhou's Lemma 3.4 (`cofree`), separation form.**  Under the hypotheses of
`withoutCollisions_cone_ray` the whole ray `x* + ℝ≥0 • b` is in fact `(9/10) ν`-separated. -/
theorem separated_cone_ray {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {K ν s θ : ℝ}
    (hK : 0 < K) (hKn : ∀ y : EN E N, ‖y‖ ≤ K * ‖y‖_[m])
    (hν : 0 < ν) {x a b : EN E N} (hsep : Separated a ν) (ha : ‖a‖_[m] = 1)
    (hb : ‖b‖_[m] = 1) (hθ0 : 0 ≤ θ) (hba : ‖b - a‖_[m] ≤ θ)
    (hcone : K * θ ≤ ν / 16)
    (hs0 : 1 ≤ s) (hs : ‖x‖_[m] + 40 * K * ‖x‖_[m] / ν ≤ s)
    (hs2 : 50 * K * ‖x‖_[m] / ν ≤ s) :
    ∀ t : ℝ, 0 ≤ t → Separated ((x + s • a) + t • b) ((9:ℝ) / 10 * ν) := by
  have hs0' : 0 < s := lt_of_lt_of_le one_pos hs0
  have hx0 : 0 ≤ ‖x‖_[m] := weightedNorm_nonneg m x
  have hdir := findxast_euclidean hm hK hKn hν ha hs0' hs
  have hznorm : 0 < ‖x + s • a‖_[m] := by
    have hlow : s - ‖x‖_[m] ≤ ‖x + s • a‖_[m] := by
      have h := weightedNorm_add_le (fun i => (hm i).le) (-x) (x + s • a)
      have h2 : (-x) + (x + s • a) = s • a := by rw [neg_add_cancel_left]
      rw [h2, weightedNorm_smul (fun i => (hm i).le) s a, ha, mul_one, abs_of_pos hs0'] at h
      have h3 : ‖-x‖_[m] = ‖x‖_[m] := by
        have h4 : (-x : EN E N) = (-1 : ℝ) • x := by simp
        rw [h4]
        simpa using weightedNorm_smul (fun i => (hm i).le) (-1) x
      rw [h3] at h
      linarith
    have hspos : 0 < s - ‖x‖_[m] := by
      rcases eq_or_lt_of_le hx0 with hx | hx
      · rw [← hx, sub_zero]; exact hs0'
      · have h4 : 0 < 40 * K := by positivity
        have h5 : 0 < 40 * K * ‖x‖_[m] := mul_pos h4 hx
        have h6 : 0 < 40 * K * ‖x‖_[m] / ν := div_pos h5 hν
        linarith
    linarith
  have hzdist : dist ((‖x + s • a‖_[m])⁻¹ • (x + s • a)) a ≤ (1 / 20) * ν := by
    rw [dist_eq_norm]
    have h := hdir
    rw [show ν / 20 = (1:ℝ) / 20 * ν by ring] at h
    exact h
  have hcdsep : Separated ((‖x + s • a‖_[m])⁻¹ • (x + s • a)) ((9:ℝ) / 10 * ν) := by
    have h := Separated.of_dist_le hsep hzdist
    have he : ν - 2 * ((1 / 20) * ν) = (9:ℝ) / 10 * ν := by ring
    rwa [he] at h
  have hzsep : Separated (x + s • a) ((9:ℝ) / 10 * ν) := by
    have h := findxast_separated hK hKn hν hsep hs2
    refine h.mono ?_
    have h2 : (9:ℝ) / 10 * ν ≤ (24 / 25) * s * ν := by nlinarith [hν, hs0]
    exact h2
  have hbd : dist b ((‖x + s • a‖_[m])⁻¹ • (x + s • a)) ≤ (1 / 8) * ((9:ℝ) / 10 * ν) := by
    have h1 : dist b ((‖x + s • a‖_[m])⁻¹ • (x + s • a))
        ≤ dist b a + dist a ((‖x + s • a‖_[m])⁻¹ • (x + s • a)) := dist_triangle _ _ _
    have h2 : dist b a ≤ K * θ := by
      rw [dist_eq_norm]
      exact (hKn (b - a)).trans (mul_le_mul_of_nonneg_left hba hK.le)
    have h3 : dist a ((‖x + s • a‖_[m])⁻¹ • (x + s • a)) ≤ (1 / 20) * ν := by
      rw [dist_comm]; exact hzdist
    linarith
  intro t ht
  exact separated_add_smul_of_close_direction (m := m) (z := x + s • a) (b := b)
    (ν := (9:ℝ) / 10 * ν) (δ := 1 / 8) hzsep hznorm (by positivity) (by norm_num) hcdsep hbd ht

/-- **Liu--Yan--Zhou's Lemma 3.4 (`cofree`).**  Let `a` be collision free with pairwise separation
`ν`, let `‖a‖_[m] = 1`, and let `x* = x + s • a` with `s` large compared with `K ‖x‖_[m]/ν` (where
`K` bounds the Euclidean norm by the mass norm).  If `b` is a unit vector with `‖b - a‖_[m] ≤ θ`
where `θ` is small enough that `K θ ≤ ν/16`, then the whole ray `x* + ℝ≥0 • b` is collision free. -/
theorem withoutCollisions_cone_ray {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {K ν s θ : ℝ}
    (hK : 0 < K) (hKn : ∀ y : EN E N, ‖y‖ ≤ K * ‖y‖_[m])
    (hν : 0 < ν) {x a b : EN E N} (hsep : Separated a ν) (ha : ‖a‖_[m] = 1)
    (hb : ‖b‖_[m] = 1) (hθ0 : 0 ≤ θ) (hba : ‖b - a‖_[m] ≤ θ)
    (hcone : K * θ ≤ ν / 16)
    (hs0 : 1 ≤ s) (hs : ‖x‖_[m] + 40 * K * ‖x‖_[m] / ν ≤ s)
    (hs2 : 50 * K * ‖x‖_[m] / ν ≤ s) :
    ∀ t : ℝ, 0 ≤ t → WithoutCollisions ((x + s • a) + t • b) := by
  intro t ht i j hij
  have h2 : (0:ℝ) < (9:ℝ) / 10 * ν := by positivity
  exact ne_of_gt (lt_of_lt_of_le h2
    (separated_cone_ray hm hK hKn hν hsep ha hb hθ0 hba hcone hs0 hs hs2 t ht i j hij))

end Submission.NBody
