import Mathlib
import Submission.Work.C17I.defs

namespace Work.C17I

open Polynomial

noncomputable section

/-!
# The four roots of the quartic `Q4x (aOf m) (aOf n)`, and `P2x ≠ 0` on the stadium

This module proves `Work.C17I.q4x_roots`, the localisation input R3 of the continuation of
`P ∘ φ` to the stadium `Sset m n` (`Work.C17I.pw_continuation`).

**Mathematical content.**  For `a = 2m+1`, `b = 2n+1` the quartic

`Q4x a b = 1 − 4ab X + (4a²+4b²−2) X² − 4ab X³ + X⁴`

is the polynomial whose roots are the four singularities `(a ± √(a²−1))(b ± √(b²−1))` of the
paper's equation (ODE).  In terms of the root parameters `sqP t = (√(t+1)+√t)²`,
`sqM t = (√(t+1)−√t)² = (sqP t)⁻¹` of `Submission.CDT.LocationSing` these four numbers are

`sqP m · sqP n`, `sqP m · sqM n`, `sqM m · sqP n`, `sqM m · sqM n`.

The proof is the Newton identity `e₁ = 4ab`, `e₂ = 4a²+4b²−2`, `e₃ = 4ab`, `e₄ = 1` for the four
roots, obtained from the two relations `sqP t + sqM t = 2(2t+1)` and `sqP t · sqM t = 1` (the
first is elementary, the second is `Submission.CDT.LocationSing.sqP_mul_sqM`).  No square roots
occur in the final identity: it is the polynomial identity

`1 − (p+q)(r+s) X + ((p+q)² + (r+s)² − 2) X² − (p+q)(r+s) X³ + X⁴ = (X−pr)(X−ps)(X−qr)(X−qs)`

for `pq = rs = 1`, which is proved by clearing denominators.

**Consequence for `P2x`.**  `P2x = (X−1)·X·(X+1)·Q4x`.  On a point `z` of the stadium
(`‖z‖ < 1`, `Re z ≥ 1/5`, `z ≠ 1/2`) the inverted coordinate `w = φ z = z/(z−1)` satisfies
`w ∉ {0, 1, −1}` (from `z ∉ {0, 1, 1/2}`) and `w` is never one of the four positive real roots
(if `w = p > 0` were real then `z = φ w = p/(p−1)` is real and either `< 0` — contradicting
`Re z ≥ 1/5` — or `> 1` — contradicting `‖z‖ < 1`).  Hence `P2x(φ z) ≠ 0`, which is exactly the
non-vanishing hypothesis needed to divide by `pp2` in the pullback of the ODE.
-/

/-! ## 1. The elementary relations between `sqP` and `sqM` -/

/-- `sqP t + sqM t = 2(2t+1) = 2a` for `a = 2t+1`: the two root parameters are the two roots of
`X² − 2aX + 1`. -/
private lemma sqP_add_sqM_aux (t : ℝ) (ht : 0 ≤ t) :
    Submission.CDT.LocationSing.sqP t + Submission.CDT.LocationSing.sqM t = 2 * (2 * t + 1) := by
  have h1 : (Real.sqrt (t + 1)) ^ 2 = t + 1 := Real.sq_sqrt (by linarith)
  have h2 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
  unfold Submission.CDT.LocationSing.sqP Submission.CDT.LocationSing.sqM
  nlinarith [h1, h2]

/-! ## 2. The quartic with four prescribed roots -/

/-- If `p + q = 2a`, `pq = 1`, `r + s = 2b`, `rs = 1` then
`1 − 4ab X + (4a²+4b²−2) X² − 4ab X³ + X⁴ = (X−pr)(X−ps)(X−qr)(X−qs)`. -/
private lemma quartic_prod_aux (a b sP sM tP tM : ℝ)
    (ha : a = (sP + sM) / 2) (hb : b = (tP + tM) / 2)
    (h1 : sP * sM = 1) (h2 : tP * tM = 1) :
    (1 - Polynomial.C (4 * a * b) * Polynomial.X
        + Polynomial.C (4 * a ^ 2 + 4 * b ^ 2 - 2) * Polynomial.X ^ 2
        - Polynomial.C (4 * a * b) * Polynomial.X ^ 3 + Polynomial.X ^ 4 : Polynomial ℝ)
      = (Polynomial.X - Polynomial.C (sP * tP)) * (Polynomial.X - Polynomial.C (sP * tM))
        * (Polynomial.X - Polynomial.C (sM * tP)) * (Polynomial.X - Polynomial.C (sM * tM)) := by
  subst ha; subst hb
  have hs : sP ≠ 0 := by rintro rfl; norm_num at h1
  have ht : tP ≠ 0 := by rintro rfl; norm_num at h2
  have hsM : sM = 1 / sP := (eq_div_iff hs).mpr (by rw [mul_comm]; exact h1)
  have htM : tM = 1 / tP := (eq_div_iff ht).mpr (by rw [mul_comm]; exact h2)
  subst hsM; subst htM
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  field_simp
  ring

/-- `Q4x (aOf m) (aOf n)`, as a polynomial over `ℝ`, is the product of the four linear factors
`X − sqP m·sqP n`, `X − sqP m·sqM n`, `X − sqM m·sqP n`, `X − sqM m·sqM n`. -/
private lemma Q4x_map_eq_prod_real (m n : ℕ) :
    (Work.C17.Q4x (Work.C17.aOf m) (Work.C17.aOf n)).map (algebraMap ℚ ℝ)
      = (Polynomial.X - Polynomial.C (Submission.CDT.LocationSing.sqP (m : ℝ) * Submission.CDT.LocationSing.sqP (n : ℝ)))
        * (Polynomial.X - Polynomial.C (Submission.CDT.LocationSing.sqP (m : ℝ) * Submission.CDT.LocationSing.sqM (n : ℝ)))
        * (Polynomial.X - Polynomial.C (Submission.CDT.LocationSing.sqM (m : ℝ) * Submission.CDT.LocationSing.sqP (n : ℝ)))
        * (Polynomial.X - Polynomial.C (Submission.CDT.LocationSing.sqM (m : ℝ) * Submission.CDT.LocationSing.sqM (n : ℝ))) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha : (((Work.C17.aOf m : ℚ)) : ℝ)
      = (Submission.CDT.LocationSing.sqP (m : ℝ) + Submission.CDT.LocationSing.sqM (m : ℝ)) / 2 := by
    rw [Work.C17.aOf_cast, sqP_add_sqM_aux m hm]; ring
  have hb : (((Work.C17.aOf n : ℚ)) : ℝ)
      = (Submission.CDT.LocationSing.sqP (n : ℝ) + Submission.CDT.LocationSing.sqM (n : ℝ)) / 2 := by
    rw [Work.C17.aOf_cast, sqP_add_sqM_aux n hn]; ring
  have h1 : Submission.CDT.LocationSing.sqP (m : ℝ) * Submission.CDT.LocationSing.sqM (m : ℝ) = 1 :=
    Submission.CDT.LocationSing.sqP_mul_sqM _ hm
  have h2 : Submission.CDT.LocationSing.sqP (n : ℝ) * Submission.CDT.LocationSing.sqM (n : ℝ) = 1 :=
    Submission.CDT.LocationSing.sqP_mul_sqM _ hn
  have hgen := quartic_prod_aux (((Work.C17.aOf m : ℚ)) : ℝ) (((Work.C17.aOf n : ℚ)) : ℝ)
    (Submission.CDT.LocationSing.sqP (m : ℝ)) (Submission.CDT.LocationSing.sqM (m : ℝ))
    (Submission.CDT.LocationSing.sqP (n : ℝ)) (Submission.CDT.LocationSing.sqM (n : ℝ)) ha hb h1 h2
  have hQ : (Work.C17.Q4x (Work.C17.aOf m) (Work.C17.aOf n)).map (algebraMap ℚ ℝ)
      = (1 - Polynomial.C (4 * (((Work.C17.aOf m : ℚ) : ℝ)) * (((Work.C17.aOf n : ℚ) : ℝ))) * Polynomial.X
          + Polynomial.C (4 * (((Work.C17.aOf m : ℚ) : ℝ)) ^ 2 + 4 * (((Work.C17.aOf n : ℚ) : ℝ)) ^ 2 - 2) * Polynomial.X ^ 2
          - Polynomial.C (4 * (((Work.C17.aOf m : ℚ) : ℝ)) * (((Work.C17.aOf n : ℚ) : ℝ))) * Polynomial.X ^ 3
          + Polynomial.X ^ 4 : Polynomial ℝ) := by
    have h1' : (algebraMap ℚ ℝ) (4 * Work.C17.aOf m * Work.C17.aOf n)
        = 4 * (((Work.C17.aOf m : ℚ) : ℝ)) * (((Work.C17.aOf n : ℚ) : ℝ)) := by simp
    have h2' : (algebraMap ℚ ℝ) (4 * Work.C17.aOf m ^ 2 + 4 * Work.C17.aOf n ^ 2 - 2)
        = 4 * (((Work.C17.aOf m : ℚ) : ℝ)) ^ 2 + 4 * (((Work.C17.aOf n : ℚ) : ℝ)) ^ 2 - 2 := by simp
    rw [Work.C17.Q4x]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_one, Polynomial.map_C, Polynomial.map_X]
    rw [h1', h2']
  rw [hQ]
  exact hgen

/-- The same factorisation over `ℂ`. -/
private lemma Q4x_map_eq_prod (m n : ℕ) :
    (Work.C17.Q4x (Work.C17.aOf m) (Work.C17.aOf n)).map (algebraMap ℚ ℂ)
      = (Polynomial.X - Polynomial.C (((Submission.CDT.LocationSing.sqP (m : ℝ) * Submission.CDT.LocationSing.sqP (n : ℝ) : ℝ) : ℂ)))
        * (Polynomial.X - Polynomial.C (((Submission.CDT.LocationSing.sqP (m : ℝ) * Submission.CDT.LocationSing.sqM (n : ℝ) : ℝ) : ℂ)))
        * (Polynomial.X - Polynomial.C (((Submission.CDT.LocationSing.sqM (m : ℝ) * Submission.CDT.LocationSing.sqP (n : ℝ) : ℝ) : ℂ)))
        * (Polynomial.X - Polynomial.C (((Submission.CDT.LocationSing.sqM (m : ℝ) * Submission.CDT.LocationSing.sqM (n : ℝ) : ℝ) : ℂ))) := by
  have hR := Q4x_map_eq_prod_real m n
  have h := congrArg (Polynomial.map (algebraMap ℝ ℂ)) hR
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℚ ℝ ℂ] at h
  rw [h]
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X]
  rfl

/-- **The roots of the quartic.**  For all `m n : ℕ` the complex roots of
`Q4x (aOf m) (aOf n)` are exactly the four numbers `sqP m·sqP n`, `sqP m·sqM n`,
`sqM m·sqP n`, `sqM m·sqM n`. -/
private lemma Q4x_roots_iff (m n : ℕ) (w : ℂ) :
    (Work.C17.Q4x (Work.C17.aOf m) (Work.C17.aOf n)).eval₂ (algebraMap ℚ ℂ) w = 0 ↔
      w = (((Submission.CDT.LocationSing.sqP (m : ℝ) * Submission.CDT.LocationSing.sqP (n : ℝ) : ℝ)) : ℂ) ∨
      w = (((Submission.CDT.LocationSing.sqP (m : ℝ) * Submission.CDT.LocationSing.sqM (n : ℝ) : ℝ)) : ℂ) ∨
      w = (((Submission.CDT.LocationSing.sqM (m : ℝ) * Submission.CDT.LocationSing.sqP (n : ℝ) : ℝ)) : ℂ) ∨
      w = (((Submission.CDT.LocationSing.sqM (m : ℝ) * Submission.CDT.LocationSing.sqM (n : ℝ) : ℝ)) : ℂ) := by
  rw [Polynomial.eval₂_eq_eval_map, Q4x_map_eq_prod m n]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  constructor
  · intro h
    simp only [mul_eq_zero, sub_eq_zero] at h
    tauto
  · intro h
    rcases h with h | h | h | h
    all_goals rw [h]; simp

/-! ## 3. The inverted coordinate `φ z = z/(z-1)` never lies on the positive real axis -/

/-- `φ` is an involution away from `z = 1`: `φ (φ z) = z`. -/
private lemma sw_invol (z : ℂ) (hz : z ≠ 1) : Work.C17I.sw (Work.C17I.sw z) = z := by
  show z / (z - 1) / (z / (z - 1) - 1) = z
  field_simp
  ring

/-- If `‖z‖ < 1` and `Re z ≥ 1/5`, then `φ z = z/(z-1)` is not a positive real number.  Indeed
`φ` is an involution, and if `z = φ p = p/(p-1)` for `p > 0` then `z` is real with
`z = p/(p-1) = 1 + 1/(p-1)`, which is `< 0` when `p < 1` (contradicting `Re z ≥ 1/5`) and `> 1`
when `p > 1` (contradicting `‖z‖ < 1`). -/
private lemma sw_ne_ofReal (z : ℂ) (hz1 : ‖z‖ < 1) (hz2 : (1 / 5 : ℝ) ≤ z.re)
    (p : ℝ) (hp : 0 < p) : Work.C17I.sw z ≠ (p : ℂ) := by
  have hz_ne1 : z ≠ 1 := by
    intro h; rw [h] at hz1; simp at hz1
  have hsw : Work.C17I.sw (Work.C17I.sw z) = z := sw_invol z hz_ne1
  intro h
  rw [h, Work.C17I.sw] at hsw
  have hp1 : p ≠ 1 := by
    intro hp1
    rw [hp1] at hsw
    norm_num at hsw
    have hz0 : z = 0 := hsw.symm
    rw [hz0] at hz2
    norm_num at hz2
  have hz_eq : z = ((p / (p - 1) : ℝ) : ℂ) := by
    rw [← hsw]
    push_cast
    ring
  have hre : z.re = p / (p - 1) := by rw [hz_eq, Complex.ofReal_re]
  rcases lt_or_gt_of_ne hp1 with hlt | hgt
  · have : p / (p - 1) < 0 := div_neg_of_pos_of_neg hp (by linarith)
    linarith
  · have h1lt : 1 < p / (p - 1) := by
      rw [lt_div_iff₀ (by linarith : (0 : ℝ) < p - 1)]
      linarith
    have := Complex.re_le_norm z
    rw [hre] at this
    linarith

/-! ## 4. `P2x` does not vanish at `φ z` on the stadium -/

/-- `P2x (aOf m) (aOf n) (φ z) ≠ 0` for `‖z‖ < 1`, `Re z ≥ 1/5`, `z ≠ 1/2`. -/
private lemma P2x_eval_ne_zero (m n : ℕ) (z : ℂ) (hz1 : ‖z‖ < 1) (hz2 : (1 / 5 : ℝ) ≤ z.re)
    (hz3 : z ≠ 1 / 2) :
    (Work.C17.P2x (Work.C17.aOf m) (Work.C17.aOf n)).eval₂ (algebraMap ℚ ℂ) (Work.C17I.sw z) ≠ 0 := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hq4 : (Work.C17.Q4x (Work.C17.aOf m) (Work.C17.aOf n)).eval₂ (algebraMap ℚ ℂ)
      (Work.C17I.sw z) ≠ 0 := by
    intro h
    rcases (Q4x_roots_iff m n (Work.C17I.sw z)).mp h with h | h | h | h
    · exact sw_ne_ofReal z hz1 hz2 _ (mul_pos (Submission.CDT.LocationSing.sqP_pos _ hm)
        (Submission.CDT.LocationSing.sqP_pos _ hn)) h
    · exact sw_ne_ofReal z hz1 hz2 _ (mul_pos (Submission.CDT.LocationSing.sqP_pos _ hm)
        (Submission.CDT.LocationSing.sqM_pos _ hn)) h
    · exact sw_ne_ofReal z hz1 hz2 _ (mul_pos (Submission.CDT.LocationSing.sqM_pos _ hm)
        (Submission.CDT.LocationSing.sqP_pos _ hn)) h
    · exact sw_ne_ofReal z hz1 hz2 _ (mul_pos (Submission.CDT.LocationSing.sqM_pos _ hm)
        (Submission.CDT.LocationSing.sqM_pos _ hn)) h
  have hz_ne1 : z ≠ 1 := by intro h; rw [h] at hz1; simp at hz1
  have hsw1 : Work.C17I.sw z ≠ 1 := by
    intro h
    rw [Work.C17I.sw, div_eq_iff (sub_ne_zero.mpr hz_ne1)] at h
    simp only [one_mul] at h
    exact one_ne_zero (sub_eq_self.mp h.symm)
  have hsw0 : Work.C17I.sw z ≠ 0 := by
    intro h
    rw [Work.C17I.sw, div_eq_zero_iff] at h
    rcases h with h | h
    · rw [h] at hz2; norm_num at hz2
    · exact hz_ne1 (sub_eq_zero.mp h)
  have hswm1 : Work.C17I.sw z ≠ -1 := by
    intro h
    rw [Work.C17I.sw, div_eq_iff (sub_ne_zero.mpr hz_ne1)] at h
    have h2 : (2 : ℂ) * z = 1 := by linear_combination h
    have hz : z = 1 / 2 := (eq_div_iff (two_ne_zero)).mpr (by rw [mul_comm]; exact h2)
    exact hz3 hz
  have hprod : (Work.C17.P2x (Work.C17.aOf m) (Work.C17.aOf n)).eval₂ (algebraMap ℚ ℂ)
      (Work.C17I.sw z)
      = (Work.C17I.sw z - 1) * Work.C17I.sw z * (Work.C17I.sw z + 1)
        * (Work.C17.Q4x (Work.C17.aOf m) (Work.C17.aOf n)).eval₂ (algebraMap ℚ ℂ) (Work.C17I.sw z) := by
    simp only [Work.C17.P2x, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_add,
      Polynomial.eval₂_X, Polynomial.eval₂_one]
  rw [hprod]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hsw1) hsw0)
    (fun h => hswm1 (add_eq_zero_iff_eq_neg.mp h))) hq4

/-! ## 5. The target lemma -/

set_option linter.unusedVariables false in
theorem q4x_roots (m n : ℕ) (hm : 1 ≤ m) (hlt : m < n) {S : Set ℂ}
    (hS1 : S ⊆ Metric.ball (0 : ℂ) 1) (hS2 : ∀ z ∈ S, (1 / 5 : ℝ) ≤ z.re)
    (hS3 : (1 / 2 : ℂ) ∉ S) :
    (∀ w : ℂ, (Work.C17.Q4x (Work.C17.aOf m) (Work.C17.aOf n)).eval₂ (algebraMap ℚ ℂ) w = 0 ↔
        w = ((Submission.CDT.LocationSing.sqP (m : ℝ) * Submission.CDT.LocationSing.sqP (n : ℝ) : ℝ) : ℂ) ∨
        w = ((Submission.CDT.LocationSing.sqP (m : ℝ) * Submission.CDT.LocationSing.sqM (n : ℝ) : ℝ) : ℂ) ∨
        w = ((Submission.CDT.LocationSing.sqM (m : ℝ) * Submission.CDT.LocationSing.sqP (n : ℝ) : ℝ) : ℂ) ∨
        w = ((Submission.CDT.LocationSing.sqM (m : ℝ) * Submission.CDT.LocationSing.sqM (n : ℝ) : ℝ) : ℂ)) ∧
    (∀ z ∈ S, (Work.C17.P2x (Work.C17.aOf m) (Work.C17.aOf n)).eval₂ (algebraMap ℚ ℂ)
        (Work.C17I.sw z) ≠ 0) := by
  refine ⟨fun w => Q4x_roots_iff m n w, fun z hzS => ?_⟩
  have hz1 : ‖z‖ < 1 := by simpa using hS1 hzS
  have hz2 : (1 / 5 : ℝ) ≤ z.re := hS2 z hzS
  have hz3 : z ≠ 1 / 2 := by intro h; exact hS3 (h ▸ hzS)
  exact P2x_eval_ne_zero m n z hz1 hz2 hz3

end

end Work.C17I
