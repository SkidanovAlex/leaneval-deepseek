import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.tauComboBounds`

The elementary bounds on the *smoothed kinetic profile* combination

  `A = (1 - ε_T) c₁² φ(x/c₁) + ε_T c₂² φ(x/c₂)`,   `0 ≤ ε_T ≤ 1/2`,  `0 < c₁ ≤ c₂`,  `0 ≤ x`,

for a profile `φ` satisfying the three FS-shaped axioms of `Work.BoseBoxFock.tauProf`
(`(r-2)₊² ≤ φ r ≤ (r-1)₊²`, `φ r = 0` for `r ≤ 1`):

* `A ≥ 0`;
* `A ≤ x²` (the `ℓ²`-mass bound of `eq:tautilde`/`lem:w2>w1` bookkeeping);
* `x ≤ c₁ → A = 0` (the combination vanishes below the *smaller* threshold `c₁`);
* `(max 0 (x - 2c₂))² ≤ 2A` (the combination is at least half the shifted square of the
  *larger* threshold, uniformly in `ε_T ∈ [0,1/2]` — this is the sharp `(r-2)₊²` lower side);
* `x² - A ≤ 4 c₂ x + c₂²` (the complementary upper side).

The mathematics is elementary: writing `t_i = c_i² φ(x/c_i)`, each `t_i` lies in the interval
`[(max 0 (x-2c_i))², (max 0 (x-c_i))²]` (the three profile axioms transported through the
substitution `c²·max(0, ·/c - d)² = max(0, · - d·c)²`), and `A` is the convex combination with
weights `1-ε_T`, `ε_T`.  The only slightly non-trivial conjuncts are the last two, which are
handled by splitting at `x = 2c₂`: either `x ≤ 2c₂` (where the cheap bounds suffice) or
`x ≥ 2c₂` (where both shifted squares are active and the resulting expression is affine in
`ε_T` with non-negative endpoints).
-/

namespace Work.BoseBogFS

/-- `max 0 (c * y) = c * max 0 y` for `c > 0`. -/
private lemma max_zero_mul_pos {c y : ℝ} (hc : 0 < c) : max 0 (c * y) = c * max 0 y := by
  rcases le_or_gt 0 y with hy | hy
  · rw [max_eq_right (mul_nonneg hc.le hy), max_eq_right hy]
  · rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos hc.le hy.le), max_eq_left hy.le, mul_zero]

/-- Scaling the truncated square: `c² * max(0, x/c - d)² = max(0, x - d c)²` for `c > 0`. -/
private lemma sq_max_mul_sub {c x d : ℝ} (hc : 0 < c) :
    c ^ 2 * (max 0 (x / c - d)) ^ 2 = (max 0 (x - d * c)) ^ 2 := by
  have h : x - d * c = c * (x / c - d) := by field_simp
  rw [h, max_zero_mul_pos hc, mul_pow]

/-- Upper side of the profile axiom, transported through `r = x/c`. -/
private lemma term_le_upper {φ : ℝ → ℝ} (hhi : ∀ r : ℝ, φ r ≤ (max 0 (r - 1)) ^ 2)
    {c x : ℝ} (hc : 0 < c) : c ^ 2 * φ (x / c) ≤ (max 0 (x - c)) ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (hhi (x / c)) (sq_nonneg c)
  have h2 := sq_max_mul_sub (c := c) (x := x) (d := 1) hc
  simpa using le_trans h (le_of_eq h2)

/-- Lower side of the profile axiom, transported through `r = x/c`. -/
private lemma term_le_lower {φ : ℝ → ℝ} (hlo : ∀ r : ℝ, (max 0 (r - 2)) ^ 2 ≤ φ r)
    {c x : ℝ} (hc : 0 < c) : (max 0 (x - 2 * c)) ^ 2 ≤ c ^ 2 * φ (x / c) := by
  have h := mul_le_mul_of_nonneg_left (hlo (x / c)) (sq_nonneg c)
  have h2 := sq_max_mul_sub (c := c) (x := x) (d := 2) hc
  simpa using le_trans (le_of_eq h2.symm) h

theorem tauComboBounds (φ : ℝ → ℝ)
    (hlo : ∀ r : ℝ, (max 0 (r - 2)) ^ 2 ≤ φ r)
    (hhi : ∀ r : ℝ, φ r ≤ (max 0 (r - 1)) ^ 2)
    (hz : ∀ r : ℝ, r ≤ 1 → φ r = 0)
    {eT c1 c2 x : ℝ} (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1 / 2)
    (hc1 : 0 < c1) (hc12 : c1 ≤ c2) (hx : 0 ≤ x) :
    0 ≤ (1 - eT) * c1 ^ 2 * φ (x / c1) + eT * c2 ^ 2 * φ (x / c2) ∧
      (1 - eT) * c1 ^ 2 * φ (x / c1) + eT * c2 ^ 2 * φ (x / c2) ≤ x ^ 2 ∧
      (x ≤ c1 → (1 - eT) * c1 ^ 2 * φ (x / c1) + eT * c2 ^ 2 * φ (x / c2) = 0) ∧
      (max 0 (x - 2 * c2)) ^ 2
        ≤ 2 * ((1 - eT) * c1 ^ 2 * φ (x / c1) + eT * c2 ^ 2 * φ (x / c2)) ∧
      x ^ 2 - ((1 - eT) * c1 ^ 2 * φ (x / c1) + eT * c2 ^ 2 * φ (x / c2))
        ≤ 4 * c2 * x + c2 ^ 2 := by
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 hc12
  have h1eT : 0 ≤ 1 - eT := by linarith
  have hφnn : ∀ r : ℝ, 0 ≤ φ r := fun r => le_trans (sq_nonneg _) (hlo r)
  -- regroup the weighted sum: `(1-ε)c₁²φ(x/c₁)` is `(1-ε)·(c₁²φ(x/c₁))`
  have hAs : (1 - eT) * c1 ^ 2 * φ (x / c1) + eT * c2 ^ 2 * φ (x / c2)
      = (1 - eT) * (c1 ^ 2 * φ (x / c1)) + eT * (c2 ^ 2 * φ (x / c2)) := by ring
  rw [hAs]
  have hA0 : 0 ≤ (1 - eT) * (c1 ^ 2 * φ (x / c1)) + eT * (c2 ^ 2 * φ (x / c2)) :=
    add_nonneg (mul_nonneg h1eT (mul_nonneg (sq_nonneg c1) (hφnn (x / c1))))
      (mul_nonneg heT0 (mul_nonneg (sq_nonneg c2) (hφnn (x / c2))))
  refine ⟨hA0, ?_, ?_, ?_, ?_⟩
  · -- `A ≤ x²`: each transported term is `≤ x²`, being a weighted average
    have hu : c1 ^ 2 * φ (x / c1) ≤ x ^ 2 :=
      le_trans (term_le_upper hhi hc1)
        (by have hm : max 0 (x - c1) ≤ x := max_le hx (by linarith)
            have hmn : 0 ≤ max 0 (x - c1) := le_max_left _ _
            nlinarith [mul_le_mul hm hm hmn hx])
    have hv : c2 ^ 2 * φ (x / c2) ≤ x ^ 2 :=
      le_trans (term_le_upper hhi hc2)
        (by have hm : max 0 (x - c2) ≤ x := max_le hx (by linarith)
            have hmn : 0 ≤ max 0 (x - c2) := le_max_left _ _
            nlinarith [mul_le_mul hm hm hmn hx])
    have k1 := mul_le_mul_of_nonneg_left hu h1eT
    have k2 := mul_le_mul_of_nonneg_left hv heT0
    linarith
  · -- `x ≤ c₁ → A = 0`: both profile evaluations vanish
    intro hxc1
    have hw1 : x / c1 ≤ 1 := (div_le_one hc1).mpr hxc1
    have hw2 : x / c2 ≤ 1 := (div_le_one hc2).mpr (le_trans hxc1 hc12)
    rw [hz (x / c1) hw1, hz (x / c2) hw2]
    ring
  · -- `(max 0 (x-2c₂))² ≤ 2A`
    by_cases h2 : x ≤ 2 * c2
    · rw [max_eq_left (by linarith : x - 2 * c2 ≤ 0)]
      linarith [hA0]
    · have h2' : 2 * c2 ≤ x := by linarith
      rw [max_eq_right (by linarith : (0:ℝ) ≤ x - 2 * c2)]
      have hm1 : max 0 (x - 2 * c1) = x - 2 * c1 := max_eq_right (by linarith)
      have hm2 : max 0 (x - 2 * c2) = x - 2 * c2 := max_eq_right (by linarith)
      have hu : (x - 2 * c1) ^ 2 ≤ c1 ^ 2 * φ (x / c1) := by
        simpa [hm1] using term_le_lower (x := x) hlo hc1
      have hv : (x - 2 * c2) ^ 2 ≤ c2 ^ 2 * φ (x / c2) := by
        simpa [hm2] using term_le_lower (x := x) hlo hc2
      have e3 : (x - 2 * c2) ^ 2 ≤ (x - 2 * c1) ^ 2 := by
        apply pow_le_pow_left₀ <;> linarith
      have k1 := mul_le_mul_of_nonneg_left (le_trans e3 hu) h1eT
      have k2 := mul_le_mul_of_nonneg_left hv heT0
      have hsum : (x - 2 * c2) ^ 2
          = (1 - eT) * (x - 2 * c2) ^ 2 + eT * (x - 2 * c2) ^ 2 := by ring
      have hfin : (x - 2 * c2) ^ 2
          ≤ (1 - eT) * (c1 ^ 2 * φ (x / c1)) + eT * (c2 ^ 2 * φ (x / c2)) := by
        linarith
      calc (x - 2 * c2) ^ 2
          ≤ (1 - eT) * (c1 ^ 2 * φ (x / c1)) + eT * (c2 ^ 2 * φ (x / c2)) := hfin
        _ ≤ 2 * ((1 - eT) * (c1 ^ 2 * φ (x / c1)) + eT * (c2 ^ 2 * φ (x / c2))) :=
            le_mul_of_one_le_left hA0 (by norm_num)
  · -- `x² - A ≤ 4 c₂ x + c₂²`
    by_cases h2 : x ≤ 2 * c2
    · -- below the threshold `x²` is already small
      have hxx : x ^ 2 ≤ 4 * c2 * x + c2 ^ 2 := by
        have h1 : x * x ≤ (2 * c2) * x := mul_le_mul_of_nonneg_right h2 hx
        have h2' : 0 ≤ c2 * x := mul_nonneg hc2.le hx
        have h3 : 0 ≤ c2 ^ 2 := sq_nonneg c2
        nlinarith
      linarith [hA0]
    · have h2' : 2 * c2 ≤ x := by linarith
      have hm1 : max 0 (x - 2 * c1) = x - 2 * c1 := max_eq_right (by linarith)
      have hm2 : max 0 (x - 2 * c2) = x - 2 * c2 := max_eq_right (by linarith)
      have hu : (x - 2 * c1) ^ 2 ≤ c1 ^ 2 * φ (x / c1) := by
        simpa [hm1] using term_le_lower (x := x) hlo hc1
      have hv : (x - 2 * c2) ^ 2 ≤ c2 ^ 2 * φ (x / c2) := by
        simpa [hm2] using term_le_lower (x := x) hlo hc2
      have k1 := mul_le_mul_of_nonneg_left hu h1eT
      have k2 := mul_le_mul_of_nonneg_left hv heT0
      -- the algebraic core: the weighted shifted squares dominate `x² - 4c₂x - c₂²`
      have halg : x ^ 2 - 4 * c2 * x - c2 ^ 2
          ≤ (1 - eT) * (x - 2 * c1) ^ 2 + eT * (x - 2 * c2) ^ 2 := by
        have a : 0 ≤ (1 - eT) * (c2 - c1) := mul_nonneg h1eT (by linarith)
        have a2 : 0 ≤ (1 - eT) * (c2 - c1) * x := mul_nonneg a hx
        have b : 0 ≤ (1 - eT) * c1 ^ 2 := mul_nonneg h1eT (sq_nonneg c1)
        have c : 0 ≤ eT * c2 ^ 2 := mul_nonneg heT0 (sq_nonneg c2)
        have d : 0 ≤ c2 ^ 2 := sq_nonneg c2
        nlinarith [a2, b, c, d]
      linarith

end Work.BoseBogFS
