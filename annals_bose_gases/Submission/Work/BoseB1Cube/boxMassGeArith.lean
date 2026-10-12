import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.boxMassGeArith`

The pure-arithmetic core of the sliding-box volume bound `64 ≤ μ·|B(u)|`
(`Work.BoseB1Cube.boxMassGeOfGate`): if the three short sides `e j` of the box
`dlBox ℓ d u` satisfy `δ ≤ e j ≤ ℓ d` with `8δ ≤ ℓd`, `512δ ≤ ℓ`, and the
"outward displacement" vector `β j = max 0 (|((ℓd)•u)_j| − ℓd/2)` (which on the
non-sliver side of the box equals `ℓ/2 − e j` whenever `e j < ℓ d`) obeys
`∑ β j² ≤ ℓ²/4`, then `∏ e j ≥ 64δ³`.

## Proof

Let `T = {j | e j < ℓd}` be the set of *clipped* indices.

* **Pair lemma.** If `(ℓ/2−a)² + (ℓ/2−b)² ≤ ℓ²/4` with `a, b ≥ δ` and
  `512δ ≤ ℓ`, then `16δ² ≤ ab`.  Writing `u = ℓ/2−a`, `v = ℓ/2−b`, the
  constraint reads `u²+v² ≤ ℓ²/4`.  Either `u ≤ ℓ/4`, whence `a ≥ ℓ/4` and
  `ab ≥ (ℓ/4)δ ≥ 16δ²` because `ℓ ≥ 64δ`; or `u ≥ ℓ/4`, and the constraint
  forces `b ≥ u²/ℓ ≥ ℓ/16` (from `v² ≤ ℓ²/4−u²` and the identity
  `(ℓ/2 − u²/ℓ)² = ℓ²/4 − u² + u⁴/ℓ² ≥ ℓ²/4 − u² ≥ v²`), so that
  `ab ≥ δ·ℓ/16 ≥ 16δ²` because `ℓ ≥ 256δ`.
* If `|T| ≤ 1` then two of the `e j` equal `ℓd ≥ 8δ` and the third is `≥ δ`, so
  `∏ e j ≥ (8δ)²δ = 64δ³`.
* If `|T| = 2` then both clipped indices satisfy the pair constraint, giving
  `∏ e j ≥ 16δ²·(ℓd) ≥ 16δ²·8δ = 128δ³`.
* If `|T| = 3` then all three pairs satisfy it, so
  `(∏ e j)² = (e₀e₁)(e₀e₂)(e₁e₂) ≥ (16δ²)³ = (64δ³)²`.

The case split on `T ⊆ Fin 3` is performed explicitly on the three predicates
`e j < ℓd`.  (Note `(ℓ/2 − e j)² = β j²` is used only through `∑ β j² ≤ ℓ²/4`,
so neither `d > 0` nor `β ≥ 0` is needed.)
-/

set_option linter.unusedVariables false

namespace Work.BoseB1Cube

/-- If `u² + v² ≤ ℓ²/4` and `0 < ℓ`, then `u² ≤ ℓ·(ℓ/2 − v)`.  Equivalently
`u²/ℓ ≤ ℓ/2 − v`: the two coordinates are coupled, a large `u` forces `v` small. -/
private lemma sq_le_mul_of_sq_add_sq_le {ℓ u v : ℝ} (hℓ : 0 < ℓ)
    (h : u ^ 2 + v ^ 2 ≤ ℓ ^ 2 / 4) : u ^ 2 ≤ ℓ * (ℓ / 2 - v) := by
  have hℓ2 : (0 : ℝ) < ℓ ^ 2 := pow_pos hℓ 2
  have hu2 : u ^ 2 ≤ ℓ ^ 2 / 4 := by nlinarith [sq_nonneg v]
  rcases le_or_gt v 0 with hv | hv
  · nlinarith [hu2, hv, hℓ]
  · have hsq : (ℓ * v) ^ 2 ≤ (ℓ ^ 2 / 2 - u ^ 2) ^ 2 := by
      have h1 : ℓ ^ 2 * (u ^ 2 + v ^ 2) ≤ ℓ ^ 2 * (ℓ ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left h hℓ2.le
      nlinarith [h1, sq_nonneg (u ^ 2)]
    have hK : 0 ≤ ℓ ^ 2 / 2 - u ^ 2 := by nlinarith
    have hlv : 0 ≤ ℓ * v := mul_nonneg hℓ.le hv.le
    have h2 : |ℓ * v| ≤ |ℓ ^ 2 / 2 - u ^ 2| := (sq_le_sq).mp hsq
    rw [abs_of_nonneg hlv, abs_of_nonneg hK] at h2
    nlinarith

/-- The pair lemma: two coordinates obeying the constraint have product `≥ 16δ²`. -/
private lemma pairArith {ℓ δ a b : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (h512 : 512 * δ ≤ ℓ)
    (ha : δ ≤ a) (hb : δ ≤ b) (h : (ℓ / 2 - a) ^ 2 + (ℓ / 2 - b) ^ 2 ≤ ℓ ^ 2 / 4) :
    16 * δ ^ 2 ≤ a * b := by
  rcases le_or_gt (ℓ / 2 - a) (ℓ / 4) with hcase | hcase
  · have ha' : ℓ / 4 ≤ a := by linarith
    have hmul : (ℓ / 4) * δ ≤ a * b := mul_le_mul ha' hb hδ.le (by linarith)
    have h64 : 64 * δ ≤ ℓ := by linarith
    nlinarith [hmul, h64, hδ]
  · have hb' : (ℓ / 2 - a) ^ 2 ≤ ℓ * b := by
      have h1 := sq_le_mul_of_sq_add_sq_le (ℓ := ℓ) (u := ℓ / 2 - a) (v := ℓ / 2 - b) hℓ h
      have h2 : ℓ / 2 - (ℓ / 2 - b) = b := by ring
      rwa [h2] at h1
    have hsq : ℓ ^ 2 / 16 ≤ (ℓ / 2 - a) ^ 2 := by
      nlinarith [hcase, hℓ]
    have hb16 : ℓ / 16 ≤ b := by
      have hm : ℓ * (ℓ / 16) ≤ ℓ * b := by nlinarith
      exact le_of_mul_le_mul_left hm hℓ
    have h256 : 256 * δ ≤ ℓ := by linarith
    have hmul : δ * (ℓ / 16) ≤ a * b := mul_le_mul ha hb16 (by linarith) (by linarith)
    nlinarith [hmul, h256, hδ]

/-- A product with two factors equal to `ℓd ≥ 8δ` and the third `≥ δ`. -/
private lemma prod_ge_of_two_ld {ℓ d δ x : ℝ} (hδ : 0 < δ) (hA : 8 * δ ≤ ℓ * d)
    (hx : δ ≤ x) : 64 * δ ^ 3 ≤ x * (ℓ * d) * (ℓ * d) := by
  have hld : 0 ≤ ℓ * d := by linarith
  have hsq : (8 * δ) ^ 2 ≤ (ℓ * d) ^ 2 := pow_le_pow_left₀ (by linarith) hA 2
  have h1 : δ * (8 * δ) ^ 2 ≤ x * (ℓ * d) ^ 2 := mul_le_mul hx hsq (by positivity) (by linarith)
  nlinarith [h1]

/-- A product with one factor `ℓd ≥ 8δ` and a pair whose product is `≥ 16δ²`. -/
private lemma prod_ge_of_pair_ld {ℓ d δ x y : ℝ} (hδ : 0 < δ) (hA : 8 * δ ≤ ℓ * d)
    (hxy : 16 * δ ^ 2 ≤ x * y) : 64 * δ ^ 3 ≤ x * y * (ℓ * d) := by
  have hld : 0 ≤ ℓ * d := by linarith
  have h1 : 16 * δ ^ 2 * (ℓ * d) ≤ (x * y) * (ℓ * d) := mul_le_mul_of_nonneg_right hxy hld
  have h2 : 16 * δ ^ 2 * (8 * δ) ≤ 16 * δ ^ 2 * (ℓ * d) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  nlinarith [h1, h2]

theorem boxMassGeArith {ℓ d δ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hδ : 0 < δ)
    (hA : 8 * δ ≤ ℓ * d) (hB : 512 * δ ≤ ℓ) (e β : Fin 3 → ℝ)
    (he_lo : ∀ j : Fin 3, δ ≤ e j) (he_hi : ∀ j : Fin 3, e j ≤ ℓ * d)
    (hβ_nn : ∀ j : Fin 3, 0 ≤ β j)
    (hclip : ∀ j : Fin 3, e j < ℓ * d → β j = ℓ / 2 - e j)
    (hcons : ∑ j : Fin 3, (β j) ^ 2 ≤ ℓ ^ 2 / 4) :
    64 * δ ^ 3 ≤ ∏ j : Fin 3, e j := by
  have hsum := hcons
  rw [Fin.sum_univ_three] at hsum
  -- the pair constraints, one per pair of *clipped* indices
  have hp01 : e 0 < ℓ * d → e 1 < ℓ * d →
      (ℓ / 2 - e 0) ^ 2 + (ℓ / 2 - e 1) ^ 2 ≤ ℓ ^ 2 / 4 := by
    intro h0 h1
    have h := hsum
    rw [hclip 0 h0, hclip 1 h1] at h
    nlinarith [sq_nonneg (β 2)]
  have hp02 : e 0 < ℓ * d → e 2 < ℓ * d →
      (ℓ / 2 - e 0) ^ 2 + (ℓ / 2 - e 2) ^ 2 ≤ ℓ ^ 2 / 4 := by
    intro h0 h2
    have h := hsum
    rw [hclip 0 h0, hclip 2 h2] at h
    nlinarith [sq_nonneg (β 1)]
  have hp12 : e 1 < ℓ * d → e 2 < ℓ * d →
      (ℓ / 2 - e 1) ^ 2 + (ℓ / 2 - e 2) ^ 2 ≤ ℓ ^ 2 / 4 := by
    intro h1 h2
    have h := hsum
    rw [hclip 1 h1, hclip 2 h2] at h
    nlinarith [sq_nonneg (β 0)]
  rw [Fin.prod_univ_three]
  -- the case split on which indices are clipped
  by_cases h0 : e 0 < ℓ * d <;> by_cases h1 : e 1 < ℓ * d <;> by_cases h2 : e 2 < ℓ * d
  · -- all three indices are `< ℓ d`: the three pairwise products are `≥ 16δ²`
    have h01 := pairArith hℓ hδ hB (he_lo 0) (he_lo 1) (hp01 h0 h1)
    have h02 := pairArith hℓ hδ hB (he_lo 0) (he_lo 2) (hp02 h0 h2)
    have h12 := pairArith hℓ hδ hB (he_lo 1) (he_lo 2) (hp12 h1 h2)
    have hp0 : 0 < e 0 := lt_of_lt_of_le hδ (he_lo 0)
    have hp1 : 0 < e 1 := lt_of_lt_of_le hδ (he_lo 1)
    have hp2 : 0 < e 2 := lt_of_lt_of_le hδ (he_lo 2)
    have hd2 : 0 ≤ 16 * δ ^ 2 := by positivity
    have s1 : (16 * δ ^ 2) * (16 * δ ^ 2) ≤ (e 0 * e 1) * (e 0 * e 2) :=
      mul_le_mul h01 h02 hd2 (mul_pos hp0 hp1).le
    have s2 : (16 * δ ^ 2) * (16 * δ ^ 2) * (16 * δ ^ 2)
        ≤ (e 0 * e 1) * (e 0 * e 2) * (e 1 * e 2) :=
      mul_le_mul s1 h12 hd2 (mul_pos (mul_pos hp0 hp1) (mul_pos hp0 hp2)).le
    have hprod : (e 0 * e 1) * (e 0 * e 2) * (e 1 * e 2) = (e 0 * e 1 * e 2) ^ 2 := by ring
    have hcube : (16 * δ ^ 2) * (16 * δ ^ 2) * (16 * δ ^ 2) = (64 * δ ^ 3) ^ 2 := by ring
    have hsq : (64 * δ ^ 3) ^ 2 ≤ (e 0 * e 1 * e 2) ^ 2 := by
      rw [← hcube, ← hprod]
      exact s2
    have hnn : 0 ≤ e 0 * e 1 * e 2 := (mul_pos (mul_pos hp0 hp1) hp2).le
    have hab := (sq_le_sq).mp hsq
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 64 * δ ^ 3), abs_of_nonneg hnn] at hab
  · -- `e 2 = ℓ d`
    have he2 : e 2 = ℓ * d := le_antisymm (he_hi 2) (not_lt.mp h2)
    have h01 := pairArith hℓ hδ hB (he_lo 0) (he_lo 1) (hp01 h0 h1)
    calc 64 * δ ^ 3 ≤ e 0 * e 1 * (ℓ * d) := prod_ge_of_pair_ld hδ hA h01
      _ = e 0 * e 1 * e 2 := by rw [he2]
  · -- `e 1 = ℓ d`
    have he1 : e 1 = ℓ * d := le_antisymm (he_hi 1) (not_lt.mp h1)
    have h02 := pairArith hℓ hδ hB (he_lo 0) (he_lo 2) (hp02 h0 h2)
    calc 64 * δ ^ 3 ≤ e 0 * e 2 * (ℓ * d) := prod_ge_of_pair_ld hδ hA h02
      _ = e 0 * e 1 * e 2 := by rw [he1]; ring
  · -- `e 1 = e 2 = ℓ d`
    have he1 : e 1 = ℓ * d := le_antisymm (he_hi 1) (not_lt.mp h1)
    have he2 : e 2 = ℓ * d := le_antisymm (he_hi 2) (not_lt.mp h2)
    calc 64 * δ ^ 3 ≤ e 0 * (ℓ * d) * (ℓ * d) := prod_ge_of_two_ld hδ hA (he_lo 0)
      _ = e 0 * e 1 * e 2 := by rw [he1, he2]
  · -- `e 0 = ℓ d`
    have he0 : e 0 = ℓ * d := le_antisymm (he_hi 0) (not_lt.mp h0)
    have h12 := pairArith hℓ hδ hB (he_lo 1) (he_lo 2) (hp12 h1 h2)
    calc 64 * δ ^ 3 ≤ e 1 * e 2 * (ℓ * d) := prod_ge_of_pair_ld hδ hA h12
      _ = e 0 * e 1 * e 2 := by rw [he0]; ring
  · -- `e 0 = e 2 = ℓ d`
    have he0 : e 0 = ℓ * d := le_antisymm (he_hi 0) (not_lt.mp h0)
    have he2 : e 2 = ℓ * d := le_antisymm (he_hi 2) (not_lt.mp h2)
    calc 64 * δ ^ 3 ≤ e 1 * (ℓ * d) * (ℓ * d) := prod_ge_of_two_ld hδ hA (he_lo 1)
      _ = e 0 * e 1 * e 2 := by rw [he0, he2]; ring
  · -- `e 0 = e 1 = ℓ d`
    have he0 : e 0 = ℓ * d := le_antisymm (he_hi 0) (not_lt.mp h0)
    have he1 : e 1 = ℓ * d := le_antisymm (he_hi 1) (not_lt.mp h1)
    calc 64 * δ ^ 3 ≤ e 2 * (ℓ * d) * (ℓ * d) := prod_ge_of_two_ld hδ hA (he_lo 2)
      _ = e 0 * e 1 * e 2 := by rw [he0, he1]; ring
  · -- all three indices equal `ℓ d`
    have he0 : e 0 = ℓ * d := le_antisymm (he_hi 0) (not_lt.mp h0)
    have he1 : e 1 = ℓ * d := le_antisymm (he_hi 1) (not_lt.mp h1)
    have he2 : e 2 = ℓ * d := le_antisymm (he_hi 2) (not_lt.mp h2)
    calc 64 * δ ^ 3 ≤ (ℓ * d) * (ℓ * d) * (ℓ * d) :=
          prod_ge_of_two_ld hδ hA (by linarith : δ ≤ ℓ * d)
      _ = e 0 * e 1 * e 2 := by rw [he0, he1, he2]

end Work.BoseB1Cube
