import Mathlib
import Submission.Work.MotC2.PoleSetup

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

open Polynomial

/-!
# Degree constraints for the `w³` chart of a Weierstrass curve

Writing `c = cubicPoly E = X³ + a₂X² + a₄X + a₆` (monic of degree `3`), `t = linPoly E = a₁X + a₃`
(of degree `≤ 1`) and `A = c + t²`, `B = 2c + t²`, the two hypotheses of
`Work.MotC2.w_cube_deg_constraints` say that the combinations

* `S = -(p·t) + q·A` has degree `≤ 3` and
* `T = p·A - q·(t·B)` has degree `≤ 4`.

Two polynomial identities drive the argument:

* `t·T + A·S = q·(A² - t²·B) = q·c²` — the degree of `q·c²` is thus `≤ 6`, and since
  `deg c² = 6` this forces `deg q ≤ 0`;
* `T + t·S = p·(A - t²) + q·t·(A - B) = c·(p - q·t)` — of degree `≤ 4`, so `deg(p - q·t) ≤ 1`,
  and since `deg(q·t) ≤ deg q + deg t ≤ 1` also `deg p ≤ 1`.

These are exactly the degree constraints used when one writes `r ∈ Coord E` in the basis
`1, x, y` and expands `r·w³ ∈ infPlace E` (`w = infW E = y/x²`, `x·w² = 1 + a₂u + a₄u² + a₆u³ -
(a₁ + a₃u)·w`), so that `v_O(r) ≥ -3` becomes the conjunction `deg q ≤ 0 ∧ deg p ≤ 1`.

## Tags

elliptic curve, pole order, chart at infinity, degree bookkeeping
-/

/-- Abstract degree bookkeeping: if `c` has degree `3` and `t` has degree `≤ 1`, and the two
combinations `-(p·t) + q·(c + t²)`, `p·(c + t²) - q·(t·(2c + t²))` have degree `≤ 3`, `≤ 4`
respectively, then `q` is constant and `p` has degree `≤ 1`.  (The data of a Weierstrass curve
used in the application are `c = cubicPoly E` — monic of degree `3` — and `t = linPoly E`.) -/
private lemma w_cube_deg_aux {L : Type*} [Field L] (c t p q : Polynomial L)
    (hc : c.degree = (3 : WithBot ℕ)) (ht : t.degree ≤ (1 : WithBot ℕ))
    (h1 : (-(p * t) + q * (c + t ^ 2)).degree ≤ 3)
    (h2 : (p * (c + t ^ 2) - q * (t * (2 * c + t ^ 2))).degree ≤ 4) :
    q.degree ≤ 0 ∧ p.degree ≤ 1 := by
  -- `deg (c + t²) ≤ 3` and `deg (2c + t²) ≤ 3`
  have hA : (c + t ^ 2).degree ≤ (3 : WithBot ℕ) := by
    refine le_trans (degree_add_le _ _) (max_le hc.le ?_)
    calc (t ^ 2).degree = (t * t).degree := by rw [pow_two]
      _ ≤ t.degree + t.degree := degree_mul_le _ _
      _ ≤ (1 : WithBot ℕ) + 1 := add_le_add ht ht
      _ = (2 : WithBot ℕ) := by norm_num
      _ ≤ 3 := by norm_num
  have hB : (2 * c + t ^ 2).degree ≤ (3 : WithBot ℕ) := by
    rw [show 2 * c + t ^ 2 = (c + t ^ 2) + c by ring]
    exact le_trans (degree_add_le _ _) (max_le hA hc.le)
  set S := -(p * t) + q * (c + t ^ 2) with hS
  set T := p * (c + t ^ 2) - q * (t * (2 * c + t ^ 2)) with hT
  have h1' : S.degree ≤ (3 : WithBot ℕ) := h1
  have h2' : T.degree ≤ (4 : WithBot ℕ) := h2
  -- first identity: `t·T + A·S = q·c²`, of degree `≤ 6`, so `deg q ≤ 0`
  have key1 : t * T + (c + t ^ 2) * S = q * c ^ 2 := by ring
  have hqc : (q * c ^ 2).degree ≤ (6 : WithBot ℕ) := by
    rw [← key1]
    refine le_trans (degree_add_le _ _) (max_le ?_ ?_)
    · calc (t * T).degree ≤ t.degree + T.degree := degree_mul_le _ _
        _ ≤ (1 : WithBot ℕ) + 4 := add_le_add ht h2'
        _ ≤ 6 := by norm_num
    · calc ((c + t ^ 2) * S).degree ≤ (c + t ^ 2).degree + S.degree := degree_mul_le _ _
        _ ≤ (3 : WithBot ℕ) + 3 := add_le_add hA h1'
        _ ≤ 6 := by norm_num
  have hq : q.degree ≤ 0 := by
    by_cases hq0 : q = 0
    · rw [hq0]; simp
    · have hc2 : (c ^ 2).degree = (6 : WithBot ℕ) := by
        rw [pow_two, degree_mul, hc]; norm_num
      have h6 : q.degree + (c ^ 2).degree ≤ (6 : WithBot ℕ) := by
        have h := hqc
        rwa [degree_mul] at h
      rw [hc2] at h6
      exact (WithBot.add_le_add_iff_right (by norm_num : (6 : WithBot ℕ) ≠ ⊥)).mp
        (by simpa using h6)
  refine ⟨hq, ?_⟩
  -- second identity: `T + t·S = c·(p - q·t)`, of degree `≤ 4`, so `deg (p - q·t) ≤ 1`
  have key2 : T + t * S = c * (p - q * t) := by ring
  have hEq : (c * (p - q * t)).degree ≤ (4 : WithBot ℕ) := by
    rw [← key2]
    refine le_trans (degree_add_le _ _) (max_le h2' ?_)
    calc (t * S).degree ≤ t.degree + S.degree := degree_mul_le _ _
      _ ≤ (1 : WithBot ℕ) + 3 := add_le_add ht h1'
      _ ≤ 4 := by norm_num
  have hpq : (p - q * t).degree ≤ (1 : WithBot ℕ) := by
    by_cases hz : p - q * t = 0
    · rw [hz]; simp
    · have h6 : c.degree + (p - q * t).degree ≤ (4 : WithBot ℕ) := by
        have h := hEq
        rwa [degree_mul] at h
      rw [hc, show (4 : WithBot ℕ) = (3 : WithBot ℕ) + 1 by norm_num] at h6
      exact (WithBot.add_le_add_iff_left (by norm_num : (3 : WithBot ℕ) ≠ ⊥)).mp h6
  -- `deg (q·t) ≤ deg q + deg t ≤ 1`, so `deg p ≤ max 1 1 = 1`
  have hqt : (q * t).degree ≤ (1 : WithBot ℕ) := by
    calc (q * t).degree ≤ q.degree + t.degree := degree_mul_le _ _
      _ ≤ (0 : WithBot ℕ) + 1 := add_le_add hq ht
      _ ≤ 1 := by norm_num
  rw [show p = (p - q * t) + q * t by ring]
  exact le_trans (degree_add_le _ _) (max_le hpq hqt)

theorem w_cube_deg_constraints (L : Type*) [Field L] (E : WeierstrassCurve L) (p q : Polynomial L) :
    (-(p * Work.MotC2.linPoly E) +
      q * (Work.MotC2.cubicPoly E + Work.MotC2.linPoly E ^ 2)).degree ≤ 3 →
    (p * (Work.MotC2.cubicPoly E + Work.MotC2.linPoly E ^ 2) -
      q * (Work.MotC2.linPoly E *
        (2 * Work.MotC2.cubicPoly E + Work.MotC2.linPoly E ^ 2))).degree ≤ 4 →
    q.degree ≤ 0 ∧ p.degree ≤ 1 := by
  intro h1 h2
  exact w_cube_deg_aux (cubicPoly E) (linPoly E) p q (cubicPoly_degree E) (linPoly_degree_le E)
    h1 h2

end Work.MotC2
