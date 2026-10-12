import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.a0A2QJointArithB1` — scalar arithmetic for the joint core `(★)`

The pure-real (integral-free) arithmetic used by the assembly of
`Work.BoseFixB1S.a0A2QJointNormB1Fix`.  Keeping these facts in a separate module keeps the
heavy-weight main proof from having to elaborate large arithmetic goals with the enormous
integral terms in scope.
-/

namespace Work.BoseFixB1S

open scoped BigOperators

/-- Decomposition of a doubly-indexed sum of three-term summands. -/
theorem sum_hier3 {ι κ : Type*} [Fintype ι] (s : ι → Finset κ) (f g h : ι → κ → ℝ) :
    (∑ i, ∑ k ∈ s i, (f i k + g i k + h i k))
      = ((∑ i, ∑ k ∈ s i, f i k) + (∑ i, ∑ k ∈ s i, g i k))
        + (∑ i, ∑ k ∈ s i, h i k) := by
  simp only [Finset.sum_add_distrib]

/-- The `1/(16X)`-coefficient identity that turns the P-side demand into the block weight. -/
theorem mul_div_sixteen (t d X : ℝ) :
    t * (d ^ 2 / (16 * X)) = (1 / 2) * ((1 / 8) * (t * d ^ 2 / X)) := by
  ring

/-- **The P-side supply.**  The P-side demand
`(M₁/V²)(¼(S+1−m)² + ¼Var + m)` is paid by the corpus's two supplies `M₁G` and the
pair-condensate slack `pcb`, using `(M₁/(2V²))Var ≤ pcb`. -/
theorem supplyP (M1 V S Var m G pcb Xp : ℝ) (hV : 0 < V) (hM1 : 0 ≤ M1) (hVar : 0 ≤ Var)
    (hG : M1 * G = (M1 / V ^ 2) * ((1 / 4) * (S + 1 - m) ^ 2 + m))
    (hXp : Xp = (M1 / V ^ 2) * ((1 / 4) * (S + 1 - m) ^ 2 + (1 / 4) * Var + m))
    (hpcb : (M1 / (2 * V ^ 2)) * Var ≤ pcb) : Xp ≤ M1 * G + pcb := by
  rw [hXp, hG]
  have h1 : (M1 / V ^ 2) * ((1 / 4) * (S + 1 - m) ^ 2 + (1 / 4) * Var + m)
      = (M1 / V ^ 2) * ((1 / 4) * (S + 1 - m) ^ 2 + m) + (M1 / (4 * V ^ 2)) * Var := by
    ring
  have h2 : (M1 / (4 * V ^ 2)) * Var ≤ (M1 / (2 * V ^ 2)) * Var := by
    have h3 : (M1 / (4 * V ^ 2)) ≤ (M1 / (2 * V ^ 2)) := by
      have hnn : 0 ≤ M1 / (4 * V ^ 2) := by positivity
      have hid : 2 * (M1 / (4 * V ^ 2)) = M1 / (2 * V ^ 2) := by ring
      linarith
    exact mul_le_mul_of_nonneg_right h3 hVar
  linarith [h1, h2, hpcb]

/-- **The credit coefficient.**  With `m = μV`, `m ≥ 1`, `49Cf ≤ C_c a`, the scalar credit pays
the Q-side demand coefficient. -/
theorem creditCoef (Cf Cc av S mu m V : ℝ) (hV : 0 < V) (hm : m = mu * V) (hm1 : 1 ≤ m)
    (hS : 0 ≤ S) (hmu : 0 < mu) (hav : 0 ≤ av) (hCf : 0 ≤ Cf)
    (hcaa : 49 * Cf ≤ Cc * av) :
    (16 * Cf / V) * (S + 2 + m) + Cf * mu ≤ Cc * av * (mu + S / V) := by
  have hm0 : 0 ≤ m := by linarith
  have h1 : 16 * Cf ≤ Cc * av := by linarith
  have hscaled : 16 * Cf * (S + 2 + m) + Cf * m ≤ Cc * av * (m + S) := by
    have hA : 16 * Cf * S ≤ Cc * av * S := mul_le_mul_of_nonneg_right h1 hS
    have hD : 32 * Cf + 17 * Cf * m ≤ Cc * av * m := by
      have hb1 : 32 * Cf ≤ 32 * Cf * m := by nlinarith [hCf, hm1]
      have hb2 : 49 * Cf * m ≤ Cc * av * m := mul_le_mul_of_nonneg_right hcaa hm0
      have hb3 : 32 * Cf + 17 * Cf * m ≤ 49 * Cf * m := by linarith
      linarith [hb3, hb2]
    have hE : 16 * Cf * (S + 2 + m) + Cf * m = 16 * Cf * S + (32 * Cf + 17 * Cf * m) := by ring
    have hF : Cc * av * (m + S) = Cc * av * S + Cc * av * m := by ring
    rw [hE, hF]
    linarith [hA, hD]
  have key : ((16 * Cf / V) * (S + 2 + m) + Cf * mu) * V ≤ (Cc * av * (mu + S / V)) * V := by
    have e1 : ((16 * Cf / V) * (S + 2 + m) + Cf * mu) * V
        = 16 * Cf * (S + 2 + m) + Cf * m := by
      rw [hm]; field_simp
    have e2 : (Cc * av * (mu + S / V)) * V = Cc * av * (m + S) := by
      rw [hm]; field_simp
    rw [e1, e2]
    exact hscaled
  exact le_of_mul_le_mul_right key hV

/-- **The Q-side arithmetic.**  The Q-side demand `(2/V)DQm` is bounded by `Xq` from the estimate
`DQm ≤ 8Cf(S+2+m)nq`. -/
theorem qsideArith (Cf V S m nq DQm Xq : ℝ) (hV : 0 < V)
    (hDQ : DQm ≤ 8 * Cf * (S + 2 + m) * nq) (hXq : Xq = (16 * Cf / V) * (S + 2 + m) * nq) :
    (2 / V) * DQm ≤ Xq := by
  have h1 : (2 / V) * DQm ≤ (2 / V) * (8 * Cf * (S + 2 + m) * nq) :=
    mul_le_mul_of_nonneg_left hDQ (by positivity)
  have h2 : (2 / V) * (8 * Cf * (S + 2 + m) * nq) = (16 * Cf / V) * (S + 2 + m) * nq := by
    field_simp
    ring
  linarith [h1, h2, hXq]

/-- The peeled P-side block: from the block weight `(1/8)t(t−1−m)²/X ≤ (1/4)(t+1−m)² + m`,
multiplied by the (nonnegative) mass `J`, with the coefficient converted to the `1/(16X)` form
produced by the sharp atom. -/
theorem psideTerm {t m X J : ℝ}
    (hblk : (1 / 8) * (t * (t - 1 - m) ^ 2 / X) ≤ (1 / 4) * (t + 1 - m) ^ 2 + m)
    (hJ : 0 ≤ J) :
    t * ((t - 1 - m) ^ 2 / (16 * X)) * J ≤ ((1 / 8) * (t + 1 - m) ^ 2 + m / 2) * J := by
  rw [mul_div_sixteen]
  have h3 : (1 / 2) * ((1 / 8) * (t * (t - 1 - m) ^ 2 / X)) ≤ (1 / 8) * (t + 1 - m) ^ 2 + m / 2 := by
    linarith
  exact mul_le_mul_of_nonneg_right h3 hJ

end Work.BoseFixB1S
