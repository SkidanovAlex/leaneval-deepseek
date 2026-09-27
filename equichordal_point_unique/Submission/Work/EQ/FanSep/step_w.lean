import Mathlib
import Submission.Work.EQ.FanSep.Defs

/-!
# The single step of the fan separation (`Work.EQ.FanSep.step_w`)

Two elementary facts used in the proof of `Work.EQ.fan_sep` (Rychlik's uniform fan
separation, Rychlik, *A complete solution to the Equichordal Point Problem*, Invent. Math.
129 (1997), Theorem 7(1) / Lemma 14).

* `invBranch a s` rescales the two coordinates of `Q - A₁` by one and the same complex factor
  `σ/ρ - 1` when the result is measured from `A₂`, `A₁ = (-a/2,0)`, `A₂ = (a/2,0)`.  Hence the
  semi-projective bound `‖Q.2‖ ≤ qw·‖Q.1 + a/2‖` is preserved, with the *same* constant `qw`,
  the distance after the step being measured to `A₂`.

* Near a point `c` that is far from both `±a/2` the ratio `‖·- a/2‖/‖·+ a/2‖` changes by at
  most a factor `1 + C‖·- c‖` on the ball of radius `(1-a)/8` about `c`.
-/

namespace Work.EQ.FanSep

open Work.EQ

/-- `invBranch a s Q` differs from `A₂ = (a/2,0)` by the coordinates of `Q - A₁`
(`A₁ = (-a/2,0)`) multiplied by one and the same complex factor
`f = σ/ρ - 1`, where `σ = ±1` is the branch sign and `ρ = ((Q.1 + a/2)^2 + Q.2^2)^{1/2}` the
principal square root. -/
lemma invBranch_mul_sub (a : ℝ) (s : Bool) (Q : ℂ × ℂ) :
    ∃ f : ℂ,
      (invBranch a s Q).1 - ((a / 2 : ℝ) : ℂ) = (Q.1 + ((a / 2 : ℝ) : ℂ)) * f ∧
      (invBranch a s Q).2 = Q.2 * f := by
  refine ⟨(if s then (1 : ℂ) else -1) / ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ) - 1,
    ?_, ?_⟩ <;>
    simp only [invBranch] <;> ring

/-- First conjunct of `step_w`: `invBranch a s` preserves the semi-projective cone
`‖Q.2‖ ≤ qw·‖Q.1 + a/2‖` — with the same constant `qw`, the distance being measured to `a/2`
after the step. -/
theorem step_w_first {a : ℝ} :
    ∀ (s : Bool) {Q : ℂ × ℂ} {qw : ℝ}, Q.1 + ((a / 2 : ℝ) : ℂ) ≠ 0 → 0 ≤ qw → qw ≤ 1 / 2 →
      ‖Q.2‖ ≤ qw * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ →
      ‖(invBranch a s Q).2‖ ≤ qw * ‖(invBranch a s Q).1 - ((a / 2 : ℝ) : ℂ)‖ := by
  intro s Q qw _hQ _hqw0 _hqw hest
  obtain ⟨f, h1, h2⟩ := invBranch_mul_sub a s Q
  rw [h2, h1, norm_mul, norm_mul]
  have hf : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  have := mul_le_mul_of_nonneg_right hest hf
  rwa [mul_assoc] at this

/-- Second conjunct of `step_w`: on the ball of radius `(1-a)/8` about a point `c` lying at
distance at least `(1-a)/2` from both `±a/2`, the ratio `‖·- a/2‖/‖·+ a/2‖` is controlled by
`1 + (16/(1-a))‖·- c‖`. -/
theorem step_w_second_est {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {c : ℝ} {Q : ℂ},
      (1 - a) / 2 ≤ ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ →
      (1 - a) / 2 ≤ ‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ →
      ‖Q - (c : ℂ)‖ ≤ (1 - a) / 8 →
      ‖Q - ((a / 2 : ℝ) : ℂ)‖ * ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ ≤
        ‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ * ‖Q + ((a / 2 : ℝ) : ℂ)‖ * (1 + C * ‖Q - (c : ℂ)‖) := by
  refine ⟨16 / (1 - a), by positivity, ?_⟩
  intro c Q h1 h2 h3
  set k : ℝ := 1 - a with hkdef
  have hkpos : 0 < k := by rw [hkdef]; linarith
  set X : ℝ := ‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ with hXdef
  set Y : ℝ := ‖Q + ((a / 2 : ℝ) : ℂ)‖ with hYdef
  set e : ℝ := ‖Q - (c : ℂ)‖ with hedef
  have he0 : 0 ≤ e := by rw [hedef]; positivity
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hX : k / 2 ≤ X := h2
  have he : e ≤ k / 8 := h3
  -- `‖Q + a/2‖` stays bounded below: `cc + a/2 = (Q + a/2) - (Q - cc)`.
  have F2 : ‖(c : ℂ) + ((a / 2 : ℝ) : ℂ)‖ ≤ Y + e := by
    have h : (c : ℂ) + ((a / 2 : ℝ) : ℂ) = (Q + ((a / 2 : ℝ) : ℂ)) - (Q - (c : ℂ)) := by ring
    rw [h]
    exact norm_sub_le _ _
  have hY : 3 * k / 8 ≤ Y := by linarith [F2, h1, he]
  -- the purely algebraic core, with `k = 1 - a`
  have core : (X + e) * (Y + e) ≤ X * Y * (1 + (16 / k) * e) := by
    have h1' : k * (X + Y + e) ≤ 16 * X * Y := by nlinarith [hkpos, hX, hY, he0, he]
    have h2' : k * e * (X + Y + e) ≤ 16 * X * Y * e := by nlinarith [h1', he0]
    have h3' : k * (X * Y * (1 + (16 / k) * e)) = k * X * Y + 16 * X * Y * e := by field_simp
    have h4' : k * ((X + e) * (Y + e)) = k * X * Y + k * e * (X + Y + e) := by ring
    have key : k * ((X + e) * (Y + e)) ≤ k * (X * Y * (1 + (16 / k) * e)) := by
      rw [h3', h4']; linarith
    exact le_of_mul_le_mul_left key hkpos
  have hQPl : ‖Q - ((a / 2 : ℝ) : ℂ)‖ ≤ X + e := by
    have h : Q - ((a / 2 : ℝ) : ℂ) = ((c : ℂ) - ((a / 2 : ℝ) : ℂ)) + (Q - (c : ℂ)) := by ring
    rw [h]; exact norm_add_le _ _
  have hprod : ‖Q - ((a / 2 : ℝ) : ℂ)‖ * ‖(c : ℂ) + ((a / 2 : ℝ) : ℂ)‖ ≤ (X + e) * (Y + e) :=
    mul_le_mul hQPl F2 (norm_nonneg _) (by linarith [hX0, he0])
  exact hprod.trans core

theorem step_w {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (∀ (s : Bool) {Q : ℂ × ℂ} {qw : ℝ}, Q.1 + ((a / 2 : ℝ) : ℂ) ≠ 0 → 0 ≤ qw → qw ≤ 1 / 2 →
      ‖Q.2‖ ≤ qw * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ →
      ‖(invBranch a s Q).2‖ ≤ qw * ‖(invBranch a s Q).1 - ((a / 2 : ℝ) : ℂ)‖) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ {c : ℝ} {Q : ℂ},
      (1 - a) / 2 ≤ ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ →
      (1 - a) / 2 ≤ ‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ →
      ‖Q - (c : ℂ)‖ ≤ (1 - a) / 8 →
      ‖Q - ((a / 2 : ℝ) : ℂ)‖ * ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖ ≤
        ‖((c : ℂ) - ((a / 2 : ℝ) : ℂ))‖ * ‖Q + ((a / 2 : ℝ) : ℂ)‖ * (1 + C * ‖Q - (c : ℂ)‖)) :=
  ⟨step_w_first (a := a), step_w_second_est ha0 ha1⟩

end Work.EQ.FanSep
