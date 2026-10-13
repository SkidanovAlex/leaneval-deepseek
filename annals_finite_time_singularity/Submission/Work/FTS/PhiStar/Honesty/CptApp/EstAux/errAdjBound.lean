/-
# `errAdjBound`: the jets of the multiplier `χ_n ζ_n − 1` are bounded by `K b · 1_{Ω_n}`

The multiplier appearing in the first block of the approximation error of
`Work.FTS.PhiStar.Honesty.exists_cptQ_approx` is

  `Φ_n z θ = chiR n z · zetaR n θ − 1`.

It vanishes identically on the closed rectangle `[2/n, n] × [2/n, π/2 − 2/n]` (the *plateau*,
where `chiR n = 1` and `zetaR n = 1`), and its complement is exactly the shrinking region
`Ω_n` of `CptApp/Defs.lean`.  Hence *every* jet `D_z^b Φ_n` is bounded by a constant times the
indicator `omegaInd n z θ`, uniformly in the scale `n ≥ 2` — which is precisely the content of
this file, and the first step of `errASlot_le`.

**The two ingredients.**

* `D_z = z ∂_z` differentiates only the radial factor: since `D_z^b` is a polynomial in `z ∂_z`,
  one has `D_z^b (f z · g θ − 1) = (dz1 b f z) · g θ` for `b ≥ 1`, where `dz1` is the
  one-variable iterate `f ↦ (z ↦ z f'(z))` (`errAdj_sep`).  The subtraction of the constant `1`
  is invisible to `∂_z` (`deriv_sub_const`) and the constant factor `g θ` is untouched
  (`deriv_mul_const_field`); the whole induction needs *no* differentiability hypothesis.
* the uniform bound `|D_z^b (chiR n)| ≤ K₀ b` of `LamAux.chiR_dzIter_boundAux` on the *support*
  of the indicator (where `|zetaR n θ| ≤ 1`), and the vanishing of `D_z^b (chiR n)` on the
  plateau `[2/n, n]` (`PlateauZero.estPlateauZero`) off it.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.PlateauZero
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamAux.chiR_dzIter_boundAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAux

/-! ## The one-variable iterate of `D_z = z ∂_z` -/

/-- The `b`-th iterate of the one-variable operator `f ↦ (z ↦ z f'(z))`, the `z`-part of `D_z`
acting on a function of `z` alone. -/
noncomputable def dz1 : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => fun z => z * deriv (dz1 n f) z

@[simp] theorem dz1_zero (f : ℝ → ℝ) : dz1 0 f = f := rfl

@[simp] theorem dz1_succ (n : ℕ) (f : ℝ → ℝ) :
    dz1 (n + 1) f = fun z => z * deriv (dz1 n f) z := rfl

/-- **`D_z^b` of a function of `z` alone is the one-variable iterate `dz1`.** -/
theorem errAdjDzIter_zOnly (b : ℕ) (f : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter b (fun z _ : ℝ => f z) z θ = dz1 b f z := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
    show z * deriv (fun z' => Work.Spaces.DzIter b (fun z _ : ℝ => f z) z' θ) z
      = dz1 (b + 1) f z
    rw [show (fun z' => Work.Spaces.DzIter b (fun z _ : ℝ => f z) z' θ) = dz1 b f from
      funext fun z' => ih z']
    rfl

/-- **`D_z^b` of a separated product minus `1`.**  For every `b`,

  `D_z^b ((z,θ) ↦ f z · g θ − 1) = (dz1 b f z) · g θ − [b = 0]`,

the constant `1` being invisible to the derivative for `b ≥ 1` and the angular factor `g θ`
being a constant along the `z`-differentiation. -/
theorem errAdj_sep (f g : ℝ → ℝ) (b : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter b (fun z θ : ℝ => f z * g θ - 1) z θ
      = dz1 b f z * g θ - (if b = 0 then 1 else 0) := by
  induction b generalizing z with
  | zero => simp
  | succ b ih =>
    show z * deriv (fun z' => Work.Spaces.DzIter b (fun z θ : ℝ => f z * g θ - 1) z' θ) z
      = dz1 (b + 1) f z * g θ - (if b + 1 = 0 then 1 else 0)
    rw [show (fun z' => Work.Spaces.DzIter b (fun z θ : ℝ => f z * g θ - 1) z' θ)
        = fun z' => dz1 b f z' * g θ - (if b = 0 then 1 else 0) from funext fun z' => ih z',
      deriv_sub_const, deriv_mul_const_field]
    rw [ite_eq_right (Nat.succ_ne_zero b)]
    simp only [dz1_succ]
    ring

/-! ## The indicator takes only the values `0` and `1` -/

theorem omegaInd_zero_or_one (n : ℕ) (z θ : ℝ) :
    Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ = 0
      ∨ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ = 1 := by
  unfold Work.FTS.PhiStar.Honesty.CptApp.omegaInd
  split_ifs <;> simp

/-! ## The main statement -/

theorem errAdjBound : ∃ K : ℕ → ℝ, (∀ b : ℕ, 0 ≤ K b) ∧
    ∀ (n b : ℕ), 2 ≤ n → ∀ (z θ : ℝ),
      |Work.Spaces.DzIter b (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ|
        ≤ K b * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ := by
  obtain ⟨K₀, hK₀nn, hK₀⟩ := Work.FTS.PhiStar.Honesty.CptApp.LamAux.chiR_dzIter_boundAux
  refine ⟨fun b => max (K₀ b) 1, fun b => le_trans (hK₀nn b) (le_max_left _ _), ?_⟩
  intro n b hn z θ
  rcases Nat.eq_zero_or_pos b with hb | hb
  · -- order `0`: the value vanishes on the plateau, and is bounded by `1` on `Ω_n`
    subst hb
    simp only [Work.Spaces.DzIter_zero]
    have hsq := Work.FTS.PhiStar.Honesty.CptApp.chiR_zetaR_sub_one_sq_le hn z θ
    have habs : |Work.FTS.PhiStar.Honesty.CptApp.chiR n z
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1|
        ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ := by
      rcases omegaInd_zero_or_one n z θ with h | h
      · rw [h] at hsq ⊢
        have hx : Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1 = 0 := by
          nlinarith [sq_nonneg (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1)]
        rw [hx, abs_zero]
      · rw [h] at hsq ⊢
        exact (sq_le_one_iff_abs_le_one _).mp hsq
    calc |Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1|
        ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ := habs
      _ = 1 * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ := (one_mul _).symm
      _ ≤ max (K₀ 0) 1 * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Work.FTS.PhiStar.Honesty.CptApp.omegaInd_nonneg n z θ)
  · -- positive order: the constant `1` drops out and only the radial factor is differentiated
    obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
    show |Work.Spaces.DzIter (k + 1) (fun z θ : ℝ =>
        Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ|
        ≤ max (K₀ (k + 1)) 1 * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
    have hdecomp : Work.Spaces.DzIter (k + 1) (fun z θ : ℝ =>
        Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
        = dz1 (k + 1) (Work.FTS.PhiStar.Honesty.CptApp.chiR n) z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ := by
      rw [errAdj_sep (Work.FTS.PhiStar.Honesty.CptApp.chiR n)
        (Work.FTS.PhiStar.Honesty.CptApp.zetaR n) (k + 1) z θ,
        ite_eq_right (Nat.succ_ne_zero k), sub_zero]
    have hz1 : dz1 (k + 1) (Work.FTS.PhiStar.Honesty.CptApp.chiR n) z
        = Work.Spaces.DzIter (k + 1)
            (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z) z θ :=
      (errAdjDzIter_zOnly (k + 1) (Work.FTS.PhiStar.Honesty.CptApp.chiR n) z θ).symm
    by_cases hmem : (z, θ) ∈ Work.FTS.PhiStar.Honesty.CptApp.Omega n
    · -- on `Ω_n`: the indicator is `1`, `zetaR n` is bounded by `1`, `chiR n` by `K₀`
      rw [Work.FTS.PhiStar.Honesty.CptApp.omegaInd_eq_one_iff.mpr hmem, hdecomp, hz1, mul_one]
      calc |Work.Spaces.DzIter (k + 1)
              (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z) z θ
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ|
          = |Work.Spaces.DzIter (k + 1)
              (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z) z θ|
            * |Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ| := abs_mul _ _
        _ ≤ K₀ (k + 1) * 1 :=
            mul_le_mul (hK₀ n (k + 1) z θ)
              (Work.FTS.PhiStar.Honesty.CptApp.abs_zetaR_le_one n θ)
              (abs_nonneg _) (hK₀nn _)
        _ ≤ max (K₀ (k + 1)) 1 := by rw [mul_one]; exact le_max_left _ _
    · -- off `Ω_n`: both cut-offs are on their plateaus, and `D_z^{k+1}` of `chiR n` vanishes
      have hzero : Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ = 0 := by
        rcases omegaInd_zero_or_one n z θ with h | h
        · exact h
        · exact absurd (Work.FTS.PhiStar.Honesty.CptApp.omegaInd_eq_one_iff.mp h) hmem
      have hnot : ¬(z < 2 / (n : ℝ) ∨ (n : ℝ) < z ∨ θ < 2 / (n : ℝ)
          ∨ Real.pi / 2 - 2 / (n : ℝ) < θ) := by
        intro hc
        exact hmem (by
          rcases hc with h1 | h2 | h3 | h4
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr (Or.inl h3))
          · exact Or.inr (Or.inr (Or.inr h4)))
      push Not at hnot
      obtain ⟨hz1', hz2', hθ1', hθ2'⟩ := hnot
      have hzeta : Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ = 1 :=
        Work.FTS.PhiStar.Honesty.CptApp.zetaR_eq_one hn hθ1' hθ2'
      have hzeroval : Work.Spaces.DzIter (k + 1)
          (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z) z θ = 0 := by
        rw [errAdjDzIter_zOnly (k + 1) (Work.FTS.PhiStar.Honesty.CptApp.chiR n) z θ,
          ← errAdjDzIter_zOnly (k + 1) (Work.FTS.PhiStar.Honesty.CptApp.chiR n) z 0]
        exact estPlateauZero.1 n hn (k + 1) (by omega) z hz1' hz2'
      rw [hzero, hdecomp, hz1, hzeroval, hzeta]
      simp

end Work.FTS.PhiStar.Honesty.CptApp.EstAux
