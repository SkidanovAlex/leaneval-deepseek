/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise slot bound `HardSlotDBound`

The pointwise form of the per-slot bound of the *hard* part of `SpecialTransport`:
after the angular integration by parts, a single slot has the coefficient

  `q·cos(2θ)·sin(2θ)^{-q-1}·f − (1/2)·sin(2θ)^{-q}·∂_θf`,

which the hypotheses `|f| ≤ K·sin(2θ)` and `|∂_θf| ≤ 3K` bound pointwise by
`(qK + 3K/2)·sin(2θ)^{-q}`.  Multiplying by the non-negative factor `(v z θ)²`
(the squared `g`-slot, whose bound `|v| ≤ C·sin(2θ)^p` is *not* needed here — only
its square is used, through non-negativity) gives the stated inequality.

The two elementary facts used are `sin(2θ) ≥ 0` on `Iθ` (so that `sin(2θ)^{-q} ≥ 0`
and `sin(2θ)^{-q-1}·sin(2θ) = sin(2θ)^{-q}` in the interior) and `|cos| ≤ 1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-- On the angular interval `[0, π/2]`, `sin (2θ) ≥ 0`. -/
private theorem sin_two_nonneg_Iθ_aux {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The triangle-type bound `|a - b| ≤ |a| + |b|`. -/
private theorem abs_sub_le_abs_add_aux (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_sub_le_iff]
  exact ⟨by linarith [le_abs_self a, neg_le_abs b], by linarith [le_abs_self b, neg_le_abs a]⟩

/-- The exponent identity `s^{-q-1}·s = s^{-q}` for `s > 0`. -/
private theorem rpow_neg_sub_one_mul_aux (q : ℝ) {s : ℝ} (hs : 0 < s) :
    s ^ (-q - 1) * s = s ^ (-q) := by
  have h2 : s ^ (-q) = s ^ (-q - 1) * s ^ (1 : ℝ) := by
    rw [← Real.rpow_add hs]; ring_nf
  rw [h2, Real.rpow_one]

/-- The pointwise bound on the coefficient produced by the angular integration by
parts: `|q·cos(2θ)·sin(2θ)^{-q-1}·f − (1/2)·sin(2θ)^{-q}·∂_θf| ≤ (qK + 3K/2)·sin(2θ)^{-q}`
on `Iθ`, from `|f| ≤ K·sin(2θ)` and `|∂_θf| ≤ 3K`. -/
private theorem hard_slot_coef_aux {q K : ℝ} (hq0 : 0 < q) (hK : 0 ≤ K)
    {f : ℝ → ℝ → ℝ} {z : ℝ}
    (hf1 : ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ K * Real.sin (2 * θ))
    (hf2 : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.pth f z θ| ≤ 3 * K) :
    ∀ θ ∈ Work.Spaces.Iθ, |q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ
        - (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Work.Spaces.pth f z θ|
      ≤ (q * K + 3 * K / 2) * (Real.sin (2 * θ)) ^ (-q) := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ_aux hθ
  rcases eq_or_lt_of_le hs0 with hs | hs
  · -- endpoint case `sin (2θ) = 0`: both `rpow`s vanish (their exponents are nonzero)
    rw [← hs, Real.zero_rpow (x := -q - 1) (by linarith), Real.zero_rpow (x := -q)
      (by linarith)]
    simp
  · -- interior case: bound each of the two summands separately
    have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
    have h1 : |q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ|
        ≤ q * K * (Real.sin (2 * θ)) ^ (-q) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0 _),
        abs_of_pos hq0]
      calc q * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-q - 1) * |f z θ|
          ≤ q * 1 * (Real.sin (2 * θ)) ^ (-q - 1) * (K * Real.sin (2 * θ)) := by
            gcongr
            · exact hf1 θ hθ
        _ = q * (K * ((Real.sin (2 * θ)) ^ (-q - 1) * Real.sin (2 * θ))) := by ring
        _ = q * (K * (Real.sin (2 * θ)) ^ (-q)) := by rw [rpow_neg_sub_one_mul_aux q hs]
        _ = q * K * (Real.sin (2 * θ)) ^ (-q) := by ring
    have h2 : |(1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Work.Spaces.pth f z θ|
        ≤ (3 * K / 2) * (Real.sin (2 * θ)) ^ (-q) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_nonneg (Real.rpow_nonneg hs0 _)]
      calc (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * |Work.Spaces.pth f z θ|
          ≤ (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * (3 * K) := by
            gcongr
            · exact hf2 θ hθ
        _ = (3 * K / 2) * (Real.sin (2 * θ)) ^ (-q) := by ring
    calc |q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ
          - (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Work.Spaces.pth f z θ|
        ≤ |q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ|
          + |(1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Work.Spaces.pth f z θ| :=
          abs_sub_le_abs_add_aux _ _
      _ ≤ q * K * (Real.sin (2 * θ)) ^ (-q) + (3 * K / 2) * (Real.sin (2 * θ)) ^ (-q) :=
          add_le_add h1 h2
      _ = (q * K + 3 * K / 2) * (Real.sin (2 * θ)) ^ (-q) := by ring

theorem HardSlotDBound {q K C p : ℝ} (hq0 : 0 < q) (hp0 : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    {f v : ℝ → ℝ → ℝ} {z : ℝ}
    (hf1 : ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ K * Real.sin (2 * θ))
    (hf2 : ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.pth f z θ| ≤ 3 * K)
    (hv1 : ∀ θ ∈ Work.Spaces.Iθ, |v z θ| ≤ C * (Real.sin (2 * θ)) ^ p) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |(q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ
          - (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Work.Spaces.pth f z θ) * (v z θ) ^ 2|
        ≤ (q * K + 3 * K / 2) * ((Real.sin (2 * θ)) ^ (-q) * (v z θ) ^ 2) := by
  intro θ hθ
  have hcoef := hard_slot_coef_aux hq0 hK hf1 hf2 θ hθ
  have hvsq : (0 : ℝ) ≤ (v z θ) ^ 2 := sq_nonneg _
  calc |(q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ
          - (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Work.Spaces.pth f z θ) * (v z θ) ^ 2|
      = |q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ
          - (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Work.Spaces.pth f z θ|
        * (v z θ) ^ 2 := by
        rw [abs_mul, abs_of_nonneg hvsq]
    _ ≤ ((q * K + 3 * K / 2) * (Real.sin (2 * θ)) ^ (-q)) * (v z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef hvsq
    _ = (q * K + 3 * K / 2) * ((Real.sin (2 * θ)) ^ (-q) * (v z θ) ^ 2) := by ring

end Work.FTS.H2
