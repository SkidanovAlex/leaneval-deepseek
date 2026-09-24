import Mathlib
import Submission.Work.GM.Affine.FarSplit_defs
import Submission.Work.GM.Affine.FarMass_defs
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.region_I_bound
import Submission.Work.GM.Affine.window_integral_Bsum

/-!
# GM §9, region II: the *window* part of the far weight

Vocabulary for the estimate `Work.GM.Affine.far_window_L2_le_far_mass`, i.e. for the part of the
far weight `Wfar` whose `τ = M₃(ℓ - y)` lies in the *bounded* window `2 < |τ| ≤ B`:

`FarWinSum K B M₁ M₂ M₃ f ξ = Σ_{m₁∈R1 M₁} |m₁|⁻¹ Bsum f M₂ (ξ/m₁) (Wfar - WfarBig)(ξ/m₁)`,

which (for `B ≥ 2`, since the windows nest: `Wfar = Wwin + WfarBig`) keeps exactly the pairs
`(m₁, ℓ) ∈ R1 M₁ × ℤ` with `2/M₃ < |ℓ - ξ/m₁| ≤ B/M₃`.

The objects below are:

* `fwWin K M₃ B y`, the window weight `M₃ Σ_{2/M₃ < |ℓ-y| ≤ B/M₃} ψ̂₁(M₃(ℓ-y))`;
* `fwL T M₁ M₃ B`, an integer bound for the relevant `ℓ`-range at frequencies `|ξ| ≤ T⁶`, and
  `fwProd T M₁ M₃ B = R1 M₁ × [-fwL, fwL]`, the *fixed* finset of candidate pairs;
* `fwP T M₁ M₃ B ξ = fwProd.filter (winCond M₃ B ξ)`, the window pairs at `ξ`;
* `fwA K M₂ M₃ f ξ p`, the summand `|p.1|⁻¹ Bsum f M₂ (ξ/p.1) · M₃ ψ̂₁(M₃(p.2 - ξ/p.1))`;
* `winMajorant K T M₁ M₂ M₃ B f ξ`, the sum of `|p.1|⁻² ‖Bsum f M₂ (ξ/p.1)‖² ‖ψ̂₁(M₃(p.2-ξ/p.1))‖²`
  over the window pairs (so that `‖Σ_{p ∈ fwP} fwA p‖² ≤ ♯fwP · M₃² · winMajorant`);
* `farTauWin B = {τ : 2 < |τ| ≤ B}` and `pairXWin B M₃ m ℓ = {ξ : 2/M₃ < |ℓ - ξ/m| ≤ B/M₃}`,
  the `τ`-form and the `ξ`-form of the window of one pair, identified by `ξ = m (ℓ + τ/M₃)`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The integrand of `Work.GM.Affine.far_window_L2_le_far_mass`. -/
def FarWinSum (K B M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
    (Wfar K M₃ (ξ / (m₁ : ℝ)) - WfarBig K B M₃ (ξ / (m₁ : ℝ)))

/-- The window weight `M₃ Σ_{2/M₃ < |ℓ-y| ≤ B/M₃} ψ̂₁(M₃(ℓ-y))`. -/
def fwWin (K M₃ B y : ℝ) : ℂ :=
  (M₃ : ℂ) * ∑' ℓ : ℤ,
    if 2 / M₃ < |(ℓ : ℝ) - y| ∧ |(ℓ : ℝ) - y| ≤ B / M₃ then
      psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0

/-- An integer bound for the window `ℓ`-range at frequencies `|ξ| ≤ T⁶`. -/
def fwL (T M₁ M₃ B : ℝ) : ℤ := ⌈T ^ 6 / M₁ + B / M₃⌉ + 1

/-- The fixed finset of candidate window pairs. -/
def fwProd (T M₁ M₃ B : ℝ) : Finset (ℤ × ℤ) :=
  (R1 M₁).product (Finset.Icc (-(fwL T M₁ M₃ B)) (fwL T M₁ M₃ B))

/-- The window condition on the pair `p = (m₁,ℓ)` at frequency `ξ`: `2/M₃ < |ℓ - ξ/m₁| ≤ B/M₃`. -/
def winCond (M₃ B : ℝ) (ξ : ℝ) (p : ℤ × ℤ) : Prop :=
  2 / M₃ < |((p.2 : ℝ) - ξ / (p.1 : ℝ))| ∧ |((p.2 : ℝ) - ξ / (p.1 : ℝ))| ≤ B / M₃

instance instDecidablePredWinCond (M₃ B ξ : ℝ) : DecidablePred (winCond M₃ B ξ) :=
  fun p => inferInstanceAs (Decidable (2 / M₃ < |((p.2 : ℝ) - ξ / (p.1 : ℝ))| ∧
    |((p.2 : ℝ) - ξ / (p.1 : ℝ))| ≤ B / M₃))

/-- The window pairs at frequency `ξ`. -/
def fwP (T M₁ M₃ B : ℝ) (ξ : ℝ) : Finset (ℤ × ℤ) :=
  (fwProd T M₁ M₃ B).filter (winCond M₃ B ξ)

/-- The summand attached to the pair `p = (m₁,ℓ)`. -/
def fwA (K M₂ M₃ : ℝ) (f : ℝ → ℝ) (ξ : ℝ) (p : ℤ × ℤ) : ℂ :=
  ((|(p.1 : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (p.1 : ℝ)) *
    ((M₃ : ℂ) * psi1hat K (M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ))))

/-- The weighted pair majorant of `‖FarWinSum‖²`. -/
def winMajorant (K T M₁ M₂ M₃ B : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∑ p ∈ fwProd T M₁ M₃ B,
    (if winCond M₃ B ξ p then
      (1 / (p.1 : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2 *
        ‖psi1hat K (M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ)))‖ ^ 2 else 0)

/-- The `τ`-window `{τ : 2 < |τ| ≤ B}`. -/
def farTauWin (B : ℝ) : Set ℝ := Set.Ioc 2 B ∪ Set.Ico (-B) (-2)

/-- The `ξ`-window of the pair `(m, ℓ)`: `{ξ : 2/M₃ < |ℓ - ξ/m| ≤ B/M₃}`. -/
def pairXWin (B M₃ : ℝ) (m ℓ : ℤ) : Set ℝ :=
  Set.Ico ((m : ℝ) * (ℓ : ℝ) - B * |(m : ℝ)| / M₃) ((m : ℝ) * (ℓ : ℝ) - 2 * |(m : ℝ)| / M₃) ∪
  Set.Ioc ((m : ℝ) * (ℓ : ℝ) + 2 * |(m : ℝ)| / M₃) ((m : ℝ) * (ℓ : ℝ) + B * |(m : ℝ)| / M₃)

lemma fwP_eq_filter (T M₁ M₃ B ξ : ℝ) :
    fwP T M₁ M₃ B ξ = (fwProd T M₁ M₃ B).filter (winCond M₃ B ξ) := rfl

lemma mem_farTauWin_iff {B τ : ℝ} : τ ∈ farTauWin B ↔ 2 < |τ| ∧ |τ| ≤ B := by
  rw [farTauWin, Set.mem_union, Set.mem_Ioc, Set.mem_Ico, lt_abs, abs_le]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Or.inl (by linarith), ⟨by linarith, by linarith⟩⟩
    · exact ⟨Or.inr (by linarith), ⟨by linarith, by linarith⟩⟩
  · rintro ⟨h1 | h1, h3, h4⟩
    · left; exact ⟨by linarith, by linarith⟩
    · right; exact ⟨by linarith, by linarith⟩

/-- The `ξ`-window of a pair and the window condition on that pair describe the same set of
frequencies. -/
lemma mem_pairXWin_iff {B M₃ : ℝ} (hM₃ : 0 < M₃) {m : ℤ} (hm : m ≠ 0)
    (ℓ : ℤ) (ξ : ℝ) : ξ ∈ pairXWin B M₃ m ℓ ↔ winCond M₃ B ξ (m, ℓ) := by
  have hmR : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hc : 0 < |(m : ℝ)| := abs_pos.mpr hmR
  have h2c : (0:ℝ) < 2 * |(m : ℝ)| / M₃ := by positivity
  have hkey : |(ℓ : ℝ) - ξ / (m : ℝ)| = |ξ - (m : ℝ) * (ℓ : ℝ)| / |(m : ℝ)| := by
    rw [show (ℓ : ℝ) - ξ / (m : ℝ) = ((m : ℝ) * (ℓ : ℝ) - ξ) / (m : ℝ) by field_simp]
    rw [abs_div, abs_sub_comm]
  rw [winCond, hkey, pairXWin, Set.mem_union, Set.mem_Ico, Set.mem_Ioc]
  have hconv1 : 2 / M₃ < |ξ - (m : ℝ) * (ℓ : ℝ)| / |(m : ℝ)|
      ↔ 2 * |(m : ℝ)| / M₃ < |ξ - (m : ℝ) * (ℓ : ℝ)| := by
    rw [lt_div_iff₀ hc, div_mul_eq_mul_div]
  have hconv2 : |ξ - (m : ℝ) * (ℓ : ℝ)| / |(m : ℝ)| ≤ B / M₃
      ↔ |ξ - (m : ℝ) * (ℓ : ℝ)| ≤ B * |(m : ℝ)| / M₃ := by
    rw [div_le_iff₀ hc, div_mul_eq_mul_div]
  rw [hconv1, hconv2]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have h3 : ξ - (m : ℝ) * (ℓ : ℝ) < 0 := by linarith
      rw [abs_of_neg h3]
      constructor <;> linarith
    · have h3 : 0 ≤ ξ - (m : ℝ) * (ℓ : ℝ) := by linarith
      rw [abs_of_nonneg h3]
      constructor <;> linarith
  · rintro ⟨h1, h2⟩
    by_cases hcase : (m : ℝ) * (ℓ : ℝ) ≤ ξ
    · right
      have h3 : 0 ≤ ξ - (m : ℝ) * (ℓ : ℝ) := by linarith
      rw [abs_of_nonneg h3] at h1 h2
      exact ⟨by linarith, by linarith⟩
    · left
      have h3 : ξ - (m : ℝ) * (ℓ : ℝ) < 0 := by linarith
      rw [abs_of_neg h3] at h1 h2
      exact ⟨by linarith, by linarith⟩

end

end Work.GM.Affine
