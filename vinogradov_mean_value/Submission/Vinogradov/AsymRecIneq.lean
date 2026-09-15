/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymRec
import Submission.Vinogradov.Section4Exp

/-!
# GLYZ §4: the recursion as an inequality between the infima `A_l(b)`

The recursion of `AsymRec.lean` is a statement about `AsymExpSet`; the exponent bootstrap
(`Commons.Analysis.Asymptotics.exponent_bootstrap_nonpos`) consumes it as an inequality between the
infima `Aexp k hk l b = sInf (AsymExpSet k hk l b)`.  This module performs the passage:

* `asymExpSet_recursion_ineq` (splits `l ≥ 2`) and `asymExpSet_recursion_one_ineq` (the split
  `l = 1`) state, eventually for `b → 0⁺`,
  `A_l(b) ≤ θ·A_{k−l}(ρb) + (1−θ)·A_{l−1}(b)` with `θ = 1/(k−l+1)`, `ρ = asymRatio k l`
  (for `l = 1` the second term is `(1−θ)·η(1−b)` with `η = etaLin k`, the `l = 0` brick).
* `Aexp_zero_le_etaLin` is the easy direction of `A_0(b) = η(1−b)`.

The models `DecLinScale L M (laneEnl k L hk hl hlk) (ofReal (a₀ M^εm))` are hypotheses for EVERY
`εm > 0`; the passage to the limit `εm → 0` (and, in the `l = 1` case, `e → η`) is what makes the
recursion an inequality without an error term.

The module is imported by `ROADMAP.lean` only; it is not on the comparator chain.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Submission.Vinogradov

/-- **The easy direction of `A_0(b) = η(1−b)`.** -/
theorem Aexp_zero_le_etaLin (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ), Aexp k hk 0 b ≤ etaLin k * (1 - b) := by
  have hev : ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ), 0 < b ∧ b ≤ 1 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iic_mem_nhds (show (0:ℝ) < 1 by norm_num)] with b hb hb0
    exact ⟨hb0, hb⟩
  refine hev.mono fun b hb => ?_
  obtain ⟨hb0, hb1⟩ := hb
  have hne : (linExpSet k).Nonempty := linExpSet_nonempty k hk
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hlt : etaLin k < etaLin k + δ / 2 := by linarith
  obtain ⟨e, he, hee⟩ := (csInf_lt_iff (bddBelow_linExpSet k) hne).mp hlt
  have hmem : e * (1 - b) ∈ AsymExpSet k hk 0 b :=
    mem_asymExpSet_zero_of_linExpSet hk he hb0 hb1
  have h1 : Aexp k hk 0 b ≤ e * (1 - b) := Aexp_le_of_mem hmem
  have h2 : e * (1 - b) ≤ etaLin k * (1 - b) + δ / 2 := by
    have h3 : e ≤ etaLin k + δ / 2 := le_of_lt hee
    have h4 : 0 ≤ 1 - b := by linarith
    have h5 : e * (1 - b) ≤ (etaLin k + δ / 2) * (1 - b) :=
      mul_le_mul_of_nonneg_right h3 h4
    have h6 : (etaLin k + δ / 2) * (1 - b) = etaLin k * (1 - b) + δ / 2 * (1 - b) := by ring
    have h7 : δ / 2 * (1 - b) ≤ δ / 2 := by
      have h8 : 1 - b ≤ 1 := by linarith
      nlinarith [hδ.le, h8]
    linarith [h5, h6, h7]
  linarith

lemma eventually_pos_le_b₀ (k : ℕ) : ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ), 0 < b ∧ b ≤ b₀ k := by
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iic_mem_nhds (b₀_pos k)] with b hb hb0
  exact ⟨hb0, hb⟩

/-- **The recursion for `l ≥ 2` as an inequality between the infima `Aexp`.** -/
theorem asymExpSet_recursion_ineq {k l : ℕ} (hk : 1 ≤ k) (hl : 2 ≤ l) (hlk : l ≤ k - 1)
    (hmMod₁ : ∀ (εm : ℝ), 0 < εm → ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ M : ℕ, 1 ≤ M →
      DecLinScale (k - l) M
        (laneEnl k (k - l) hk (by omega) (by omega)) (ENNReal.ofReal (a₀ * (M : ℝ) ^ εm)))
    (hmMod₂ : ∀ (εm : ℝ), 0 < εm → ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ M : ℕ, 1 ≤ M →
      DecLinScale (l - 1) M
        (laneEnl k (l - 1) hk (by omega) (by omega)) (ENNReal.ofReal (a₀ * (M : ℝ) ^ εm))) :
    ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ),
      Aexp k hk l b ≤ (1 / ((k:ℝ) - (l:ℝ) + 1)) * Aexp k hk (k - l) (asymRatio k l * b)
        + (((k:ℝ) - (l:ℝ)) / ((k:ℝ) - (l:ℝ) + 1)) * Aexp k hk (l - 1) b := by
  have hl1 : 1 ≤ l := by omega
  have hkl : (l:ℝ) ≤ (k:ℝ) := by
    have : l ≤ k := by omega
    exact_mod_cast this
  have hden : 0 < (k:ℝ) - (l:ℝ) + 1 := by linarith
  set θ : ℝ := 1 / ((k:ℝ) - (l:ℝ) + 1) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg zero_le_one hden.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hden]; linarith
  have h1θeq : 1 - θ = ((k:ℝ) - (l:ℝ)) / ((k:ℝ) - (l:ℝ) + 1) := by
    rw [hθ]; field_simp; ring
  have hrec0 : 0 ≤ recC k l := by
    rw [recC]
    have h1 : 0 ≤ max (gRatio₁ k l) (gRatio₂ k l) :=
      le_trans (le_of_lt (gRatio₁_pos hl1 hlk)) (le_max_left _ _)
    linarith
  refine (eventually_pos_le_b₀ k).mono fun b hb => ?_
  obtain ⟨hb0, hb1⟩ := hb
  have hb1' : b ≤ 1 := le_trans hb1 (b₀_le_one k)
  have hρ1 : asymRatio k l * b ≤ 1 :=
    asymRatio_mul_b_le_one hk hl1 (by omega) hb0.le hb1
  have hne₁ : (AsymExpSet k hk (k - l) (asymRatio k l * b)).Nonempty :=
    asymExpSet_nonempty k hk (by omega) (mul_pos (asymRatio_pos' hk hlk) hb0) hρ1
      (asymRatio_mul_asymRatio_mul_le_one hk hl1 hlk hb0.le hb1)
  have hne₂ : (AsymExpSet k hk (l - 1) b).Nonempty :=
    asymExpSet_nonempty k hk (by omega) hb0 hb1'
      (asymRatio_pred_mul_le_one hk hl hlk hb0.le hb1)
  rw [← h1θeq]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε : ℝ := δ / 4 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hmpos : 0 < recC k l * b + 1 := by nlinarith [hrec0, hb0]
  set εm : ℝ := δ / (4 * (recC k l * b + 1)) with hεm
  have hεm0 : 0 < εm := by
    rw [hεm]
    exact div_pos hδ (by linarith)
  obtain ⟨A₁, hA₁mem, hA₁lt⟩ :=
    (csInf_lt_iff (bddBelow_asymExpSet k hk (k - l) (asymRatio k l * b)) hne₁).mp
      (show Aexp k hk (k - l) (asymRatio k l * b)
          < Aexp k hk (k - l) (asymRatio k l * b) + ε by linarith)
  obtain ⟨A₂, hA₂mem, hA₂lt⟩ :=
    (csInf_lt_iff (bddBelow_asymExpSet k hk (l - 1) b) hne₂).mp
      (show Aexp k hk (l - 1) b < Aexp k hk (l - 1) b + ε by linarith)
  have hle := asymExpSet_recursion hk hl hlk hεm0 hmMod₁ hmMod₂ hb0 hb1 hA₁mem hA₂mem
  have hle' : θ * A₁ + (1 - θ) * A₂ + recC k l * εm * b ∈ AsymExpSet k hk l b := by
    rw [hθ, h1θeq]
    exact hle
  have hmain : Aexp k hk l b ≤ θ * A₁ + (1 - θ) * A₂ + recC k l * εm * b :=
    Aexp_le_of_mem hle'
  have hstep1 : θ * A₁ ≤ θ * (Aexp k hk (k - l) (asymRatio k l * b) + ε) :=
    mul_le_mul_of_nonneg_left hA₁lt.le hθ0
  have hstep2 : (1 - θ) * A₂ ≤ (1 - θ) * (Aexp k hk (l - 1) b + ε) :=
    mul_le_mul_of_nonneg_left hA₂lt.le (by linarith)
  have hsmall : θ * ε + (1 - θ) * ε + recC k l * εm * b ≤ δ := by
    have h1 : θ * ε ≤ δ / 4 := by
      have : θ * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right hθ1 hε0.le
      rw [hε] at this ⊢
      linarith
    have h2 : (1 - θ) * ε ≤ δ / 4 := by
      have : (1 - θ) * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right (by linarith) hε0.le
      rw [hε] at this ⊢
      linarith
    have h3 : recC k l * εm * b ≤ δ / 4 := by
      have h4 : recC k l * b ≤ recC k l * b + 1 := by linarith
      have h5 : recC k l * b * δ ≤ (recC k l * b + 1) * δ :=
        mul_le_mul_of_nonneg_right h4 hδ.le
      rw [hεm]
      rw [show recC k l * (δ / (4 * (recC k l * b + 1))) * b
          = recC k l * b * δ / (4 * (recC k l * b + 1)) from by ring]
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 4 * (recC k l * b + 1))]
      linarith
    linarith
  have hexpand : θ * (Aexp k hk (k - l) (asymRatio k l * b) + ε)
      + (1 - θ) * (Aexp k hk (l - 1) b + ε) + recC k l * εm * b
      = (θ * Aexp k hk (k - l) (asymRatio k l * b) + (1 - θ) * Aexp k hk (l - 1) b)
        + (θ * ε + (1 - θ) * ε + recC k l * εm * b) := by ring
  nlinarith [hmain, hstep1, hstep2, hsmall, hexpand]

/-- **The recursion for `l = 1` as an inequality between the infima `Aexp`.**  The second term is
`η(1−b)` with `η = etaLin k`: this is the eventual equality `A_0(b) = η(1−b)` in the direction
`Aexp 0 b ≤ η(1−b)` (the other direction is not needed for the recursion). -/
theorem asymExpSet_recursion_one_ineq {k : ℕ} (hk : 1 ≤ k) (hk2 : 1 ≤ k - 1)
    (hmMod₁ : ∀ (εm : ℝ), 0 < εm → ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ M : ℕ, 1 ≤ M →
      DecLinScale (k - 1) M
        (laneEnl k (k - 1) hk (by omega) (by omega)) (ENNReal.ofReal (a₀ * (M : ℝ) ^ εm))) :
    ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ),
      Aexp k hk 1 b ≤ (1 / (k:ℝ)) * Aexp k hk (k - 1) (asymRatio k 1 * b)
        + (((k:ℝ) - 1) / (k:ℝ)) * (etaLin k * (1 - b)) := by
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hden : 0 < (k:ℝ) := by linarith
  set θ : ℝ := 1 / (k:ℝ) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg zero_le_one hden.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hden]; linarith
  have h1θeq : 1 - θ = ((k:ℝ) - 1) / (k:ℝ) := by
    rw [hθ]; field_simp
  have hrec0 : 0 ≤ recC k 1 := by
    rw [recC]
    have h1 : 0 ≤ max (gRatio₁ k 1) (gRatio₂ k 1) :=
      le_trans (le_of_lt (gRatio₁_pos (le_refl 1) hk2)) (le_max_left _ _)
    linarith
  have hne : (linExpSet k).Nonempty := linExpSet_nonempty k hk
  refine (eventually_pos_le_b₀ k).mono fun b hb => ?_
  obtain ⟨hb0, hb1⟩ := hb
  have hb1' : b ≤ 1 := le_trans hb1 (b₀_le_one k)
  rw [← h1θeq]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε : ℝ := δ / 4 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hmpos : 0 < recC k 1 * b + 1 := by nlinarith [hrec0, hb0]
  set εm : ℝ := δ / (4 * (recC k 1 * b + 1)) with hεm
  have hεm0 : 0 < εm := by rw [hεm]; exact div_pos hδ (by linarith)
  -- the exponent `e` of the second factor
  obtain ⟨e, he, hee⟩ :=
    (csInf_lt_iff (bddBelow_linExpSet k) hne).mp
      (show etaLin k < etaLin k + δ / 8 by linarith)
  have hA₂mem : e * (1 - b) ∈ AsymExpSet k hk 0 b :=
    mem_asymExpSet_zero_of_linExpSet hk he hb0 hb1'
  -- the first factor
  have hρ1 : asymRatio k 1 * b ≤ 1 :=
    asymRatio_mul_b_le_one hk (le_refl 1) (by omega) hb0.le hb1
  have hne₁ : (AsymExpSet k hk (k - 1) (asymRatio k 1 * b)).Nonempty :=
    asymExpSet_nonempty k hk (by omega) (mul_pos (asymRatio_pos' hk hk2) hb0) hρ1
      (asymRatio_mul_asymRatio_mul_le_one hk (le_refl 1) hk2 hb0.le hb1)
  obtain ⟨A₁, hA₁mem, hA₁lt⟩ :=
    (csInf_lt_iff (bddBelow_asymExpSet k hk (k - 1) (asymRatio k 1 * b)) hne₁).mp
      (show Aexp k hk (k - 1) (asymRatio k 1 * b)
          < Aexp k hk (k - 1) (asymRatio k 1 * b) + ε by linarith)
  have hle := asymExpSet_recursion_one hk hk2 hεm0 hmMod₁ hb0 hb1
    hA₁mem hA₂mem
  have hle' : θ * A₁ + (1 - θ) * (e * (1 - b)) + recC k 1 * εm * b
      ∈ AsymExpSet k hk 1 b := by
    rw [hθ, h1θeq]
    exact hle
  have hmain : Aexp k hk 1 b ≤ θ * A₁ + (1 - θ) * (e * (1 - b)) + recC k 1 * εm * b :=
    Aexp_le_of_mem hle'
  have hstep1 : θ * A₁ ≤ θ * (Aexp k hk (k - 1) (asymRatio k 1 * b) + ε) :=
    mul_le_mul_of_nonneg_left hA₁lt.le hθ0
  have hstep2 : (1 - θ) * (e * (1 - b))
      ≤ (1 - θ) * (etaLin k * (1 - b) + δ / 8) := by
    have h3 : e ≤ etaLin k + δ / 8 := le_of_lt hee
    have h4 : 0 ≤ 1 - b := by linarith
    have h5 : e * (1 - b) ≤ (etaLin k + δ / 8) * (1 - b) :=
      mul_le_mul_of_nonneg_right h3 h4
    have h6 : (etaLin k + δ / 8) * (1 - b)
        = etaLin k * (1 - b) + δ / 8 * (1 - b) := by ring
    have h7 : δ / 8 * (1 - b) ≤ δ / 8 := by
      have h8 : 1 - b ≤ 1 := by linarith
      nlinarith [hδ.le, h8]
    have h9 : e * (1 - b) ≤ etaLin k * (1 - b) + δ / 8 := by linarith [h5, h6, h7]
    exact mul_le_mul_of_nonneg_left h9 (by linarith)
  have hsmall : θ * ε + (1 - θ) * (δ / 8) + recC k 1 * εm * b ≤ δ := by
    have h1 : θ * ε ≤ δ / 4 := by
      have : θ * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right hθ1 hε0.le
      rw [hε] at this ⊢
      linarith
    have h2 : (1 - θ) * (δ / 8) ≤ δ / 8 := by
      have : (1 - θ) * (δ / 8) ≤ 1 * (δ / 8) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      linarith
    have h3 : recC k 1 * εm * b ≤ δ / 4 := by
      have h4 : recC k 1 * b ≤ recC k 1 * b + 1 := by linarith
      have h5 : recC k 1 * b * δ ≤ (recC k 1 * b + 1) * δ :=
        mul_le_mul_of_nonneg_right h4 hδ.le
      rw [hεm]
      rw [show recC k 1 * (δ / (4 * (recC k 1 * b + 1))) * b
          = recC k 1 * b * δ / (4 * (recC k 1 * b + 1)) from by ring]
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 4 * (recC k 1 * b + 1))]
      linarith
    linarith
  have hexpand : θ * (Aexp k hk (k - 1) (asymRatio k 1 * b) + ε)
      + (1 - θ) * (etaLin k * (1 - b) + δ / 8) + recC k 1 * εm * b
      = (θ * Aexp k hk (k - 1) (asymRatio k 1 * b) + (1 - θ) * (etaLin k * (1 - b)))
        + (θ * ε + (1 - θ) * (δ / 8) + recC k 1 * εm * b) := by ring
  nlinarith [hmain, hstep1, hstep2, hsmall, hexpand]

/-- The decoupling exponent is nonnegative (the exponent set is contained in `[0,∞)`). -/
lemma etaLin_nonneg (k : ℕ) (hk : 1 ≤ k) : 0 ≤ etaLin k :=
  le_csInf (linExpSet_nonempty k hk) fun e he => he.1

end Submission.Vinogradov
