import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.ULPMAsm
import Submission.Work.WilC0.Main
import Submission.Work.WilC4.RatioLowerDefs
import Submission.Work.WilC4.argInv_definable
import Submission.Work.WilC4.rpow_ratio_bound

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr)

variable {k : ℕ}

theorem ratio_lower_zero {k : ℕ}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (B : Set (Fin (k + 1) → ℝ)) (N₀ : ℕ)
    (hBcard : ∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ B}.encard ≤ N₀)
    (hgf : Work.WilC4.GoodFibre Y B) :
    ∃ m : ℝ, 0 < m ∧ ∀ c : Fin k → ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      ∀ y y' : ℝ, Work.WilC4.Route.Gr Y c t y → Work.WilC4.Route.Gr Y c (2 * t) y' →
        y ≠ 0 → m * |y| ≤ |y'| := by
  -- ## The argument-inverted family `W = ArgInv Y`, to which `hPB` applies
  have hWdef : (∅ : Set ℝ).Definable LRc (ArgInv Y) := argInv_definable hY
  have hWfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ),
      Gr (ArgInv Y) c x y → Gr (ArgInv Y) c x y' → y = y' := argInv_functional hfun
  have hWrex : WilkiesDesign.RExpExist (ArgInv Y) :=
    WilkiesDesign.CG.C0_rexp_syntax_proved hR (ArgInv Y) hWdef
  obtain ⟨Qs, hQs⟩ := hPB k (ArgInv Y) hWrex hWfun
  -- ## The core: given any `m` below every `2^{-q}/4` (`q ∈ Qs`), the conclusion holds
  have hmain : ∀ m : ℝ, 0 < m → (∀ q ∈ Qs, m ≤ (2 : ℝ) ^ (-(q : ℝ)) / 4) →
      ∀ c : Fin k → ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
        ∀ y y' : ℝ, Gr Y c t y → Gr Y c (2 * t) y' → y ≠ 0 → m * |y| ≤ |y'| := by
    intro m hm hmlt c
    rcases hQs c with ⟨R, hRb⟩ | ⟨q, hqQs, a, ha, hasym⟩
    · -- the inverted fibre is eventually zero: the conclusion is vacuous
      have hMpos : (0 : ℝ) < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
      refine ⟨(max R 1)⁻¹, inv_pos.mpr hMpos, ?_⟩
      intro t ht0 htδ y y' hy hy' hy0
      exfalso
      have htinv_ge : max R 1 ≤ t⁻¹ := (le_inv_comm₀ ht0 hMpos).mp htδ
      have hRle : R ≤ t⁻¹ := le_trans (le_max_left R 1) htinv_ge
      have hgW : Gr (ArgInv Y) c t⁻¹ y :=
        (gr_argInv_iff Y c t⁻¹ y).mpr
          ⟨inv_ne_zero (ne_of_gt ht0), by simpa [inv_inv] using hy⟩
      exact hy0 (hRb t⁻¹ y hRle hgW)
    · -- the inverted fibre is asymptotic to `a · x^q`: the ratio is bounded below
      have haabs : 0 < |a| / 2 := half_pos (abs_pos.mpr ha)
      obtain ⟨R', hRs⟩ := hasym (|a| / 2) haabs
      have hMpos : (0 : ℝ) < max R' 1 := lt_of_lt_of_le zero_lt_one (le_max_right R' 1)
      have h2Mpos : (0 : ℝ) < 2 * max R' 1 := by linarith
      refine ⟨(2 * max R' 1)⁻¹, inv_pos.mpr h2Mpos, ?_⟩
      intro t ht0 htδ y y' hy hy' hy0
      have htinv_ge : 2 * max R' 1 ≤ t⁻¹ := (le_inv_comm₀ ht0 h2Mpos).mp htδ
      have h1ge : R' ≤ t⁻¹ := by linarith [htinv_ge, le_max_left R' 1]
      have h2ge : R' ≤ t⁻¹ / 2 := by linarith [htinv_ge, le_max_left R' 1]
      have hgW : Gr (ArgInv Y) c t⁻¹ y :=
        (gr_argInv_iff Y c t⁻¹ y).mpr
          ⟨inv_ne_zero (ne_of_gt ht0), by simpa [inv_inv] using hy⟩
      have hinv : (t⁻¹ / 2)⁻¹ = 2 * t := by
        rw [div_eq_mul_inv, mul_inv, inv_inv, inv_inv]; ring
      have hgW' : Gr (ArgInv Y) c (t⁻¹ / 2) y' :=
        (gr_argInv_iff Y c (t⁻¹ / 2) y').mpr
          ⟨div_ne_zero (inv_ne_zero (ne_of_gt ht0)) (by norm_num),
            by rw [hinv]; exact hy'⟩
      have h1 : |y / (t⁻¹) ^ (q : ℝ) - a| < |a| / 2 := hRs t⁻¹ y h1ge hgW
      have h2 : |y' / (t⁻¹ / 2) ^ (q : ℝ) - a| < |a| / 2 := hRs (t⁻¹ / 2) y' h2ge hgW'
      have hb := rpow_ratio_bound ha (inv_pos.mpr ht0) h1 h2
      exact le_trans (mul_le_mul_of_nonneg_right (hmlt q hqQs) (abs_nonneg y)) hb
  -- ## The uniform constant
  by_cases hne : Qs.Nonempty
  · refine ⟨(2 : ℝ) ^ (-(((Qs.max' hne : ℚ) : ℝ))) / 4, ?_, ?_⟩
    · exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)
    · refine hmain _ (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)) ?_
      intro q hq
      have hqle : q ≤ Qs.max' hne := Finset.le_max' Qs q hq
      have hcast : (q : ℝ) ≤ ((Qs.max' hne : ℚ) : ℝ) := by exact_mod_cast hqle
      have hexp : -(((Qs.max' hne : ℚ) : ℝ)) ≤ -(q : ℝ) := by linarith
      have h2le : (2 : ℝ) ^ (-(((Qs.max' hne : ℚ) : ℝ))) ≤ (2 : ℝ) ^ (-(q : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      linarith [div_le_div_of_nonneg_right h2le (by norm_num : (0 : ℝ) ≤ 4)]
  · refine ⟨1, one_pos, hmain 1 one_pos ?_⟩
    intro q hq
    exact absurd ⟨q, hq⟩ hne

end Work.WilC4
