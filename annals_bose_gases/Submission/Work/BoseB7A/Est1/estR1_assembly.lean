import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7A.Est1.estR1_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.Est1.estR1_assembly` — the assembly of piece **C**

Given the four pieces of the `R1` estimate

* `hsplit` — `R1` is the sum `Wta + Wb1 + Wb2` of its three words;
* `hWta` — the θ-word is bounded below by `-(costTa)‖Φ‖² - (b/800)ℓ⁻²⟨n₊⟩`;
* `hWb1`, `hWb2` — the two squeezed words are bounded below by
  `-(costB_i)‖Φ‖² - (𝓁²/8)⟨dNumOpR(P_H^q)⟩`;
* `harith` — `costTa + costB2 + costB3 ≤ C·e1A`,

the estimate of piece **C** of FS `eq:EstimateQ3Tilde1` follows: split `qw` over
the three words, note that the gap word dominates its `ℓ⁻²n₊` piece, spend the
quarter-region reserve as `𝓁²/8 + 𝓁²/8` and compare the constants.
-/

noncomputable section

open scoped BigOperators

set_option linter.unusedVariables false

namespace Work.BoseB7A

namespace Est1

open Work.BoseB7

universe u v

/-- **The assembly of `estR1`.** -/
theorem estR1_of_pieces (K₀ b₀ : ℝ) (hb₀ : 0 < b₀)
    (hsplit : ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
      (F : FockData.{u, v} Mode) (T : TildeData.{u, v} F) (E : Q3Env.{u} Mode),
      R1 F T E = Wta F T E + Wb1 F T E + Wb2 F T E)
    (hWta : ∃ t : ℝ, 0 < t ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData.{u, v} Mode) (T : TildeData.{u, v} F) (E : Q3Env.{u} Mode)
        (hv : FSParamsView E),
        hv.t ≤ t → b₀ ≤ E.b → Q3Kernel K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          - (costTa K₀ E hv) * F.normSq Φ
              - (E.b / 800) * E.ell ^ (-(2 : ℝ)) * F.bp (T.N Φ) Φ
            ≤ F.qw Φ (Wta F T E))
    (hWb1 : ∃ t : ℝ, 0 < t ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData.{u, v} Mode) (T : TildeData.{u, v} F) (E : Q3Env.{u} Mode)
        (hv : FSParamsView E),
        hv.t ≤ t → b₀ ≤ E.b → Q3Kernel K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          - (costB2 K₀ E) * F.normSq Φ
              - (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
            ≤ F.qw Φ (Wb1 F T E))
    (hWb2 : ∃ t : ℝ, 0 < t ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData.{u, v} Mode) (T : TildeData.{u, v} F) (E : Q3Env.{u} Mode)
        (hv : FSParamsView E),
        hv.t ≤ t → b₀ ≤ E.b → Q3Kernel K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          - (costB3 K₀ E) * F.normSq Φ
              - (E.lille ^ 2 / 8) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
            ≤ F.qw Φ (Wb2 F T E))
    (harith : ∃ C t : ℝ, 0 ≤ C ∧ 0 < t ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode]
        (E : Q3Env.{u} Mode) (hv : FSParamsView E),
        hv.t ≤ t → b₀ ≤ E.b →
        costTa K₀ E hv + costB2 K₀ E + costB3 K₀ E ≤ C * e1A E) :
    ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧
      ∀ {Mode : Type u} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData.{u, v} Mode) (T : TildeData.{u, v} F) (E : Q3Env.{u} Mode)
        (hv : FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Q3Kernel K₀ F T E →
        ∀ Φ : F.H, T.NWindow E.bigM Φ →
          -(C * e1A E) * F.normSq Φ
              - (E.lille ^ 2 / 4) * F.qw Φ (F.dNumOpR E (F.PHq E.KH E.aScat))
              - (E.b / 800) * F.qw Φ (T.gapOpT E)
            ≤ F.qw Φ (R1 F T E) := by
  obtain ⟨t₁, ht₁, H₁⟩ := hWta
  obtain ⟨t₂, ht₂, H₂⟩ := hWb1
  obtain ⟨t₃, ht₃, H₃⟩ := hWb2
  obtain ⟨C, t₄, hC, ht₄, H₄⟩ := harith
  refine ⟨C, min t₁ (min t₂ (min t₃ t₄)), hC,
    lt_min ht₁ (lt_min ht₂ (lt_min ht₃ ht₄)), ?_⟩
  intro Mode _ _ _ F T E hv hle hb hK Φ hΦ
  have h1 : hv.t ≤ t₁ := le_trans hle (min_le_left _ _)
  have h2 : hv.t ≤ t₂ := le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : hv.t ≤ t₃ :=
    le_trans hle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have h4 : hv.t ≤ t₄ :=
    le_trans hle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have w1 := H₁ F T E hv h1 hb hK Φ hΦ
  have w2 := H₂ F T E hv h2 hb hK Φ hΦ
  have w3 := H₃ F T E hv h3 hb hK Φ hΦ
  have ha := H₄ E hv h4 hb
  -- the gap word contains its `ℓ⁻² n₊` piece
  have hgap : (E.b / 800) * (E.ell ^ (-(2 : ℝ)) * F.bp (T.N Φ) Φ)
      ≤ (E.b / 800) * F.qw Φ (T.gapOpT E) := by
    have hell : 0 < E.ell := Work.BoseB7.ell_pos E hv
    have hd : 0 < E.d := by rw [hv.d_eq]; exact Work.BoseBox.fsXp_pos hv.t_pos
    have hNH : 0 ≤ F.bp (T.NH Φ) Φ := T.NH_nonneg Φ
    have hcoef : 0 ≤ E.eT * (E.d * E.ell) ^ (-(2 : ℝ)) :=
      mul_nonneg (eT_nonneg E hv) (Real.rpow_nonneg (mul_pos hd hell).le _)
    have hgapOp : F.qw Φ (T.gapOpT E)
        = E.ell ^ (-(2 : ℝ)) * F.bp (T.N Φ) Φ
          + (E.eT * (E.d * E.ell) ^ (-(2 : ℝ))) * F.bp (T.NH Φ) Φ := by
      rw [TildeData.gapOpT, FockData.qw_add, FockData.qw_smul, FockData.qw_smul]
      simp only [FockData.qw]
    rw [hgapOp]
    have hb0 : 0 ≤ E.b / 800 := div_nonneg (le_trans hb₀.le hb) (by norm_num)
    nlinarith [mul_nonneg hcoef hNH, hb0]
  -- split `R1` and expand `qw`
  have hq : F.qw Φ (R1 F T E)
      = F.qw Φ (Wta F T E) + F.qw Φ (Wb1 F T E) + F.qw Φ (Wb2 F T E) := by
    rw [hsplit F T E]
    simp only [FockData.qw_add]
  rw [hq]
  have hcost : (costTa K₀ E hv + costB2 K₀ E + costB3 K₀ E) * F.normSq Φ
      ≤ (C * e1A E) * F.normSq Φ :=
    mul_le_mul_of_nonneg_right ha (F.normSq_nonneg Φ)
  have hnn : 0 ≤ F.normSq Φ := F.normSq_nonneg Φ
  nlinarith [w1, w2, w3, hgap, hcost, hnn]

end Est1

end Work.BoseB7A
