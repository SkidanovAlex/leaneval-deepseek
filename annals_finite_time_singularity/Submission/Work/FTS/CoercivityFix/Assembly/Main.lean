/-
# `Assembly/Main.lean` — the assembly of the headline `UnifIP`

This module assembles the corrected coercivity node N2

  `∃ IP α₂ cc clo Cup Ccs, UnifIP IP α₂ cc clo Cup Ccs`   (`Work.FTS.Nonlin.UnifIP`)

from the pieces proved in `Submission/Work/FTS/CoercivityFix/`:

* `Assembly.V_core` — the five membership-free/algebraic clauses of `IP4`
  (`symm`, `add_fst`, `smul_fst`, `congr_qd`, `nonneg`);
* `Assembly.coerData2_four` — the corrected induction for the **clean** operator
  `𝓛̂ = 𝓛 − Transport`, giving the level-`4` Cauchy–Schwarz bound and the level-`4`
  coercivity `cc₄|f|²_{ℋ⁴} ≤ IP4 … α (𝓛̂ f) f` on `RegQ α 5`, for every `α ∈ (0, 1/4]`,
  with coefficients independent of `α`;
* `Assembly.V_bounds` — `lo`, `up` and `Dz_self` on `CoerAdm`;
* `Assembly.exists_coerAdm_pos` — non-vacuity of the class (`witF`, a compactly supported
  `w`-profile times `Γ`).

The one clause of `UnifIP` that is **not** produced by the pieces above is `coer` — the
level-`4` coercivity of `𝓛_Γ^T = 𝓛̂ + Corr` on `CoerAdm`.  `main_of_coer` below takes that
clause as its hypothesis and returns the headline; the obligation is precisely the statement
proved (or to be proved) by `Work.FTS.CoercivityFix.Assembly.transfer_coer`.  Keeping it as a
hypothesis here is deliberate: the assembly then contains **no** `sorry`, and the remaining
gap is a single, explicitly named `Prop`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.CoercivityFix.Assembly.V_core
import Submission.Work.FTS.CoercivityFix.Assembly.V_bounds
import Submission.Work.FTS.CoercivityFix.Assembly.coerData2_four
import Submission.Work.FTS.CoercivityFix.Assembly.exists_coerAdm_pos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ CoerAdm UnifIP Xn)

set_option autoImplicit false

/-- **The coercivity obligation of `𝓛_Γ^T` at level `4`**, with the coefficients produced by
the corrected induction (`Assembly.coerData2_four`).

This is the exact content of `Assembly.transfer_coer`, stated for the *produced* coefficients
rather than for an arbitrary positive coefficient vector; it is the only input of the headline
that is not a projection of an already-proved piece. -/
def CoerObligation (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) : Prop :=
  ∃ α₂ cc : ℝ, 0 < α₂ ∧ 0 < cc ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 α₂ →
    ∀ f : ℝ → ℝ → ℝ, CoerAdm α f →
      cc * Work.Spaces.HkSq α 4 f
        ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Work.Coercivity.LGammaT α f) f

/-- **The assembly.**  Given the level-`4` coercivity of `𝓛_Γ^T` on `CoerAdm` for the
coefficients of the corrected induction, the headline `UnifIP` statement follows. -/
theorem main_of_coer
    (hcoer : ∀ (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ),
      0 < c₁ → 0 < c₂ → 0 < c₁' → 0 < c₂' → 0 < c₁'' → 0 < c₂'' →
      CoerObligation c₁ c₂ c₁' c₂' c₁'' c₂'') :
    ∃ IP : ℝ → Fn → Fn → ℝ, ∃ α₂ cc clo Cup Ccs : ℝ, UnifIP IP α₂ cc clo Cup Ccs := by
  obtain ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', cc, CC,
    hc₁, hc₂, hc₁', hc₂', hc₁'', hc₂'', hcc, hCC, hdata⟩ := coerData2_four
  obtain ⟨αT, ccT, hαT, hccT, hT⟩ := hcoer c₁ c₂ c₁' c₂' c₁'' c₂''
    hc₁ hc₂ hc₁' hc₂' hc₁'' hc₂''
  obtain ⟨αB, clo, Cup, Cdz, hαB, hclo, hCup, hCdz, hlo, hup, hdz⟩ :=
    V_bounds hc₁ hc₂ hc₁' hc₂' hc₁'' hc₂''
  obtain ⟨hsymm, hadd, hsmul, hcongr, hnonneg⟩ :=
    V_core (le_of_lt hc₁) (le_of_lt hc₂) (le_of_lt hc₁') (le_of_lt hc₂')
      (le_of_lt hc₁'') (le_of_lt hc₂'')
  refine ⟨IP4 c₁ c₂ c₁' c₂' c₁'' c₂'', min (1 / 4) (min αT αB), ccT, clo, Cup,
    max CC Cdz, ?_⟩
  have hα₂ : 0 < min (1 / 4) (min αT αB) :=
    lt_min (by norm_num) (lt_min hαT hαB)
  have hmem₁ : ∀ {α : ℝ}, α ∈ Set.Ioc 0 (min (1 / 4) (min αT αB)) →
      α ∈ Set.Ioc 0 (1 / 4) := fun hα =>
    ⟨hα.1, le_trans hα.2 (min_le_left _ _)⟩
  have hmemT : ∀ {α : ℝ}, α ∈ Set.Ioc 0 (min (1 / 4) (min αT αB)) →
      α ∈ Set.Ioc 0 αT := fun hα =>
    ⟨hα.1, le_trans hα.2 (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have hmemB : ∀ {α : ℝ}, α ∈ Set.Ioc 0 (min (1 / 4) (min αT αB)) →
      α ∈ Set.Ioc 0 αB := fun hα =>
    ⟨hα.1, le_trans hα.2 (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hCCl : CC ≤ max CC Cdz := le_max_left _ _
  have hCdzl : Cdz ≤ max CC Cdz := le_max_right _ _
  refine ⟨⟨hα₂, hccT, hclo, hCup, lt_of_lt_of_le hCC hCCl⟩,
    hsymm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `add_fst`
    intro α hα f₁ f₂ g h₁ h₂ h₃
    exact hadd α hα.1 f₁ f₂ g h₁ h₂ h₃
  · -- `smul_fst`
    intro α hα c f g h₁ h₂
    exact hsmul α hα.1 c f g h₁ h₂
  · -- `congr_qd`
    intro α hα f f' g h₁ h₂ h
    exact hcongr α hα.1 f f' g h₁ h₂ h
  · -- `nonneg`
    intro α hα f hf
    exact hnonneg α hα.1 f hf
  · -- `cs`
    intro α hα f g hf hg
    have h := (hdata α (hmem₁ hα)).cs f g hf hg
    calc |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g|
        ≤ CC * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g := h
      _ ≤ max CC Cdz * Xn α f * Xn α g := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCCl
            (Work.Spaces.HkNorm_nonneg α 4 f)) (Work.Spaces.HkNorm_nonneg α 4 g)
  · -- `lo`
    intro α hα f hf
    exact hlo α (hmemB hα) f hf
  · -- `up`
    intro α hα f hf
    exact hup α (hmemB hα) f hf
  · -- `coer`
    intro α hα f hf
    exact hT α (hmemT hα) f hf
  · -- `Dz_self`
    intro α hα f hf
    have h := hdz α (hmemB hα) f hf
    have hsq : Work.Spaces.HkSq α 4 f = Xn α f ^ 2 := by
      rw [Xn, Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    calc |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Work.Spaces.Dz f) f|
        ≤ Cdz * Work.Spaces.HkSq α 4 f := h
      _ = Cdz * Xn α f ^ 2 := by rw [hsq]
      _ ≤ max CC Cdz * Xn α f ^ 2 :=
          mul_le_mul_of_nonneg_right hCdzl (sq_nonneg _)

/-- **The headline, together with the non-vacuity of its coercivity class.**  The `UnifIP`
statement above is not vacuous: `CoerAdm α` contains an explicit non-zero profile with
`0 < |f|²_{ℋ⁴}` for every `α ∈ (0, 1/4]` (`Assembly.exists_coerAdm_pos`). -/
theorem main_of_coer_nonvacuous
    (hcoer : ∀ (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ),
      0 < c₁ → 0 < c₂ → 0 < c₁' → 0 < c₂' → 0 < c₁'' → 0 < c₂'' →
      CoerObligation c₁ c₂ c₁' c₂' c₁'' c₂'') :
    (∃ IP : ℝ → Fn → Fn → ℝ, ∃ α₂ cc clo Cup Ccs : ℝ, UnifIP IP α₂ cc clo Cup Ccs) ∧
      (∀ α : ℝ, 0 < α → ∃ f : ℝ → ℝ → ℝ,
        CoerAdm α f ∧ 0 < Work.Spaces.HkSq α 4 f) :=
  ⟨main_of_coer hcoer, exists_coerAdm_pos⟩

end Work.FTS.CoercivityFix.Assembly
