/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsE4Thr/TransO/CoerTransferO.lean` — the `coer` clause of `UnifIPO (IP4 …)`

This is the end of the open-class transfer chapter: it discharges the four inputs of
`TransO.stepPair_O`-based `TransO.transfer_level4_O`

* the level-`1` clean data `hCD₁` (`CoerData2O α 1 (H1IP α) 2 CC₁`) — from the proved
  `Coer1LhatO.coerData2_one_H1IP_O`;
* the three level packages `hok₁/₂/₃ : LevelPkgO …` — from `TransO.levelPkg_of_O` with the
  algebraic inputs `CommSm_L1` / `CommSm_succ` and the Cauchy–Schwarz inputs `CSQ_one_unif` /
  `CSQ_succ` (the constant `CC₁ = max CC_Q CC_M` is chosen exactly as in
  `Transfer/Instantiate.ok_data`),

so that `transfer_level4_O` produces

  `∃ c…, ∃ α₂ cc, ∀ α ∈ Ioc 0 α₂, ∀ f, CoerAdmO α f → cc·|f|²_{ℋ⁴} ≤ IP4 c… α (𝓛_Γ^T f) f`

— **the `coer` clause**, and then `UnifIPO (IP4 …)` via the (already proved)
`unifIPO_IP4_of_coer_only`, which supplies `lo`, `up`, `Dz_self`, the algebraic clauses and
Cauchy–Schwarz on the open class.

This is the open-class replacement of `Transfer/Instantiate.headline_from_norms`: no
`SmoothQuad` occurs anywhere, so the level-four small-ball half of `AprioriP` can be run at the
projected mollified slices `Pz (J_ε (slice g τ))` of the route.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.L4MainO
import Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.LevelPkgInstO
import Submission.Work.FTS.StrongEps.EpsE4Thr.Coer1LhatO
import Submission.Work.FTS.StrongEps.EpsE4Thr.E1_norm_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.UnifIPOOfCoerFinal
import Submission.Work.FTS.CoercivityFix.Transfer.CommSm_L1
import Submission.Work.FTS.CoercivityFix.Transfer.CommSm_succ
import Submission.Work.FTS.CoercivityFix.Transfer.CSQ_one_unif
import Submission.Work.FTS.CoercivityFix.Transfer.CSQ_succ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)
open Work.FTS.CoercivityFix.Transfer
open Work.FTS.StrongEps.EpsE4Thr (CoerAdmO CoerData2O RegQo)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "IP2" => Work.FTS.CoercivityFix.Assembly.IP2
local notation "IP3" => Work.FTS.CoercivityFix.Assembly.IP3
local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-- **The four inputs `hCD₁`, `hok₁`, `hok₂`, `hok₃` of `transfer_level4_O`, together with their
uniform constants** — the open-class twin of `Transfer/Instantiate.ok_data`. -/
theorem ok_data_O :
    ∃ CC₁ : ℝ, 0 < CC₁ ∧
      (∀ α : ℝ, α ∈ Set.Ioc 0 (1 / 10 ^ 14) →
        CoerData2O α 1 (Work.Coercivity.H1IP α) 2 CC₁) ∧
      (∀ α : ℝ, 0 < α → α ≤ 1 →
        LevelPkgO α 1 (Work.Coercivity.H1IP α) CC₁) ∧
      (∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ c₂ : ℝ, 0 < c₂ →
        LevelPkgO α 2 (IP2 1 c₂ α) (3 * max 1 (max 1 c₂) * CC₁)) ∧
      (∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ c₂ c₂' : ℝ, 0 < c₂ → 0 < c₂' →
        LevelPkgO α 3 (IP3 1 c₂ 1 c₂' α)
          (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁))) := by
  obtain ⟨CC_Q, hCC_Q, hQ⟩ := Work.FTS.StrongEps.EpsE4Thr.coerData2_one_H1IP_O
  obtain ⟨CC_M, hCC_M, hM⟩ := Work.FTS.CoercivityFix.Transfer.CSQ_one_unif
  set CC₁ : ℝ := max CC_Q CC_M with hCC₁def
  have hCC₁ : 0 < CC₁ := lt_of_lt_of_le hCC_Q (le_max_left _ _)
  have hCC₁0 : 0 ≤ CC₁ := le_of_lt hCC₁
  have hleQ : CC_Q ≤ CC₁ := le_max_left _ _
  have hleM : CC_M ≤ CC₁ := le_max_right _ _
  have hCSQ₁ : ∀ α : ℝ, 0 < α → CSQ α 1 (Work.Coercivity.H1IP α) CC₁ := by
    intro α hα X Y hX hY hmX hmY
    refine le_trans (hM α hα X Y hX hY hmX hmY) ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hleM (Work.Spaces.HkNorm_nonneg α 1 X))
      (Work.Spaces.HkNorm_nonneg α 1 Y)
  refine ⟨CC₁, hCC₁, ?_, ?_, ?_, ?_⟩
  · -- `hCD₁`
    intro α hα
    obtain ⟨hcc, hCC, hcs, hcoer⟩ := hQ α ⟨hα.1, by linarith [hα.2]⟩
    exact ⟨hcc, hCC₁,
      fun f g hf hg => le_trans (hcs f g hf hg)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hleQ (Work.Spaces.HkNorm_nonneg α 1 f))
          (Work.Spaces.HkNorm_nonneg α 1 g)),
      hcoer⟩
  · -- `hok₁`
    intro α hα hα1
    exact levelPkg_of_O α hα hα1 1 (by norm_num)
      (Work.FTS.CoercivityFix.Transfer.CommSm_L1 α hα) (hCSQ₁ α hα)
  · -- `hok₂`
    intro α hα hα1 c₂ hc₂
    have hstep : CSQ α 2 (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP α))
        (3 * max 1 (max 1 c₂) * CC₁) :=
      Work.FTS.CoercivityFix.Transfer.CSQ_succ α hα 1 hCC₁0 (by norm_num) (le_of_lt hc₂)
        (hCSQ₁ α hα)
    exact levelPkg_of_O α hα hα1 2 (by norm_num)
      (Work.FTS.CoercivityFix.Transfer.CommSm_succ α hα 1
        (Work.FTS.CoercivityFix.Transfer.CommSm_L1 α hα)) hstep
  · -- `hok₃`
    intro α hα hα1 c₂ c₂' hc₂ hc₂'
    have h2 : CSQ α 2 (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP α))
        (3 * max 1 (max 1 c₂) * CC₁) :=
      Work.FTS.CoercivityFix.Transfer.CSQ_succ α hα 1 hCC₁0 (by norm_num) (le_of_lt hc₂)
        (hCSQ₁ α hα)
    have h3 : CSQ α 3
        (Work.Coercivity.HkIPStep 1 c₂'
          (Work.Coercivity.HkIPStep 1 c₂ (Work.Coercivity.H1IP α)))
        (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁)) :=
      Work.FTS.CoercivityFix.Transfer.CSQ_succ α hα 2 (by positivity) (by norm_num)
        (le_of_lt hc₂') h2
    exact levelPkg_of_O α hα hα1 3 (by norm_num)
      (Work.FTS.CoercivityFix.Transfer.CommSm_succ α hα 2
        (Work.FTS.CoercivityFix.Transfer.CommSm_succ α hα 1
          (Work.FTS.CoercivityFix.Transfer.CommSm_L1 α hα))) h3

/-- **The `coer` clause on the open class**: the coercivity of `𝓛_Γ^T` in the level-four pairing
`IP4`, for `α` in some `(0, α₂]`. -/
theorem coer_transfer_O :
    ∃ (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ),
      0 < c₁ ∧ 0 < c₂ ∧ 0 < c₁' ∧ 0 < c₂' ∧ 0 < c₁'' ∧ 0 < c₂'' ∧
      ∃ (α₂ cc : ℝ), 0 < α₂ ∧ 0 < cc ∧
        ∀ α : ℝ, α ∈ Set.Ioc 0 α₂ → ∀ f : Fn, CoerAdmO α f →
          cc * Work.Spaces.HkSq α 4 f
            ≤ IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (Work.Coercivity.LGammaT α f) f := by
  obtain ⟨CC₁, hCC₁, hCD₁, hok₁, hok₂, hok₃⟩ := ok_data_O
  obtain ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', hc₁, hc₂, hc₁', hc₂', hc₁'', hc₂'',
    αT, ccT, _CCT, hαT, hccT, _hCCT, hdat⟩ :=
    transfer_level4_O Work.FTS.StrongEps.EpsE4Thr.E1_norm_O
      Work.FTS.StrongEps.EpsE4Thr.E2_norm_O CC₁ hCC₁ hCD₁ hok₁ hok₂ hok₃
  exact ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', hc₁, hc₂, hc₁', hc₂', hc₁'', hc₂'',
    αT, ccT, hαT, hccT, fun α hα f hf => (hdat α hα).coer f hf⟩

/-- **`UnifIPO (IP4 …)` on the open class, unconditionally.**  The `coer` clause is
`coer_transfer_O`; `lo`, `up`, `Dz_self`, the algebraic clauses and Cauchy–Schwarz come from
`UnifIPOOfCoerFinal.unifIPO_IP4_of_coer_only`. -/
theorem unifIPO_IP4_of_transfer :
    ∃ (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ),
      0 < c₁ ∧ 0 < c₂ ∧ 0 < c₁' ∧ 0 < c₂' ∧ 0 < c₁'' ∧ 0 < c₂'' ∧
      ∃ (α₂ cc clo Cup Ccs : ℝ), 0 < α₂ ∧ 0 < cc ∧ 0 < clo ∧ 0 < Cup ∧ 0 < Ccs ∧
        UnifIPO (IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ cc clo Cup Ccs := by
  obtain ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', hc₁, hc₂, hc₁', hc₂', hc₁'', hc₂'',
    α₂, cc, hα₂, hcc, hcoer⟩ := coer_transfer_O
  obtain ⟨clo, Cup, Ccs, hclo, hCup, hCcs, hU⟩ :=
    Work.FTS.StrongEps.EpsE4Thr.unifIPO_IP4_of_coer_only hc₁ hc₂ hc₁' hc₂' hc₁'' hc₂''
      hα₂ hcc hcoer
  exact ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', hc₁, hc₂, hc₁', hc₂', hc₁'', hc₂'',
    min α₂ 1, cc, clo, Cup, Ccs, lt_min hα₂ one_pos, hcc, hclo, hCup, hCcs, hU⟩

end Work.FTS.StrongEps.EpsE4Thr.TransO
