/-
Copyright: work module for the Elgindi finite-time singularity project.

# `IPGen/Assembly.lean` — the end product of the `IP`-generation chapter

Collects the chapter's results into the shape the lead's chain consumes (design
`FTS_ELL_GALERKIN.md` §2 and the integration audit `FTS_INTEGRATION_AUDIT.md` §4 item 3): the
coefficients of the corrected coercivity are **not** pinned to `1`, and the concrete
`Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂''` is produced together with the `IPLinHQo` package and the
clauses of the corrected `N4ExtraQ` contract — all for the *same* coefficient tuple.

Everything here is `sorry`-free.  Single import for a consumer:
`Submission.Work.FTS.IPGen.Assembly`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.IPGen.Defs
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.IPGen.IP4Add
import Submission.Work.FTS.IPGen.IP4Smul
import Submission.Work.FTS.IPGen.ip4SlotDomGen
import Submission.Work.FTS.IPGen.slotPairing_abs_le
import Submission.Work.FTS.IPGen.IP4Lin
import Submission.Work.FTS.IPGen.N4ExtraQ
import Submission.Work.FTS.IPGen.headline_IP4_of_errors
import Submission.Work.FTS.IPGen.CoerDataOne
import Submission.Work.FTS.IPGen.N4ExtraQ_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.IPGen

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)

set_option autoImplicit false

/-- **The end product of the `IPGen` chapter.**

From the five obligation families of `CoercivityFix.Transfer.headline_of_errors` (`hE1`,
`hE2`, `CC₁`, `hCD₁`, `hok₁`, `hok₂`, `hok₃`) one gets six positive coefficients
`c₁ … c₂''` such that, for `IP := Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂''`:

1. `UnifIP IP α₂ cc clo Cup Ccs` (the coercivity headline, with the inner product **exposed
   rather than hidden** behind an existential — the design's `headline_IP4`);
2. `IPLinHQo IP α₂ Ct` (additivity/homogeneity on `HQo α 4`, Cauchy–Schwarz against
   `|·|_{ℋ⁴}`, and congruence on the open quadrant);
3. the four clause families of the corrected contract `N4ExtraQ` which this chapter owns:
   `cs` on `HQo α 4 × HQo α 4`, `add` on `HQo α 4`, the frozen `VocabO.T2Clause` and
   `VocabO.T3Clause`.

The `smul`, `neg` and `congr` clauses hold with no restriction on `α` and are available as
`ip4_smul`, `ip4_neg`, `ip4_congr_Qd`; the remaining `N4ExtraQ` fields (`dz`, `t1`, `t4`,
`st`) are other subprojects' obligations. -/
theorem IP4_package_of_errors
    (hE1 : ∃ κ₁ : ℝ, 0 ≤ κ₁ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 →
      ∀ f : Fn, Work.FTS.Nonlin.CoerAdm α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
          ≤ α * κ₁ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hE2 : ∃ κ₂ : ℝ, 0 ≤ κ₂ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 →
      ∀ f : Fn, Work.FTS.Nonlin.CoerAdm α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
          ≤ κ₂ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (CC₁ : ℝ) (hCC₁ : 0 < CC₁)
    (hCD₁ : ∀ α : ℝ, α ∈ Set.Ioc 0 (1 / 10 ^ 14) →
      Work.FTS.CoercivityFix.Assembly.CoerData2 α 1 (Work.Coercivity.H1IP α) 2 CC₁)
    (hok₁ : ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.FTS.CoercivityFix.Transfer.LevelPkg α 1 (Work.Coercivity.H1IP α) CC₁)
    (hok₂ : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ c₂ : ℝ, 0 < c₂ →
      Work.FTS.CoercivityFix.Transfer.LevelPkg α 2
        (Work.FTS.CoercivityFix.Assembly.IP2 1 c₂ α) (3 * max 1 (max 1 c₂) * CC₁))
    (hok₃ : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ c₂ c₂' : ℝ, 0 < c₂ → 0 < c₂' →
      Work.FTS.CoercivityFix.Transfer.LevelPkg α 3
        (Work.FTS.CoercivityFix.Assembly.IP3 1 c₂ 1 c₂' α)
        (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁))) :
    ∃ c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ,
      0 < c₁ ∧ 0 < c₂ ∧ 0 < c₁' ∧ 0 < c₂' ∧ 0 < c₁'' ∧ 0 < c₂'' ∧
      (∃ α₂ cc clo Cup Ccs : ℝ,
        Work.FTS.Nonlin.UnifIP
          (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ cc clo Cup Ccs) ∧
      (∃ α₂ Ct : ℝ, 0 < α₂ ∧ 0 < Ct ∧
        IPLinHQo (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ Ct) ∧
      ((∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
          Work.FTS.VocabO.HQo α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
          |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g|
            ≤ Ct * Xn α f * Xn α g)
        ∧ (∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn,
            Work.FTS.VocabO.HQo α 4 f₁ → Work.FTS.VocabO.HQo α 4 f₂ →
            Work.FTS.Nonlin.RegQ α 4 g →
            Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (f₁ + f₂) g
              = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₁ g
                + Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₂ g)
        ∧ (∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
            Work.FTS.VocabO.T2Clause
              (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ Ct)
        ∧ (∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
            Work.FTS.VocabO.T3Clause
              (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ Ct)) := by
  obtain ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', hc₁, hc₂, hc₁', hc₂', hc₁'', hc₂'', hUnif⟩ :=
    headline_IP4_of_errors hE1 hE2 CC₁ hCC₁ hCD₁ hok₁ hok₂ hok₃
  exact ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', hc₁, hc₂, hc₁', hc₂', hc₁'', hc₂'', hUnif,
    ip4_IPLinHQo (le_of_lt hc₁) (le_of_lt hc₂) (le_of_lt hc₁') (le_of_lt hc₂')
      (le_of_lt hc₁'') (le_of_lt hc₂''),
    ip4_N4ExtraQ_clauses (le_of_lt hc₁) (le_of_lt hc₂) (le_of_lt hc₁') (le_of_lt hc₂')
      (le_of_lt hc₁'') (le_of_lt hc₂'')⟩

/-- **The `IP`-generation headline with the Cauchy–Schwarz obligation discharged.**

Same conclusion as `headline_IP4_of_errors` (the coercivity `UnifIP` for an explicit
`Assembly.IP4 c₁ … c₂''`), but the obligation family `hCD₁` of
`CoercivityFix.Transfer.headline_of_errors` is *proved*, in this chapter, as
`IPGen.coerData2_one_H1IP` (with `CC₁ = 10^22`, from `H1IP_cs_Q` and `coer1_Lhat`).  The
remaining hypotheses are the four defect obligations `hE1`, `hE2`, `hok₁`, `hok₂`, `hok₃`, which
involve the transfer defects `E1`, `E2` (the `CoercivityFix` layer). -/
theorem headline_IP4_min
    (hE1 : ∃ κ₁ : ℝ, 0 ≤ κ₁ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 →
      ∀ f : Fn, Work.FTS.Nonlin.CoerAdm α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
          ≤ α * κ₁ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hE2 : ∃ κ₂ : ℝ, 0 ≤ κ₂ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 →
      ∀ f : Fn, Work.FTS.Nonlin.CoerAdm α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
          ≤ κ₂ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hok₁ : ∀ (CC₁ : ℝ), 0 < CC₁ → ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.FTS.CoercivityFix.Transfer.LevelPkg α 1 (Work.Coercivity.H1IP α) CC₁)
    (hok₂ : ∀ (CC₁ : ℝ), 0 < CC₁ → ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ c₂ : ℝ, 0 < c₂ →
      Work.FTS.CoercivityFix.Transfer.LevelPkg α 2
        (Work.FTS.CoercivityFix.Assembly.IP2 1 c₂ α) (3 * max 1 (max 1 c₂) * CC₁))
    (hok₃ : ∀ (CC₁ : ℝ), 0 < CC₁ → ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ c₂ c₂' : ℝ,
      0 < c₂ → 0 < c₂' →
      Work.FTS.CoercivityFix.Transfer.LevelPkg α 3
        (Work.FTS.CoercivityFix.Assembly.IP3 1 c₂ 1 c₂' α)
        (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁))) :
    ∃ c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ,
      0 < c₁ ∧ 0 < c₂ ∧ 0 < c₁' ∧ 0 < c₂' ∧ 0 < c₁'' ∧ 0 < c₂'' ∧
      ∃ α₂ cc clo Cup Ccs : ℝ,
        Work.FTS.Nonlin.UnifIP
          (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ cc clo Cup Ccs := by
  obtain ⟨CC₁, hCC₁, hCD₁⟩ := coerData2_one_H1IP
  exact headline_IP4_of_errors hE1 hE2 CC₁ hCC₁ hCD₁ (hok₁ CC₁ hCC₁) (hok₂ CC₁ hCC₁)
    (hok₃ CC₁ hCC₁)

set_option linter.defProp false

/-- **The design's name `headline_IP4`** for `headline_IP4_of_errors`.

It is *conditional*, on exactly the five obligation families of
`CoercivityFix.Transfer.headline_of_errors`.  The hypothesis-free `headline_IP4` of
`FTS_ELL_GALERKIN_STMTS.lean.txt` is this statement with `hE1`, `hE2`, `hok₁`, `hok₂`, `hok₃`
discharged, which is the `CoercivityFix` layer's remaining work (one of the five, `hCD₁`, *is*
discharged here — see `IPGen.coerData2_one_H1IP` and `headline_IP4_min`). -/
def headline_IP4 := @headline_IP4_of_errors

end Work.FTS.IPGen
