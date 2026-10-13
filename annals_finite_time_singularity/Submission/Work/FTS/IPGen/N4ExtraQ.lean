/-
Copyright: work module for the Elgindi finite-time singularity project.

# `IPGen/N4ExtraQ.lean` — the corrected `IP`-level contract for the coercive `IP4`

`Work.FTS.OpenPkg.N4Extra' IP α₂ Ct` is the primed contract consumed by the rows.  The design
(`FTS_ELL_GALERKIN.md`, "New defects") shows that its clauses `cs`, `add`, `smul`, `neg`,
`congr` are **junk traps** in the form stated there: they hypothesise only
`HkMem α 4` (integrability of the `ℋ⁴`-integrand), which carries no smoothness, while `IP4` is
built out of the derivatives `D_z^bD_θ^a f`.  Take `f₁ = h` nowhere differentiable and
`f₂ = s − h` smooth: then `HkMem α 4 f₁` and `HkMem α 4 f₂` hold, but the derivative slots of
`f₁` are Lean's junk value, so `IP4 (f₁ + f₂) g ≠ IP4 f₁ g + IP4 f₂ g`.

`IPGen.N4ExtraQ` (`IPGen/Defs.lean`) is the repair: the class `HQo α 4 = SmoothOpen ∧ HkMem α 4`
interior `C^∞` plus honesty) replaces `HkMem α 4` in exactly those five clauses.

This file proves, for the concrete `Assembly.IP4 c₁ … c₂''` with *free* (nonnegative)
coefficients, the clauses of that contract which this subproject owns:

| clause | proved as |
|---|---|
| `cs` | `IPGen.ip4_cs_HQo` (`IPGen/IP4Lin.lean`) |
| `add` | `IPGen.ip4_add_HQo` (`IPGen/IP4Add.lean`) |
| `smul` | `IPGen.ip4_smul` (`IPGen/IP4Smul.lean`, unconditional) |
| `neg` | `IPGen.ip4_neg` (`IPGen/IP4Smul.lean`, unconditional) |
| `congr` | `IPGen.ip4_congr_Qd` (`IPGen/IP4Add.lean`, no membership at all) |
| `t2` | `ip4_T2Clause` below, from `TransportS.t2SlotGuarded` |
| `t3` | `ip4_T3Clause` below, from `TransportS.t3SlotGuarded` |

The remaining clauses (`dz`, `t1`, `t4`, `st`) belong to the row-side subprojects; they are
**not** touched here.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.IPGen.Defs
import Submission.Work.FTS.IPGen.IP4Lin
import Submission.Work.FTS.TransportS.ClauseBridge
import Submission.Work.FTS.TransportS.t2SlotGuarded
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.OpenPkg.Basic

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

/-! ## The two transport clauses for the general-coefficient `IP4` -/

/-- **The `t2` clause (`VocabO.T2Clause`) for the coercive `IP4` with free nonnegative
coefficients.**  `TransportS.T2Clause_of_slot` sums the per-slot transport bound
`TransportS.t2SlotGuarded` over the `75` leaves of the unfolding, whose domination
`SlotDomIP` is `IPGen.ip4SlotDomGen`. -/
theorem ip4_T2Clause {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂)
    (h₁' : 0 ≤ c₁') (h₂' : 0 ≤ c₂') (h₁'' : 0 ≤ c₁'') (h₂'' : 0 ≤ c₂'') :
    ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
      Work.FTS.VocabO.T2Clause
        (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ Ct := by
  obtain ⟨C, hC, hS⟩ := Work.FTS.TransportS.t2SlotGuarded
  have hD := ip4SlotDomGen (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
    (c₁'' := c₁'') (c₂'' := c₂'') h₁ h₂ h₁' h₂' h₁'' h₂''
  set K : ℝ := max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))) ^ 3 * 3 ^ 3 * 10 ^ 22
    with hKdef
  have hKpos : 0 < K := hD.1
  exact ⟨K * 75 * C, 1, mul_pos (mul_pos hKpos (by norm_num)) hC, one_pos,
    Work.FTS.TransportS.T2Clause_of_slot hC.le (le_refl 1) hS hD⟩

/-- **The `t3` clause (`VocabO.T3Clause`) for the coercive `IP4` with free nonnegative
coefficients**, from `TransportS.t3SlotGuarded` and `IPGen.ip4SlotDomGen`. -/
theorem ip4_T3Clause {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂)
    (h₁' : 0 ≤ c₁') (h₂' : 0 ≤ c₂') (h₁'' : 0 ≤ c₁'') (h₂'' : 0 ≤ c₂'') :
    ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
      Work.FTS.VocabO.T3Clause
        (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ Ct := by
  obtain ⟨C, hC, hS⟩ := Work.FTS.TransportS.t3SlotGuarded
  have hD := ip4SlotDomGen (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
    (c₁'' := c₁'') (c₂'' := c₂'') h₁ h₂ h₁' h₂' h₁'' h₂''
  set K : ℝ := max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))) ^ 3 * 3 ^ 3 * 10 ^ 22
    with hKdef
  have hKpos : 0 < K := hD.1
  exact ⟨K * 75 * C, 1, mul_pos (mul_pos hKpos (by norm_num)) hC, one_pos,
    Work.FTS.TransportS.T3Clause_of_slot hC.le (le_refl 1) hS hD⟩

/-! ## The clause package -/

/-- **Cauchy–Schwarz for `IP4` with a `RegQ` second argument** (the shape of
`OpenPkg.N4Extra'.cs`): immediate from `ip4_cs_HQo` and `OpenPkg.HQo_of_RegQ`. -/
theorem ip4_cs_RegQ {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂)
    (h₁' : 0 ≤ c₁') (h₂' : 0 ≤ c₂') (h₁'' : 0 ≤ c₁'') (h₂'' : 0 ≤ c₂'') :
    ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
      Work.FTS.VocabO.HQo α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
      |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g|
        ≤ Ct * Xn α f * Xn α g := by
  obtain ⟨Ct, α₂, hCt, hα₂, h⟩ := ip4_cs_HQo h₁ h₂ h₁' h₂' h₁'' h₂''
  exact ⟨Ct, α₂, hCt, hα₂, fun α hα f g hf hg =>
    h α hα f g hf (Work.FTS.OpenPkg.HQo_of_RegQ hg)⟩

/-- **Additivity of `IP4` with a `RegQ` second argument** (the shape of
`OpenPkg.N4Extra'.add`): immediate from `ip4_add_HQo` and `OpenPkg.HQo_of_RegQ`. -/
theorem ip4_add_RegQ {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} :
    ∃ α₂ : ℝ, 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn,
      Work.FTS.VocabO.HQo α 4 f₁ → Work.FTS.VocabO.HQo α 4 f₂ →
      Work.FTS.Nonlin.RegQ α 4 g →
      Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (f₁ + f₂) g
        = Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₁ g
          + Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₂ g := by
  obtain ⟨α₂, hα₂, h⟩ := ip4_add_HQo (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
    (c₁'' := c₁'') (c₂'' := c₂'')
  exact ⟨α₂, hα₂, fun α hα f₁ f₂ g h₁ h₂ h₃ =>
    h α hα f₁ f₂ g h₁ h₂ (Work.FTS.OpenPkg.HQo_of_RegQ h₃)⟩

/-- **The clauses of the corrected contract `N4ExtraQ` for the general-coefficient coercive
`IP4`** — the `IP`-side content this subproject owns, bundled.  The two repaired clauses that
carry a constant (`cs`, `add`) are stated with a `HQo α 4` first argument and the frozen
`RegQ α 4` second argument (the shape of `N4Extra'.cs`/`N4Extra'.add`), and the two transport
clauses are the frozen `VocabO.T2Clause`/`T3Clause`.

The remaining repaired clauses hold **unconditionally** and are available separately:
`ip4_smul`, `ip4_neg` (any `α`, no hypothesis) and `ip4_congr_Qd` (no membership at all).

This is the statement the lead's assembly consumes in place of
`Work.FTS.OpenPkg.N4Extra'`: combine it with the remaining clauses (`dz`, `t1`, `t4`, `st`) to
build `IPGen.N4ExtraQ (Assembly.IP4 c₁ … c₂'') α₂ Ct`. -/
theorem ip4_N4ExtraQ_clauses {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂)
    (h₁' : 0 ≤ c₁') (h₂' : 0 ≤ c₂') (h₁'' : 0 ≤ c₁'') (h₂'' : 0 ≤ c₂'') :
    (∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
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
            (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ Ct) :=
  ⟨ip4_cs_RegQ h₁ h₂ h₁' h₂' h₁'' h₂'',
    ip4_add_RegQ (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂') (c₁'' := c₁'')
      (c₂'' := c₂''),
    ip4_T2Clause h₁ h₂ h₁' h₂' h₁'' h₂'', ip4_T3Clause h₁ h₂ h₁' h₂' h₁'' h₂''⟩

end Work.FTS.IPGen
