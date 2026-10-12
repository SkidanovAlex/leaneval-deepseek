import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.exists_honestModes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseWireFix/exists_honestModes_family` — an honest mode family meeting a
prescribed cube-size requirement at **every** chemical potential

Audit item 3 of `Submission/Work/BOSE_INTEGRATION_AUDIT.md` §4.  The pointwise BF1 theorem
`Work.BoseBoxFock.exists_honestModes v μ N` produces, for each *single* `(μ, N)`,
`HM : Work.BoseBoxFock.HonestModes v μ` with `HM.N = N`.  Every consumer of the honest family,
however, is a *function* `HM : ∀ μ, HonestModes v μ` (see `Work.BoseBoxFock.HonestBoxFam`,
`Work.BoseBoxFock.viewFS_of_gate`, `Work.BoseRowsFS.exists_honestGateFS_of_honestInterface`),
and the cube sizes it has to satisfy are themselves functions of `μ` — FS's `N_uv` (the `Ŵ₁`
cut-off pin, `4K_L√(μa) ≤ uvRad ℓ N`), the gate's `N_g`, and `N_min`.  The audit's missing link
(b) is exactly "the choice of an `HM` with `N ≥ max(N_min, N_g, N_uv)`", and a *choice* has to
be made *uniformly in `μ`*: `Classical.choose` on `fun μ => exists_honestModes v μ (Nreq μ)`.

This module does that once and for all:

* `Work.BoseWireFix.exists_honestModes_family v Nreq` —
  `∃ HM : ∀ μ, HonestModes v μ, ∀ μ, Nreq μ ≤ (HM μ).N`;
* `…_spec` — the same with the equality `(HM μ).N = Nreq μ` (so the caller can `rw` the size);
* `…_max` — the three-requirement form matching the audit's phrase, useful because the ledger
  requires all three rows at once.

A caller therefore never has to redo the choice: it writes down the *requirement function*
`Nreq : ℝ → ℕ` (for instance `fun μ => max (Nmin μ) (max (Ng μ) (Nuv μ))`) and obtains one
family `HM` that satisfies it at every `μ`.

## Conventions

* `HonestModes v μ` is `Work.BoseBoxFock.HonestModes` (`Submission/Work/BoseBoxFock/Defs.lean`),
  its `N` field being the cube label count `Lab N = (ZMod (2N+1))³`.
* nothing here is new mathematics: it is the `Classical.choose` distribution of
  `Work.BoseBoxFock.exists_honestModes` over `μ`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseWireFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The family -/

/-- **An honest mode family meeting a prescribed cube-size requirement at every `μ`.**  For any
`Nreq : ℝ → ℕ` there is one family `HM`, simultaneously defined at every chemical potential,
whose cube size dominates `Nreq μ`.

This is the audit's item 3: it turns the pointwise BF1 theorem
`Work.BoseBoxFock.exists_honestModes` into the *choice* of `HM` that the gate (`hN`, the `Ŵ₁`
cut-off row of `viewFS_of_gate`), the row-3 window and the §7–11 assembly all require. -/
theorem exists_honestModes_family (v : ℝ³ → ℝ) (Nreq : ℝ → ℕ) :
    ∃ HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ, ∀ μ : ℝ, Nreq μ ≤ (HM μ).N := by
  have h := fun μ : ℝ => Work.BoseBoxFock.exists_honestModes v μ (Nreq μ)
  choose HM hN using h
  exact ⟨HM, fun μ => by rw [hN μ]⟩

/-- The same family, with the cube size *pinned* to the requirement: `(HM μ).N = Nreq μ` for
every `μ`.  Callers who want to `rw` the cube size (e.g. citizens of the `Lab N` bookkeeping)
should use this form. -/
theorem exists_honestModes_family_spec (v : ℝ³ → ℝ) (Nreq : ℝ → ℕ) :
    ∃ HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ, ∀ μ : ℝ, (HM μ).N = Nreq μ := by
  choose HM hN using fun μ : ℝ => Work.BoseBoxFock.exists_honestModes v μ (Nreq μ)
  exact ⟨HM, hN⟩

/-! ## 2. The three-requirement form (the audit's `max(Nmin, Ng, Nuv)`) -/

/-- **The audit's phrase made precise**: for three requirement functions `N₁ N₂ N₃ : ℝ → ℕ`
(the minimum size `N_min`, the gate's `N_g`, and the UV window `N_uv`) there is one honest mode
family whose cube size dominates all three at every `μ`.

Immediate from `exists_honestModes_family` at `Nreq μ = max (N₁ μ) (max (N₂ μ) (N₃ μ))`, since
each of the three is `≤ max (N₁ μ) (max (N₂ μ) (N₃ μ))` (`le_max_left`,
`le_trans (le_max_left _ _) (le_max_right _ _)`, `le_trans (le_max_right _ _) (le_max_right _ _)`). -/
theorem exists_honestModes_family_max (v : ℝ³ → ℝ) (N₁ N₂ N₃ : ℝ → ℕ) :
    ∃ HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ,
      (∀ μ : ℝ, N₁ μ ≤ (HM μ).N) ∧ (∀ μ : ℝ, N₂ μ ≤ (HM μ).N) ∧
        (∀ μ : ℝ, N₃ μ ≤ (HM μ).N) := by
  obtain ⟨HM, hN⟩ := exists_honestModes_family_spec v
    (fun μ => max (N₁ μ) (max (N₂ μ) (N₃ μ)))
  refine ⟨HM, fun μ => ?_, fun μ => ?_, fun μ => ?_⟩
  · exact le_trans (le_max_left _ _) (le_of_eq (hN μ).symm)
  · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_of_eq (hN μ).symm)
  · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_of_eq (hN μ).symm)

/-- **The same family pinned to the maximum**: the three-requirement family with the cube size
*equal* to `max (N₁ μ) (max (N₂ μ) (N₃ μ))`. -/
theorem exists_honestModes_family_max_spec (v : ℝ³ → ℝ) (N₁ N₂ N₃ : ℝ → ℕ) :
    ∃ HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ,
      ∀ μ : ℝ, (HM μ).N = max (N₁ μ) (max (N₂ μ) (N₃ μ)) :=
  exists_honestModes_family_spec v (fun μ => max (N₁ μ) (max (N₂ μ) (N₃ μ)))

end Work.BoseWireFix
