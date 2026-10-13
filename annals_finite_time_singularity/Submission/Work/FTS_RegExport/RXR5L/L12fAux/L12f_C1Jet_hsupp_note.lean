/-
# `L12f_C1Jet_hsupp_note` — the `hsupp` hypothesis of the assigned `L12f_C1Jet` is unsatisfiable

The assigned lemma `Work.FTS_RegExport.RXR5L.L12f_C1Jet` carries the hypothesis

```
hsupp : ∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, Lf ≤ z →
      Work.FTS.Regularity.profFull (Work.FTS.Regularity.pExp α)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) z θ τ = 0
```

**This hypothesis has no model.**  The two facts that collide are definitional:

* `profFull β G z θ τ = Fstar (pExp β) z θ + G z θ τ` (`Regularity.profFull_apply`), so with
  `β := pExp α` the profile is `Fstar (pExp (pExp α)) = Fstar (9α)` plus the family;
* the sanitiser `FinalV2.gS α h` is, *by definition*, `-Fstar (pExp α) = -Fstar (3α)` for
  `z > 0` and `θ ∉ Iθ` (its else-branch), independently of `h`.

Consequently, for `z ≥ Lf > 0`, `τ ∈ [0,S]` and every `θ ∉ Iθ` the hypothesis forces the
identity `Fstar (9α) z θ = Fstar (3α) z θ` — this is the machine-checked lemma
`profFull_pExp_forces_Fstar_eq` below.

That identity is false for every `α > 0`: writing `Fstar β z θ = β·(Γ_β(θ)/c β)·F̂(z)` with
`Γ_β(θ) = (sinθ·cos²θ)^{β/3}` and `F̂(z) = 2z/(1+z)² > 0` (`z > 0`), it is equivalent to

    `3·u(θ)^{2α}·c(3α) = c(9α)`     for every `u(θ) = sinθ·cos²θ`, `θ ∈ (π/2, π)`.

The left side is a strictly monotone function of `u` (as `α > 0`), while the set of values
`u(θ)`, `θ ∈ (π/2,π)`, is an interval with more than one point (e.g. `u(3π/4) = √2/4` and
`u(2π/3) = √3/8`), and `c(3α), c(9α) > 0`.  So the hypothesis is unsatisfiable; the statement
`L12f_C1Jet` is *vacuous* and does not express the intended claim.

**The intended hypothesis** is `profFull α (gS α (tauExt g)) z θ τ = 0` (equivalently
`Fstar (pExp α) z θ + g̃ = 0`, i.e. `Work.Construction.Ftau (pExp α) (gS α (tauExt g)) τ = 0`),
which is the shape used everywhere else in the tree
(`FTS/RegPkgGal/Defs.lean`'s `RegPkg.hsupp`, `FTS_RegExport/Supp.lean`'s `suppExport_proved`,
`FTS/FinalV2/Sanitize.lean`'s `hsuppOut_gS`): with it, the off-`Iθ` branch of `gS` matches the
`Fstar (pExp α)` of the profile *automatically*, and the support hypothesis becomes the genuine
compactness of the full profile.  **That statement is proved**: see
`Submission/Work/FTS_RegExport/RXR5L/L12fAux/L12f_C1Jet_profFull.lean`, declaration
`Work.FTS_RegExport.RXR5L.L12fAux.L12f_C1Jet_profFull` (sorry-free, axioms
`[propext, Classical.choice, Quot.sound]`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS.FinalV2.Sanitize

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXR5L.L12fAux

set_option autoImplicit false

/-- **The `pExp α`-support hypothesis forces `Fstar (9α) = Fstar (3α)` off the angular
interval.**  This is the exact sense in which the hypothesis of the assigned `L12f_C1Jet` is
unsatisfiable: its off-`Iθ` content is an identity between two *different* static profiles. -/
theorem profFull_pExp_forces_Fstar_eq {α S Lf τ z θ : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hLf : 0 < Lf)
    (hvan : ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, Lf ≤ z →
      Work.FTS.Regularity.profFull (Work.FTS.Regularity.pExp α)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) z θ τ = 0)
    (hτ : τ ∈ Set.Icc (0:ℝ) S) (hz : Lf ≤ z) (hθ : θ ∉ Work.Spaces.Iθ) :
    Work.Construction.Fstar (Work.FTS.Regularity.pExp (Work.FTS.Regularity.pExp α)) z θ
      = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ := by
  have h := hvan τ hτ z θ hz
  rw [Work.FTS.Regularity.profFull_apply, Work.FTS.Regularity.pExp_eq] at h
  have hz' : 0 < z := lt_of_lt_of_le hLf hz
  have hgS : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ τ
      = - Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ := by
    simp only [Work.FTS.FinalV2.gS, hz', ↓reduceIte]
    refine if_neg ?_
    simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
  rw [hgS] at h
  have h2 : Work.Construction.Fstar (3 * Work.FTS.Regularity.pExp α) z θ
      = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ := by linarith
  simpa only [Work.FTS.Regularity.pExp_eq] using h2

end Work.FTS_RegExport.RXR5L.L12fAux
