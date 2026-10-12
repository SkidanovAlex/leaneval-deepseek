import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/WindowInhabited.lean` — the §6 window is inhabited

`Work.BoseB7A.TildeData.NWindow M Φ` (FS `eq:LocalizedAftercNumber`,
`1_{[0,𝓜]}(n₊)Φ = Φ` in the algebraic form of `BOSE_3Q_LEAD.md` §5) asks for a
decomposition `Φ = Σ_{m ≤ ⌊M⌋} φ_m` into eigenvectors of `T.N` with eigenvalues
the *natural numbers* `m`.

`RB4box` (`Defs.lean`) demands, for every admissible `μ`, the existence of a
**nonzero** window state: FS's `thm:Kafz` infimises over *normalised* `Φ` in the
window, and the assembly (`Assembly.nodeRestrictedB_of_residuals`) needs the
index set of `KzVal`'s infimum to be nonempty (`KzVal_le_of_bound`).

That nonemptiness is **not** a consequence of `KzKernels` (child
`RB4boxCanonHold`, machine-checked: `TildeData.shiftN` preserves every field,
while `TildeData.NWindow_shiftN_eq_zero` empties the window) — it is a property of
FS's honest datum, where `N` *is* the number operator and the Fock vacuum is a
nonzero eigenvector with eigenvalue `0`.

This module isolates it: from the honest, instance-level fact "there is a nonzero
vector killed by `T.N`" (the vacuum; `Work.BoseB4.tildeData` has `N = totNumOp`,
whose kernel is spanned by the Fock vacuum), the window is inhabited for *every*
`𝓜 ≥ 0` — in particular at `𝓜 = E.bigM = K_M(μa³)^{-1/4} ≥ 0`.

The two lemmas here are what an RB4box proof (or the honest instantiation) should
consume instead of re-deriving the window algebra.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : Work.BoseB7.FockData Mode}

set_option linter.unusedVariables false

/-- `0` is always in the window (`thm:Kafz`'s `inf` is over normalised states, so
the zero state has to be excluded by hand — this is the algebraic reason). -/
theorem TildeData.NWindow_zero (T : TildeData F) (M : ℝ) : T.NWindow M 0 :=
  ⟨fun _ => 0, fun m => by simp, by simp⟩

/-- **The window is inhabited, from the vacuum.**  If `T.N` kills a nonzero vector
(FS's Fock vacuum: in `Work.BoseB4.tildeData`, `N = totNumOp` and
`totNumOp Ω = 0`, `Ω ≠ 0`) and `𝓜 ≥ 0`, then there is a nonzero `𝓜`-window state.

This is the nondegeneracy `RB4box` demands of the realisation; it is a property
of the honest datum only (`RB4boxCanonHold`'s child: it fails for the `N`-shifts
of `FINDING_canon_view_uninhabited.md`), so a consumer proves it from the vacuum
fact of the concrete model. -/
theorem TildeData.window_nonempty_of_vac (T : TildeData F) {M : ℝ} (hM : 0 ≤ M)
    (hvac : ∃ f₀ : F.H, f₀ ≠ 0 ∧ T.N f₀ = 0) :
    ∃ f₀ : F.H, T.NWindow M f₀ ∧ f₀ ≠ 0 := by
  obtain ⟨f₀, hne, hkill⟩ := hvac
  refine ⟨f₀, ⟨fun m => if m = 0 then f₀ else 0, ?_, ?_⟩, hne⟩
  · intro m
    by_cases hm : m = 0
    · subst hm; simpa using hkill
    · simp [hm]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro m _ hm; simp [hm]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

end Work.BoseB7A
