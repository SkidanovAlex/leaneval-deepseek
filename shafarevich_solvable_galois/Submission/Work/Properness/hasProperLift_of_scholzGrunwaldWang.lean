/-
Copyright (c) 2025. All rights reserved.

# Proper solutions from the Scholz–Grunwald–Wang input

The arithmetic step of Proposition 11 of

* A. Schmidt, K. Wingberg, *Šafarevič's theorem on solvable groups as Galois groups*,
  arXiv:math/9809211:

given the *named arithmetic hypothesis* `Work.Properness.Setup.ScholzGrunwaldWangInput` at the
local data (`T i ≤ H_K`, `φ i : T i →* A`), a proper solution of the embedding problem with
abelian kernel exists as soon as the local images generate the kernel `A`.

In other words: the Grunwald–Wang theorem supplies a global `1`-cocycle `x ∈ Z¹(H, A)` realizing
the prescribed local differences, and the properness criterion
(`Work.Properness.Setup.isProper_of_iSup_map_eq`) then makes the resulting solution `ψ = x · ψ₀`
surjective — this is the whole logical content of Proposition 11.

See `Submission/Work/Properness/ScholzGrunwaldWang.lean` for the paper-shaped statement
`Work.Properness.prop11`, and `Submission/Work/Properness/NOTES.md` §4 for the status of the
arithmetic hypothesis (in particular: it is a *hypothesis at the given local data*, since the
universal form over all abstract configurations is false).
-/
import Mathlib
import Submission.Work.Properness.Defs
import Submission.Work.Properness.exists_properLift_of_datum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Properness

open scoped Classical

noncomputable section

universe u v w x

/-- **Proposition 11, the arithmetic step.**  Let `S` be an embedding problem with abelian kernel
(`1 → A → E → Q → 1`, `A = ker π` abelian, `ρ : H ↠ Q` the map to be lifted, `H_K = ker ρ`), let
`ψ₀` be a plain solution, let `T i ≤ H_K` be a finite family of subgroups (in the arithmetic
situation: decomposition groups of primes splitting completely in the field cut out by `ρ`) with
prescribed local maps `φ i : T i →* A`, and suppose the named arithmetic hypothesis
`S.ScholzGrunwaldWangInput ψ₀ T hT φ` holds, i.e. the prescribed differences are realized by a
global `1`-cocycle.  If the local images generate `A` (`⨆ i, (φ i).range = ⊤`), then the embedding
problem has a **proper** (surjective) solution: `S.HasProperLift`.

This is `Work.Properness.exists_properLift_of_datum` with the hypothesis unpacked. -/
theorem hasProperLift_of_scholzGrunwaldWang {S : Setup.{u, v, w}} {ι : Type x} [Fintype ι]
    (ψ₀ : S.Lift) (T : ι → Subgroup S.H) (hT : ∀ i, T i ≤ S.HK) (φ : ∀ i, T i →* S.A)
    (h : S.ScholzGrunwaldWangInput ψ₀ T hT φ) (hgen : (⨆ i, (φ i).range) = ⊤) :
    S.HasProperLift :=
  @exists_properLift_of_datum.{w, v, u, x, 0} PUnit PUnit.unit PUnit.unit PUnit.unit
    S ι _ ψ₀ T hT φ h.2 hgen

end

end Work.Properness
