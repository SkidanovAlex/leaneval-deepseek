/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The indicator of a position of a visit list lying in a track

`Dunwoody/ArcPref.lean` defines

    `midSum τ vs k = (((vs.take k).map (fun m => if trackOf m = τ then 1 else 0))).sum`,

the number (mod 2) of visits among the first `k` of `vs` that lie in the track `τ`.  The
`Finset`-level statements about `midSum` need the same indicator as a function of the *position*:
`midInd τ vs i` is `[vs[i] ∈ τ]` for a position `i` of `vs`, and `0` for a position beyond the end
of `vs`.  Using `vs[i]?` (rather than `vs[i]`) keeps the definition free of proof arguments.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.ArcPref

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-- **The indicator of the `i`-th visit of `vs` lying in the track `τ`**: `1` if `i` is a position
of `vs` whose visit lies in `τ`, and `0` otherwise (in particular for `i ≥ vs.length`). -/
noncomputable def midInd (τ : Dunwoody.Track D) (vs : List (Dunwoody.MidV D)) (i : ℕ) :
    ZMod 2 := by
  classical
  exact match vs[i]? with
    | some m => if Dunwoody.trackOf m = τ then 1 else 0
    | none => 0

end Work.ORDunwoody
