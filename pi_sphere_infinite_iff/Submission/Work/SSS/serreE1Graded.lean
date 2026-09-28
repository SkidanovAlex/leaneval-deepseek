import Mathlib
import Submission.Work.SSS.grFMap

/-!
# The Eilenberg–Zilber splitting of the graded pieces of the Serre filtration

The proof is `Work.SSS.serreE1Graded_iso` in `Submission/Work/SSS/grFMap.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

/-- **The Eilenberg–Zilber splitting of the graded pieces of the Serre filtration.**  For a
morphism of simplicial sets `f : X ⟶ Y`, the `d`-th graded piece of the Serre filtration of the
simplicial chain complex of `X` along `f` — the quotient of the chains on the preimage of the
`(d+1)`-st skeleton by the chains on the preimage of the `d`-th skeleton — is the direct sum, over
the *nondegenerate* `d`-simplices `y` of `Y`, of the σ-pieces `C(T_y)/C(∂T_y)`, where
`T_y = Δ[d] ×_Y X` is the pullback of `f` along the simplex `y` and `∂T_y` is the preimage of
`∂Δ[d]`.

This is `REFS/NOTES_LEAD_SSS.md` §1(a).  A simplex `x` of `X` whose image `f x` in `Y` has
nondegenerate part of dimension exactly `d` can be written uniquely as `y` composed with a monotone
surjection `[n] ↠ [d]` (Eilenberg–Zilber lemma, `SSet.exists_nonDegenerate` /
`SSet.unique_nonDegenerate_map`); this identifies the degreewise bases and hence the chain
complexes.  Concretely the composite `∐_y T_y → X` (whose `y`-component is the second projection of
the pullback) is bijective on the simplices whose image has nondegenerate dimension `d`, and the
differentials agree because a face `d_j x` stays in the quotient iff the corresponding face
`d_j(u,x)` is not in `∂T_y`.

For `d = 0`: `grF F 0 = F.obj 0 = C(f⁻¹ (sk 1))`, `∂Δ[0] = ⊥` so `pieceAlong f (nIndexSigma Y 0 y)`
is `C(T_y)` — the chain complex of the fibre `Sing (f⁻¹ {y})` over the vertex `y` — and
`f⁻¹ (skeleton 1) = ∐_{vertices y} T_y`.

Vocabulary: `Submission/Work/SSS/serreE1Defs.lean` (`Work.SSS.grF`, `Work.SSS.natShift`,
`Work.SSS.nIndex`, `Work.SSS.nIndexSigma`, `Work.SSS.pieceAlong`, `Work.SSS.pullAlong`,
`Work.SSS.bdryAlong`, `Work.SSS.sCC`, `Work.SSS.sCCMap`), plus
`Work.StemsB.serreChainFiltration` and `Work.SSS.grF`/`Work.SSS.incF` from
`Submission/Work/SSS/Filtration.lean`.

Do NOT use `sorry`, `axiom` or `admit`. -/
theorem serreE1Graded {X Y : SSet.{0}} (f : X ⟶ Y) (d : ℕ) :
    Nonempty (Work.SSS.grF (Work.SSS.natShift ⋙ Work.StemsB.serreChainFiltration f ℤ) d
      ≅ (∐ (fun y : Work.SSS.nIndex Y d =>
          Work.SSS.pieceAlong f (Work.SSS.nIndexSigma Y d y)))) :=
  serreE1Graded_iso f d

end Work.SSS
