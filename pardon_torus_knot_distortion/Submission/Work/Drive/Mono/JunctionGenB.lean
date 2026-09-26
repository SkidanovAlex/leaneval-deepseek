import Mathlib
import Submission.Work.Drive.Mono.JunctionGen

/-!
# The corrected junction bundle `JunctionGenB`

`Work.Drive.Mono.JunctionGen` (`Mono/JunctionGen.lean`) has four clauses; its clause **(c)** asks
that *every* carrier point with two extremal box coordinates has its `ℓ`-level in the finite
exceptional set `exc`.  That is **not satisfiable in general**: such points need not lie on the box
sphere (the third coordinate may be strictly outside the box — the "crust" of the box), the surface
may contain an *arc* of an edge line, and then infinitely many distinct `ℓ`-levels would have to lie
in the finite `exc`.  (This is the obstruction of `Mono/NOTES_JunctionGen_OBSTRUCTIONS.md` §2, where
the carrier contains two infinite flat families along box edges.)

None of the *consumers* of the clause ever needs it away from the box sphere: the trace of a level
is contained in `closure (PBox) = {boxNorm ≤ s}` (`frontier R ⊆ closure R ⊆ closure (PBox)`), so a
crust point of the carrier is never on the trace; and the assembly
`Work.Drive.Mono.trace_locallyEuclidean_of_junctionGen` uses clause (c) only at a point which is
*already known to be on the box sphere* (it derives the two-extremal condition from
`boxNorm = s`), while `Work.Drive.Mono.aboveGenericAt_of_junctionGen` uses only clause (a).

`Work.Drive.Mono.JunctionGenB` below is the corrected bundle: clause (c) is restricted to the box
sphere.  It is **implied** by `JunctionGen` (`junctionGenB_of_junctionGen`), it is *provable* for
generic data at a level where the box sphere is in general position (`BoxGen`: the box sphere meets
the surface in a finite union of circles, which meets an edge *line* in finitely many points, so
only finitely many levels have to be added to `exc`), and the two assemblies of the trace are
adapted to it in `Mono/traceLocallyEuclidean_of_junctionGenB.lean` and
`Mono/aboveGenericAt_of_junctionGenB.lean` (the proofs are the resident ones with the definition
swapped).
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

namespace Work.Drive.Mono

noncomputable section

/-- **The corrected stratified genericity of the trace at the junctions.**

Clauses (a), (b), (d) of `Work.Drive.Mono.JunctionGen` verbatim; clause (c) — the levels of the
carrier points of the box sphere with two extremal coordinates lie in `exc` — restricted to points
*on the box sphere*. -/
def JunctionGenB (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) : Prop :=
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) → ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lam →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0 ∧
        fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
        ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
          t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) → ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| = h → ℓ z < lam →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
        fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
        ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠
          t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) →
      ℓ z ∈ (exc : Set ℝ)) ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| = h →
      ℓ z ∈ (exc : Set ℝ))

/-- **The corrected bundle is implied by the original one** (the restriction of clause (c) to the
box sphere is a weakening). -/
theorem junctionGenB_of_junctionGen {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} (hJ : JunctionGen ψ s c σ u v h ℓ exc lam0 lam1) :
    JunctionGenB ψ s c σ u v h ℓ exc lam0 lam1 :=
  ⟨hJ.1, hJ.2.1, fun z hz _ hext => hJ.2.2.1 z hz hext, hJ.2.2.2⟩

end

end Work.Drive.Mono
