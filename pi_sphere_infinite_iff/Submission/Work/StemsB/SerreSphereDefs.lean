import Mathlib
import Submission.Work.StemsB.SphLoopModel
import Submission.Work.StemsB.onePoint_radialPush
import Submission.Work.StemsB.RelThickening
import Submission.Work.StemsB.CubePairHomology

set_option synthInstance.maxHeartbeats 400000

/-!
# The Serre exact sequence over the sphere: the decomposition and the triviality interface

This file sets up the *second* decomposition of the sphere model `SphModel b = OnePoint ℝᵇ`
(`Submission/Work/StemsB/SphLoopModel.lean`) that the sphere case of the Serre exact sequence in the
stable range uses.  Besides the thick outer disc `P = sphLoopThick b` (which contains the base point
`∞` and the whole outer disc `sphLoopOut b`) it introduces the thick inner cube

  `Q = sphLoopBig b = {↑v | ∀ i, |v i| < 3/2}`   (open, contractible, does not contain `∞`),

whose intersection with `P` is the **shell** `sphLoopMid b = P ∩ Q`, a set homotopy equivalent to
`S^{b-1}`.  The two open sets `P`, `Q` cover the sphere; the pair `(Q, P ∩ Q)` is a "disc pair"
`(D^b, S^{b-1})` in the weak sense needed by the relative Künneth theorem `Work.StemsB.cubePair_iso`
(both component maps of `(Q, P ∩ Q) → (I^b, ∂I^b)` are homotopy equivalences).

The point `sphShellPt b` (the first coordinate equal to `1`) lies in the shell, so that both `P` and
`Q` are contractible *open* sets containing it; the fibrations over them therefore have the *same*
fibre `p⁻¹(sphShellPt b)`.

## The triviality interface

The mathematical input of the Serre exact sequence over a sphere is the *fibrewise* triviality of
the fibration over each of the two pieces: over the shell, where a disc-pair structure is available,
the relative Künneth theorem computes the relative homology, and for the *pair* `(E|_Q, E|_{P∩Q})`
to be comparable with `(Q × F, (P ∩ Q) × F)` the homotopies of the trivialisation must preserve the
base coordinate (otherwise they need not restrict to the preimage of a subset of the base).

`Work.StemsB.FibrewiseTrivial p W d₀` records exactly that data for a continuous map `p : E → B`, an
open set `W ⊆ B` and a point `d₀ ∈ W`, and
`Work.StemsB.relChainsMapOf_homologyMap_isIso_of_fibrewiseTrivial` is its consequence: for every
`A ⊆ W` and every map `f : A → A'` induced by the pair restriction, the induced map of relative
chain complexes `(p⁻¹W, p⁻¹A) → (W × F, A × F)` is a quasi-isomorphism.

For a **Hurewicz fibration** the fibrewise triviality over a contractible base is a theorem of Dold
and Strøm (fibrations over a contractible base are fibre-homotopy trivial); it is *not* available in
this workspace.  It is however available *explicitly* for the path–loop fibration
`Work.StemsB.evalOne X x₀`, which is the fibration the application (the transgression isomorphism
for the rational Hurewicz theorem) uses.  The main theorem of this chapter,
`Work.StemsB.serreExactSphere_of_fibrewiseTrivial`, is therefore stated with the fibrewise
triviality over the two pieces as an explicit hypothesis.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

variable {E : Type} {B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## The decomposition of the sphere -/

/-- The **thick inner cube** `{|v|_∞ < 3/2}` (the "inner piece" `Q`), an open set not containing
`∞`. -/
def sphLoopBig (n : ℕ) : Set (SphModel n) :=
  {x | ∃ v : EuclideanSpace ℝ (Fin n), x = ↑v ∧ ∀ i, |v i| < 3 / 2}

/-- The **shell** `P ∩ Q` between the outer thickening and the inner cube. -/
def sphLoopMid (n : ℕ) : Set (SphModel n) := sphLoopThick n ∩ sphLoopBig n

/-- The relative part `(P ∩ Q) × Y` of the product `Q × Y`, as a subset of `↥Q × Y`. -/
def sphLoopMidProd (n : ℕ) (Y : Type) : Set (↥(sphLoopBig n) × Y) :=
  {x | (x.1 : SphModel n) ∈ sphLoopMid n}

/-- A point of the model with first coordinate `1`; it lies in the shell `sphLoopMid b`, so that
both `sphLoopThick b` and `sphLoopBig b` are contractible open sets containing it. -/
def sphShellPt (n : ℕ) : SphModel n :=
  OnePoint.some ((WithLp.equiv 2 (Fin n → ℝ)).symm
    (fun i : Fin n => if (i : ℕ) = 0 then (1 : ℝ) else 0))

/-! ## The triviality interface -/

/-- **Fibrewise triviality of `p : E → B` over `W ⊆ B`, with fibre the fibre over `d₀ ∈ W`.**

This is the data that the Serre exact sequence needs: maps `Φ : p⁻¹W → W × p⁻¹(d₀)` and
`Ψ : W × p⁻¹(d₀) → p⁻¹W` over the base (`(Φ x).1 = p x`, `(Ψ y).1 = y.1`) together with
**fibrewise** homotopies `id ≃ Ψ ∘ Φ` and `Φ ∘ Ψ ≃ id` (both preserving the base coordinate). -/
def FibrewiseTrivial (p : C(E, B)) (W : Set B) (d₀ : ↥W) : Prop :=
  ∃ (Φ : C(↥(p ⁻¹' W), ↥W × ↥(p ⁻¹' {d₀.1})))
    (Ψ : C(↥W × ↥(p ⁻¹' {d₀.1}), ↥(p ⁻¹' W))),
    (∀ x, (Φ x).1 = ⟨p x.1, x.2⟩) ∧ (∀ y, p (Ψ y).1 = (y.1 : B)) ∧
    (∃ (H : C(↥(p ⁻¹' W) × unitInterval, ↥(p ⁻¹' W))),
      (∀ x, H (x, 0) = x) ∧ (∀ x, H (x, 1) = Ψ (Φ x)) ∧
      (∀ x t, p (H (x, t)).1 = p x.1)) ∧
    (∃ (K : C((↥W × ↥(p ⁻¹' {d₀.1})) × unitInterval, ↥W × ↥(p ⁻¹' {d₀.1}))),
      (∀ y, K (y, 0) = y) ∧ (∀ y, K (y, 1) = Φ (Ψ y)) ∧
      (∀ y t, (K (y, t)).1 = y.1))

end

end Work.StemsB
