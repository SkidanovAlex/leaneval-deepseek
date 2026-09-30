import Submission.Work.Serre.Basic
import Submission.Work.Serre.Models
import Submission.Work.StemsB.WangSphere
import Submission.Work.SSSR.Stems.Cubical.CubeFace
import Submission.Work.SSSR.StemsB.SerreFiltration
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.Cohomology.cupH
import Submission.Work.SSSR.Cohomology.HomologyPairSequence
import Submission.Work.SSSR.StemsB.Fibrations
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Serre
variable {R : Type} [CommRing R] [Nontrivial R]

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval
namespace Work.SSSR.Serre

noncomputable section

/-! ## E2 — the `E¹` page, in the form prescribed by the lead's ADDENDUM 1

The blueprint's E2 asked for **fibre-homotopy triviality** of a Serre fibration over a cube
(`Work.StemsB.FibrewiseTrivial`, homotopies over the base).  *That statement is not the right
target*: it needs the HLP with respect to test spaces such as `F × I`, which a Serre fibration does
not provide (only cubes), and the fibres of a Serre fibration are in general only weakly
equivalent.  The lead's ADDENDUM 1 replaces it by the four statements below, all of which use cubes
only.  Everything downstream (E1, E3(a), E3(b), E4) consumes only *homology*.
-/

/-- The **hat** of the cube-cylinder, `Iⁿ × 0 ∪ ∂Iⁿ × I ⊆ Iⁿ × I`: the subcomplex on which the
partial lift of the relative HLP is prescribed. -/
def hatSet (n : ℕ) : Set (Work.SSSR.Stems.Cubical.IC n × unitInterval) :=
  {x | x.2 = 0} ∪ {x | x.1 ∈ Cube.boundary (Fin n)}

/-- The inclusion `Iⁿ × 0 ∪ ∂Iⁿ × I → Iⁿ × I`. -/
def hatIncl (n : ℕ) : C(↥(hatSet n), Work.SSSR.Stems.Cubical.IC n × unitInterval) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- **E2(a): the relative cube HLP of a Serre fibration.**  A Serre fibration lifts homotopies of
the pair `(Iⁿ × I, Iⁿ × 0 ∪ ∂Iⁿ × I)`: a lift of the homotopy already given on
`Iⁿ × 0 ∪ ∂Iⁿ × I` extends to all of `Iⁿ × I`.  This is the statement whose proof is the standard
trick — the pair `(Iⁿ × I, Iⁿ × 0 ∪ ∂Iⁿ × I)` is homeomorphic to `(Iⁿ × I, Iⁿ × 0)` by radial
projection from `(½,…,½,2)`, after which the absolute cube HLP applies.

(`Iⁿ × 0` is part of the prescribed data: without it the statement is *false*, e.g. for the
constant map `S¹ → *`, where two lifts which disagree on the two ends of `I × 0` would exhibit a
homotopy between non-homotopic loops.  With `Iⁿ × 0` included, the case `n = 0` is the ordinary
path-lifting property, which Serre fibrations have.) -/
def SerreE2a : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (n : ℕ),
    Work.SSSR.StemsB.IsSerreFibration p →
      ∀ (H : C(Work.SSSR.Stems.Cubical.IC n × unitInterval, B))
        (g : C(↥(hatSet n), E))
        (_hg : p.comp g = H.comp (hatIncl n)),
        ∃ G : C(Work.SSSR.Stems.Cubical.IC n × unitInterval, E),
          p.comp G = H ∧ ∀ x : ↥(hatSet n), G (hatIncl n x) = g x

/-- **E2(b): compression implies vanishing of relative homology.**  If `A ⊆ X` and every map
`(Iⁿ, ∂Iⁿ) → (X, A)` is homotopic to a map into `A` relative to `∂Iⁿ` (for all `n ≤ N`), then
`H_n(X, A) = 0` for `n ≤ N`.  Proof: the *relative* singular cone construction of ADDENDUM 1 (C)
— deform singular simplices into `A` skeleton by skeleton, compatibly with faces.

`SerreE0Rel` is the same statement (it is the reusable cone step of E0); E0 is its special case
`A = {x₀}`. -/
def SerreE2b : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (A : Set X) (N : ℕ),
    (∀ (n : ℕ), n ≤ N →
      ∀ f : C(Work.SSSR.Stems.Cubical.IC n, X),
        (∀ t : Work.SSSR.Stems.Cubical.IC n, t ∈ Cube.boundary (Fin n) → f t ∈ A) →
        ∃ g : C(Work.SSSR.Stems.Cubical.IC n, X),
          (∀ t : Work.SSSR.Stems.Cubical.IC n, g t ∈ A) ∧
            ContinuousMap.HomotopicRel f g (Cube.boundary (Fin n))) →
    ∀ n : ℕ, n ≤ N →
      IsZero ((Work.SSSR.Cohomology.relChains R (TopCat.of X) A).homology n)

end

end Work.SSSR.Serre
