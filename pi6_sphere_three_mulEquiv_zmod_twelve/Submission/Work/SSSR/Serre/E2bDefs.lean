import Mathlib
import Submission.Work.SSSR.Serre.Engine
import Submission.Work.SSSR.RatHurewicz.ExcisionSetup
import Submission.Work.SSSR.StemsB.exists_lift_rel
import Submission.Work.SSSR.Stems.Cubical.CubeFace
import Submission.Work.SSSR.Serre.E0SimplexDefs
import Submission.Work.SSSR.RatHurewicz.Bridge.Defs
import Submission.Work.RatHurewicz.Bridge.H_faces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Serre
variable {R : Type} [CommRing R] [Nontrivial R]

open scoped Topology unitInterval
open Work.SSSR.Stems.Cubical
namespace Work.SSSR.Serre

noncomputable section

/-- The **outer boundary** of the hat `LSet n = (Iⁿ × {0}) ∪ (∂Iⁿ × I)`: the set
`{(x,t) : x ∈ ∂Iⁿ, t = 1}`.  It is the boundary of the hat viewed as a disc, and is the set on
which the *hypothesis* of the compression property is used. -/
def hatBdry (n : ℕ) : Set (IC n × unitInterval) :=
  {q | q.1 ∈ Cube.boundary (Fin n) ∧ q.2 = 1}

/-- The hypothesis of `SerreE2b`, in the form of the compression property `CompressRel`:
every map of pairs `(Iⁿ, ∂Iⁿ) → (X,A)` with `n ≤ N` is homotopic to a map into `A`, relative to
the boundary. -/
def CompressHyp (X : Type) [TopologicalSpace X] (A : Set X) (N : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ N → Work.SSSR.RatHurewicz.CompressRel X A n

end

end Work.SSSR.Serre

namespace Work.SSSR.Serre

noncomputable section

open Work.SSSR.RatHurewicz.Bridge
/-- The **hat of the standard simplex**: `(Δⁿ × {0}) ∪ (∂Δⁿ × I)`, where
`∂Δⁿ = Work.Serre.simplexBdry n` is the simplicial boundary of `Δⁿ`. -/
def sHat (n : ℕ) : Set (↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval) :=
  {q | q.2 = 0} ∪ {q | q.1 ∈ simplexBdry n}

/-- The **outer boundary of the simplex hat**: `{(z,t) : z ∈ ∂Δⁿ, t = 1}`. -/
def sHatBdry (n : ℕ) : Set (↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval) :=
  {q | q.1 ∈ simplexBdry n ∧ q.2 = 1}

/-- The `i`-th coface of the standard simplex has a vanishing `i`-th coordinate. -/
theorem coface_mem_simplexBdry {m : ℕ} (i : Fin (m + 2))
    (x : ↥(stdSimplex ℝ (Fin (m + 1)))) :
    ((coface m i) x : ↥(stdSimplex ℝ (Fin (m + 2)))) ∈ simplexBdry (m + 1) :=
  ⟨i, Work.SSSR.RatHurewicz.Bridge.coface_apply_self m i x⟩

/-- **The homotopies of the relative cone construction**, for singular simplices of dimension
`≤ N`.

`G n σ : Δⁿ × I → X` is a homotopy from the singular simplex `σ` (at time `0`) into `A`
(at time `1`), whose restriction to the `i`-th coface `Δⁿ⁻¹ ⊆ Δⁿ` is the homotopy of the `i`-th
face of `σ` (`hside`).  A simplex whose image already lies in `A` is compressed by the constant
homotopy (`hconst`); this is what makes the resulting chain maps descend to the relative complex
`C_*(X)/C_*(A)`.

The values of `G n` for `n > N` are irrelevant. -/
structure SimpHom (X : Type) [TopologicalSpace X] (A : Set X) (N : ℕ) where
  /-- The homotopy of a singular simplex. -/
  G : ∀ n : ℕ, C(↥(stdSimplex ℝ (Fin (n + 1))), X) →
    C(↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval, X)
  /-- At time `0` the homotopy is the simplex itself. -/
  ht0 : ∀ (n : ℕ), n ≤ N → ∀ (s : C(↥(stdSimplex ℝ (Fin (n + 1))), X))
    (z : ↥(stdSimplex ℝ (Fin (n + 1)))), G n s (z, 0) = s z
  /-- The restriction of the homotopy to the `i`-th coface is the homotopy of the `i`-th face. -/
  hside : ∀ (n : ℕ), n + 1 ≤ N →
    ∀ (s : C(↥(stdSimplex ℝ (Fin (n + 2))), X)) (i : Fin (n + 2))
      (x : ↥(stdSimplex ℝ (Fin (n + 1)))) (t : unitInterval),
      G (n + 1) s ((coface n i) x, t) = G n (s.comp (coface n i)) (x, t)
  /-- At time `1` the homotopy lands in `A`. -/
  htop : ∀ (n : ℕ), n ≤ N → ∀ (s : C(↥(stdSimplex ℝ (Fin (n + 1))), X))
    (z : ↥(stdSimplex ℝ (Fin (n + 1)))), G n s (z, 1) ∈ A
  /-- A simplex whose image lies in `A` is compressed by the constant homotopy. -/
  hconst : ∀ (n : ℕ), n ≤ N → ∀ (s : C(↥(stdSimplex ℝ (Fin (n + 1))), X)),
    (∀ z, s z ∈ A) → ∀ (z : ↥(stdSimplex ℝ (Fin (n + 1)))) (t : unitInterval), G n s (z, t) = s z

end

end Work.SSSR.Serre
