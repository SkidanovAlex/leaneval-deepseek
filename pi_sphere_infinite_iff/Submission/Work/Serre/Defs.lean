import Mathlib
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.localHomology
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.StemsB.HurewiczFibration

set_option synthInstance.maxHeartbeats 400000

/-!
# SUBPROJECT SERRE — vocabulary

This is the vocabulary chapter of Serre's rational finiteness theorem, formalising the blueprint
`Submission/Work/Drive/SERRE_BLUEPRINT.md`.  Nothing here is specific to the exotic sphere: the
notions are the standard ones of rational homotopy theory, written in the vocabulary of the
workspace (`Work.Cohomology.singularChains`, `Work.RatHurewicz.homotopyFibre`,
`HomotopyGroup`).

## Conventions (read this before using anything)

* `ratChains X = Work.Cohomology.singularChains ℚ X` is the **simplicial** singular chain complex
  with rational coefficients; `ratH X n = (ratChains X).homology n` is `H_n(X;ℚ)`.
* `ratHomologyMap f n : ratH X n ⟶ ratH Y n` is the map induced by `f : C(X,Y)`.  A continuous map
  is a **rational homology isomorphism** (`IsRatHomologyIso f`) when all of these are isomorphisms;
  since `H_0(X;ℚ)` is the free `ℚ`-module on `π₀(X)`, this also encodes bijectivity on `π₀`.
* `RatAcyclic X` means that the unique map `X → *` is a rational homology isomorphism, i.e. the
  **reduced** rational homology `H̃_*(X;ℚ)` vanishes.
* `WeaklyContractible X x₀` is cube-based: `∀ i, Subsingleton (π_i(X,x₀))`, `π₀` included.
* Homotopy groups are Mathlib's `HomotopyGroup (Fin n) X x₀` (`n`-cubes), so `π₀` is
  `HomotopyGroup (Fin 0) X x₀`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Serre

noncomputable section

/-- The singular chain complex of `X` with **rational** coefficients. -/
abbrev ratChains (X : TopCat) : ChainComplex (ModuleCat ℚ) ℕ :=
  Work.Cohomology.singularChains ℚ X

/-- `H_n(X;ℚ)`, the rational singular homology of `X`. -/
abbrev ratH (X : TopCat) (n : ℕ) : ModuleCat ℚ := (ratChains X).homology n

/-- The map `H_n(X;ℚ) → H_n(Y;ℚ)` induced by a continuous map `f : X → Y`. -/
abbrev ratHomologyMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) : ratH (TopCat.of X) n ⟶ ratH (TopCat.of Y) n :=
  HomologicalComplex.homologyMap
    (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) n

/-- **`f` is a rational homology isomorphism**: it induces an isomorphism on `H_n(-;ℚ)` for every
`n`.  Equivalently (the mapping theorem, blueprint E3(a)) its homotopy fibre is rationally acyclic,
but that is a theorem, not the definition. -/
def IsRatHomologyIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) : Prop :=
  ∀ n : ℕ, IsIso (ratHomologyMap f n)

/-- The unique map from `X` to the one-point space. -/
def toPoint (X : Type) [TopologicalSpace X] : C(X, PUnit) :=
  ⟨fun _ => PUnit.unit, continuous_const⟩

/-- **`X` is rationally acyclic**: its reduced rational homology vanishes, i.e. `X → *` is a
rational homology isomorphism. -/
def RatAcyclic (X : Type) [TopologicalSpace X] : Prop :=
  IsRatHomologyIso (toPoint X)

/-- **`X` has the rational homology of `S^n`** (`n ≥ 1`): connected, `H_n(X;ℚ) ≅ ℚ`, and
`H_j(X;ℚ) = 0` for `j ≠ 0, n`. -/
def RatHomologySphere (X : Type) [TopologicalSpace X] (n : ℕ) : Prop :=
  1 ≤ n ∧ PathConnectedSpace X ∧ Nonempty (ratH (TopCat.of X) n ≅ ModuleCat.of ℚ ℚ) ∧
    ∀ j : ℕ, j ≠ 0 → j ≠ n → IsZero (ratH (TopCat.of X) j)

/-- **`X` is weakly contractible** (cube-based homotopy groups, `π₀` included). -/
def WeaklyContractible (X : Type) [TopologicalSpace X] (x₀ : X) : Prop :=
  ∀ i : ℕ, Subsingleton (HomotopyGroup (Fin i) X x₀)

/-- **`X` is rationally acyclic in positive degrees below `m`**: `H_j(X;ℚ) = 0` for
`0 < j < m`. -/
def RatVanishingBelow (X : Type) [TopologicalSpace X] (m : ℕ) : Prop :=
  ∀ j : ℕ, 0 < j → j < m → IsZero (ratH (TopCat.of X) j)

/-- **`X` is `(k-1)`-connected** in the cube-based sense, with `π₀` included. -/
def Conn (X : Type) [TopologicalSpace X] (x₀ : X) (k : ℕ) : Prop :=
  ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) X x₀)

/-- The unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`, the space whose homotopy groups the STEMS contract is about. -/
abbrev Sph (n : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- **`π_{n+1}(X,x₀)` is torsion** (the conclusion shape of the drive's contract
`Work.Drive.StableStemsTorsion`, which is indexed so that the group is `π_{n+1}`). -/
def PiTorsion (X : Type) [TopologicalSpace X] (x₀ : X) (n : ℕ) : Prop :=
  ∀ α : HomotopyGroup (Fin (n + 1)) X x₀, ∃ N : ℕ, 0 < N ∧ α ^ N = 1

end

end Work.Serre
