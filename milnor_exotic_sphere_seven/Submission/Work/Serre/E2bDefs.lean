import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.Stems.Cubical.CubeFace
import Submission.Work.Serre.E0SimplexDefs
import Submission.Work.RatHurewicz.Bridge.Defs
import Submission.Work.RatHurewicz.Bridge.H_faces

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# E2(b) — the vocabulary of the relative cone construction

`SerreE2b` (`Submission/Work/Serre/Engine.lean`) states that a pair `(X,A)` for which every map of
pairs `(Iⁿ, ∂Iⁿ) → (X,A)` compresses into `A` (for `n ≤ N`) has vanishing relative homology
`H_n(X,A;ℤ) = 0`, `n ≤ N`.

The proof is the *relative cone construction*: for every singular simplex `σ` one builds a homotopy
`G_σ : Δⁿ × I → X` from `σ` to a map into `A`, whose restrictions to the faces are the homotopies
of the faces; the prism chains of the `G_σ` then give a chain contraction of the relative complex
`C_*(X,A) = C_*(X)/C_*(A)`.

This file contains the vocabulary:

* `Work.Serre.hatBdry` — the outer boundary of the hat `LSet n = (Iⁿ×{0}) ∪ (∂Iⁿ×I)`;
* `Work.Serre.CompressHyp` — the hypothesis of `SerreE2b` in the form `CompressRel`;
* `Work.Serre.CubComp` — the family of compression homotopies of cubes, in dimensions `≤ N`.
-/

open scoped Topology unitInterval
open Work.Stems.Cubical

namespace Work.Serre

noncomputable section

/-- The **outer boundary** of the hat `LSet n = (Iⁿ × {0}) ∪ (∂Iⁿ × I)`: the set
`{(x,t) : x ∈ ∂Iⁿ, t = 1}`.  It is the boundary of the hat viewed as a disc, and is the set on
which the *hypothesis* of the compression property is used. -/
def hatBdry (n : ℕ) : Set (IC n × unitInterval) :=
  {q | q.1 ∈ Cube.boundary (Fin n) ∧ q.2 = 1}

theorem hatBdry_subset_hat (n : ℕ) : hatBdry n ⊆ Work.StemsB.LSet n :=
  fun _ hq => Or.inr hq.1

/-- The hypothesis of `SerreE2b`, in the form of the compression property `CompressRel`:
every map of pairs `(Iⁿ, ∂Iⁿ) → (X,A)` with `n ≤ N` is homotopic to a map into `A`, relative to
the boundary. -/
def CompressHyp (X : Type) [TopologicalSpace X] (A : Set X) (N : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ N → Work.RatHurewicz.CompressRel X A n

/-- **The family of compression homotopies of cubes**, in dimensions `≤ N`.

`K n c : Iⁿ × I → X` is a homotopy from the cube `c` (at time `0`) into `A` (at time `1`), whose
restriction to the face `x i = ε` of the cube is the homotopy `K (n-1) (c ∘ face)`.  For a cube `c`
whose image already lies in `A` it is the constant homotopy — this is what makes the chain maps
descend to the relative complex.

The values of `K` above dimension `N` are irrelevant. -/
structure CubComp (X : Type) [TopologicalSpace X] (A : Set X) (N : ℕ) where
  /-- The compression homotopy of a cube. -/
  K : ∀ n : ℕ, C(IC n, X) → C(IC n × unitInterval, X)
  /-- At time `0` the homotopy is the cube itself. -/
  ht0 : ∀ (n : ℕ), n ≤ N → ∀ (c : C(IC n, X)) (x : IC n), K n c (x, 0) = c x
  /-- The homotopy restricted to the face `x i = ε` is the homotopy of the corresponding face. -/
  hside : ∀ (m : ℕ), m + 1 ≤ N → ∀ (c : C(IC (m+1), X)) (i : Fin (m+1)) (ε : unitInterval)
    (x : IC (m+1)) (t : unitInterval), x i = ε →
      K (m+1) c (x, t) = K m (c.comp (faceCM i ε))
        (Work.RatHurewicz.Bridge.proj m i x, t)
  /-- At time `1` the homotopy lands in `A`. -/
  htop : ∀ (n : ℕ), n ≤ N → ∀ (c : C(IC n, X)) (x : IC n), K n c (x, 1) ∈ A
  /-- A cube whose image lies in `A` is compressed by the constant homotopy. -/
  hconst : ∀ (n : ℕ), n ≤ N → ∀ (c : C(IC n, X)), (∀ x, c x ∈ A) → ∀ (x : IC n) (t : unitInterval),
    K n c (x, t) = c x

end

end Work.Serre

namespace Work.Serre

noncomputable section

open Work.RatHurewicz.Bridge

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
  ⟨i, Work.RatHurewicz.Bridge.coface_apply_self m i x⟩

/-- The point `(coface m i x, t)` of `Δ^{m+1} × I` lies in the hat `sHat (m+1)`. -/
theorem coface_mem_sHat {m : ℕ} (i : Fin (m + 2))
    (x : ↥(stdSimplex ℝ (Fin (m + 1)))) (t : unitInterval) :
    (((coface m i) x : ↥(stdSimplex ℝ (Fin (m + 2)))), t) ∈ sHat (m + 1) :=
  Or.inr (coface_mem_simplexBdry i x)

theorem sHatBdry_subset_sHat (n : ℕ) : sHatBdry n ⊆ sHat n :=
  fun _ hq => Or.inr hq.1

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

end Work.Serre
