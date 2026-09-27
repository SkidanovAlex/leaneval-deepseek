import Mathlib

/-!
# PL vocabulary for `poincare_high_dim_topological` (lead file, frozen)

Everyone imports this file (`Submission.Work.PL.Defs`). Do NOT change existing definitions;
add new ones in your own area. Blueprint: Submission/Work/NOTES_LEAD_poincare_blueprint.md §1.
Methods of `Cx` are plain functions in namespace `PL` (write `PL.DimLE K p`, not `K.DimLE p`).
-/

open Set Metric

namespace PL

/-- `E n = ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Geometric simplicial complexes in `ℝᴺ`. -/
abbrev Cx (N : ℕ) := Geometry.SimplicialComplex ℝ (E N)

/-- Sup-norm cubes. -/
def closedCube {n : ℕ} (r : ℝ) : Set (E n) := {x | ∀ i, |x i| ≤ r}
def openCube {n : ℕ} (r : ℝ) : Set (E n) := {x | ∀ i, |x i| < r}

/-- The simplex spanned by a finite vertex set. -/
def simp {N : ℕ} (s : Finset (E N)) : Set (E N) := convexHull ℝ (s : Set (E N))

/-- A finite complex. -/
structure FinCx (N : ℕ) where
  K : Cx N
  fin : K.faces.Finite

/-- All faces have at most `p + 1` vertices. -/
def DimLE {N : ℕ} (K : Cx N) (p : ℕ) : Prop := ∀ s ∈ K.faces, s.card ≤ p + 1

/-- Mesh `< δ` (vertex diameter; simplices are convex hulls, so this bounds their diameter). -/
def MeshLT {N : ℕ} (K : Cx N) (δ : ℝ) : Prop :=
  ∀ s ∈ K.faces, ∀ x ∈ s, ∀ y ∈ s, dist x y < δ

/-- `K'` subdivides `K`. -/
def Subdivides {N : ℕ} (K' K : Cx N) : Prop :=
  K'.space = K.space ∧ ∀ s' ∈ K'.faces, ∃ s ∈ K.faces, simp s' ⊆ simp s

/-- `L` is a subcomplex of `K`. -/
def IsSub {N : ℕ} (L K : Cx N) : Prop := L.faces ⊆ K.faces

/-- `f` is affine on every simplex of `K`. -/
def LinOn {N m : ℕ} (K : Cx N) (f : E N → E m) : Prop :=
  ∀ s ∈ K.faces, ∃ A : E N →ᵃ[ℝ] E m, EqOn f A (simp s)

/-- Non-degenerate: the images of the vertices of each face are affinely independent. -/
def Nondeg {N m : ℕ} (K : Cx N) (f : E N → E m) : Prop :=
  ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => f v)

/-- Newman's "dimension ≤ d": covered by finitely many simplices with ≤ d+1 vertices
(`d : ℤ`; `d < 0` forces `A = ∅`). -/
def DomDim {m : ℕ} (A : Set (E m)) (d : ℤ) : Prop :=
  ∃ S : Finset (Finset (E m)), (∀ s ∈ S, (s.card : ℤ) ≤ d + 1) ∧ A ⊆ ⋃ s ∈ S, simp s

/-- Cube chart: an open embedding of the open unit cube into `M`. -/
structure CubeChart (n : ℕ) (M : Type*) [TopologicalSpace M] where
  toFun : E n → M
  cont : ContinuousOn toFun (openCube 1)
  emb : Topology.IsOpenEmbedding ((openCube (n := n) 1).domRestrict toFun)

/-- Every point of `M` lies in the image of the open ½-cube of some cube chart. -/
def LocCube (n : ℕ) (M : Type*) [TopologicalSpace M] : Prop :=
  ∀ x : M, ∃ ψ : CubeChart n M, x ∈ ψ.toFun '' openCube (1 / 2)

/-- `j`-connectivity in extension form: every map `Sʲ → X` extends over `Dʲ⁺¹`. -/
def ExtOverDisc (X : Type*) [TopologicalSpace X] (j : ℕ) : Prop :=
  ∀ f : C(sphere (0 : E (j + 1)) 1, X), ∃ g : C(closedBall (0 : E (j + 1)) 1, X),
    ∀ x : sphere (0 : E (j + 1)) 1, g ⟨x.1, sphere_subset_closedBall x.2⟩ = f x

/-- Open `n`-cell. -/
def IsOpenCell {M : Type*} [TopologicalSpace M] (n : ℕ) (W : Set M) : Prop :=
  IsOpen W ∧ Nonempty (W ≃ₜ E n)

/-- `M` is a union of `k` open `n`-cells. -/
def CellCover (n : ℕ) (M : Type*) [TopologicalSpace M] (k : ℕ) : Prop :=
  ∃ W : Fin k → Set M, (∀ i, IsOpenCell n (W i)) ∧ (⋃ i, W i) = univ

/-- Compactly supported self-homeomorphism, identity off a compact subset of `W`. -/
def CSupp {M : Type*} [TopologicalSpace M] (h : M ≃ₜ M) (W : Set M) : Prop :=
  ∃ C, IsCompact C ∧ C ⊆ W ∧ ∀ x ∉ C, h x = x

end PL
