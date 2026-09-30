import Mathlib
import Submission.Work.Gen.cochainAssembly
import Submission.Work.ThomBordism.sigmaSSetIso
import Submission.Work.Cohomology.CupRing

/-!
# The singular cochains of a `σ`-type of spaces: the cochain-level decomposition

For a family of topological spaces `Y : ι → Type` the `σ`-type `Σ i, Y i` (with the sum topology)
is the coproduct of the pieces, so every singular simplex of `Σ i, Y i` lies in a single piece
(the standard simplex is connected: `Work.ThomBordism.exists_lift_sigma`).  This module sets up

* `Work.Serre.Sigma.legs` / `split` -- the legs of the coproduct cofan of the singular simplices
  and its inverse (the simplex splitting);
* `Work.Serre.Sigma.restr R i n` -- restriction of an `n`-cochain on `Σ i, Y i` to the `i`-th
  piece (pullback along the inclusion);
* `Work.Serre.Sigma.assemble R n` -- assembly of a family of cochains on the pieces into a cochain
  on `Σ i, Y i` (the value at a simplex is the value of the cochain of the piece containing it);

together with the basic computation rules (`genEval_restr`, `genEval_assemble`) and the
compatibility of the splitting with the face maps (`split_δ`) and the Alexander–Whitney faces
(`split_frontFace`, `split_backFace`).

The identities that make `restr`/`assemble` a pair of inverse morphisms of cochain complexes
(differentials, cup products) are proved in the sibling modules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

namespace Work.Serre.Sigma

noncomputable section

variable {ι : Type} {Y : ι → Type} [∀ i, TopologicalSpace (Y i)]

/-! ## The singular simplicial set of the `σ`-type and its pieces -/

/-- The singular simplicial set of the `σ`-type `Σ i, Y i`. -/
abbrev Ssig (ι : Type) (Y : ι → Type) [∀ i, TopologicalSpace (Y i)] : SSet :=
  TopCat.toSSet.obj (TopCat.of (Σ i, Y i))

/-- The singular simplicial set of the `i`-th piece. -/
abbrev Spiece (ι : Type) (Y : ι → Type) [∀ i, TopologicalSpace (Y i)] (i : ι) : SSet :=
  TopCat.toSSet.obj (TopCat.of (Y i))

/-- The inclusion of the `i`-th piece of the `σ`-type. -/
def pieceIncl (i : ι) : TopCat.of (Y i) ⟶ TopCat.of (Σ j, Y j) :=
  TopCat.sigmaι (fun i => TopCat.of (Y i)) i

/-- The legs of the coproduct cofan: `(i, s) ↦ s`, as an `n`-simplex of `Σ i, Y i`. -/
def legs (n : ℕ) :
    (Σ i, (Spiece ι Y i) _⦋n⦌) → (Ssig ι Y) _⦋n⦌ :=
  fun x => (TopCat.toSSet.map (pieceIncl (Y := Y) x.1)).app (Opposite.op ⦋n⦌) x.2

/-- **The legs of the coproduct cofan are a bijection**: every `n`-simplex of the `σ`-type lies in
a single piece (`Work.ThomBordism.sigmaLegs_bijective`). -/
theorem legs_bijective (n : ℕ) : Function.Bijective (legs (ι := ι) (Y := Y) n) :=
  Work.ThomBordism.sigmaLegs_bijective (fun i => TopCat.of (Y i)) (Opposite.op ⦋n⦌)

/-- **The simplex splitting**: the piece containing a simplex of the `σ`-type, together with the
simplex read in that piece. -/
noncomputable def split (n : ℕ) (σ : (Ssig ι Y) _⦋n⦌) :
    Σ i, (Spiece ι Y i) _⦋n⦌ :=
  ((legs_bijective (ι := ι) (Y := Y) n).surjective σ).choose

/-- The defining property of the splitting. -/
theorem legs_split (n : ℕ) (σ : (Ssig ι Y) _⦋n⦌) :
    legs (ι := ι) (Y := Y) n (split (ι := ι) (Y := Y) n σ) = σ :=
  ((legs_bijective (ι := ι) (Y := Y) n).surjective σ).choose_spec

/-- The splitting is a section of `legs`. -/
theorem split_legs (n : ℕ) (x : Σ i, (Spiece ι Y i) _⦋n⦌) :
    split (ι := ι) (Y := Y) n (legs (ι := ι) (Y := Y) n x) = x :=
  (legs_bijective (ι := ι) (Y := Y) n).injective (legs_split n (legs (ι := ι) (Y := Y) n x))

/-- The splitting of a simplex coming from the `i`-th piece. -/
theorem split_pieceIncl (n : ℕ) (i : ι) (s : (Spiece ι Y i) _⦋n⦌) :
    split (ι := ι) (Y := Y) n (legs (ι := ι) (Y := Y) n ⟨i, s⟩) = ⟨i, s⟩ :=
  split_legs n ⟨i, s⟩

/-! ## Compatibility of the splitting with the face maps -/

/-- The face maps commute with the legs of the cofan. -/
theorem legs_δ (n : ℕ) (j : Fin (n + 2)) (x : Σ i, (Spiece ι Y i) _⦋n + 1⦌) :
    (Ssig ι Y).δ j (legs (ι := ι) (Y := Y) (n + 1) x) =
      legs (ι := ι) (Y := Y) n ⟨x.1, (Spiece ι Y x.1).δ j x.2⟩ :=
  (SSet.δ_naturality_apply (TopCat.toSSet.map (pieceIncl (Y := Y) x.1)) j x.2).symm

/-- **The splitting is compatible with the face maps.** -/
theorem split_δ (n : ℕ) (j : Fin (n + 2)) (σ : (Ssig ι Y) _⦋n + 1⦌) :
    split (ι := ι) (Y := Y) n ((Ssig ι Y).δ j σ) =
      ⟨(split (ι := ι) (Y := Y) (n + 1) σ).1,
        (Spiece ι Y (split (ι := ι) (Y := Y) (n + 1) σ).1).δ j
          (split (ι := ι) (Y := Y) (n + 1) σ).2⟩ := by
  apply (legs_bijective (ι := ι) (Y := Y) n).injective
  rw [legs_split, ← legs_δ n j (split (ι := ι) (Y := Y) (n + 1) σ),
    legs_split (ι := ι) (Y := Y) (n + 1) σ]

/-- The front face maps commute with the legs of the cofan. -/
theorem legs_frontFace (n m : ℕ) (x : Σ i, (Spiece ι Y i) _⦋n + m⦌) :
    Work.Cohomology.frontFace (Ssig ι Y) n (n + m) (Nat.le_add_right n m)
        (legs (ι := ι) (Y := Y) (n + m) x) =
      legs (ι := ι) (Y := Y) n ⟨x.1, Work.Cohomology.frontFace (Spiece ι Y x.1) n (n + m)
        (Nat.le_add_right n m) x.2⟩ :=
  (NatTrans.naturality_apply (TopCat.toSSet.map (pieceIncl (Y := Y) x.1))
    (Work.Cohomology.frontIncl n (n + m) (Nat.le_add_right n m)).op x.2).symm

/-- **The splitting is compatible with the front faces.** -/
theorem split_frontFace (n m : ℕ) (σ : (Ssig ι Y) _⦋n + m⦌) :
    split (ι := ι) (Y := Y) n
        (Work.Cohomology.frontFace (Ssig ι Y) n (n + m) (Nat.le_add_right n m) σ) =
      ⟨(split (ι := ι) (Y := Y) (n + m) σ).1, Work.Cohomology.frontFace
        (Spiece ι Y (split (ι := ι) (Y := Y) (n + m) σ).1) n (n + m) (Nat.le_add_right n m)
        (split (ι := ι) (Y := Y) (n + m) σ).2⟩ := by
  apply (legs_bijective (ι := ι) (Y := Y) n).injective
  rw [legs_split, ← legs_frontFace n m (split (ι := ι) (Y := Y) (n + m) σ),
    legs_split (ι := ι) (Y := Y) (n + m) σ]

/-- The back face maps commute with the legs of the cofan. -/
theorem legs_backFace (n m : ℕ) (x : Σ i, (Spiece ι Y i) _⦋n + m⦌) :
    Work.Cohomology.backFace (Ssig ι Y) n m (legs (ι := ι) (Y := Y) (n + m) x) =
      legs (ι := ι) (Y := Y) m ⟨x.1, Work.Cohomology.backFace (Spiece ι Y x.1) n m x.2⟩ :=
  (NatTrans.naturality_apply (TopCat.toSSet.map (pieceIncl (Y := Y) x.1))
    (Work.Cohomology.backIncl n m).op x.2).symm

/-- **The splitting is compatible with the back faces.** -/
theorem split_backFace (n m : ℕ) (σ : (Ssig ι Y) _⦋n + m⦌) :
    split (ι := ι) (Y := Y) m (Work.Cohomology.backFace (Ssig ι Y) n m σ) =
      ⟨(split (ι := ι) (Y := Y) (n + m) σ).1, Work.Cohomology.backFace
        (Spiece ι Y (split (ι := ι) (Y := Y) (n + m) σ).1) n m
        (split (ι := ι) (Y := Y) (n + m) σ).2⟩ := by
  apply (legs_bijective (ι := ι) (Y := Y) m).injective
  rw [legs_split, ← legs_backFace n m (split (ι := ι) (Y := Y) (n + m) σ),
    legs_split (ι := ι) (Y := Y) (n + m) σ]

/-! ## The two cochain-level maps -/

/-- **Restriction to the `i`-th piece**: the pullback of a cochain on the `σ`-type along the
inclusion `Y i ⟶ Σ j, Y j`. -/
noncomputable def restr (R : Type) [CommRing R] (i : ι) (n : ℕ) :
    Work.Cohomology.Cochain R (Ssig ι Y) n →ₗ[R] Work.Cohomology.Cochain R (Spiece ι Y i) n :=
  (Work.Cohomology.cochainPullbackHom R (TopCat.of (Y i)) (TopCat.of (Σ j, Y j))
    (pieceIncl (Y := Y) i) n).hom

/-- The computation rule for the restriction. -/
theorem genEval_restr (R : Type) [CommRing R] (i : ι) (n : ℕ)
    (β : Work.Cohomology.Cochain R (Ssig ι Y) n) (s : (Spiece ι Y i) _⦋n⦌) :
    Work.Cohomology.genEval R (Spiece ι Y i) (restr R i n β) s =
      Work.Cohomology.genEval R (Ssig ι Y) β (legs (Y := Y) n ⟨i, s⟩) :=
  Work.Gen.genEval_cochainPullbackHom R (pieceIncl (Y := Y) i) β s

/-- **Assembly of a family of cochains on the pieces**: the cochain on the `σ`-type whose value at
a simplex is the value of the cochain of the piece containing it. -/
noncomputable def assemble (R : Type) [CommRing R] (n : ℕ)
    (w : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) n) :
    Work.Cohomology.Cochain R (Ssig ι Y) n :=
  Work.Gen.mkCochain R (Ssig ι Y) n
    (fun σ => Work.Cohomology.genEval R (Spiece ι Y (split (Y := Y) n σ).1)
      (w (split (Y := Y) n σ).1) (split (Y := Y) n σ).2)

/-- The computation rule for the assembly. -/
theorem genEval_assemble (R : Type) [CommRing R] (n : ℕ)
    (w : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) n) (σ : (Ssig ι Y) _⦋n⦌) :
    Work.Cohomology.genEval R (Ssig ι Y) (assemble R n w) σ =
      Work.Cohomology.genEval R (Spiece ι Y (split (Y := Y) n σ).1)
        (w (split (Y := Y) n σ).1) (split (Y := Y) n σ).2 :=
  Work.Gen.genEval_mkCochain R (Ssig ι Y) n _ σ


/-! ## The `σ`-type of a family of continuous maps -/

section SigmaMap

variable {X B : ι → Type} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (B i)]

/-- The `σ`-type of a family of continuous maps. -/
def sigmaMap (q : ∀ i, C(X i, B i)) : C((Σ i, X i), (Σ i, B i)) :=
  ⟨fun z => ⟨z.1, q z.1 z.2⟩, by continuity⟩

@[simp]
theorem sigmaMap_apply (q : ∀ i, C(X i, B i)) (z : Σ i, X i) :
    sigmaMap q z = ⟨z.1, q z.1 z.2⟩ := rfl

/-- The `σ`-map is the map of the target of `Work.Serre.thomCylAt_of_sigma`. -/
theorem sigmaMap_eq (q : ∀ i, C(X i, B i)) :
    sigmaMap q = (⟨fun z => ⟨z.1, q z.1 z.2⟩, by continuity⟩ : C((Σ i, X i), (Σ i, B i))) := rfl

/-- The compatibility of the `σ`-map with the inclusions of the pieces. -/
theorem sigmaMap_pieceIncl (q : ∀ i, C(X i, B i)) (i : ι) :
    (pieceIncl (Y := X) i) ≫ TopCat.ofHom (sigmaMap q)
      = TopCat.ofHom (q i) ≫ pieceIncl (Y := B) i := by
  apply TopCat.Hom.ext
  apply ContinuousMap.ext
  intro z
  rfl

end SigmaMap


/-! ## The subspace of the `σ`-type defined by a family of subsets -/

/-- The subspace of the `σ`-type `Σ i, Y i` consisting of the points whose second component lies
in `A (·.1)`. -/
def sigmaSet (A : ∀ i, Set (Y i)) : Set (Σ i, Y i) :=
  {y | y.2 ∈ A y.1}

@[simp]
theorem mem_sigmaSet (A : ∀ i, Set (Y i)) (y : Σ i, Y i) :
    y ∈ sigmaSet A ↔ y.2 ∈ A y.1 := Iff.rfl

end

end Work.Serre.Sigma
