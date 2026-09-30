import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Serre.E0Defs
import Submission.Work.Serre.E0SbdryMatching
import Submission.Work.Serre.E0SimplexBdryExt
import Submission.Work.Serre.e0CubeBoundaryExtension
import Submission.Work.RatHurewicz.Bridge.SigmaChain
import Submission.Work.RatHurewicz.ConnectivityBridge

/-!
# SUBPROJECT SERRE — E0 in range form: the cone construction

The blueprint's ADDENDUM 1 (C): `Work.Serre.hasSimplexCones_of_homotopyGroup_subsingleton`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial Topology unitInterval

namespace Work.Serre

noncomputable section

open Work.RatHurewicz.Bridge

variable {X : Type} [TopologicalSpace X]

/-! ## The concrete map attached to a singular simplex -/

/-- The map on the standard simplex attached to a singular `n`-simplex. -/
def concretize {n : ℕ} (s : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n⦌)) : C(↥(stdSimplex ℝ (Fin (n+1))), X) :=
  (TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌) s

/-- The concrete form of a face. -/
theorem concretize_face {n : ℕ} (w : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n+1⦌)) (i : Fin (n+2)) :
    concretize (SimplicialObject.δ (TopCat.toSSet.obj (TopCat.of X)) i w) =
      (concretize w).comp (coface n i) := by
  ext z
  rw [ContinuousMap.comp_apply, coface_apply]
  exact TopCat.toSSetObjEquivT_δ_apply w i z

/-- The concrete form of a simplex built from a map. -/
theorem concretize_simplexOf {n : ℕ} (c : C(↥(stdSimplex ℝ (Fin (n+1))), X)) :
    concretize (simplexOf n c) = c :=
  toSSetObjEquiv_simplexOf n c

/-- **The simplex filling lemma**: a matching family of faces of `Δ^{k+2}` determines a map on
`Δ^{k+2}` as soon as boundary maps on the cube extend. -/
theorem exists_simplexFiller (k : ℕ) {X : Type} [TopologicalSpace X]
    (hcube : ∀ (f : C(↥(Cube.boundary (Fin (k+2))), X)),
      ∃ g : C(Fin (k+2) → unitInterval, X), ∀ z : ↥(Cube.boundary (Fin (k+2))), g z.1 = f z)
    (x : (i : Fin (k + 3)) → C(↥(stdSimplex ℝ (Fin (k + 2))), X))
    (hx : ∀ (i j : Fin (k + 3)) (hij : i < j),
      (x j).comp (coface k ⟨i.val, by have h : i.val < j.val := hij; omega⟩) =
        (x i).comp (coface k ⟨j.val - 1, by omega⟩)) :
    ∃ y : C(↥(stdSimplex ℝ (Fin (k + 3))), X),
      ∀ i : Fin (k+3), y.comp (coface (k+1) i) = x i := by
  obtain ⟨b, hb⟩ := e0SimplexBdryOfMatching k x hx
  obtain ⟨y, hy⟩ := e0SimplexBdryExtension k hcube b
  refine ⟨y, fun i => ?_⟩
  ext z
  have h1 : y ((faceIncl (k+1) i z).1) = b (faceIncl (k+1) i z) := hy (faceIncl (k+1) i z)
  have h2 : b (faceIncl (k+1) i z) = x i z := by
    have := congrFun (congrArg DFunLike.coe (hb i)) z
    simpa only [ContinuousMap.comp_apply] using this
  change y (coface (k+1) i z) = x i z
  rw [← faceIncl_coe (k+1) i z]
  rw [h1, h2]

end

end Work.Serre


namespace Work.Serre

noncomputable section

open Work.RatHurewicz.Bridge

/-! ## The `succAbove` shuffle -/

/-- The `succAbove` shuffle: inserting `b` then `a` (in the two possible orders) gives the same
map, for `a < b`. -/
theorem succAbove_shuffle {n : ℕ} (a b : Fin (n+2)) (hab : a < b) (l : Fin n) :
    (Fin.succAbove a) (Fin.succAbove ⟨b.val - 1, by omega⟩ l) =
      (Fin.succAbove b) (Fin.succAbove ⟨a.val, by omega⟩ l) := by
  apply Fin.ext
  simp only [val_succAbove]
  split_ifs <;> omega

/-- Cone data in degrees `≤ N`, with the bound as an explicit argument. -/
structure SSetConeDataBdd (K : SSet) (N : ℕ) where
  H : ∀ n : ℕ, n ≤ N → K _⦋n⦌ → K _⦋n+1⦌
  H_congr : ∀ (n : ℕ) (h1 h2 : n ≤ N) (s : K _⦋n⦌), H n h1 s = H n h2 s
  face_cast : ∀ (m : ℕ) (hm : m + 1 ≤ N) (s : K _⦋m+1⦌) (i : Fin (m+2)),
    K.δ (Fin.castSucc i) (H (m+1) hm s) = H m (by omega) (K.δ i s)
  face_last : ∀ (m : ℕ) (hm : m ≤ N) (s : K _⦋m⦌),
    K.δ (Fin.last (m+1)) (H m hm s) = s

end

end Work.Serre


namespace Work.Serre

noncomputable section

open Work.RatHurewicz.Bridge

variable {X : Type} [TopologicalSpace X]

open Work.RatHurewicz.Bridge

/-- Injectivity of the "concretisation" of a simplex. -/
theorem concretize_injective {X : Type} [TopologicalSpace X] {n : ℕ} :
    Function.Injective (concretize (X := X) (n := n)) :=
  fun a b h => (TopCat.toSSetObjEquivT (TopCat.of X) (Opposite.op ⦋n⦌)).injective h

/-- Triviality of `πₙ` at every basepoint, from triviality at one basepoint in a path connected
space. -/
theorem subsingleton_homotopyGroup_of_pathConnected {X : Type} [TopologicalSpace X] {x₀ : X}
    (hpath : PathConnectedSpace X) (n : ℕ)
    (h : Subsingleton (HomotopyGroup (Fin n) X x₀)) :
    ∀ y : X, Subsingleton (HomotopyGroup (Fin n) X y) :=
  fun y => Work.Stems.subsingleton_homotopyGroup_change_basepoint
    (PathConnectedSpace.joined x₀ y).some h

/-- Forget the bound of the bounded cone data: the condition at a degree below the bound is
irrelevant, and above the bound we use the degeneracy. -/
def SSetConeDataBdd.toSSetConeData {K : SSet} {N : ℕ} (D : SSetConeDataBdd K N) :
    SSetConeData K N where
  H := fun n s => if h : n ≤ N then D.H n h s
    else SimplicialObject.σ K (0 : Fin (n+1)) s
  face_cast := by
    intro m hm s i
    have h1 : m + 1 ≤ N := hm
    have h2 : m ≤ N := by omega
    rw [dif_pos h1, dif_pos h2]
    exact D.face_cast m h1 s i
  face_last := by
    intro m hm s
    rw [dif_pos hm]
    exact D.face_last m hm s

end

end Work.Serre
