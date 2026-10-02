import Submission.Work.Stems.Hur2b.PsiCancel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The gluing of the six filled faces of a 3-cube along `∂I³`

Let `τ : I³ → X`.  On the face `F_{i,b} = {z : z_i = b}` of `∂I³` put the filling
`Ψ(τ ∘ faceCM i b) : I² → X`.  Each filling is `x₀` on `∂I²`, and a point of `∂I³` lying on two
faces has (in the 2-cube coordinates of either face) a coordinate in `{0,1}`, hence is mapped to
`x₀` by both.  So the six fillings glue into a single continuous map `gluing : ∂I³ → X`
(Hutchings' `f` in the proof of `(2.5)`).

The file records: the gluing is well defined, continuous, and `x₀` on the 1-skeleton of the cube.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- The two face values `0`, `1`, as an element of `Fin 2`. -/
def bval : Fin 2 → unitInterval := ![0, 1]

@[simp] theorem bval_zero : bval 0 = 0 := rfl
@[simp] theorem bval_one : bval 1 = 1 := rfl

theorem bval_injective : Function.Injective bval := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all

/-- The set of points of the cube whose `i`-th coordinate is the face value `b`. -/
def faceSet3 (i : Fin 3) (b : Fin 2) : Set (IC 3) := {z | z i = bval b}

/-- The 2-cube coordinates of a point of the cube relative to the coordinate `i`. -/
def coordOf (i : Fin 3) (z : IC 3) : IC 2 := fun j => z (i.succAbove j)

theorem faceFun_coordOf {z : IC 3} {i : Fin 3} {b : Fin 2} (h : z i = bval b) :
    faceFun i (bval b) (coordOf i z) = z := by
  rw [show coordOf i z = fun j => z (i.succAbove j) from rfl]
  funext k
  rw [faceFun, Fin.succAbove_cases_eq_insertNth]
  rcases Fin.eq_self_or_eq_succAbove i k with hk | ⟨j, hj⟩
  · subst hk; rw [Fin.insertNth_apply_same]; exact h.symm
  · subst hj; rw [Fin.insertNth_apply_succAbove]

theorem faceSet3_subset_boundary (i : Fin 3) (b : Fin 2) :
    faceSet3 i b ⊆ Cube.boundary (Fin 3) := by
  intro z hz
  refine ⟨i, ?_⟩
  rw [hz]; fin_cases b <;> simp [bval]

/-- If two distinct coordinates of `z` are frozen at face values, then the 2-cube coordinates of
`z` relative to the first are those of a *boundary* point of the square. -/
theorem coordOf_mem_boundary {z : IC 3} {i i' : Fin 3} {b b' : Fin 2}
    (h : z i = bval b) (h' : z i' = bval b') (hii : i ≠ i') :
    coordOf i z ∈ Cube.boundary (Fin 2) := by
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hii)
  refine ⟨j, ?_⟩
  show z (i.succAbove j) = 0 ∨ z (i.succAbove j) = 1
  rw [hj, h']
  fin_cases b' <;> simp [bval]

/-- **On the boundary of the square the filling is `x₀`.** -/
theorem PsiCube_mem_boundary' (x₀ : X) {c : C(IC 2, X)} {t : IC 2}
    (ht : t ∈ Cube.boundary (Fin 2)) : PsiCube x₀ c t = x₀ := PsiCube_mem_boundary ht

theorem PsiCube_coordOf_eq_x₀ (x₀ : X) (τ : C(IC 3, X)) {z : IC 3} {i i' : Fin 3} {b b' : Fin 2}
    (h : z i = bval b) (h' : z i' = bval b') (hii : i ≠ i') :
    PsiCube x₀ (τ.comp (faceCM i (bval b))) (coordOf i z) = x₀ :=
  PsiCube_mem_boundary' x₀ (coordOf_mem_boundary h h' hii)

/-! ## Selecting a face -/

theorem exists_face (z : IC 3) (hz : z ∈ Cube.boundary (Fin 3)) :
    ∃ (i : Fin 3) (b : Fin 2), z i = bval b := by
  obtain ⟨i, hi | hi⟩ := hz
  · exact ⟨i, 0, by rw [hi, bval_zero]⟩
  · exact ⟨i, 1, by rw [hi, bval_one]⟩

/-- A face of the cube containing `z`. -/
def whichFst (z : IC 3) (hz : z ∈ Cube.boundary (Fin 3)) : Fin 3 :=
  Classical.choose (exists_face z hz)

def whichSnd (z : IC 3) (hz : z ∈ Cube.boundary (Fin 3)) : Fin 2 :=
  Classical.choose (Classical.choose_spec (exists_face z hz))

theorem whichFace_spec (z : IC 3) (hz : z ∈ Cube.boundary (Fin 3)) :
    z (whichFst z hz) = bval (whichSnd z hz) :=
  Classical.choose_spec (Classical.choose_spec (exists_face z hz))

/-- The value of the gluing on `∂I³`: fill the selected face. -/
def gluingFun (x₀ : X) (τ : C(IC 3, X)) (z : IC 3) (hz : z ∈ Cube.boundary (Fin 3)) : X :=
  PsiCube x₀ (τ.comp (faceCM (whichFst z hz) (bval (whichSnd z hz)))) (coordOf (whichFst z hz) z)

/-- **On a face of the cube the gluing is the filling of that face.** -/
theorem gluingFun_eq_of_mem (x₀ : X) (τ : C(IC 3, X)) {z : IC 3}
    (hz : z ∈ Cube.boundary (Fin 3)) {i : Fin 3} {b : Fin 2} (h : z ∈ faceSet3 i b) :
    gluingFun x₀ τ z hz = PsiCube x₀ (τ.comp (faceCM i (bval b))) (coordOf i z) := by
  unfold gluingFun
  by_cases hcase : whichFst z hz = i ∧ whichSnd z hz = b
  · obtain ⟨h1, h2⟩ := hcase
    rw [h1, h2]
  · have hne : whichFst z hz ≠ i := by
      intro heq
      exact hcase ⟨heq, bval_injective (by rw [← whichFace_spec z hz, heq]; exact h)⟩
    rw [PsiCube_coordOf_eq_x₀ x₀ τ (whichFace_spec z hz) h hne,
      PsiCube_coordOf_eq_x₀ x₀ τ h (whichFace_spec z hz) hne.symm]


/-! ## Continuity of the gluing -/

/-- The boundary of the 3-cube as a topological space. -/
abbrev Bdy3 : Type := {z : IC 3 // z ∈ Cube.boundary (Fin 3)}

theorem isClosed_faceSet3 (i : Fin 3) (b : Fin 2) : IsClosed (faceSet3 i b) := by
  have h : faceSet3 i b = (fun z : IC 3 => z i) ⁻¹' ({bval b} : Set unitInterval) := rfl
  rw [h]
  exact isClosed_singleton.preimage (continuous_apply i)

/-- The `(i,b)`-face as a subset of `∂I³`. -/
def faceSub (i : Fin 3) (b : Fin 2) : Set Bdy3 := {p | p.1 ∈ faceSet3 i b}

theorem isClosed_faceSub (i : Fin 3) (b : Fin 2) : IsClosed (faceSub i b) :=
  (isClosed_faceSet3 i b).preimage continuous_subtype_val

/-- The face inclusion of the `(i,b)`-face of `∂I³`, as a map `I² → ∂I³`. -/
def faceIncl (i : Fin 3) (b : Fin 2) : C(IC 2, Bdy3) where
  toFun t := ⟨faceFun i (bval b) t, ⟨i, by
    rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]
    fin_cases b <;> simp [bval]⟩⟩
  continuous_toFun := Continuous.subtype_mk (faceCM i (bval b)).continuous _

/-- **The gluing of the six filled faces of a 3-cube.** -/
def gluingMap (x₀ : X) (τ : C(IC 3, X)) : C(Bdy3, X) where
  toFun p := gluingFun x₀ τ p.1 p.2
  continuous_toFun := by
    have hcont : ∀ (i : Fin 3) (b : Fin 2),
        ContinuousOn (fun p : Bdy3 => gluingFun x₀ τ p.1 p.2) (faceSub i b) := by
      intro i b
      refine ((PsiCube x₀ (τ.comp (faceCM i (bval b)))).continuous.comp
        (continuous_pi fun j => (continuous_apply (i.succAbove j)).comp
          continuous_subtype_val)).continuousOn.congr ?_
      intro p hp
      exact gluingFun_eq_of_mem x₀ τ p.2 hp
    rw [← continuousOn_univ]
    rw [show (Set.univ : Set Bdy3) = faceSub 0 0 ∪ (faceSub 0 1 ∪ (faceSub 1 0
          ∪ (faceSub 1 1 ∪ (faceSub 2 0 ∪ faceSub 2 1)))) from by
      ext p
      constructor
      · intro _
        obtain ⟨i, b, hb⟩ := exists_face p.1 p.2
        fin_cases i <;> fin_cases b <;> simp_all [faceSub, faceSet3]
      · intro _; trivial]
    rw [continuousOn_union_iff_of_isClosed (isClosed_faceSub 0 0)
      ((isClosed_faceSub 0 1).union ((isClosed_faceSub 1 0).union
        ((isClosed_faceSub 1 1).union ((isClosed_faceSub 2 0).union (isClosed_faceSub 2 1)))))]
    refine ⟨hcont 0 0, ?_⟩
    rw [continuousOn_union_iff_of_isClosed (isClosed_faceSub 0 1)
      ((isClosed_faceSub 1 0).union ((isClosed_faceSub 1 1).union
        ((isClosed_faceSub 2 0).union (isClosed_faceSub 2 1))))]
    refine ⟨hcont 0 1, ?_⟩
    rw [continuousOn_union_iff_of_isClosed (isClosed_faceSub 1 0)
      ((isClosed_faceSub 1 1).union ((isClosed_faceSub 2 0).union (isClosed_faceSub 2 1)))]
    refine ⟨hcont 1 0, ?_⟩
    rw [continuousOn_union_iff_of_isClosed (isClosed_faceSub 1 1)
      ((isClosed_faceSub 2 0).union (isClosed_faceSub 2 1))]
    exact ⟨hcont 1 1, (continuousOn_union_iff_of_isClosed (isClosed_faceSub 2 0)
      (isClosed_faceSub 2 1)).mpr ⟨hcont 2 0, hcont 2 1⟩⟩

@[simp] theorem gluingMap_apply (x₀ : X) (τ : C(IC 3, X)) (p : Bdy3) :
    gluingMap x₀ τ p = gluingFun x₀ τ p.1 p.2 := rfl

/-- **On a face the gluing is the filling of that face.** -/
theorem gluingMap_eq_of_mem (x₀ : X) (τ : C(IC 3, X)) (p : Bdy3) {i : Fin 3} {b : Fin 2}
    (h : p.1 ∈ faceSet3 i b) :
    gluingMap x₀ τ p = PsiCube x₀ (τ.comp (faceCM i (bval b))) (coordOf i p.1) :=
  gluingFun_eq_of_mem x₀ τ p.2 h

/-- **The gluing restricted to a face is the filling of that face.** -/
theorem gluingMap_comp_faceIncl (x₀ : X) (τ : C(IC 3, X)) (i : Fin 3) (b : Fin 2) :
    (gluingMap x₀ τ).comp (faceIncl i b) = PsiCube x₀ (τ.comp (faceCM i (bval b))) := by
  ext t
  have hmem : ((faceIncl i b) t).1 ∈ faceSet3 i b := by
    show faceFun i (bval b) t i = bval b
    rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]
  show gluingFun x₀ τ ((faceIncl i b) t).1 ((faceIncl i b) t).2
    = (PsiCube x₀ (τ.comp (faceCM i (bval b)))) t
  rw [gluingFun_eq_of_mem x₀ τ ((faceIncl i b) t).2 hmem]
  have hcoord : coordOf i ((faceIncl i b) t).1 = t := by
    show (fun j => faceFun i (bval b) t (i.succAbove j)) = t
    funext j
    rw [faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]
  rw [hcoord]

/-- **The gluing is `x₀` on the 1-skeleton of the cube.** -/
theorem gluingMap_eq_x₀_of_mem_two (x₀ : X) (τ : C(IC 3, X)) {p : Bdy3} {i i' : Fin 3}
    {b b' : Fin 2} (h : p.1 ∈ faceSet3 i b) (h' : p.1 ∈ faceSet3 i' b') (hii : i ≠ i') :
    gluingMap x₀ τ p = x₀ := by
  rw [gluingMap_eq_of_mem x₀ τ p h]
  exact PsiCube_coordOf_eq_x₀ x₀ τ h h' hii

end

end Work.Stems.Hur2b
