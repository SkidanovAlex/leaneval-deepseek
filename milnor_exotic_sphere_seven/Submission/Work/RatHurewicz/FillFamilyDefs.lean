import Mathlib
import Submission.Work.RatHurewicz.CubicalDefs
import Submission.Work.RatHurewicz.CubeFaceAux
import Submission.Work.ThomBordism.TwoSet.ConeDescent

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the filling family `K` of the cubical Hurewicz construction

This file collects the objects used by `Work.RatHurewicz.fillingFamilyConst`.

* `bface n i b` — the inclusion of the `i`-th face (frozen at the value `cval b ∈ {0,1}`) into
  the boundary subtype `∂I^{n+1}`, as a map `I^n → ↥(Cube.boundary (Fin (n+1)))`.

* `delCM n j` — the "deletion of the coordinate `castSucc j`": if `z` lies on the face
  `{z (castSucc j) = b}` of `I^{n+1}` then `delCM n j z` is the corresponding point of `I^n`.

* `topVal`, `botVal`, `sideVal` — the values which the boundary map of the filling `K n p` must
  take on the top face (`{last n = 1}`, value `p`), the bottom face (`{last n = 0}`, value `x₀`) and
  the side faces (`{castSucc j = b}`, value `K (n-1) (p ∘ face_j b)`).  These are defined as
  *total* functions on `I^{n+1}`; on the face for which they are prescribed they are the correct
  value, and the fact that they agree on overlaps (the "consistency" of the prescribed data) is
  `Work.RatHurewicz.pieceVal_agree`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {n m : ℕ}

/-! ## Faces of the cube boundary -/

theorem mem_cubeBoundary_faceCM {n : ℕ} (i : Fin (n + 1)) {b : unitInterval} (hb : b = 0 ∨ b = 1)
    (u : IC n) : faceCM i b u ∈ Cube.boundary (Fin (n + 1)) :=
  ⟨i, by
    rcases hb with h | h
    · exact Or.inl (by rw [faceCM_eq_insertNth, ← h, Fin.insertNth_apply_same])
    · exact Or.inr (by rw [faceCM_eq_insertNth, ← h, Fin.insertNth_apply_same])⟩

theorem mem_cubeBoundary_faceCM_cval {n : ℕ} (i : Fin (n + 1)) (b : Fin 2) (u : IC n) :
    faceCM i (cval b) u ∈ Cube.boundary (Fin (n + 1)) := by
  refine mem_cubeBoundary_faceCM i ?_ u
  fin_cases b <;> simp

/-- The inclusion of the face `{z i = cval b}` of the boundary `∂I^{n+1}`, as a map out of `I^n`. -/
def bface (n : ℕ) (i : Fin (n + 1)) (b : Fin 2) :
    C(IC n, ↥(Cube.boundary (Fin (n + 1)))) where
  toFun u := ⟨faceCM i (cval b) u, mem_cubeBoundary_faceCM_cval i b u⟩
  continuous_toFun := Continuous.subtype_mk ((faceCM i (cval b)).continuous) _

@[simp] theorem bface_apply (i : Fin (n + 1)) (b : Fin 2) (u : IC n) :
    ((bface n i b u : ↥(Cube.boundary (Fin (n + 1)))) : IC (n + 1)) = faceCM i (cval b) u := rfl

theorem bface_val (i : Fin (n + 1)) (b : Fin 2) :
    (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(Cube.boundary (Fin (n + 1))), IC (n + 1))).comp (bface n i b)
      = faceCM i (cval b) := by
  ext u; simp

/-! ## Deletion of a coordinate -/

/-- Delete the coordinate `castSucc j` of a point of `I^{n+1}`.  On the face
`{z (castSucc j) = b}` this is the inverse of `faceCM (castSucc j) b`. -/
def delCM (n : ℕ) (j : Fin n) : C(IC (n + 1), IC n) where
  toFun z := fun k => z ((Fin.castSucc j).succAbove k)
  continuous_toFun := continuous_pi fun k => continuous_apply _

@[simp] theorem delCM_apply (j : Fin n) (z : IC (n + 1)) (k : Fin n) :
    delCM n j z k = z ((Fin.castSucc j).succAbove k) := rfl

/-- The "space part" of a point of `I^{n+1}` as a continuous map. -/
def initCM (n : ℕ) : C(IC (n + 1), IC n) where
  toFun := initC n
  continuous_toFun := continuous_pi fun k => continuous_apply _

@[simp] theorem initCM_apply (n : ℕ) (z : IC (n + 1)) : initCM n z = initC n z := rfl

/-! ## The prescribed values on the faces -/

/-- The value prescribed on the top face `{last (k+1) = 1}` for the boundary of `K (k+1) p`. -/
def topVal {X : Type} [TopologicalSpace X] {k : ℕ} (p : C(IC (k + 1), X)) (z : IC (k + 2)) : X :=
  p (initC (k + 1) z)

/-- The value prescribed on the bottom face `{last (k+1) = 0}`. -/
def botVal {X : Type} [TopologicalSpace X] {k : ℕ} (x₀ : X) (_ : IC (k + 2)) : X := x₀

/-- The value prescribed on the side face `{castSucc j = b}` for the boundary of `K (k+1) p`,
where `Kp` is the operator at level `k`. -/
def sideVal {X : Type} [TopologicalSpace X] {k : ℕ} (Kp : C(IC k, X) → C(IC (k + 1), X))
    (p : C(IC (k + 1), X)) (j : Fin (k + 1)) (b : Fin 2) (z : IC (k + 2)) : X :=
  (Kp (p.comp (faceCM j (cval b)))) (delCM (k + 1) j z)

theorem continuous_topVal {X : Type} [TopologicalSpace X] {k : ℕ} (p : C(IC (k + 1), X)) :
    Continuous (topVal p) :=
  p.continuous.comp (initCM (k + 1)).continuous

theorem continuous_sideVal {X : Type} [TopologicalSpace X] {k : ℕ}
    (Kp : C(IC k, X) → C(IC (k + 1), X)) (p : C(IC (k + 1), X)) (j : Fin (k + 1)) (b : Fin 2) :
    Continuous (sideVal Kp p j b) :=
  (Kp (p.comp (faceCM j (cval b)))).continuous.comp (delCM (k + 1) j).continuous


/-! ## The pinch geometry of the cube boundary

For `m ≥ 1` we construct a copy of the closed disk `I^m` inside the boundary `∂I^{m+1}`, namely the
complement of the (open) bottom face, and its inverse on that hemisphere:

* `sig` is the `ℓ∞` radial coordinate `max_i |2 u_i - 1|` of a point of `I^m` (`0` at the centre,
  `1` exactly on `∂I^m`), `tau` is the "time" coordinate `min 1 (2 - 2 sig)` and `radialPt` is the
  point on the ray from the centre through `u` at the normalised radius;
* `iotaFun u = (radialPt u, tau u)`: a point of `∂I^{m+1}`.  For `sig u = 1` it is `(u, 0)`, for
  `sig u < 1/2` it is on the top cap `{last = 1}`, and in between it is on the side wall.
  `iota : I^m → ↥(∂I^{m+1})` is the induced map into the boundary subtype.
* `psiFun z = c + (1 - z_last/2) (initC z - c)` (`c` the centre of `I^m`): the inverse of `iota` on
  the hemisphere `{z_last ≠ 0}`; it is defined on all of `I^{m+1}` and is a continuous map
  `psi : I^{m+1} → I^m`, restricted to `psiBd` on the boundary subtype.
-/


/-! ## Round trips between the faces and the deletions -/

theorem initC_faceCM_last (n : ℕ) (b : unitInterval) (u : IC n) :
    initC n (faceCM (Fin.last n) b u) = u := by
  funext k
  rw [initC_apply, faceCM_last, Fin.snoc_castSucc]

theorem delCM_faceCM_castSucc (n : ℕ) (j : Fin n) (b : unitInterval) (u : IC n) :
    delCM n j (faceCM (Fin.castSucc j) b u) = u := by
  funext k
  rw [delCM_apply, faceCM_eq_insertNth, Fin.insertNth_apply_succAbove]

theorem faceCM_delCM_of_apply (n : ℕ) (j : Fin n) {b : unitInterval} (u : IC (n + 1))
    (hu : u (Fin.castSucc j) = b) : faceCM (Fin.castSucc j) b (delCM n j u) = u := by
  rw [← hu, faceCM_eq_insertNth]
  convert insertNth_succAbove_self (Fin.castSucc j) u using 2
  rw [delCM]; rfl

theorem faceCM_last_apply (n : ℕ) {b : unitInterval} (u : IC (n + 1)) (hu : u (Fin.last n) = b) :
    faceCM (Fin.last n) b (initC n u) = u := by
  rw [← hu, faceCM_last]
  funext i
  cases i using Fin.lastCases with
  | last => rw [Fin.snoc_last]
  | cast j => rw [Fin.snoc_castSucc, initC_apply]


/-! ## The uniform deletion of one coordinate -/

/-- Deleting the coordinate `i` from a point of `I^{n+1}` (uniformly in `i`, including the last
coordinate, where it is the "space part" `initC`). -/
def delG (n : ℕ) (i : Fin (n + 1)) : C(IC (n + 1), IC n) where
  toFun z := fun k => z (i.succAbove k)
  continuous_toFun := continuous_pi fun k => continuous_apply _

@[simp] theorem delG_apply (i : Fin (n + 1)) (z : IC (n + 1)) (k : Fin n) :
    delG n i z k = z (i.succAbove k) := rfl

theorem delG_eq_delCM (j : Fin n) (z : IC (n + 1)) : delG n (Fin.castSucc j) z = delCM n j z := by
  funext k
  rw [delG_apply, delCM_apply]

theorem delG_last (z : IC (n + 1)) : delG n (Fin.last n) z = initC n z := by
  funext k
  rw [delG_apply, initC_apply]
  congr 1
  rw [Fin.succAbove]
  rw [if_pos]
  rw [Fin.lt_def, Fin.val_castSucc]
  exact Fin.isLt k

theorem delG_faceCM (i : Fin (n + 1)) {b : unitInterval} (u : IC (n + 1)) (hu : u i = b) :
    faceCM i b (delG n i u) = u := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [delG_eq_delCM]; exact faceCM_delCM_of_apply n j u hu
  · rw [delG_last]; exact faceCM_last_apply n u hu

theorem faceCM_delG (i : Fin (n + 1)) (b : unitInterval) (w : IC n) :
    delG n i (faceCM i b w) = w := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [delG_eq_delCM]; exact delCM_faceCM_castSucc n j b w
  · rw [delG_last, initC_faceCM_last]


/-! ## The prescribed value on one face of the boundary of a filling -/

/-- The value prescribed on the face `{z i = cval b}` of the boundary `∂I^{ℓ+2}` for the filling
`K (ℓ+1) p`: the constant `x₀` on the bottom face, the cube `p` on the top face, and
`K ℓ (p ∘ face_i b)` on the side faces. -/
def pieceVal {X : Type} [TopologicalSpace X] {ℓ : ℕ} (x₀ : X)
    (Kp : C(IC ℓ, X) → C(IC (ℓ + 1), X)) (p : C(IC (ℓ + 1), X))
    (i : Fin (ℓ + 2)) (b : Fin 2) (z : IC (ℓ + 2)) : X :=
  if hi : i = Fin.last (ℓ + 1) then (if b = 1 then p (initC (ℓ + 1) z) else x₀)
  else (Kp (p.comp (faceCM (i.castPred hi) (cval b)))) (delG (ℓ + 1) i z)

theorem pieceVal_last {X : Type} [TopologicalSpace X] {ℓ : ℕ} (x₀ : X)
    (Kp : C(IC ℓ, X) → C(IC (ℓ + 1), X)) (p : C(IC (ℓ + 1), X)) (b : Fin 2)
    (z : IC (ℓ + 2)) :
    pieceVal x₀ Kp p (Fin.last (ℓ + 1)) b z = (if b = 1 then p (initC (ℓ + 1) z) else x₀) := by
  rw [pieceVal, dif_pos rfl]

theorem pieceVal_side {X : Type} [TopologicalSpace X] {ℓ : ℕ} (x₀ : X)
    (Kp : C(IC ℓ, X) → C(IC (ℓ + 1), X)) (p : C(IC (ℓ + 1), X))
    {i : Fin (ℓ + 2)} (hi : i ≠ Fin.last (ℓ + 1)) (b : Fin 2) (z : IC (ℓ + 2)) :
    pieceVal x₀ Kp p i b z
      = (Kp (p.comp (faceCM (i.castPred hi) (cval b)))) (delG (ℓ + 1) i z) := by
  rw [pieceVal, dif_neg hi]

end

end Work.RatHurewicz
