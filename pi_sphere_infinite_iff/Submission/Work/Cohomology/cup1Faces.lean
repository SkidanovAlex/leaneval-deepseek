import Mathlib
import Submission.Work.Cohomology.cup1Shuffle

/-!
# Faces of the auxiliary simplices

The faces of the `(n+1)`-simplices `Wmap` and of the `(m+1)`-simplices `Qmap` that occur in the
cup-1 computation, identified with the maps `Amap`, `Ymap`, `frontIncl`, `backIncl`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {R : Type} [CommRing R] {X : SSet}

/-- Top face of `Wmap`. -/
lemma Wmap_face_top (n m s : ℕ) (hs : s + 1 ≤ m) :
    SimplexCategory.δ (⟨n+1, by omega⟩ : Fin (n+2)) ≫ Wmap n m s hs
      = Amap n m s (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, CategoryTheory.comp_apply, SimplexCategory.coe_δ,
    Wmap_val, Amap_val, succAbove_val_if', Fin.val_zero, Fin.val_mk]
  split_ifs <;> omega

/-- `0`-th face of `Wmap`. -/
lemma Wmap_face_zero (n m s : ℕ) (hs : s + 1 ≤ m) :
    SimplexCategory.δ (0 : Fin (n+2)) ≫ Wmap n m s hs = Amap n m (s+1) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, CategoryTheory.comp_apply, SimplexCategory.coe_δ,
    Wmap_val, Amap_val, succAbove_val_if', Fin.val_zero, Fin.val_mk]
  split_ifs <;> omega

/-- `0`-th face of `Qmap 0` is the back inclusion. -/
lemma Qmap_face_zero (n m : ℕ) :
    SimplexCategory.δ (0 : Fin (m+2)) ≫ Qmap n m 0 (by omega) = backIncl n m := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, CategoryTheory.comp_apply, SimplexCategory.coe_δ,
    Qmap_val_if, hom_backIncl_val, succAbove_val_if', Fin.val_zero]
  split_ifs <;> omega

/-- Top face of `Qmap m` is the front inclusion. -/
lemma Qmap_face_top (n m : ℕ) :
    SimplexCategory.δ (⟨m+1, by omega⟩ : Fin (m+2)) ≫ Qmap n m m (by omega)
      = frontIncl m (n+m) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, CategoryTheory.comp_apply, SimplexCategory.coe_δ,
    Qmap_val_if, hom_frontIncl_val, succAbove_val_if', Fin.val_mk]
  split_ifs <;> omega

/-- The `(s+1)`-st face of `Qmap s` is `Ymap s`. -/
lemma Qmap_face_Y (n m s : ℕ) (hs : s + 1 ≤ m) :
    SimplexCategory.δ (⟨s+1, by omega⟩ : Fin (m+2)) ≫ Qmap n m s (by omega)
      = Ymap n m s hs := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, CategoryTheory.comp_apply, SimplexCategory.coe_δ,
    Qmap_val_if, Ymap_val_if, succAbove_val_if', Fin.val_mk]
  split_ifs <;> omega

/-- The `(s+1)`-st face of `Qmap (s+1)` is `Ymap s`. -/
lemma Qmap_face_Y' (n m s : ℕ) (hs : s + 1 ≤ m) :
    SimplexCategory.δ (⟨s+1, by omega⟩ : Fin (m+2)) ≫ Qmap n m (s+1) (by omega)
      = Ymap n m s hs := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, CategoryTheory.comp_apply, SimplexCategory.coe_δ,
    Qmap_val_if, Ymap_val_if, succAbove_val_if', Fin.val_mk]
  split_ifs <;> omega

/-! ## The face identities at the level of simplices -/

section Faces

variable {n m : ℕ}

lemma mop {a b c : ℕ} (φ : ⦋a⦌ ⟶ ⦋b⦌) (ψ : ⦋c⦌ ⟶ ⦋a⦌) (x : X _⦋b⦌) :
    X.map ψ.op (X.map φ.op x) = X.map (ψ ≫ φ).op x :=
  map_op_comp φ ψ x

/-- Regime `k ≤ s`. -/
lemma face_F_le (σ : X _⦋n+m⦌) (k s : ℕ) (hk : k ≤ s) (hs : s < m) :
    X.map (Fface n m s (by omega)).op (X.map (Delmap n m k (by omega)).op σ)
      = X.map (Amap n m (s+1) (by omega)).op σ := by
  rw [mop (Delmap n m k (by omega)) (Fface n m s (by omega)) σ, Fface_Del_le n m k s hk (by omega)]

/-- Regime `k ≤ s` for the back face. -/
lemma face_G_le (σ : X _⦋n+m⦌) (k s : ℕ) (hk : k ≤ s) (hs : s < m) :
    X.map (Gface n m s (by omega)).op (X.map (Delmap n m k (by omega)).op σ)
      = X.map ((SimplexCategory.δ (⟨k, by omega⟩ : Fin (m+2))) ≫ Qmap n m (s+1) (by omega)).op σ := by
  rw [mop (Delmap n m k (by omega)) (Gface n m s (by omega)) σ, Gface_Del_le n m k s hk (by omega)]

/-- Regime `s < k ≤ s+n`. -/
lemma face_F_mid (σ : X _⦋n+m⦌) (k s : ℕ) (hk1 : s + 1 ≤ k) (hk2 : k ≤ s + n) (hs : s < m) :
    X.map (Fface n m s (by omega)).op (X.map (Delmap n m k (by omega)).op σ)
      = X.map ((SimplexCategory.δ (⟨k - s, by omega⟩ : Fin (n+2))) ≫ Wmap n m s (by omega)).op σ := by
  rw [mop (Delmap n m k (by omega)) (Fface n m s (by omega)) σ, Fface_Del_mid n m k s hk1 hk2 (by omega)]

/-- Regime `s < k ≤ s+n` for the back face. -/
lemma face_G_mid (σ : X _⦋n+m⦌) (k s : ℕ) (hk1 : s + 1 ≤ k) (hk2 : k ≤ s + n) (hs : s < m) :
    X.map (Gface n m s (by omega)).op (X.map (Delmap n m k (by omega)).op σ)
      = X.map (Ymap n m s (by omega)).op σ := by
  rw [mop (Delmap n m k (by omega)) (Gface n m s (by omega)) σ, Gface_Del_mid n m k s hk1 hk2 (by omega)]

/-- Regime `s+n < k`. -/
lemma face_F_gt (σ : X _⦋n+m⦌) (k s : ℕ) (hk : s + n + 1 ≤ k) (hs : s < m) :
    X.map (Fface n m s (by omega)).op (X.map (Delmap n m k (by omega)).op σ)
      = X.map (Amap n m s (by omega)).op σ := by
  rw [mop (Delmap n m k (by omega)) (Fface n m s (by omega)) σ, Fface_Del_gt n m k s hk (by omega)]

/-- Regime `s+n < k` for the back face. -/
lemma face_G_gt (σ : X _⦋n+m⦌) (k s : ℕ) (hk1 : s + n + 1 ≤ k) (hk2 : k ≤ n + m) (hs : s < m) :
    X.map (Gface n m s (by omega)).op (X.map (Delmap n m k (by omega)).op σ)
      = X.map ((SimplexCategory.δ (⟨k - n + 1, by omega⟩ : Fin (m+2))) ≫ Qmap n m s (by omega)).op σ := by
  rw [mop (Delmap n m k (by omega)) (Gface n m s (by omega)) σ, Gface_Del_gt n m k s hk1 hk2 (by omega)]

/-- `X.δ 0` of the `(n+1)`-simplex `Wmap s` is the `(s+1)`-st `n`-face. -/
lemma Wcomp_zero (σ : X _⦋n+m⦌) (s : ℕ) (hs : s < m) :
    X.map ((SimplexCategory.δ (0 : Fin (n+2))) ≫ Wmap n m s (by omega)).op σ
      = X.map (Amap n m (s+1) (by omega)).op σ := by
  rw [Wmap_face_zero n m s (by omega)]

/-- `X.δ ⟨n+1⟩` of the `(n+1)`-simplex `Wmap s` is the `s`-th `n`-face. -/
lemma Wcomp_top (σ : X _⦋n+m⦌) (s : ℕ) (hs : s < m) :
    X.map ((SimplexCategory.δ (⟨n+1, by omega⟩ : Fin (n+2))) ≫ Wmap n m s (by omega)).op σ
      = X.map (Amap n m s (by omega)).op σ := by
  rw [Wmap_face_top n m s (by omega)]

/-- The `(s+1)`-st face of `Qmap s` is `Ymap s`. -/
lemma Qcomp_Y (σ : X _⦋n+m⦌) (s : ℕ) (hs : s < m) :
    X.map ((SimplexCategory.δ (⟨s+1, by omega⟩ : Fin (m+2))) ≫ Qmap n m s (by omega)).op σ
      = X.map (Ymap n m s (by omega)).op σ := by
  rw [Qmap_face_Y n m s (by omega)]

/-- The `(s+1)`-st face of `Qmap (s+1)` is `Ymap s`. -/
lemma Qcomp_Y' (σ : X _⦋n+m⦌) (s : ℕ) (hs : s < m) :
    X.map ((SimplexCategory.δ (⟨s+1, by omega⟩ : Fin (m+2))) ≫ Qmap n m (s+1) (by omega)).op σ
      = X.map (Ymap n m s (by omega)).op σ := by
  rw [Qmap_face_Y' n m s (by omega)]

/-- The `0`-th face of `Qmap 0` is the back inclusion. -/
lemma Qcomp_zero (σ : X _⦋n+m⦌) :
    X.map ((SimplexCategory.δ (0 : Fin (m+2))) ≫ Qmap n m 0 (by omega)).op σ
      = X.map (backIncl n m).op σ := by
  rw [Qmap_face_zero n m]

/-- The top face of `Qmap m` is the front inclusion. -/
lemma Qcomp_top (σ : X _⦋n+m⦌) :
    X.map ((SimplexCategory.δ (⟨m+1, by omega⟩ : Fin (m+2))) ≫ Qmap n m m (by omega)).op σ
      = X.map (frontIncl m (n+m) (by omega)).op σ := by
  rw [Qmap_face_top n m]

/-! ## Versions with a variable face index -/

lemma Wcomp_zero_of (σ : X _⦋n+m⦌) (s : ℕ) (hs : s < m) (j : Fin (n+2)) (hj : (j:ℕ) = 0) :
    X.map ((SimplexCategory.δ j) ≫ Wmap n m s (by omega)).op σ
      = X.map (Amap n m (s+1) (by omega)).op σ := by
  rw [show SimplexCategory.δ j = SimplexCategory.δ (0 : Fin (n+2)) from
        congrArg SimplexCategory.δ (Fin.ext (by simpa using hj))]
  rw [Wmap_face_zero n m s (by omega)]

lemma Wcomp_top_of (σ : X _⦋n+m⦌) (s : ℕ) (hs : s < m) (j : Fin (n+2)) (hj : (j:ℕ) = n+1) :
    X.map ((SimplexCategory.δ j) ≫ Wmap n m s (by omega)).op σ
      = X.map (Amap n m s (by omega)).op σ := by
  rw [show SimplexCategory.δ j = SimplexCategory.δ (⟨n+1, by omega⟩ : Fin (n+2)) from
        congrArg SimplexCategory.δ (Fin.ext (by simpa [Fin.val_mk] using hj))]
  rw [Wmap_face_top n m s (by omega)]

lemma Qcomp_Y_of (σ : X _⦋n+m⦌) (s : ℕ) (hs : s < m) (j : Fin (m+2)) (hj : (j:ℕ) = s+1) :
    X.map ((SimplexCategory.δ j) ≫ Qmap n m s (by omega)).op σ
      = X.map (Ymap n m s (by omega)).op σ := by
  rw [show SimplexCategory.δ j = SimplexCategory.δ (⟨s+1, by omega⟩ : Fin (m+2)) from
        congrArg SimplexCategory.δ (Fin.ext (by simpa [Fin.val_mk] using hj))]
  rw [Qmap_face_Y n m s (by omega)]

lemma Qcomp_Y'_of (σ : X _⦋n+m⦌) (s : ℕ) (hs : s < m) (j : Fin (m+2)) (hj : (j:ℕ) = s+1) :
    X.map ((SimplexCategory.δ j) ≫ Qmap n m (s+1) (by omega)).op σ
      = X.map (Ymap n m s (by omega)).op σ := by
  rw [show SimplexCategory.δ j = SimplexCategory.δ (⟨s+1, by omega⟩ : Fin (m+2)) from
        congrArg SimplexCategory.δ (Fin.ext (by simpa [Fin.val_mk] using hj))]
  rw [Qmap_face_Y' n m s (by omega)]

lemma Qcomp_zero_of (σ : X _⦋n+m⦌) (j : Fin (m+2)) (hj : (j:ℕ) = 0) :
    X.map ((SimplexCategory.δ j) ≫ Qmap n m 0 (by omega)).op σ
      = X.map (backIncl n m).op σ := by
  rw [show SimplexCategory.δ j = SimplexCategory.δ (0 : Fin (m+2)) from
        congrArg SimplexCategory.δ (Fin.ext (by simpa using hj))]
  rw [Qmap_face_zero n m]

lemma Qcomp_top_of (σ : X _⦋n+m⦌) (j : Fin (m+2)) (hj : (j:ℕ) = m+1) :
    X.map ((SimplexCategory.δ j) ≫ Qmap n m m (by omega)).op σ
      = X.map (frontIncl m (n+m) (by omega)).op σ := by
  rw [show SimplexCategory.δ j = SimplexCategory.δ (⟨m+1, by omega⟩ : Fin (m+2)) from
        congrArg SimplexCategory.δ (Fin.ext (by simpa [Fin.val_mk] using hj))]
  rw [Qmap_face_top n m]

end Faces

end

end Work.Cohomology
