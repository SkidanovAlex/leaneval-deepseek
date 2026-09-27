import Mathlib
import Submission.Work.KT.PatchProjDefs
import Submission.Work.KT.FiberUtil
import Submission.Work.KT.mvLin

/-!
# Auxiliary constructions for `Work.KT.clipP_range`

This file sets up the explicit linear map whose image under `clipP` identifies the patched module
of `γ` with the range of the clutching projection.  The main definition is `clipRangeFun`, which
sends a patched pair `(f, g)` to the `Fin (n+n) → TwoDisk V` vector with first block
`G⁻¹ *ᵥ padVec f 0` and second block `padVec g 0`.
-/

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

/-! ## Elementary block-vector lemmas -/

lemma padVec_add {S : Type} [Ring S] {m : ℕ} (f f' g g' : Fin m → S) :
    padVec (f + f') (g + g') = padVec f g + padVec f' g' := by
  funext j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with i | i <;> simp

lemma padVec_smul {S : Type} [Ring S] {m : ℕ} (c : S) (f g : Fin m → S) :
    padVec (c • f) (c • g) = c • padVec f g := by
  funext j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with i | i <;> simp

lemma padVec_smul_zero {S : Type} [Ring S] {m : ℕ} (c : S) (f : Fin m → S) :
    padVec (c • f) (0 : Fin m → S) = c • padVec f 0 := by
  funext j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with i | i <;> simp

lemma map_padVec_zero {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {m : ℕ}
    (f : Fin m → A) :
    (fun j => φ (padVec f (0 : Fin m → A) j)) = padVec (fun i => φ (f i)) 0 := by
  rw [map_padVec_ringHom]
  congr 1
  funext i
  exact map_zero φ

lemma sndBlk_eq_zero_iff {S : Type} [Ring S] {m : ℕ} (v : Fin (m + m) → S) :
    sndBlk v = 0 ↔ ∀ i : Fin m, v (finSumFinEquiv (Sum.inr i)) = 0 := by
  constructor
  · intro h i
    have := congrFun h i
    simpa [sndBlk] using this
  · intro h
    funext i
    simpa [sndBlk] using h i

/-- A vector fixed by the standard projection is the padding of its first block with `0`. -/
lemma eq_padVec_fstBlk_zero {S : Type} [Ring S] {m : ℕ} {v : Fin (m + m) → S}
    (h : sndBlk v = 0) : v = padVec (fstBlk v) 0 :=
  eq_padVec_of_sndBlk_eq h

lemma mulVec_mulVec_three {S : Type} [Ring S] {m : ℕ} (A B C : Matrix (Fin m) (Fin m) S)
    (v : Fin m → S) : (A * B * C) *ᵥ v = A *ᵥ (B *ᵥ (C *ᵥ v)) :=
  ((Matrix.mulVec_mulVec v (A * B) C).symm).trans ((Matrix.mulVec_mulVec (C *ᵥ v) A B).symm)

/-! ## The compatibility computation -/

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ)
  (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ)

/-- The first block of `diag(γ, γ⁻¹) *ᵥ X` is `γ *ᵥ X` restricted to the first block. -/
lemma fstBlk_diagGlue_mulVec (X : Fin (n + n) → C(Sph V, ℂ)) :
    fstBlk (diagGlue V n γ *ᵥ X) =
      (↑γ : Matrix (Fin n) (Fin n) C(Sph V, ℂ)) *ᵥ fstBlk X := by
  funext i
  rw [fstBlk, diagGlue, blockMulVec_inl]
  rfl

/-- The boundary restriction of `G⁻¹ *ᵥ padVec f 0` only depends on the boundary restriction of
`g`, via the patched equation `ρ f = γ *ᵥ ρ g`. -/
lemma mapMatrix_Ginv_mulVec_padVec (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ)
    (f g : Fin n → C(Ball V, ℂ))
    (hf : (fun i => restRho V (f i)) = (↑γ : Matrix (Fin n) (Fin n) C(Sph V, ℂ)) *ᵥ
          (fun i => restRho V (g i))) :
    RingHom.mapMatrix (restRho V) (↑(G⁻¹) : BallMat V n) *ᵥ
        padVec (fun i => restRho V (f i)) (0 : Fin n → C(Sph V, ℂ)) =
      padVec (fun i => restRho V (g i)) (0 : Fin n → C(Sph V, ℂ)) := by
  have hdg : diagGlue V n γ *ᵥ padVec (fun i => restRho V (g i))
        (0 : Fin n → C(Sph V, ℂ)) =
      padVec (fun i => restRho V (f i)) (0 : Fin n → C(Sph V, ℂ)) := by
    rw [diagGlue, blockMulVec_padVec, hf, Matrix.mulVec_zero]
  rw [← hdg, Matrix.mulVec_mulVec, mapMatrix_Ginv_mul_diagGlue V n γ hG, Matrix.one_mulVec]

/-- The patched module of `γ`. -/
abbrev clipPatched :=
  FiberProd.patched (ρ₁ := restRho V) (ρ₂ := restRho V) (comm_sphereC V) n (↑γ)

/-- Compatibility of the two components of the image vector. -/
lemma clipRangeCompat (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ)
    (z : clipPatched V n γ) (j : Fin (n + n)) :
    restRho V (((↑(G⁻¹) : BallMat V n) *ᵥ padVec z.1.1 (0 : Fin n → C(Ball V, ℂ))) j) =
    restRho V ((padVec z.1.2 (0 : Fin n → C(Ball V, ℂ))) j) := by
  have h := mapMatrix_Ginv_mulVec_padVec V n γ G hG z.1.1 z.1.2 z.2
  calc restRho V (((↑(G⁻¹) : BallMat V n) *ᵥ padVec z.1.1 0) j)
      = ((RingHom.mapMatrix (restRho V) (↑(G⁻¹) : BallMat V n)) *ᵥ
          (fun k => restRho V (padVec z.1.1 0 k))) j := by
          rw [RingHom.map_mulVec]; rfl
    _ = ((RingHom.mapMatrix (restRho V) (↑(G⁻¹) : BallMat V n)) *ᵥ
          padVec (fun i => restRho V (z.1.1 i)) 0) j := by rw [map_padVec_zero]
    _ = (padVec (fun i => restRho V (z.1.2 i)) 0) j := by rw [h]
    _ = restRho V ((padVec z.1.2 0) j) := by rw [← map_padVec_zero (restRho V) z.1.2]

/-- The image vector of the patched pair `z`. -/
def clipRangeFun (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ)
    (z : clipPatched V n γ) : Fin (n + n) → TwoDisk V :=
  fun j => ⟨(((↑(G⁻¹) : BallMat V n) *ᵥ padVec z.1.1 (0 : Fin n → C(Ball V, ℂ))) j,
    (padVec z.1.2 (0 : Fin n → C(Ball V, ℂ))) j), clipRangeCompat V n γ G hG z j⟩

@[simp] lemma clipRangeFun_apply_fst (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ)
    (z : clipPatched V n γ) (j : Fin (n + n)) :
    (clipRangeFun V n γ G hG z j).1.1 =
      ((↑(G⁻¹) : BallMat V n) *ᵥ padVec z.1.1 (0 : Fin n → C(Ball V, ℂ))) j := rfl

@[simp] lemma clipRangeFun_apply_snd (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ)
    (z : clipPatched V n γ) (j : Fin (n + n)) :
    (clipRangeFun V n γ G hG z j).1.2 =
      (padVec z.1.2 (0 : Fin n → C(Ball V, ℂ))) j := rfl

lemma clipRangeFun_add (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ)
    (z z' : clipPatched V n γ) :
    clipRangeFun V n γ G hG (z + z') =
      clipRangeFun V n γ G hG z + clipRangeFun V n γ G hG z' := by
  have hz : (z + z').1.1 = z.1.1 + z'.1.1 := rfl
  have hz2 : (z + z').1.2 = z.1.2 + z'.1.2 := rfl
  funext j
  apply Subtype.ext
  apply Prod.ext
  · show (((↑(G⁻¹) : BallMat V n) *ᵥ padVec (z + z').1.1 0) j) =
      (((↑(G⁻¹) : BallMat V n) *ᵥ padVec z.1.1 0) j +
        ((↑(G⁻¹) : BallMat V n) *ᵥ padVec z'.1.1 0) j)
    rw [hz]
    have h1 : padVec (z.1.1 + z'.1.1) (0 : Fin n → C(Ball V, ℂ)) =
        padVec z.1.1 0 + padVec z'.1.1 0 := by
      rw [← padVec_add]; simp
    rw [h1, Matrix.mulVec_add]
    rfl
  · show (padVec (z + z').1.2 (0 : Fin n → C(Ball V, ℂ))) j =
      ((padVec z.1.2 (0 : Fin n → C(Ball V, ℂ))) j +
        (padVec z'.1.2 (0 : Fin n → C(Ball V, ℂ))) j)
    rw [hz2]
    have h2 : padVec (z.1.2 + z'.1.2) (0 : Fin n → C(Ball V, ℂ)) =
        padVec z.1.2 0 + padVec z'.1.2 0 := by
      rw [← padVec_add]; simp
    rw [h2]
    rfl

lemma clipRangeFun_smul (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ)
    (a : TwoDisk V) (z : clipPatched V n γ) :
    clipRangeFun V n γ G hG (a • z) = a • clipRangeFun V n γ G hG z := by
  have hz : (a • z).1.1 = FiberProd.fstHom a • z.1.1 := rfl
  have hz2 : (a • z).1.2 = FiberProd.sndHom a • z.1.2 := rfl
  funext j
  apply Subtype.ext
  apply Prod.ext
  · show (((↑(G⁻¹) : BallMat V n) *ᵥ padVec (a • z).1.1 0) j) =
      (FiberProd.fstHom a) * (((↑(G⁻¹) : BallMat V n) *ᵥ padVec z.1.1 0) j)
    rw [hz, padVec_smul_zero, Matrix.mulVec_smul]
    rfl
  · show (padVec (a • z).1.2 (0 : Fin n → C(Ball V, ℂ))) j =
      (FiberProd.sndHom a) * ((padVec z.1.2 (0 : Fin n → C(Ball V, ℂ))) j)
    rw [hz2, padVec_smul_zero]
    rfl

/-- The underlying linear map `z ↦ (G⁻¹ *ᵥ padVec f 0, padVec g 0)`. -/
def clipRangeLin (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ) :
    clipPatched V n γ →ₗ[TwoDisk V] (Fin (n + n) → TwoDisk V) where
  toFun := clipRangeFun V n γ G hG
  map_add' := clipRangeFun_add V n γ G hG
  map_smul' := clipRangeFun_smul V n γ G hG

@[simp] lemma clipRangeLin_apply (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ)
    (z : clipPatched V n γ) :
    clipRangeLin V n γ G hG z = clipRangeFun V n γ G hG z := rfl

/-! ## The image lands in the range of `clipP` -/

lemma clipRangeFun_mem_range (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ)
    (z : clipPatched V n γ) :
    clipRangeFun V n γ G hG z ∈ (mvLin (comm_twoDisk V) (clipP V n γ G hG)).range := by
  rw [mem_range_mvLin]
  refine ⟨clipRangeFun V n γ G hG z, ?_⟩
  have hfst : RingHom.mapMatrix (FiberProd.fstHom : TwoDisk V →+* C(Ball V, ℂ))
        (clipP V n γ G hG) =
      (↑(G⁻¹) : BallMat V n) * stdProj (C(Ball V, ℂ)) n * (↑G : BallMat V n) := by
    rw [mapMatrix_clipP_fst, mapMatrix_fstHom_clipZ]
  have hsnd : RingHom.mapMatrix (FiberProd.sndHom : TwoDisk V →+* C(Ball V, ℂ))
        (clipP V n γ G hG) = stdProj (C(Ball V, ℂ)) n := by
    rw [mapMatrix_clipP_snd, mapMatrix_sndHom_clipZ]
  have hW₁ : (fun i => (clipRangeFun V n γ G hG z i).1.1) =
      (↑(G⁻¹) : BallMat V n) *ᵥ padVec z.1.1 (0 : Fin n → C(Ball V, ℂ)) := by
    funext i; rfl
  have hW₂ : (fun i => (clipRangeFun V n γ G hG z i).1.2) =
      padVec z.1.2 (0 : Fin n → C(Ball V, ℂ)) := by
    funext i; rfl
  have hGG : (↑G : BallMat V n) *ᵥ ((↑(G⁻¹) : BallMat V n) *ᵥ
      padVec z.1.1 (0 : Fin n → C(Ball V, ℂ))) = padVec z.1.1 0 := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hZ₁ : stdProj (C(Ball V, ℂ)) n *ᵥ padVec z.1.1 (0 : Fin n → C(Ball V, ℂ)) =
      padVec z.1.1 0 := by
    rw [stdProj_mulVec_eq_self_iff]; intro i; simp
  have hZ₂ : stdProj (C(Ball V, ℂ)) n *ᵥ padVec z.1.2 (0 : Fin n → C(Ball V, ℂ)) =
      padVec z.1.2 0 := by
    rw [stdProj_mulVec_eq_self_iff]; intro i; simp
  funext j
  apply Subtype.ext
  apply Prod.ext
  · have hf := congrFun (map_fstHom_mulVec (ρ₁ := restRho V) (ρ₂ := restRho V)
      (clipP V n γ G hG) (clipRangeFun V n γ G hG z)) j
    simp only [clipRangeFun_apply_fst] at hf
    rw [hf, hfst]
    rw [show (fun i => ((↑(G⁻¹) : BallMat V n) *ᵥ
          padVec z.1.1 (0 : Fin n → C(Ball V, ℂ))) i) =
        (↑(G⁻¹) : BallMat V n) *ᵥ padVec z.1.1 (0 : Fin n → C(Ball V, ℂ)) from rfl]
    rw [mulVec_mulVec_three, hGG, hZ₁]
    rfl
  · have hs := congrFun (map_sndHom_mulVec (ρ₁ := restRho V) (ρ₂ := restRho V)
      (clipP V n γ G hG) (clipRangeFun V n γ G hG z)) j
    simp only [clipRangeFun_apply_snd] at hs
    rw [hs, hsnd]
    rw [show (fun i => (padVec z.1.2 (0 : Fin n → C(Ball V, ℂ))) i) =
        padVec z.1.2 (0 : Fin n → C(Ball V, ℂ)) from rfl]
    rw [hZ₂]
    rfl

end

end Work.KT
