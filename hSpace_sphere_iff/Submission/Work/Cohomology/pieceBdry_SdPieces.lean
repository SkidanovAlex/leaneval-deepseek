/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The barycentric subdivision is a chain map

This file proves `Work.Cohomology.pieceBdry_SdPieces`, the chain-map property
`∂ ∘ Sd = Sd ∘ ∂` of the barycentric subdivision, at the level of the chain-level subdivision
`Submission.Cohomology.SdPieces` of the universal simplex:

`∂ (Sd(Δ^{n+1})) = ∑ᵢ (-1)ⁱ (δᵢ)₊ (Sd(Δⁿ))`.

The right-hand side is the `n`-th **simplicial boundary operator** `B n n` on chains of
`n`-pieces: the alternating sum of the pushforwards along the coface inclusions
`Δⁿ → Δ^{n+1}`.  Writing `Sd(Δ^{n+1}) = cone_β (B n n (Sd Δⁿ))` (the definition of `SdPieces`),
the proof is the classical induction on `n`, via the cone identity
`∂ (b · θ) = θ - b · (∂θ)` (`Submission.Cohomology.pieceBdry_conePieces`, and its bottom-dimensional
special case proved here):
* `∂ (Sd Δ^{n+1}) = B n n (Sd Δⁿ) - cone_β (∂ (B n n (Sd Δⁿ)))`, and
* `∂ (B n n (Sd Δⁿ)) = B n (n-1) (∂ (Sd Δⁿ)) = B n (n-1) (B (n-1) (n-1) (Sd Δ^{n-1})) = 0`
  by the induction hypothesis and `B² = 0` (`SdAux.B_comp`).
* For `n = 0` the correction term `cone_β (∂ θ)` is not available; instead the bottom-dimensional
  cone identity produces `single (const β) (aug θ)`, which vanishes because `aug (B 0 0 θ) = 0`
  (the alternating sum of two equal terms).

The crucial point `B² = 0` is obtained not by a new combinatorial argument but from Mathlib's
`AlternatingCofaceMapComplex.d_squared` applied to the **cosimplicial object**
`n ↦ (chains of `m`-pieces of `Δⁿ`)` built here (`SdAux.pieceCo`), whose coface maps are the
pushforwards along the face inclusions `Δⁿ → Δ^{n+1}`.
-/
import Mathlib
import Submission.Work.Cohomology.SubdivisionChain

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

namespace Work.Cohomology

noncomputable section

/-! Auxiliary material for `pieceBdry_SdPieces`. -/
namespace SdAux

open Submission.Cohomology

/-! ## The cosimplicial object of chains of pieces -/

lemma pushPieces_id_eq (N m : ℕ) :
    pushPieces (id : TSimplex N → TSimplex N) m = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single q r => simp [pushPieces_single]

lemma pushPieces_comp_lm {n₁ n₂ n₃ : ℕ} (f : TSimplex n₂ → TSimplex n₃)
    (g : TSimplex n₁ → TSimplex n₂) (m : ℕ) :
    (pushPieces f m).comp (pushPieces g m) = pushPieces (f ∘ g) m := by
  apply LinearMap.ext; intro x
  rw [LinearMap.comp_apply, pushPieces_comp]

/-- The cosimplicial object `n ↦` (chains of `m`-pieces of `Δⁿ`): the structure map of a
simplicial operator `φ` pushes the vertices of a piece forward along `φ`. -/
def pieceCo (m : ℕ) : CosimplicialObject (ModuleCat ℚ) where
  obj n := ModuleCat.of ℚ (Piece n.len m →₀ ℚ)
  map {a b} f := ModuleCat.ofHom (pushPieces (stdSimplex.map ⇑(f.toOrderHom)) m)
  map_id a := by
    rw [← ModuleCat.ofHom_id]
    congr 1
    have h1 : ⇑(SimplexCategory.Hom.toOrderHom (𝟙 a))
        = (id : Fin (a.len+1) → Fin (a.len+1)) := by
      rw [SimplexCategory.id_toOrderHom]; rfl
    rw [h1]
    have h2 : (stdSimplex.map (S := ℝ) (id : Fin (a.len+1) → Fin (a.len+1)))
        = (id : TSimplex a.len → TSimplex a.len) := by
      funext x
      exact stdSimplex.map_id_apply (S := ℝ) x
    rw [h2, pushPieces_id_eq]
  map_comp {a b c} f g := by
    rw [← ModuleCat.ofHom_comp]
    congr 1
    have hfun : (stdSimplex.map (S := ℝ) ⇑(SimplexCategory.Hom.toOrderHom (f ≫ g)))
        = (stdSimplex.map (S := ℝ) ⇑(SimplexCategory.Hom.toOrderHom g)) ∘
          (stdSimplex.map (S := ℝ) ⇑(SimplexCategory.Hom.toOrderHom f)) := by
      funext x
      have hcomp : ⇑(SimplexCategory.Hom.toOrderHom (f ≫ g))
          = ⇑(SimplexCategory.Hom.toOrderHom g) ∘ ⇑(SimplexCategory.Hom.toOrderHom f) := by
        rw [SimplexCategory.comp_toOrderHom]; rfl
      rw [Function.comp_apply, hcomp, stdSimplex.map_comp_apply (S := ℝ)]
    rw [hfun, pushPieces_comp_lm]

/-- The coface maps of `pieceCo` are the pushforwards along the face inclusions. -/
lemma pieceCo_δ (m : ℕ) {n : ℕ} (i : Fin (n+2)) :
    (pieceCo m).δ i = ModuleCat.ofHom (pushPieces (faceIncl i) m) := by
  apply ModuleCat.hom_ext
  change pushPieces (stdSimplex.map ⇑(SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i))) m
    = pushPieces (faceIncl i) m
  congr 1

lemma pieceCo_δ_hom (m : ℕ) {n : ℕ} (i : Fin (n+2)) :
    ((pieceCo m).δ i).hom = pushPieces (faceIncl i) m :=
  congrArg ModuleCat.Hom.hom (pieceCo_δ m i)

/-- The alternating coface differential of `pieceCo` is `B`: the alternating sum of the
pushforwards along the coface inclusions. -/
lemma pieceCo_objD_hom (m n : ℕ) :
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (pieceCo m) n).hom
      = ∑ i : Fin (n+2), (-1 : ℚ) ^ (i : ℕ) • pushPieces (faceIncl i) m := by
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  simp only [pieceCo_δ]
  simp only [ModuleCat.hom_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ModuleCat.Hom.hom ((-1:ℤ)^(i:ℕ) • (ModuleCat.ofHom (pushPieces (faceIncl i) m) :
      ModuleCat.of ℚ (Piece n m →₀ ℚ) ⟶ ModuleCat.of ℚ (Piece (n+1) m →₀ ℚ)))
    = (-1:ℚ)^(i:ℕ) • pushPieces (faceIncl i) m
  rw [ModuleCat.hom_zsmul, ModuleCat.hom_ofHom]
  rw [← Int.cast_smul_eq_zsmul (R := ℚ) ((-1:ℤ) ^ (i:ℕ)) (pushPieces (faceIncl i) m)]
  congr 1
  push_cast
  ring

/-- The `n`-th simplicial boundary operator on chains of pieces: `∑ᵢ (-1)ⁱ (δᵢ)₊`. -/
def B (m n : ℕ) : (Piece n m →₀ ℚ) →ₗ[ℚ] (Piece (n+1) m →₀ ℚ) :=
  ∑ i : Fin (n+2), (-1 : ℚ) ^ (i : ℕ) • pushPieces (faceIncl i) m

lemma B_apply (m n : ℕ) (x : Piece n m →₀ ℚ) :
    B m n x = ∑ i : Fin (n+2), (-1 : ℚ) ^ (i : ℕ) • pushPieces (faceIncl i) m x := by
  simp only [B, LinearMap.sum_apply, LinearMap.smul_apply]

lemma B_eq_objD (m n : ℕ) :
    B m n = (AlgebraicTopology.AlternatingCofaceMapComplex.objD (pieceCo m) n).hom := by
  rw [pieceCo_objD_hom m n]
  rfl

/-- **`B² = 0`**: the alternating sum of the pushforwards along the coface inclusions is a
differential.  This is Mathlib's `AlternatingCofaceMapComplex.d_squared` for `pieceCo`. -/
lemma B_comp (m n : ℕ) : (B m (n+1)).comp (B m n) = 0 := by
  rw [B_eq_objD m (n+1), B_eq_objD m n]
  have h := AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (pieceCo m) n
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  exact h2

/-! ## The boundary of a cone, in degree `0` -/

/-- The augmentation `(Piece N 0 →₀ ℚ) → ℚ`, summing the coefficients. -/
def aug (N : ℕ) : (Piece N 0 →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ (fun _ : Piece N 0 => (1 : ℚ))

lemma aug_single (N : ℕ) (q : Piece N 0) (r : ℚ) : aug N (Finsupp.single q r) = r := by
  rw [aug, Finsupp.linearCombination_single]; simp

lemma aug_pushPieces (N N' : ℕ) (f : TSimplex N → TSimplex N') (x : Piece N 0 →₀ ℚ) :
    aug N' (pushPieces f 0 x) = aug N x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single q r => simp only [pushPieces_single, aug_single]

lemma facePiece_conePiece_zero_dim {N : ℕ} (b : TSimplex N) (q : Piece N 0) :
    facePiece (conePiece b q) (0 : Fin 2) = q := by
  funext t
  show (conePiece b q) (Fin.succAbove (0 : Fin 2) t) = q t
  fin_cases t
  exact conePiece_succ b q 0

lemma facePiece_conePiece_one_dim {N : ℕ} (b : TSimplex N) (q : Piece N 0) :
    facePiece (conePiece b q) (1 : Fin 2) = (fun _ : Fin 1 => b) := by
  funext t
  show (conePiece b q) (Fin.succAbove (1 : Fin 2) t) = b
  fin_cases t
  exact conePiece_zero b q

/-- The cone identity in the bottom dimension (where `∂θ` is not available and the cone over
it is replaced by the augmentation of `θ`). -/
lemma pieceBdry_zero_cone (N : ℕ) (b : TSimplex N) (γ : Piece N 0 →₀ ℚ) :
    pieceBdry 0 (conePieces b 0 γ)
      = γ - Finsupp.single (fun _ : Fin 1 => b) (aug N γ) := by
  induction γ using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
      simp only [map_add, hu, hv, Finsupp.single_add]
      abel
  | single q r =>
      rw [conePieces_single, pieceBdry_single, Fin.sum_univ_two,
        facePiece_conePiece_zero_dim, facePiece_conePiece_one_dim, aug_single]
      simp [Finsupp.single_neg, sub_eq_add_neg]

/-! ## The chain map property -/

/-- `B` commutes with the piece boundary: `∂ (B x) = B (∂ x)`. -/
lemma pieceBdry_B (m N : ℕ) (x : Piece N (m+1) →₀ ℚ) :
    pieceBdry m (B (m+1) N x) = B m N (pieceBdry m x) := by
  rw [B_apply (m+1) N x, map_sum, B_apply m N (pieceBdry m x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, pieceBdry_pushPieces]

/-- `Sd(Δ^{k+1}) = cone_{barycentre}(B (Sd Δ^k))`, from the definition of `SdPieces` and the
linearity of the cone operator. -/
lemma SdPieces_succ (k : ℕ) :
    SdPieces (k+1) = conePieces (bary (k+1)) k (B k k (SdPieces k)) := by
  have h : SdPieces (k+1) = ∑ i : Fin (k+2), (-1 : ℚ) ^ (i : ℕ) •
      conePieces (bary (k+1)) k (pushPieces (faceIncl i) k (SdPieces k)) := rfl
  rw [h, B_apply k k (SdPieces k), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]

/-- In dimension `0` the augmentation kills `B`, because `B` is the difference of two pushes
and the augmentation is invariant under pushforward. -/
lemma aug_B_zero (x : Piece 0 0 →₀ ℚ) : aug 1 (B 0 0 x) = 0 := by
  rw [B_apply 0 0 x]
  have key : aug 1 (∑ i : Fin 2, (-1 : ℚ) ^ (i:ℕ) • pushPieces (faceIncl i) 0 x)
      = ∑ i : Fin 2, (-1 : ℚ) ^ (i:ℕ) * aug 0 x := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, aug_pushPieces 0 1 (faceIncl i) x]
  rw [key, ← Finset.sum_mul, Fin.sum_univ_two]
  norm_num

/-- The chain map property `∂ (Sd Δ^{n+1}) = B (Sd Δⁿ)`, in the form useful for the
induction. -/
lemma pieceBdry_SdPieces_aux (n : ℕ) :
    pieceBdry n (SdPieces (n+1)) = B n n (SdPieces n) := by
  induction n with
  | zero =>
      rw [SdPieces_succ 0, pieceBdry_zero_cone, aug_B_zero (SdPieces 0),
        Finsupp.single_zero, sub_zero]
  | succ k ih =>
      rw [SdPieces_succ (k+1), pieceBdry_conePieces]
      have hzero : pieceBdry k (B (k+1) (k+1) (SdPieces (k+1))) = 0 := by
        rw [pieceBdry_B k (k+1) (SdPieces (k+1)), ih, ← LinearMap.comp_apply, B_comp k k]
        simp
      rw [hzero]
      simp

end SdAux

/-- **The chain-map property of the barycentric subdivision**: `∂ (Sd(Δ^{n+1}))` is the
alternating sum `∑ᵢ (-1)ⁱ (δᵢ)₊ (Sd(Δⁿ))` of the pushforwards of the barycentric subdivision of
`Δⁿ` along the coface inclusions. -/
theorem pieceBdry_SdPieces (n : ℕ) :
    Submission.Cohomology.pieceBdry n (Submission.Cohomology.SdPieces (n+1))
      = ∑ i : Fin (n+2), (-1 : ℚ) ^ (i : ℕ) •
          Submission.Cohomology.pushPieces (Submission.Cohomology.faceIncl i) n
            (Submission.Cohomology.SdPieces n) := by
  rw [← SdAux.B_apply n n (Submission.Cohomology.SdPieces n)]
  exact SdAux.pieceBdry_SdPieces_aux n

end

end Work.Cohomology
