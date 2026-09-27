/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team
-/
import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.clutch_agree
import Submission.Work.KT.Fund.map_orthProj
import Submission.Work.KT.Fund.isUnit_one_add_conjTranspose_mul
import Submission.Work.KT.Fund.graphB_recipB_conjTranspose_mul_self
import Submission.Work.KT.Fund.recipB_eq_graphB_mul
import Submission.Work.KT.Fund.map_witness

/-!
# `Work.KT.Fund.kappa_one`

`Fund.kappa X n u` is the clutched class in `K0 C(X × S², ℂ)` of a unit `u` over
`C(X × S¹, ℂ)` (Hatcher's elementary construction of the Bott class): glue two trivial bundles
over the two hemispheres of `S²` along the clutching function `u`.  For the *trivial* clutching
function `u = 1` the glued bundle is the trivial rank-`n` bundle, so

  `kappa X n 1 = cls (Mat.one C(X × S², ℂ) n)`.

The proof identifies the clutched idempotent — an element of `Mat ↥(pullAlg2 X)` of size `2n`,
given by the pair of per-disc orthogonal projections `graphProj F` (upper hemisphere) and
`recipProj G` (lower hemisphere), where `F`, `G` are the chosen lifts of `u = 1`, resp. `u⁻¹ = 1`
— and exhibits explicit Murray–von Neumann data for it:

* on each disc, `B := graphB F` (resp. `recipB G`) satisfies
  `(BᴴB)⁻¹Bᴴ * B = 1` and `B * ((BᴴB)⁻¹Bᴴ) = orthProj B` (the Gram matrix `BᴴB = 1 + FᴴF` is a
  unit), so the projection onto the graph of `F` is Murray–von Neumann equivalent to `1ₙ`;
* for `u = 1` the two discarded boundary matrices coincide, `graphB C(X × S¹, ℂ) 1 =
  recipB C(X × S¹, ℂ) 1`, so the *same* explicit data can be glued: the witness matrices agree on
  the equator (`map_witness` + `map_graphB_recipB`), and the glued matrices over the fibre product
  `pullAlg2 X` multiply to the projection, resp. to the identity.

`Mat.mvN_reindex_data` transfers the resulting Murray–von Neumann equivalence, which is stated for
the block index set `Fin n ⊕ Fin n`, to the reindexed `2n × 2n` matrices appearing in
`clutchIdem`.
-/

namespace Work.KT.Fund

open Matrix

noncomputable section

/-! ## Murray–von Neumann equivalence under a reindexing -/

/-- If matrices `a`, `b` exhibit Murray–von Neumann equivalence between an `ι × ι`-matrix `M` and
an `n × n`-matrix `N` (`b * a = M`, `a * b = N`), then the same matrices, reindexed along an
equivalence `e : ι ≃ Fin m`, exhibit Murray–von Neumann equivalence between `reindex e e M` and
`N`.  This is how the block form `Fin n ⊕ Fin n` of `Fund.clutchIdem` is compared with the
`Fin (n+n)` form of the `K₀` classes. -/
theorem Mat.mvN_reindex_data {A : Type} [Ring A] {ι : Type} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (e : ι ≃ Fin m) {n : ℕ} {M : Matrix ι ι A} {N : Matrix (Fin n) (Fin n) A}
    (a : Matrix (Fin n) ι A) (b : Matrix ι (Fin n) A) (hba : b * a = M) (hab : a * b = N) :
    Mat.MvN ⟨m, Matrix.reindex e e M⟩ ⟨n, N⟩ := by
  refine ⟨a.submatrix id e.symm, b.submatrix e.symm id, ?_, ?_⟩
  · rw [← Matrix.submatrix_mul (M := b) (N := a) (e₁ := ⇑e.symm) (e₂ := id) (e₃ := ⇑e.symm)
        Function.bijective_id, hba, Matrix.reindex_apply]
  · rw [← Matrix.submatrix_mul (M := a) (N := b) (e₁ := id) (e₂ := ⇑e.symm) (e₃ := id)
        e.symm.bijective, hab, Matrix.submatrix_id_id]

/-! ## The explicit Murray–von Neumann data of a single disc -/

/-- The orthogonal projection onto the image of `B` factors as `B · ((BᴴB)⁻¹Bᴴ)`. -/
lemma orthProj_eq_mul {n : ℕ} (R : Type) [CommRing R] [Star R]
    (B : Matrix (Fin n ⊕ Fin n) (Fin n) R) :
    B * (Ring.inverse (B.conjTranspose * B) * B.conjTranspose) = orthProj R B := by
  unfold orthProj
  rw [Matrix.mul_assoc]

/-- `(BᴴB)⁻¹Bᴴ` is a left inverse of `B`, provided `BᴴB` is a unit. -/
lemma witness_conjTranspose_mul {n : ℕ} (R : Type) [CommRing R] [Star R]
    (B : Matrix (Fin n ⊕ Fin n) (Fin n) R) (h : IsUnit (B.conjTranspose * B)) :
    (Ring.inverse (B.conjTranspose * B) * B.conjTranspose) * B = 1 := by
  rw [Matrix.mul_assoc, Ring.inverse_mul_cancel _ h]

/-- The Gram matrix `BᴴB` of `graphB` is a unit over `C(Y, ℂ)`, being `1 + FᴴF`. -/
lemma isUnit_graphB_gram {n : ℕ} (Y : Type) [TopologicalSpace Y]
    (F : Matrix (Fin n) (Fin n) C(Y, ℂ)) :
    IsUnit ((graphB C(Y, ℂ) F).conjTranspose * graphB C(Y, ℂ) F) := by
  rw [(graphB_recipB_conjTranspose_mul_self C(Y, ℂ) F F).1]
  exact isUnit_one_add_conjTranspose_mul F

/-- The Gram matrix `BᴴB` of `recipB` is a unit over `C(Y, ℂ)`, being `1 + GᴴG`. -/
lemma isUnit_recipB_gram {n : ℕ} (Y : Type) [TopologicalSpace Y]
    (G : Matrix (Fin n) (Fin n) C(Y, ℂ)) :
    IsUnit ((recipB C(Y, ℂ) G).conjTranspose * recipB C(Y, ℂ) G) := by
  rw [(graphB_recipB_conjTranspose_mul_self C(Y, ℂ) G G).2]
  exact isUnit_one_add_conjTranspose_mul G

/-! ## The rectangular pairing of the two disc algebras -/

/-- Rectangular version of `Fund.pairMat`: from a compatible pair of matrices over the two discs,
the matrix over the fibre product `pullAlg2 X` with entries the glued pairs. -/
def pairMatR {ι κ : Type} (X : Type) [TopologicalSpace X]
    (M₀ M₁ : Matrix ι κ C(X × Ball ℂ, ℂ))
    (h : M₀.map ⇑(bdryRestrict X) = M₁.map ⇑(bdryRestrict X)) :
    Matrix ι κ ↥(pullAlg2 X) :=
  fun i j => mkPair X (M₀ i j) (M₁ i j) (by
    have h' := congrFun (congrFun h i) j
    simpa only [Matrix.map_apply] using h')

@[simp] lemma pairMatR_map_prF {ι κ : Type} (X : Type) [TopologicalSpace X]
    (M₀ M₁ : Matrix ι κ C(X × Ball ℂ, ℂ))
    (h : M₀.map ⇑(bdryRestrict X) = M₁.map ⇑(bdryRestrict X)) :
    (pairMatR X M₀ M₁ h).map ⇑(prF X) = M₀ := rfl

@[simp] lemma pairMatR_map_prS {ι κ : Type} (X : Type) [TopologicalSpace X]
    (M₀ M₁ : Matrix ι κ C(X × Ball ℂ, ℂ))
    (h : M₀.map ⇑(bdryRestrict X) = M₁.map ⇑(bdryRestrict X)) :
    (pairMatR X M₀ M₁ h).map ⇑(prS X) = M₁ := rfl

/-- `pairMatR` does not depend on the compatibility proof. -/
lemma pairMatR_congr {ι κ : Type} (X : Type) [TopologicalSpace X]
    (M₀ M₁ : Matrix ι κ C(X × Ball ℂ, ℂ))
    (h h' : M₀.map ⇑(bdryRestrict X) = M₁.map ⇑(bdryRestrict X)) :
    pairMatR X M₀ M₁ h = pairMatR X M₀ M₁ h' := rfl

/-- `pairMatR` and `Fund.pairMat` agree on square matrices. -/
lemma pairMat_eq_pairMatR {ι : Type} (X : Type) [TopologicalSpace X]
    (M₀ M₁ : Matrix ι ι C(X × Ball ℂ, ℂ))
    (h : M₀.map ⇑(bdryRestrict X) = M₁.map ⇑(bdryRestrict X)) :
    pairMat X M₀ M₁ h = pairMatR X M₀ M₁ h := rfl

/-- Two matrices over the fibre product with the same two projections are equal (rectangular
version of `Fund.mat_ext`). -/
lemma mat_ext_rect {ι κ : Type} (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {A B : Matrix ι κ ↥(pullAlg2 X)}
    (h₁ : A.map ⇑(prF X) = B.map ⇑(prF X)) (h₂ : A.map ⇑(prS X) = B.map ⇑(prS X)) : A = B := by
  refine Matrix.ext fun i j => ?_
  refine Subtype.ext ?_
  refine Prod.ext ?_ ?_
  · have h := congrFun (congrFun h₁ i) j
    simpa only [Matrix.map_apply, prF_apply] using h
  · have h := congrFun (congrFun h₂ i) j
    simpa only [Matrix.map_apply, prS_apply] using h

/-- `pairMatR` is multiplicative. -/
lemma pairMatR_mul {ι κ μ : Type} [Fintype κ] (X : Type) [TopologicalSpace X]
    [CompactSpace X] [T2Space X]
    (M₀ M₁ : Matrix ι κ C(X × Ball ℂ, ℂ)) (N₀ N₁ : Matrix κ μ C(X × Ball ℂ, ℂ))
    (hM : M₀.map ⇑(bdryRestrict X) = M₁.map ⇑(bdryRestrict X))
    (hN : N₀.map ⇑(bdryRestrict X) = N₁.map ⇑(bdryRestrict X))
    (hc : (M₀ * N₀).map ⇑(bdryRestrict X) = (M₁ * N₁).map ⇑(bdryRestrict X)) :
    pairMatR X M₀ M₁ hM * pairMatR X N₀ N₁ hN = pairMatR X (M₀ * N₀) (M₁ * N₁) hc := by
  apply mat_ext_rect X
  · rw [Matrix.map_mul, pairMatR_map_prF, pairMatR_map_prF, pairMatR_map_prF]
  · rw [Matrix.map_mul, pairMatR_map_prS, pairMatR_map_prS, pairMatR_map_prS]

/-- `pairMatR` of two identity matrices is the identity matrix. -/
lemma pairMatR_one (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ)
    (h : (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map ⇑(bdryRestrict X)
      = (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map ⇑(bdryRestrict X)) :
    pairMatR X (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
      (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) h = 1 := by
  apply mat_ext_rect X
  · simp only [pairMatR_map_prF, Matrix.map_one (prF X) (map_zero _) (map_one _)]
  · simp only [pairMatR_map_prS, Matrix.map_one (prS X) (map_zero _) (map_one _)]

/-! ## The main computation -/

/-- The identity matrix of any size is idempotent.  (`Mat.one_isIdem` is declared in several
modules of the workspace with different argument implicitness, so it is reproduced here.) -/
private lemma one_isIdem_local {R : Type} [Ring R] (n : ℕ) : (Mat.one R n).IsIdem := by
  unfold Mat.IsIdem Mat.one
  exact Matrix.one_mul 1

/-- The clutched idempotent of the trivial unit is the class of the trivial bundle of rank `n`. -/
private lemma clutchIdem_one_cls (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (F G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hF : F.map ⇑(bdryRestrict X) = ↑(1 : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ))
    (hG : G.map ⇑(bdryRestrict X) = ↑(1 : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)) :
    cls (clutchIdem X n 1 F G hF hG) = cls (Mat.one ↥(pullAlg2 X) n) := by
  have hFm : F.map ⇑(bdryRestrict X) = (1 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := hF
  have hGm : G.map ⇑(bdryRestrict X) = (1 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := hG
  apply cls_eq_of_mvn (clutchIdem_isIdem X n 1 F G hF hG) (one_isIdem_local n)
  change Mat.MvN ⟨n + n, Matrix.reindex finSumFinEquiv finSumFinEquiv
      (pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G)
        (clutch_agree X n 1 F G hF hG))⟩ ⟨n, (1 : Matrix (Fin n) (Fin n) ↥(pullAlg2 X))⟩
  -- the two boundary matrices and the two witnesses
  set B₀ : Matrix (Fin n ⊕ Fin n) (Fin n) C(X × Ball ℂ, ℂ) := graphB C(X × Ball ℂ, ℂ) F with hB₀
  set B₁ : Matrix (Fin n ⊕ Fin n) (Fin n) C(X × Ball ℂ, ℂ) := recipB C(X × Ball ℂ, ℂ) G with hB₁
  set W₀ : Matrix (Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
    Ring.inverse (B₀.conjTranspose * B₀) * B₀.conjTranspose with hW₀
  set W₁ : Matrix (Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
    Ring.inverse (B₁.conjTranspose * B₁) * B₁.conjTranspose with hW₁
  have hunit₀ : IsUnit (B₀.conjTranspose * B₀) := by
    rw [hB₀]; exact isUnit_graphB_gram (X × Ball ℂ) F
  have hunit₁ : IsUnit (B₁.conjTranspose * B₁) := by
    rw [hB₁]; exact isUnit_recipB_gram (X × Ball ℂ) G
  have hBW₀ : B₀ * W₀ = graphProj C(X × Ball ℂ, ℂ) F := by
    rw [hW₀, hB₀]
    exact orthProj_eq_mul C(X × Ball ℂ, ℂ) (graphB C(X × Ball ℂ, ℂ) F)
  have hBW₁ : B₁ * W₁ = recipProj C(X × Ball ℂ, ℂ) G := by
    rw [hW₁, hB₁]
    exact orthProj_eq_mul C(X × Ball ℂ, ℂ) (recipB C(X × Ball ℂ, ℂ) G)
  have hWB₀ : W₀ * B₀ = 1 := by
    rw [hW₀]
    exact witness_conjTranspose_mul C(X × Ball ℂ, ℂ) B₀ hunit₀
  have hWB₁ : W₁ * B₁ = 1 := by
    rw [hW₁]
    exact witness_conjTranspose_mul C(X × Ball ℂ, ℂ) B₁ hunit₁
  -- the two boundary matrices agree (both are `[[1],[1]]`)
  have hBcompat : B₀.map ⇑(bdryRestrict X) = B₁.map ⇑(bdryRestrict X) := by
    rw [hB₀, hB₁, (map_graphB_recipB (bdryRestrict X) F).1,
      (map_graphB_recipB (bdryRestrict X) G).2, hFm, hGm,
      recipB_eq_graphB_mul C(X × Sph ℂ, ℂ)
        (1 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
        (1 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) (by simp), Matrix.mul_one]
  -- hence so do the witnesses
  have hWcompat : W₀.map ⇑(bdryRestrict X) = W₁.map ⇑(bdryRestrict X) := by
    rw [hW₀, hW₁,
      map_witness (bdryRestrict X) (bdryRestrict_semiconj_star X) B₀ hunit₀,
      map_witness (bdryRestrict X) (bdryRestrict_semiconj_star X) B₁ hunit₁,
      hBcompat]
  have hba : pairMatR X B₀ B₁ hBcompat * pairMatR X W₀ W₁ hWcompat
      = pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G)
          (clutch_agree X n 1 F G hF hG) := by
    apply mat_ext_rect X
    · rw [Matrix.map_mul, pairMatR_map_prF, pairMatR_map_prF, pairMat_map_prF]
      exact hBW₀
    · rw [Matrix.map_mul, pairMatR_map_prS, pairMatR_map_prS, pairMat_map_prS]
      exact hBW₁
  have hab : pairMatR X W₀ W₁ hWcompat * pairMatR X B₀ B₁ hBcompat = 1 := by
    apply mat_ext_rect X
    · rw [Matrix.map_mul, pairMatR_map_prF, pairMatR_map_prF,
        Matrix.map_one (prF X) (map_zero _) (map_one _)]
      exact hWB₀
    · rw [Matrix.map_mul, pairMatR_map_prS, pairMatR_map_prS,
        Matrix.map_one (prS X) (map_zero _) (map_one _)]
      exact hWB₁
  exact Mat.mvN_reindex_data (e := finSumFinEquiv)
    (M := pairMat X (graphProj C(X × Ball ℂ, ℂ) F) (recipProj C(X × Ball ℂ, ℂ) G)
      (clutch_agree X n 1 F G hF hG))
    (N := (1 : Matrix (Fin n) (Fin n) ↥(pullAlg2 X)))
    (a := pairMatR X W₀ W₁ hWcompat) (b := pairMatR X B₀ B₁ hBcompat) hba hab

/-- `k0Glue` sends the class of the trivial bundle over `X × S²` to the class of the trivial
bundle over the fibre product. -/
private lemma k0Glue_cls_one (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) :
    (k0Glue X) (cls (Mat.one C(X × S2, ℂ) n)) = cls (Mat.one ↥(pullAlg2 X) n) := by
  show K0.map (glueEquiv X : C(X × S2, ℂ) →+* ↥(pullAlg2 X))
      (cls (Mat.one C(X × S2, ℂ) n)) = _
  rw [K0.map_cls _ (one_isIdem_local n)]
  apply cls_congr
  show (⟨n, (1 : Matrix (Fin n) (Fin n) C(X × S2, ℂ)).map ⇑(glueEquiv X)⟩ : Mat ↥(pullAlg2 X))
      = ⟨n, 1⟩
  rw [Matrix.map_one (⇑(glueEquiv X)) (map_zero _) (map_one _)]

/-- **The trivial clutching class**: `κ(1) = [1ₙ]`. -/
theorem kappa_one (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n : ℕ) :
    Work.KT.Fund.kappa X n (1 : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
      = Work.KT.cls (Work.KT.Mat.one C(X × S2, ℂ) n) := by
  rw [kappa_val]
  simp only [Units.val_one, inv_one]
  refine (k0Glue X).injective.eq_iff.mp ?_
  rw [AddEquiv.apply_symm_apply, k0Glue_cls_one]
  exact clutchIdem_one_cls X n (liftOf X (1 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (liftOf X (1 : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (liftOf_spec X _) (liftOf_spec X _)

end

end Work.KT.Fund
