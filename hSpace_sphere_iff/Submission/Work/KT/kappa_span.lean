import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.Pullback
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Bott.k0_exact
import Submission.Work.KT.Bott.mvN_glue
import Submission.Work.KT.Bott.GlueAux
import Submission.Work.KT.mvN_of_cls_eq
import Submission.Work.KT.lift_diag_unit
import Submission.Work.KT.ExtGen.disc_square
import Submission.Work.KT.RelGen.disc_pair_mvN
import Submission.Work.KT.RelGen.star_left_inverse

namespace Work.KT

open Matrix

noncomputable section

/-! ## Auxiliary algebra -/

section Algebra

variable {R S : Type} [Ring R] [Ring S] {N : ℕ}

/-- A ring homomorphism commutes with the totalized inverse of a unit matrix. -/
lemma inverse_map_matrix (φ : R →+* S) (M : Matrix (Fin N) (Fin N) R) (h : IsUnit M) :
    (Ring.inverse M).map φ = Ring.inverse (M.map φ) := by
  have hx : IsUnit (M.map φ) := by
    rw [← RingHom.mapMatrix_apply]
    exact h.map (RingHom.mapMatrix φ)
  have h2 : M.map φ * (Ring.inverse M).map φ = 1 := by
    rw [← Matrix.map_mul, Ring.mul_inverse_cancel M h,
      Matrix.map_one (⇑φ) (map_zero φ) (map_one φ)]
  calc (Ring.inverse M).map φ
      = 1 * (Ring.inverse M).map φ := (Matrix.one_mul _).symm
    _ = (Ring.inverse (M.map φ) * M.map φ) * (Ring.inverse M).map φ := by
          rw [Ring.inverse_mul_cancel _ hx]
    _ = Ring.inverse (M.map φ) * (M.map φ * (Ring.inverse M).map φ) := by rw [Matrix.mul_assoc]
    _ = Ring.inverse (M.map φ) * 1 := by rw [h2]
    _ = Ring.inverse (M.map φ) := by rw [mul_one]

end Algebra

section DiscAux

/-! ### Reindexing helpers: the block matrices `[[1],[F]]` with `Fin (n+n)` indices -/

section ReindexAux

variable {R S : Type} [Ring R] [Ring S]

/-- The graph column `[[1],[F]]` with its `Fin n ⊕ Fin n` row index reindexed to `Fin (n+n)`. -/
def rgraphB {n : ℕ} (R : Type) [Ring R] (F : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + n)) (Fin n) R :=
  Matrix.reindex finSumFinEquiv (Equiv.refl (Fin n)) (Fund.graphB R F)

/-- The reciprocal graph column `[[G],[1]]` with its row index reindexed to `Fin (n+n)`. -/
def rrecipB {n : ℕ} (R : Type) [Ring R] (G : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + n)) (Fin n) R :=
  Matrix.reindex finSumFinEquiv (Equiv.refl (Fin n)) (Fund.recipB R G)

/-- Reindexing the rows of a matrix commutes with entrywise ring maps. -/
lemma reindexRow_map {k k' n : Type} (e : k ≃ k') (M : Matrix k n R)
    (φ : R →+* S) :
    (Matrix.reindex e (Equiv.refl n) M).map φ =
      Matrix.reindex e (Equiv.refl n) (M.map φ) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply,
    Equiv.refl_symm, Equiv.coe_refl, id_eq]

/-- Reindexing the columns of a matrix commutes with entrywise ring maps. -/
lemma reindexCol_map {m n k : Type} (e : n ≃ k) (M : Matrix m n R)
    (φ : R →+* S) :
    (Matrix.reindex (Equiv.refl m) e M).map φ =
      Matrix.reindex (Equiv.refl m) e (M.map φ) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply,
    Equiv.refl_symm, Equiv.coe_refl, id_eq]

/-- Reindexing the columns of a product with a square matrix on the left. -/
lemma reindexCol_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin n) (Fin n ⊕ Fin n) R) :
    Matrix.reindex (Equiv.refl (Fin n)) finSumFinEquiv (A * B) =
      A * Matrix.reindex (Equiv.refl (Fin n)) finSumFinEquiv B := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply, Equiv.refl_symm,
    Equiv.coe_refl, id_eq]

/-- Reindexing the rows of a product with a square matrix on the right. -/
lemma reindexRow_mul {n : ℕ} (M : Matrix (Fin n ⊕ Fin n) (Fin n) R)
    (N : Matrix (Fin n) (Fin n) R) :
    Matrix.reindex finSumFinEquiv (Equiv.refl (Fin n)) (M * N) =
      Matrix.reindex finSumFinEquiv (Equiv.refl (Fin n)) M * N := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply, Equiv.refl_symm,
    Equiv.coe_refl, id_eq]

lemma rgraphB_map {n : ℕ} (F : Matrix (Fin n) (Fin n) R) (φ : R →+* S) :
    (rgraphB R F).map φ = rgraphB S (F.map φ) := by
  ext i j
  rcases h : finSumFinEquiv.symm i with a | a <;>
    simp [rgraphB, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply,
      Fund.graphB, h]

lemma rrecipB_map {n : ℕ} (G : Matrix (Fin n) (Fin n) R) (φ : R →+* S) :
    (rrecipB R G).map φ = rrecipB S (G.map φ) := by
  ext i j
  rcases h : finSumFinEquiv.symm i with a | a <;>
    simp [rrecipB, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply,
      Fund.graphB, Fund.recipB, h]

end ReindexAux

section ReindexProj

variable {R : Type} [CommRing R] [Star R]

/-- The graph projection with `Fin (n+n)` indices. -/
def rgraphProj {n : ℕ} (R : Type) [CommRing R] [Star R] (F : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + n)) (Fin (n + n)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.graphProj R F)

/-- The reciprocal graph projection with `Fin (n+n)` indices. -/
def rrecipProj {n : ℕ} (R : Type) [CommRing R] [Star R] (G : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + n)) (Fin (n + n)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.recipProj R G)

/-- The left inverse of `rgraphB`, with `Fin (n+n)` column index. -/
def rgraphLinv {n : ℕ} (R : Type) [CommRing R] [Star R] (F : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin (n + n)) R :=
  Matrix.reindex (Equiv.refl (Fin n)) finSumFinEquiv
    (Ring.inverse ((Fund.graphB R F).conjTranspose * Fund.graphB R F) *
      (Fund.graphB R F).conjTranspose)

/-- The left inverse of `rrecipB`, with `Fin (n+n)` column index. -/
def rrecipLinv {n : ℕ} (R : Type) [CommRing R] [Star R] (G : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin (n + n)) R :=
  Matrix.reindex (Equiv.refl (Fin n)) finSumFinEquiv
    (Ring.inverse ((Fund.recipB R G).conjTranspose * Fund.recipB R G) *
      (Fund.recipB R G).conjTranspose)

lemma rgraphLinv_mul {n : ℕ} (R : Type) [CommRing R] [Star R] (F : Matrix (Fin n) (Fin n) R)
    (h : IsUnit ((Fund.graphB R F).conjTranspose * Fund.graphB R F)) :
    rgraphLinv R F * rgraphB R F = 1 := by
  rw [rgraphLinv, rgraphB, Work.KT.reindexMul, Matrix.mul_assoc,
    Ring.inverse_mul_cancel _ h, Bott.matrix_reindex_one]

lemma rrecipLinv_mul {n : ℕ} (R : Type) [CommRing R] [Star R] (G : Matrix (Fin n) (Fin n) R)
    (h : IsUnit ((Fund.recipB R G).conjTranspose * Fund.recipB R G)) :
    rrecipLinv R G * rrecipB R G = 1 := by
  rw [rrecipLinv, rrecipB, Work.KT.reindexMul, Matrix.mul_assoc,
    Ring.inverse_mul_cancel _ h, Bott.matrix_reindex_one]

lemma rgraphB_mul_rgraphLinv {n : ℕ} (R : Type) [CommRing R] [Star R]
    (F : Matrix (Fin n) (Fin n) R) :
    rgraphB R F * rgraphLinv R F = rgraphProj R F := by
  rw [rgraphB, rgraphLinv, rgraphProj, Work.KT.reindexMul, ← Matrix.mul_assoc]
  rfl

lemma rrecipB_mul_rrecipLinv {n : ℕ} (R : Type) [CommRing R] [Star R]
    (G : Matrix (Fin n) (Fin n) R) :
    rrecipB R G * rrecipLinv R G = rrecipProj R G := by
  rw [rrecipB, rrecipLinv, rrecipProj, Work.KT.reindexMul, ← Matrix.mul_assoc]
  rfl

end ReindexProj

open Work.KT.Fund (bdryRestrict)

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ### The `C(X × D, ℂ)`-valued left inverses -/

/-- The "left inverse" (`N × (N ⊕ N)`) of the graph column `[[1],[F]]`. -/
def graphLinv {N : ℕ} (F : Matrix (Fin N) (Fin N) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin N) (Fin N ⊕ Fin N) C(X × Ball ℂ, ℂ) :=
  Ring.inverse ((Fund.graphB C(X × Ball ℂ, ℂ) F).conjTranspose * Fund.graphB C(X × Ball ℂ, ℂ) F) *
    (Fund.graphB C(X × Ball ℂ, ℂ) F).conjTranspose

/-- The "left inverse" of the reciprocal graph column `[[G],[1]]`. -/
def recipLinv {N : ℕ} (G : Matrix (Fin N) (Fin N) C(X × Ball ℂ, ℂ)) :
    Matrix (Fin N) (Fin N ⊕ Fin N) C(X × Ball ℂ, ℂ) :=
  Ring.inverse ((Fund.recipB C(X × Ball ℂ, ℂ) G).conjTranspose * Fund.recipB C(X × Ball ℂ, ℂ) G) *
    (Fund.recipB C(X × Ball ℂ, ℂ) G).conjTranspose

lemma graphB_gram_isUnit {N : ℕ} (F : Matrix (Fin N) (Fin N) C(X × Ball ℂ, ℂ)) :
    IsUnit ((Fund.graphB C(X × Ball ℂ, ℂ) F).conjTranspose *
      Fund.graphB C(X × Ball ℂ, ℂ) F) := by
  rw [(Fund.graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) F F).1]
  exact Fund.isUnit_one_add_conjTranspose_mul F

lemma recipB_gram_isUnit {N : ℕ} (G : Matrix (Fin N) (Fin N) C(X × Ball ℂ, ℂ)) :
    IsUnit ((Fund.recipB C(X × Ball ℂ, ℂ) G).conjTranspose *
      Fund.recipB C(X × Ball ℂ, ℂ) G) := by
  rw [(Fund.graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) G G).2]
  exact Fund.isUnit_one_add_conjTranspose_mul G

lemma graphLinv_mul {N : ℕ} (F : Matrix (Fin N) (Fin N) C(X × Ball ℂ, ℂ)) :
    graphLinv X F * Fund.graphB C(X × Ball ℂ, ℂ) F = 1 := by
  rw [graphLinv, Matrix.mul_assoc, Ring.inverse_mul_cancel _ (graphB_gram_isUnit X F)]

lemma recipLinv_mul {N : ℕ} (G : Matrix (Fin N) (Fin N) C(X × Ball ℂ, ℂ)) :
    recipLinv X G * Fund.recipB C(X × Ball ℂ, ℂ) G = 1 := by
  rw [recipLinv, Matrix.mul_assoc, Ring.inverse_mul_cancel _ (recipB_gram_isUnit X G)]

lemma graphB_mul_graphLinv {N : ℕ} (F : Matrix (Fin N) (Fin N) C(X × Ball ℂ, ℂ)) :
    Fund.graphB C(X × Ball ℂ, ℂ) F * graphLinv X F =
      Fund.graphProj C(X × Ball ℂ, ℂ) F := by
  rw [graphLinv, ← Matrix.mul_assoc]
  rfl

lemma recipB_mul_recipLinv {N : ℕ} (G : Matrix (Fin N) (Fin N) C(X × Ball ℂ, ℂ)) :
    Fund.recipB C(X × Ball ℂ, ℂ) G * recipLinv X G =
      Fund.recipProj C(X × Ball ℂ, ℂ) G := by
  rw [recipLinv, ← Matrix.mul_assoc]
  rfl

/-- `recipB (u⁻¹) * u = graphB u`. -/
lemma recipB_inv_mul_graphB {N : ℕ} (u : (Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))ˣ) :
    Fund.recipB C(X × Sph ℂ, ℂ) (↑(u⁻¹) : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)) *
        (↑u : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)) =
      Fund.graphB C(X × Sph ℂ, ℂ) (↑u : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)) := by
  have key : Fund.recipB C(X × Sph ℂ, ℂ) (↑(u⁻¹) : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)) =
      Fund.graphB C(X × Sph ℂ, ℂ) (↑u : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)) *
        (↑(u⁻¹) : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)) :=
    Fund.recipB_eq_graphB_mul _ _ _ (Units.mul_inv u)
  rw [key, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/-- The first projection of the explicit clutched matrix. -/
lemma clutchData_map_prF {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (F G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hF : F.map (Fund.bdryRestrict X) = ↑u) (hG : G.map (Fund.bdryRestrict X) = ↑(u⁻¹)) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Fund.pairMat X (Fund.graphProj C(X × Ball ℂ, ℂ) F) (Fund.recipProj C(X × Ball ℂ, ℂ) G)
          (Fund.clutch_agree X n u F G hF hG))).map (Fund.prF X) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.graphProj C(X × Ball ℂ, ℂ) F) := by
  rw [Bott.reindex_map_bott, Fund.pairMat_map_prF]

/-- The second projection of the explicit clutched matrix. -/
lemma clutchData_map_prS {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (F G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hF : F.map (Fund.bdryRestrict X) = ↑u) (hG : G.map (Fund.bdryRestrict X) = ↑(u⁻¹)) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Fund.pairMat X (Fund.graphProj C(X × Ball ℂ, ℂ) F) (Fund.recipProj C(X × Ball ℂ, ℂ) G)
          (Fund.clutch_agree X n u F G hF hG))).map (Fund.prS X) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.recipProj C(X × Ball ℂ, ℂ) G) := by
  rw [Bott.reindex_map_bott, Fund.pairMat_map_prS]

lemma blk_one_zero {R : Type} [Ring R] {N : ℕ} :
    Bott.blk 0 (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  rw [Bott.blk, Matrix.fromBlocks_one, Bott.matrix_reindex_one]

end DiscAux

section LinvMap

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The image of `rgraphLinv` on the circle. -/
lemma rgraphLinv_map {N : ℕ} (F : Matrix (Fin N) (Fin N) C(X × Ball ℂ, ℂ))
    (u : (Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))ˣ)
    (hFs : F.map (Fund.bdryRestrict X) = ↑u) :
    (rgraphLinv C(X × Ball ℂ, ℂ) F).map (Fund.bdryRestrict X) =
      rgraphLinv C(X × Sph ℂ, ℂ) (↑u : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)) := by
  rw [rgraphLinv, rgraphLinv, reindexCol_map]
  congr 1
  rw [Matrix.map_mul, Matrix.conjTranspose_map (Fund.bdryRestrict X)
      (Fund.bdryRestrict_semiconj_star X)]
  rw [inverse_map_matrix (Fund.bdryRestrict X) _ (graphB_gram_isUnit X F)]
  simp only [Matrix.map_mul]
  rw [Matrix.conjTranspose_map (Fund.bdryRestrict X) (Fund.bdryRestrict_semiconj_star X),
    (Fund.map_graphB_recipB (Fund.bdryRestrict X) F).1, hFs]

/-- The image of `rrecipLinv` on the circle. -/
lemma rrecipLinv_map {N : ℕ} (G : Matrix (Fin N) (Fin N) C(X × Ball ℂ, ℂ))
    (u : (Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))ˣ)
    (hGs : G.map (Fund.bdryRestrict X) = ↑(u⁻¹)) :
    (rrecipLinv C(X × Ball ℂ, ℂ) G).map (Fund.bdryRestrict X) =
      rrecipLinv C(X × Sph ℂ, ℂ) (↑(u⁻¹) : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)) := by
  rw [rrecipLinv, rrecipLinv, reindexCol_map]
  congr 1
  rw [Matrix.map_mul, Matrix.conjTranspose_map (Fund.bdryRestrict X)
      (Fund.bdryRestrict_semiconj_star X)]
  rw [inverse_map_matrix (Fund.bdryRestrict X) _ (recipB_gram_isUnit X G)]
  simp only [Matrix.map_mul]
  rw [Matrix.conjTranspose_map (Fund.bdryRestrict X) (Fund.bdryRestrict_semiconj_star X),
    (Fund.map_graphB_recipB (Fund.bdryRestrict X) G).2, hGs]

end LinvMap

section MainGlue

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- **Gluing of an idempotent with the canonical clutched idempotent.** -/
theorem clutchIdem_mvN (m n a : ℕ) (E : Matrix (Fin m) (Fin m) ↥(Fund.pullAlg2 X))
    (SA₁ : Matrix (Fin (n + a)) (Fin (m + a)) C(X × Ball ℂ, ℂ))
    (TB₁ : Matrix (Fin (m + a)) (Fin (n + a)) C(X × Ball ℂ, ℂ))
    (SA₂ : Matrix (Fin (n + a)) (Fin (m + a)) C(X × Ball ℂ, ℂ))
    (TB₂ : Matrix (Fin (m + a)) (Fin (n + a)) C(X × Ball ℂ, ℂ))
    (h₁ : TB₁ * SA₁ = Bott.blk a (E.map (Fund.prF X)))
    (h₂ : SA₁ * TB₁ = 1)
    (h₃ : TB₂ * SA₂ = Bott.blk a (E.map (Fund.prS X)))
    (h₄ : SA₂ * TB₂ = 1)
    (u : (Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ))ˣ)
    (hu₁ : (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)) *
        (SA₁.map (Fund.bdryRestrict X)) = SA₂.map (Fund.bdryRestrict X))
    (hu₂ : (TB₁.map (Fund.bdryRestrict X)) =
        (TB₂.map (Fund.bdryRestrict X)) * (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ))) :
    Mat.MvN (Mat.sum (⟨m, E⟩ : Mat ↥(Fund.pullAlg2 X)) (Mat.one ↥(Fund.pullAlg2 X) a))
      (Fund.clutchIdem X (n + a) u
        (Fund.liftOf X (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf X (↑(u⁻¹) : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf_spec X (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf_spec X (↑(u⁻¹) : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)))) := by
  set FU : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Ball ℂ, ℂ) :=
    Fund.liftOf X (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)) with hFU
  set GU : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Ball ℂ, ℂ) :=
    Fund.liftOf X (↑(u⁻¹) : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)) with hGU
  have hFUs : FU.map (Fund.bdryRestrict X) =
      (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)) := by
    rw [hFU]; exact Fund.liftOf_spec X _
  have hGUs : GU.map (Fund.bdryRestrict X) =
      (↑(u⁻¹) : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)) := by
    rw [hGU]; exact Fund.liftOf_spec X _
  have hgu : IsUnit ((Fund.graphB C(X × Ball ℂ, ℂ) FU).conjTranspose *
      Fund.graphB C(X × Ball ℂ, ℂ) FU) := graphB_gram_isUnit X FU
  have hgv : IsUnit ((Fund.recipB C(X × Ball ℂ, ℂ) GU).conjTranspose *
      Fund.recipB C(X × Ball ℂ, ℂ) GU) := recipB_gram_isUnit X GU
  set a₁ : Matrix (Fin ((n + a) + (n + a))) (Fin (m + a)) C(X × Ball ℂ, ℂ) :=
    rgraphB C(X × Ball ℂ, ℂ) FU * SA₁ with ha₁
  set b₁ : Matrix (Fin (m + a)) (Fin ((n + a) + (n + a))) C(X × Ball ℂ, ℂ) :=
    TB₁ * rgraphLinv C(X × Ball ℂ, ℂ) FU with hb₁
  set a₂ : Matrix (Fin ((n + a) + (n + a))) (Fin (m + a)) C(X × Ball ℂ, ℂ) :=
    rrecipB C(X × Ball ℂ, ℂ) GU * SA₂ with ha₂
  set b₂ : Matrix (Fin (m + a)) (Fin ((n + a) + (n + a))) C(X × Ball ℂ, ℂ) :=
    TB₂ * rrecipLinv C(X × Ball ℂ, ℂ) GU with hb₂
  set Q : Matrix (Fin ((n + a) + (n + a))) (Fin ((n + a) + (n + a))) ↥(Fund.pullAlg2 X) :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Fund.pairMat X (Fund.graphProj C(X × Ball ℂ, ℂ) FU) (Fund.recipProj C(X × Ball ℂ, ℂ) GU)
        (Fund.clutch_agree X (n + a) u FU GU hFUs hGUs)) with hQ
  -- the four Murray–von Neumann identities
  have hb₁a₁ : b₁ * a₁ = (Bott.blk a E).map (Fund.prF X) := by
    rw [hb₁, ha₁, Matrix.mul_assoc,
      ← Matrix.mul_assoc (rgraphLinv C(X × Ball ℂ, ℂ) FU) (rgraphB C(X × Ball ℂ, ℂ) FU) SA₁,
      rgraphLinv_mul C(X × Ball ℂ, ℂ) FU hgu, Matrix.one_mul, h₁, Bott.blk_map]
  have ha₁b₁ : a₁ * b₁ =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.graphProj C(X × Ball ℂ, ℂ) FU) := by
    rw [ha₁, hb₁, Matrix.mul_assoc,
      ← Matrix.mul_assoc SA₁ TB₁ (rgraphLinv C(X × Ball ℂ, ℂ) FU), h₂, Matrix.one_mul,
      rgraphB_mul_rgraphLinv]
    rfl
  have hb₂a₂ : b₂ * a₂ = (Bott.blk a E).map (Fund.prS X) := by
    rw [hb₂, ha₂, Matrix.mul_assoc,
      ← Matrix.mul_assoc (rrecipLinv C(X × Ball ℂ, ℂ) GU) (rrecipB C(X × Ball ℂ, ℂ) GU) SA₂,
      rrecipLinv_mul C(X × Ball ℂ, ℂ) GU hgv, Matrix.one_mul, h₃, Bott.blk_map]
  have ha₂b₂ : a₂ * b₂ =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.recipProj C(X × Ball ℂ, ℂ) GU) := by
    rw [ha₂, hb₂, Matrix.mul_assoc,
      ← Matrix.mul_assoc SA₂ TB₂ (rrecipLinv C(X × Ball ℂ, ℂ) GU), h₄, Matrix.one_mul,
      rrecipB_mul_rrecipLinv]
    rfl
  -- the boundary compatibility of the `a`-data
  have ha : a₁.map (Fund.bdryRestrict X) = a₂.map (Fund.bdryRestrict X) := by
    rw [ha₁, ha₂, Matrix.map_mul, Matrix.map_mul, rgraphB_map, rrecipB_map, hFUs, hGUs]
    have hgr : rgraphB C(X × Sph ℂ, ℂ) (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)) =
        rrecipB C(X × Sph ℂ, ℂ) (↑(u⁻¹) : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)) *
          (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)) := by
      rw [rgraphB, rrecipB, ← reindexRow_mul, recipB_inv_mul_graphB X u]
    rw [hgr, Matrix.mul_assoc, hu₁]
  -- the boundary compatibility of the `b`-data
  have hY : (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)) *
      (rgraphLinv C(X × Ball ℂ, ℂ) FU).map (Fund.bdryRestrict X) =
      rrecipLinv C(X × Sph ℂ, ℂ)
        (↑(u⁻¹) : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)) := by
    rw [rgraphLinv_map X FU u hFUs]
    rw [rgraphLinv, rrecipLinv, ← reindexCol_mul, ← Matrix.mul_assoc]
    rw [RelGen.star_left_inverse X (n + a) u]
  have hb : b₁.map (Fund.bdryRestrict X) = b₂.map (Fund.bdryRestrict X) := by
    rw [hb₁, hb₂, Matrix.map_mul, Matrix.map_mul, hu₂, Matrix.mul_assoc]
    rw [hY, rrecipLinv_map X GU u hGUs]
  -- conclude
  refine RelGen.disc_pair_mvN X (P := Bott.blk a E) (Q := Q) a₁ b₁ a₂ b₂
    hb₁a₁ ?_ hb₂a₂ ?_ ha hb
  · rw [hQ]
    exact ((clutchData_map_prF X u FU GU hFUs hGUs).trans ha₁b₁.symm).symm
  · rw [hQ]
    exact ((clutchData_map_prS X u FU GU hFUs hGUs).trans ha₂b₂.symm).symm

end MainGlue

section OneCls

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The clutched class of the trivial unit is trivial. -/
lemma clutchIdem_one_cls (N : ℕ) :
    cls (Fund.clutchIdem X N (1 : (Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))ˣ)
        (Fund.liftOf X (1 : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf X (1 : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf_spec X (1 : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf_spec X (1 : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)))) =
      cls (Mat.one ↥(Fund.pullAlg2 X) N) := by
  have hmvN := clutchIdem_mvN X N N 0 (1 : Matrix (Fin N) (Fin N) ↥(Fund.pullAlg2 X))
    (1 : Matrix (Fin (N + 0)) (Fin (N + 0)) C(X × Ball ℂ, ℂ))
    (1 : Matrix (Fin (N + 0)) (Fin (N + 0)) C(X × Ball ℂ, ℂ))
    (1 : Matrix (Fin (N + 0)) (Fin (N + 0)) C(X × Ball ℂ, ℂ))
    (1 : Matrix (Fin (N + 0)) (Fin (N + 0)) C(X × Ball ℂ, ℂ))
    (by rw [Matrix.one_mul, Matrix.map_one (Fund.prF X) (map_zero _) (map_one _), blk_one_zero])
    (by rw [Matrix.one_mul])
    (by rw [Matrix.one_mul, Matrix.map_one (Fund.prS X) (map_zero _) (map_one _), blk_one_zero])
    (by rw [Matrix.one_mul])
    (1 : (Matrix (Fin (N + 0)) (Fin (N + 0)) C(X × Sph ℂ, ℂ))ˣ)
    (by rw [Matrix.map_one (Fund.bdryRestrict X) (map_zero _) (map_one _), Matrix.mul_one]
        rfl)
    (by rw [Matrix.map_one (Fund.bdryRestrict X) (map_zero _) (map_one _), Matrix.one_mul]
        rfl)
  have hone0 : cls (Mat.one ↥(Fund.pullAlg2 X) 0) = 0 := by
    have h : (Mat.one ↥(Fund.pullAlg2 X) 0 : Mat ↥(Fund.pullAlg2 X)) =
        (⟨0, (0 : Matrix (Fin 0) (Fin 0) ↥(Fund.pullAlg2 X))⟩ :
          Mat ↥(Fund.pullAlg2 X)) := by
      refine Sigma.ext rfl ?_
      apply heq_of_eq
      funext i
      exact Fin.elim0 i
    rw [h, cls_zero_mat 0]
  have hsum : cls (Mat.sum (⟨N, (1 : Matrix (Fin N) (Fin N) ↥(Fund.pullAlg2 X))⟩ :
        Mat ↥(Fund.pullAlg2 X)) (Mat.one ↥(Fund.pullAlg2 X) 0)) =
      cls (Mat.one ↥(Fund.pullAlg2 X) N) := by
    change cls (Mat.sum (Mat.one ↥(Fund.pullAlg2 X) N) (Mat.one ↥(Fund.pullAlg2 X) 0)) =
      cls (Mat.one ↥(Fund.pullAlg2 X) N)
    rw [cls_sum (Mat.one_isIdem ↥(Fund.pullAlg2 X) N)
        (Mat.one_isIdem ↥(Fund.pullAlg2 X) 0), hone0, add_zero]
  have hcl : cls (Mat.sum (⟨N, (1 : Matrix (Fin N) (Fin N) ↥(Fund.pullAlg2 X))⟩ :
        Mat ↥(Fund.pullAlg2 X)) (Mat.one ↥(Fund.pullAlg2 X) 0)) =
      cls (Fund.clutchIdem X N (1 : (Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))ˣ)
        (Fund.liftOf X (1 : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf X (1 : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf_spec X (1 : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf_spec X (1 : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)))) :=
    cls_eq_of_mvn
      (Mat.sum_idem (Mat.one_isIdem ↥(Fund.pullAlg2 X) N) (Mat.one_isIdem ↥(Fund.pullAlg2 X) 0))
      (Fund.clutchIdem_isIdem X N (1 : (Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ))ˣ)
        (Fund.liftOf X (1 : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf X (1 : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf_spec X (1 : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf_spec X (1 : Matrix (Fin N) (Fin N) C(X × Sph ℂ, ℂ)))) hmvN
  exact hcl.symm.trans hsum

end OneCls

/-- The two boundary restrictions of a function on `X × S²` compose the same way with the two
projections of the fibre product. -/
lemma square_comm_prF (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    (Fund.bdryRestrict X).comp (Fund.prF X) = (Fund.bdryRestrict X).comp (Fund.prS X) :=
  ExtGen.square_comm X

/-- **Generation of the relative group by the clutched classes** (step 2 of the route note in
`Submission/Work/KT/fund_product.lean`: Milnor's Mayer–Vietoris patching argument for the two-disc
square, the only place where the `K₁ → K₀` boundary map is needed).

`Fund.kappa X n u` is the clutched class of a unit `u` over the circle `C(X × S¹, ℂ)`: an element
of `K0 C(X × S², ℂ)` whose two disc restrictions are the class of the trivial rank-`n` bundle.
Claim: every class `z` of `K0 C(X × S², ℂ)` killed by *both* disc restrictions
`K0.map (Fund.pullUp X)` and `K0.map (Fund.pullDn X)` — i.e. lying in the relative group of the
two-disc decomposition — is a finite `ℤ`-linear combination of the reduced clutched classes
`κ(u) - κ(1)`.  `κ(1)` is the class of the trivially clutched bundle (MvN equivalent to `1_n`), so
these are the standard generators `κ(u) - 1`.

Route (Milnor patching; every tool is already in the workspace).

1. Transport along `Fund.glueEquiv`: `K0.map ((Fund.glueEquiv X).symm.toRingHom) z` lies in
   `K0 ↥(Fund.pullAlg2 X)` and is killed by `Fund.prF` and `Fund.prS` (compatibilities
   `ExtGen.fstProj_comp_glueEquiv_symm` and its `sndProj` twin, in `ExtGen/disc_square.lean`).
2. `Work.KT.hk_k0_eq_diff` writes it as `cls P - cls Q` with `P`, `Q` idempotent over
   `pullAlg2 X`; `prF z = 0` says `cls (P.map (Fund.prF X)) = cls (Q.map (Fund.prF X))`.  Extract
   explicit Murray–von Neumann data `A₁, B₁` over `C(X × D, ℂ)` via `Work.KT.mvN_of_cls_eq` /
   `Work.KT.cls_eq_stable_mvN` (after stabilising by identity blocks), and `A₂, B₂` on the second
   disc.
3. The two choices need not agree on the circle: `A₁.map σ * B₂.map σ` (with `σ = Fund.bdryRestrict
   X`) is a *unit* over `C(X × S¹, ℂ)` by `Bott.isUnit_mulMap_prod` — the clutching function `w`.
4. Glue with `Bott.mvN_glue`: its stable-lifting hypothesis `hlift` comes from `Fund.liftOf` /
   `Bott.mat_lift_surj` plus stabilisation by an identity block (`Work.KT.lift_diag_unit`,
   `Work.KT.whitehead_diag`, `Work.KT.elem_lift`).  One obtains a global MvN equivalence between the
   stabilised `P`, `Q` and the patched idempotent `Fund.clutchIdem X n w (Fund.liftOf X w)
   (Fund.liftOf X w⁻¹) _ _`, the gluing identity on the equator being `Fund.clutch_agree`.  Reading
   off classes gives `z = κ(w) - κ(1)`, up to sign and stabilisation (a `ℤ`-linear combination as
   claimed).
5. Additivity in the stabilised `K₁`: `Bott.patch_idem_dim` supplies the patched idempotent for
   general `(e₁, e₂, S, T)`, so the boundary assignment is additive and finite combinations are
   generated as stated.

The conclusion is phrased as a *finite* combination rather than "kernel = image of a map
`K₁ → K₀`" because `K₁` is not formalised here; this is equivalent for every use in the route note,
since only finite combinations of the `κ(w)` are ever consumed. -/
theorem kappa_span (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (z : K0 C(X × S2, ℂ))
    (h₁ : K0.map (Fund.pullUp X) z = 0) (h₂ : K0.map (Fund.pullDn X) z = 0) :
    ∃ (m : ℕ) (N : Fin m → ℕ)
      (u : ∀ i : Fin m, (Matrix (Fin (N i)) (Fin (N i)) C(X × Sph ℂ, ℂ))ˣ)
      (c : Fin m → ℤ),
      z = ∑ i, c i • (Fund.kappa X (N i) (u i) - Fund.kappa X (N i) 1)
:= by
  classical
  have hcomp₁ : ((Fund.prF X).comp ((Fund.glueEquiv X) : C(X × S2, ℂ) →+* ↥(Fund.pullAlg2 X)))
      = Fund.pullUp X := by
    refine RingHom.ext fun g => ?_
    exact ExtGen.fstProj_glueEquiv X g
  have hcomp₂ : ((Fund.prS X).comp ((Fund.glueEquiv X) : C(X × S2, ℂ) →+* ↥(Fund.pullAlg2 X)))
      = Fund.pullDn X := by
    refine RingHom.ext fun g => ?_
    exact ExtGen.sndProj_glueEquiv X g
  set y : K0 ↥(Fund.pullAlg2 X) :=
    K0.map ((Fund.glueEquiv X) : C(X × S2, ℂ) →+* ↥(Fund.pullAlg2 X)) z with hy
  have hy₁ : K0.map (Fund.prF X) y = 0 := by
    rw [hy, ← K0.map_comp_apply, hcomp₁]
    exact h₁
  have hy₂ : K0.map (Fund.prS X) y = 0 := by
    rw [hy, ← K0.map_comp_apply, hcomp₂]
    exact h₂
  obtain ⟨F, n, hFidem, hyF⟩ := k0_rep y
  have hc₁ : cls (F.map (Fund.prF X)) = cls (Mat.one (C(X × Ball ℂ, ℂ)) n) := by
    have h : K0.map (Fund.prF X) (cls F - cls (Mat.one ↥(Fund.pullAlg2 X) n)) = 0 := by
      rw [← hyF]; exact hy₁
    rw [map_sub, K0.map_cls (Fund.prF X) hFidem,
      K0.map_cls (Fund.prF X) (Mat.one_isIdem ↥(Fund.pullAlg2 X) n),
      Bott.mat_map_one (Fund.prF X) n] at h
    exact sub_eq_zero.mp h
  have hc₂ : cls (F.map (Fund.prS X)) = cls (Mat.one (C(X × Ball ℂ, ℂ)) n) := by
    have h : K0.map (Fund.prS X) (cls F - cls (Mat.one ↥(Fund.pullAlg2 X) n)) = 0 := by
      rw [← hyF]; exact hy₂
    rw [map_sub, K0.map_cls (Fund.prS X) hFidem,
      K0.map_cls (Fund.prS X) (Mat.one_isIdem ↥(Fund.pullAlg2 X) n),
      Bott.mat_map_one (Fund.prS X) n] at h
    exact sub_eq_zero.mp h
  obtain ⟨k₁, hk₁⟩ := (cls_eq_stable_mvN (F.map (Fund.prF X))
    (Mat.one (C(X × Ball ℂ, ℂ)) n) (Mat.map_idem (Fund.prF X) hFidem)
    (Mat.one_isIdem _ n)).mp hc₁
  obtain ⟨k₂, hk₂⟩ := (cls_eq_stable_mvN (F.map (Fund.prS X))
    (Mat.one (C(X × Ball ℂ, ℂ)) n) (Mat.map_idem (Fund.prS X) hFidem)
    (Mat.one_isIdem _ n)).mp hc₂
  set a : ℕ := max k₁ k₂ with ha
  have hk₁' : Mat.MvN (Mat.sum (F.map (Fund.prF X)) (Mat.one (C(X × Ball ℂ, ℂ)) a))
      (Mat.one (C(X × Ball ℂ, ℂ)) (n + a)) := by
    have h := k2_mvN_add_one_right (p := F.map (Fund.prF X))
      (q := Mat.one (C(X × Ball ℂ, ℂ)) n) (Mat.map_idem (Fund.prF X) hFidem)
      (Mat.one_isIdem _ n) hk₁ (a - k₁)
    rw [Nat.add_sub_of_le (le_max_left k₁ k₂)] at h
    rwa [k2_one_sum_one] at h
  have hk₂' : Mat.MvN (Mat.sum (F.map (Fund.prS X)) (Mat.one (C(X × Ball ℂ, ℂ)) a))
      (Mat.one (C(X × Ball ℂ, ℂ)) (n + a)) := by
    have h := k2_mvN_add_one_right (p := F.map (Fund.prS X))
      (q := Mat.one (C(X × Ball ℂ, ℂ)) n) (Mat.map_idem (Fund.prS X) hFidem)
      (Mat.one_isIdem _ n) hk₂ (a - k₂)
    rw [Nat.add_sub_of_le (le_max_right k₁ k₂)] at h
    rwa [k2_one_sum_one] at h
  obtain ⟨SA₁, TB₁, hTB₁SA₁, hSA₁TB₁⟩ :=
    Bott.exists_factor_of_mvN (F.2.map (Fund.prF X)) n a hk₁'
  obtain ⟨SA₂, TB₂, hTB₂SA₂, hSA₂TB₂⟩ :=
    Bott.exists_factor_of_mvN (F.2.map (Fund.prS X)) n a hk₂'
  -- the clutching unit on the circle
  have hVA : (SA₁.map (Fund.bdryRestrict X)) * (TB₁.map (Fund.bdryRestrict X)) = 1 := by
    rw [← Matrix.map_mul, hSA₁TB₁, Matrix.map_one (⇑(Fund.bdryRestrict X))
      (map_zero _) (map_one _)]
  have hVB : (SA₂.map (Fund.bdryRestrict X)) * (TB₂.map (Fund.bdryRestrict X)) = 1 := by
    rw [← Matrix.map_mul, hSA₂TB₂, Matrix.map_one (⇑(Fund.bdryRestrict X))
      (map_zero _) (map_one _)]
  have hEB : (TB₁.map (Fund.bdryRestrict X)) * (SA₁.map (Fund.bdryRestrict X)) =
      (Bott.blk a (F.2.map (Fund.prF X))).map (Fund.bdryRestrict X) := by
    rw [← Matrix.map_mul, hTB₁SA₁]
  have hEB' : (TB₂.map (Fund.bdryRestrict X)) * (SA₂.map (Fund.bdryRestrict X)) =
      (Bott.blk a (F.2.map (Fund.prS X))).map (Fund.bdryRestrict X) := by
    rw [← Matrix.map_mul, hTB₂SA₂]
  have hE : (Bott.blk a (F.2.map (Fund.prF X))).map (Fund.bdryRestrict X) =
      (Bott.blk a (F.2.map (Fund.prS X))).map (Fund.bdryRestrict X) := by
    rw [Bott.blk_map, Bott.blk_map, Bott.matrix_map_map, Bott.matrix_map_map,
      square_comm_prF X]
  have hU : ((SA₂.map (Fund.bdryRestrict X)) * (TB₁.map (Fund.bdryRestrict X))) *
      ((SA₁.map (Fund.bdryRestrict X)) * (TB₂.map (Fund.bdryRestrict X))) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (TB₁.map (Fund.bdryRestrict X))
        (SA₁.map (Fund.bdryRestrict X)) (TB₂.map (Fund.bdryRestrict X)),
      hEB, hE, ← hEB', Matrix.mul_assoc, hVB, Matrix.mul_one, hVB]
  have hW : ((SA₁.map (Fund.bdryRestrict X)) * (TB₂.map (Fund.bdryRestrict X))) *
      ((SA₂.map (Fund.bdryRestrict X)) * (TB₁.map (Fund.bdryRestrict X))) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (TB₂.map (Fund.bdryRestrict X))
        (SA₂.map (Fund.bdryRestrict X)) (TB₁.map (Fund.bdryRestrict X)),
      hEB', ← hE, ← hEB, Matrix.mul_assoc, hVA, Matrix.mul_one, hVA]
  let u : (Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ))ˣ :=
    ⟨(SA₂.map (Fund.bdryRestrict X)) * (TB₁.map (Fund.bdryRestrict X)),
     (SA₁.map (Fund.bdryRestrict X)) * (TB₂.map (Fund.bdryRestrict X)), hU, hW⟩
  have hu₁ : (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)) *
      (SA₁.map (Fund.bdryRestrict X)) = SA₂.map (Fund.bdryRestrict X) := by
    show ((SA₂.map (Fund.bdryRestrict X)) * (TB₁.map (Fund.bdryRestrict X))) *
        (SA₁.map (Fund.bdryRestrict X)) = SA₂.map (Fund.bdryRestrict X)
    rw [Matrix.mul_assoc, hEB, hE, ← hEB',
      ← Matrix.mul_assoc (SA₂.map (Fund.bdryRestrict X)) (TB₂.map (Fund.bdryRestrict X))
        (SA₂.map (Fund.bdryRestrict X)), hVB, Matrix.one_mul]
  have hu₂ : (TB₁.map (Fund.bdryRestrict X)) =
      (TB₂.map (Fund.bdryRestrict X)) * (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)) := by
    show (TB₁.map (Fund.bdryRestrict X)) = (TB₂.map (Fund.bdryRestrict X)) *
        ((SA₂.map (Fund.bdryRestrict X)) * (TB₁.map (Fund.bdryRestrict X)))
    rw [← Matrix.mul_assoc (TB₂.map (Fund.bdryRestrict X)) (SA₂.map (Fund.bdryRestrict X))
        (TB₁.map (Fund.bdryRestrict X)), hEB', ← hE, ← hEB, Matrix.mul_assoc, hVA, Matrix.mul_one]
  -- the MvN equivalence with the clutched idempotent
  have hmvN := clutchIdem_mvN X F.1 n a F.2 SA₁ TB₁ SA₂ TB₂ hTB₁SA₁ hSA₁TB₁ hTB₂SA₂ hSA₂TB₂
    u hu₁ hu₂
  have hcl : cls F - cls (Mat.one ↥(Fund.pullAlg2 X) n) =
      cls (Fund.clutchIdem X (n + a) u (Fund.liftOf X ↑u) (Fund.liftOf X ↑(u⁻¹))
        (Fund.liftOf_spec X (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf_spec X (↑(u⁻¹) : Matrix (Fin (n + a)) (Fin (n + a))
          C(X × Sph ℂ, ℂ)))) -
        cls (Mat.one ↥(Fund.pullAlg2 X) (n + a)) := by
    have h1 : cls (Mat.sum F (Mat.one ↥(Fund.pullAlg2 X) a)) =
        cls F + cls (Mat.one ↥(Fund.pullAlg2 X) a) :=
      cls_sum hFidem (Mat.one_isIdem _ a)
    have h2 : cls (Mat.sum F (Mat.one ↥(Fund.pullAlg2 X) a)) =
        cls (Fund.clutchIdem X (n + a) u (Fund.liftOf X ↑u) (Fund.liftOf X ↑(u⁻¹))
          (Fund.liftOf_spec X (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)))
          (Fund.liftOf_spec X (↑(u⁻¹) : Matrix (Fin (n + a)) (Fin (n + a))
            C(X × Sph ℂ, ℂ)))) :=
      cls_eq_of_mvn (Mat.sum_idem hFidem (Mat.one_isIdem _ a))
        (Fund.clutchIdem_isIdem X (n + a) u (Fund.liftOf X ↑u) (Fund.liftOf X ↑(u⁻¹))
          (Fund.liftOf_spec X (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)))
          (Fund.liftOf_spec X (↑(u⁻¹) : Matrix (Fin (n + a)) (Fin (n + a))
            C(X × Sph ℂ, ℂ)))) hmvN
    have h3 : cls (Mat.one ↥(Fund.pullAlg2 X) (n + a)) =
        cls (Mat.one ↥(Fund.pullAlg2 X) n) + cls (Mat.one ↥(Fund.pullAlg2 X) a) := by
      rw [← k2_one_sum_one ↥(Fund.pullAlg2 X) n a,
        cls_sum (Mat.one_isIdem _ n) (Mat.one_isIdem _ a)]
    rw [h3, ← h2, h1]
    abel
  -- the two `κ`-values
  have hku : K0.map ((Fund.glueEquiv X) : C(X × S2, ℂ) →+* ↥(Fund.pullAlg2 X))
      (Fund.kappa X (n + a) u) =
      cls (Fund.clutchIdem X (n + a) u (Fund.liftOf X ↑u) (Fund.liftOf X ↑(u⁻¹))
        (Fund.liftOf_spec X (↑u : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf_spec X (↑(u⁻¹) : Matrix (Fin (n + a)) (Fin (n + a))
          C(X × Sph ℂ, ℂ)))) := by
    rw [Fund.kappa_val X (n + a) u]
    exact (Fund.k0Glue X).apply_symm_apply _
  have hk1 : K0.map ((Fund.glueEquiv X) : C(X × S2, ℂ) →+* ↥(Fund.pullAlg2 X))
      (Fund.kappa X (n + a) 1) = cls (Mat.one ↥(Fund.pullAlg2 X) (n + a)) := by
    rw [Fund.kappa_val X (n + a) 1]
    exact (AddEquiv.apply_symm_apply (Fund.k0Glue X)
      (cls (Fund.clutchIdem X (n + a)
        (1 : (Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ))ˣ)
        (Fund.liftOf X ↑(1 : (Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ))ˣ))
        (Fund.liftOf X ↑((1 : (Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ))ˣ)⁻¹))
        (Fund.liftOf_spec X (↑(1 : (Matrix (Fin (n + a)) (Fin (n + a))
          C(X × Sph ℂ, ℂ))ˣ) : Matrix (Fin (n + a)) (Fin (n + a)) C(X × Sph ℂ, ℂ)))
        (Fund.liftOf_spec X (↑((1 : (Matrix (Fin (n + a)) (Fin (n + a))
          C(X × Sph ℂ, ℂ))ˣ)⁻¹) : Matrix (Fin (n + a)) (Fin (n + a))
            C(X × Sph ℂ, ℂ)))))).trans (clutchIdem_one_cls X (n + a))
  -- conclude
  refine ⟨1, fun _ => n + a, fun _ => u, fun _ => (1 : ℤ), ?_⟩
  rw [Fin.sum_univ_one, one_smul]
  have hyeq : y = K0.map ((Fund.glueEquiv X) : C(X × S2, ℂ) →+* ↥(Fund.pullAlg2 X))
      (Fund.kappa X (n + a) u - Fund.kappa X (n + a) 1) := by
    rw [map_sub, hku, hk1]
    exact hyF.trans hcl
  have h2eq : K0.map ((Fund.glueEquiv X) : C(X × S2, ℂ) →+* ↥(Fund.pullAlg2 X))
      (Fund.kappa X (n + a) u - Fund.kappa X (n + a) 1) =
      K0.map ((Fund.glueEquiv X) : C(X × S2, ℂ) →+* ↥(Fund.pullAlg2 X)) z :=
    hyeq.symm.trans hy
  exact ((Fund.k0Glue X).injective h2eq).symm

end

end Work.KT
