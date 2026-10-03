import Mathlib
import Submission.Work.ORHughesFree.Epic.DimTheory
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin
import Submission.Work.ORHughesFree.Epic.rk_blkM_zero_C_one
import Submission.Work.ORHughesFree.Epic.rk_blkM_eq_of_relations

set_option autoImplicit false
set_option maxHeartbeats 2000000

universe u

namespace Work.ORHughesFree.Epic

open Matrix

variable {R : Type u} [Ring R]

/-! ## The row map of a matrix -/

theorem fpAux_rowMulLin_single {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) (i : Fin a) :
    rowMulLin M (Pi.single i 1) = M i := by
  ext j
  show (∑ l, (Pi.single i (1 : R) : Fin a → R) l * M l j) = M i j
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Pi.single_apply, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem fpAux_rowMulLin_mul {a b c : ℕ} (M : Matrix (Fin a) (Fin b) R) (N : Matrix (Fin b) (Fin c) R) :
    rowMulLin (M * N) = (rowMulLin N).comp (rowMulLin M) := by
  refine LinearMap.ext fun v => ?_
  refine funext fun j => ?_
  show (∑ i, v i * (∑ k, M i k * N k j)) = ∑ k, (∑ i, v i * M i k) * N k j
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc]

/-- The expansion of a vector in the standard basis. -/
theorem fpAux_eq_sum_smul_single {a : ℕ} (v : Fin a → R) :
    v = ∑ i, v i • (Pi.single i (1 : R) : Fin a → R) := by
  ext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Pi.single_apply, if_neg (Ne.symm hb), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The matrix of a linear map `(Fin a → R) →ₗ (Fin b → R)`: its `i`-th row is the image of
the `i`-th standard basis vector. -/
noncomputable def fpAux_matOf {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    Matrix (Fin a) (Fin b) R :=
  fun i j => f (Pi.single i 1) j

theorem fpAux_rowMulLin_matOf {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    rowMulLin (fpAux_matOf f) = f := by
  refine LinearMap.ext fun v => ?_
  refine funext fun j => ?_
  show (∑ i, v i * f (Pi.single i (1 : R)) j) = f v j
  conv_rhs => rw [fpAux_eq_sum_smul_single v]
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem fpAux_matOf_rowMulLin {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) :
    fpAux_matOf (rowMulLin M) = M := by
  ext i j
  simp only [fpAux_matOf]
  rw [fpAux_rowMulLin_single]

theorem fpAux_matOf_sub {a b : ℕ} (f g : (Fin a → R) →ₗ[R] (Fin b → R)) :
    fpAux_matOf (f - g) = fpAux_matOf f - fpAux_matOf g := by
  ext i j
  simp [fpAux_matOf, LinearMap.sub_apply, Matrix.sub_apply]

theorem fpAux_matOf_id (b : ℕ) :
    fpAux_matOf (LinearMap.id : (Fin b → R) →ₗ[R] (Fin b → R)) = 1 := by
  ext i j
  simp [fpAux_matOf, Matrix.one_apply, Pi.single_apply, eq_comm]

/-- If the range of `f` is contained in the range of `rowMulLin M`, then `f` is given by right
multiplication by `M` composed with a matrix. -/
theorem fpAux_exists_eq_mul_of_range_le {a b c : ℕ} (f : (Fin a → R) →ₗ[R] (Fin c → R))
    (M : Matrix (Fin b) (Fin c) R) (h : LinearMap.range f ≤ LinearMap.range (rowMulLin M)) :
    ∃ Z : Matrix (Fin a) (Fin b) R, fpAux_matOf f = Z * M := by
  have hz : ∀ i : Fin a, ∃ z : Fin b → R, rowMulLin M z = f (Pi.single i 1) := fun i =>
    LinearMap.mem_range.mp (h (LinearMap.mem_range.mpr ⟨Pi.single i 1, rfl⟩))
  choose z hz' using hz
  refine ⟨fun i => z i, ?_⟩
  ext i j
  simp only [fpAux_matOf]
  rw [← congrFun (hz' i) j]
  rfl

/-- The Sylvester rank of a matrix depends only on its row space. -/
theorem fpAux_rk_eq_of_range_eq {a b c : ℕ} (rk : SylvesterRank R)
    (A : Matrix (Fin a) (Fin c) R) (B : Matrix (Fin b) (Fin c) R)
    (h : LinearMap.range (rowMulLin A) = LinearMap.range (rowMulLin B)) :
    rk.rk a c A = rk.rk b c B := by
  refine le_antisymm ?_ ?_
  · obtain ⟨Z, hZ⟩ := fpAux_exists_eq_mul_of_range_le (rowMulLin A) B h.le
    have hA : A = Z * B := by rw [← hZ, fpAux_matOf_rowMulLin]
    rw [hA]
    exact rk.rk_mul_le_right Z B
  · obtain ⟨Z, hZ⟩ := fpAux_exists_eq_mul_of_range_le (rowMulLin B) A h.ge
    have hB : B = Z * A := by rw [← hZ, fpAux_matOf_rowMulLin]
    rw [hB]
    exact rk.rk_mul_le_right Z A

/-! ## Invariance of `n - rk A` under change of presentation -/

/-- Any two matrices over `R` with isomorphic cokernels have the same value `n - rk A`, where
`n` is the number of columns.  This is the well-definedness of the dimension attached to a
Sylvester rank function ([JZLA20, §2.4]). -/
theorem sub_eq_of_coker_equiv {m n m' n' : ℕ} (rk : SylvesterRank R)
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin m') (Fin n') R)
    (q : cokerMat A ≃ₗ[R] cokerMat B) :
    (n : ℝ) - rk.rk m n A = (n' : ℝ) - rk.rk m' n' B := by
  obtain ⟨β, hβ⟩ := Module.projective_lifting_property (P := (Fin n' → R))
    (Submodule.mkQ (LinearMap.range (rowMulLin A)))
    (q.symm.toLinearMap.comp (Submodule.mkQ (LinearMap.range (rowMulLin B))))
    (Submodule.mkQ_surjective _)
  obtain ⟨γ, hγ⟩ := Module.projective_lifting_property (P := (Fin n → R))
    (Submodule.mkQ (LinearMap.range (rowMulLin B)))
    (q.toLinearMap.comp (Submodule.mkQ (LinearMap.range (rowMulLin A))))
    (Submodule.mkQ_surjective _)
  let P : Matrix (Fin n') (Fin n) R := fpAux_matOf β
  let G : Matrix (Fin n) (Fin n') R := fpAux_matOf γ
  have hβP : rowMulLin P = β := fpAux_rowMulLin_matOf β
  have hγG : rowMulLin G = γ := fpAux_rowMulLin_matOf γ
  have hmatβ : fpAux_matOf (β.comp (rowMulLin B)) = B * P := by
    rw [← hβP, ← fpAux_rowMulLin_mul]
    exact fpAux_matOf_rowMulLin (B * P)
  have hmatγ : fpAux_matOf (γ.comp (rowMulLin A)) = A * G := by
    rw [← hγG, ← fpAux_rowMulLin_mul]
    exact fpAux_matOf_rowMulLin (A * G)
  have hmatβγ : fpAux_matOf (β.comp γ) = G * P := by
    rw [← hβP, ← hγG, ← fpAux_rowMulLin_mul]
    exact fpAux_matOf_rowMulLin (G * P)
  have hmatγβ : fpAux_matOf (γ.comp β) = P * G := by
    rw [← hγG, ← hβP, ← fpAux_rowMulLin_mul]
    exact fpAux_matOf_rowMulLin (P * G)
  have hmkQsub : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) R),
      (Submodule.mkQ (LinearMap.range (rowMulLin M))).comp (rowMulLin M) = 0 := by
    intro a b M
    refine LinearMap.ext fun v => ?_
    show Submodule.mkQ (LinearMap.range (rowMulLin M)) (rowMulLin M v) = 0
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact ⟨v, rfl⟩
  have hqβγ : (Submodule.mkQ (LinearMap.range (rowMulLin A))).comp (β.comp γ)
      = Submodule.mkQ (LinearMap.range (rowMulLin A)) := by
    have hs : (q.symm.toLinearMap).comp q.toLinearMap = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      exact q.symm_apply_apply x
    rw [← LinearMap.comp_assoc, hβ, LinearMap.comp_assoc, hγ, ← LinearMap.comp_assoc, hs,
      LinearMap.id_comp]
  have hqγα : (Submodule.mkQ (LinearMap.range (rowMulLin B))).comp (γ.comp β)
      = Submodule.mkQ (LinearMap.range (rowMulLin B)) := by
    have hs : (q.toLinearMap).comp q.symm.toLinearMap = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      exact q.apply_symm_apply x
    rw [← LinearMap.comp_assoc, hγ, LinearMap.comp_assoc, hβ, ← LinearMap.comp_assoc, hs,
      LinearMap.id_comp]
  have h1 : ∃ W : Matrix (Fin m') (Fin m) R, B * P = W * A := by
    obtain ⟨W, hW⟩ := fpAux_exists_eq_mul_of_range_le (β.comp (rowMulLin B)) A (by
      rw [← Submodule.ker_mkQ (LinearMap.range (rowMulLin A)), LinearMap.range_le_ker_iff,
        ← LinearMap.comp_assoc, hβ, LinearMap.comp_assoc, hmkQsub, LinearMap.comp_zero])
    exact ⟨W, by rw [← hmatβ]; exact hW⟩
  have h2 : ∃ Z : Matrix (Fin n) (Fin m) R, G * P = 1 + Z * A := by
    obtain ⟨Z, hZ⟩ := fpAux_exists_eq_mul_of_range_le (β.comp γ - LinearMap.id) A (by
      rw [← Submodule.ker_mkQ (LinearMap.range (rowMulLin A)), LinearMap.range_le_ker_iff]
      refine LinearMap.ext fun x => ?_
      have hx : Submodule.mkQ (LinearMap.range (rowMulLin A)) (β (γ x))
          = Submodule.mkQ (LinearMap.range (rowMulLin A)) x := by
        simpa [LinearMap.comp_apply] using DFunLike.congr_fun hqβγ x
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.zero_apply]
      rw [map_sub, hx, sub_self])
    refine ⟨Z, ?_⟩
    have hmat : fpAux_matOf (β.comp γ - LinearMap.id) = G * P - 1 := by
      rw [fpAux_matOf_sub, hmatβγ, fpAux_matOf_id]
    have hGP : G * P - 1 = Z * A := by rw [← hmat, hZ]
    rw [← hGP]
    abel
  have h3 : ∃ X : Matrix (Fin m) (Fin m') R, A * G = X * B := by
    obtain ⟨X, hX⟩ := fpAux_exists_eq_mul_of_range_le (γ.comp (rowMulLin A)) B (by
      rw [← Submodule.ker_mkQ (LinearMap.range (rowMulLin B)), LinearMap.range_le_ker_iff,
        ← LinearMap.comp_assoc, hγ, LinearMap.comp_assoc, hmkQsub, LinearMap.comp_zero])
    exact ⟨X, by rw [← hmatγ]; exact hX⟩
  have h4 : ∃ Z' : Matrix (Fin n') (Fin m') R, P * G = 1 + Z' * B := by
    obtain ⟨Z', hZ'⟩ := fpAux_exists_eq_mul_of_range_le (γ.comp β - LinearMap.id) B (by
      rw [← Submodule.ker_mkQ (LinearMap.range (rowMulLin B)), LinearMap.range_le_ker_iff]
      refine LinearMap.ext fun x => ?_
      have hx : Submodule.mkQ (LinearMap.range (rowMulLin B)) (γ (β x))
          = Submodule.mkQ (LinearMap.range (rowMulLin B)) x := by
        simpa [LinearMap.comp_apply] using DFunLike.congr_fun hqγα x
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.zero_apply]
      rw [map_sub, hx, sub_self])
    refine ⟨Z', ?_⟩
    have hmat : fpAux_matOf (γ.comp β - LinearMap.id) = P * G - 1 := by
      rw [fpAux_matOf_sub, hmatγβ, fpAux_matOf_id]
    have hPG : P * G - 1 = Z' * B := by rw [← hmat, hZ']
    rw [← hPG]
    abel
  have hT : rk.rk (m + n') (n + n')
      ((Matrix.fromBlocks A 0 P (1 : Matrix (Fin n') (Fin n') R)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm) = rk.rk m n A + (n' : ℝ) :=
    rk_blkM_zero_C_one rk A P
  have hS : rk.rk (m' + n) (n' + n)
      ((Matrix.fromBlocks B 0 G (1 : Matrix (Fin n) (Fin n) R)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm) = rk.rk m' n' B + (n : ℝ) :=
    rk_blkM_zero_C_one rk B G
  have hE := rk_blkM_eq_of_relations rk A B P G h1 h2 h3 h4
  have hsum : rk.rk m n A + (n' : ℝ) = rk.rk m' n' B + (n : ℝ) := by
    rw [← hT, hE, hS]
  linarith

theorem fpDim_eq_of_presentation {R : Type u} [Ring R] (rk : Work.ORHughesFree.SylvesterRank R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) (e : Work.ORHughesFree.Epic.cokerMat A ≃ₗ[R] M) :
    Work.ORHughesFree.Epic.fpDim rk M = (n : ℝ) - rk.rk m n A := by
  unfold fpDim
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨(n : ℝ) - rk.rk m n A, m, n, A, ⟨e⟩, rfl⟩ ?_
    rintro x ⟨m₁, n₁, B, ⟨e₁⟩, rfl⟩
    exact le_of_eq (sub_eq_of_coker_equiv rk B A (e₁.trans e.symm))
  · refine le_csSup ⟨(n : ℝ) - rk.rk m n A, ?_⟩ ⟨m, n, A, ⟨e⟩, rfl⟩
    rintro x ⟨m₁, n₁, B, ⟨e₁⟩, rfl⟩
    exact le_of_eq (sub_eq_of_coker_equiv rk B A (e₁.trans e.symm))

end Work.ORHughesFree.Epic
