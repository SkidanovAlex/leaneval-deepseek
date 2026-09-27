import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.SliceAux
import Submission.Work.KT.FP.pCirc_eq_of_annulus
import Submission.Work.KT.FP.pencil_local_annulus
import Submission.Work.KT.Fund.Laurent
import Submission.Work.KT.Fund.Disc
import Submission.Work.Idx.matPenProj_eval
import Submission.Work.KT.FP.wPen_isUnit_of_sum_isUnit
import Submission.Work.KT.FP.matPProj_idem
import Submission.Work.KT.FP.coeffSeq_sum_isUnit

namespace Work.KT.FP

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

/-! ## The delegated lemmas (proved in the sibling files) -/

/-! ## Slicing of the linearisation -/

lemma evalPull_eq_sliceHom (X : Type) [TopologicalSpace X] (t : unitInterval) :
    Work.KT.Idx.evalPull X t = sliceHom X t := rfl

lemma lapSlice_coeff (X : Type) [TopologicalSpace X] (t : unitInterval)
    (q : LaurentPolynomial C(X × unitInterval, ℂ)) (k : ℤ) :
    (lapSlice X t q).coeff k = sliceHom X t (q.coeff k) := by
  simp [lapSlice]

lemma reindex_map_eq {m n : Type*} (e : m ≃ n) {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (M : Matrix m m R) :
    (Matrix.reindex e e M).map f = Matrix.reindex e e (M.map f) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_map]

lemma wPenA_map_slice (X : Type) [TopologicalSpace X] (n d : ℕ) (t : unitInterval) :
    (wPenA (X × unitInterval) n d).map (sliceHom X t) = wPenA X n d := by
  ext i j
  simp only [Matrix.map_apply, wPenA]
  by_cases h : i.1 = j.1 ∧ (i.1 : ℕ) ≠ d
  · rw [if_pos h, if_pos h]
    by_cases h2 : i.2 = j.2
    · simp [Matrix.one_apply, h2]
    · simp [Matrix.one_apply, h2]
  · rw [if_neg h, if_neg h]; simp

lemma wPenB_map_slice (X : Type) [TopologicalSpace X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X × unitInterval, ℂ)) (t : unitInterval) :
    (wPenB (X × unitInterval) n d b).map (sliceHom X t)
      = wPenB X n d (fun j => (b j).map (sliceHom X t)) := by
  ext i j
  simp only [Matrix.map_apply, wPenB]
  by_cases h : (i.1 : ℕ) + 1 = (j.1 : ℕ)
  · rw [if_pos h, if_pos h]
    by_cases h2 : (i.1 : ℕ) = d
    · simp [h2]
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : i.2 = j.2
      · simp [Matrix.one_apply, h3]
      · simp [Matrix.one_apply, h3]
  · rw [if_neg h, if_neg h]
    by_cases h2 : (i.1 : ℕ) = d
    · simp [h2]
    · rw [if_neg h2, if_neg h2]; simp

lemma coeffSeq_map_slice (X : Type) [TopologicalSpace X] (n m : ℕ)
    (Q : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X × unitInterval, ℂ)))
    (t : unitInterval) (j : Fin (2 * m + 1)) :
    (coeffSeq (X × unitInterval) n m Q j).map (sliceHom X t)
      = coeffSeq X n m (matSlice X t Q) j := by
  ext a c
  simp only [Matrix.map_apply, coeffSeq, matSlice, lapSlice, AddMonoidAlgebra.coeff_ofCoeff,
    Finsupp.mapRange_apply]

lemma linAf_map_slice (X : Type) [TopologicalSpace X] (n m : ℕ) (t : unitInterval) :
    (linAf (X × unitInterval) n m).map (sliceHom X t) = linAf X n m := by
  unfold linAf wPenAf
  rw [reindex_map_eq, wPenA_map_slice]

lemma linBf_map_slice (X : Type) [TopologicalSpace X] (n m : ℕ)
    (Q : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X × unitInterval, ℂ)))
    (t : unitInterval) :
    (linBf (X × unitInterval) n m Q).map (sliceHom X t)
      = linBf X n m (matSlice X t Q) := by
  have hb : (fun j : Fin (2 * m + 1) =>
        (coeffSeq (X × unitInterval) n m Q j).map (sliceHom X t))
      = coeffSeq X n m (matSlice X t Q) := by
    funext j
    exact coeffSeq_map_slice X n m Q t j
  unfold linBf wPenBf
  rw [reindex_map_eq, wPenB_map_slice, hb]

/-! ## Slicing of the pencil projection -/

lemma slice_matPProj (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (N : ℕ) (A B : Matrix (Fin N) (Fin N) C(X × unitInterval, ℂ)) (t : unitInterval)
    (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    (matPProj (X × unitInterval) N A B 1).map (sliceHom X t)
      = matPProj X N (A.map (sliceHom X t)) (B.map (sliceHom X t)) 1 := by
  have h := Work.Idx.matPenProj_eval X A B t hunit
  exact h

/-! ## Deformation of the pencil projection in the radius -/

lemma pProj_deform {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (A B : R) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • A + B)) :
    pProj A B ρ = pProj A B 1 := by
  unfold pProj
  rw [pCirc_eq_of_annulus A B hρ0 hρ1 hunit]

lemma matPProj_deform (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (N : ℕ) (A B : Matrix (Fin N) (Fin N) C(X, ℂ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hunit : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • A + B)) :
    matPProj X N A B ρ = matPProj X N A B 1 :=
  @pProj_deform (Matrix (Fin N) (Fin N) C(X, ℂ)) (Matrix.linftyOpNormedRing)
    (Matrix.linftyOpNormedAlgebra) (Matrix.instCompleteSpace (Fin N) (Fin N) C(X, ℂ))
    A B ρ hρ0 hρ1 hunit

/-! ## The invertibility of the linearised pencil -/

theorem linPencil_isUnit (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n m : ℕ) (Q : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    (hb : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (Q i j).coeff k = 0)
    (hunit : IsUnit (Q.map (Work.KT.laurentMap X))) {z : ℂ} (hz : ‖z‖ = 1) :
    IsUnit (z • linAf X n m + linBf X n m Q) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; norm_num at hz
  have h := wPen_isUnit_of_sum_isUnit X n (2 * m) (coeffSeq X n m Q) hz0
    (coeffSeq_sum_isUnit X n m Q hb hunit hz)
  simpa only [linAf, linBf] using h

/-! ## Continuity of the sliced projection -/

def swapTI (X : Type) [TopologicalSpace X] : C(unitInterval × X, X × unitInterval) where
  toFun p := (p.2, p.1)
  continuous_toFun := by fun_prop

lemma continuous_map_evalPull (X : Type) [TopologicalSpace X] {N : ℕ}
    (P : Matrix (Fin N) (Fin N) C(X × unitInterval, ℂ)) :
    Continuous (fun t : unitInterval => P.map (Work.KT.Idx.evalPull X t)) := by
  apply continuous_matrix
  intro i j
  have h : (fun t : unitInterval => (P.map (Work.KT.Idx.evalPull X t)) i j)
      = ⇑(((P i j).comp (swapTI X)).curry) := by
    funext t
    ext x
    simp [Matrix.map_apply, swapTI, ContinuousMap.curry_apply, Work.KT.Idx.evalPull, pullAlg,
      ContinuousMap.compStarAlgHom'_apply]
  rw [h]
  exact (((P i j).comp (swapTI X)).curry).continuous

/-! ## The main theorem -/

theorem lindAt_slice_eq (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n m : ℕ) (Q : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X × unitInterval, ℂ)))
    (hbound : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (Q i j).coeff k = 0)
    (hunit : IsUnit (Q.map (Work.KT.laurentMap (X × unitInterval))))
    {ρ₀ ρ₁ : ℝ} (hρ₀0 : 0 < ρ₀) (hρ₀1 : ρ₀ ≤ 1) (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ ≤ 1)
    (h₀ : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • linAf X n m + linBf X n m (matSlice X 0 Q)))
    (h₁ : ∀ z : ℂ, ρ₁ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • linAf X n m + linBf X n m (matSlice X 1 Q))) :
    lindAt X n m (matSlice X 0 Q) ρ₀ = lindAt X n m (matSlice X 1 Q) ρ₁ := by
  -- the pencil over the cylinder is invertible on the unit circle
  have hinv : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (z • linAf (X × unitInterval) n m + linBf (X × unitInterval) n m Q) :=
    fun z hz => linPencil_isUnit (X × unitInterval) n m Q hbound hunit hz
  -- its Riesz projection is idempotent
  have hidem : matPProj (X × unitInterval) ((2 * m + 1) * n)
        (linAf (X × unitInterval) n m) (linBf (X × unitInterval) n m Q) 1 *
      matPProj (X × unitInterval) ((2 * m + 1) * n)
        (linAf (X × unitInterval) n m) (linBf (X × unitInterval) n m Q) 1
      = matPProj (X × unitInterval) ((2 * m + 1) * n)
        (linAf (X × unitInterval) n m) (linBf (X × unitInterval) n m Q) 1 :=
    matPProj_idem (X × unitInterval) _ _ (ρ := 1) (by norm_num) le_rfl
      (fun z hz1 hz2 => hinv z (le_antisymm hz2 hz1))
  -- the resulting path of idempotents over `X`
  let Pg : Matrix (Fin ((2 * m + 1) * n)) (Fin ((2 * m + 1) * n)) C(X × unitInterval, ℂ) :=
    matPProj (X × unitInterval) ((2 * m + 1) * n)
      (linAf (X × unitInterval) n m) (linBf (X × unitInterval) n m Q) 1
  let γ : unitInterval → Matrix (Fin ((2 * m + 1) * n)) (Fin ((2 * m + 1) * n)) C(X, ℂ) :=
    fun t => Pg.map (Work.KT.Idx.evalPull X t)
  have hidemP : Pg * Pg = Pg := hidem
  have hγ : Continuous γ := continuous_map_evalPull X Pg
  have hidemγ : ∀ t, γ t * γ t = γ t := by
    intro t
    dsimp only [γ]
    rw [← Matrix.map_mul, hidemP]
  have hpath := Work.KT.Fund.cls_eq_of_path (C(X, ℂ)) γ hγ hidemγ
  -- identify the two ends of the path
  have hγ0 : γ 0 = matPProj X ((2 * m + 1) * n) (linAf X n m)
      (linBf X n m (matSlice X 0 Q)) 1 := by
    dsimp only [γ, Pg]
    rw [evalPull_eq_sliceHom, slice_matPProj X _ _ _ 0 hinv, linAf_map_slice, linBf_map_slice]
  have hγ1 : γ 1 = matPProj X ((2 * m + 1) * n) (linAf X n m)
      (linBf X n m (matSlice X 1 Q)) 1 := by
    dsimp only [γ, Pg]
    rw [evalPull_eq_sliceHom, slice_matPProj X _ _ _ 1 hinv, linAf_map_slice, linBf_map_slice]
  have hcls : cls (⟨(2 * m + 1) * n, matPProj X ((2 * m + 1) * n) (linAf X n m)
        (linBf X n m (matSlice X 0 Q)) 1⟩ : Mat C(X, ℂ))
      = cls (⟨(2 * m + 1) * n, matPProj X ((2 * m + 1) * n) (linAf X n m)
        (linBf X n m (matSlice X 1 Q)) 1⟩ : Mat C(X, ℂ)) := by
    rw [hγ0, hγ1] at hpath
    exact hpath
  -- deformation in the radius
  have hdef0 : matPProj X ((2 * m + 1) * n) (linAf X n m) (linBf X n m (matSlice X 0 Q)) ρ₀
      = matPProj X ((2 * m + 1) * n) (linAf X n m) (linBf X n m (matSlice X 0 Q)) 1 :=
    matPProj_deform X _ _ _ hρ₀0 hρ₀1 h₀
  have hdef1 : matPProj X ((2 * m + 1) * n) (linAf X n m) (linBf X n m (matSlice X 1 Q)) ρ₁
      = matPProj X ((2 * m + 1) * n) (linAf X n m) (linBf X n m (matSlice X 1 Q)) 1 :=
    matPProj_deform X _ _ _ hρ₁0 hρ₁1 h₁
  unfold lindAt
  rw [hdef0, hdef1, hcls]

end

end Work.KT.FP
