import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one
import Submission.Commons.LinearAlgebra.Matrix.sigPos_toQuadraticForm_eq_card_pos_roots

namespace Commons.LinearAlgebra.Matrix


set_option autoImplicit false

/-- Coordinates of a vector in the eigenbasis of the symmetric matrix `A`. -/
private noncomputable def eigenCoord {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ((symmBasis A hA).repr (WithLp.toLp 2 x)).ofLp i

/-- `quadReal A x y` expressed in the eigenbasis of `A`. -/
private lemma quadReal_eq_eigen_coord_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (x y : Fin n → ℝ) :
    quadReal A x y = ∑ i : Fin n, symmEigenvalues A hA i *
      (eigenCoord A hA x i * eigenCoord A hA y i) := by
  simpa [eigenCoord] using quadReal_eq_eigen_sum' A hA x y

/-- Every choice of eigen-coordinates is realized by some vector. -/
private lemma exists_vector_of_coord {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (a : Fin n → ℝ) :
    ∃ v : Fin n → ℝ, ∀ i : Fin n, eigenCoord A hA v i = a i := by
  classical
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := symmBasis A hA
  let ev : EuclideanSpace ℝ (Fin n) := b.repr.symm (WithLp.toLp 2 a)
  let v : Fin n → ℝ := fun i => ev.ofLp i
  refine ⟨v, ?_⟩
  intro i
  have htoLp : WithLp.toLp 2 v = ev := by
    apply (WithLp.ext_iff (p := 2)).mpr
    funext j
    simp [v, ev]
  have hcoord : ((symmBasis A hA).repr (WithLp.toLp 2 v)).ofLp i = a i := by
    rw [htoLp]
    simp [b, ev]
  simpa [eigenCoord] using hcoord

theorem negDef_ker_pos_implies_strict (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (e : Fin n → ℝ)
    (hpos : 0 < Commons.LinearAlgebra.Matrix.quadReal A e e)
    (hker : ∀ v : Fin n → ℝ, Commons.LinearAlgebra.Matrix.quadReal A e v = 0 →
      v = 0 ∨ Commons.LinearAlgebra.Matrix.quadReal A v v < 0) :
    IsUnit A ∧ (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1 := by
  classical
  constructor
  · -- `A` acts injectively, hence is a unit.
    have hker_triv : ∀ x : Fin n → ℝ, A.mulVec x = 0 → x = 0 := by
      intro x hx
      by_contra hxne
      have hqe : quadReal A e x = 0 := by
        rw [quadReal_mulVec, hx]
        simp
      have hqx : quadReal A x x = 0 := by
        rw [quadReal_mulVec, hx]
        simp
      rcases hker x hqe with hvz | hvneg
      · exact hxne hvz
      · linarith
    exact Matrix.mulVec_injective_iff_isUnit.mp (by
      intro x y hxy
      exact sub_eq_zero.mp (hker_triv (x - y) (by
        rw [Matrix.mulVec_sub]
        exact sub_eq_zero.mpr hxy)))
  · -- The characteristic polynomial of `A` has exactly one positive root.
    have hsum_pos : 0 < ∑ i : Fin n,
        symmEigenvalues A hA i * (eigenCoord A hA e i * eigenCoord A hA e i) := by
      rw [← quadReal_eq_eigen_coord_sum A hA e e]
      exact hpos
    -- at least one positive eigenvalue
    have hpos_lam : ∃ i : Fin n, 0 < symmEigenvalues A hA i := by
      by_contra h
      have hnonpos : ∀ i : Fin n, symmEigenvalues A hA i ≤ 0 := by
        intro i
        exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
      have hsum_nonpos : (∑ i : Fin n,
          symmEigenvalues A hA i * (eigenCoord A hA e i * eigenCoord A hA e i)) ≤ 0 := by
        apply Finset.sum_nonpos
        intro i hi
        exact mul_nonpos_of_nonpos_of_nonneg (hnonpos i) (mul_self_nonneg (eigenCoord A hA e i))
      linarith
    have hcard_ge_one : 1 ≤ (Finset.univ.filter (fun i : Fin n => 0 < symmEigenvalues A hA i)).card := by
      rcases hpos_lam with ⟨i, hi⟩
      exact (Finset.one_le_card).mpr ⟨i, by simp [hi]⟩
    -- at most one positive eigenvalue
    have hcard_le_one : (Finset.univ.filter (fun i : Fin n => 0 < symmEigenvalues A hA i)).card ≤ 1 := by
      by_contra hnot
      have hge2 : 2 ≤ (Finset.univ.filter (fun i : Fin n => 0 < symmEigenvalues A hA i)).card := by
        omega
      obtain ⟨a, hcross, hpos_a⟩ :=
        exists_coord_cross_zero_of_two_pos (symmEigenvalues A hA) (eigenCoord A hA e) hge2
      obtain ⟨v, hcoord_v⟩ := exists_vector_of_coord A hA a
      have hq_ev : quadReal A e v = 0 := by
        rw [quadReal_symm A hA e v]
        calc
          quadReal A v e = ∑ i : Fin n, symmEigenvalues A hA i *
              (eigenCoord A hA v i * eigenCoord A hA e i) :=
                quadReal_eq_eigen_coord_sum A hA v e
          _ = ∑ i : Fin n, symmEigenvalues A hA i * (a i * eigenCoord A hA e i) := by
                simp_rw [hcoord_v]
          _ = 0 := hcross
      have hq_vv : quadReal A v v = ∑ i : Fin n, symmEigenvalues A hA i * (a i * a i) := by
        calc
          quadReal A v v = ∑ i : Fin n, symmEigenvalues A hA i *
              (eigenCoord A hA v i * eigenCoord A hA v i) :=
                quadReal_eq_eigen_coord_sum A hA v v
          _ = ∑ i : Fin n, symmEigenvalues A hA i * (a i * a i) := by
                simp_rw [hcoord_v]
      have hposvv : 0 < quadReal A v v := by
        rw [hq_vv]
        exact hpos_a
      rcases hker v hq_ev with hvz | hvneg
      · have hvv0 : quadReal A v v = 0 := by
          rw [hvz]
          simp [quadReal]
        linarith
      · linarith
    have hcard_eq : (Finset.univ.filter (fun i : Fin n => 0 < symmEigenvalues A hA i)).card = 1 := by
      omega
    rw [charpoly_positive_roots_card_eq A hA]
    change (Finset.univ.filter (fun i : Fin n => 0 < symmEigenvalues A hA i)).card = 1
    exact hcard_eq

end Commons.LinearAlgebra.Matrix
