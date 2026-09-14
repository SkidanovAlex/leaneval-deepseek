import Mathlib
import Submission.Subspace.RealRank.Wedge
open Matrix
open scoped BigOperators

namespace Submission.Subspace.RealRank

variable {N : ℕ}

/-- The index type of the compound matrix (the spelling used by the commons `compound`). -/
abbrev Idx (N r : ℕ) : Type := {U : Finset (Fin N) // U.card = r}

/-- Bridge between the two spellings of the index type. -/
lemma sum_subtype_eq_sum_powersetCard {N r : ℕ} {M : Type*} [AddCommMonoid M]
    (g : Set.powersetCard (Fin N) r → M) :
    (∑ T : Set.powersetCard (Fin N) r, g T) = ∑ T : Idx N r, g T := by
  refine Finset.sum_bij (fun (T : Set.powersetCard (Fin N) r) _ => (T : Idx N r)) ?_ ?_ ?_ ?_
  · intro T _; exact Finset.mem_univ _
  · intro T _ T' _ h; exact Subtype.ext (congrArg Subtype.val h)
  · intro T' _; exact ⟨(T' : Set.powersetCard (Fin N) r), Finset.mem_univ _, Subtype.ext rfl⟩
  · intro T _; rfl

/-- **The value of a compound form on a wedge vector** (Cauchy–Binet). -/
theorem compound_wedge_value (r : ℕ) (M V : Matrix (Fin N) (Fin N) ℝ)
    (S T : Idx N r) :
    (∑ S' : Idx N r, (Commons.LinearAlgebra.Matrix.compound r M) T S' *
        (Commons.LinearAlgebra.Matrix.compound r V) S' S)
      = (Commons.LinearAlgebra.Matrix.compound r (M * V)) T S := by
  rw [Commons.LinearAlgebra.Matrix.compound_mul]
  exact (Matrix.mul_apply (M := Commons.LinearAlgebra.Matrix.compound r M)
    (N := Commons.LinearAlgebra.Matrix.compound r V)).symm

/-- **The rpow form of the Leibniz bound.** -/
theorem compound_entry_le_rpow {r : ℕ} (M V : Matrix (Fin N) (Fin N) ℝ)
    (lam c : Fin N → ℝ) {Q C : ℝ} (hQ : 1 < Q) (hC : 0 < C) (hlam : ∀ t, 0 < lam t)
    (hbound : ∀ t j : Fin N,
      |∑ i, M t i * V i j| ≤ C * min (lam t) (lam j) * Q ^ (c t))
    (T S : Idx N r) :
    |(Commons.LinearAlgebra.Matrix.compound r (M * V)) T S| ≤
      Q ^ ((∑ a : Fin r, c (T.1.orderEmbOfFin T.2 a)) +
        Real.log (Nat.factorial r * C ^ r *
          ∏ a : Fin r, lam (T.1.orderEmbOfFin T.2 a)) / Real.log Q) := by
  classical
  have hQpos : 0 < Q := by linarith
  have hQlog : 0 < Real.log Q := Real.log_pos (by linarith)
  have h1 := compound_det_abs_le M V lam c Q C hQpos (le_of_lt hC)
    (fun t => le_of_lt (hlam t)) hbound T.1 S.1 T.2 S.2
  have h2 : (Commons.LinearAlgebra.Matrix.compound r (M * V)) T S
      = ((M * V).submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2)).det := rfl
  rw [h2]
  refine h1.trans ?_
  set K0 : ℝ := (Nat.factorial r : ℝ) * C ^ r *
    ∏ a : Fin r, lam (T.1.orderEmbOfFin T.2 a) with hK0
  have hK : 0 < K0 := by
    rw [hK0]
    exact mul_pos (mul_pos (by positivity) (pow_pos hC r))
      (Finset.prod_pos (fun a _ => hlam _))
  have hQK : Q ^ (Real.log K0 / Real.log Q) = K0 := by
    rw [Real.rpow_def_of_pos hQpos,
      show Real.log Q * (Real.log K0 / Real.log Q) = Real.log K0 from by field_simp]
    exact Real.exp_log hK
  have hX : Q ^ ((∑ a : Fin r, c (T.1.orderEmbOfFin T.2 a)) + Real.log K0 / Real.log Q)
      = Q ^ (∑ a : Fin r, c (T.1.orderEmbOfFin T.2 a)) * K0 := by
    rw [Real.rpow_add hQpos, hQK]
  rw [hX, hK0]
  exact le_of_eq (by ring)

/-- **The sharpened rpow bound at the top index set.** -/
theorem compound_entry_le_rpow_sharp {r : ℕ} (M V : Matrix (Fin N) (Fin N) ℝ)
    (lam c : Fin N → ℝ) {Q C : ℝ} (hQ : 1 < Q) (hC : 0 < C) (hlam : ∀ t, 0 < lam t)
    (hbound : ∀ t j : Fin N,
      |∑ i, M t i * V i j| ≤ C * min (lam t) (lam j) * Q ^ (c t))
    (T S : Finset (Fin N)) (hT : T.card = r) (hS : S.card = r)
    (low high : ℝ) (hlow : 0 < low) (hhigh : 0 < high)
    (hTlow : ∀ a : Fin r, low ≤ lam (T.orderEmbOfFin hT a))
    (hShigh : ∃ s ∈ S, lam s ≤ high) :
    |((M * V).submatrix (T.orderEmbOfFin hT) (S.orderEmbOfFin hS)).det| ≤
      Q ^ ((∑ a : Fin r, c (T.orderEmbOfFin hT a)) +
        Real.log (Nat.factorial r * C ^ r * (high / low) *
          ∏ a : Fin r, lam (T.orderEmbOfFin hT a)) / Real.log Q) := by
  classical
  have hQpos : 0 < Q := by linarith
  have hQlog : 0 < Real.log Q := Real.log_pos (by linarith)
  have h1 := compound_det_abs_le_sharp M V lam c Q C hQpos (le_of_lt hC)
    (fun t => le_of_lt (hlam t)) hbound T S hT hS low high hlow hTlow hShigh
  refine h1.trans ?_
  set K0 : ℝ := (Nat.factorial r : ℝ) * C ^ r * (high / low) *
    ∏ a : Fin r, lam (T.orderEmbOfFin hT a) with hK0
  have hK : 0 < K0 := by
    rw [hK0]
    exact mul_pos (mul_pos (mul_pos (by positivity) (pow_pos hC r)) (div_pos hhigh hlow))
      (Finset.prod_pos (fun a _ => hlam _))
  have hQK : Q ^ (Real.log K0 / Real.log Q) = K0 := by
    rw [Real.rpow_def_of_pos hQpos,
      show Real.log Q * (Real.log K0 / Real.log Q) = Real.log K0 from by field_simp]
    exact Real.exp_log hK
  have hX : Q ^ ((∑ a : Fin r, c (T.orderEmbOfFin hT a)) + Real.log K0 / Real.log Q)
      = Q ^ (∑ a : Fin r, c (T.orderEmbOfFin hT a)) * K0 := by
    rw [Real.rpow_add hQpos, hQK]
  rw [hX, hK0]
  exact le_of_eq (by ring)

/-- The compound of the realification of an integer matrix is the realification of the compound
(entrywise application of `RingHom.map_det`). -/
lemma compound_map_intCast_apply (r : ℕ) (V : Matrix (Fin N) (Fin N) ℤ) (T S : Idx N r) :
    ((Commons.LinearAlgebra.Matrix.compound r V) T S : ℝ)
      = Commons.LinearAlgebra.Matrix.compound r (V.map (Int.castRingHom ℝ)) T S := by
  rw [Commons.LinearAlgebra.Matrix.compound, Commons.LinearAlgebra.Matrix.compound,
    Matrix.of_apply, Matrix.of_apply, Matrix.submatrix_map, ← RingHom.mapMatrix_apply]
  exact RingHom.map_det (Int.castRingHom ℝ) _

/-- **The wedge vectors lie in the compound box.** -/
theorem wedgeVec_mem_box {N r : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (V : Matrix (Fin N) (Fin N) ℤ) (lam c : Fin N → ℝ)
    {Q C : ℝ} (hQ : 1 < Q) (hC : 0 < C) (hlam : ∀ t, 0 < lam t)
    (hbound : ∀ t j : Fin N,
      |∑ i, M t i * (V i j : ℝ)| ≤ C * min (lam t) (lam j) * Q ^ (c t))
    (Tstar : Idx N r) (low high : ℝ) (hlow : 0 < low) (hhigh : 0 < high)
    (hTlow : ∀ a : Fin r, low ≤ lam (Tstar.1.orderEmbOfFin Tstar.2 a))
    (hShigh : ∀ S : Idx N r, S ≠ Tstar → ∃ s ∈ S.1, lam s ≤ high)
    (xbar : Idx N r → ℝ)
    (hx1 : ∀ T : Idx N r, T ≠ Tstar →
      (∑ a : Fin r, c (T.1.orderEmbOfFin T.2 a)) +
        Real.log (Nat.factorial r * C ^ r *
          ∏ a : Fin r, lam (T.1.orderEmbOfFin T.2 a)) / Real.log Q ≤ xbar T)
    (hx2 : (∑ a : Fin r, c (Tstar.1.orderEmbOfFin Tstar.2 a)) +
        Real.log (Nat.factorial r * C ^ r * (high / low) *
          ∏ a : Fin r, lam (Tstar.1.orderEmbOfFin Tstar.2 a)) / Real.log Q ≤ xbar Tstar)
    (S : Idx N r) (hS : S ≠ Tstar) :
    ∀ T : Idx N r,
      |∑ S' : Idx N r, (Commons.LinearAlgebra.Matrix.compound r M) T S' *
        ((Commons.LinearAlgebra.Matrix.compound r V) S' S : ℝ)| ≤ Q ^ (xbar T) := by
  intro T
  have hVR : ∀ t j : Fin N, |∑ i, M t i * (V.map (Int.castRingHom ℝ)) i j|
      ≤ C * min (lam t) (lam j) * Q ^ (c t) := by
    intro t j
    simpa [Matrix.map_apply] using hbound t j
  have hval : (∑ S' : Idx N r, (Commons.LinearAlgebra.Matrix.compound r M) T S' *
        ((Commons.LinearAlgebra.Matrix.compound r V) S' S : ℝ))
      = (Commons.LinearAlgebra.Matrix.compound r (M * V.map (Int.castRingHom ℝ))) T S := by
    rw [← compound_wedge_value r M (V.map (Int.castRingHom ℝ)) S T]
    refine Finset.sum_congr rfl (fun S' _ => ?_)
    rw [compound_map_intCast_apply]
  rw [hval]
  by_cases hT : T = Tstar
  · rw [hT]
    refine (compound_entry_le_rpow_sharp M _ lam c hQ hC hlam hVR Tstar.1 S.1 Tstar.2 S.2
      low high hlow hhigh hTlow (hShigh S hS)).trans ?_
    exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hQ) hx2
  · refine (compound_entry_le_rpow M _ lam c hQ hC hlam hVR T S).trans ?_
    exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hQ) (hx1 T hT)


end Submission.Subspace.RealRank
