import Mathlib
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.nearId_norm
import Submission.Work.Mostow.nearId_entry_le_one
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.gapA.nilpotentPairNearIdAt
import Submission.Work.Mostow.QIDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-- Conjugating `g` into the chart so that the `NearIdAt` centre becomes `0`:
if `g` moves the unit ball around `h • 0` by less than `η`, then `h⁻¹ * g * h` moves the unit
ball around `0` by less than `η`. -/
lemma isomNormTrace_nearIdAt_conj (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (h g : PO n 1) (η : ℝ)
    (hne : Submission.Mostow.NearIdAt g (h • (0 : E n)) η) :
    Submission.Mostow.NearIdAt (h⁻¹ * g * h) (0 : E n) η := by
  intro u hu
  have hiso : ∀ (a : PO n 1) (x y : E n), hdist (a • x) (a • y) = hdist x y := hI.2.2.2.2.2.2.1
  have hone : ∀ w : E n, (1 : PO n 1) • w = w := hA.2.2.2.1
  have hmul : ∀ (a b : PO n 1) (w : E n), (a * b) • w = a • (b • w) := hA.2.2.2.2.1
  have hhu : hdist (h • (0 : E n)) (h • u) = hdist (0 : E n) u := hiso h 0 u
  have h1 : hdist (h • u) (g • (h • u)) < η := hne (h • u) (by rw [hhu]; exact hu)
  have h2 : (h⁻¹ * g * h) • u = h⁻¹ • (g • (h • u)) := by
    rw [hmul (h⁻¹ * g) h u, hmul h⁻¹ g (h • u)]
  rw [h2]
  have h3 : hdist (h • u) (h • (h⁻¹ • (g • (h • u)))) = hdist u (h⁻¹ • (g • (h • u))) :=
    hiso h u (h⁻¹ • (g • (h • u)))
  rw [← h3]
  have h4 : h • (h⁻¹ • (g • (h • u))) = g • (h • u) := by
    rw [← hmul h h⁻¹ (g • (h • u)), mul_inv_cancel, hone]
  rw [h4]
  exact h1

/-- Norm/trace analysis for linear isometries and for the Lorentz lift: for a linear isometry `R`
of `E n` the operator norm of `R - 1` is controlled by the trace defect `n - tr R`, and for
`NearIdAt g w η` the trace of the lift `LambdaMat g` is within `C η` of `n + 1`. -/
theorem isomNormTrace (n : ℕ) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n) :
    (∀ R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ‖(R : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) - 1‖ ^ 2 ≤
        2 * ((n : ℝ) - LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (R : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (g : LeanEval.Geometry.MostowRigidity.PO n 1) (w : EuclideanSpace ℝ (Fin n)) (η : ℝ),
      0 < η → η ≤ 1 → Submission.Mostow.NearIdAt g w η →
      |(Work.Mostow.LambdaMat g).trace - ((n : ℝ) + 1)| ≤ C * η) := by
  refine ⟨?_, ?_⟩
  · -- Part 1: operator norm ≤ Hilbert–Schmidt norm, computed on an orthonormal basis.
    intro R
    classical
    set T : E n →L[ℝ] E n := (R : E n →L[ℝ] E n) - 1 with hT
    let b : OrthonormalBasis (Fin n) ℝ (E n) := EuclideanSpace.basisFun (Fin n) ℝ
    have hkey : ∀ x : E n, ‖T x‖ ≤ Real.sqrt (∑ i, ‖T (b i)‖ ^ 2) * ‖x‖ := by
      intro x
      have hx : x = ∑ i, (inner ℝ (b i) x : ℝ) • b i := (b.sum_repr' x).symm
      have hstep1 : T x = ∑ i, (inner ℝ (b i) x : ℝ) • T (b i) := by
        conv_lhs => rw [hx]
        rw [map_sum]
        exact Finset.sum_congr rfl (fun i _ => map_smul T _ _)
      have hcs : (∑ i, |inner ℝ (b i) x| * ‖T (b i)‖) ≤
          Real.sqrt (∑ i, ‖T (b i)‖ ^ 2) * Real.sqrt (∑ i, (inner ℝ (b i) x : ℝ) ^ 2) := by
        rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg _))
          (∑ i, (inner ℝ (b i) x : ℝ) ^ 2)]
        rw [Real.le_sqrt (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)))
          (mul_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))
            (Finset.sum_nonneg (fun i _ => sq_nonneg _)))]
        calc (∑ i, |inner ℝ (b i) x| * ‖T (b i)‖) ^ 2
            = (∑ i, ‖T (b i)‖ * |inner ℝ (b i) x|) ^ 2 := by
              congr 1; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
          _ ≤ (∑ i, ‖T (b i)‖ ^ 2) * (∑ i, |inner ℝ (b i) x| ^ 2) :=
              Finset.sum_mul_sq_le_sq_mul_sq _ _ _
          _ = (∑ i, ‖T (b i)‖ ^ 2) * (∑ i, (inner ℝ (b i) x : ℝ) ^ 2) := by
              congr 1; exact Finset.sum_congr rfl (fun i _ => sq_abs _)
      calc ‖T x‖ = ‖∑ i, (inner ℝ (b i) x : ℝ) • T (b i)‖ := by rw [hstep1]
        _ ≤ ∑ i, ‖(inner ℝ (b i) x : ℝ) • T (b i)‖ := norm_sum_le _ _
        _ = ∑ i, |inner ℝ (b i) x| * ‖T (b i)‖ := by
            apply Finset.sum_congr rfl; intro i _
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ Real.sqrt (∑ i, ‖T (b i)‖ ^ 2) * Real.sqrt (∑ i, (inner ℝ (b i) x : ℝ) ^ 2) := hcs
        _ = Real.sqrt (∑ i, ‖T (b i)‖ ^ 2) * ‖x‖ := by
            rw [b.sum_sq_inner_right x, Real.sqrt_sq (norm_nonneg x)]
    have hop : ‖T‖ ≤ Real.sqrt (∑ i, ‖T (b i)‖ ^ 2) :=
      ContinuousLinearMap.opNorm_le_bound T (Real.sqrt_nonneg _) hkey
    have hsum : ∑ i, ‖T (b i)‖ ^ 2
        = 2 * ((n : ℝ) - LinearMap.trace ℝ (E n)
            (R : E n →ₗ[ℝ] E n)) := by
      have htr : LinearMap.trace ℝ (E n) (R : E n →ₗ[ℝ] E n)
          = ∑ i, inner ℝ (b i) (R (b i)) :=
        LinearMap.trace_eq_sum_inner (𝕜 := ℝ) (E := E n) (ι := Fin n)
          (R : E n →ₗ[ℝ] E n) b
      rw [htr]
      have hone : ∀ i, ‖T (b i)‖ ^ 2 = 2 * (1 - inner ℝ (b i) (R (b i))) := by
        intro i
        have hTv : T (b i) = R (b i) - b i := by
          rw [hT]; simp
        rw [hTv, norm_sub_sq (𝕜 := ℝ)]
        rw [R.norm_map, b.orthonormal.norm_eq_one i]
        simp only [RCLike.re_to_real]
        rw [real_inner_comm (b i) (R (b i))]
        ring
      calc ∑ i, ‖T (b i)‖ ^ 2 = ∑ i, 2 * (1 - inner ℝ (b i) (R (b i))) :=
            Finset.sum_congr rfl (fun i _ => hone i)
        _ = 2 * ∑ i, (1 - inner ℝ (b i) (R (b i))) := by rw [Finset.mul_sum]
        _ = 2 * ((n : ℝ) - ∑ i, inner ℝ (b i) (R (b i))) := by
            congr 1
            rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            simp [nsmul_eq_mul]
    have hfin : ‖T‖ ^ 2 ≤ ∑ i, ‖T (b i)‖ ^ 2 := by
      have h0 : (0 : ℝ) ≤ ∑ i, ‖T (b i)‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      nlinarith [hop, Real.sq_sqrt h0, norm_nonneg T]
    linarith [hfin, hsum]
  · -- Part 2: conjugate to centre `0`, use the entrywise near-identity estimate, sum the diagonal.
    obtain ⟨C₀, hC₀pos, hC₀⟩ := nearId_entry_le_one n hA hI
    refine ⟨((n : ℝ) + 1) * C₀, by positivity, ?_⟩
    intro g w η hη hη1 hnear
    obtain ⟨h, hh⟩ := (BoostTransitive n hA).1 w
    have hconj : Submission.Mostow.NearIdAt (h⁻¹ * g * h) (0 : E n) η :=
      isomNormTrace_nearIdAt_conj n hA hI h g η (by rw [hh]; exact hnear)
    have hentry := hC₀ (h⁻¹ * g * h) η hη hη1 hconj
    set A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ := LambdaMat (h⁻¹ * g * h) with hAdef
    have htr : A.trace = (LambdaMat g).trace := by
      rw [hAdef, LambdaMat_mul hA (h⁻¹ * g) h, LambdaMat_mul hA h⁻¹ g]
      rw [Matrix.trace_mul_cycle, LambdaMat_inv hA h, Matrix.one_mul]
    have hdiag : A.trace - ((n : ℝ) + 1) = ∑ i : Fin n ⊕ Fin 1, (A - 1) i i := by
      have hcard : ((n : ℝ) + 1) = (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ).trace := by
        rw [Matrix.trace_one, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
        push_cast; ring
      rw [hcard, ← Matrix.trace_sub, Matrix.trace]
      exact Finset.sum_congr rfl (fun i _ => Matrix.diag_apply _ i)
    have hsum : ∑ i : Fin n ⊕ Fin 1, C₀ * η = (((n : ℝ) + 1) * C₀) * η := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
        Fintype.card_fin]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    calc |(LambdaMat g).trace - ((n : ℝ) + 1)| = |A.trace - ((n : ℝ) + 1)| := by rw [htr]
      _ = |∑ i : Fin n ⊕ Fin 1, (A - 1) i i| := by rw [hdiag]
      _ ≤ ∑ i : Fin n ⊕ Fin 1, |(A - 1) i i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n ⊕ Fin 1, C₀ * η := by
          apply Finset.sum_le_sum; intro i _
          rw [hAdef]; exact hentry i i
      _ = (((n : ℝ) + 1) * C₀) * η := hsum

end Work.Mostow
