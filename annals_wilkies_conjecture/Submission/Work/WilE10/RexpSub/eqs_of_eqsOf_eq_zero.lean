import Mathlib
import Submission.Work.WilE10.RexpSubDefs

noncomputable section
open Classical

namespace Work.WilE10.RexpSub

open Work.WilE10 WilkiesDesign WilkiesDesign.E

/-! ## Elementary identities for the compactification `psi` used by the branch equations -/

/-- The small-branch relation `u = psi t` solves: `psi t ^ 2 * (1 + t ^ 2) = t ^ 2`. -/
lemma psi_sq_mul_one_add_sq (t : ℝ) : psi t ^ 2 * (1 + t ^ 2) = t ^ 2 := by
  rw [psi_sq]; field_simp

/-- The large-branch relation `u = psi (1/t)`, cleared of denominators:
`psi t ^ 2 * (1 + (1/t) ^ 2) = 1` for `t ≠ 0`. -/
lemma psi_sq_mul_one_add_inv_sq {t : ℝ} (ht : t ≠ 0) : psi t ^ 2 * (1 + t⁻¹ ^ 2) = 1 := by
  rw [psi_sq, inv_pow]; field_simp; ring

/-- `psi` has the same sign as its argument. -/
lemma psi_mul_self_nonneg (t : ℝ) : 0 ≤ psi t * t := by
  have h : psi t * t = t ^ 2 / Real.sqrt (1 + t ^ 2) := by rw [psi]; field_simp
  rw [h]; positivity

/-- Each of the tag/relation equations of the branch basic set vanishes at the auxiliary point
`mkPt n m x ε z`, for the branch pattern `ε` determined by the values `z` themselves. -/
theorem eqs_of_eqsOf_eq_zero (n m : ℕ) (x : Fin n → ℝ) (ε : Fin (n + m) → Bool)
    (z : Fin (n + m) → ℝ) (hzx : ∀ i : Fin n, z (Fin.castAdd m i) = x i)
    (hε : ∀ i : Fin (n + m), ε i = true ↔ |z i| ≤ 1) :
    ∀ f ∈ ((List.finRange (n + m)).flatMap (fun i => if ε i then [Work.WilE10.tagEq n m i] else [])) ++
        ((List.finRange n).flatMap (fun i =>
          if ε (Fin.castAdd m i) then [Work.WilE10.relA n m i, Work.WilE10.relB n m i]
          else [Work.WilE10.relC n m i])),
      WilkiesDesign.E.eaEval (Work.WilE10.chain n m) f (Work.WilE10.mkPt n m x ε z) = 0 := by
  intro f hf
  rw [List.mem_append] at hf
  rcases hf with hf | hf
  · -- the tag equations `tᵢ² + qᵢ² = 1`
    rw [List.mem_flatMap] at hf
    obtain ⟨i, -, hfi⟩ := hf
    by_cases hi : ε i = true
    · rw [ite_eq_left hi, List.mem_singleton] at hfi
      rw [hfi]
      have h1 : 0 ≤ 1 - z i ^ 2 := by
        have h2 : |z i| ≤ 1 := (hε i).mp hi
        nlinarith [abs_nonneg (z i), sq_abs (z i)]
      rw [show eaEval (chain n m) (tagEq n m i) (mkPt n m x ε z) =
          (mkPt n m x ε z (ut n m i)) ^ 2 + (mkPt n m x ε z (uq n m i)) ^ 2 - 1 from by
        simp [eaEval, tagEq, Xa]]
      rw [mkPt_ut, mkPt_uq, ite_eq_left hi, ite_eq_left hi, Real.sq_sqrt h1]
      ring
    · rw [ite_eq_right hi] at hfi
      exact absurd hfi List.not_mem_nil
  · -- the `psi`-relations, small and large branch
    rw [List.mem_flatMap] at hf
    obtain ⟨i, -, hfi⟩ := hf
    by_cases hi : ε (Fin.castAdd m i) = true
    · rw [ite_eq_left hi, List.mem_cons, List.mem_singleton] at hfi
      rcases hfi with rfl | rfl
      · -- small branch: `uᵢ²(1 + tᵢ²) = tᵢ²`
        rw [show eaEval (chain n m) (relA n m i) (mkPt n m x ε z) =
            (mkPt n m x ε z (uu n m i)) ^ 2 *
                (1 + (mkPt n m x ε z (ut n m (Fin.castAdd m i))) ^ 2) -
              (mkPt n m x ε z (ut n m (Fin.castAdd m i))) ^ 2 from by
          simp [eaEval, relA, Xa]]
        rw [mkPt_uu, mkPt_ut, ite_eq_left hi, hzx i, psi_sq_mul_one_add_sq (x i)]
        ring
      · -- small branch: the sign condition `uᵢ·tᵢ = wᵢ²`
        rw [show eaEval (chain n m) (relB n m i) (mkPt n m x ε z) =
            (mkPt n m x ε z (uu n m i)) * (mkPt n m x ε z (ut n m (Fin.castAdd m i))) -
              (mkPt n m x ε z (uw n m i)) ^ 2 from by
          simp [eaEval, relB, Xa]]
        rw [mkPt_uu, mkPt_ut, mkPt_uw, ite_eq_left hi, ite_eq_left hi, hzx i,
          Real.sq_sqrt (psi_mul_self_nonneg (x i))]
        ring
    · -- large branch: `uᵢ²(1 + sᵢ²) = 1` with `sᵢ = 1/tᵢ`
      have hif : ε (Fin.castAdd m i) = false := by
        cases h : ε (Fin.castAdd m i) <;> simp_all
      rw [ite_eq_right hi, List.mem_singleton] at hfi
      rw [hfi]
      have hlt : 1 < |z (Fin.castAdd m i)| := by
        have h2 : ¬ (|z (Fin.castAdd m i)| ≤ 1) := fun h => by
          have := (hε (Fin.castAdd m i)).mpr h
          rw [this] at hif; exact absurd hif (by simp)
        exact not_le.mp h2
      have hx0 : x i ≠ 0 := by
        have h3 : 1 < |x i| := by rw [hzx i] at hlt; exact hlt
        intro h0; rw [h0] at h3; norm_num at h3
      rw [show eaEval (chain n m) (relC n m i) (mkPt n m x ε z) =
          (mkPt n m x ε z (uu n m i)) ^ 2 *
              (1 + (mkPt n m x ε z (us n m (Fin.castAdd m i))) ^ 2) - 1 from by
        simp [eaEval, relC, Xa]]
      rw [mkPt_uu, mkPt_us, ite_eq_right (by simp [hif]), hzx i, psi_sq_mul_one_add_inv_sq hx0]
      ring

end Work.WilE10.RexpSub
