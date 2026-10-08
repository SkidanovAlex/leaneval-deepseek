import Mathlib

namespace Work.L2F.Props.CFP

/-- Two vectors `u v : Fin 2 → F` over a field `F`, with `v ≠ 0`, that are parallel
(in the sense `u 0 * v 1 = u 1 * v 0`) are scalar multiples of one another. -/
lemma exists_smul_of_parallel {F : Type*} [Field F] (u v : Fin 2 → F) (hv : v ≠ 0)
    (h : u 0 * v 1 = u 1 * v 0) : ∃ ν : F, u = ν • v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨u 1 / v 1, ?_⟩
    have hgoal : ∀ i : Fin 2, u i = (u 1 / v 1) * v i := by
      rw [Fin.forall_fin_two]
      constructor
      · rw [h0, mul_zero]
        have hh : u 0 * v 1 = 0 := by rw [h, h0, mul_zero]
        exact (mul_eq_zero.mp hh).resolve_right h1
      · exact (div_mul_cancel₀ _ h1).symm
    exact funext fun i => by simpa [smul_eq_mul] using hgoal i
  · refine ⟨u 0 / v 0, ?_⟩
    have hgoal : ∀ i : Fin 2, u i = (u 0 / v 0) * v i := by
      rw [Fin.forall_fin_two]
      constructor
      · exact (div_mul_cancel₀ _ h0).symm
      · rw [div_mul_eq_mul_div, h]
        exact (mul_div_cancel_right₀ _ h0).symm
    exact funext fun i => by simpa [smul_eq_mul] using hgoal i

/-- A `2 × 2` matrix over a field whose square is zero has vanishing trace. -/
lemma trace_eq_zero_of_sq_zero {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (h : M * M = 0) : M 0 0 + M 1 1 = 0 := by
  have h00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = 0 := by
    have := congrFun (congrFun h 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : M 0 0 * M 0 1 + M 0 1 * M 1 1 = 0 := by
    have := congrFun (congrFun h 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : M 1 0 * M 0 0 + M 1 1 * M 1 0 = 0 := by
    have := congrFun (congrFun h 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 = 0 := by
    have := congrFun (congrFun h 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  by_contra hne
  have keyb : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination h01
  have keyc : (M 0 0 + M 1 1) * M 1 0 = 0 := by linear_combination h10
  have hb : M 0 1 = 0 := by
    rcases mul_eq_zero.mp keyb with h' | h'
    · exact h'
    · exact absurd h' hne
  have hc : M 1 0 = 0 := by
    rcases mul_eq_zero.mp keyc with h' | h'
    · exact absurd h' hne
    · exact h'
  have ha : M 0 0 = 0 := by
    have h' : M 0 0 * M 0 0 = 0 := by simpa [hb, hc] using h00
    exact (mul_self_eq_zero).mp h'
  have he : M 1 1 = 0 := by
    have h' : M 1 1 * M 1 1 = 0 := by simpa [hb, hc] using h11
    exact (mul_self_eq_zero).mp h'
  rw [ha, he] at hne
  exact hne (by simp)

/-- If a `2 × 2` matrix `M` over a field satisfies `M * M = 0` and `M.mulVec v = 0` for a
nonzero vector `v`, then the image of `M` is contained in the line spanned by `v`. -/
lemma mulVec_mem_span {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F)
    (hv : v ≠ 0) (hM : M * M = 0) (hvM : M.mulVec v = 0) :
    ∀ x : Fin 2 → F, ∃ ν : F, M.mulVec x = ν • v := by
  have htr : M 0 0 + M 1 1 = 0 := trace_eq_zero_of_sq_zero M hM
  have hMv0 : M 0 0 * v 0 + M 0 1 * v 1 = 0 := by
    have := congrFun hvM 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hMv1 : M 1 0 * v 0 + M 1 1 * v 1 = 0 := by
    have := congrFun hvM 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hM11 : M 1 1 = -M 0 0 := by linear_combination htr
  have hcol0 : (fun i => M i 0) 0 * v 1 = (fun i => M i 0) 1 * v 0 := by
    simp only
    rw [hM11] at hMv1
    linear_combination -hMv1
  have hcol1 : (fun i => M i 1) 0 * v 1 = (fun i => M i 1) 1 * v 0 := by
    simp only
    rw [hM11]
    linear_combination hMv0
  intro x
  obtain ⟨ν0, hν0⟩ := exists_smul_of_parallel (fun i => M i 0) v hv hcol0
  obtain ⟨ν1, hν1⟩ := exists_smul_of_parallel (fun i => M i 1) v hv hcol1
  refine ⟨x 0 * ν0 + x 1 * ν1, ?_⟩
  funext i
  have e0 : M i 0 = ν0 * v i := by
    have := congrFun hν0 i; simpa [smul_eq_mul] using this
  have e1 : M i 1 = ν1 * v i := by
    have := congrFun hν1 i; simpa [smul_eq_mul] using this
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
  rw [e0, e1]; ring

theorem sub_sq_zero_commute (F : Type*) [Field F] (X Y : Matrix (Fin 2) (Fin 2) F)
    (v : Fin 2 → F) (hv : v ≠ 0) (c d : F)
    (hX : (X - c • 1) * (X - c • 1) = 0) (hY : (Y - d • 1) * (Y - d • 1) = 0)
    (hXv : Matrix.mulVec (X - c • 1) v = 0) (hYv : Matrix.mulVec (Y - d • 1) v = 0) :
    X * Y = Y * X := by
  set A : Matrix (Fin 2) (Fin 2) F := X - c • 1 with hAdef
  set B : Matrix (Fin 2) (Fin 2) F := Y - d • 1 with hBdef
  have hAA : A * A = 0 := by rw [hAdef]; exact hX
  have hBB : B * B = 0 := by rw [hBdef]; exact hY
  have hAv : A.mulVec v = 0 := by rw [hAdef]; exact hXv
  have hBv : B.mulVec v = 0 := by rw [hBdef]; exact hYv
  have himA : ∀ x : Fin 2 → F, ∃ ν : F, A.mulVec x = ν • v :=
    mulVec_mem_span A v hv hAA hAv
  have himB : ∀ x : Fin 2 → F, ∃ ν : F, B.mulVec x = ν • v :=
    mulVec_mem_span B v hv hBB hBv
  -- the image of `B` lies in the line of `v`, and `A` kills `v`, so `A * B = 0`
  have hAB : A * B = 0 := by
    ext i j
    have hs : (A * B).mulVec (Pi.single j 1) = 0 := by
      rw [← Matrix.mulVec_mulVec]
      obtain ⟨ν, hν⟩ := himB (Pi.single j 1)
      rw [hν, Matrix.mulVec_smul, hAv, smul_zero]
    have hc := congrFun hs i
    rw [Matrix.mulVec_single_one] at hc
    exact hc
  have hBA : B * A = 0 := by
    ext i j
    have hs : (B * A).mulVec (Pi.single j 1) = 0 := by
      rw [← Matrix.mulVec_mulVec]
      obtain ⟨ν, hν⟩ := himA (Pi.single j 1)
      rw [hν, Matrix.mulVec_smul, hBv, smul_zero]
    have hc := congrFun hs i
    rw [Matrix.mulVec_single_one] at hc
    exact hc
  have hXeq : X = A + c • 1 := by rw [hAdef]; exact (sub_add_cancel X (c • 1)).symm
  have hYeq : Y = B + d • 1 := by rw [hBdef]; exact (sub_add_cancel Y (d • 1)).symm
  rw [hXeq, hYeq, ← sub_eq_zero]
  have hid : (A + c • 1) * (B + d • 1) - (B + d • 1) * (A + c • 1) = A * B - B * A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply,
        Matrix.one_apply, Fin.sum_univ_two, smul_eq_mul] <;> ring
  rw [hid, hAB, hBA, sub_zero]

end Work.L2F.Props.CFP
