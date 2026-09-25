import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Final.iterDerivNorm_comp_smul

namespace Work.CR.Flat.Holder

/-- Reverse scaling estimate for the Hölder norm: composing with the dilation `z ↦ s • z`
(`0 < s ≤ 1`) can only *decrease* the `C^{k,α}` norm, and the loss is at most the factor
`1 / s ^ (k+1)`.  This is the inverse of `holderNorm_comp_smul_isOpen`, and it needs no
smoothness of `f`: it is a consequence of the exact scaling identity
`Work.NN.Final.iterDerivNorm_comp_smul`, valid for within-derivatives on an open set. -/
theorem holderNorm_le_ofReal_inv_pow_mul_comp_smul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {α : ℝ} (hα : α ≤ 1) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (f : X → ℂ) {Ω : Set X}
    (hΩ : IsOpen Ω) :
    Work.CR.Flat.holderNorm k α f Ω ≤
      ENNReal.ofReal (1 / s ^ (k + 1)) *
        Work.CR.Flat.holderNorm k α (fun z => f (s • z)) {z | s • z ∈ Ω} := by
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hterm : ∀ i, i ≤ k →
      Work.CR.Flat.iterDerivNorm i f Ω + Work.CR.Flat.holderSeminorm i α f Ω
        ≤ ENNReal.ofReal (1 / s ^ (k + 1)) *
          (Work.CR.Flat.iterDerivNorm i (fun z => f (s • z)) {z | s • z ∈ Ω}
            + Work.CR.Flat.holderSeminorm i α (fun z => f (s • z)) {z | s • z ∈ Ω}) := by
    intro i hik
    obtain ⟨hE, hS⟩ := Work.NN.Final.iterDerivNorm_comp_smul s hsne i α f hΩ
    rw [abs_of_pos hs0] at hE hS
    -- Bound the iterated-derivative term.
    have hpowi : s ^ (k + 1) ≤ s ^ i :=
      pow_le_pow_of_le_one hs0.le hs1 (Nat.le_succ_of_le hik)
    have hCi : ENNReal.ofReal ((s ^ i)⁻¹) ≤ ENNReal.ofReal (1 / s ^ (k + 1)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (pow_pos hs0 _) hpowi
    have hAi : Work.CR.Flat.iterDerivNorm i f Ω
        = ENNReal.ofReal ((s ^ i)⁻¹)
            * Work.CR.Flat.iterDerivNorm i (fun z => f (s • z)) {z | s • z ∈ Ω} := by
      have h1 : ENNReal.ofReal ((s ^ i)⁻¹) * ENNReal.ofReal (s ^ i) = 1 := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hs0.le i)),
          inv_mul_cancel₀ (pow_ne_zero i hsne), ENNReal.ofReal_one]
      calc Work.CR.Flat.iterDerivNorm i f Ω
          = (ENNReal.ofReal ((s ^ i)⁻¹) * ENNReal.ofReal (s ^ i))
              * Work.CR.Flat.iterDerivNorm i f Ω := by rw [h1, one_mul]
        _ = ENNReal.ofReal ((s ^ i)⁻¹)
              * (ENNReal.ofReal (s ^ i) * Work.CR.Flat.iterDerivNorm i f Ω) := by rw [mul_assoc]
        _ = ENNReal.ofReal ((s ^ i)⁻¹)
              * Work.CR.Flat.iterDerivNorm i (fun z => f (s • z)) {z | s • z ∈ Ω} := by
            rw [← hE]
    have hbi : Work.CR.Flat.iterDerivNorm i f Ω
        ≤ ENNReal.ofReal (1 / s ^ (k + 1))
            * Work.CR.Flat.iterDerivNorm i (fun z => f (s • z)) {z | s • z ∈ Ω} := by
      rw [hAi]
      exact mul_le_mul_left hCi _
    -- Bound the Hölder-seminorm term.
    have hexp : ((i : ℝ) + α) ≤ ((k + 1 : ℕ) : ℝ) := by
      have hik' : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hik
      rw [Nat.cast_add, Nat.cast_one]; linarith
    have hpowα : s ^ (k + 1) ≤ s ^ ((i : ℝ) + α) := by
      calc s ^ (k + 1) = s ^ ((k + 1 : ℕ) : ℝ) := (Real.rpow_natCast s (k + 1)).symm
        _ ≤ s ^ ((i : ℝ) + α) := Real.rpow_le_rpow_of_exponent_ge hs0 hs1 hexp
    have hCα : ENNReal.ofReal ((s ^ ((i : ℝ) + α))⁻¹) ≤ ENNReal.ofReal (1 / s ^ (k + 1)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (pow_pos hs0 _) hpowα
    have hAα : Work.CR.Flat.holderSeminorm i α f Ω
        = ENNReal.ofReal ((s ^ ((i : ℝ) + α))⁻¹)
            * Work.CR.Flat.holderSeminorm i α (fun z => f (s • z)) {z | s • z ∈ Ω} := by
      have h1 : ENNReal.ofReal ((s ^ ((i : ℝ) + α))⁻¹)
          * ENNReal.ofReal (s ^ ((i : ℝ) + α)) = 1 := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.rpow_nonneg hs0.le _)),
          inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hs0 _)), ENNReal.ofReal_one]
      calc Work.CR.Flat.holderSeminorm i α f Ω
          = (ENNReal.ofReal ((s ^ ((i : ℝ) + α))⁻¹)
              * ENNReal.ofReal (s ^ ((i : ℝ) + α))) * Work.CR.Flat.holderSeminorm i α f Ω := by
            rw [h1, one_mul]
        _ = ENNReal.ofReal ((s ^ ((i : ℝ) + α))⁻¹)
              * (ENNReal.ofReal (s ^ ((i : ℝ) + α)) * Work.CR.Flat.holderSeminorm i α f Ω) := by
            rw [mul_assoc]
        _ = ENNReal.ofReal ((s ^ ((i : ℝ) + α))⁻¹)
              * Work.CR.Flat.holderSeminorm i α (fun z => f (s • z)) {z | s • z ∈ Ω} := by
            rw [← hS]
    have hbα : Work.CR.Flat.holderSeminorm i α f Ω
        ≤ ENNReal.ofReal (1 / s ^ (k + 1))
            * Work.CR.Flat.holderSeminorm i α (fun z => f (s • z)) {z | s • z ∈ Ω} := by
      rw [hAα]
      exact mul_le_mul_left hCα _
    calc Work.CR.Flat.iterDerivNorm i f Ω + Work.CR.Flat.holderSeminorm i α f Ω
        ≤ ENNReal.ofReal (1 / s ^ (k + 1))
            * Work.CR.Flat.iterDerivNorm i (fun z => f (s • z)) {z | s • z ∈ Ω}
          + ENNReal.ofReal (1 / s ^ (k + 1))
            * Work.CR.Flat.holderSeminorm i α (fun z => f (s • z)) {z | s • z ∈ Ω} :=
          add_le_add hbi hbα
      _ = ENNReal.ofReal (1 / s ^ (k + 1))
            * (Work.CR.Flat.iterDerivNorm i (fun z => f (s • z)) {z | s • z ∈ Ω}
              + Work.CR.Flat.holderSeminorm i α (fun z => f (s • z)) {z | s • z ∈ Ω}) :=
          (mul_add _ _ _).symm
  simp only [Work.CR.Flat.holderNorm]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact hterm i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

end Work.CR.Flat.Holder
