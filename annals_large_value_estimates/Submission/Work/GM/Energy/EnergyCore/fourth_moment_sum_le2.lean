import Mathlib
import Submission.Work.GM.Energy.EnergyCore.Setup2

namespace Work.GM.Energy.EnergyCore

/-- GM Lemma 11.6 summed over all gcd-scales `d ∈ [A,2N]`: applying the discrete fourth moment
bound at scale `M = ⌈N/d⌉` for every `d` and using `Σ ⌈N/d⌉ ≤ 4N(1+log2N)`, `Σ ⌈N/d⌉² ≤ 20N^{6/5}`. -/
theorem fourth_moment_sum_le (ε C₄ : ℝ) (hC₄ : 0 < C₄)
    (h4 : ∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
      (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
      (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
        ≤ C₄ * T ^ ε * ((W.card : ℝ) ^ 4 * (M : ℝ)
            + (M : ℝ) ^ 2 * (Submission.GM.energy W : ℝ)
            + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
                * T ^ ((1 : ℝ) / 2) * (M : ℝ)))
    (N A : ℕ) (hN : 1 ≤ N) (hA : 1 ≤ A)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N))
    (hsep : Submission.GM.Separated W 1)
    (hS1 : (∑ d ∈ Finset.Icc A (2 * N), (Work.GM.Energy.EnergyCore.Md N d : ℝ))
        ≤ 4 * (N : ℝ) * (1 + Real.log (2 * N)))
    (hS2 : (∑ d ∈ Finset.Icc A (2 * N), (Work.GM.Energy.EnergyCore.Md N d : ℝ) ^ 2)
        ≤ 20 * Submission.LargeValues.M N) :
    (∑ d ∈ Finset.Icc A (2 * N),
      ∑ n1 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
        ∑ n2 ∈ Finset.Icc (Work.GM.Energy.EnergyCore.Md N d) (2 * Work.GM.Energy.EnergyCore.Md N d),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
    ≤ (20 * C₄ * (Submission.LargeValues.M N) ^ ε) *
        ((W.card : ℝ) ^ 4 * ((N : ℝ) * (1 + Real.log (2 * (N : ℝ))))
          + (Submission.GM.energy W : ℝ) * Submission.LargeValues.M N
          + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
              * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2) * ((N : ℝ) * (1 + Real.log (2 * (N : ℝ))))) := by
  have hT0ge : (1 : ℝ) ≤ Submission.LargeValues.M N := one_le_MN hN
  have hT0pos : (0 : ℝ) < Submission.LargeValues.M N := lt_of_lt_of_le zero_lt_one hT0ge
  have hA0 : (0 : ℝ) ≤ (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) := by
    apply mul_nonneg (by positivity)
    have hNge : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  have hE0 : (0 : ℝ) ≤ (Submission.GM.energy W : ℝ) := by positivity
  have hQ0 : (0 : ℝ) ≤ (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hE0 _
  have hR0 : (0 : ℝ) ≤ (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg hT0pos.le _
  have hP0 : (0 : ℝ) ≤ (Submission.LargeValues.M N) ^ ε := Real.rpow_nonneg hT0pos.le _
  have hW40 : (0 : ℝ) ≤ (W.card : ℝ) ^ 4 := by positivity
  -- the per-scale bound, valid for every `d ∈ [A,2N]`
  have hper : ∀ d ∈ Finset.Icc A (2 * N),
      (∑ n1 ∈ Finset.Icc (Md N d) (2 * Md N d),
        ∑ n2 ∈ Finset.Icc (Md N d) (2 * Md N d),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
      ≤ C₄ * (Submission.LargeValues.M N) ^ ε *
        ((W.card : ℝ) ^ 4 * (Md N d : ℝ) + (Md N d : ℝ) ^ 2 * (Submission.GM.energy W : ℝ)
          + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
            * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2) * (Md N d : ℝ)) := by
    intro d hd
    have hd1 : 1 ≤ d := le_trans hA (Finset.mem_Icc.mp hd).1
    have hMd : 1 ≤ Md N d := Md_pos hN hd1
    exact h4 (Md N d) hMd (Submission.LargeValues.M N) hT0ge W hW hsep
  -- split the summed bound into the three aggregated quantities
  have hbig : (∑ d ∈ Finset.Icc A (2 * N),
        ((W.card : ℝ) ^ 4 * (Md N d : ℝ) + (Md N d : ℝ) ^ 2 * (Submission.GM.energy W : ℝ)
          + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
            * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2) * (Md N d : ℝ)))
      = (W.card : ℝ) ^ 4 * (∑ d ∈ Finset.Icc A (2 * N), (Md N d : ℝ))
        + (∑ d ∈ Finset.Icc A (2 * N), (Md N d : ℝ) ^ 2) * (Submission.GM.energy W : ℝ)
        + ((Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
            * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2))
          * (∑ d ∈ Finset.Icc A (2 * N), (Md N d : ℝ)) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  have hS1' : (∑ d ∈ Finset.Icc A (2 * N), (Md N d : ℝ))
      ≤ 4 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))) := by simpa using hS1
  have hb1 : (W.card : ℝ) ^ 4 * (∑ d ∈ Finset.Icc A (2 * N), (Md N d : ℝ))
      ≤ (W.card : ℝ) ^ 4 * (4 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ)))) :=
    mul_le_mul_of_nonneg_left hS1' hW40
  have hb2 : (∑ d ∈ Finset.Icc A (2 * N), (Md N d : ℝ) ^ 2) * (Submission.GM.energy W : ℝ)
      ≤ (20 * Submission.LargeValues.M N) * (Submission.GM.energy W : ℝ) :=
    mul_le_mul_of_nonneg_right hS2 hE0
  have hb3 : ((Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
        * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2))
        * (∑ d ∈ Finset.Icc A (2 * N), (Md N d : ℝ))
      ≤ ((Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
        * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2))
        * (4 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ)))) :=
    mul_le_mul_of_nonneg_left hS1' (mul_nonneg (mul_nonneg hQ0 (by positivity)) hR0)
  have hX : (∑ d ∈ Finset.Icc A (2 * N),
        ((W.card : ℝ) ^ 4 * (Md N d : ℝ) + (Md N d : ℝ) ^ 2 * (Submission.GM.energy W : ℝ)
          + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
            * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2) * (Md N d : ℝ)))
      ≤ 20 * ((W.card : ℝ) ^ 4 * ((N : ℝ) * (1 + Real.log (2 * (N : ℝ))))
          + (Submission.GM.energy W : ℝ) * Submission.LargeValues.M N
          + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
            * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2)
            * ((N : ℝ) * (1 + Real.log (2 * (N : ℝ))))) := by
    rw [hbig]
    have hQ' : (0 : ℝ) ≤ (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
        * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2) :=
      mul_nonneg (mul_nonneg hQ0 (by positivity)) hR0
    have hstep : (W.card : ℝ) ^ 4 * (∑ d ∈ Finset.Icc A (2 * N), (Md N d : ℝ))
          + (∑ d ∈ Finset.Icc A (2 * N), (Md N d : ℝ) ^ 2) * (Submission.GM.energy W : ℝ)
          + ((Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
              * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2))
            * (∑ d ∈ Finset.Icc A (2 * N), (Md N d : ℝ))
        ≤ (W.card : ℝ) ^ 4 * (4 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))))
          + (20 * Submission.LargeValues.M N) * (Submission.GM.energy W : ℝ)
          + ((Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
              * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2))
            * (4 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ)))) :=
      add_le_add (add_le_add hb1 hb2) hb3
    have hfin : (W.card : ℝ) ^ 4 * (4 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))))
          + (20 * Submission.LargeValues.M N) * (Submission.GM.energy W : ℝ)
          + ((Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
              * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2))
            * (4 * (N : ℝ) * (1 + Real.log (2 * (N : ℝ))))
        ≤ 20 * ((W.card : ℝ) ^ 4 * ((N : ℝ) * (1 + Real.log (2 * (N : ℝ))))
          + (Submission.GM.energy W : ℝ) * Submission.LargeValues.M N
          + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
            * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2)
            * ((N : ℝ) * (1 + Real.log (2 * (N : ℝ))))) := by
      nlinarith [hA0, hW40, hE0, hQ', mul_nonneg hW40 hA0, mul_nonneg hQ' hA0]
    linarith
  calc (∑ d ∈ Finset.Icc A (2 * N),
        (∑ n1 ∈ Finset.Icc (Md N d) (2 * Md N d),
          ∑ n2 ∈ Finset.Icc (Md N d) (2 * Md N d),
            ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4))
      ≤ ∑ d ∈ Finset.Icc A (2 * N), C₄ * (Submission.LargeValues.M N) ^ ε *
          ((W.card : ℝ) ^ 4 * (Md N d : ℝ) + (Md N d : ℝ) ^ 2 * (Submission.GM.energy W : ℝ)
            + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
              * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2) * (Md N d : ℝ)) :=
        Finset.sum_le_sum hper
    _ = C₄ * (Submission.LargeValues.M N) ^ ε *
          (∑ d ∈ Finset.Icc A (2 * N),
            ((W.card : ℝ) ^ 4 * (Md N d : ℝ) + (Md N d : ℝ) ^ 2 * (Submission.GM.energy W : ℝ)
              + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
                * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2) * (Md N d : ℝ))) := by
        rw [Finset.mul_sum]
    _ ≤ C₄ * (Submission.LargeValues.M N) ^ ε *
          (20 * ((W.card : ℝ) ^ 4 * ((N : ℝ) * (1 + Real.log (2 * (N : ℝ))))
            + (Submission.GM.energy W : ℝ) * Submission.LargeValues.M N
            + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
              * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2)
              * ((N : ℝ) * (1 + Real.log (2 * (N : ℝ)))))) :=
        mul_le_mul_of_nonneg_left hX (mul_nonneg hC₄.le hP0)
    _ = (20 * C₄ * (Submission.LargeValues.M N) ^ ε) *
          ((W.card : ℝ) ^ 4 * ((N : ℝ) * (1 + Real.log (2 * (N : ℝ))))
            + (Submission.GM.energy W : ℝ) * Submission.LargeValues.M N
            + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
              * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 2)
              * ((N : ℝ) * (1 + Real.log (2 * (N : ℝ))))) := by ring

end Work.GM.Energy.EnergyCore
