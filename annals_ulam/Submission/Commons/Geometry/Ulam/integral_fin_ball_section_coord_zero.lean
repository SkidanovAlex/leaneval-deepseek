import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

set_option linter.unusedVariables false

lemma integral_fin_ball_section_coord_zero {m : ℕ} [Nonempty (Fin m)] {a b s h : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hf_meas : Measurable f)
    (j : Fin m) :
    let S : Set (ℝ × (ℝ × (Fin m → ℝ))) :=
      {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1 ^ 2}
    ∫ p : ℝ × (ℝ × (Fin m → ℝ)) in S, p.2.2 j ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) = 0 := by
  intro S
  let μ : Measure (ℝ × (ℝ × (Fin m → ℝ))) :=
    (volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))
  change ∫ p : ℝ × (ℝ × (Fin m → ℝ)) in S, p.2.2 j ∂μ = 0
  let T : (ℝ × (ℝ × (Fin m → ℝ))) → (ℝ × (ℝ × (Fin m → ℝ))) :=
    fun p => (p.1, p.2.1, -p.2.2)
  have hS_meas : MeasurableSet S := by
    have h1 : MeasurableSet {p : ℝ × (ℝ × (Fin m → ℝ)) | p.1 ∈ Set.Icc a b} := by
      exact (measurableSet_Icc : MeasurableSet (Set.Icc (a : ℝ) b)).preimage measurable_fst
    have h2 : MeasurableSet {p : ℝ × (ℝ × (Fin m → ℝ)) | p.2.1 ≤ s * p.1 + h} := by
      apply measurableSet_le
      · exact measurable_fst.comp measurable_snd
      · exact (measurable_const.mul measurable_fst).add measurable_const
    have h3 : MeasurableSet {p : ℝ × (ℝ × (Fin m → ℝ)) |
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1 ^ 2} := by
      apply measurableSet_le
      · have hz : Measurable (fun p : ℝ × (ℝ × (Fin m → ℝ)) => p.2.1 ^ 2) :=
          (measurable_fst.comp measurable_snd).pow measurable_const
        have hsum : Measurable (fun p : ℝ × (ℝ × (Fin m → ℝ)) => ∑ j : Fin m, (p.2.2 j)^2) := by
          refine Finset.measurable_sum (Finset.univ : Finset (Fin m)) ?_
          intro j hj
          have hpj : Measurable (fun p : ℝ × (ℝ × (Fin m → ℝ)) => p.2.2 j) :=
            (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
          exact hpj.pow measurable_const
        exact hz.add hsum
      · exact (hf_meas.comp measurable_fst).pow measurable_const
    dsimp [S]
    exact h1.inter (h2.inter h3)
  have hmp : MeasurePreserving T μ μ := by
    dsimp [T, μ]
    exact (MeasurePreserving.id (volume : Measure ℝ)).prod
      ((MeasurePreserving.id (volume : Measure ℝ)).prod
        (Measure.measurePreserving_neg (volume : Measure (Fin m → ℝ))))
  have hemb : MeasurableEmbedding T := by
    dsimp [T]
    exact MeasurableEmbedding.id.prodMap (MeasurableEmbedding.id.prodMap measurableEmbedding_neg)
  have hpre : T ⁻¹' S = S := by
    ext p
    constructor
    · intro hp
      dsimp [S] at hp ⊢
      rcases hp with ⟨hp1, hp2, hp3⟩
      refine ⟨hp1, hp2, ?_⟩
      simpa [T, Pi.neg_apply, neg_sq] using hp3
    · intro hp
      dsimp [S] at hp ⊢
      rcases hp with ⟨hp1, hp2, hp3⟩
      refine ⟨hp1, hp2, ?_⟩
      simpa [T, Pi.neg_apply, neg_sq] using hp3
  have hchange := hmp.setIntegral_preimage_emb hemb (fun p : ℝ × (ℝ × (Fin m → ℝ)) => p.2.2 j) S
  rw [hpre] at hchange
  have hleft : (∫ p in S, (fun p : ℝ × (ℝ × (Fin m → ℝ)) => p.2.2 j) (T p) ∂μ) =
      ∫ p in S, - (p.2.2 j) ∂μ := by
    refine setIntegral_congr_fun hS_meas ?_
    intro p hp
    simp [T, Pi.neg_apply]
  rw [hleft] at hchange
  have hneg : (∫ p in S, - (p.2.2 j) ∂μ) = - (∫ p in S, p.2.2 j ∂μ) := by
    simp [integral_neg]
  rw [hneg] at hchange
  have : (∫ p : ℝ × (ℝ × (Fin m → ℝ)) in S, p.2.2 j ∂μ) = 0 := by linarith
  simpa [μ] using this

end Commons.Geometry.Ulam