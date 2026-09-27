import Mathlib

namespace Work.EKLC6Core

/-- The gain scale `1/(k+1)` tending to `0`. -/
private noncomputable def gain (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

private lemma gain_pos (k : ℕ) : 0 < gain k := by
  unfold gain; positivity

theorem ae_forall_pos_exists_lt_of_tendsto_integral {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ] (Ψ : ℕ → X → ℝ)
    (hint : ∀ n, MeasureTheory.Integrable (Ψ n) μ)
    (hnonneg : ∀ᵐ x ∂μ, ∀ n, 0 ≤ Ψ n x)
    (htend : Filter.Tendsto (fun n : ℕ => ∫ x, Ψ n x ∂μ) Filter.atTop (nhds (0 : ℝ))) :
    ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, Ψ n x < ε := by
  -- For each scale `gain k`, the set of points where every `Ψ n` is at least `gain k`
  -- is `μ`-null: a Markov-type bound combined with `∫ Ψ n → 0`.
  have hS : ∀ k, μ {x | ∀ n, gain k ≤ Ψ n x} = 0 := by
    intro k
    have hbound : ∀ n, gain k * (μ {x | ∀ n, gain k ≤ Ψ n x}).toReal ≤ ∫ x, Ψ n x ∂μ := by
      intro n
      -- `gain k ≤ Ψ n` holds a.e. for the restricted measure on the null-candidate set.
      have hae : ∀ᵐ x ∂(μ.restrict {x | ∀ n, gain k ≤ Ψ n x}), gain k ≤ Ψ n x := by
        rw [MeasureTheory.ae_restrict_iff₀
          (nullMeasurableSet_le aemeasurable_const
            (hint n).aestronglyMeasurable.restrict.aemeasurable)]
        exact Filter.Eventually.of_forall (fun x hx => hx n)
      have hInt : MeasureTheory.Integrable (Ψ n) (μ.restrict {x | ∀ n, gain k ≤ Ψ n x}) :=
        (hint n).restrict
      have hIntc : MeasureTheory.Integrable (fun _ : X => gain k)
          (μ.restrict {x | ∀ n, gain k ≤ Ψ n x}) := MeasureTheory.integrable_const _
      have h1 : ∫ x, gain k ∂(μ.restrict {x | ∀ n, gain k ≤ Ψ n x})
          ≤ ∫ x, Ψ n x ∂(μ.restrict {x | ∀ n, gain k ≤ Ψ n x}) :=
        MeasureTheory.integral_mono_ae hIntc hInt hae
      have h2 : ∫ x, Ψ n x ∂(μ.restrict {x | ∀ n, gain k ≤ Ψ n x}) ≤ ∫ x, Ψ n x ∂μ :=
        MeasureTheory.integral_mono_measure MeasureTheory.Measure.restrict_le_self
          (hnonneg.mono (fun x hx => hx n)) (hint n)
      have hconst : ∫ x, gain k ∂(μ.restrict {x | ∀ n, gain k ≤ Ψ n x})
          = gain k * (μ {x | ∀ n, gain k ≤ Ψ n x}).toReal := by
        rw [MeasureTheory.integral_const, MeasureTheory.Measure.real_def,
          MeasureTheory.Measure.restrict_apply_univ, smul_eq_mul, mul_comm]
      calc gain k * (μ {x | ∀ n, gain k ≤ Ψ n x}).toReal
          = ∫ x, gain k ∂(μ.restrict {x | ∀ n, gain k ≤ Ψ n x}) := hconst.symm
        _ ≤ ∫ x, Ψ n x ∂(μ.restrict {x | ∀ n, gain k ≤ Ψ n x}) := h1
        _ ≤ ∫ x, Ψ n x ∂μ := h2
    have hle0 : gain k * (μ {x | ∀ n, gain k ≤ Ψ n x}).toReal ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds htend (Filter.Eventually.of_forall hbound)
    have hnonpos : (μ {x | ∀ n, gain k ≤ Ψ n x}).toReal ≤ 0 := by
      by_contra h
      rw [not_le] at h
      have hpos : 0 < gain k * (μ {x | ∀ n, gain k ≤ Ψ n x}).toReal :=
        mul_pos (gain_pos k) h
      linarith
    have htoReal : (μ {x | ∀ n, gain k ≤ Ψ n x}).toReal = 0 :=
      le_antisymm hnonpos ENNReal.toReal_nonneg
    have hfin : μ {x | ∀ n, gain k ≤ Ψ n x} ≠ ⊤ := MeasureTheory.measure_ne_top μ _
    rcases (ENNReal.toReal_eq_zero_iff _).mp htoReal with hzero | htop
    · exact hzero
    · exact absurd htop hfin
  -- Convert to a.e. statements at each scale and intersect over the countable family.
  have hgood : ∀ k, ∀ᵐ x ∂μ, ∃ n : ℕ, Ψ n x < gain k := by
    intro k
    rw [MeasureTheory.ae_iff]
    have hset : {x | ¬ ∃ n : ℕ, Ψ n x < gain k} = {x | ∀ n, gain k ≤ Ψ n x} := by
      ext x
      simp only [Set.mem_ofPred_eq, not_exists, not_lt]
    rw [hset]
    exact hS k
  refine (MeasureTheory.ae_all_iff.mpr hgood).mono ?_
  intro x hx ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  exact ⟨(hx k).choose, lt_trans (hx k).choose_spec (by simpa only [gain] using hk)⟩

end Work.EKLC6Core
