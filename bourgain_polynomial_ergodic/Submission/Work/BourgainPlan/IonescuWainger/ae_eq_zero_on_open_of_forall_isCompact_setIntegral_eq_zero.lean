import Mathlib

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory Set

/-- Localization of the fundamental lemma: an integrable function whose integral vanishes over
every compact subset of an open set `U` vanishes a.e. on `U`. -/
theorem ae_eq_zero_on_open_of_forall_isCompact_setIntegral_eq_zero
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [SigmaCompactSpace X] [BorelSpace X]
    {μ : MeasureTheory.Measure X} {f : X → ℂ} (hf : MeasureTheory.Integrable f μ)
    {U : Set X} (hU : IsOpen U)
    (h : ∀ C : Set X, IsCompact C → C ⊆ U → ∫ x in C, f x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ U → f x = 0 := by
  have hUmeas : MeasurableSet U := hU.measurableSet
  have hzero : ∀ C : Set X, IsCompact C → ∫ x in C, U.indicator f x ∂μ = 0 := by
    intro C hC
    rw [setIntegral_indicator hUmeas]
    rcases Set.eq_empty_or_nonempty (Uᶜ) with hUc | hne
    · have hUuniv : U = univ := by rw [← compl_compl U, hUc, compl_empty]
      have hCU : C ∩ U = C := by rw [hUuniv]; exact inter_univ C
      rw [hCU]
      exact h C hC (by rw [hUuniv]; exact subset_univ C)
    · let T : ℕ → Set X := fun n => {x | (1 : ℝ) / ((n : ℝ) + 1) ≤ Metric.infDist x (Uᶜ)}
      let S : ℕ → Set X := fun n => C ∩ T n
      have hTclosed : ∀ n, IsClosed (T n) := fun n =>
        isClosed_le continuous_const (Metric.continuous_infDist_pt (Uᶜ))
      have hSmeas : ∀ n, MeasurableSet (S n) := fun n =>
        (hC.isClosed.inter (hTclosed n)).measurableSet
      have hSc : ∀ n, IsCompact (S n) := fun n => hC.inter_right (hTclosed n)
      have hmono : Monotone S := by
        intro m n hmn x hx
        refine ⟨hx.1, ?_⟩
        have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ (1 : ℝ) / ((m : ℝ) + 1) := by
          refine one_div_le_one_div_of_le (by positivity) ?_
          have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
          linarith
        exact hle.trans hx.2
      have hUnion : (⋃ n, S n) = C ∩ U := by
        ext x
        constructor
        · intro hx
          rw [mem_iUnion] at hx
          obtain ⟨n, hn⟩ := hx
          refine ⟨hn.1, ?_⟩
          by_contra hxUc
          have h0 : Metric.infDist x (Uᶜ) = 0 := Metric.infDist_zero_of_mem hxUc
          have hle2 : (1 : ℝ) / ((n : ℝ) + 1) ≤ Metric.infDist x (Uᶜ) := hn.2
          have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith
        · rintro ⟨hxC, hxU⟩
          rw [mem_iUnion]
          have hpos : 0 < Metric.infDist x (Uᶜ) :=
            (hU.isClosed_compl.notMem_iff_infDist_pos hne).1 (by simpa using hxU)
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
          exact ⟨n, hxC, le_of_lt hn⟩
      have hsi : ∀ n, ∫ x in S n, f x ∂μ = 0 := fun n =>
        h (S n) (hSc n) (fun x hx => by
          have hxCU : x ∈ C ∩ U := by
            rw [← hUnion]
            exact mem_iUnion_of_mem n hx
          exact hxCU.2)
      have hlim : ∫ x in (⋃ n, S n), f x ∂μ = 0 := by
        have htend := tendsto_setIntegral_of_monotone hSmeas hmono hf.integrableOn
        simp_rw [hsi] at htend
        rw [tendsto_const_nhds_iff] at htend
        exact htend.symm
      rw [hUnion] at hlim
      exact hlim
  have hae : U.indicator f =ᵐ[μ] 0 :=
    ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero (hf.indicator hUmeas) hzero
  filter_upwards [hae] with x hx hxU
  simpa [Set.indicator_of_mem hxU] using hx

end Work.BourgainPlan.IonescuWainger
