import Mathlib

namespace Work.WilE4.CAD

theorem exists_seq_of_not_eventually_nhdsWithin {X : Type*} [PseudoMetricSpace X] {x₀ : X}
    {C : Set X} {P : X → Prop} (h : ¬ (∀ᶠ x in nhdsWithin x₀ C, P x)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ C) ∧ Filter.Tendsto u Filter.atTop (nhds x₀) ∧ ∀ n, ¬ P (u n) := by
  have hf : ∃ᶠ x in nhdsWithin x₀ C, ¬ P x := Filter.not_eventually.mp h
  have hchoice : ∀ n : ℕ, ∃ x : X, x ∈ Metric.ball x₀ (1 / ((n : ℝ) + 1)) ∧ x ∈ C ∧ ¬ P x := by
    intro n
    have hball : Metric.ball x₀ (1 / ((n : ℝ) + 1)) ∈ nhds x₀ :=
      Metric.ball_mem_nhds x₀ (by positivity)
    have hC : C ∈ Filter.principal C := Filter.mem_principal.mpr (subset_refl C)
    have hmem : Metric.ball x₀ (1 / ((n : ℝ) + 1)) ∩ C ∈ nhdsWithin x₀ C := by
      rw [nhdsWithin]
      exact Filter.inter_mem_inf hball hC
    obtain ⟨x, hx, hxP⟩ := (Filter.frequently_iff.mp hf) hmem
    exact ⟨x, hx.1, hx.2, hxP⟩
  choose u hu using hchoice
  refine ⟨u, fun n => (hu n).2.1, ?_, fun n => (hu n).2.2⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hg : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlt : Filter.Eventually (fun n : ℕ => 1 / ((n : ℝ) + 1) < ε) Filter.atTop :=
    hg.eventually (isOpen_Iio.mem_nhds hε)
  filter_upwards [hlt] with n hn
  calc dist (u n) x₀ < 1 / ((n : ℝ) + 1) := Metric.mem_ball.mp (hu n).1
    _ < ε := hn

end Work.WilE4.CAD
