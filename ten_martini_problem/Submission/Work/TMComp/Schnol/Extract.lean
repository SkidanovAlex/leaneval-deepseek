import Mathlib

/-!
# Component C15 (`P_Schnol`): extracting a pointwise convergent subsequence

A bounded sequence of energies together with vectors whose coordinates are uniformly bounded
(by `C : ℤ → ℝ`) has a subsequence along which both the energies and every coordinate
converge, the limits obeying the same bounds.  This is the diagonal-extraction step of the
finite-volume proof of Schnol's theorem.
-/

open Filter Topology

namespace Work.TMComp.Schnol

theorem subseqExtract (Eseq : ℕ → ℝ) (M₀ : ℝ) (hE : ∀ k, |Eseq k| ≤ M₀)
    (u : ℕ → ℤ → ℂ) (C : ℤ → ℝ) (hC : ∀ n, 0 ≤ C n) (hu : ∀ k n, ‖u k n‖ ≤ C n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ E' : ℝ, |E'| ≤ M₀ ∧ ∃ u' : ℤ → ℂ,
      (∀ n, ‖u' n‖ ≤ C n) ∧ Filter.Tendsto (fun k => Eseq (φ k)) Filter.atTop (nhds E') ∧
      ∀ n : ℤ, Filter.Tendsto (fun k => u (φ k) n) Filter.atTop (nhds (u' n)) := by
  have hK : IsCompact (Set.Icc (-M₀) M₀
      ×ˢ Set.univ.pi (fun n : ℤ => Metric.closedBall (0 : ℂ) (C n))) :=
    isCompact_Icc.prod (isCompact_univ_pi fun n => isCompact_closedBall 0 (C n))
  have hx : ∀ k : ℕ, (Eseq k, u k) ∈ Set.Icc (-M₀) M₀
      ×ˢ Set.univ.pi (fun n : ℤ => Metric.closedBall (0 : ℂ) (C n)) := by
    intro k
    refine ⟨abs_le.mp (hE k), ?_⟩
    intro n _
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu k n
  obtain ⟨p, hpK, φ, hφmono, hpφ⟩ := hK.tendsto_subseq hx
  obtain ⟨hpE, hpu⟩ := hpK
  refine ⟨φ, hφmono, p.1, abs_le.mpr hpE, p.2, ?_, ?_, ?_⟩
  · intro n
    have hmem := Set.mem_univ_pi.mp hpu n
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem
    exact hmem
  · have h1 : Filter.Tendsto (fun k => (((fun m => (Eseq m, u m)) ∘ φ) k).1) Filter.atTop
        (nhds p.1) := (continuous_fst.tendsto p).comp hpφ
    simpa using h1
  · intro n
    have h2 : Filter.Tendsto (fun k => (((fun m => (Eseq m, u m)) ∘ φ) k).2) Filter.atTop
        (nhds p.2) := (continuous_snd.tendsto p).comp hpφ
    have h3 : Filter.Tendsto (fun k => (u (φ k)) n) Filter.atTop (nhds (p.2 n)) :=
      ((continuous_apply n).tendsto p.2).comp h2
    simpa using h3

end Work.TMComp.Schnol
