import Mathlib
import Submission.Work.EQ.EquiLocalDefs

namespace Work.EQ

open Filter _root_.Topology

/-- **Uniqueness of the value of a section at a point of `H0`.**  If two local analytic sections
of `ψ₁` pass through the same point `q ∈ H0`, then near the base point `q.2.1` they coincide.

The proof is the local injectivity clause `LocalInj`: it provides an open neighbourhood `U` of `q`
on which `ψ₁` is injective on `U ∩ H0`.  Both sections are continuous at the centre, so for `u`
close enough to `q.2.1` the values `f u` and `g u` both lie in `U`; by construction they lie in
`H0` and have `ψ₁`-value `u`.  Injectivity of `ψ₁` on `U ∩ H0` therefore forces `f u = g u`. -/
theorem sections_agree_nearby {a : ℝ} {h : ℂ → ℂ} {q : ChainData} {f g : ℂ → ChainData}
    {ρ ρ' : ℝ} (hinj : LocalInj a h) (hq : q ∈ H0 a h)
    (hf : IsSection a h f q ρ) (hg : IsSection a h g q ρ') :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ min ρ ρ' ∧ ∀ u ∈ Metric.ball q.2.1 ε, f u = g u := by
  -- the neighbourhood of `q` on which `ψ₁` is injective on `H0`
  obtain ⟨U, hUo, hqU, hU⟩ := hinj q hq
  -- continuity at the centre turns it into neighbourhoods of `q.2.1`
  have hnf : f ⁻¹' U ∈ 𝓝 q.2.1 :=
    hf.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [hf.2.1]; exact hqU))
  have hng : g ⁻¹' U ∈ 𝓝 q.2.1 :=
    hg.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [hg.2.1]; exact hqU))
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hnf hng)
  have hρ : 0 < ρ := hf.1
  have hρ' : 0 < ρ' := hg.1
  refine ⟨min δ (min ρ ρ'), lt_min hδ (lt_min hρ hρ'), min_le_right _ _, ?_⟩
  intro u hu
  have hu' : dist u q.2.1 < min δ (min ρ ρ') := Metric.mem_ball.mp hu
  have hδu : dist u q.2.1 < δ := lt_of_lt_of_le hu' (min_le_left _ _)
  have hmu : dist u q.2.1 < min ρ ρ' := lt_of_lt_of_le hu' (min_le_right _ _)
  have huρ : u ∈ Metric.ball q.2.1 ρ := Metric.mem_ball.mpr (lt_of_lt_of_le hmu (min_le_left _ _))
  have huρ' : u ∈ Metric.ball q.2.1 ρ' := Metric.mem_ball.mpr (lt_of_lt_of_le hmu (min_le_right _ _))
  have hV := hδball (Metric.mem_ball.mpr hδu)
  exact hU (f u) hV.1 (hf.2.2.1 u huρ).1 (g u) hV.2 (hg.2.2.1 u huρ').1
    (by rw [(hf.2.2.1 u huρ).2, (hg.2.2.1 u huρ').2])

end Work.EQ
