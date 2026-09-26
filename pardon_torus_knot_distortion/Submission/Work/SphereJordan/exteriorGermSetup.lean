import Mathlib
import Submission.Work.Smooth.Jordan.Separation
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.jsepExists
import Submission.Work.Smooth.Jordan.plane_separation_eq
import Submission.Work.Smooth.SphereJordan.crosscutComponents
import Submission.Work.Smooth.SphereJordan.ballSdiffDiscPreconnected
import Submission.Work.SphereJordan.gammaInjOnArc

/-!
# The exterior germ of a plane Jordan separation

For a simple closed plane curve `γ` with a Jordan separation `S`
(`S.U` the unbounded side, `S.V` the bounded side), and any point `γ θ₀` of the curve and any
`ε > 0`, there is `ρ ∈ (0, ε)` such that the part of the unbounded side inside `Metric.ball (γ θ₀) ρ`
lies in a *single* connected component of the part of the unbounded side inside
`Metric.ball (γ θ₀) ε`.
-/

namespace Work.SphereJordan

open Set

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- **The trace is the frontier of the unbounded side of any `PlaneSeparation`.** -/
theorem frontier_U_eq_trace (S : Work.Smooth.Jordan.PlaneSeparation γ) :
    frontier S.U = γ.trace := by
  obtain ⟨J⟩ := Work.Smooth.SphereJordan.exists_jsep γ S.simple
  have h : S.U = (J.toPlaneSeparation S.simple).U ∧ S.V = (J.toPlaneSeparation S.simple).V ∨
      S.U = (J.toPlaneSeparation S.simple).V ∧ S.V = (J.toPlaneSeparation S.simple).U :=
    Work.Smooth.Jordan.plane_separation_eq S (J.toPlaneSeparation S.simple)
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
  · rw [h1]; exact J.frontier_U
  · rw [h1]; exact J.frontier_V

/-- **The trace is the frontier of the bounded side of any `PlaneSeparation`.** -/
theorem frontier_V_eq_trace (S : Work.Smooth.Jordan.PlaneSeparation γ) :
    frontier S.V = γ.trace := by
  obtain ⟨J⟩ := Work.Smooth.SphereJordan.exists_jsep γ S.simple
  have h : S.U = (J.toPlaneSeparation S.simple).U ∧ S.V = (J.toPlaneSeparation S.simple).V ∨
      S.U = (J.toPlaneSeparation S.simple).V ∧ S.V = (J.toPlaneSeparation S.simple).U :=
    Work.Smooth.Jordan.plane_separation_eq S (J.toPlaneSeparation S.simple)
  rcases h with ⟨-, h2⟩ | ⟨-, h2⟩
  · rw [h2]; exact J.frontier_V
  · rw [h2]; exact J.frontier_U

/-- **The trace lies in the closure of the unbounded side.** -/
theorem trace_subset_closure_U (S : Work.Smooth.Jordan.PlaneSeparation γ) :
    γ.trace ⊆ closure S.U := by
  rw [← frontier_U_eq_trace S]; exact frontier_subset_closure

/-- **The trace lies in the closure of the bounded side.** -/
theorem trace_subset_closure_V (S : Work.Smooth.Jordan.PlaneSeparation γ) :
    γ.trace ⊆ closure S.V := by
  rw [← frontier_V_eq_trace S]; exact frontier_subset_closure

/-- **The unbounded side is the complement of the closed bounded side.** -/
theorem U_eq_compl_closure_V (S : Work.Smooth.Jordan.PlaneSeparation γ) :
    S.U = (closure S.V)ᶜ := by
  have hUSub : S.U ⊆ γ.traceᶜ := by
    intro z hz
    have : z ∈ S.U ∪ S.V := Or.inl hz
    rw [S.union_eq] at this; exact this
  have hcl : closure S.V = S.V ∪ γ.trace := by
    rw [closure_eq_self_union_frontier, frontier_V_eq_trace S]
  ext z
  constructor
  · intro hz hzcl
    rw [hcl, Set.mem_union] at hzcl
    rcases hzcl with h | h
    · exact Set.disjoint_left.mp S.disjoint_UV hz h
    · exact hUSub hz h
  · intro hzcl
    have hzV : z ∉ S.V := fun hV => hzcl (subset_closure hV)
    have hzT : z ∉ γ.trace := fun hT => hzcl (trace_subset_closure_V S hT)
    have h2 : z ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hzT
    rcases h2 with h | h
    · exact h
    · exact absurd h hzV

/-- **The trace in a small ball is covered by a parameter window.** -/
theorem exists_window (hs : γ.IsSimple) {θ₀ δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, ‖γ.γ t - γ.γ θ₀‖ < ρ → ∃ s ∈ Set.Icc (θ₀ - δ) (θ₀ + δ),
      γ.γ s = γ.γ t := by
  classical
  set K : Set ℝ := Set.Icc (θ₀ - Real.pi) (θ₀ + Real.pi) \ Set.Ioo (θ₀ - δ) (θ₀ + δ) with hK
  have hKc : IsCompact K := isCompact_Icc.diff isOpen_Ioo
  have hpK : γ.γ θ₀ ∉ γ.γ '' K := by
    rintro ⟨t, ht, hteq⟩
    obtain ⟨k, hk⟩ := Work.SphereJordan.gamma_eq_imp_mod hs hteq
    have hle : |t - θ₀| ≤ Real.pi := by
      rw [abs_le]; exact ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩
    have hkabs : |(k : ℝ)| * (2 * Real.pi) ≤ Real.pi := by
      have h2 : |(k : ℝ) * (2 * Real.pi)| ≤ Real.pi := by rw [← hk]; exact hle
      rwa [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at h2
    have hk0 : k = 0 := by
      have h2 : |(k : ℝ)| ≤ 1 / 2 := by nlinarith [hkabs, Real.pi_pos]
      have h3 : |(k : ℝ)| < 1 := by linarith
      by_contra hk'
      have h5 : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk'
      linarith
    have ht_eq : t = θ₀ := by
      have h := hk; rw [hk0] at h; simp only [Int.cast_zero, zero_mul] at h; linarith
    exact ht.2 (ht_eq ▸ ⟨by linarith, by linarith⟩)
  have hKcomp : IsCompact (γ.γ '' K) := hKc.image γ.cont
  obtain ⟨d, hd, hdsub⟩ := Metric.isOpen_iff.mp hKcomp.isClosed.isOpen_compl (γ.γ θ₀) hpK
  refine ⟨d, hd, fun t ht => ?_⟩
  obtain ⟨m, hm⟩ := Work.Topology.PlaneCurve.exists_int_mul_add_mem_Ico
    (T := 2 * Real.pi) (by positivity) (θ₀ - Real.pi) t
  set s : ℝ := t + (m : ℝ) * (2 * Real.pi) with hsdef
  have hper : γ.γ s = γ.γ t := by rw [hsdef]; exact γ.periodic.int_mul m t
  have hsI : s ∈ Set.Icc (θ₀ - Real.pi) (θ₀ + Real.pi) :=
    ⟨hm.1, by have := hm.2; rw [hsdef] at this ⊢; linarith⟩
  have hsball : γ.γ s ∈ Metric.ball (γ.γ θ₀) d := by
    rw [Metric.mem_ball, dist_eq_norm, hper]; exact ht
  rcases lt_or_ge (θ₀ - δ) s with hslt | hsge
  · rcases lt_or_ge s (θ₀ + δ) with hslt2 | hsge2
    · exact ⟨s, ⟨le_of_lt hslt, le_of_lt hslt2⟩, hper⟩
    · exfalso
      exact (hdsub hsball) ⟨s, ⟨hsI, fun h => absurd h.2 (not_lt.mpr hsge2)⟩, rfl⟩
  · exfalso
    exact (hdsub hsball) ⟨s, ⟨hsI, fun h => absurd h.1 (not_lt.mpr hsge)⟩, rfl⟩

end

end Work.SphereJordan
