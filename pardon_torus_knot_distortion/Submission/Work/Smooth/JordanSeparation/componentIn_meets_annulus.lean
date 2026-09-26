import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs
import Submission.Work.Smooth.JordanSeparation.annulus_mem_nhds_of_regular
import Submission.Work.Smooth.JordanSeparation.frontier_component_meets_regular

/-!
# Every component of the complement of the curve meets the offset annulus

Given a `C¹` `2π`-periodic curve `c`, a continuous `2π`-periodic field `v` and `δ > 0` such that
the offset map `(t,u) ↦ c.γ t + u·v t` is injective in `u` on the strip `|u| < δ`, **every
connected component of the complement of the trace meets the annulus** `offset c v '' (ℝ×(-δ,δ))`.

The proof splits on whether `c` is an immersion somewhere.
* If `deriv c.γ` is nonzero somewhere, the frontier of any component `W` of the complement contains
  a regular point `c.γ t` (`frontier_component_meets_regular`); at a regular point the annulus is a
  neighbourhood of `c.γ t` (`annulus_mem_nhds_of_regular`), and since `c.γ t` lies in the frontier
  of `W`, that neighbourhood meets `W`.
* If `deriv c.γ` vanishes identically, then `c` is constant: the trace is a single point, the
  complement is connected, and it contains all the other offset points `c.γ 0 + u·v 0`.
-/

open Set

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- The field `v` never vanishes, since otherwise the offset map would identify `(t,0)` and
`(t,u)` for `u ≠ 0`. -/
theorem v_ne_zero_of_offset_inj (c : Work.Smooth.Jordan.SmoothPlaneCurve) {v : ℝ → ℂ} {δ : ℝ}
    (hδ : 0 < δ)
    (hinj : ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      Work.Smooth.JordanSeparation.offset c v (t, u)
        = Work.Smooth.JordanSeparation.offset c v (t', u') → u = u') :
    ∀ t : ℝ, v t ≠ 0 := by
  intro t hv0
  have hu : |δ / 2| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
  have h0 : |(0 : ℝ)| < δ := by simpa using hδ
  have heq : Work.Smooth.JordanSeparation.offset c v (t, δ / 2)
      = Work.Smooth.JordanSeparation.offset c v (t, 0) := by
    simp [Work.Smooth.JordanSeparation.offset_def, hv0]
  have := hinj t t (δ / 2) 0 hu h0 heq
  linarith

/-- **Every component of the complement meets the annulus.** -/
theorem componentIn_meets_annulus (c : Work.Smooth.Jordan.SmoothPlaneCurve) {v : ℝ → ℂ}
    {δ : ℝ}
    (hv : Continuous v) (hδ : 0 < δ) (hper : Function.Periodic v (2 * Real.pi))
    (htrace : c.trace ⊆ Work.Smooth.JordanSeparation.annulus c v δ)
    (hinj : ∀ t t' u u' : ℝ, |u| < δ → |u'| < δ →
      Work.Smooth.JordanSeparation.offset c v (t, u)
        = Work.Smooth.JordanSeparation.offset c v (t', u') → u = u') :
    ∀ z : ℂ, z ∉ c.trace →
      (connectedComponentIn c.traceᶜ z ∩ Work.Smooth.JordanSeparation.annulus c v δ).Nonempty := by
  intro z hz
  by_cases hnc : ∃ t : ℝ, deriv c.γ t ≠ 0
  · obtain ⟨t, htfront, htreg⟩ :=
      frontier_component_meets_regular c hv hδ hper hinj hnc hz
    have hnhds : Work.Smooth.JordanSeparation.annulus c v δ ∈ nhds (c.γ t) :=
      annulus_mem_nhds_of_regular c hv hδ hper hinj htreg
    have hcl : c.γ t ∈ closure (connectedComponentIn c.traceᶜ z) := by
      have h := htfront
      rw [frontier_eq_closure_inter_closure] at h
      exact h.1
    obtain ⟨U, hUsub, hUopen, hUt⟩ := mem_nhds_iff.mp hnhds
    obtain ⟨a, haU, haW⟩ := mem_closure_iff.mp hcl U hUopen hUt
    exact ⟨a, haW, hUsub haU⟩
  · push_neg at hnc
    have hconst : ∀ s s' : ℝ, c.γ s = c.γ s' :=
      is_const_of_deriv_eq_zero c.differentiable hnc
    have htrace_single : c.trace = {c.γ 0} := by
      ext y
      constructor
      · rintro ⟨s, rfl⟩; exact hconst s 0
      · rintro rfl; exact ⟨0, rfl⟩
    have hpre : IsPreconnected c.traceᶜ := by
      rw [htrace_single]
      exact (isConnected_compl_singleton_of_one_lt_rank
        (by rw [Complex.rank_real_complex]; norm_num) (c.γ 0)).2
    have hsub : c.traceᶜ ⊆ connectedComponentIn c.traceᶜ z :=
      IsPreconnected.subset_connectedComponentIn hpre hz (le_refl _)
    refine ⟨Work.Smooth.JordanSeparation.offset c v (0, δ / 2), ?_, ?_⟩
    · apply hsub
      rw [htrace_single, Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h0
      have h0' : Work.Smooth.JordanSeparation.offset c v (0, δ / 2)
          = Work.Smooth.JordanSeparation.offset c v (0, 0) := by
        rw [Work.Smooth.JordanSeparation.offset_zero]; exact h0
      have hlt : |δ / 2| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
      have h0lt : |(0 : ℝ)| < δ := by simpa using hδ
      have := hinj 0 0 (δ / 2) 0 hlt h0lt h0'
      linarith
    · exact ⟨(0, δ / 2), ⟨trivial, by constructor <;> linarith⟩, rfl⟩

end

end Work.Smooth.JordanSeparation
