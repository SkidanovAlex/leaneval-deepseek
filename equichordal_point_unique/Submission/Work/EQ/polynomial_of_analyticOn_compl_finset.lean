import Mathlib
import Submission.Work.EQ.FillDefs
import Submission.Work.EQ.entire_of_polyGrowth
import Submission.Work.EQ.differentiableAt_fill_of_mem

namespace Work.EQ

open Filter _root_.Topology Metric

/-- `fill f P` inherits polynomial growth from `f`: outside a disc large enough to contain
all points of `P`, the two functions agree. -/
lemma fill_growth {f : ℂ → ℂ} {P : Finset ℂ}
    (hgrow : ∃ (m : ℕ) (C R : ℝ), 0 < C ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ m) :
    ∃ (m : ℕ) (C R : ℝ), 0 < C ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖fill f P z‖ ≤ C * ‖z‖ ^ m := by
  obtain ⟨m, C, R, hC, hbound⟩ := hgrow
  set M : ℝ := ∑ p ∈ P, (‖p‖ + 1) with hM
  refine ⟨m, C, max R M, hC, fun z hz => ?_⟩
  have hzP : z ∉ P := by
    intro hmem
    have h1 : ‖z‖ + 1 ≤ M := by
      rw [hM]
      exact Finset.single_le_sum (f := fun p : ℂ => ‖p‖ + 1) (fun p _ => by positivity) hmem
    have h2 : M ≤ max R M := le_max_right _ _
    have h3 : max R M ≤ ‖z‖ := hz
    linarith
  rw [fill_of_notMem hzP]
  exact hbound z (le_trans (le_max_left _ _) hz)

/-- The filled function is entire: off `P` it agrees locally with the analytic `f`, and at the
points of `P` the removable singularity theorem applies. -/
lemma differentiable_fill {f : ℂ → ℂ} {P : Finset ℂ}
    (hf : AnalyticOnNhd ℂ f (↑P)ᶜ)
    (hbdd : ∀ p ∈ P, ∃ C : ℝ, ∀ᶠ z in nhdsWithin p {p}ᶜ, ‖f z‖ ≤ C) :
    Differentiable ℂ (fill f P) := by
  intro z
  by_cases hz : z ∈ P
  · exact differentiableAt_fill_of_mem hf hbdd hz
  · have hclosed : IsClosed (↑P : Set ℂ) := P.finite_toSet.isClosed
    have hmem : (↑P : Set ℂ)ᶜ ∈ 𝓝 z := hclosed.isOpen_compl.mem_nhds (by simpa using hz)
    have hev : fill f P =ᶠ[𝓝 z] f := by
      filter_upwards [hmem] with w hw
      exact fill_of_notMem (by simpa using hw)
    exact (hf z (by simpa using hz)).differentiableAt.congr_of_eventuallyEq hev

/-- **Removable singularities at a finite set + polynomial growth.** If `f` is holomorphic off a
finite set `P`, is locally bounded near each point of `P`, and has polynomial growth at infinity,
then `f` agrees off `P` with a polynomial.

Suggested route: fill the finitely many points of `P` using `Function.update` with
`limUnder (nhdsWithin p {p}ᶜ) f`; analyticity of the filled function at `p` follows from
`Complex.differentiableOn_update_limUnder_of_bddAbove` (take a ball around `p` meeting
`P \ {p}` trivially) plus `DifferentiableAt.congr_of_eventuallyEq`. Enlarge `R` past the moduli of
the points of `P` so that the bound holds for all `z` with `R ≤ ‖z‖`. The filled function is entire
of polynomial growth, hence a polynomial: either show that all derivatives of order `> m` vanish
(`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` on circles of large radius, letting
the radius tend to infinity) or apply Liouville to the Taylor remainder divided by `z ^ (m + 1)`. -/
theorem polynomial_of_analyticOn_compl_finset {f : ℂ → ℂ} {P : Finset ℂ}
    (hf : AnalyticOnNhd ℂ f (↑P)ᶜ)
    (hbdd : ∀ p ∈ P, ∃ C : ℝ, ∀ᶠ z in nhdsWithin p {p}ᶜ, ‖f z‖ ≤ C)
    (hgrow : ∃ (m : ℕ) (C R : ℝ), 0 < C ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ m) :
    ∃ N : Polynomial ℂ, ∀ z : ℂ, z ∉ P → f z = N.eval z := by
  obtain ⟨N, hN⟩ := entire_of_polyGrowth (differentiable_fill hf hbdd) (fill_growth hgrow)
  exact ⟨N, fun z hz => (fill_of_notMem hz).symm.trans (hN z)⟩

end Work.EQ
