import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N4chain

/-- A finite set of reals misses some point of any open interval. -/
lemma exists_lt_lt_notMem_of_finite {S : Set ℝ} (hS : S.Finite) {a b : ℝ} (hab : a < b) :
    ∃ x : ℝ, a < x ∧ x < b ∧ x ∉ S := by
  by_contra h
  have hsub : Set.Ioo a b ⊆ S := fun x hx => by
    by_contra hxS
    exact h ⟨x, hx.1, hx.2, hxS⟩
  exact (Set.Ioo_infinite hab) (hS.subset hsub)

/-- Existence of a "good" radius for a Dirichlet L-function: for a character ψ mod N, a centre `cc` and `η > 0` such that the ball `ball cc (η+1)` contains no point equal to 1 (so `L(·,ψ)` is analytic there) and `L(cc,ψ) ≠ 0`, there is `R` with `η/2 < R ≤ η` whose two circles of radii `R` and `R/2` around `cc` are zero-free for `L(·,ψ)`. -/
theorem L_goodRadius {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {cc : ℂ} {η : ℝ} (hη : 0 < η) (hne : ∀ w : ℂ, w ∈ Metric.ball cc (η + 1) → w ≠ 1) (hcc : DirichletCharacter.LFunction ψ cc ≠ 0) : ∃ R : ℝ, η / 2 < R ∧ R ≤ η ∧ (∀ w : ℂ, ‖w - cc‖ = R → DirichletCharacter.LFunction ψ w ≠ 0) ∧ (∀ w : ℂ, ‖w - cc‖ = R / 2 → DirichletCharacter.LFunction ψ w ≠ 0) := by
  -- The L-function is analytic on the closed ball `U` of radius `η` around `cc` (which avoids `1`).
  set f : ℂ → ℂ := DirichletCharacter.LFunction ψ with hfdef
  set U : Set ℂ := Metric.closedBall cc η with hUdef
  have hccf : f cc ≠ 0 := by rw [hfdef]; exact hcc
  have hf_an_ball : AnalyticOnNhd ℂ f (Metric.ball cc (η + 1)) := by
    rw [hfdef]
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) Metric.isOpen_ball
    exact (DirichletCharacter.differentiableAt_LFunction ψ w (Or.inl (hne w hw))).differentiableWithinAt
  have hf_an : AnalyticOnNhd ℂ f U := hf_an_ball.mono (fun w hw => by
    rw [hUdef, Metric.mem_closedBall, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_eq_norm]
    linarith)
  have hcc_mem : cc ∈ U := by
    rw [hUdef, Metric.mem_closedBall, dist_eq_norm, sub_self, norm_zero]; exact hη.le
  have hpre : IsPreconnected U := by
    rw [hUdef]; exact (convex_closedBall cc η).isPreconnected
  have horder_cc : analyticOrderAt f cc ≠ ⊤ := by
    have hcc_an : AnalyticAt ℂ f cc := hf_an cc hcc_mem
    rw [(hcc_an.analyticOrderAt_eq_zero).2 hccf]
    exact ENat.zero_ne_top
  -- `f` has finite order at every point of `U` (else it would vanish identically on the connected
  -- set `U`, contradicting `f cc ≠ 0`).
  have horder_ne_top : ∀ u : U, meromorphicOrderAt f u.1 ≠ ⊤ := by
    intro u
    have hu_an : AnalyticAt ℂ f u.1 := hf_an u.1 u.2
    rw [hu_an.meromorphicOrderAt_eq]
    exact fun h =>
      (hf_an.analyticOrderAt_ne_top_of_isPreconnected hpre hcc_mem u.2 horder_cc)
        (ENat.map_eq_top_iff.mp h)
  -- Hence the zero set of `f` inside `U` is the support of its divisor, which is finite.
  have hzerofin : (f ⁻¹' {0} ∩ U).Finite := by
    have hset := MeromorphicNFOn.zero_set_eq_divisor_support (f := f) (U := U)
      hf_an.meromorphicNFOn horder_ne_top
    rw [Set.inter_comm, hset]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := f) (U := U) (V := U)
      hf_an.meromorphicOn (by rw [hUdef]; exact isCompact_closedBall cc η) (subset_refl U)
  set Z : Set ℂ := f ⁻¹' {0} ∩ U with hZdef
  have hZfin : Z.Finite := by rw [hZdef]; exact hzerofin
  -- Choose `R` avoiding the finitely many radii (and half-radii) of these zeros.
  have hEfin : ((fun z : ℂ => ‖z - cc‖) '' Z ∪
      (fun r : ℝ => 2 * r) '' ((fun z : ℂ => ‖z - cc‖) '' Z)).Finite :=
    (hZfin.image _).union ((hZfin.image _).image _)
  obtain ⟨R, hR1, hR2lt, hRnotE⟩ :=
    exists_lt_lt_notMem_of_finite hEfin (by linarith : η / 2 < η)
  have hR2 : R ≤ η := le_of_lt hR2lt
  refine ⟨R, hR1, hR2, ?_, ?_⟩
  · intro w hw hw0
    have hw0' : f w = 0 := by rw [hfdef]; exact hw0
    have hwZ : w ∈ Z := by
      rw [hZdef]
      exact ⟨by simpa using hw0', by
        rw [hUdef, Metric.mem_closedBall, dist_eq_norm, hw]; exact hR2⟩
    exact hRnotE (Or.inl ⟨w, hwZ, hw⟩)
  · intro w hw hw0
    have hw0' : f w = 0 := by rw [hfdef]; exact hw0
    have hwZ : w ∈ Z := by
      rw [hZdef]
      exact ⟨by simpa using hw0', by
        rw [hUdef, Metric.mem_closedBall, dist_eq_norm, hw]; linarith⟩
    exact hRnotE (Or.inr ⟨R / 2, ⟨w, hwZ, hw⟩, by ring⟩)

end Work.BMF.N4chain
