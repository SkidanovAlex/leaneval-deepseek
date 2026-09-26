import Submission.Work.Topology.Classical.Defs

/-!
# The separation statement of a `SchoenfliesData`

The classical content of "the two discs bounded by a Jordan curve cover the sphere and meet exactly
in the curve" is that the *open* parts of the two discs are disjoint and exhaust the complement of
the curve: the curve separates `A` into exactly two open parts.

This file derives that statement from the clauses of `Work.Topology.Classical.SchoenfliesData`
(covering, meeting and injectivity, the boundary being parametrised by `circlePoint`, and the
surjectivity of `circlePoint` onto the boundary circle of the model disc).  It is the sharpest
"Jordan separation" statement available in the vocabulary of this chapter. -/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.Classical

noncomputable section

/-- **The boundary of the model disc is the image of `circlePoint`**: every `z : 𝔻` of norm `1` is
`circlePoint θ` for some `θ`.  (From the surjectivity of polar coordinates in the plane.) -/
theorem eq_circlePoint_of_norm_eq_one (z : Disc) (hz : ‖(z : ℂ)‖ = 1) :
    ∃ θ : ℝ, z = circlePoint θ := by
  have h := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  rw [hz] at h
  exact ⟨Complex.arg (z : ℂ), Subtype.ext (by rw [circlePoint_coe]; simpa using h.symm)⟩

/-- **Jordan separation of a `SchoenfliesData`.**  The open parts of the two discs bounded by the
curve `c i` are disjoint, and they exhaust the complement of the curve in `A`: every point of `A`
that is not on the curve lies on exactly one of the two sides. -/
theorem separation_of_schoenfliesData {A : Set R3} {ι : Type} [Fintype ι] {c : ι → ℝ → R3}
    (D : SchoenfliesData A ι c) (i : ι) :
    Disjoint {x : A | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e i z = (x : R3)}
      {x : A | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e' i z = (x : R3)} ∧
    (∀ x : A, (x : R3) ∉ Set.range (c i) →
      (∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e i z = (x : R3)) ∨
      (∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e' i z = (x : R3))) := by
  constructor
  · refine Set.disjoint_left.mpr ?_
    rintro x ⟨z, hz, hzx⟩ ⟨z', hz', hz'x⟩
    have hmem : (x : R3) ∈ Set.range (D.e i) ∩ Set.range (D.e' i) :=
      ⟨⟨z, hzx⟩, ⟨z', hz'x⟩⟩
    rw [D.meet i] at hmem
    obtain ⟨θ, hθ⟩ := hmem
    have h1 : D.e i z = D.e i (circlePoint θ) := by rw [D.boundary i θ, hθ, ← hzx]
    have h2 : z = circlePoint θ := D.inj i h1
    have h3 : ‖(z : ℂ)‖ = 1 := by rw [h2, circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
    linarith
  · intro x hx
    have hmem : (x : R3) ∈ Set.range (D.e i) ∪ Set.range (D.e' i) := by
      rw [D.cover i]; exact x.2
    have hnorm_le : ∀ z : Disc, ‖(z : ℂ)‖ ≤ 1 := by
      intro z
      have h : dist (z : ℂ) 0 ≤ 1 := z.2
      rwa [dist_zero_right] at h
    rcases hmem with ⟨z, hz⟩ | ⟨z, hz⟩
    · refine Or.inl ?_
      by_cases hz1 : ‖(z : ℂ)‖ = 1
      · obtain ⟨θ, rfl⟩ := eq_circlePoint_of_norm_eq_one z hz1
        exact absurd (by rw [← hz, D.boundary i θ]; exact Set.mem_range_self θ) hx
      · exact ⟨z, lt_of_le_of_ne (hnorm_le z) hz1, hz⟩
    · refine Or.inr ?_
      by_cases hz1 : ‖(z : ℂ)‖ = 1
      · obtain ⟨θ, rfl⟩ := eq_circlePoint_of_norm_eq_one z hz1
        exact absurd (by rw [← hz, D.boundary' i θ]; exact Set.mem_range_self θ) hx
      · exact ⟨z, lt_of_le_of_ne (hnorm_le z) hz1, hz⟩

/-- **A connected set avoiding the curve lies on one side of it.**  This is the form of Jordan
separation which the innermost-curve arguments use: a preconnected subset of `A` disjoint from the
curve is contained in one of the two open discs bounded by it. -/
theorem preconnected_subset_openDisc_or_of_schoenfliesData {A : Set R3} {ι : Type} [Fintype ι]
    {c : ι → ℝ → R3} (D : SchoenfliesData A ι c) (i : ι) {s : Set A} (hs : IsPreconnected s)
    (hsv : ∀ x ∈ s, (x : R3) ∉ Set.range (c i)) :
    s ⊆ {x : A | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e i z = (x : R3)} ∨
      s ⊆ {x : A | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ D.e' i z = (x : R3)} := by
  obtain ⟨hdisj, hcover⟩ := separation_of_schoenfliesData D i
  refine IsPreconnected.subset_or_subset (D.open_interior i) (D.open_interior' i) hdisj ?_ hs
  intro x hx
  exact hcover x (hsv x hx)

end

end Work.Topology.Classical
