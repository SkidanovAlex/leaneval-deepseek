import Mathlib
import Submission.Work.Smooth.Jordan.Separation

/-!
# The bounded side of a Jordan curve lies in any closed convex set containing it

If the trace of the simple closed curve `c` is contained in a closed convex set `C ⊆ ℂ`, then the
whole region bounded by `c` is contained in `C`, and hence so is the image of the Schoenflies
embedding `e : 𝔻 → ℂ`, whose range is the closure of that region.

The proof is the classical "ray to infinity" argument, and it only uses *separation* of the plane
by the curve (the bounded side `V` is bounded and the complement of the trace is the disjoint union
of `U` and `V`), not the Schoenflies embedding.  Suppose `x` lies in the bounded side `V` but not
in `C`.  Since `C` is closed and convex, the Hahn–Banach theorem (Mathlib's
`geometric_hahn_banach_closed_point`, strict separation of a point from a closed convex set)
produces a nonzero real-linear functional `f` whose values on `C` are strictly below `f x`.  The
ray `t ↦ x + t • d`, `t ≥ 0`, taken along a direction `d` with `f d = 1`, therefore meets neither
`C` nor — since `c.trace ⊆ C` — the trace of `c`.  That ray is preconnected and contains `x ∈ V`,
so, the complement of the trace being the disjoint union of the two sides `U`, `V`, the ray must
lie entirely in `V`.  But the ray is unbounded, contradicting the boundedness of `V` given by
Jordan separation.
-/

open Set

namespace Work.Smooth.Jordan

noncomputable section

/-- **The bounded side of a Jordan curve inside a closed convex set.**  If the trace of `c` is
contained in a closed convex set `C`, then the bounded side `h.V` of `c` is contained in `C`.

This is the core geometric statement; it needs only Jordan separation, not the Schoenflies
embedding. -/
theorem plane_separation_V_subset_of_convex {c : PlaneCurve} (h : PlaneSeparation c) {C : Set ℂ}
    (hC : Convex ℝ C) (hCc : IsClosed C) (htrace : c.trace ⊆ C) : h.V ⊆ C := by
  intro x hxV
  by_contra hxC
  -- Strict separation of the point `x` from the closed convex set `C`.
  obtain ⟨f, u, hfu, hux⟩ :=
    geometric_hahn_banach_closed_point (E := ℂ) hC hCc hxC
  -- `f` is nonzero, since it separates a point of the trace (which lies in `C`) from `x`.
  have hfne : ∃ y : ℂ, f y ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ y : ℂ, f y = 0 := fun y => by
      by_contra h
      exact hcon ⟨y, h⟩
    have hCmem : c.γ 0 ∈ C := htrace (PlaneCurve.mem_trace c 0)
    have h1 : f (c.γ 0) < u := hfu _ hCmem
    rw [hcon' (c.γ 0)] at h1
    rw [hcon' x] at hux
    linarith
  obtain ⟨y, hy⟩ := hfne
  -- A direction on which `f` is positive.
  set d : ℂ := (f y)⁻¹ • y with hd
  have hfd : f d = 1 := by
    rw [hd, map_smul, smul_eq_mul, inv_mul_cancel₀ hy]
  have hd_ne : d ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hfd
    exact one_ne_zero hfd.symm
  -- The ray from `x` in the direction `d`.
  set R : Set ℂ := (fun t : ℝ => x + t • d) '' (Set.Ici 0) with hR
  have hRpre : IsPreconnected R := by
    rw [hR]
    exact isPreconnected_Ici.image _ (by fun_prop)
  have hxR : x ∈ R := by
    rw [hR]
    exact ⟨0, by simp, by simp⟩
  -- The ray avoids the trace of `c`, because it avoids `C ⊇ c.trace`.
  have hRsubC : R ⊆ c.traceᶜ := by
    rintro z ⟨t, ht, rfl⟩ hz
    have ht0 : (0 : ℝ) ≤ t := Set.mem_Ici.mp ht
    obtain ⟨s, hs⟩ := hz
    have hCmem : c.γ s ∈ C := htrace ⟨s, rfl⟩
    have h1 : f (c.γ s) < u := hfu _ hCmem
    have h2 : f (x + t • d) = f x + t := by
      rw [map_add, map_smul, hfd, smul_eq_mul, mul_one]
    rw [hs, h2] at h1
    linarith
  -- The ray therefore lies on one side of the curve, and it meets `V` at `x`.
  have hsub : R ⊆ h.U ∪ h.V := by
    rw [h.union_eq]
    exact hRsubC
  rcases hRpre.subset_or_subset h.isOpen_U h.isOpen_V h.disjoint_UV hsub with hRU | hRV
  · exact Set.disjoint_left.mp h.disjoint_UV (hRU hxR) hxV
  · -- The ray is unbounded, so `V` would be unbounded, contradicting Jordan separation.
    have hbR : Bornology.IsBounded R := h.bounded_V.subset hRV
    rw [isBounded_iff_forall_norm_le] at hbR
    obtain ⟨M, hM⟩ := hbR
    have hM0 : 0 ≤ M := le_trans (norm_nonneg x) (hM x hxR)
    have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
    set t : ℝ := (M + ‖x‖ + 1) / ‖d‖ with ht
    have ht0 : 0 ≤ t := by
      rw [ht]
      positivity
    have hmemR : x + t • d ∈ R := by
      rw [hR]
      exact ⟨t, by simpa using ht0, rfl⟩
    have hbnd : ‖x + t • d‖ ≤ M := hM _ hmemR
    have htdnorm : ‖t • d‖ = M + ‖x‖ + 1 := by
      rw [norm_smul, Real.norm_of_nonneg ht0, ht]
      field_simp
    have hsplit : ‖t • d‖ ≤ ‖x + t • d‖ + ‖x‖ := by
      have h2 := norm_add_le (x + t • d) (-x)
      rw [show (x + t • d) + (-x) = t • d by abel, norm_neg] at h2
      exact h2
    linarith

/-- **Schoenflies outside a closed convex set.**  If the trace of `c` is contained in a closed
convex set `C`, then so is the image of the spanning embedding `h.e`, i.e. the closure of the
bounded side of `c`. -/
theorem plane_schoenflies_convex {c : PlaneCurve} (h : PlaneSchoenflies c) {C : Set ℂ}
    (hC : Convex ℝ C) (hCc : IsClosed C) (htrace : c.trace ⊆ C) : Set.range h.e ⊆ C := by
  rw [h.range_e]
  exact hCc.closure_subset_iff.mpr
    (plane_separation_V_subset_of_convex h.toPlaneSeparation hC hCc htrace)

end

end Work.Smooth.Jordan
