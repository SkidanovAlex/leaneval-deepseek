import Mathlib

open Filter Topology

namespace Work.Asymptotics

/-- Changing the single value of an even differentiable function at `0` to `0` does not change its
positive-order iterated derivatives: with `g r = if r = 0 then 0 else f r` one has
`iteratedDeriv l g = iteratedDeriv l f` for every `l ≥ 1`.  (`deriv` is a local notion, so only
`deriv g 0 = deriv f 0` needs care: either `f 0 = 0`, and then `g = f`; or `f 0 ≠ 0`, and then `g`
is discontinuous at `0`, hence not differentiable there, so `deriv g 0 = 0 = deriv f 0` by evenness
of `f`.) -/
theorem punctured_iteratedDeriv {f : ℝ → ℂ} (heven : ∀ r : ℝ, f (-r) = f r)
    (hdiff : Differentiable ℝ f) :
    ∀ l : ℕ, 1 ≤ l →
      iteratedDeriv l (fun r : ℝ => if r = 0 then 0 else f r) = iteratedDeriv l f := by
  classical
  set g : ℝ → ℂ := fun r => if r = 0 then 0 else f r with hg_def
  have hg0 : g 0 = 0 := by rw [hg_def]; simp
  have heq_off : ∀ {s : ℝ}, s ≠ 0 → g s = f s := by
    intro s hs
    rw [hg_def]
    show (if s = 0 then 0 else f s) = f s
    rw [if_neg hs]
  -- An even function has vanishing derivative at `0`.
  have hf_even : deriv f 0 = 0 := by
    have h1 : deriv (fun r : ℝ => f (-r)) 0 = deriv f 0 := by
      have : (fun r : ℝ => f (-r)) = f := by funext r; exact heven r
      rw [this]
    have h2 : deriv (fun r : ℝ => f (-r)) 0 = - deriv f 0 := by
      rw [deriv_comp_neg, neg_zero]
    have h3 : deriv f 0 = - deriv f 0 := h1.symm.trans h2
    exact add_self_eq_zero.mp ((eq_neg_iff_add_eq_zero (b := deriv f 0)).mp h3)
  -- Pointwise equality of first derivatives.
  have hderiv : deriv g = deriv f := by
    funext r
    by_cases hr : r = 0
    · subst hr
      by_cases hf0 : f 0 = 0
      · have hgf : g = f := by
          funext s
          by_cases hs : s = 0
          · subst hs; rw [hg0, hf0]
          · exact heq_off hs
        rw [hgf]
      · rw [hf_even]
        apply deriv_zero_of_not_differentiableAt
        intro hd
        have hgf_punct : g =ᶠ[𝓝[≠] (0:ℝ)] f := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          exact heq_off (by simpa using hs)
        have hftend : Filter.Tendsto f (𝓝[≠] (0:ℝ)) (𝓝 (f 0)) :=
          ((hdiff 0).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
        have hgtend₁ : Filter.Tendsto g (𝓝[≠] (0:ℝ)) (𝓝 (0:ℂ)) := by
          have h : Filter.Tendsto g (𝓝[≠] (0:ℝ)) (𝓝 (g 0)) :=
            hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
          rw [hg0] at h
          exact h
        have hgtend₂ : Filter.Tendsto g (𝓝[≠] (0:ℝ)) (𝓝 (f 0)) :=
          hftend.congr' hgf_punct.symm
        exact hf0 (tendsto_nhds_unique hgtend₁ hgtend₂).symm
    · have hev : g =ᶠ[𝓝 r] f := by
        filter_upwards [isOpen_ne.mem_nhds hr] with s hs
        exact heq_off hs
      exact hev.deriv_eq
  intro l hl
  refine Nat.le_induction ?base ?step l hl
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    exact hderiv
  · intro n hn ih
    simp only [iteratedDeriv_succ, ih]

end Work.Asymptotics
