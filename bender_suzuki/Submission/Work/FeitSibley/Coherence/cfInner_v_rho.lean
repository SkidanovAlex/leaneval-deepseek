import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.engine

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.Coherence

open Classical

/-- If an integral linear map `ρ` preserves the character inner product on all of `ℤ[S]` and `S`
is orthonormal, then subtracting from an arbitrary `T` its orthogonal projection onto the family
`ρ '' S` makes the result orthogonal to every `ρ y`, `y ∈ S`.

Concretely: writing `⟨·,·⟩` for `cfInner`,
`T - ∑_{y' ∈ S} ⟨T, ρ y'⟩ • ρ y'` is orthogonal to each `ρ y`.

The point is that `⟨ρ y', ρ y⟩ = ⟨y', y⟩ = δ_{y'y}` for `y', y ∈ S`: the isometry hypothesis
replaces the inner product of the images by the inner product of the two orthonormal
irreducibles `y', y` in the source. -/
theorem cfInner_sub_proj_eq_zero {H G : Type} [Group H] [Fintype H] [Group G] [Fintype G]
    {S : Finset (H → ℂ)} {ρ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hρ : Work.Coherence.IsometryOnAll S ρ)
    (horth : Work.Coherence.Orthonormal S) (T : G → ℂ) :
    ∀ y ∈ S, Work.Coherence.cfInner
      (T - ∑ y' ∈ S, (Work.Coherence.cfInner T (ρ y') : ℂ) • ρ y') (ρ y) = 0 := by
  intro y hy
  rw [Work.Coherence.cfInner_sub_left]
  -- each summand pairs against `ρ y` to `⟨T, ρ y'⟩ · δ_{y' y}`
  have hterm : ∀ y' ∈ S, Work.Coherence.cfInner
        ((Work.Coherence.cfInner T (ρ y') : ℂ) • ρ y') (ρ y)
      = (Work.Coherence.cfInner T (ρ y') : ℂ) * (if y' = y then 1 else 0) := by
    intro y' hy'
    rw [Work.Coherence.cfInner_smul_left]
    congr 1
    rw [hρ.inner_eq y' (Work.Coherence.self_mem_zSpan hy') y (Work.Coherence.self_mem_zSpan hy)]
    exact horth y' hy' y hy
  have hsum : Work.Coherence.cfInner
      (∑ y' ∈ S, (Work.Coherence.cfInner T (ρ y') : ℂ) • ρ y') (ρ y)
      = Work.Coherence.cfInner T (ρ y) := by
    rw [Work.Coherence.cfInner_sum_left]
    have hstep : ∑ y' ∈ S, Work.Coherence.cfInner
          ((Work.Coherence.cfInner T (ρ y') : ℂ) • ρ y') (ρ y)
        = ∑ y' ∈ S, (Work.Coherence.cfInner T (ρ y') : ℂ) * (if y' = y then 1 else 0) :=
      Finset.sum_congr rfl hterm
    rw [hstep,
      Finset.sum_eq_single y (fun b _ hne => by simp [hne]) (fun hycon => absurd hy hycon)]
    simp
  rw [hsum, sub_self]

/-- Peterfalvi II, Appendice XII: the residual of an arbitrary class function `T` after
orthogonal projection onto the Dade isometry's image of `𝒮(Q')` is orthogonal to every member
of that image.  This is the "orthogonality of the two blocks" step, in the special case where
only the `𝒮(Q')` block is projected out.

The hypothesis `hρ` that `ρ` is an isometry on all of `ℤ[𝒮(Q')]` together with the
orthonormality of `𝒮(Q')` (two distinct irreducibles of `H`) is exactly what is needed: the
Gram matrix of the family `ρ '' 𝒮(Q')` is the identity. -/
theorem cfInner_v_rho {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {ρ : (↥h.H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hρ : Work.Coherence.IsometryOnAll
      (Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h)) ρ)
    (T : G → ℂ) :
    ∀ y ∈ Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h),
      Work.Coherence.cfInner
        (T - ∑ y' ∈ Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSQcomm h),
          (Work.Coherence.cfInner T (ρ y') : ℂ) • ρ y') (ρ y) = 0 :=
  cfInner_sub_proj_eq_zero hρ (scriptSR_Qcomm_orthonormal h) T

end Work.FeitSibley.Coherence
