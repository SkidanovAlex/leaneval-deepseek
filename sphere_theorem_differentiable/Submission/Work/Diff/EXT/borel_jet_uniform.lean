import Mathlib
import Submission.Work.Diff.EXT.borel_jet_on
import Submission.Work.Diff.EXT.borel_smul_cutoff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter Set
open scoped Topology ContDiff

namespace Work.Diff.EXT

/-- **Borel's theorem on jets, realised by a globally smooth function.**

This is the same statement as `Work.Diff.EXT.borel_jet_on`, except that the realising function `F`
is required to be smooth on *all* of `ℝ × E` (there the smoothness is only asserted on a slab
`(-ε, ε) ×ˢ W` around `{0} × W`).

The proof takes a local realisation `F₀` of the jets (provided by `borel_jet_on`, smooth on
`(-ε₀, ε₀) ×ˢ W₀`), a ball `ball y₀ r ⊆ W₀`, and multiplies `F₀` by the smooth cut-off
`ρ (t, y) = ψ t * β y`, where `ψ` is a bump equal to `1` on `[-ε₀/2, ε₀/2]` with
`tsupport ψ ⊆ (-ε₀, ε₀)` and `β` is a bump equal to `1` on `closedBall y₀ (r/2)` with
`tsupport β ⊆ W₀`.  Then `ρ • F₀` is globally smooth (`borel_smul_cutoff`), while on the smaller
neighbourhood `ball y₀ (r/2)` the `t`-slices agree with those of `F₀` near `t = 0`, so the jets at
`0` are unchanged. -/
theorem borel_jet_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {U : Set E} (hU : IsOpen U) (f : ℕ → E → Z) (hf : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (f k) U)
    {y₀ : E} (hy₀ : y₀ ∈ U) :
    ∃ ε > 0, ∃ W : Set E, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ U ∧ ∃ F : ℝ × E → Z,
      ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ k : ℕ, ∀ y ∈ W, iteratedDeriv k (fun t : ℝ => F (t, y)) 0 = f k y := by
  -- A local realisation of the jets, smooth on a slab around `{0} × W₀`.
  obtain ⟨ε₀, hε₀pos, W₀, hW₀open, hy₀W₀, hW₀U, F₀, hF₀sm, hjet₀⟩ :=
    borel_jet_on hU f hf hy₀
  -- A ball around `y₀` inside `W₀`.
  obtain ⟨r, hrpos, hrW⟩ : ∃ r > 0, Metric.ball y₀ r ⊆ W₀ :=
    Metric.isOpen_iff.mp hW₀open y₀ hy₀W₀
  -- The two cut-off bumps, in the time and in the space variable.
  let ψ : ContDiffBump (0 : ℝ) := ⟨ε₀ / 2, 3 * ε₀ / 4, by linarith, by linarith⟩
  let β : ContDiffBump y₀ := ⟨r / 2, 3 * r / 4, by linarith, by linarith⟩
  -- The product cut-off.
  let ρ : ℝ × E → ℝ := fun p => (ψ : ℝ → ℝ) p.1 * (β : E → ℝ) p.2
  have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × E => (ψ : ℝ → ℝ) p.1) :=
      ψ.contDiff.comp_continuousLinearMap (g := ContinuousLinearMap.fst ℝ ℝ E)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × E => (β : E → ℝ) p.2) :=
      β.contDiff.comp_continuousLinearMap (g := ContinuousLinearMap.snd ℝ ℝ E)
    exact h1.mul h2
  have hψrOut : ψ.rOut = 3 * ε₀ / 4 := rfl
  have hβrOut : β.rOut = 3 * r / 4 := rfl
  -- The supports of the two factors.
  have hψsupp : tsupport (ψ : ℝ → ℝ) ⊆ Set.Ioo (-ε₀) ε₀ := by
    rw [ContDiffBump.tsupport_eq, hψrOut]
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at ht
    obtain ⟨hl, hr⟩ := abs_le.mp ht
    exact ⟨by linarith, by linarith⟩
  have hβsupp : tsupport (β : E → ℝ) ⊆ W₀ := by
    rw [ContDiffBump.tsupport_eq, hβrOut]
    intro y hy
    rw [Metric.mem_closedBall] at hy
    exact hrW (by rw [Metric.mem_ball]; linarith)
  -- The support of the product is contained in the slab on which `F₀` is smooth.
  have hsupp : tsupport ρ ⊆ Set.Ioo (-ε₀) ε₀ ×ˢ W₀ := by
    have hSclosed : IsClosed {p : ℝ × E |
        p.1 ∈ tsupport (ψ : ℝ → ℝ) ∧ p.2 ∈ tsupport (β : E → ℝ)} :=
      ((isClosed_tsupport (ψ : ℝ → ℝ)).preimage continuous_fst).inter
        ((isClosed_tsupport (β : E → ℝ)).preimage continuous_snd)
    have h1 : tsupport ρ ⊆ {p : ℝ × E |
        p.1 ∈ tsupport (ψ : ℝ → ℝ) ∧ p.2 ∈ tsupport (β : E → ℝ)} := by
      rw [tsupport]
      refine (IsClosed.closure_subset_iff hSclosed).mpr ?_
      intro p hp
      rw [Function.mem_support] at hp
      exact ⟨subset_tsupport _ (fun h => hp (by simp [ρ, h])),
        subset_tsupport _ (fun h => hp (by simp [ρ, h]))⟩
    intro p hp
    obtain ⟨h1p, h2p⟩ := h1 hp
    exact ⟨hψsupp h1p, hβsupp h2p⟩
  -- The globally smooth realisation and the smaller neighbourhood.
  refine ⟨1, one_pos, Metric.ball y₀ (r / 2), Metric.isOpen_ball,
    Metric.mem_ball_self (by linarith),
    fun y hy => hW₀U (hrW (Metric.ball_subset_ball (by linarith) hy)),
    fun p => ρ p • F₀ p,
    borel_smul_cutoff ρ hρ (isOpen_Ioo.prod hW₀open) hsupp F₀ hF₀sm, ?_⟩
  -- The `t`-jets at `0` are those of `F₀`, since the cut-off is `1` near `0`.
  intro k y hy
  have hβy : (β : E → ℝ) y = 1 := by
    refine β.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall]
    have h : dist y y₀ < r / 2 := Metric.mem_ball.mp hy
    have hrIn : β.rIn = r / 2 := rfl
    rw [hrIn]
    exact le_of_lt h
  have hslice : (fun t : ℝ => (fun p : ℝ × E => ρ p • F₀ p) (t, y)) =ᶠ[𝓝 0]
      (fun t : ℝ => F₀ (t, y)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : -(ε₀ / 2) < (0 : ℝ))
      (by linarith : (0 : ℝ) < ε₀ / 2)] with t ht
    have hψt : (ψ : ℝ → ℝ) t = 1 := by
      refine ψ.one_of_mem_closedBall ?_
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      have hrIn : ψ.rIn = ε₀ / 2 := rfl
      rw [hrIn]
      exact le_of_lt (abs_lt.mpr ⟨ht.1, ht.2⟩)
    simp [ρ, hψt, hβy]
  exact (Filter.EventuallyEq.iteratedDeriv_eq k hslice).trans
    (hjet₀ k y (hrW (Metric.ball_subset_ball (by linarith) hy)))

end Work.Diff.EXT
