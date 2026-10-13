import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.EllSol.PkgK5.InterpTraceCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.InterpTrace

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The radial weight `w²` is continuous on `(0,∞)`. -/
theorem continuousOn_w_sq_Ioi : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact ContinuousOn.pow (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))) 2

/-- **Differentiation under the integral sign for the `m`-integrand.**

For a weight `c` continuous on `[a,b]` with `0 < a ≤ b`, and a datum `ψ` that is `C^∞` on the
open quadrant `(0,∞) × (0,π/2)`, the parametric integral
`θ ↦ ∫_a^b c z * ψ z θ * ∂_θψ z θ dz` is differentiable at `θ₀ ∈ (0,π/2)` with derivative
`∫_a^b c z (∂_θψ z θ₀)² dz + ∫_a^b c z ψ z θ₀ ∂_θ²ψ z θ₀ dz`. -/
theorem hasDerivAt_integral_mul_pth {c : ℝ → ℝ} {a b θ₀ : ℝ} {ψ : ℝ → ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : ContinuousOn c (Set.uIcc a b))
    (hψ : Work.FTS.EllipticEst.SmoothOpen ψ)
    (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ => ∫ z in a..b, c z * ψ z θ * Work.Spaces.pth ψ z θ)
      ((∫ z in a..b, c z * (Work.Spaces.pth ψ z θ₀) ^ 2)
        + (∫ z in a..b, c z * ψ z θ₀ * Work.Spaces.pthIter 2 ψ z θ₀)) θ₀ := by
  -- the open neighbourhood `(t₁,t₂) ∋ θ₀` and the open interval `(a,b)`
  set t₁ : ℝ := θ₀ / 2 with ht₁
  set t₂ : ℝ := (θ₀ + Real.pi / 2) / 2 with ht₂
  have hπ : 0 < Real.pi := Real.pi_pos
  have ht₁0 : 0 < t₁ := by rw [ht₁]; linarith [hθ₀.1]
  have ht₂π : t₂ < Real.pi / 2 := by rw [ht₂]; linarith [hθ₀.2]
  have hθ₀mem : θ₀ ∈ Set.Ioo t₁ t₂ :=
    ⟨by rw [ht₁]; linarith [hθ₀.1], by rw [ht₂]; linarith [hθ₀.2]⟩
  -- the interval endpoints lie in `(0,∞)`
  have hIocc : Set.uIoc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    have h1 : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
    rw [Set.uIcc_of_le hab] at h1
    exact lt_of_lt_of_le ha h1.1
  -- slices of a smooth datum are continuous on the radial interval
  have sliceOf : ∀ {g : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen g →
      ∀ x ∈ Set.Ioo t₁ t₂, ContinuousOn (fun t : ℝ => g t x) (Set.uIcc a b) := by
    intro g hg x hx
    refine hg.continuousOn.comp ((continuous_id.prodMk continuous_const).continuousOn)
      (fun t ht => ?_)
    have h1 : t ∈ Set.Icc a b := by rw [Set.uIcc_of_le hab] at ht; exact ht
    show (t, x) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)
    exact ⟨lt_of_lt_of_le ha h1.1, lt_of_lt_of_le ht₁0 (le_of_lt hx.1), lt_trans hx.2 ht₂π⟩
  -- the integrand and its candidate `θ`-derivative
  set F : ℝ → ℝ → ℝ := fun x t => c t * ψ t x * Work.Spaces.pth ψ t x with hF
  set F' : ℝ → ℝ → ℝ := fun x t => c t * (Work.Spaces.pth ψ t x * Work.Spaces.pth ψ t x
    + ψ t x * Work.Spaces.pthIter 2 ψ t x) with hF'
  have hFcont : ∀ x ∈ Set.Ioo t₁ t₂, ContinuousOn (F x) (Set.uIcc a b) := by
    intro x hx
    change ContinuousOn (fun t : ℝ => c t * ψ t x * Work.Spaces.pth ψ t x) (Set.uIcc a b)
    exact (hc.mul (sliceOf hψ x hx)).mul (sliceOf hψ.pth x hx)
  have hF'cont : ∀ x ∈ Set.Ioo t₁ t₂, ContinuousOn (F' x) (Set.uIcc a b) := by
    intro x hx
    change ContinuousOn (fun t : ℝ => c t * (Work.Spaces.pth ψ t x * Work.Spaces.pth ψ t x
      + ψ t x * Work.Spaces.pthIter 2 ψ t x)) (Set.uIcc a b)
    exact hc.mul (((sliceOf hψ.pth x hx).mul (sliceOf hψ.pth x hx)).add
      ((sliceOf hψ x hx).mul (sliceOf ((hψ.pth).pth) x hx)))
  -- uniform bound for `F'` on the compact set `[t₁,t₂] × [a,b]`
  have hmemQ : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Set.uIcc a b,
      (p.2, p.1) ∈ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have h2 : p.2 ∈ Set.Icc a b := by rw [Set.uIcc_of_le hab] at hp2; exact hp2
    show (p.2, p.1) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)
    exact ⟨lt_of_lt_of_le ha h2.1, lt_of_lt_of_le ht₁0 hp1.1, lt_of_le_of_lt hp1.2 ht₂π⟩
  have hbig : ContinuousOn (fun p : ℝ × ℝ =>
      c p.2 * (Work.Spaces.pth ψ p.2 p.1 * Work.Spaces.pth ψ p.2 p.1
        + ψ p.2 p.1 * Work.Spaces.pthIter 2 ψ p.2 p.1))
      (Set.Icc t₁ t₂ ×ˢ Set.uIcc a b) := by
    have hct : ContinuousOn (fun p : ℝ × ℝ => c p.2)
        (Set.Icc t₁ t₂ ×ˢ Set.uIcc a b) :=
      hc.comp continuous_snd.continuousOn (fun p hp => hp.2)
    have hψ0 : ContinuousOn (fun p : ℝ × ℝ => ψ p.2 p.1)
        (Set.Icc t₁ t₂ ×ˢ Set.uIcc a b) :=
      hψ.continuousOn.comp continuous_swap.continuousOn hmemQ
    have hψ1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth ψ p.2 p.1)
        (Set.Icc t₁ t₂ ×ˢ Set.uIcc a b) :=
      hψ.pth.continuousOn.comp continuous_swap.continuousOn hmemQ
    have hψ2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 ψ p.2 p.1)
        (Set.Icc t₁ t₂ ×ˢ Set.uIcc a b) :=
      ((hψ.pth).pth).continuousOn.comp continuous_swap.continuousOn hmemQ
    exact hct.mul ((hψ1.mul hψ1).add (hψ0.mul hψ2))
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn hbig
  -- the seven hypotheses of the dominated-convergence differentiation lemma
  have hmeas : ∀ᶠ x in 𝓝 θ₀,
      AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc a b)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ₀mem] with x hx
    exact (hFcont x hx).aestronglyMeasurable_of_subset_isCompact isCompact_uIcc
      measurableSet_uIoc Set.uIoc_subset_uIcc
  have hint : IntervalIntegrable (F θ₀) volume a b :=
    (hFcont θ₀ hθ₀mem).intervalIntegrable
  have hmeas' : AEStronglyMeasurable (F' θ₀) (volume.restrict (Set.uIoc a b)) :=
    (hF'cont θ₀ hθ₀mem).aestronglyMeasurable_of_subset_isCompact isCompact_uIcc
      measurableSet_uIoc Set.uIoc_subset_uIcc
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → ∀ x ∈ Set.Ioo t₁ t₂,
      ‖F' x t‖ ≤ (fun _ : ℝ => max C 0) t := by
    refine Eventually.of_forall fun t ht x hx => ?_
    have htu : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
    have hmem : (x, t) ∈ Set.Icc t₁ t₂ ×ˢ Set.uIcc a b :=
      ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, htu⟩
    exact le_trans (hC (x, t) hmem) (le_max_left C 0)
  have hintb : IntervalIntegrable (fun _ : ℝ => max C 0) volume a b := intervalIntegrable_const
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → ∀ x ∈ Set.Ioo t₁ t₂,
      HasDerivAt (fun x => F x t) (F' x t) x := by
    refine Eventually.of_forall fun t ht x hx => ?_
    have ht0 : 0 < t := by
      have h1 : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
      rw [Set.uIcc_of_le hab] at h1
      exact lt_of_lt_of_le ha h1.1
    have hxmem : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_of_lt_of_le ht₁0 (le_of_lt hx.1), lt_trans hx.2 ht₂π⟩
    have hd1 : HasDerivAt (fun y : ℝ => ψ t y) (Work.Spaces.pth ψ t x) x :=
      (((hψ.curry_θ ht0).contDiffAt (isOpen_Ioo.mem_nhds hxmem)).differentiableAt
        (by simp [Work.Stability.smoothOrder])).hasDerivAt
    have hd2 : HasDerivAt (fun y : ℝ => Work.Spaces.pth ψ t y)
        (Work.Spaces.pthIter 2 ψ t x) x :=
      (((hψ.pth.curry_θ ht0).contDiffAt (isOpen_Ioo.mem_nhds hxmem)).differentiableAt
        (by simp [Work.Stability.smoothOrder])).hasDerivAt
    have hgoal : HasDerivAt (fun y : ℝ => c t * ψ t y * Work.Spaces.pth ψ t y)
        (c t * (Work.Spaces.pth ψ t x * Work.Spaces.pth ψ t x
          + ψ t x * Work.Spaces.pthIter 2 ψ t x)) x := by
      have hcmul := (hd1.mul hd2).const_mul (c t)
      refine hcmul.congr_of_eventuallyEq ?_
      filter_upwards with y
      show c t * ψ t y * Work.Spaces.pth ψ t y = c t * (ψ t y * Work.Spaces.pth ψ t y)
      ring
    exact hgoal
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b) (x₀ := θ₀) (s := Set.Ioo t₁ t₂)
    (bound := fun _ : ℝ => max C 0) (F := F) (F' := F')
    (isOpen_Ioo.mem_nhds hθ₀mem) hmeas hint hmeas' hbound hintb hdiff
  -- the derivative integral splits into the two stated pieces
  have hI1 : IntervalIntegrable (fun z : ℝ => c z * (Work.Spaces.pth ψ z θ₀) ^ 2)
      volume a b :=
    (hc.mul (sliceOf hψ.pth θ₀ hθ₀mem |>.pow 2)).intervalIntegrable
  have hI2 : IntervalIntegrable (fun z : ℝ => c z * ψ z θ₀ * Work.Spaces.pthIter 2 ψ z θ₀)
      volume a b :=
    ((hc.mul (sliceOf hψ θ₀ hθ₀mem)).mul (sliceOf ((hψ.pth).pth) θ₀ hθ₀mem)).intervalIntegrable
  have hsplit : (∫ t in a..b, F' θ₀ t)
      = (∫ z in a..b, c z * (Work.Spaces.pth ψ z θ₀) ^ 2)
        + (∫ z in a..b, c z * ψ z θ₀ * Work.Spaces.pthIter 2 ψ z θ₀) := by
    have hfun : (fun t : ℝ => F' θ₀ t)
        = fun t : ℝ => (fun z : ℝ => c z * (Work.Spaces.pth ψ z θ₀) ^ 2) t
            + (fun z : ℝ => c z * ψ z θ₀ * Work.Spaces.pthIter 2 ψ z θ₀) t := by
      funext t
      simp only [hF']
      ring
    rw [hfun, intervalIntegral.integral_add hI1 hI2]
  rw [← hsplit]
  exact key.2

theorem mK_hasDerivAt_two {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {ψ : ℝ → ℝ → ℝ}
    (hψ : Work.FTS.EllipticEst.SmoothOpen ψ)
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ => ∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
        χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ * Work.Spaces.pth ψ z θ)
      ((∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * (Work.Spaces.pth ψ z θ₀) ^ 2)
       + (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
          χ k z * (Work.Spaces.w z) ^ 2 * ψ z θ₀ * Work.Spaces.pthIter 2 ψ z θ₀)) θ₀ := by
  have hc : ContinuousOn (fun z : ℝ => χ k z * (Work.Spaces.w z) ^ 2)
      (Set.uIcc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k)) := by
    have hsub : Set.uIcc (Work.FTS.EllSol.PkgK5.cA k) (Work.FTS.EllSol.PkgK5.cB k)
        ⊆ Set.Ioi (0 : ℝ) := by
      intro z hz
      rw [Set.uIcc_of_le (Work.FTS.EllSol.PkgK5.cA_le_cB k)] at hz
      exact lt_of_lt_of_le (Work.FTS.EllSol.PkgK5.cA_pos k) hz.1
    exact ((hχ.sm k).continuousOn.mono hsub).mul (continuousOn_w_sq_Ioi.mono hsub)
  exact hasDerivAt_integral_mul_pth (Work.FTS.EllSol.PkgK5.cA_pos k)
    (Work.FTS.EllSol.PkgK5.cA_le_cB k) hc hψ hθ₀

end Work.FTS.EllSol.PkgK5.InterpTrace
