import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Iter
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.RXT0.SlabFlat
import Submission.Work.FTS.StrongEps.EpsE4Thr.RegSlab.continuousOn_intervalIntegral_slab_normed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsE4Thr/Leaves/regFromVolterra.lean` — the joint `C¹` of a Volterra curve

The Volterra curve `τ ↦ h₀ + ∫₀^τ A (w_σ) dσ` is jointly `C¹` in `(z, θ, τ)` on the slab
`(0,∞) × (0,π/2) × [0,δ]` provided only that

* the `τ`-slices `(z,θ) ↦ A (w_τ) (z,θ)` are `C¹` (hypothesis `hAy`, on the open quadrant, which
  is exactly where the `τ`-integral is taken),
* the integrand `(z,θ,τ) ↦ A (w_τ) (z,θ)` is continuous on the slab (hypothesis `hAc`), and
* the *spatial* derivative `(z,θ,τ) ↦ ∂_{(z,θ)} A (w_τ) (z,θ)` is continuous on the slab
  (hypothesis `hB`).

No `C¹`-regularity in the *fake time* `τ` is needed — this is the corrected (LEAF-D) form of the
interface item, cf. `EpsE4Thr/RegFromVolterraD.lean`.
-/

noncomputable section
open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## The key integral-differentiation lemma, with only the two-slice data -/

/-- **Differentiation under the `τ`-integral, from the slice data alone.**  This is the analogue of
`Work.FTS.StrongEps.EpsE4Thr.RegSlab.hasFDerivAt_intervalIntegral_slab` in which the hypothesis
`ContDiffOn ℝ 1 A (slab)` is replaced by the two weaker ones that the paper's setting actually
provides: joint *continuity* of `A` on the slab (`hAc`) and the `C¹`-regularity of each `τ`-slice
(`hslice`).  The uniform bound on the derivatives along the `(z,θ)`-direction comes from the
continuity of the derivative field (`hB`) on the compact `(z,θ) × [0,δ]` box. -/
theorem hasFDerivAt_intervalIntegral_slab_of_slice {Z Θ : Set ℝ} (hZ : IsOpen Z) (hΘ : IsOpen Θ)
    {δ : ℝ} {A : ℝ × ℝ × ℝ → ℝ}
    (hAc : ContinuousOn (fun p : ℝ × ℝ × ℝ => A (p.1, p.2.1, p.2.2))
      (Z ×ˢ (Θ ×ˢ Set.Icc (0 : ℝ) δ)))
    (hslice : ∀ σ ∈ Set.Icc (0 : ℝ) δ, ∀ z ∈ Z, ∀ θ ∈ Θ,
      HasFDerivAt (fun q : ℝ × ℝ => A (q.1, q.2, σ))
        (fderiv ℝ (fun q : ℝ × ℝ => A (q.1, q.2, σ)) (z, θ)) (z, θ))
    (hB : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (fun q : ℝ × ℝ => A (q.1, q.2, p.2.2)) (p.1, p.2.1))
      (Z ×ˢ (Θ ×ˢ Set.Icc (0 : ℝ) δ)))
    {z θ τ : ℝ} (hz : z ∈ Z) (hθ : θ ∈ Θ) (hτ : τ ∈ Set.Icc (0 : ℝ) δ) :
    HasFDerivAt (fun q : ℝ × ℝ => ∫ σ in (0 : ℝ)..τ, A (q.1, q.2, σ))
      (∫ σ in (0 : ℝ)..τ, fderiv ℝ (fun q : ℝ × ℝ => A (q.1, q.2, σ)) (z, θ)) (z, θ) := by
  have h0τ : (0 : ℝ) ≤ τ := hτ.1
  have hτδ : τ ≤ δ := hτ.2
  -- the `σ`-slice derivative as a function of the point
  let B : ℝ × ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) :=
    fun p => fderiv ℝ (fun q : ℝ × ℝ => A (q.1, q.2, p.2.2)) (p.1, p.2.1)
  let F' : ℝ × ℝ → ℝ → (ℝ × ℝ →L[ℝ] ℝ) :=
    fun x t => fderiv ℝ (fun q : ℝ × ℝ => A (q.1, q.2, t)) x
  have hBc : ContinuousOn B (Z ×ˢ (Θ ×ˢ Set.Icc (0 : ℝ) δ)) := hB
  -- openness: a neighbourhood `s` of `(z, θ)` inside `Z ×ˢ Θ`
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.isOpen_iff.mp hZ z hz
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.isOpen_iff.mp hΘ θ hθ
  let s : Set (ℝ × ℝ) := Metric.closedBall z (ε₁ / 2) ×ˢ Metric.closedBall θ (ε₂ / 2)
  have hs : s ⊆ Z ×ˢ Θ := by
    intro x hx
    exact ⟨hε₁ (Metric.closedBall_subset_ball (by linarith) hx.1),
      hε₂ (Metric.closedBall_subset_ball (by linarith) hx.2)⟩
  have hs_nhds : ∀ᶠ x in 𝓝 (z, θ), x ∈ s := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (Metric.closedBall_mem_nhds z (by linarith))
      (Metric.closedBall_mem_nhds θ (by linarith))
  -- the compact set on which the derivative field is bounded
  have hKsub : Metric.closedBall z (ε₁ / 2) ×ˢ (Metric.closedBall θ (ε₂ / 2) ×ˢ Set.Icc (0 : ℝ) δ)
      ⊆ Z ×ˢ (Θ ×ˢ Set.Icc (0 : ℝ) δ) := by
    intro p hp
    exact ⟨hε₁ (Metric.closedBall_subset_ball (by linarith) hp.1),
      hε₂ (Metric.closedBall_subset_ball (by linarith) hp.2.1), hp.2.2⟩
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z (ε₁ / 2)).prod
      ((isCompact_closedBall θ (ε₂ / 2)).prod isCompact_Icc)).exists_bound_of_continuousOn
        (hBc.mono hKsub)
  -- the slices are continuous in the integration variable (joint continuity on the slab)
  have slice_cont : ∀ x ∈ s, ContinuousOn (fun t : ℝ => A (x.1, x.2, t)) (Set.Icc (0 : ℝ) δ) := by
    intro x hx
    have hxZ : x.1 ∈ Z := (hs hx).1
    have hxΘ : x.2 ∈ Θ := (hs hx).2
    have hinner : ContinuousOn (fun t : ℝ => (x.1, x.2, t)) (Set.Icc (0 : ℝ) δ) := by fun_prop
    exact hAc.comp hinner (fun t ht => ⟨hxZ, hxΘ, ht⟩)
  have huIoc_sub : Set.uIoc (0 : ℝ) τ ⊆ Set.Icc (0 : ℝ) δ := by
    intro t ht
    rw [Set.uIoc_of_le h0τ] at ht
    exact ⟨le_of_lt ht.1, ht.2.trans hτδ⟩
  have hzθ_mem_s : (z, θ) ∈ s :=
    ⟨Metric.mem_closedBall_self (by linarith), Metric.mem_closedBall_self (by linarith)⟩
  -- measurability hypotheses
  have hF_meas : ∀ᶠ x in 𝓝 (z, θ),
      AEStronglyMeasurable (fun t : ℝ => A (x.1, x.2, t))
        (volume.restrict (Set.uIoc (0 : ℝ) τ)) :=
    hs_nhds.mono fun x hx =>
      ((slice_cont x hx).mono huIoc_sub).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (fun t : ℝ => A (z, θ, t)) volume (0 : ℝ) τ :=
    ((slice_cont (z, θ) hzθ_mem_s).mono (Set.Icc_subset_Icc le_rfl hτδ)).intervalIntegrable_of_Icc
      h0τ
  have hBz : ContinuousOn (fun t : ℝ => B (z, θ, t)) (Set.Icc (0 : ℝ) δ) := by
    have hinner : ContinuousOn (fun t : ℝ => (z, θ, t)) (Set.Icc (0 : ℝ) δ) := by fun_prop
    exact hBc.comp hinner (fun t ht => ⟨hz, hθ, ht⟩)
  have hF'_meas : AEStronglyMeasurable (F' (z, θ)) (volume.restrict (Set.uIoc (0 : ℝ) τ)) :=
    (hBz.mono huIoc_sub).aestronglyMeasurable measurableSet_uIoc
  -- the uniform bound on the derivative
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) τ → ∀ x ∈ s, ‖F' x t‖ ≤ C := by
    refine Filter.Eventually.of_forall fun t ht x hx => ?_
    have htIcc : t ∈ Set.Icc (0 : ℝ) δ := huIoc_sub ht
    have hmemK : (x.1, x.2, t) ∈ Metric.closedBall z (ε₁ / 2) ×ˢ
        (Metric.closedBall θ (ε₂ / 2) ×ˢ Set.Icc (0 : ℝ) δ) := ⟨hx.1, hx.2, htIcc⟩
    have h := hC (x.1, x.2, t) hmemK
    simpa [F'] using h
  -- the pointwise slice differentiability (from the slice hypothesis, `hAy`)
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) τ →
      ∀ x ∈ s, HasFDerivAt (fun x : ℝ × ℝ => A (x.1, x.2, t)) (F' x t) x := by
    refine Filter.Eventually.of_forall fun t ht x hx => ?_
    exact hslice t (huIoc_sub ht) x.1 (hs hx).1 x.2 (hs hx).2
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C) volume (0 : ℝ) τ := intervalIntegrable_const
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := volume) (s := s) (a := (0 : ℝ)) (b := τ) (bound := fun _ : ℝ => C)
    (F := fun (x : ℝ × ℝ) (t : ℝ) => A (x.1, x.2, t)) (F' := F') (x₀ := (z, θ))
    hs_nhds hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa [F'] using key

/-! ## The slab data -/

/-- The right-hand side of the Volterra equation, as a function on the slab. -/
private def slabA (F : Fn → Fn) (h₀ : Fn) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ σ => F (slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) σ) z θ

/-- The Volterra curve, as a function on the slab. -/
private def slabF (F : Fn → Fn) (h₀ : Fn) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => h₀ z θ + ∫ σ in (0 : ℝ)..τ, slabA F h₀ z θ σ

/-- The candidate `(z,θ)`-derivative of the `τ`-slice, as a function on the slab. -/
private def slabL (F : Fn → Fn) (h₀ : Fn) : ℝ × ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ :=
  fun p => fderiv ℝ (Function.uncurry h₀) (p.1, p.2.1)
    + ∫ σ in (0 : ℝ)..p.2.2, fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (p.1, p.2.1)

/-! ## The target -/

theorem regFromVolterra {F : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {h₀ : Work.FTS.Galerkin.Fn} {δ : ℝ} (hδ : 0 < δ)
    (hsm0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hvol : ∀ z θ τ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ,
            F (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) s) z θ)
    (hAc : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        F (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) p.2.2) p.1 p.2.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ))
    (hAy : ∀ σ ∈ Set.Icc 0 δ, ContDiffOn ℝ 1 (Function.uncurry
        (F (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) σ))) Work.FTS.EllipticEst.Q0)
    (hB : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (Function.uncurry
          (F (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) p.2.2))) (p.1, p.2.1))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ =>
        Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ) := by
  set U : Set (ℝ × ℝ × ℝ) :=
    Set.Ioi 0 ×ˢ (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc (0 : ℝ) δ) with hUdef
  have hmemU : ∀ p : ℝ × ℝ × ℝ, p ∈ U ↔ 0 < p.1 ∧ 0 < p.2.1 ∧ p.2.1 < Real.pi / 2 ∧
      0 ≤ p.2.2 ∧ p.2.2 ≤ δ := by
    intro p
    simp only [hUdef, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
    tauto
  -- the integrand is continuous on the slab
  have hAcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => slabA F h₀ p.1 p.2.1 p.2.2) U := hAc
  -- the `(z,θ)`-derivative of the `τ`-slice is continuous on the slab
  have hBcont : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 p.2.2) (p.1, p.2.1)) U := hB
  -- each `τ`-slice is `C¹` on the open quadrant
  have hslice : ∀ σ ∈ Set.Icc (0 : ℝ) δ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasFDerivAt (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ)
        (fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (z, θ)) (z, θ) := by
    intro σ hσ z hz θ hθ
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
    have hcd : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ)
        Work.FTS.EllipticEst.Q0 := hAy σ hσ
    have hca : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (z, θ) :=
      hcd.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
    exact (hca.differentiableAt (by norm_num)).hasFDerivAt
  -- the `τ`-slice is differentiable in `(z,θ)` with derivative `slabL`
  have hd : ∀ p ∈ U, HasFDerivAt (fun q : ℝ × ℝ => slabF F h₀ q.1 q.2 p.2.2)
      (slabL F h₀ p) (p.1, p.2.1) := by
    intro p hp
    obtain ⟨hz, hθ, hθ2, hτ0, hτδ⟩ := (hmemU p).mp hp
    -- the `h₀` part
    have hcont0 : ContDiffAt ℝ 1 (Function.uncurry h₀) (p.1, p.2.1) :=
      (((hsm0.forall 1).contDiffWithinAt (x := (p.1, p.2.1)) ⟨hz, hθ, hθ2⟩).contDiffAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, hθ, hθ2⟩))
    have h1 : HasFDerivAt (fun q : ℝ × ℝ => h₀ q.1 q.2)
        (fderiv ℝ (Function.uncurry h₀) (p.1, p.2.1)) (p.1, p.2.1) :=
      (hcont0.differentiableAt (by norm_num)).hasFDerivAt
    -- the integral part
    have h2 : HasFDerivAt (fun q : ℝ × ℝ => ∫ σ in (0 : ℝ)..p.2.2, slabA F h₀ q.1 q.2 σ)
        (∫ σ in (0 : ℝ)..p.2.2,
          fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (p.1, p.2.1)) (p.1, p.2.1) :=
      hasFDerivAt_intervalIntegral_slab_of_slice (Z := Set.Ioi (0 : ℝ))
        (Θ := Set.Ioo (0 : ℝ) (Real.pi / 2))
        (A := fun p : ℝ × ℝ × ℝ => slabA F h₀ p.1 p.2.1 p.2.2)
        isOpen_Ioi isOpen_Ioo hAcont hslice hBcont
        hz ⟨hθ, hθ2⟩ ⟨hτ0, hτδ⟩
    have hsum := h1.add h2
    refine HasFDerivAt.congr_of_eventuallyEq (f₁ := fun q : ℝ × ℝ => slabF F h₀ q.1 q.2 p.2.2)
      (f := (fun q : ℝ × ℝ => h₀ q.1 q.2) + fun q : ℝ × ℝ =>
        ∫ σ in (0 : ℝ)..p.2.2, slabA F h₀ q.1 q.2 σ)
      (f' := fderiv ℝ (Function.uncurry h₀) (p.1, p.2.1)
        + ∫ σ in (0 : ℝ)..p.2.2, fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (p.1, p.2.1))
      (x := (p.1, p.2.1)) hsum ?_
    filter_upwards with q
    simp only [slabF, slabA, Pi.add_apply]
  -- the derivative function is continuous on the slab
  have hL : ContinuousOn (slabL F h₀) U := by
    have hQ0 : ContDiffOn ℝ 1 (Function.uncurry h₀) Work.FTS.EllipticEst.Q0 := hsm0.forall 1
    have hc0 : ContinuousOn (fderiv ℝ (Function.uncurry h₀)) Work.FTS.EllipticEst.Q0 :=
      hQ0.continuousOn_fderiv_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 le_rfl
    have hproj : ContinuousOn (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) U :=
      ((continuous_fst.prodMk (continuous_fst.comp continuous_snd))).continuousOn
    have hmaps : MapsTo (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) U Work.FTS.EllipticEst.Q0 :=
      fun p hp => by
        obtain ⟨hz, hθ, hθ2, hτ0, hτδ⟩ := (hmemU p).mp hp
        exact ⟨hz, hθ, hθ2⟩
    have hL1 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (Function.uncurry h₀) (p.1, p.2.1)) U := hc0.comp hproj hmaps
    have hL2 : ContinuousOn (fun p : ℝ × ℝ × ℝ => ∫ σ in (0 : ℝ)..p.2.2,
        fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (p.1, p.2.1)) U :=
      RegSlab.continuousOn_intervalIntegral_slab_normed (B := fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 p.2.2) (p.1, p.2.1)) hBcont
    have heq : slabL F h₀ = (fun p : ℝ × ℝ × ℝ => fderiv ℝ (Function.uncurry h₀) (p.1, p.2.1))
        + fun p : ℝ × ℝ × ℝ => ∫ σ in (0 : ℝ)..p.2.2,
            fderiv ℝ (fun q : ℝ × ℝ => slabA F h₀ q.1 q.2 σ) (p.1, p.2.1) := by
      funext p
      simp only [slabL, Pi.add_apply]
    rw [heq]
    exact hL1.add hL2
  -- the identity of the Volterra representation
  have hId : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ δ →
      slabF F h₀ z θ τ = slabF F h₀ z θ 0 + ∫ σ in (0 : ℝ)..τ, slabA F h₀ z θ σ := by
    intro z θ τ hz hθ hθ2 hτ0 hτδ
    simp only [slabF]
    rw [intervalIntegral.integral_same, add_zero]
  -- the abstract slab `C¹`-lemma
  have hmain : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => slabF F h₀ p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc (0 : ℝ) δ)) :=
    (Work.FTS_RegExport.RXT0.slabC1Flat (S := δ) (A := slabA F h₀) (f := slabF F h₀)
      (L := slabL F h₀) hδ hAcont hId hd hL).1
  -- transfer to the Volterra curve
  have hUeq : U = Set.Ioi 0 ×ˢ (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc (0 : ℝ) δ) := rfl
  rw [hUeq]
  refine hmain.congr fun p hp => ?_
  obtain ⟨hz, hθ, hθ2, hτ0, hτδ⟩ := (hmemU p).mp (hUeq ▸ hp)
  simpa only [slabF, slabA] using hvol p.1 p.2.1 p.2.2 hz ⟨hθ, hθ2⟩ ⟨hτ0, hτδ⟩

end Work.FTS.StrongEps.EpsE4Thr.Leaves
