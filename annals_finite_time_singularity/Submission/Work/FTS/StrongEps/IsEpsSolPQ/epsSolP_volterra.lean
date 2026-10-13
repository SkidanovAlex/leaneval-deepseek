/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/IsEpsSolPQ/epsSolP_volterra.lean`

**The Volterra identity of the projected `ε`-scheme** (node D1 of the `IsEpsSolP_eq_of_epsClass`
chain).  Two `P₀`-solutions `g`, `g'` of the projected scheme

  `∂_τ g = P₀ J_ε [𝓛 + 𝓡] (P₀ J_ε g)`   (`StrongEps.IsEpsSolP`, `StrongEps.epsRHSP`)

with the same datum `g₀`, whose families are jointly `C¹` on the half-open strip
`(0,∞) × (0,π/2) × [0,T]`, satisfy

* the pointwise Volterra identity `g - g' = ∫₀^τ (Feps (slice g s) - Feps (slice g' s)) ds`
  on the open quadrant (`Feps` is the τ-free form of the scheme's right-hand side, by
  `EpsEngine.epsRHSP_eq_Feps_slice`), and
* the two weighted curves `s ↦ (…)*epsW α` are a.e. strongly measurable for
  `(volume↾uIoc 0 τ) ×ₚ DomM` — the measurability input of Cauchy–Schwarz
  (`EpsSq_intervalIntegral_le_sqrt`) in the uniqueness argument.

## The two analytic ingredients

* **The strip is `UniqueDiffOn`.**  `Dset T = Ioi 0 ×ˢ (Ioo 0 (π/2) ×ˢ Icc 0 T)` is a product of
  intervals, so `UniqueDiffOn ℝ (Dset T)` follows from
  `uniqueDiffOn_Ioi.prod (… .prod (uniqueDiffOn_Icc hT))`.  Hence
  `ContDiffOn.continuousOn_fderivWithin` makes `fderivWithin ℝ G (Dset T)` continuous on the
  *closed* strip — this is what controls the fake-time derivative uniformly up to `τ = T`, where
  `Ioc 0 τ` reaches the endpoint `T` (interval integrability, and the conullness of the strip
  `Sset T`).
* **The fake-time derivative is a `derivWithin`.**  `IsEpsSolP` gives, for every `s ∈ Icc 0 T`, a
  `HasDerivWithinAt` of `s' ↦ g z θ s'` on `Icc 0 T`; the same curve is the composition of
  `s' ↦ (z,(θ,s'))` with the joint family, so uniqueness of `derivWithin`
  (`uniqueDiffOn_Icc hT`) identifies the scheme's right-hand side with the third partial derivative
  of the joint family.  Consequently `s ↦ Feps α ρ ε Φs E (slice g s) z θ` is
  `ContinuousOn (Icc 0 T)`, which gives both the fundamental theorem of calculus and the
  measurability bookkeeping.

Everything in this module is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.EpsEngine.VolterraV4Main
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps.IsEpsSolPQ

set_option autoImplicit false

/-! ## The strip of the joint `C¹` hypothesis -/

/-- The half-open strip `(0,∞) × (0,π/2) × [0,T]` of the joint `C¹` clause of the scheme, displayed
in the associativity of `ℝ × (ℝ × ℝ)`, i.e. as the set of triples `(z, (θ, τ))`. -/
def Dset (T : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  Set.Ioi 0 ×ˢ (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 T)

theorem mem_Dset {T : ℝ} {p : ℝ × (ℝ × ℝ)} :
    p ∈ Dset T ↔ 0 < p.1 ∧ 0 < p.2.1 ∧ p.2.1 < Real.pi / 2 ∧ p.2.2 ∈ Set.Icc 0 T := by
  simp only [Dset, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
  tauto

/-- The set of parameter pairs `q = (s, (z, θ))` whose shuffled triple `(z, θ, s)` lies in the strip
`Dset T`. -/
def Sset (T : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {q | (q.2.1, (q.2.2, q.1)) ∈ Dset T}

theorem mem_Sset {T : ℝ} {q : ℝ × (ℝ × ℝ)} :
    q ∈ Sset T ↔ 0 < q.2.1 ∧ 0 < q.2.2 ∧ q.2.2 < Real.pi / 2 ∧ q.1 ∈ Set.Icc 0 T := by
  simp only [Sset, mem_Dset]
  exact ⟨fun h => h, fun h => h⟩

theorem measurableSet_Dset (T : ℝ) : MeasurableSet (Dset T) := by
  rw [Dset]
  exact (isOpen_Ioi.measurableSet).prod
    ((isOpen_Ioo.measurableSet).prod measurableSet_Icc)

theorem measurableSet_Sset (T : ℝ) : MeasurableSet (Sset T) :=
  (measurableSet_Dset T).preimage (by fun_prop)

theorem uniqueDiffOn_Dset {T : ℝ} (hT : 0 < T) : UniqueDiffOn ℝ (Dset T) := by
  rw [Dset]
  exact (uniqueDiffOn_Ioi 0).prod
    ((uniqueDiffOn_Ioo 0 (Real.pi / 2)).prod (uniqueDiffOn_Icc hT))

/-- The coordinate shuffle `q = (s,(z,θ)) ↦ (z,(θ,s))` maps `Sset T` into the strip `Dset T`. -/
theorem mapsTo_shuffle (T : ℝ) :
    Set.MapsTo (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1))) (Sset T) (Dset T) :=
  fun _ hq => hq

/-! ## The two analytic ingredients -/

/-- **The fake-time derivative of a solution, read as a within-derivative of the joint family.**
For `z > 0`, `θ ∈ (0,π/2)` and `s ∈ [0,T]`, the third partial derivative (within the strip) of the
jointly `C¹` family `(z,θ,s') ↦ g z θ s'` is the scheme's right-hand side at the slice `g s`. -/
theorem fderivWithin_eq_Feps {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (hT : 0 < T) (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hc1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (Dset T))
    {z θ s : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hs : s ∈ Set.Icc 0 T) :
    (fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (Dset T) (z, (θ, s))) (0, (0, 1))
      = Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g s) z θ := by
  have hmem : (z, (θ, s)) ∈ Dset T := by
    rw [mem_Dset]
    exact ⟨hz, hθ.1, hθ.2, hs⟩
  have hfd : HasFDerivWithinAt (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (Dset T) (z, (θ, s)))
      (Dset T) (z, (θ, s)) :=
    ((hc1.differentiableOn one_ne_zero) _ hmem).hasFDerivWithinAt
  have hcurve : HasDerivWithinAt (fun s' : ℝ => (z, (θ, s'))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))
      (Set.Icc 0 T) s := by
    have h := (hasDerivWithinAt_const s (Set.Icc 0 T) z).prodMk
      ((hasDerivWithinAt_const s (Set.Icc 0 T) θ).prodMk (hasDerivWithinAt_id s (Set.Icc 0 T)))
    simpa using h
  have hmap : Set.MapsTo (fun s' : ℝ => (z, (θ, s'))) (Set.Icc 0 T) (Dset T) := by
    intro s' hs'
    rw [mem_Dset]
    exact ⟨hz, hθ.1, hθ.2, hs'⟩
  have hcomp := hfd.comp_hasDerivWithinAt s hcurve hmap
  have hUD : UniqueDiffWithinAt ℝ (Set.Icc 0 T) s :=
    (uniqueDiffOn_Icc hT).uniqueDiffWithinAt hs
  have h1 := hcomp.derivWithin hUD
  have hder := hsol.2 z θ s hz hθ hs
  rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E] at hder
  have h2 := hder.derivWithin hUD
  rw [← h1, ← h2]
  rfl

/-- **The fake-time derivative is continuous in the fake time**, on all of `[0,T]` (the endpoints
included), thanks to `fderivWithin` on the closed strip. -/
theorem continuousOn_derivWithin_curve {f : ℝ × (ℝ × ℝ) → ℝ} {T z θ : ℝ} {v : ℝ → ℝ}
    (hT : 0 < T) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hc1 : ContDiffOn ℝ 1 f (Dset T))
    (hder : ∀ s ∈ Set.Icc 0 T, HasDerivWithinAt (fun s' : ℝ => f (z, (θ, s'))) (v s)
      (Set.Icc 0 T) s) :
    ContinuousOn v (Set.Icc 0 T) := by
  have hfd : ContinuousOn (fderivWithin ℝ f (Dset T)) (Dset T) :=
    hc1.continuousOn_fderivWithin (uniqueDiffOn_Dset hT) (by norm_num)
  have hφcont : ContinuousOn (fun s : ℝ => (z, (θ, s))) (Set.Icc 0 T) := by fun_prop
  have hmap : Set.MapsTo (fun s : ℝ => (z, (θ, s))) (Set.Icc 0 T) (Dset T) := by
    intro s' hs'
    rw [mem_Dset]
    exact ⟨hz, hθ.1, hθ.2, hs'⟩
  have hcont : ContinuousOn
      (fun s : ℝ => (fderivWithin ℝ f (Dset T) (z, (θ, s))) (0, (0, 1))) (Set.Icc 0 T) :=
    (hfd.comp hφcont hmap).clm_apply continuousOn_const
  refine hcont.congr (fun s hs => ?_)
  have hmem : (z, (θ, s)) ∈ Dset T := by
    rw [mem_Dset]
    exact ⟨hz, hθ.1, hθ.2, hs⟩
  have hfd' : HasFDerivWithinAt f (fderivWithin ℝ f (Dset T) (z, (θ, s))) (Dset T)
      (z, (θ, s)) :=
    ((hc1.differentiableOn one_ne_zero) _ hmem).hasFDerivWithinAt
  have hcurve : HasDerivWithinAt (fun s' : ℝ => (z, (θ, s'))) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))
      (Set.Icc 0 T) s := by
    have h := (hasDerivWithinAt_const s (Set.Icc 0 T) z).prodMk
      ((hasDerivWithinAt_const s (Set.Icc 0 T) θ).prodMk (hasDerivWithinAt_id s (Set.Icc 0 T)))
    simpa using h
  have hmap' : Set.MapsTo (fun s' : ℝ => (z, (θ, s'))) (Set.Icc 0 T) (Dset T) := by
    intro s' hs'
    rw [mem_Dset]
    exact ⟨hz, hθ.1, hθ.2, hs'⟩
  have hcomp := hfd'.comp_hasDerivWithinAt s hcurve hmap'
  have hUD : UniqueDiffWithinAt ℝ (Set.Icc 0 T) s :=
    (uniqueDiffOn_Icc hT).uniqueDiffWithinAt hs
  have h1 := hcomp.derivWithin hUD
  have h2 := (hder s hs).derivWithin hUD
  have hgoal : (fderivWithin ℝ f (Dset T) (z, (θ, s))) (0, (0, 1)) = v s := by
    rw [← h1, ← h2]
    rfl
  exact hgoal.symm

/-! ## The Volterra identity and the two measurability clauses -/

theorem epsSolP_volterra {α C₁ Ce Cs B T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g g' : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hT : 0 < T)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E) (hB : 0 ≤ B)
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hsol' : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g')
    (hc1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.prod (Set.Ioi 0) (Set.prod (Set.Ioo 0 (Real.pi / 2)) (Set.Icc 0 T))))
    (hc1' : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g' p.1 p.2.1 p.2.2)
      (Set.prod (Set.Ioi 0) (Set.prod (Set.Ioo 0 (Real.pi / 2)) (Set.Icc 0 T)))) :
    (∀ z θ τ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → τ ∈ Set.Icc 0 T →
      g z θ τ - g' z θ τ
        = ∫ s in (0 : ℝ)..τ,
            (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g s) z θ
              - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g' s) z θ))
    ∧ (∀ τ ∈ Set.Icc 0 T, MeasureTheory.AEStronglyMeasurable
        (fun q : ℝ × (ℝ × ℝ) =>
          (Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g q.1) q.2.1 q.2.2
            - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice g' q.1) q.2.1 q.2.2)
          * Work.FTS.StrongEps.epsW α q.2.1 q.2.2)
        ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod
          Work.FTS.StrongEps.EpsLocalPStar.DomM))
    ∧ (∀ τ ∈ Set.Icc 0 T, MeasureTheory.AEStronglyMeasurable
        (fun q : ℝ × (ℝ × ℝ) =>
          (g q.2.1 q.2.2 q.1 - g' q.2.1 q.2.2 q.1) * Work.FTS.StrongEps.epsW α q.2.1 q.2.2)
        ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod
          Work.FTS.StrongEps.EpsLocalPStar.DomM)) := by
  classical
  have hc1D : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (Dset T) := hc1
  have hc1D' : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g' p.1 p.2.1 p.2.2) (Dset T) := hc1'
  refine ⟨?_, ?_, ?_⟩
  · -- ## 1. the pointwise Volterra identity
    intro z θ τ hz hθ hτ
    have hτ0 : 0 ≤ τ := hτ.1
    have hcontg : ContinuousOn
        (fun s : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g s) z θ) (Set.Icc 0 T) :=
      continuousOn_derivWithin_curve (f := fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
        (v := fun s : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g s) z θ)
        hT hz hθ hc1D fun s hs => by
          have h := hsol.2 z θ s hz hθ hs
          rwa [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E] at h
    have hcontg' : ContinuousOn
        (fun s : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g' s) z θ) (Set.Icc 0 T) :=
      continuousOn_derivWithin_curve (f := fun p : ℝ × ℝ × ℝ => g' p.1 p.2.1 p.2.2)
        (v := fun s : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g' s) z θ)
        hT hz hθ hc1D' fun s hs => by
          have h := hsol'.2 z θ s hz hθ hs
          rwa [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E] at h
    have hintg : IntervalIntegrable
        (fun s : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g s) z θ) volume 0 τ :=
      ContinuousOn.intervalIntegrable_of_Icc hτ0 (hcontg.mono (Set.Icc_subset_Icc_right hτ.2))
    have hintg' : IntervalIntegrable
        (fun s : ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g' s) z θ) volume 0 τ :=
      ContinuousOn.intervalIntegrable_of_Icc hτ0 (hcontg'.mono (Set.Icc_subset_Icc_right hτ.2))
    have hmemI : Set.MapsTo (fun s : ℝ => (z, (θ, s))) (Set.Icc 0 τ) (Dset T) := by
      intro s hs
      rw [mem_Dset]
      exact ⟨hz, hθ.1, hθ.2, hs.1, le_trans hs.2 hτ.2⟩
    have hFTCg : (∫ s in (0 : ℝ)..τ,
          Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g s) z θ) = g z θ τ - g z θ 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ0
        (hc1.continuousOn.comp (by fun_prop) hmemI) ?_ hintg
      intro x hx
      have hxT : x < T := lt_of_lt_of_le hx.2 hτ.2
      have h := hsol.2 z θ x hz hθ ⟨hx.1.le, le_trans hx.2.le hτ.2⟩
      rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E] at h
      exact h.hasDerivAt (Icc_mem_nhds hx.1 hxT)
    have hFTCg' : (∫ s in (0 : ℝ)..τ,
          Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g' s) z θ) = g' z θ τ - g' z θ 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ0
        (hc1'.continuousOn.comp (by fun_prop) hmemI) ?_ hintg'
      intro x hx
      have hxT : x < T := lt_of_lt_of_le hx.2 hτ.2
      have h := hsol'.2 z θ x hz hθ ⟨hx.1.le, le_trans hx.2.le hτ.2⟩
      rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice α ρ ε Φs E] at h
      exact h.hasDerivAt (Icc_mem_nhds hx.1 hxT)
    rw [intervalIntegral.integral_sub hintg hintg', hFTCg, hFTCg', hsol.1 z θ, hsol'.1 z θ]
    ring
  · -- ## 2. measurability of the right-hand-side curve
    intro τ hτ
    set μ : MeasureTheory.Measure (ℝ × (ℝ × ℝ)) :=
      (MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM with hμdef
    have hSmeas : MeasurableSet (Sset T) := measurableSet_Sset T
    have haeS : ∀ᵐ q ∂μ, q ∈ Sset T := by
      have hae1 : ∀ᵐ q ∂μ, q.1 ∈ Set.uIoc 0 τ := by
        rw [hμdef]
        refine (Measure.ae_prod_iff_ae_ae
          (measurableSet_uIoc.preimage measurable_fst)).mpr ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
        exact Eventually.of_forall fun _ => hx
      have hae2 : ∀ᵐ q ∂μ, 0 < q.2.1 ∧ 0 < q.2.2 ∧ q.2.2 < Real.pi / 2 := by
        rw [hμdef]
        refine (Measure.ae_prod_iff_ae_ae ?_).mpr
          (Eventually.of_forall fun _ =>
            Work.FTS.StrongEps.EpsLocalPStar.ae_open_DomM)
        exact (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
          ((measurableSet_lt measurable_const (measurable_snd.comp measurable_snd)).inter
            (measurableSet_lt (measurable_snd.comp measurable_snd) measurable_const))
      filter_upwards [hae1, hae2] with q h1 h2
      rw [Set.uIoc_of_le hτ.1] at h1
      rw [mem_Sset]
      exact ⟨h2.1, h2.2.1, h2.2.2, h1.1.le, le_trans h1.2 hτ.2⟩
    have hμS : μ.restrict (Sset T) = μ := Measure.restrict_eq_self_of_ae_mem haeS
    have hφcont : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1))) (Sset T) := by
      fun_prop
    -- the "shadow": the continuous within-derivative on the strip, read in the `(s,(z,θ))` order
    have hshadow : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
        (fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (Dset T)
          (q.2.1, (q.2.2, q.1))) (0, (0, 1))) (Sset T) :=
      ((hc1D.continuousOn_fderivWithin (uniqueDiffOn_Dset hT) (by norm_num)).comp hφcont
        (mapsTo_shuffle T)).clm_apply continuousOn_const
    have haesmShadow : MeasureTheory.AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) =>
        (fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (Dset T)
          (q.2.1, (q.2.2, q.1))) (0, (0, 1))) μ := by
      rw [← hμS]
      exact hshadow.aestronglyMeasurable hSmeas
    have haeeq : (fun q : ℝ × (ℝ × ℝ) =>
          (fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (Dset T)
            (q.2.1, (q.2.2, q.1))) (0, (0, 1)))
        =ᵐ[μ] (fun q : ℝ × (ℝ × ℝ) =>
          Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g q.1) q.2.1 q.2.2) := by
      filter_upwards [haeS] with q hq
      rw [mem_Sset] at hq
      exact fderivWithin_eq_Feps hT hsol hc1D hq.1 ⟨hq.2.1, hq.2.2.1⟩ hq.2.2.2
    have haesmg : MeasureTheory.AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) =>
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g q.1) q.2.1 q.2.2) μ :=
      haesmShadow.congr haeeq
    have haesmg' : MeasureTheory.AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) =>
        Work.FTS.EpsEngine.Feps α ρ ε Φs E (slice g' q.1) q.2.1 q.2.2) μ := by
      have hshadow' : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
          (fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => g' p.1 p.2.1 p.2.2) (Dset T)
            (q.2.1, (q.2.2, q.1))) (0, (0, 1))) (Sset T) :=
        ((hc1D'.continuousOn_fderivWithin (uniqueDiffOn_Dset hT) (by norm_num)).comp hφcont
          (mapsTo_shuffle T)).clm_apply continuousOn_const
      have haesmShadow' : MeasureTheory.AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) =>
          (fderivWithin ℝ (fun p : ℝ × ℝ × ℝ => g' p.1 p.2.1 p.2.2) (Dset T)
            (q.2.1, (q.2.2, q.1))) (0, (0, 1))) μ := by
        rw [← hμS]
        exact hshadow'.aestronglyMeasurable hSmeas
      refine haesmShadow'.congr ?_
      filter_upwards [haeS] with q hq
      rw [mem_Sset] at hq
      exact fderivWithin_eq_Feps hT hsol' hc1D' hq.1 ⟨hq.2.1, hq.2.2.1⟩ hq.2.2.2
    have hEpsW : MeasureTheory.AEStronglyMeasurable
        (fun q : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.epsW α q.2.1 q.2.2) μ :=
      ((Work.FTS.StrongEps.EpsLocalPStar.measurable_epsW α).comp
        (by fun_prop : Measurable (fun q : ℝ × (ℝ × ℝ) => (q.2.1, q.2.2)))).aestronglyMeasurable
    exact (haesmg.sub haesmg').mul hEpsW
  · -- ## 3. measurability of the slice-difference curve
    intro τ hτ
    set μ : MeasureTheory.Measure (ℝ × (ℝ × ℝ)) :=
      (MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod
        Work.FTS.StrongEps.EpsLocalPStar.DomM with hμdef
    have hSmeas : MeasurableSet (Sset T) := measurableSet_Sset T
    have haeS : ∀ᵐ q ∂μ, q ∈ Sset T := by
      have hae1 : ∀ᵐ q ∂μ, q.1 ∈ Set.uIoc 0 τ := by
        rw [hμdef]
        refine (Measure.ae_prod_iff_ae_ae
          (measurableSet_uIoc.preimage measurable_fst)).mpr ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
        exact Eventually.of_forall fun _ => hx
      have hae2 : ∀ᵐ q ∂μ, 0 < q.2.1 ∧ 0 < q.2.2 ∧ q.2.2 < Real.pi / 2 := by
        rw [hμdef]
        refine (Measure.ae_prod_iff_ae_ae ?_).mpr
          (Eventually.of_forall fun _ =>
            Work.FTS.StrongEps.EpsLocalPStar.ae_open_DomM)
        exact (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
          ((measurableSet_lt measurable_const (measurable_snd.comp measurable_snd)).inter
            (measurableSet_lt (measurable_snd.comp measurable_snd) measurable_const))
      filter_upwards [hae1, hae2] with q h1 h2
      rw [Set.uIoc_of_le hτ.1] at h1
      rw [mem_Sset]
      exact ⟨h2.1, h2.2.1, h2.2.2, h1.1.le, le_trans h1.2 hτ.2⟩
    have hμS : μ.restrict (Sset T) = μ := Measure.restrict_eq_self_of_ae_mem haeS
    have hφcont : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1))) (Sset T) := by
      fun_prop
    have hφQ0 : Set.MapsTo (fun q : ℝ × (ℝ × ℝ) => (q.2.1, q.2.2)) (Sset T)
        Work.FTS.EllipticEst.Q0 := by
      intro q hq
      rw [mem_Sset] at hq
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨hq.1, hq.2.1, hq.2.2.1⟩
    have hcontW : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
        (g q.2.1 q.2.2 q.1 - g' q.2.1 q.2.2 q.1) * Work.FTS.StrongEps.epsW α q.2.1 q.2.2)
        (Sset T) := by
      have h1 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1) (Sset T) :=
        hc1D.continuousOn.comp hφcont (mapsTo_shuffle T)
      have h2 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => g' q.2.1 q.2.2 q.1) (Sset T) :=
        hc1D'.continuousOn.comp hφcont (mapsTo_shuffle T)
      have h3 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Work.FTS.StrongEps.epsW α q.2.1 q.2.2)
          (Sset T) :=
        (Work.FTS.StrongEps.EpsSqTools.continuousOn_epsW α).comp
          (by fun_prop : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (q.2.1, q.2.2)) (Sset T)) hφQ0
      exact (h1.sub h2).mul h3
    rw [← hμS]
    exact hcontW.aestronglyMeasurable hSmeas

end Work.FTS.StrongEps.IsEpsSolPQ
