import Mathlib
import Submission.Work.SimplyConnected.ABS.ExtremalImports

/-!
# Elementary interface steps for the divisor (Weierstrass/Behnke–Stein) chapter

The target of this directory, `Work.Analysis.RiemannSurface.single_simple_zero_at`, asks for a
holomorphic function on a non-compact connected Riemann surface whose zero set is exactly one
prescribed point, the zero being simple.  Every classical route to it produces, not the function
itself, but one of the equivalent data; the conversion is pure chart bookkeeping and is done here:

* a holomorphic function on `X ∖ {x₀}`, nowhere zero there, with a *simple pole of residue one* at
  `x₀` (the Mittag–Leffler / additive Cousin formulation); its reciprocal, extended by `0` at `x₀`,
  is the required function — `singleSimpleZero_of_singleSimplePole` below.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.Analysis.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ### Chart bookkeeping for the reciprocal -/

/-- **Holomorphy of the reciprocal.**  A function holomorphic at `x` and non-zero there has a
holomorphic reciprocal at `x`.  (Not in `Submission/Holomorphic.lean`.) -/
theorem HolomorphicOnXAt.inv {f : X → ℂ} {x : X} (hf : Submission.HolomorphicOnXAt f x)
    (hx : f x ≠ 0) : Submission.HolomorphicOnXAt (fun z => (f z)⁻¹) x := by
  rw [Submission.HolomorphicOnXAt] at hf ⊢
  have hval : (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := by
    rw [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    exact hx
  exact (hf.inv hval).congr (by filter_upwards with w; rfl)

/-- **The "single simple pole of residue one" datum** at `x₀`: in the preferred chart at `x₀`, `h`
looks like `w ↦ (w - w₀)⁻¹ + H w` with `H` analytic at `w₀` and `H w₀ ≠ 0`.  This is the
principal-part datum of the Mittag–Leffler (additive Cousin) formulation of the divisor `-1·x₀`;
`h` is only required to be holomorphic off `x₀`, so the condition is purely local at `x₀`. -/
def HasSimplePoleAt (x₀ : X) (h : X → ℂ) : Prop :=
  ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧ H ((chartAt ℂ x₀) x₀) ≠ 0 ∧
    (h ∘ (chartAt ℂ x₀).symm) =ᶠ[𝓝 ((chartAt ℂ x₀) x₀)]
      (fun w : ℂ => (w - (chartAt ℂ x₀) x₀)⁻¹ + H w)

/-- **From a single simple pole to the single simple zero.**  If `h` is holomorphic and nowhere zero
off `x₀` and has a simple pole of residue one at `x₀` (`HasSimplePoleAt`), then its reciprocal,
extended by `0` at `x₀`, is holomorphic on `X`, has no zero other than `x₀`, and has a simple zero
there — exactly the conclusion of the target. -/
theorem singleSimpleZero_of_singleSimplePole {x₀ : X} {h : X → ℂ}
    (hhol : Submission.HolomorphicOnX h (univ \ {x₀}))
    (hne : ∀ z, z ≠ x₀ → h z ≠ 0)
    (hpole : HasSimplePoleAt x₀ h) :
    ∃ g : X → ℂ, Submission.HolomorphicOnX g univ ∧ (∀ z, z ≠ x₀ → g z ≠ 0) ∧
      Submission.HasLogPoleAt x₀ g := by
  obtain ⟨H, hHana, hHne, hev⟩ := hpole
  set c := chartAt ℂ x₀ with hc
  set a : ℂ := c x₀ with ha
  have hsrc : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hsymm_a : c.symm a = x₀ := c.left_inv hsrc
  set g : X → ℂ := fun z => if z = x₀ then 0 else (h z)⁻¹ with hg
  -- the analytic witness of the simple zero at `x₀`
  have hKana : AnalyticAt ℂ (fun w : ℂ => (1 + (w - a) * H w)⁻¹) a := by
    have h1 : AnalyticAt ℂ (fun w : ℂ => 1 + (w - a) * H w) a :=
      analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hHana)
    have h1a : (1 + (a - a) * H a) ≠ 0 := by simp
    exact h1.inv h1a
  have hKa : (fun w : ℂ => (1 + (w - a) * H w)⁻¹) a ≠ 0 := by simp
  -- `g` read in the chart at `x₀` is `w ↦ (w - a) * K w` on a neighbourhood of `a`
  have hmain : (g ∘ c.symm) =ᶠ[𝓝 a] (fun w : ℂ => (w - a) * (1 + (w - a) * H w)⁻¹) := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hsrc), hev] with w hw hh
    by_cases hcx : c.symm w = x₀
    · -- then `w = a`, and both sides vanish there
      have hwa : w = a := by
        calc w = c (c.symm w) := (c.right_inv hw).symm
          _ = c x₀ := by rw [hcx]
          _ = a := ha.symm
      subst hwa
      simp [hg, hcx]
    · -- otherwise `g` is the reciprocal of `h` at that point
      have hwa : w ≠ a := by
        intro hwa
        exact hcx (by rw [hwa]; exact hsymm_a)
      simp only [Function.comp_apply, hg, if_neg hcx]
      have hh' : h (c.symm w) = (w - a)⁻¹ + H w := hh
      rw [hh']
      have hfac : (w - a)⁻¹ + H w = (w - a)⁻¹ * (1 + (w - a) * H w) := by field_simp
      rw [hfac, mul_inv_rev, inv_inv, mul_comm]
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z _
    rw [Submission.HolomorphicOnXAt]
    by_cases hz : z = x₀
    · subst hz
      have hana : AnalyticAt ℂ (fun w : ℂ => (w - a) * (1 + (w - a) * H w)⁻¹) a :=
        (analyticAt_id.sub analyticAt_const).mul hKana
      exact hana.congr hmain.symm
    · -- away from `x₀`, `g` agrees with the reciprocal of `h`
      have hg_eq : g =ᶠ[𝓝 z] (fun y => (h y)⁻¹) := by
        filter_upwards [eventually_ne_nhds hz] with y hy
        simp only [hg, if_neg hy]
      have hcz : (chartAt ℂ z) z ∈ (chartAt ℂ z).target :=
        (chartAt ℂ z).map_source (mem_chart_source ℂ z)
      have hcont : Tendsto (chartAt ℂ z).symm (𝓝 ((chartAt ℂ z) z)) (𝓝 z) := by
        simpa only [(chartAt ℂ z).left_inv (mem_chart_source ℂ z)] using
          ((chartAt ℂ z).continuousAt_symm hcz).tendsto
      have hpull : (g ∘ (chartAt ℂ z).symm)
          =ᶠ[𝓝 ((chartAt ℂ z) z)] ((fun y => (h y)⁻¹) ∘ (chartAt ℂ z).symm) :=
        hcont.eventually hg_eq
      have hhana : AnalyticAt ℂ ((h ∘ (chartAt ℂ z).symm)⁻¹) ((chartAt ℂ z) z) := by
        have hhole : Submission.HolomorphicOnXAt h z := hhol z (by simp [hz])
        rw [Submission.HolomorphicOnXAt] at hhole
        refine hhole.inv ?_
        rw [Function.comp_apply, (chartAt ℂ z).left_inv (mem_chart_source ℂ z)]
        exact hne z hz
      refine hhana.congr ?_
      filter_upwards [hpull] with w hw
      simp only [Function.comp_apply, Pi.inv_apply]
      exact hw.symm
  · intro z hz
    simp only [hg, if_neg hz]
    exact inv_ne_zero (hne z hz)
  · exact ⟨fun w : ℂ => (1 + (w - a) * H w)⁻¹, hKana, hKa, hmain⟩

/-- **The Mittag--Leffler datum in the form in which the divisor chapter produces it.**  The
normalisation `H x₀ ≠ 0` of `HasSimplePoleAt` is *not* implied by "`h` has a simple pole of residue
one at `x₀`" (the residue of `h` at `x₀` is `1` regardless of the value `H x₀`), and the
construction along a Runge exhaustion produces the datum only in this weaker form.  The conclusion
is the same as that of `singleSimpleZero_of_singleSimplePole`, and the proof is that proof without
the unused hypothesis. -/
theorem singleSimpleZero_of_poleData {x₀ : X} {h : X → ℂ} {H : ℂ → ℂ}
    (hhol : Submission.HolomorphicOnX h (univ \ {x₀}))
    (hne : ∀ z, z ≠ x₀ → h z ≠ 0)
    (hHana : AnalyticAt ℂ H ((chartAt ℂ x₀) x₀))
    (hev : (h ∘ (chartAt ℂ x₀).symm) =ᶠ[𝓝 ((chartAt ℂ x₀) x₀)]
      (fun w : ℂ => (w - (chartAt ℂ x₀) x₀)⁻¹ + H w)) :
    ∃ g : X → ℂ, Submission.HolomorphicOnX g univ ∧ (∀ z, z ≠ x₀ → g z ≠ 0) ∧
      Submission.HasLogPoleAt x₀ g := by
  set c := chartAt ℂ x₀ with hc
  set a : ℂ := c x₀ with ha
  have hsrc : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hsymm_a : c.symm a = x₀ := c.left_inv hsrc
  set g : X → ℂ := fun z => if z = x₀ then 0 else (h z)⁻¹ with hg
  have hKana : AnalyticAt ℂ (fun w : ℂ => (1 + (w - a) * H w)⁻¹) a := by
    have h1 : AnalyticAt ℂ (fun w : ℂ => 1 + (w - a) * H w) a :=
      analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hHana)
    have h1a : (1 + (a - a) * H a) ≠ 0 := by simp
    exact h1.inv h1a
  have hKa : (fun w : ℂ => (1 + (w - a) * H w)⁻¹) a ≠ 0 := by simp
  have hmain : (g ∘ c.symm) =ᶠ[𝓝 a] (fun w : ℂ => (w - a) * (1 + (w - a) * H w)⁻¹) := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hsrc), hev] with w hw hh
    by_cases hcx : c.symm w = x₀
    · have hwa : w = a := by
        calc w = c (c.symm w) := (c.right_inv hw).symm
          _ = c x₀ := by rw [hcx]
          _ = a := ha.symm
      subst hwa
      simp [hg, hcx]
    · have hwa : w ≠ a := by
        intro hwa
        exact hcx (by rw [hwa]; exact hsymm_a)
      simp only [Function.comp_apply, hg, if_neg hcx]
      have hh' : h (c.symm w) = (w - a)⁻¹ + H w := hh
      rw [hh']
      have hfac : (w - a)⁻¹ + H w = (w - a)⁻¹ * (1 + (w - a) * H w) := by field_simp
      rw [hfac, mul_inv_rev, inv_inv, mul_comm]
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z _
    rw [Submission.HolomorphicOnXAt]
    by_cases hz : z = x₀
    · subst hz
      have hana : AnalyticAt ℂ (fun w : ℂ => (w - a) * (1 + (w - a) * H w)⁻¹) a :=
        (analyticAt_id.sub analyticAt_const).mul hKana
      exact hana.congr hmain.symm
    · have hg_eq : g =ᶠ[𝓝 z] (fun y => (h y)⁻¹) := by
        filter_upwards [eventually_ne_nhds hz] with y hy
        simp only [hg, if_neg hy]
      have hcz : (chartAt ℂ z) z ∈ (chartAt ℂ z).target :=
        (chartAt ℂ z).map_source (mem_chart_source ℂ z)
      have hcont : Tendsto (chartAt ℂ z).symm (𝓝 ((chartAt ℂ z) z)) (𝓝 z) := by
        simpa only [(chartAt ℂ z).left_inv (mem_chart_source ℂ z)] using
          ((chartAt ℂ z).continuousAt_symm hcz).tendsto
      have hpull : (g ∘ (chartAt ℂ z).symm)
          =ᶠ[𝓝 ((chartAt ℂ z) z)] ((fun y => (h y)⁻¹) ∘ (chartAt ℂ z).symm) :=
        hcont.eventually hg_eq
      have hhana : AnalyticAt ℂ ((h ∘ (chartAt ℂ z).symm)⁻¹) ((chartAt ℂ z) z) := by
        have hhole : Submission.HolomorphicOnXAt h z := hhol z (by simp [hz])
        rw [Submission.HolomorphicOnXAt] at hhole
        refine hhole.inv ?_
        rw [Function.comp_apply, (chartAt ℂ z).left_inv (mem_chart_source ℂ z)]
        exact hne z hz
      refine hhana.congr ?_
      filter_upwards [hpull] with w hw
      simp only [Function.comp_apply, Pi.inv_apply]
      exact hw.symm
  · intro z hz
    simp only [hg, if_neg hz]
    exact inv_ne_zero (hne z hz)
  · exact ⟨fun w : ℂ => (1 + (w - a) * H w)⁻¹, hKana, hKa, hmain⟩


/-- **Converse bookkeeping.**  A holomorphic function on `X` with zero set exactly `{x₀}`, the zero
being simple, produces the datum consumed by `singleSimpleZero_of_poleData` (after rescaling by the
value of the chart factor at `x₀`, which normalises the residue to one).  This completes the verified
equivalence of the two formulations of the divisor theorem.  The value of `h` at `x₀` is chosen so
that the eventual identity below also holds *at* the centre `a` of the chart. -/
theorem exists_poleData_of_singleSimpleZero {x₀ : X} {g : X → ℂ}
    (hhol : Submission.HolomorphicOnX g Set.univ) (hne : ∀ z : X, z ≠ x₀ → g z ≠ 0)
    (hsimple : Submission.HasLogPoleAt x₀ g) :
    ∃ (h : X → ℂ) (H : ℂ → ℂ), Submission.HolomorphicOnX h (Set.univ \ {x₀}) ∧
      (∀ z : X, z ≠ x₀ → h z ≠ 0) ∧ AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧
      (h ∘ (chartAt ℂ x₀).symm) =ᶠ[𝓝 ((chartAt ℂ x₀) x₀)]
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀)⁻¹ + H w) := by
  obtain ⟨G, hGana, hGne, hevG⟩ := hsimple
  set c := chartAt ℂ x₀ with hc
  set a : ℂ := c x₀ with ha
  have hsrc : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hsymm_a : c.symm a = x₀ := by rw [ha]; exact c.left_inv hsrc
  have hcx₀ : c x₀ = a := ha.symm
  -- Taylor expansion of `G` at `a`
  have hshift : AnalyticAt ℂ (fun v : ℂ => G (a + v)) 0 := by
    have hinner : AnalyticAt ℂ (fun v : ℂ => a + v) 0 := by
      have h1 := (analyticAt_const (𝕜 := ℂ) (v := a) (x := (0 : ℂ))).add
        (analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ)))
      exact h1.congr (by filter_upwards with v; rfl)
    have hz : AnalyticAt ℂ G ((fun v : ℂ => a + v) 0) := by simpa using hGana
    have h2 := hz.comp (f := fun v : ℂ => a + v) hinner
    exact h2.congr (by filter_upwards with v; rfl)
  obtain ⟨p, hp, hpeq⟩ := hshift.exists_eventuallyEq_sum_add_pow_mul 1
  have hGexp : (fun v : ℂ => G (a + v)) =ᶠ[𝓝 0] (fun v : ℂ => G a + v * p v) := by
    filter_upwards [hpeq] with v hv
    rw [hv]
    simp
  have htrans : (fun w : ℂ => G w) =ᶠ[𝓝 a] (fun w : ℂ => G a + (w - a) * p (w - a)) := by
    have htend : Tendsto (fun w : ℂ => w - a) (𝓝 a) (𝓝 0) := by
      have h1 : Tendsto (fun w : ℂ => w) (𝓝 a) (𝓝 a) := tendsto_id
      have h2 : Tendsto (fun _ : ℂ => a) (𝓝 a) (𝓝 a) := tendsto_const_nhds
      simpa using h1.sub h2
    filter_upwards [htend.eventually hGexp] with w hw
    simpa [show a + (w - a) = w from by ring] using hw
  -- the witness of the remaining analytic part
  have hHana : AnalyticAt ℂ (fun w => -(p (w - a)) / G w) a := by
    have hcomp : AnalyticAt ℂ (fun w : ℂ => p (w - a)) a := by
      have hinner : AnalyticAt ℂ (fun w : ℂ => w - a) a := by
        have h1 : AnalyticAt ℂ (fun w : ℂ => w) a := analyticAt_id
        have h2 : AnalyticAt ℂ (fun _ : ℂ => a) a := analyticAt_const
        have h3 := h1.sub h2
        exact h3.congr (by filter_upwards with w; rfl)
      have hz : AnalyticAt ℂ p ((fun w : ℂ => w - a) a) := by simpa using hp
      have h4 := hz.comp (f := fun w : ℂ => w - a) hinner
      exact h4.congr (by filter_upwards with w; rfl)
    exact hcomp.neg.div hGana hGne
  have hHa : (fun w : ℂ => -(p (w - a)) / G w) a = -(p 0) / G a := by simp
  refine ⟨fun z => if z = x₀ then (-(p 0)) / G a else G a * (g z)⁻¹,
    fun w => -(p (w - a)) / G w, ?_, ?_, hHana, ?_⟩
  · -- holomorphy of the reciprocal datum off `x₀`
    intro z hz
    have hz' : z ≠ x₀ := by simpa using hz
    rw [Submission.HolomorphicOnXAt]
    have hg' : AnalyticAt ℂ (g ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) :=
      hhol z (Set.mem_univ z)
    have hne' : (g ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) ≠ 0 := by
      simp only [Function.comp_apply, (chartAt ℂ z).left_inv (mem_chart_source ℂ z)]
      exact hne z hz'
    have h1 : AnalyticAt ℂ (((fun y : X => (g y)⁻¹)) ∘ (chartAt ℂ z).symm)
        ((chartAt ℂ z) z) := hg'.inv hne'
    have h2 := (analyticAt_const (𝕜 := ℂ) (v := G a) (x := ((chartAt ℂ z) z))).mul h1
    refine h2.congr ?_
    have hz_nhds : ∀ᶠ y in 𝓝 z, y ≠ x₀ := eventually_ne_nhds hz'
    have hcont : Tendsto (chartAt ℂ z).symm (𝓝 ((chartAt ℂ z) z)) (𝓝 z) := by
      simpa only [(chartAt ℂ z).left_inv (mem_chart_source ℂ z)] using
        ((chartAt ℂ z).continuousAt_symm ((chartAt ℂ z).map_source (mem_chart_source ℂ z))).tendsto
    filter_upwards [hcont.eventually hz_nhds] with w hw
    simp only [Function.comp_apply, if_neg hw]
    rfl
  · intro z hz
    have hz' : z ≠ x₀ := by simpa using hz
    simp only [if_neg hz']
    exact mul_ne_zero hGne (inv_ne_zero (hne z hz'))
  · -- the eventual identity, including at the centre
    have hGnear : ∀ᶠ w in 𝓝 a, G w ≠ 0 := hGana.continuousAt.eventually_ne hGne
    have htarget : ∀ᶠ w in 𝓝 a, w ∈ c.target :=
      c.open_target.mem_nhds (c.map_source hsrc)
    filter_upwards [hevG, htrans, hGnear, htarget] with w hw hwg hwne hwt
    have hgcd : g (c.symm w) = (w - a) * G w := hw
    have hGcd : G w = G a + (w - a) * p (w - a) := hwg
    by_cases hwa : w = a
    · -- the centre: both sides equal `-(p 0) / G a`
      subst hwa
      simp only [Function.comp_apply, hsymm_a]
      simp
    · -- off the centre: the algebraic identity
      have hsymmw : c.symm w ≠ x₀ := by
        intro hcontra
        have hat : a ∈ c.target := c.map_source hsrc
        have hcontra' : c.symm w = c.symm a := by rw [hcontra, hsymm_a]
        exact hwa (c.symm.injOn hwt hat hcontra')
      have hwa' : w - a ≠ 0 := sub_ne_zero.mpr hwa
      simp only [Function.comp_apply, if_neg hsymmw]
      rw [hGcd] at hwne
      rw [hgcd, hGcd]
      field_simp
      ring

end Work.Analysis.RiemannSurface
