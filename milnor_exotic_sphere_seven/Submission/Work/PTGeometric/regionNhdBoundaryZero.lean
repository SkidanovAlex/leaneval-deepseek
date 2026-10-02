import Mathlib
import Submission.Work.ThomBordism.Transversality.Preimage.BoundaryCoord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A neighbourhood of a boundary zero of a submersion on a manifold with boundary

`Work.PTGeometric.regionNhdBoundaryZero`: if `Φ : A → ℝ` is a `C^∞` function on a smooth manifold
with boundary which is a *submersion* (Mathlib's local-normal-form notion) at each of its zeros and
whose differential at each boundary zero is a *negative* multiple of the differential of a
boundary-defining chart coordinate, then `Φ ≤ 0` near every boundary zero.

The proof strategy:

* `normalFunctionalHalfSpace` (pure model space): the `0`-th coordinate functional of a map of the
  half-space that keeps the half-space and moves the hyperplane `{z 0 = 0}` onto itself has
  derivative a positive multiple of the `0`-th coordinate functional.
* `chartCoordMfderiv` (chart form of the same statement): for a chart `e` of the maximal atlas of
  `A` at a boundary point `x`, the derivative of `y ↦ (e y).1 0` at `x` is a positive multiple of
  `PiLp.proj 2 _ 0` (the `0`-th coordinate functional in the model).
* `eventuallyLeZeroOfHasDerivAt`: a function with `Ψ 0 = 0` and nonzero derivative `d` at `0` has,
  near `0`, the sign of `d * s`.
-/

set_option linter.style.haveILetI false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- **The normal functional of a half-space map at a boundary point.**

Let `χ` be (the germ near the boundary point `p`, `p 0 = 0`) of a map of the model half-space
`EuclideanHalfSpace n = {z | 0 ≤ z 0} ⊆ EuclideanSpace ℝ (Fin n)` which keeps the half-space
(`0 ≤ (χ z) 0` near `p`) and moves the hyperplane `{z 0 = 0}` exactly onto itself
(`(χ z) 0 = 0 ↔ z 0 = 0` near `p`), with surjective derivative `A` at `p`.  Then the `0`-th
coordinate functional of `χ` has derivative a *positive* multiple of the `0`-th coordinate
functional at `p`. -/
theorem normalFunctionalHalfSpace {n : ℕ} [NeZero n]
    {χ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {p : EuclideanSpace ℝ (Fin n)} (hp : p.ofLp 0 = 0)
    (hdiff : HasFDerivWithinAt χ A (range (𝓡∂ n)) p) (hsurj : Function.Surjective A)
    (hpos : ∀ᶠ z in 𝓝[range (𝓡∂ n)] p, 0 ≤ (χ z).ofLp 0)
    (hzero : ∀ᶠ z in 𝓝[range (𝓡∂ n)] p, ((χ z).ofLp 0 = 0 ↔ z.ofLp 0 = 0)) :
    ∃ c : ℝ, 0 < c ∧ fderivWithin ℝ (fun z => (χ z).ofLp 0) (range (𝓡∂ n)) p
      = c • PiLp.proj 2 (fun _ : Fin n => ℝ) 0 := by
  set L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n => ℝ) 0 with hL
  have hp0 : 0 ≤ p.ofLp 0 := le_of_eq hp.symm
  have hpmem : p ∈ range (𝓡∂ n) := by
    rw [range_modelWithCornersEuclideanHalfSpace]; exact hp0
  have hcoord : HasFDerivWithinAt (fun z => (χ z).ofLp 0) (L.comp A) (range (𝓡∂ n)) p := by
    have hg : HasFDerivWithinAt (fun z : EuclideanSpace ℝ (Fin n) => z.ofLp 0) L univ (χ p) :=
      ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin n => ℝ) (χ p) 0)).hasFDerivWithinAt
    exact hg.comp p hdiff (mapsTo_univ _ _)
  have hfderiv : fderivWithin ℝ (fun z => (χ z).ofLp 0) (range (𝓡∂ n)) p = L.comp A :=
    hcoord.fderivWithin ((𝓡∂ n).uniqueDiffOn.uniqueDiffWithinAt hpmem)
  have hpos' : ∀ᶠ z in 𝓝 p, z ∈ range (𝓡∂ n) → 0 ≤ (χ z).ofLp 0 :=
    eventually_nhdsWithin_iff.mp hpos
  have hzero' : ∀ᶠ z in 𝓝 p, z ∈ range (𝓡∂ n) → ((χ z).ofLp 0 = 0 ↔ z.ofLp 0 = 0) :=
    eventually_nhdsWithin_iff.mp hzero
  set e₀ : EuclideanSpace ℝ (Fin n) := PiLp.single 2 (0 : Fin n) (1 : ℝ) with he₀
  have he₀_0 : e₀.ofLp 0 = 1 := by simp [he₀]
  have hpχ : (χ p).ofLp 0 = 0 := ((hzero'.self_of_nhds) hpmem).mpr hp
  -- ## Step A: the derivative kills the hyperplane `{z 0 = 0}`
  have stepA : ∀ v : EuclideanSpace ℝ (Fin n), v.ofLp 0 = 0 → (A v).ofLp 0 = 0 := by
    intro v hv
    have hcurvecoord : ∀ t : ℝ, (p + t • v).ofLp 0 = 0 := by
      intro t; simp [PiLp.smul_apply, hp, hv]
    have hmemcurve : ∀ t : ℝ, p + t • v ∈ range (𝓡∂ n) := by
      intro t
      rw [range_modelWithCornersEuclideanHalfSpace]
      show (0:ℝ) ≤ (p + t • v).ofLp 0
      rw [hcurvecoord t]
    have hmemEv : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), p + t • v ∈ range (𝓡∂ n) :=
      Eventually.of_forall hmemcurve
    have hcurve : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • v) ((1 : ℝ) • v) (0 : ℝ) :=
        (hasDerivAt_id (0 : ℝ)).smul_const v
      have h2 : HasDerivAt (fun t : ℝ => p + t • v) ((1 : ℝ) • v) 0 := h1.const_add p
      simpa using h2
    have hcont : Tendsto (fun t : ℝ => p + t • v) (𝓝 (0:ℝ)) (𝓝 p) := by
      have h' := hcurve.continuousAt.tendsto
      rwa [show p + (0:ℝ) • v = p from by simp] at h'
    have hcoord' : HasFDerivWithinAt (fun z => (χ z).ofLp 0) (L.comp A) (range (𝓡∂ n))
        (p + (0:ℝ) • v) := by simpa using hcoord
    have hder : HasDerivAt ((fun z => (χ z).ofLp 0) ∘ fun t : ℝ => p + t • v) (L (A v)) 0 :=
      hcoord'.comp_hasDerivAt (x := (0:ℝ)) (f := fun t : ℝ => p + t • v) (f' := v)
        (l := fun z => (χ z).ofLp 0) (l' := L.comp A) hcurve hmemEv
    have hev : ((fun z => (χ z).ofLp 0) ∘ fun t : ℝ => p + t • v) =ᶠ[𝓝 (0:ℝ)] fun _ => 0 := by
      have hA : ∀ᶠ t : ℝ in 𝓝 (0:ℝ),
          (p + t • v) ∈ range (𝓡∂ n) → ((χ (p + t • v)).ofLp 0 = 0 ↔ (p + t • v).ofLp 0 = 0) :=
        hcont.eventually hzero'
      filter_upwards [hA, hmemEv] with t h1 h2
      exact (h1 h2).mpr (hcurvecoord t)
    have hder0 : HasDerivAt ((fun z => (χ z).ofLp 0) ∘ fun t : ℝ => p + t • v) 0 0 :=
      hev.hasDerivAt_iff.mpr (hasDerivAt_const (x := (0:ℝ)) (c := (0:ℝ)))
    have h := hder.unique hder0
    simpa [hL, ContinuousLinearMap.comp_apply, PiLp.proj_apply] using h
  -- ## Step B: `L ∘ A = (L (A e₀)) • L`
  have hlin : ∀ v : EuclideanSpace ℝ (Fin n), (A v).ofLp 0 = v.ofLp 0 * (A e₀).ofLp 0 := by
    intro v
    have hker : (v - v.ofLp 0 • e₀).ofLp 0 = 0 := by
      simp [PiLp.sub_apply, PiLp.smul_apply, he₀_0]
    have hdecomp : v = v.ofLp 0 • e₀ + (v - v.ofLp 0 • e₀) := by abel
    calc (A v).ofLp 0
        = (A (v.ofLp 0 • e₀ + (v - v.ofLp 0 • e₀))).ofLp 0 := by rw [← hdecomp]
      _ = ((v.ofLp 0) • (A e₀) + A (v - v.ofLp 0 • e₀)).ofLp 0 := by rw [map_add, map_smul]
      _ = v.ofLp 0 * (A e₀).ofLp 0 + (A (v - v.ofLp 0 • e₀)).ofLp 0 := by
            simp [PiLp.smul_apply]
      _ = v.ofLp 0 * (A e₀).ofLp 0 := by rw [stepA _ hker, add_zero]
  -- ## Step C: positivity of `L (A e₀)`
  have hcurv : HasDerivAt (fun t : ℝ => p + t • e₀) e₀ 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • e₀) ((1 : ℝ) • e₀) (0 : ℝ) :=
      (hasDerivAt_id (0 : ℝ)).smul_const e₀
    have h2 : HasDerivAt (fun t : ℝ => p + t • e₀) ((1 : ℝ) • e₀) 0 := h1.const_add p
    simpa using h2
  have hcontv : Tendsto (fun t : ℝ => p + t • e₀) (𝓝 (0:ℝ)) (𝓝 p) := by
    have h' := hcurv.continuousAt.tendsto
    rwa [show p + (0:ℝ) • e₀ = p from by simp] at h'
  have hcoord'' : HasFDerivWithinAt (fun z => (χ z).ofLp 0) (L.comp A) (range (𝓡∂ n))
      (p + (0:ℝ) • e₀) := by simpa using hcoord
  have hmapsIci : MapsTo (fun t : ℝ => p + t • e₀) (Ici 0) (range (𝓡∂ n)) := by
    intro t ht
    rw [range_modelWithCornersEuclideanHalfSpace]
    show (0:ℝ) ≤ (p + t • e₀).ofLp 0
    rw [show (p + t • e₀).ofLp 0 = t from by simp [PiLp.smul_apply, hp, he₀_0]]
    exact ht
  have hderIci : HasDerivWithinAt ((fun z => (χ z).ofLp 0) ∘ fun t : ℝ => p + t • e₀)
      (L (A e₀)) (Ici 0) 0 :=
    hcoord''.comp_hasDerivWithinAt (x := (0:ℝ)) (f := fun t : ℝ => p + t • e₀) (f' := e₀)
      (l := fun z => (χ z).ofLp 0) (l' := L.comp A) hcurv.hasDerivWithinAt hmapsIci
  have hposIci : ∀ᶠ t : ℝ in 𝓝[Ici 0] (0:ℝ), 0 ≤ (χ (p + t • e₀)).ofLp 0 := by
    have h1 : ∀ᶠ t : ℝ in 𝓝[Ici 0] (0:ℝ), p + t • e₀ ∈ range (𝓡∂ n) :=
      Eventually.mono (show ∀ᶠ t : ℝ in 𝓝[Ici 0] (0:ℝ), t ∈ Ici (0:ℝ) from self_mem_nhdsWithin)
        (fun t ht => hmapsIci ht)
    have h2 : ∀ᶠ t : ℝ in 𝓝[Ici 0] (0:ℝ), (p + t • e₀) ∈ range (𝓡∂ n) →
        0 ≤ (χ (p + t • e₀)).ofLp 0 :=
      (hcontv.mono_left nhdsWithin_le_nhds).eventually hpos'
    filter_upwards [h2, h1] with t h3 h4
    exact h3 h4
  have hc_nonneg : 0 ≤ L (A e₀) := by
    have hslope : Tendsto (slope ((fun z => (χ z).ofLp 0) ∘ fun t : ℝ => p + t • e₀) 0)
        (𝓝[Ici (0:ℝ) \ {0}] (0:ℝ)) (𝓝 (L (A e₀))) :=
      (hasDerivWithinAt_iff_tendsto_slope).mp hderIci
    have hfilt : Ici (0:ℝ) \ {0} = Ioi 0 := by
      ext t
      constructor
      · intro ht
        simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff] at ht
        exact lt_of_le_of_ne' ht.1 ht.2
      · intro ht
        simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff]
        exact ⟨le_of_lt ht, ne_of_gt ht⟩
    rw [hfilt] at hslope
    haveI : (𝓝[>] (0:ℝ)).NeBot := nhdsGT_neBot 0
    refine ge_of_tendsto hslope ?_
    filter_upwards [hposIci.filter_mono (nhdsWithin_mono 0 Ioi_subset_Ici_self),
      (show ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), (0:ℝ) < t from self_mem_nhdsWithin)] with t hpt ht
    have hf0 : ((fun z => (χ z).ofLp 0) ∘ fun t : ℝ => p + t • e₀) 0 = 0 := by
      simpa using hpχ
    rw [slope_def_module, hf0, sub_zero]
    exact smul_nonneg (inv_nonneg.mpr (le_of_lt ht)) (by simpa using hpt)
  have hc_ne : L (A e₀) ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := hsurj e₀
    have h3 : L (A e₀) = (A e₀).ofLp 0 := by simp [hL, PiLp.proj_apply]
    have h1 : (A v).ofLp 0 = 0 := by rw [hlin v, ← h3, h0, mul_zero]
    rw [hv, he₀_0] at h1
    exact one_ne_zero h1
  -- ## Step D
  refine ⟨L (A e₀), lt_of_le_of_ne hc_nonneg (Ne.symm hc_ne), ?_⟩
  have hLA : L.comp A = (L (A e₀)) • L := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, smul_apply]
    have h1 : L (A v) = (A v).ofLp 0 := by simp [hL, PiLp.proj_apply]
    have h2 : L v = v.ofLp 0 := by simp [hL, PiLp.proj_apply]
    have h3 : L (A e₀) = (A e₀).ofLp 0 := by simp [hL, PiLp.proj_apply]
    rw [h1, h2, h3, hlin v, mul_comm, smul_eq_mul]
  rw [hfderiv, hLA, hL]

/-- A function `Ψ` with `Ψ 0 = 0` and nonzero derivative `d` at `0` has, near `0`, the sign of
`d * s`. -/
theorem eventuallyLeZeroOfHasDerivAt {Ψ : ℝ → ℝ} {d : ℝ} (h0 : Ψ 0 = 0) (hd : HasDerivAt Ψ d 0)
    (hne : d ≠ 0) : ∀ᶠ s in 𝓝 (0 : ℝ), (Ψ s ≤ 0 ↔ d * s ≤ 0) := by
  have hslope : Tendsto (slope Ψ 0) (𝓝[≠] (0:ℝ)) (𝓝 d) := hd.tendsto_slope
  have hev : ∀ᶠ s in 𝓝[≠] (0:ℝ), |slope Ψ 0 s - d| < |d| := by
    have h := (Metric.tendsto_nhds.mp hslope) |d| (abs_pos.mpr hne)
    filter_upwards [h] with s hs
    rwa [Real.dist_eq] at hs
  have hsign : ∀ᶠ s in 𝓝[≠] (0:ℝ),
      (0 < d → 0 < slope Ψ 0 s) ∧ (d < 0 → slope Ψ 0 s < 0) := by
    filter_upwards [hev] with s hs
    obtain ⟨h1, h2⟩ := abs_sub_lt_iff.mp hs
    constructor
    · intro hd'
      have h3 : |d| = d := abs_of_pos hd'
      rw [h3] at h2
      linarith
    · intro hd'
      have h3 : |d| = -d := abs_of_neg hd'
      rw [h3] at h1
      linarith
  have hmain : ∀ᶠ s in 𝓝[≠] (0:ℝ), (Ψ s ≤ 0 ↔ d * s ≤ 0) := by
    filter_upwards [hsign, (show ∀ᶠ s in 𝓝[≠] (0:ℝ), s ≠ 0 from self_mem_nhdsWithin)]
      with s hs hs0
    have hval : Ψ s = s * slope Ψ 0 s := by
      simp only [slope_def_field, h0, sub_zero]
      exact (mul_div_cancel₀ (Ψ s) hs0).symm
    rw [hval]
    rcases lt_trichotomy d 0 with hd' | hd' | hd'
    · have hsl : slope Ψ 0 s < 0 := hs.2 hd'
      constructor
      · intro h
        rcases (mul_nonpos_iff.mp h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hd') h1
        · exact absurd h2 (not_le_of_gt hsl)
      · intro h
        rcases (mul_nonpos_iff.mp h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1 (not_le_of_gt hd')
        · exact mul_nonpos_of_nonneg_of_nonpos h2 (le_of_lt hsl)
    · exact absurd hd' hne
    · have hsl : 0 < slope Ψ 0 s := hs.1 hd'
      constructor
      · intro h
        rcases (mul_nonpos_iff.mp h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h2 (not_le_of_gt hsl)
        · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd') h1
      · intro h
        rcases (mul_nonpos_iff.mp h) with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact mul_nonpos_of_nonpos_of_nonneg h2 (le_of_lt hsl)
        · exact absurd h1 (not_le_of_gt hd')
  have hfin := eventually_nhdsWithin_iff.mp hmain
  filter_upwards [hfin] with s hs
  by_cases hs0 : s = 0
  · rw [hs0]; simp [h0]
  · exact hs hs0

/-- **The `0`-th coordinate of a chart of the maximal atlas at a boundary point.**  For a chart `e`
of the maximal atlas of `A` around a boundary point `x`, the derivative of `y ↦ (e y).1 0` at `x` is
a *positive* multiple of the `0`-th coordinate functional `z ↦ z 0` of the model
`EuclideanSpace ℝ (Fin n)` (identified with the tangent space of `A` at `x`). -/
theorem chartCoordMfderiv {n : ℕ} [NeZero n] {A : Type*} [TopologicalSpace A]
    [ChartedSpace (EuclideanHalfSpace n) A] [IsManifold (𝓡∂ n) ∞ A]
    (e : OpenPartialHomeomorph A (EuclideanHalfSpace n))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ A) {x : A} (hx : x ∈ e.source)
    (hxb : x ∈ (𝓡∂ n).boundary A) :
    ∃ c : ℝ, 0 < c ∧ mfderiv (𝓡∂ n) (𝓘(ℝ,ℝ)) (fun y : A => (e y).1 0) x
      = c • PiLp.proj 2 (fun _ : Fin n => ℝ) 0 := by
  have hchart : chartAt (EuclideanHalfSpace n) x ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ A :=
    IsManifold.chart_mem_maximalAtlas x
  have hchartx : x ∈ (chartAt (EuclideanHalfSpace n) x).source := mem_chart_source _ _
  set χp : PartialEquiv (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    (𝓡∂ n).extendCoordChange (chartAt (EuclideanHalfSpace n) x) e with hχp
  set χ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := ⇑χp with hχ
  set ex : EuclideanSpace ℝ (Fin n) := extChartAt (𝓡∂ n) x x with hex
  have hex0 : ex.ofLp 0 = 0 := by
    have h1 : ex ∈ frontier (range (𝓡∂ n)) := by
      rw [← (𝓡∂ n).isBoundaryPoint_iff]; exact hxb
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at h1
    exact h1.symm
  have hcd : ContDiffWithinAt ℝ ∞ χ (range (𝓡∂ n)) ex :=
    ModelWithCorners.contDiffWithinAt_extendCoordChange' (I := (𝓡∂ n))
      (e := chartAt (EuclideanHalfSpace n) x) (e' := e) (x := x) hchart he hchartx hx
  have hexsource : ex ∈ χp.source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter]
    exact mem_image_of_mem _ ⟨hchartx, hx⟩
  have huniq : UniqueDiffWithinAt ℝ χp.source ex :=
    (ModelWithCorners.uniqueDiffOn_extendCoordChange_source (I := (𝓡∂ n))
      (e := chartAt (EuclideanHalfSpace n) x) (e' := e)).uniqueDiffWithinAt hexsource
  have hsub : χp.source ⊆ range (𝓡∂ n) := by
    rw [hχp, ModelWithCorners.extendCoordChange_source]; exact Set.image_subset_range _ _
  have hdiffR : DifferentiableWithinAt ℝ χ (range (𝓡∂ n)) ex :=
    hcd.differentiableWithinAt (by simp)
  have hswap : fderivWithin ℝ χ χp.source ex = fderivWithin ℝ χ (range (𝓡∂ n)) ex :=
    fderivWithin_subset hsub huniq hdiffR
  have hsurj : Function.Surjective (fderivWithin ℝ χ (range (𝓡∂ n)) ex) := by
    rw [← hswap]
    exact (ModelWithCorners.isInvertible_fderivWithin_extendCoordChange (hn := by simp)
      (I := (𝓡∂ n)) hchart he hexsource).surjective
  have hdiff : HasFDerivWithinAt χ (fderivWithin ℝ χ (range (𝓡∂ n)) ex) (range (𝓡∂ n)) ex :=
    hdiffR.hasFDerivWithinAt
  have hpos : ∀ᶠ z in 𝓝[range (𝓡∂ n)] ex, 0 ≤ (χ z).ofLp 0 := by
    filter_upwards with z
    change 0 ≤ (((e.extend (𝓡∂ n)) (((chartAt (EuclideanHalfSpace n) x).extend (𝓡∂ n)).symm z))).ofLp 0
    rw [OpenPartialHomeomorph.extend_coe]
    exact (e (((chartAt (EuclideanHalfSpace n) x).extend (𝓡∂ n)).symm z)).2
  have hzero : ∀ᶠ z in 𝓝[range (𝓡∂ n)] ex, ((χ z).ofLp 0 = 0 ↔ z.ofLp 0 = 0) := by
    have h1 : ∀ᶠ z in 𝓝[range (𝓡∂ n)] ex, z ∈ (extChartAt (𝓡∂ n) x).target :=
      extChartAt_target_mem_nhdsWithin x
    have h2 : (extChartAt (𝓡∂ n) x).symm ⁻¹' e.source ∈ 𝓝 (extChartAt (𝓡∂ n) x x) :=
      OpenPartialHomeomorph.extend_preimage_mem_nhds (f := chartAt (EuclideanHalfSpace n) x)
        (I := (𝓡∂ n)) hchartx (e.open_source.mem_nhds hx)
    have h2' : ∀ᶠ z in 𝓝[range (𝓡∂ n)] ex, (extChartAt (𝓡∂ n) x).symm z ∈ e.source :=
      nhdsWithin_le_nhds h2
    have h3 : (extChartAt (𝓡∂ n) x).symm ⁻¹' (chartAt (EuclideanHalfSpace n) x).source ∈
        𝓝 (extChartAt (𝓡∂ n) x x) :=
      OpenPartialHomeomorph.extend_preimage_mem_nhds (f := chartAt (EuclideanHalfSpace n) x)
        (I := (𝓡∂ n)) hchartx ((chartAt (EuclideanHalfSpace n) x).open_source.mem_nhds hchartx)
    have h3' : ∀ᶠ z in 𝓝[range (𝓡∂ n)] ex,
        (extChartAt (𝓡∂ n) x).symm z ∈ (chartAt (EuclideanHalfSpace n) x).source :=
      nhdsWithin_le_nhds h3
    filter_upwards [h1, h2', h3'] with z hz1 hz2 hz3
    have hzy : (extChartAt (𝓡∂ n) x) ((extChartAt (𝓡∂ n) x).symm z) = z :=
      PartialEquiv.right_inv _ hz1
    have hA : ((χ z).ofLp 0 = 0) ↔
        (((e.extend (𝓡∂ n)) ((extChartAt (𝓡∂ n) x).symm z)).ofLp 0 = 0) := Iff.rfl
    rw [hA]
    have hB := Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
      (m := n) (M := A) he hz2
    have hC := Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
      (m := n) (M := A) hchart hz3
    rw [← hB, hC]
    rw [show ((chartAt (EuclideanHalfSpace n) x).extend (𝓡∂ n))
        ((extChartAt (𝓡∂ n) x).symm z) = z from hzy]
  obtain ⟨c, hc, hc'⟩ := normalFunctionalHalfSpace (n := n) hex0 hdiff hsurj hpos hzero
  let P : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin n => ℝ) 0
  have hexmem : ex ∈ range (𝓡∂ n) := by
    rw [range_modelWithCornersEuclideanHalfSpace]; exact le_of_eq hex0.symm
  have hfun : writtenInExtChartAt (𝓡∂ n) (𝓘(ℝ,ℝ)) x (fun y : A => (e y).1 0)
      = fun z : EuclideanSpace ℝ (Fin n) => (χ z).ofLp 0 := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply,
      ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
      OpenPartialHomeomorph.extend_coe, modelWithCornersEuclideanHalfSpace_apply]
    rfl
  have hcomp : HasFDerivWithinAt (fun z : EuclideanSpace ℝ (Fin n) => (χ z).ofLp 0)
      (P.comp (fderivWithin ℝ χ (range (𝓡∂ n)) ex)) (range (𝓡∂ n)) ex := by
    have hbase : HasFDerivWithinAt ((⇑P) ∘ χ)
        (P.comp (fderivWithin ℝ χ (range (𝓡∂ n)) ex)) (range (𝓡∂ n)) ex :=
      (P.hasFDerivAt.hasFDerivWithinAt).comp (g := ⇑P) ex hdiff (mapsTo_univ _ _)
    rw [show (fun z : EuclideanSpace ℝ (Fin n) => (χ z).ofLp 0) = (⇑P ∘ χ) from by
      funext z; rfl]
    exact hbase
  have hderCoord : fderivWithin ℝ (fun z : EuclideanSpace ℝ (Fin n) => (χ z).ofLp 0)
      (range (𝓡∂ n)) ex = P.comp (fderivWithin ℝ χ (range (𝓡∂ n)) ex) :=
    hcomp.fderivWithin ((𝓡∂ n).uniqueDiffOn.uniqueDiffWithinAt hexmem)
  have hmf : mfderiv (𝓡∂ n) (𝓘(ℝ,ℝ)) (fun y : A => (e y).1 0) x
      = P.comp (fderivWithin ℝ χ (range (𝓡∂ n)) ex) := by
    have hsm1 : ContMDiffAt (𝓡∂ n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (e.extend (𝓡∂ n)) x :=
      (e.contMDiffOn_extend (I := (𝓡∂ n)) he).contMDiffAt (I := (𝓡∂ n))
        (e.open_source.mem_nhds hx)
    have hsm2 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓘(ℝ,ℝ)) ∞ P (e.extend (𝓡∂ n) x) :=
      P.contMDiff.contMDiffAt
    have hsm3 : ContMDiffAt (𝓡∂ n) (𝓘(ℝ,ℝ)) ∞
        (fun y : A => ((e.extend (𝓡∂ n)) y).ofLp 0) x := hsm2.comp x hsm1
    have hsm : ContMDiffAt (𝓡∂ n) (𝓘(ℝ,ℝ)) ∞ (fun y : A => (e y).1 0) x := by
      simpa only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
        modelWithCornersEuclideanHalfSpace_apply] using hsm3
    have hwritten : HasFDerivWithinAt
        (writtenInExtChartAt (𝓡∂ n) (𝓘(ℝ,ℝ)) x (fun y : A => (e y).1 0))
        (P.comp (fderivWithin ℝ χ (range (𝓡∂ n)) ex)) (range (𝓡∂ n)) ((extChartAt (𝓡∂ n) x) x) := by
      rw [hfun, ← hex]
      exact hcomp
    exact (show HasMFDerivAt (𝓡∂ n) (𝓘(ℝ,ℝ)) (fun y : A => (e y).1 0) x
        (P.comp (fderivWithin ℝ χ (range (𝓡∂ n)) ex)) from
        ⟨hsm.continuousAt, hwritten⟩).mfderiv
  refine ⟨c, hc, ?_⟩
  have hmid : fderivWithin ℝ (fun z : EuclideanSpace ℝ (Fin n) => (χ z).ofLp 0)
      (range (𝓡∂ n)) ex = c • PiLp.proj 2 (fun _ : Fin n => ℝ) 0 := hc'
  have h1 : mfderiv (𝓡∂ n) (𝓘(ℝ,ℝ)) (fun y : A => (e y).1 0) x
      = fderivWithin ℝ (fun z : EuclideanSpace ℝ (Fin n) => (χ z).ofLp 0) (range (𝓡∂ n)) ex :=
    hmf.trans hderCoord.symm
  exact h1.trans hmid


/-- The derivative of an extended chart of the maximal atlas (as a map into the model) equals the
derivative, within the model, of the corresponding transition map. -/
theorem mfderiv_extend_eq_fderivWithin {n : ℕ} [NeZero n] {A : Type*} [TopologicalSpace A]
    [ChartedSpace (EuclideanHalfSpace n) A] [IsManifold (𝓡∂ n) ∞ A]
    (e : OpenPartialHomeomorph A (EuclideanHalfSpace n))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ A) {x : A} (hx : x ∈ e.source) :
    mfderiv (𝓡∂ n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (e.extend (𝓡∂ n)) x
      = fderivWithin ℝ (⇑((𝓡∂ n).extendCoordChange (chartAt (EuclideanHalfSpace n) x) e))
          (range (𝓡∂ n)) (extChartAt (𝓡∂ n) x x) := by
  have hmd : MDifferentiableAt (𝓡∂ n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (e.extend (𝓡∂ n)) x :=
    ((e.contMDiffOn_extend (I := (𝓡∂ n)) he).contMDiffAt (I := (𝓡∂ n))
      (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hfun : writtenInExtChartAt (𝓡∂ n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x (e.extend (𝓡∂ n))
      = ⇑((𝓡∂ n).extendCoordChange (chartAt (EuclideanHalfSpace n) x) e) := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply,
      ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply]
    rfl
  refine (show HasMFDerivAt (𝓡∂ n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (e.extend (𝓡∂ n)) x
      (fderivWithin ℝ (⇑((𝓡∂ n).extendCoordChange (chartAt (EuclideanHalfSpace n) x) e))
        (range (𝓡∂ n)) (extChartAt (𝓡∂ n) x x)) from ⟨hmd.continuousAt, ?_⟩).mfderiv
  rw [hfun]
  exact (((ModelWithCorners.contDiffWithinAt_extendCoordChange' (I := (𝓡∂ n))
      (e := chartAt (EuclideanHalfSpace n) x) (e' := e) (x := x)
      (IsManifold.chart_mem_maximalAtlas x) he (mem_chart_source _ _) hx)).differentiableWithinAt
        (by simp)).hasFDerivWithinAt

/-- The derivative, within the model, of the transition map between the chart at a point and any
chart of the maximal atlas is invertible. -/
theorem isInvertible_fderivWithin_transition {n : ℕ} [NeZero n] {A : Type*} [TopologicalSpace A]
    [ChartedSpace (EuclideanHalfSpace n) A] [IsManifold (𝓡∂ n) ∞ A]
    (e : OpenPartialHomeomorph A (EuclideanHalfSpace n))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ A) {x : A} (hx : x ∈ e.source) :
    (fderivWithin ℝ (⇑((𝓡∂ n).extendCoordChange (chartAt (EuclideanHalfSpace n) x) e))
      (range (𝓡∂ n)) (extChartAt (𝓡∂ n) x x)).IsInvertible := by
  have hchartx : x ∈ (chartAt (EuclideanHalfSpace n) x).source := mem_chart_source _ _
  have hchart : chartAt (EuclideanHalfSpace n) x ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ A :=
    IsManifold.chart_mem_maximalAtlas x
  set τp : PartialEquiv (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    (𝓡∂ n).extendCoordChange (chartAt (EuclideanHalfSpace n) x) e with hτp
  have hexsource : extChartAt (𝓡∂ n) x x ∈ τp.source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter]
    exact mem_image_of_mem _ ⟨hchartx, hx⟩
  have huniq : UniqueDiffWithinAt ℝ τp.source (extChartAt (𝓡∂ n) x x) :=
    (ModelWithCorners.uniqueDiffOn_extendCoordChange_source (I := (𝓡∂ n))
      (e := chartAt (EuclideanHalfSpace n) x) (e' := e)).uniqueDiffWithinAt hexsource
  have hsub : τp.source ⊆ range (𝓡∂ n) := by
    rw [hτp, ModelWithCorners.extendCoordChange_source]; exact Set.image_subset_range _ _
  have hcd : ContDiffWithinAt ℝ ∞ (⇑τp) (range (𝓡∂ n)) (extChartAt (𝓡∂ n) x x) :=
    ModelWithCorners.contDiffWithinAt_extendCoordChange' (I := (𝓡∂ n))
      (e := chartAt (EuclideanHalfSpace n) x) (e' := e) (x := x) hchart he hchartx hx
  have hdiffR : DifferentiableWithinAt ℝ (⇑τp) (range (𝓡∂ n)) (extChartAt (𝓡∂ n) x x) :=
    hcd.differentiableWithinAt (by simp)
  have hswap : fderivWithin ℝ (⇑τp) τp.source (extChartAt (𝓡∂ n) x x)
      = fderivWithin ℝ (⇑τp) (range (𝓡∂ n)) (extChartAt (𝓡∂ n) x x) :=
    fderivWithin_subset hsub huniq hdiffR
  rw [← hswap]
  exact ModelWithCorners.isInvertible_fderivWithin_extendCoordChange (hn := by simp)
    (I := (𝓡∂ n)) hchart he hexsource

theorem regionNhdBoundaryZero {n : ℕ} [NeZero n] (A : Type*) [TopologicalSpace A]
    [ChartedSpace (EuclideanHalfSpace n) A] [IsManifold (𝓡∂ n) ∞ A] (Φ : A → ℝ)
    (hΦ : ContMDiff (𝓡∂ n) (𝓘(ℝ, ℝ)) ∞ Φ)
    (hsub : ∀ x : A, Φ x = 0 → IsSubmersionAt (𝓡∂ n) (𝓘(ℝ, ℝ)) ∞ Φ x)
    (hone : ∀ x ∈ (𝓡∂ n).boundary A, Φ x = 0 →
      ∃ (e : OpenPartialHomeomorph A (EuclideanHalfSpace n)) (c : ℝ),
        e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ A ∧ x ∈ e.source ∧ c < 0 ∧
        (∀ y ∈ e.source, (e y).1 0 = 0 ↔ y ∈ (𝓡∂ n).boundary A) ∧
        mfderiv (𝓡∂ n) (𝓘(ℝ, ℝ)) Φ x
          = c • mfderiv (𝓡∂ n) (𝓘(ℝ, ℝ)) (fun y : A => (e y).1 0) x)
    {x : A} (hxb : x ∈ (𝓡∂ n).boundary A) (hx0 : Φ x = 0) :
    ∀ᶠ y in 𝓝 x, Φ y ≤ 0 := by
  have hchartx : x ∈ (chartAt (EuclideanHalfSpace n) x).source := mem_chart_source _ _
  set ex : EuclideanSpace ℝ (Fin n) := extChartAt (𝓡∂ n) x x with hex
  -- ## 1. hone's chart, and the derivative of Φ at x
  obtain ⟨e, c, he, hxe, hc, hzero_e, hdere⟩ := hone x hxb hx0
  obtain ⟨ce, hce_pos, hce_eq⟩ := chartCoordMfderiv e he hxe hxb
  have hdPhi : mfderiv (𝓡∂ n) (𝓘(ℝ,ℝ)) Φ x = (c * ce) • PiLp.proj 2 (fun _ : Fin n => ℝ) 0 := by
    rw [hdere, hce_eq]
    ext v
    show c * (ce * (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) 0 v))
      = (c * ce) * (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) 0 v)
    ring
  have hcce_neg : c * ce < 0 := mul_neg_of_neg_of_pos hc hce_pos
  set e₀ : EuclideanSpace ℝ (Fin n) := PiLp.single 2 (0 : Fin n) (1 : ℝ) with he₀
  have hPe₀ : (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) 0) e₀ = 1 := by simp [he₀]
  have hPne : (PiLp.proj 2 (fun _ : Fin n => ℝ) 0 :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ≠ 0 := by
    intro h0
    rw [h0, ContinuousLinearMap.zero_apply] at hPe₀
    exact one_ne_zero hPe₀.symm
  -- ## 2. the submersion normal form at x
  obtain ⟨F, hF₁, hF₂, h⟩ := hsub x hx0
  let Lc : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ F).comp h.equiv.toContinuousLinearMap
  have hφmax : h.domChart ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ A := h.domChart_mem_maximalAtlas
  have hψmax : h.codChart ∈ IsManifold.maximalAtlas (𝓘(ℝ,ℝ)) ∞ ℝ := h.codChart_mem_maximalAtlas
  have hφx : x ∈ h.domChart.source := h.mem_domChart_source
  have hψ0src : Φ x ∈ h.codChart.source := h.mem_codChart_source
  have hmaps_to : h.domChart.source ⊆ Φ ⁻¹' h.codChart.source := h.source_subset_preimage_source
  obtain ⟨cφ, hcφ_pos, hcφ_eq⟩ := chartCoordMfderiv h.domChart hφmax hφx hxb
  have hφx0 : ((h.domChart.extend (𝓡∂ n)) x).ofLp 0 = 0 :=
    (Work.ThomBordism.Transversality.Preimage.mem_boundary_iff_extend_apply_coord_eq_zero
      (m := n) (M := A) hφmax hφx).mp hxb
  -- the normal-form equation
  have hEq : ∀ y ∈ h.domChart.source, h.codChart (Φ y) = Lc ((h.domChart.extend (𝓡∂ n)) y) := by
    intro y hy
    have hz : (h.domChart.extend (𝓡∂ n)) y ∈ (h.domChart.extend (𝓡∂ n)).target :=
      PartialEquiv.map_source _ (by simpa using hy)
    have hw := h.writtenInCharts (I := (𝓡∂ n)) (J := (𝓘(ℝ,ℝ))) hz
    have hsymm : (h.domChart.extend (𝓡∂ n)).symm ((h.domChart.extend (𝓡∂ n)) y) = y :=
      PartialEquiv.left_inv _ (by simpa using hy)
    simp only [Function.comp_apply] at hw
    rw [hsymm] at hw
    have hw' : h.codChart (Φ y) = (h.equiv ((h.domChart.extend (𝓡∂ n)) y)).1 := by
      simpa only [OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, Function.comp_apply,
        Function.id_def] using hw
    rw [hw']
    rfl
  -- ## 3. the transition to the distinguished chart, and its derivative
  set τp : PartialEquiv (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    (𝓡∂ n).extendCoordChange (chartAt (EuclideanHalfSpace n) x) h.domChart with hτp
  set τ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := ⇑τp with hτ
  have hτeq : τ = ⇑((𝓡∂ n).extendCoordChange (chartAt (EuclideanHalfSpace n) x) h.domChart) := by
    rw [hτ, hτp]
  set A' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fderivWithin ℝ τ (range (𝓡∂ n)) ex with hA'
  have hAeq : mfderiv (𝓡∂ n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (h.domChart.extend (𝓡∂ n)) x = A' := by
    have hml := mfderiv_extend_eq_fderivWithin (e := h.domChart) hφmax hφx
    rw [← hex] at hml
    rw [show ⇑((𝓡∂ n).extendCoordChange (chartAt (EuclideanHalfSpace n) x) h.domChart) = τ
      from hτeq.symm] at hml
    rw [hA']
    exact hml
  -- ## 3b. `A'` is invertible, hence surjective
  have hAinv : A'.IsInvertible := by
    rw [hA', hτeq]
    exact isInvertible_fderivWithin_transition (e := h.domChart) hφmax hφx
  have hAsurj : Function.Surjective A' := hAinv.surjective
  -- ## 3c. `P ∘ A' = cφ • P`
  have hφmd : MDifferentiableAt (𝓡∂ n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (h.domChart.extend (𝓡∂ n)) x :=
    ((h.domChart.contMDiffOn_extend (I := (𝓡∂ n)) hφmax).contMDiffAt (I := (𝓡∂ n))
      (h.domChart.open_source.mem_nhds hφx)).mdifferentiableAt (by simp)
  have hPmf : mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓘(ℝ,ℝ))
      (⇑(PiLp.proj 2 (fun _ : Fin n => ℝ) 0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      ((h.domChart.extend (𝓡∂ n)) x) = (PiLp.proj 2 (fun _ : Fin n => ℝ) 0 :
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
    rw [mfderiv_eq_fderiv]
    exact (ContinuousLinearMap.hasFDerivAt _).fderiv
  have hcoordmf : mfderiv (𝓡∂ n) (𝓘(ℝ,ℝ)) (fun y : A => (h.domChart y).1 0) x
      = (PiLp.proj 2 (fun _ : Fin n => ℝ) 0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).comp
        (mfderiv (𝓡∂ n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (h.domChart.extend (𝓡∂ n)) x) := by
    have hcomp := mfderiv_comp (I := (𝓡∂ n)) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I'' := 𝓘(ℝ,ℝ)) x (f := h.domChart.extend (𝓡∂ n))
      (g := ⇑(PiLp.proj 2 (fun _ : Fin n => ℝ) 0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
      (ContinuousLinearMap.mdifferentiableAt _) hφmd
    rw [hPmf] at hcomp
    rw [show (fun y : A => (h.domChart y).1 0) = ((⇑(PiLp.proj 2 (fun _ : Fin n => ℝ) 0 :
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∘ (h.domChart.extend (𝓡∂ n))) from by
      funext y; rfl]
    exact hcomp
  have hPA : (PiLp.proj 2 (fun _ : Fin n => ℝ) 0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).comp A'
      = cφ • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := by
    rw [← hAeq, ← hcoordmf]
    exact hcφ_eq
  -- ## 4. the chain rule
  set Ψ : ℝ → ℝ := ⇑(h.codChart.symm) with hΨ
  set φL : A → ℝ := ⇑Lc ∘ (h.domChart.extend (𝓡∂ n)) with hφL
  have hφc : ContMDiffAt (𝓡∂ n) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (h.domChart.extend (𝓡∂ n)) x :=
    (h.domChart.contMDiffOn_extend (I := (𝓡∂ n)) hφmax).contMDiffAt (I := (𝓡∂ n))
      (h.domChart.open_source.mem_nhds hφx)
  have hφLy : ∀ y : A, φL y = Lc ((h.domChart.extend (𝓡∂ n)) y) := by
    intro y; simp only [hφL, Function.comp_apply]
  have hHc : ContMDiffAt (𝓡∂ n) (𝓘(ℝ,ℝ)) ∞ φL x := by
    have h := (ContinuousLinearMap.contMDiff (𝕜 := ℝ) Lc).contMDiffAt.comp x hφc
    rwa [hφL]
  have hHmd : MDifferentiableAt (𝓡∂ n) (𝓘(ℝ,ℝ)) φL x := hHc.mdifferentiableAt (by simp)
  have htl : φL x ∈ h.codChart.target := by
    rw [hφLy x, ← hEq x hφx]
    exact PartialEquiv.map_source _ hψ0src
  have hΨc : ContMDiffAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) ∞ Ψ (φL x) := by
    have h1 := contMDiffAt_symm_of_mem_maximalAtlas (I := (𝓘(ℝ,ℝ))) (n := ∞) hψmax htl
    simpa only [hΨ] using h1
  have hΨmd : MDifferentiableAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) Ψ (φL x) := hΨc.mdifferentiableAt (by simp)
  have hHeq : Φ =ᶠ[𝓝 x] Ψ ∘ φL := by
    filter_upwards [h.domChart.open_source.mem_nhds hφx] with y hy
    simp only [Function.comp_apply, hφLy y]
    exact ((h.codChart.left_inv (hmaps_to hy)).symm).trans (congrArg Ψ (hEq y hy))
  have h4 : mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓘(ℝ,ℝ)) (⇑Lc)
      ((h.domChart.extend (𝓡∂ n)) x) = Lc := by
    rw [mfderiv_eq_fderiv]
    exact ContinuousLinearMap.fderiv Lc
  have hHder : mfderiv (𝓡∂ n) (𝓘(ℝ,ℝ)) φL x = Lc.comp A' := by
    have hcomp := mfderiv_comp (I := (𝓡∂ n)) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I'' := 𝓘(ℝ,ℝ)) x (f := (h.domChart.extend (𝓡∂ n))) (g := ⇑Lc)
      (ContinuousLinearMap.mdifferentiableAt Lc) hφmd
    rw [h4, hAeq] at hcomp
    rw [hφL]
    exact hcomp
  have hchain : mfderiv (𝓡∂ n) (𝓘(ℝ,ℝ)) Φ x
      = (fderiv ℝ Ψ (φL x)).comp (Lc.comp A') := by
    have h1 := mfderiv_comp (I := (𝓡∂ n)) (I' := 𝓘(ℝ,ℝ))
      (I'' := 𝓘(ℝ,ℝ)) x (f := φL) (g := Ψ) hΨmd hHmd
    have h2 : mfderiv (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) Ψ (φL x) = fderiv ℝ Ψ (φL x) := by
      rw [mfderiv_eq_fderiv]
      all_goals first | rfl | (ext v; rfl) | simp
    calc mfderiv (𝓡∂ n) (𝓘(ℝ,ℝ)) Φ x
        = mfderiv (𝓡∂ n) (𝓘(ℝ,ℝ)) (Ψ ∘ φL) x := hHeq.mfderiv_eq
      _ = (mfderiv (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) Ψ (φL x)).comp (mfderiv (𝓡∂ n) (𝓘(ℝ,ℝ)) φL x) := h1
      _ = (fderiv ℝ Ψ (φL x)).comp (Lc.comp A') := by rw [h2, hHder]
  -- ## 5. the linear algebra
  have hAB : (fderiv ℝ Ψ (φL x)).comp (Lc.comp A')
      = (c * ce) • (PiLp.proj 2 (fun _ : Fin n => ℝ) 0 :
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := hchain.symm.trans hdPhi
  set d1 : ℝ := (fderiv ℝ Ψ (φL x)) 1 with hd1
  set κ : ℝ := (c * ce) / (d1 * cφ) with hκ
  have hfd1 : ∀ s : ℝ, (fderiv ℝ Ψ (φL x)) s = d1 * s := by
    intro s
    have hm := map_smul (fderiv ℝ Ψ (φL x)) s (1 : ℝ)
    simp only [smul_eq_mul, mul_one] at hm
    rw [← hd1] at hm
    rw [hm, mul_comm]
  have hd1ne : d1 ≠ 0 := by
    intro h0
    have hval := congrArg (fun F : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => F e₀) hAB
    simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul] at hval
    rw [hfd1, h0, zero_mul, hPe₀, mul_one] at hval
    exact hcce_neg.ne hval.symm
  have hsec : ∀ v : EuclideanSpace ℝ (Fin n),
      Lc (A' v) = ((c * ce) / d1) * (v.ofLp 0) := by
    intro v
    have h1 := congrArg (fun F : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => F v) hAB
    simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul] at h1
    rw [hfd1, PiLp.proj_apply] at h1
    have h2 : Lc (A' v) = ((c * ce) * (v.ofLp 0)) / d1 := by
      rw [eq_div_iff hd1ne, mul_comm (Lc (A' v)) d1]
      exact h1
    rw [h2, div_mul_eq_mul_div]
  have hsecP : ∀ v : EuclideanSpace ℝ (Fin n), (A' v).ofLp 0 = cφ * (v.ofLp 0) := by
    intro v
    have h1 := congrArg (fun F : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => F v) hPA
    simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul,
      PiLp.proj_apply] at h1
    exact h1
  have hLcP : ∀ w : EuclideanSpace ℝ (Fin n), Lc w = κ * (w.ofLp 0) := by
    intro w
    obtain ⟨v, hv⟩ := hAsurj w
    have h1 : Lc w = ((c * ce) / d1) * (v.ofLp 0) := by
      rw [← hv]
      exact hsec v
    have h2 : w.ofLp 0 = cφ * (v.ofLp 0) := by
      rw [← hv]
      exact hsecP v
    rw [h1, h2, hκ]
    field_simp
  -- ## 6. the sign
  have hφLx0 : φL x = 0 := by
    rw [hφLy x, hLcP ((h.domChart.extend (𝓡∂ n)) x), hφx0, mul_zero]
  have hψ0 : h.codChart 0 = 0 := by
    have h1 := hEq x hφx
    rw [hx0] at h1
    rw [h1]
    exact hφLx0
  have hΨ0 : Ψ 0 = 0 := by
    have hm : (0 : ℝ) ∈ h.codChart.source := by rw [← hx0]; exact hψ0src
    have h2 : Ψ 0 = h.codChart.symm (h.codChart 0) := by rw [hΨ, hψ0]
    rw [h2, h.codChart.left_inv hm]
  have hsd : HasDerivAt Ψ d1 0 := by
    rw [hd1]
    have hmd0 : MDifferentiableAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,ℝ)) Ψ 0 := by
      have ht : (0 : ℝ) ∈ h.codChart.target := by
        have h0src : (0 : ℝ) ∈ h.codChart.source := by rw [← hx0]; exact hψ0src
        rw [← hψ0]
        exact PartialEquiv.map_source h.codChart.toPartialEquiv h0src
      exact (contMDiffAt_symm_of_mem_maximalAtlas (I := (𝓘(ℝ,ℝ))) (n := ∞) hψmax
        ht).mdifferentiableAt (by simp)
    have hd0 : DifferentiableAt ℝ Ψ 0 := mdifferentiableAt_iff_differentiableAt.mp hmd0
    have hder := hd0.hasFDerivAt.hasDerivAt
    rwa [show (fderiv ℝ Ψ (φL x)) = fderiv ℝ Ψ 0 from by rw [hφLx0]]
  have hsgn := eventuallyLeZeroOfHasDerivAt hΨ0 hsd hd1ne
  have hnonneg : ∀ y : A, 0 ≤ ((h.domChart.extend (𝓡∂ n)) y).ofLp 0 := by
    intro y
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      modelWithCornersEuclideanHalfSpace_apply]
    exact (h.domChart y).2
  have hκd1 : d1 * κ < 0 := by
    have h1 : d1 * κ = (c * ce) / cφ := by
      rw [hκ]
      field_simp
    rw [h1]
    exact div_neg_of_neg_of_pos hcce_neg hcφ_pos
  have hκmd : ContMDiffAt (𝓡∂ n) (𝓘(ℝ,ℝ)) ∞
      (fun y : A => ((h.domChart.extend (𝓡∂ n)) y).ofLp 0) x :=
    ((ContinuousLinearMap.contMDiff (𝕜 := ℝ) (PiLp.proj 2 (fun _ : Fin n => ℝ) 0 :
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).contMDiffAt).comp x hφc
  have hcont : Tendsto (fun y : A => κ * ((h.domChart.extend (𝓡∂ n)) y).ofLp 0) (𝓝 x) (𝓝 0) := by
    have h1 : Tendsto (fun y : A => κ * ((h.domChart.extend (𝓡∂ n)) y).ofLp 0) (𝓝 x)
        (𝓝 (κ * ((h.domChart.extend (𝓡∂ n)) x).ofLp 0)) := hκmd.continuousAt.const_mul κ
    rwa [hφx0, mul_zero] at h1
  have hval : ∀ y ∈ h.domChart.source, Φ y
      = Ψ (κ * ((h.domChart.extend (𝓡∂ n)) y).ofLp 0) := by
    intro y hy
    have h1 : Φ y = Ψ (h.codChart (Φ y)) := (h.codChart.left_inv (hmaps_to hy)).symm
    rw [h1, hEq y hy, hLcP ((h.domChart.extend (𝓡∂ n)) y)]
  have hsgn' : ∀ᶠ y in 𝓝 x, Ψ (κ * ((h.domChart.extend (𝓡∂ n)) y).ofLp 0) ≤ 0 := by
    filter_upwards [hcont.eventually hsgn] with y hy
    have ht : 0 ≤ ((h.domChart.extend (𝓡∂ n)) y).ofLp 0 := hnonneg y
    have h2 : d1 * (κ * ((h.domChart.extend (𝓡∂ n)) y).ofLp 0) ≤ 0 := by
      rw [← mul_assoc]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hκd1) ht
    exact hy.mpr h2
  filter_upwards [hsgn', h.domChart.open_source.mem_nhds hφx] with y h1 h2
  rw [hval y h2]
  exact h1


end

end Work.PTGeometric
