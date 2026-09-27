import Mathlib
import Submission.Work.Drive.N2.mfderiv_eq_zero_of_eqOn_band

/-! Companion of `Work.Drive.N2.mfderiv_eq_zero_of_eqOn_band` for `M`-valued maps (the
real-valued form cannot express an identity like `σ (τ z) = σ z`); the boundary case `f x = a` or
`f x = b`, where the band is only one-sided, needs the same chart/ray argument, and `hreg` plus
`hab` are what make it work.  Intended use: with `G z := Φ (c - f (Φ (b - f z, z)), Φ (b - f z, z))`
and `H z := Φ (c - f z, z)` (`c := f x`), both equal on the band by the flow composition law, it
gives `mfderiv (σ ∘ τ) x = mfderiv σ x`, hence
`(mfderiv σ (τ x)).comp (mfderiv τ x) = mfderiv σ x` by the chain rule. -/

open scoped Manifold ContDiff Topology
open Filter Set

namespace Work.Drive.N2

set_option autoImplicit false


/-! ## The one-dimensional one-sided lemma (Banach-valued) -/

/-- If `φ ψ : ℝ → E` are differentiable at `0` and agree on an interval `[α,β] ∋ 0` with
`α < β`, then `deriv φ 0 = deriv ψ 0`. -/
lemma deriv_eq_of_eqOn_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α β : ℝ} (hαβ : α < β) {φ ψ : ℝ → E} (h0 : (0:ℝ) ∈ Set.Icc α β)
    (h : ∀ s ∈ Set.Icc α β, φ s = ψ s)
    (hφ : DifferentiableAt ℝ φ 0) (hψ : DifferentiableAt ℝ ψ 0) :
    deriv φ 0 = deriv ψ 0 := by
  have hS : UniqueDiffWithinAt ℝ (Set.Icc α β) (0:ℝ) := (uniqueDiffOn_Icc hαβ) 0 h0
  rw [← hφ.derivWithin hS, ← hψ.derivWithin hS]
  exact derivWithin_congr (fun s hs => h s hs) (h 0 h0)

/-! ## The Euclidean Banach-valued core -/

/-- **Euclidean core, Banach-valued.**  Let `F : E → ℝ` and `G H : E → E'` be differentiable at
`x`, with `F x ∈ [a,b]`, `fderiv F x ≠ 0`, and `G = H` on the band `F ⁻¹' [a,b]`.  Then
`fderiv G x = fderiv H x`.

The band near `x` is a genuine slab when `F x` is in the open interval, and a one-sided half-slab
when `F x = a` or `F x = b`; along a straight line in each direction with `(fderiv F x) u ≠ 0` the
line meets the band on a one-sided interval, and `deriv_eq_of_eqOn_Icc` gives the agreement of the
one-dimensional derivatives. -/
theorem fderiv_eq_of_eventually_eqOn_band {E E' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (F : E → ℝ) (G H : E → E') {a b : ℝ} (hab : a < b) {x : E}
    (hF : HasFDerivAt F (fderiv ℝ F x) x)
    (hG : HasFDerivAt G (fderiv ℝ G x) x) (hH : HasFDerivAt H (fderiv ℝ H x) x)
    (hx : F x ∈ Set.Icc a b) (hreg : fderiv ℝ F x ≠ 0)
    (hGH : ∀ z, F z ∈ Set.Icc a b → G z = H z) :
    fderiv ℝ G x = fderiv ℝ H x := by
  have key_pos : ∀ u : E, 0 < (fderiv ℝ F x) u → (fderiv ℝ G x) u = (fderiv ℝ H x) u := by
    intro u hu
    have hline : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
      have h := ((hasDerivAt_id (0:ℝ)).smul_const u).const_add x
      simpa using h
    have hxline : (fun t : ℝ => x + t • u) 0 = x := by simp
    have hF' : HasFDerivAt F (fderiv ℝ F x) ((fun t : ℝ => x + t • u) 0) := by
      rw [hxline]; exact hF
    have hG' : HasFDerivAt G (fderiv ℝ G x) ((fun t : ℝ => x + t • u) 0) := by
      rw [hxline]; exact hG
    have hH' : HasFDerivAt H (fderiv ℝ H x) ((fun t : ℝ => x + t • u) 0) := by
      rw [hxline]; exact hH
    have hξ : HasDerivAt (fun t : ℝ => F (x + t • u)) ((fderiv ℝ F x) u) 0 :=
      hF'.comp_hasDerivAt 0 hline
    have hρ : HasDerivAt (fun t : ℝ => G (x + t • u)) ((fderiv ℝ G x) u) 0 :=
      hG'.comp_hasDerivAt 0 hline
    have hη : HasDerivAt (fun t : ℝ => H (x + t • u)) ((fderiv ℝ H x) u) 0 :=
      hH'.comp_hasDerivAt 0 hline
    rcases lt_or_eq_of_le hx.2 with hb | hb
    · obtain ⟨δ₀, hδ₀, hδP⟩ := exists_Icc_right_of_eventually
          (eventually_Icc_nhdsGT hξ hu (by simpa using hx.1) (by simpa using hb))
          (by simpa using hx)
      have hmem : ∀ s ∈ Set.Icc (0:ℝ) δ₀,
          (fun t : ℝ => G (x + t • u)) s = (fun t : ℝ => H (x + t • u)) s := by
        intro s hs
        exact hGH _ (hδP s hs)
      have hder := deriv_eq_of_eqOn_Icc hδ₀ ⟨le_refl 0, hδ₀.le⟩ hmem
          hρ.differentiableAt hη.differentiableAt
      rwa [hρ.deriv, hη.deriv] at hder
    · have ha' : a < F (x + (0:ℝ) • u) := by simpa [hb] using hab
      have hb' : F (x + (0:ℝ) • u) ≤ b := by simp [hb]
      obtain ⟨δ₀, hδ₀, hδP⟩ := exists_Icc_left_of_eventually
          (eventually_Icc_nhdsLT hξ hu ha' hb') (by simpa using hx)
      have hmem : ∀ s ∈ Set.Icc (-δ₀) 0,
          (fun t : ℝ => G (x + t • u)) s = (fun t : ℝ => H (x + t • u)) s := by
        intro s hs
        exact hGH _ (hδP s hs)
      have hder := deriv_eq_of_eqOn_Icc (by linarith) ⟨by linarith, le_refl 0⟩ hmem
          hρ.differentiableAt hη.differentiableAt
      rwa [hρ.deriv, hη.deriv] at hder
  have key : ∀ u : E, (fderiv ℝ F x) u ≠ 0 → (fderiv ℝ G x) u = (fderiv ℝ H x) u := by
    intro u hu
    rcases lt_or_gt_of_ne hu with hlt | hgt
    · have h := key_pos (-u) (by rw [map_neg]; exact neg_pos.mpr hlt)
      rwa [map_neg, map_neg, neg_inj] at h
    · exact key_pos u hgt
  let L : E →L[ℝ] E' := (fderiv ℝ G x) - (fderiv ℝ H x)
  have keyL : ∀ u : E, (fderiv ℝ F x) u ≠ 0 → L u = 0 := by
    intro u hu
    show (fderiv ℝ G x) u - (fderiv ℝ H x) u = 0
    rw [sub_eq_zero]
    exact key u hu
  have hL : L = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    show L u = 0
    by_cases hu : (fderiv ℝ F x) u = 0
    · obtain ⟨w, hw⟩ : ∃ w : E, (fderiv ℝ F x) w ≠ 0 := by
        by_contra h
        simp only [not_exists, not_not] at h
        exact hreg (ContinuousLinearMap.ext h)
      have h1 : L (u + w) = 0 := keyL _ (by rw [map_add, hu, zero_add]; exact hw)
      have h2 : L w = 0 := keyL _ hw
      rw [map_add, h2, add_zero] at h1
      exact h1
    · exact keyL u hu
  have : (fderiv ℝ G x) - (fderiv ℝ H x) = 0 := hL
  exact sub_eq_zero.mp this

/-! ## The chart representation of a map into a normed space -/

/-- The manifold derivative of `g : M → E'` at a point of a chart source factors through the
derivative of the chart, the remaining factor being the Fréchet derivative of the chart
representation of `g`. -/
theorem mfderiv_eq_fderiv_chartRep {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : M → E') (p : M) (hg : MDifferentiableAt (𝓡 n) 𝓘(ℝ,E') g p) :
    mfderiv (𝓡 n) 𝓘(ℝ,E') g p =
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        g ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y))
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) p)) ∘L
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) p := by
  have hpsrc : p ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source := mem_chart_source _ p
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) p :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hpsrc
  have hcs : MDifferentiableAt (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas _ _)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).map_source hpsrc)
  have hgr : MDifferentiableAt (𝓡 n) 𝓘(ℝ,E')
      (fun y : EuclideanSpace ℝ (Fin n) => g ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y))
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) :=
    MDifferentiableAt.comp_of_eq ((chartAt (EuclideanSpace ℝ (Fin n)) p) p) hg hcs
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv hpsrc)
  have hcomp := mfderiv_comp p hgr hc
  have heq : mfderiv (𝓡 n) 𝓘(ℝ,E')
      ((fun y : EuclideanSpace ℝ (Fin n) => g ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y))
        ∘ (chartAt (EuclideanSpace ℝ (Fin n)) p)) p = mfderiv (𝓡 n) 𝓘(ℝ,E') g p := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds hpsrc] with y hy
    simp only [Function.comp_apply]
    rw [OpenPartialHomeomorph.left_inv _ hy]
  rw [← heq, hcomp]
  conv_lhs => rw [mfderiv_eq_fderiv]
  rfl

/-! ## The manifold statement for maps into a normed space -/

/-- The band-regularity statement for maps into a normed space `E'`: two maps that agree on the
band `f ⁻¹' [a,b]` have the same derivative at a regular point of the band. -/
theorem mfderiv_eq_of_eqOn_band_normed {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (f : M → ℝ) {a b : ℝ} (hab : a < b) {x : M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (g h : M → E') (hg : MDifferentiableAt (𝓡 n) 𝓘(ℝ,E') g x)
    (hh : MDifferentiableAt (𝓡 n) 𝓘(ℝ,E') h x)
    (hx : f x ∈ Set.Icc a b) (hreg : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0)
    (hgh : ∀ z : M, f z ∈ Set.Icc a b → g z = h z) :
    mfderiv (𝓡 n) 𝓘(ℝ,E') g x = mfderiv (𝓡 n) 𝓘(ℝ,E') h x := by
  have hφsrc : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := mem_chart_source _ x
  let F : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => f ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm y)
  let G' : EuclideanSpace ℝ (Fin n) → E' :=
    fun y => g ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm y)
  let H' : EuclideanSpace ℝ (Fin n) → E' :=
    fun y => h ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm y)
  have hx' : F ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) ∈ Set.Icc a b := by
    simpa [F, (chartAt (EuclideanSpace ℝ (Fin n)) x).left_inv hφsrc] using hx
  have hFdiff : MDifferentiableAt (𝓡 n) 𝓘(ℝ,ℝ) F
      ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) :=
    MDifferentiableAt.comp_of_eq ((chartAt (EuclideanSpace ℝ (Fin n)) x) x)
      ((hf x).mdifferentiableAt (by simp))
      (mdifferentiableAt_atlas_symm (chart_mem_atlas _ _)
        ((chartAt (EuclideanSpace ℝ (Fin n)) x).map_source hφsrc))
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).left_inv hφsrc)
  have hGdiff : MDifferentiableAt (𝓡 n) 𝓘(ℝ,E') G'
      ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) :=
    MDifferentiableAt.comp_of_eq ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) hg
      (mdifferentiableAt_atlas_symm (chart_mem_atlas _ _)
        ((chartAt (EuclideanSpace ℝ (Fin n)) x).map_source hφsrc))
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).left_inv hφsrc)
  have hHdiff : MDifferentiableAt (𝓡 n) 𝓘(ℝ,E') H'
      ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) :=
    MDifferentiableAt.comp_of_eq ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) hh
      (mdifferentiableAt_atlas_symm (chart_mem_atlas _ _)
        ((chartAt (EuclideanSpace ℝ (Fin n)) x).map_source hφsrc))
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).left_inv hφsrc)
  have hGH' : ∀ z, F z ∈ Set.Icc a b → G' z = H' z :=
    fun z hz => hgh _ hz
  have hFdec := mfderiv_chartRep_eq f hf x x hφsrc
  have hGdec := mfderiv_eq_fderiv_chartRep g x hg
  have hHdec := mfderiv_eq_fderiv_chartRep h x hh
  have hreg' : fderiv ℝ F ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) ≠ 0 := by
    intro h0
    apply hreg
    rw [hFdec]
    apply ContinuousLinearMap.ext
    intro v
    show (fderiv ℝ F ((chartAt (EuclideanSpace ℝ (Fin n)) x) x))
        ((mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) x) x) v) = 0
    rw [h0]
    rfl
  have hcore := fderiv_eq_of_eventually_eqOn_band F G' H' hab
      hFdiff.differentiableAt.hasFDerivAt hGdiff.differentiableAt.hasFDerivAt
      hHdiff.differentiableAt.hasFDerivAt hx' hreg' hGH'
  rw [hGdec, hHdec, hcore]

/-! ## The target statement -/

theorem mfderiv_eq_of_eqOn_band {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → ℝ) {a b : ℝ} (hab : a < b) {x : M}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (G H : M → M) (hG : ContMDiff (𝓡 n) (𝓡 n) ∞ G) (hH : ContMDiff (𝓡 n) (𝓡 n) ∞ H)
    (hx : f x ∈ Set.Icc a b) (hreg : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0)
    (hGH : ∀ z : M, f z ∈ Set.Icc a b → G z = H z) :
    mfderiv (𝓡 n) (𝓡 n) G x = mfderiv (𝓡 n) (𝓡 n) H x := by
  have hGx : G x = H x := hGH x hx
  have hGsm : MDifferentiableAt (𝓡 n) (𝓡 n) G x := (hG x).mdifferentiableAt (by simp)
  have hHsm : MDifferentiableAt (𝓡 n) (𝓡 n) H x := (hH x).mdifferentiableAt (by simp)
  have hψsm : MDifferentiableAt (𝓡 n) (𝓡 n)
      (chartAt (EuclideanSpace ℝ (Fin n)) (G x)) (G x) :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) (mem_chart_source _ _)
  have hψG : MDifferentiableAt (𝓡 n) (𝓡 n)
      ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ G) x :=
    MDifferentiableAt.comp_of_eq x hψsm hGsm rfl
  have hψH : MDifferentiableAt (𝓡 n) (𝓡 n)
      ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ H) x := by
    have hψsm' : MDifferentiableAt (𝓡 n) (𝓡 n)
        (chartAt (EuclideanSpace ℝ (Fin n)) (G x)) (H x) := by
      rw [← hGx]; exact hψsm
    exact MDifferentiableAt.comp_of_eq x hψsm' hHsm rfl
  have hinner := mfderiv_eq_of_eqOn_band_normed (n := n) (M := M) f hab hf
      ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ G)
      ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ H) hψG hψH hx hreg
      (fun z hz => by
        simp only [Function.comp_apply]
        rw [hGH z hz])
  have hinner' : mfderiv (𝓡 n) (𝓡 n)
        ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ G) x
      = mfderiv (𝓡 n) (𝓡 n)
        ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ H) x := hinner
  have houtG : mfderiv (𝓡 n) (𝓡 n) G x =
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) (G x)).symm
        (((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ G) x) ∘L
      mfderiv (𝓡 n) (𝓡 n) ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ G) x := by
    have hsrcG : G x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (G x)).source :=
      mem_chart_source _ _
    have hsymm : MDifferentiableAt (𝓡 n) (𝓡 n)
        (chartAt (EuclideanSpace ℝ (Fin n)) (G x)).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) (G x)) :=
      mdifferentiableAt_atlas_symm (chart_mem_atlas _ _)
        ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)).map_source hsrcG)
    have hcomp := mfderiv_comp x hsymm hψG
    have heq : mfderiv (𝓡 n) (𝓡 n)
        ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)).symm
          ∘ ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ G)) x
        = mfderiv (𝓡 n) (𝓡 n) G x := by
      apply Filter.EventuallyEq.mfderiv_eq
      filter_upwards [hGsm.continuousAt.eventually
        ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)).open_source.mem_nhds hsrcG)] with y hy
      simp only [Function.comp_apply]
      exact (chartAt (EuclideanSpace ℝ (Fin n)) (G x)).left_inv hy
    rw [← heq]
    exact hcomp
  have houtH : mfderiv (𝓡 n) (𝓡 n) H x =
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) (G x)).symm
        (((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ H) x) ∘L
      mfderiv (𝓡 n) (𝓡 n) ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ H) x := by
    have hsrcH : H x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (G x)).source := by
      rw [← hGx]; exact mem_chart_source _ _
    have hsymmH : MDifferentiableAt (𝓡 n) (𝓡 n)
        (chartAt (EuclideanSpace ℝ (Fin n)) (G x)).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) (H x)) :=
      mdifferentiableAt_atlas_symm (chart_mem_atlas _ _)
        ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)).map_source hsrcH)
    have hcomp := mfderiv_comp x hsymmH hψH
    have heq : mfderiv (𝓡 n) (𝓡 n)
        ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)).symm
          ∘ ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ H)) x
        = mfderiv (𝓡 n) (𝓡 n) H x := by
      apply Filter.EventuallyEq.mfderiv_eq
      filter_upwards [hHsm.continuousAt.eventually
        ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)).open_source.mem_nhds hsrcH)] with y hy
      simp only [Function.comp_apply]
      exact (chartAt (EuclideanSpace ℝ (Fin n)) (G x)).left_inv hy
    rw [← heq]
    exact hcomp
  have hp : ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ G) x
          = ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ H) x := by
    simp only [Function.comp_apply]
    exact congrArg (chartAt (EuclideanSpace ℝ (Fin n)) (G x)) hGx
  have hA : mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) (G x)).symm
        (((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ G) x)
      = mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) (G x)).symm
        (((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ H) x) := by
    rw [hp]
  rw [houtG, houtH]
  exact (congrArg (fun L => mfderiv (𝓡 n) (𝓡 n)
          (chartAt (EuclideanSpace ℝ (Fin n)) (G x)).symm
          (((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ G) x) ∘L L) hinner').trans
        (congrArg (fun A => A ∘L mfderiv (𝓡 n) (𝓡 n)
          ((chartAt (EuclideanSpace ℝ (Fin n)) (G x)) ∘ H) x) hA)

end Work.Drive.N2
