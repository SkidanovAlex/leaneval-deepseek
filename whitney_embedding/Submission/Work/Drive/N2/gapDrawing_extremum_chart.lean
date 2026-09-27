import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.ModelDefs
import Submission.Work.Drive.N2.exists_contMDiff_bump_tsupport

/-!
# The extremum gap: drawing a level set of a chart model around an extremum

This file proves `Work.Drive.N2.gapDrawing_extremum_chart`, the *chart-local* form of the
"extremum gap" of the movie construction for the compact `n = 2` case (see
`NOTES_classify_route_and_the_gap.md`, §13, item (B)).

`f` is the height function, modelled on the chart `φ` around an extremum as
`f y = c₀ + s * ((φ y 0)^2 + (φ y 1)^2)` with `s = ±1`; the band `f ∈ [c₀ - η, c₀ + η]` is contained
in the source of `φ`, so inside the band the level sets of `f` are the `φ`-preimages of circles
about `0`.  The drawing is then simply the chart model reading `g y = χ y • ι (φ y)`, where
`ι : ℝ² → ℝ³` is the inclusion of the first two coordinates and `χ` is a smooth bump which is `1`
on an open neighbourhood `V` of the band and whose closed support lies in `φ.source`.

* off the closed support of `χ` the map `g` vanishes, so it is smooth there;
* on `φ.source` it is a product of smooth maps, so it is smooth there;
* on `V`, `g = ι ∘ φ`, so `mfderiv g x = ι ∘ mfderiv φ x`; `mfderiv φ x` is injective because `φ`
  is a local diffeomorphism (`hφsm` + `hφsymm`), and `ι` is injective, giving the immersion clause
  `ker (df) ⊓ ker (dg) = 0` (in fact `ker (dg) = 0` there);
* on the band `g = ι ∘ φ`, so `f x = f y` and `g x = g y` force `φ x = φ y` (same `f`-value means
  both points lie on the same circle, but even `g x = g y` alone forces `ι (φ x) = ι (φ y)`, hence
  `φ x = φ y` by injectivity of `ι`), whence `x = y` by injectivity of `φ`.
-/

open scoped Manifold ContDiff Topology
open Filter

namespace Work.Drive.N2

/-- The coordinates of the inclusion `incl23 : ℝ² → ℝ³`. -/
private theorem incl23_apply_val (y : EuclideanSpace ℝ (Fin 2)) (j : Fin 3) :
    incl23 y j = if h : (j : ℕ) < 2 then y ⟨j, h⟩ else 0 := by
  fin_cases j <;> simp [incl23, WithLp.linearEquiv_symm_apply]

private theorem incl23_apply_cast (y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    incl23 y (Fin.castLE (by norm_num : 2 ≤ 3) i) = y i := by
  rw [incl23_apply_val]
  rw [dif_pos (by rw [Fin.val_castLE]; exact i.isLt)]
  exact congrArg y (Fin.ext (by rw [Fin.val_castLE]))

/-- The coordinate inclusion `incl23 : ℝ² → ℝ³` is injective. -/
theorem incl23_inj :
    Function.Injective (incl23 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) := by
  intro y z h
  ext i
  have h2 : incl23 y (Fin.castLE (by norm_num : 2 ≤ 3) i)
      = incl23 z (Fin.castLE (by norm_num : 2 ≤ 3) i) := by rw [h]
  rwa [incl23_apply_cast, incl23_apply_cast] at h2

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- **The differential of a local chart of the manifold is injective.**  If `φ` is an open partial
homeomorphism from `M` to `ℝ²` which is smooth on its source and whose inverse is smooth on its
target, then its manifold derivative at a point of the source is injective (differentiate
`φ.symm ∘ φ = id`). -/
theorem mfderiv_chart_injective {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))}
    (hφsm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞ (fun y : M => φ y) φ.source)
    (hφsymm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞
      (fun z : EuclideanSpace ℝ (Fin 2) => φ.symm z) φ.target)
    {y : M} (hy : y ∈ φ.source) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 2) (fun z : M => φ z) y) := by
  intro v w hvw
  have hdy : MDifferentiableAt (𝓡 2) (𝓡 2) (fun z : M => φ z) y :=
    (hφsm.contMDiffAt (φ.open_source.mem_nhds hy)).mdifferentiableAt (by norm_num)
  have hdy' : MDifferentiableAt (𝓡 2) (𝓡 2)
      (fun t : EuclideanSpace ℝ (Fin 2) => φ.symm t) (φ y) :=
    (hφsymm.contMDiffAt (φ.open_target.mem_nhds (φ.map_source hy))).mdifferentiableAt (by norm_num)
  have hev : (fun z : M => φ.symm (φ z)) =ᶠ[𝓝 y] id := by
    filter_upwards [φ.open_source.mem_nhds hy] with z hz
    exact φ.left_inv hz
  have hid : mfderiv (𝓡 2) (𝓡 2) (fun z : M => φ.symm (φ z)) y
      = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 2) y) := by
    rw [Filter.EventuallyEq.mfderiv_eq hev]
    exact mfderiv_id
  have hcomp : mfderiv (𝓡 2) (𝓡 2) (fun z : M => φ.symm (φ z)) y
      = (mfderiv (𝓡 2) (𝓡 2) (fun t : EuclideanSpace ℝ (Fin 2) => φ.symm t) (φ y)).comp
        (mfderiv (𝓡 2) (𝓡 2) (fun z : M => φ z) y) :=
    mfderiv_comp (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 2)
      (f := fun z : M => φ z) (g := fun t : EuclideanSpace ℝ (Fin 2) => φ.symm t)
      (x := y) hdy' hdy
  have hkey : ∀ t : TangentSpace (𝓡 2) y,
      t = (mfderiv (𝓡 2) (𝓡 2) (fun s : EuclideanSpace ℝ (Fin 2) => φ.symm s) (φ y))
        ((mfderiv (𝓡 2) (𝓡 2) (fun z : M => φ z) y) t) := by
    intro t
    have h1 : (mfderiv (𝓡 2) (𝓡 2) (fun z : M => φ.symm (φ z)) y) t = t := by rw [hid]; rfl
    have h2 : (mfderiv (𝓡 2) (𝓡 2) (fun z : M => φ.symm (φ z)) y) t
        = (mfderiv (𝓡 2) (𝓡 2) (fun s : EuclideanSpace ℝ (Fin 2) => φ.symm s) (φ y))
            ((mfderiv (𝓡 2) (𝓡 2) (fun z : M => φ z) y) t) := by
      rw [hcomp]; rfl
    exact h1.symm.trans h2
  rw [hkey v, hvw, ← hkey w]

/-- **The chain rule for the chart composed with the coordinate inclusion.** -/
theorem mfderiv_incl23_comp {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))}
    (hφsm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ∞ (fun y : M => φ y) φ.source)
    {y : M} (hy : y ∈ φ.source) (t : TangentSpace (𝓡 2) y) :
    mfderiv (𝓡 2) (𝓡 3) (fun z : M => incl23 (φ z)) y t
      = incl23 ((mfderiv (𝓡 2) (𝓡 2) (fun z : M => φ z) y) t) := by
  have hmdg : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun s : EuclideanSpace ℝ (Fin 2) => incl23 s) (φ y) :=
    ContinuousLinearMap.mdifferentiableAt incl23
  have hmdφ : MDifferentiableAt (𝓡 2) (𝓡 2) (fun z : M => φ z) y :=
    (hφsm.contMDiffAt (φ.open_source.mem_nhds hy)).mdifferentiableAt (by norm_num)
  have hc := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 3)
    (f := fun z : M => φ z)
    (g := fun s : EuclideanSpace ℝ (Fin 2) => incl23 s)
    (x := y) hmdg hmdφ t
  rw [ContinuousLinearMap.mfderiv_eq] at hc
  exact hc

end Work.Drive.N2

namespace Work.Drive.N2

open scoped Manifold ContDiff
open Filter Topology

theorem gapDrawing_extremum_chart {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (c₀ η s : ℝ) (hη : 0 < η) (hs : s = 1 ∨ s = -1)
    (hφsm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => φ y) φ.source)
    (hφsymm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => φ.symm z) φ.target)
    (hmodel : ∀ y : M, y ∈ φ.source → f y = c₀ + s * ((φ y 0) ^ 2 + (φ y 1) ^ 2))
    (hinside : ∀ y : M, f y ∈ Set.Icc (c₀ - η) (c₀ + η) → y ∈ φ.source) :
    ∃ g : M → EuclideanSpace ℝ (Fin 3),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      (∀ x : M, f x ∈ Set.Icc (c₀ - η) (c₀ + η) →
        ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) x,
          mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ ℝ) f x v = 0 →
          mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) g x v = 0 → v = 0) ∧
      (∀ x y : M, f x ∈ Set.Icc (c₀ - η) (c₀ + η) → f x = f y → g x = g y → x = y) := by
  classical
  -- the band `K` is compact and contained in the source of the chart
  have hK : IsCompact (f ⁻¹' (Set.Icc (c₀ - η) (c₀ + η))) :=
    (isClosed_Icc.preimage hf.continuous).isCompact
  have hKU : f ⁻¹' (Set.Icc (c₀ - η) (c₀ + η)) ⊆ φ.source := fun y hy => hinside y hy
  -- a smooth bump which is `1` on an open neighbourhood `V` of `K`, with closed support in the chart
  obtain ⟨χ, V, hχsm, hχsupp, hVopen, hKV, hχV, _hχbd⟩ :=
    exists_contMDiff_bump_tsupport (K := f ⁻¹' (Set.Icc (c₀ - η) (c₀ + η)))
      (U := φ.source) hK φ.open_source hKU
  refine ⟨fun y : M => χ y • incl23 (φ y), ?_, ?_, ?_⟩
  · -- smoothness, pointwise
    intro y
    by_cases hy : y ∈ φ.source
    · have hχat : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ y := hχsm y
      have hφat : ContMDiffAt (𝓡 2) (𝓡 2) ∞ (fun z : M => φ z) y :=
        hφsm.contMDiffAt (φ.open_source.mem_nhds hy)
      have hvat : ContMDiffAt (𝓡 2) (𝓡 3) ∞ (fun z : M => incl23 (φ z)) y :=
        (incl23.contMDiffAt (x := φ y)).comp y hφat
      exact hχat.smul hvat
    · have hymem : y ∈ (tsupport χ)ᶜ := fun hc => hy (hχsupp hc)
      have hzero : ∀ z ∈ (tsupport χ)ᶜ, χ z = 0 := by
        intro z hz
        by_contra h
        exact hz (subset_tsupport χ h)
      have hev : (fun z : M => χ z • incl23 (φ z))
          =ᶠ[𝓝 y] (fun _ : M => (0 : EuclideanSpace ℝ (Fin 3))) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hymem] with z hz
        simp only [hzero z hz, zero_smul]
      exact (Filter.EventuallyEq.contMDiffAt_iff hev).mpr contMDiffAt_const
  · -- the immersion clause
    intro x hx v _hdf hdg
    have hxV : x ∈ V := hKV hx
    have hxsrc : x ∈ φ.source := hKU hx
    have hev : (fun z : M => χ z • incl23 (φ z)) =ᶠ[𝓝 x] (fun z : M => incl23 (φ z)) := by
      filter_upwards [hVopen.mem_nhds hxV] with z hz
      simp only [hχV z hz, one_smul]
    have hflat : mfderiv (𝓡 2) (𝓡 3) (fun z : M => incl23 (φ z)) x v = 0 :=
      Eq.mp (congrArg (fun (L : TangentSpace (𝓡 2) x →L[ℝ] EuclideanSpace ℝ (Fin 3)) =>
        (L v = 0)) (Filter.EventuallyEq.mfderiv_eq hev)) hdg
    have hkey : incl23 ((mfderiv (𝓡 2) (𝓡 2) (fun z : M => φ z) x) v) = 0 :=
      (mfderiv_incl23_comp hφsm hxsrc v).symm.trans hflat
    have hfv : mfderiv (𝓡 2) (𝓡 2) (fun z : M => φ z) x v = 0 :=
      incl23_inj (hkey.trans (map_zero (incl23 : EuclideanSpace ℝ (Fin 2) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))).symm)
    exact mfderiv_chart_injective hφsm hφsymm hxsrc (by rw [hfv, map_zero])
  · -- injectivity on the level sets
    intro x y hx hfxy hgxy
    have hyband : y ∈ f ⁻¹' (Set.Icc (c₀ - η) (c₀ + η)) := by
      rw [Set.mem_preimage, ← hfxy]; exact hx
    have hxV : x ∈ V := hKV hx
    have hyV : y ∈ V := hKV hyband
    have hxsrc : x ∈ φ.source := hKU hx
    have hysrc : y ∈ φ.source := hKU hyband
    have h1 : incl23 (φ x) = incl23 (φ y) := by
      have hx' : χ x • incl23 (φ x) = incl23 (φ x) := by rw [hχV x hxV, one_smul]
      have hy' : χ y • incl23 (φ y) = incl23 (φ y) := by rw [hχV y hyV, one_smul]
      rw [← hx', ← hy']
      exact hgxy
    exact φ.injOn hxsrc hysrc (incl23_inj h1)

end Work.Drive.N2
