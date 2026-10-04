import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Submission.Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_congr_of_eventuallyEq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Geometry.Manifold.LocalDiffeomorph

open scoped _root_.Manifold _root_.ContDiff
open Filter Set
open scoped Topology

/-- The preferred extended chart at an interior point of a manifold is a `C^∞` local
diffeomorphism there, from the manifold `M` to the model space `E` endowed with the trivial model
with corners `𝓘(𝕜, E)`.  (`∞`-smooth version of the analytic statement.) -/
private theorem isLocalDiffeomorphAt_infty_extChartAt
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {x : M} (hx : I.IsInteriorPoint x) :
    IsLocalDiffeomorphAt I 𝓘(𝕜, E) ∞ (extChartAt I x) x := by
  let e := extChartAt I x
  let U : Set M := e.source ∩ e ⁻¹' interior (range I)
  have hU_open : IsOpen U :=
    (continuousOn_extChartAt x).isOpen_inter_preimage (isOpen_extChartAt_source x) isOpen_interior
  have hxU : x ∈ U := ⟨mem_extChartAt_source x, hx⟩
  have hV_open : IsOpen (e '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨u, hu, rfl⟩
    exact extChartAt_image_nhds_mem_nhds_of_mem_interior_range hu.1 hu.2
      (hU_open.mem_nhds hu)
  refine ⟨{ toPartialEquiv :=
              { toFun := e
                invFun := e.symm
                source := U
                target := e '' U
                map_source' := fun y hy => ⟨y, hy, rfl⟩
                map_target' := fun z hz => by
                  obtain ⟨y, hy, rfl⟩ := hz
                  rw [e.left_inv hy.1]
                  exact hy
                left_inv' := fun y hy => e.left_inv hy.1
                right_inv' := fun z hz => by
                  obtain ⟨y, hy, rfl⟩ := hz
                  exact e.right_inv (e.map_source hy.1) }
            open_source := hU_open
            open_target := hV_open
            contMDiffOn_toFun :=
              (contMDiffOn_extChartAt (I := I) (x := x)).mono (t := U) (fun y hy => by
                rw [← extChartAt_source I]
                exact hy.1)
            contMDiffOn_invFun :=
              (contMDiffOn_extChartAt_symm (I := I) (x := x)).mono (t := e '' U) (fun z hz => by
                obtain ⟨y, hy, rfl⟩ := hz
                exact e.map_source hy.1) }, hxU, fun y hy => rfl⟩

/-- The inverse of the preferred extended chart at an interior point of a manifold is a `C^∞` local
diffeomorphism at the image point, from the model space `E` (with the trivial model with corners
`𝓘(𝕜, E)`) to the manifold `M`. -/
private theorem isLocalDiffeomorphAt_infty_extChartAt_symm
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {x : M} (hx : I.IsInteriorPoint x) :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) I ∞ (extChartAt I x).symm (extChartAt I x x) := by
  let e : PartialEquiv M E := extChartAt I x
  let s : Set E := interior (range I) ∩ I.symm ⁻¹' (chartAt H x).target
  let t : Set M := e.symm '' s
  have hsymm : I.symm (e x) = (chartAt H x) x := by
    change I.symm (I ((chartAt H x) x)) = (chartAt H x) x
    rw [ModelWithCorners.left_inv]
  have hz : e x ∈ s := by
    change e x ∈ interior (range I) ∩ I.symm ⁻¹' (chartAt H x).target
    refine ⟨?_, ?_⟩
    · exact hx
    · change I.symm (e x) ∈ (chartAt H x).target
      rw [hsymm]; exact mem_chart_target H x
  have hs_sub : s ⊆ e.target := by
    intro y hy
    change y ∈ (extChartAt I x).target
    rw [extChartAt_target]
    exact ⟨hy.2, interior_subset hy.1⟩
  have ht_sub : t ⊆ e.source := by
    change e.symm '' s ⊆ e.source
    calc e.symm '' s ⊆ e.symm '' e.target := image_mono hs_sub
      _ = e.source := e.symm_image_target_eq_source
  have ht_open : IsOpen t := by
    have hI : I.symm '' interior (range I) = I ⁻¹' interior (range I) := by
      have h := PartialEquiv.symm_image_eq_source_inter_preimage (e := I.toPartialEquiv)
        (s := interior (range I)) (by
          rw [ModelWithCorners.target_eq]; exact interior_subset)
      simpa [ModelWithCorners.source_eq] using h
    have hU : I.symm '' s = I ⁻¹' interior (range I) ∩ (chartAt H x).target := by
      change I.symm '' (interior (range I) ∩ I.symm ⁻¹' (chartAt H x).target) = _
      rw [Set.image_inter_preimage, hI]
    have hc : ⇑e.symm = (chartAt H x).symm ∘ I.symm := (extChartAt_coe_symm x).symm
    have hcomp : (chartAt H x).symm '' (I.symm '' s) = t := by
      rw [← Set.image_comp, ← hc]
    rw [← hcomp]
    refine (chartAt H x).symm.isOpen_image_of_subset_source ?_ ?_
    · rw [hU]
      exact (I.continuous.isOpen_preimage _ isOpen_interior).inter (chartAt H x).open_target
    · rw [hU]; exact inter_subset_right
  refine ⟨{ toPartialEquiv :=
              { toFun := e.symm
                invFun := e
                source := s
                target := t
                map_source' := fun y hy => ⟨y, hy, rfl⟩
                map_target' := fun y hy => by
                  obtain ⟨y', hy', rfl⟩ := hy
                  rw [e.right_inv (hs_sub hy')]
                  exact hy'
                left_inv' := fun y hy => e.right_inv (hs_sub hy)
                right_inv' := fun y hy => by
                  obtain ⟨y', hy', rfl⟩ := hy
                  rw [e.right_inv (hs_sub hy')] },
            open_source := by
              change IsOpen (interior (range I) ∩ I.symm ⁻¹' (chartAt H x).target)
              exact isOpen_interior.inter
                (I.continuous_symm.isOpen_preimage _ (chartAt H x).open_target)
            open_target := ht_open,
            contMDiffOn_toFun := by
              exact (contMDiffOn_extChartAt_symm (I := I) x).mono hs_sub
            contMDiffOn_invFun := by
              refine (contMDiffOn_extChartAt (I := I) (x := x)).mono ?_
              intro y hy
              have h := ht_sub hy
              change y ∈ (extChartAt I x).source at h
              rwa [extChartAt_source] at h },
          hz, fun y _ => rfl⟩


/-- **Inverse function theorem, model space case, `C^∞` version with local smoothness.**
If `g : E → E'` is `C^∞` on a neighbourhood `u` of `a` and `fderiv 𝕜 g a` is invertible, then `g`
is a `C^∞` local diffeomorphism at `a`. -/
private theorem isLocalDiffeomorphAt_infty_of_contDiffOn_of_isInvertible
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
    {g : E → E'} {a : E} {u : Set E} (hu : u ∈ 𝓝 a)
    (hg : ContDiffOn 𝕜 ∞ g u)
    (h : (fderiv 𝕜 g a).IsInvertible) :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E') ∞ g a := by
  obtain ⟨V, hVu, hVopen, haV⟩ := mem_nhds_iff.mp hu
  have hgV : ContDiffOn 𝕜 ∞ g V := hg.mono hVu
  have ha : ContDiffAt 𝕜 ∞ g a := hgV.contDiffAt (hVopen.mem_nhds haV)
  obtain ⟨e, he⟩ := h
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hd : HasFDerivAt g (e : E →L[𝕜] E') a := by
    have h1 : HasFDerivAt g (fderiv 𝕜 g a) a := (ha.differentiableAt hn).hasFDerivAt
    rwa [← he] at h1
  set Ψ : OpenPartialHomeomorph E E' := ha.toOpenPartialHomeomorph g hd hn with hΨdef
  have hΨcoe : (Ψ : E → E') = g := ContDiffAt.toOpenPartialHomeomorph_coe ha hd hn
  have haΨ : a ∈ Ψ.source := ContDiffAt.mem_toOpenPartialHomeomorph_source ha hd hn
  -- The Fréchet derivative stays invertible on a neighbourhood of `a`.
  have hcont : ContinuousAt (fderiv 𝕜 g) a :=
    (hgV.continuousOn_fderiv_of_isOpen hVopen (by simp : (1 : ℕ∞ω) ≤ ∞)).continuousAt
      (hVopen.mem_nhds haV)
  have hUnhds : {S : E →L[𝕜] E' | S.IsInvertible} ∈ 𝓝 (fderiv 𝕜 g a) := by
    have hche := ContinuousLinearEquiv.nhds e
    have hset : {S : E →L[𝕜] E' | S.IsInvertible}
        = range (ContinuousLinearEquiv.toContinuousLinearMap :
            (E ≃L[𝕜] E') → (E →L[𝕜] E')) := by
      ext S
      exact ⟨fun ⟨A, hA⟩ => ⟨A, hA⟩, fun ⟨A, hA⟩ => ⟨A, hA⟩⟩
    rw [← hset] at hche
    rwa [he] at hche
  have hinv_nhds : {x : E | (fderiv 𝕜 g x).IsInvertible} ∈ 𝓝 a :=
    hcont.preimage_mem_nhds hUnhds
  have hS_nhds : (V ∩ Ψ.source ∩ {x : E | (fderiv 𝕜 g x).IsInvertible}) ∈ 𝓝 a :=
    inter_mem (inter_mem (hVopen.mem_nhds haV) (Ψ.open_source.mem_nhds haΨ)) hinv_nhds
  obtain ⟨s, hs_sub, hs_open, has⟩ := mem_nhds_iff.mp hS_nhds
  have hsV : s ⊆ V := fun x hx => (hs_sub hx).1.1
  have hsΨ : s ⊆ Ψ.source := fun x hx => (hs_sub hx).1.2
  have hsInv : ∀ x ∈ s, (fderiv 𝕜 g x).IsInvertible := fun x hx => (hs_sub hx).2
  refine ⟨{ toFun := g
            invFun := Ψ.symm
            source := s
            target := g '' s
            map_source' := fun x hx => ⟨x, hx, rfl⟩
            map_target' := fun y hy => by
              obtain ⟨x, hx, rfl⟩ := hy
              rw [← hΨcoe, Ψ.left_inv (hsΨ hx)]
              exact hx
            left_inv' := fun x hx => by
              rw [← hΨcoe]
              exact Ψ.left_inv (hsΨ hx)
            right_inv' := fun y hy => by
              obtain ⟨x, hx, rfl⟩ := hy
              rw [← hΨcoe]
              exact Ψ.right_inv (Ψ.map_source (hsΨ hx))
            open_source := hs_open
            open_target := by
              rw [← hΨcoe]
              exact Ψ.isOpen_image_of_subset_source hs_open hsΨ
            contMDiffOn_toFun :=
              contMDiffOn_iff_contDiffOn.mpr (hgV.mono hsV)
            contMDiffOn_invFun := by
              rw [contMDiffOn_iff_contDiffOn]
              intro y hy
              obtain ⟨x, hx, rfl⟩ := hy
              have hxV : x ∈ V := hsV hx
              have hxΨ : x ∈ Ψ.source := hsΨ hx
              have hsymm : Ψ.symm (g x) = x := by
                rw [← hΨcoe]
                exact Ψ.left_inv hxΨ
              have hyt : g x ∈ Ψ.target := by
                rw [← hΨcoe]
                exact Ψ.map_source hxΨ
              obtain ⟨ex, hex⟩ := hsInv x hx
              have hgx : ContDiffAt 𝕜 ∞ g x := hgV.contDiffAt (hVopen.mem_nhds hxV)
              have hΨx : ContDiffAt 𝕜 ∞ (Ψ : E → E') x :=
                hgx.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hΨcoe)
              have hf' : HasFDerivAt (Ψ : E → E') (ex : E →L[𝕜] E') x := by
                have h1 : HasFDerivAt g (fderiv 𝕜 g x) x :=
                  (hgx.differentiableAt hn).hasFDerivAt
                rw [← hex] at h1
                exact h1.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hΨcoe)
              exact (Ψ.contDiffAt_symm hyt (by rw [hsymm]; exact hf')
                (by rw [hsymm]; exact hΨx)).contDiffWithinAt },
        has, fun x _ => rfl⟩


/-- **Inverse function theorem, manifold case, `C^∞` version with local smoothness.** -/
theorem isLocalDiffeomorphAt_infty_of_contMDiffOn_of_mfderiv_isInvertible
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold I' ((⊤ : ENat) : WithTop ENat) N]
    {f : M → N} {x : M} {U : Set M} (hU : U ∈ 𝓝 x)
    (hf : ContMDiffOn I I' ((⊤ : ENat) : WithTop ENat) f U)
    (hx : I.IsInteriorPoint x)
    (h : (mfderiv I I' f x).IsInvertible) :
    IsLocalDiffeomorphAt I I' ((⊤ : ENat) : WithTop ENat) f x := by
  have hn : (((⊤ : ENat) : WithTop ENat)) ≠ 0 := by simp
  have hfc : ContMDiffAt I I' ∞ f x := hf.contMDiffAt hU
  -- a small open neighbourhood contained in one chart pair
  have hchart : (chartAt H x).source ∩ f ⁻¹' (chartAt H' (f x)).source ∩ U ∈ 𝓝 x :=
    inter_mem (inter_mem
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
      (hfc.continuousAt.preimage_mem_nhds
        ((chartAt H' (f x)).open_source.mem_nhds (mem_chart_source H' (f x))))) hU
  obtain ⟨s, hs_sub, hs_open, hxs⟩ := mem_nhds_iff.mp hchart
  have hsSrc : s ⊆ (chartAt H x).source := fun y hy => (hs_sub hy).1.1
  have hsTgt : MapsTo f s (chartAt H' (f x)).source := fun y hy => (hs_sub hy).1.2
  have hsU : s ⊆ U := fun y hy => (hs_sub hy).2
  set g : E → E' := ⇑(extChartAt I' (f x)) ∘ f ∘ ⇑(extChartAt I x).symm with hg_def
  have hfs : ContMDiffOn I I' ∞ f s := hf.mono hsU
  have hg : ContDiffOn 𝕜 ∞ g (extChartAt I x '' s) := by
    have h' := (contMDiffOn_iff_of_subset_source (I := I) (I' := I') (x := x) (y := f x)
      (s := s) hsSrc hsTgt).mp hfs
    rw [hg_def]
    exact h'.2
  have hw : extChartAt I x '' s ∈ 𝓝 (extChartAt I x x) :=
    extChartAt_image_nhds_mem_nhds_of_mem_interior_range (mem_extChartAt_source x) hx
      (hs_open.mem_nhds hxs)
  have hmd : MDiffAt f x := hfc.mdifferentiableAt hn
  have hgi : (fderiv 𝕜 g (extChartAt I x x)).IsInvertible := by
    have hmf : mfderiv I I' f x = fderiv 𝕜 g ((extChartAt I x) x) := by
      -- v4.34: `MDifferentiableAt.mfderiv` wraps the result in `tangentSpaceCastModel`
      -- casts, which are definitionally the identity.
      rw [hmd.mfderiv, hg_def, fderivWithin_of_mem_nhds (range_mem_nhds_isInteriorPoint hx)]
      all_goals first | rfl | (ext v; rfl)
    exact hmf ▸ h
  have h2 : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E') ∞ g ((extChartAt I x) x) :=
    isLocalDiffeomorphAt_infty_of_contDiffOn_of_isInvertible hw hg hgi
  have hfx : I'.IsInteriorPoint (f x) := by
    refine hmd.isInteriorPoint_of_surjective_mfderiv ?_ hx
    obtain ⟨A, hA⟩ := h
    rw [← hA]
    exact A.surjective
  have h1 : IsLocalDiffeomorphAt I 𝓘(𝕜, E) ∞ (extChartAt I x) x :=
    isLocalDiffeomorphAt_infty_extChartAt hx
  have h3 : IsLocalDiffeomorphAt 𝓘(𝕜, E') I' ∞ (extChartAt I' (f x)).symm
      ((extChartAt I' (f x)) (f x)) :=
    isLocalDiffeomorphAt_infty_extChartAt_symm hfx
  have h12 : IsLocalDiffeomorphAt I 𝓘(𝕜, E') ∞ (g ∘ ⇑(extChartAt I x)) x :=
    IsLocalDiffeomorphAt.comp (K := 𝓘(𝕜, E')) (P := E') h1 h2
  have hpt : (g ∘ ⇑(extChartAt I x)) x = (extChartAt I' (f x)) (f x) := by
    rw [hg_def]
    simp only [Function.comp_apply]
    rw [extChartAt_to_inv x]
  have h3' : IsLocalDiffeomorphAt 𝓘(𝕜, E') I' ∞ (extChartAt I' (f x)).symm
      ((g ∘ ⇑(extChartAt I x)) x) := by
    rw [hpt]
    exact h3
  have h123 : IsLocalDiffeomorphAt I I' ∞
      (⇑(extChartAt I' (f x)).symm ∘ (g ∘ ⇑(extChartAt I x))) x :=
    IsLocalDiffeomorphAt.comp (K := I') (P := N) h12 h3'
  refine isLocalDiffeomorphAt_congr_of_eventuallyEq h123 ?_
  filter_upwards [extChartAt_source_mem_nhds (I := I) x,
    hfc.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I') (f x))]
    with y hyφ hyf
  rw [Function.comp_apply, Function.comp_apply, hg_def]
  simp only [Function.comp_apply]
  rw [PartialEquiv.left_inv _ hyφ]
  exact PartialEquiv.left_inv (extChartAt I' (f x)) hyf

end Commons.Geometry.Manifold.LocalDiffeomorph