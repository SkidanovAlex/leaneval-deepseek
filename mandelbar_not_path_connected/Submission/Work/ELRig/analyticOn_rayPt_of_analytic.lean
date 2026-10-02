import Mathlib
import Submission.Work.Bottcher.All
import Submission.Work.ELTop.Defs
import Submission.Work.ParamRays.DynBottcher
import Submission.Work.ELRig.LocalInverse.exists_analytic_localInverse
import Submission.Work.ELRig.deriv_ne_zero_of_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set Filter Metric
open scoped Topology

/-!
# Real-analyticity of the dynamic rays in the level

This file proves `Work.ELRig.analyticOn_rayPt_of_analytic`: for a dynamical Nakane datum
`hN : Work.EL.DynB c φ` and a Böttcher coordinate `φ` which is analytic on the escape set, the
level-`t` point of the dynamic ray of angle `θ` depends real-analytically on `t` for `t > 1`.

The vehicle is the **inverse Böttcher coordinate** `invBottcher hN`, the plain inverse of the
homeomorphism `hN.e : (K c)ᶜ ≃ₜ exteriorDisc` viewed as a total function on `ℂ`.  Since `φ`
agrees with `hN.e` off the filled Julia set and the filled Julia set is exactly the complement of
the escape set (`mem_EscapeSet_iff_notMem_K`), the points of the exterior disc are precisely the
images off the filled Julia set, and `invBottcher hN` is a right inverse of the injective
analytic map `φ` restricted to the escape set.  The analytic inverse function theorem
(`AnalyticAt.analyticAt_localInverse`) then makes `invBottcher hN` analytic on the exterior disc
(`analyticAt_invBottcher`).  Finally `t ↦ rayPoint θ t = t * exp (2πiθ)` is complex-linear, and
`Work.EL.rayPt hN θ t = invBottcher hN (rayPoint θ t)` for `t > 1`
(`invBottcher_rayPoint`).
-/

/-- The complement of the filled Julia set `K c = Work.ParamRays.filledJulia c` is the escape set
`Work.Bottcher.EscapeSet c = {z | 0 < green c z}`. -/
theorem mem_EscapeSet_iff_notMem_K {c z : ℂ} :
    z ∈ Work.Bottcher.EscapeSet c ↔ z ∉ Work.EL.K c := by
  rw [Work.Bottcher.Contraction.escapeSet_eq_escapingSet, ← Work.ParamRays.compl_filledJulia,
    Set.mem_compl_iff]

/-- Off the filled Julia set, the analytic coordinate `φ` agrees with the Nakane homeomorphism
`hN.e`. -/
theorem phi_eq_e {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {z : ℂ} (hz : z ∉ Work.EL.K c) :
    φ z = ((hN.e ⟨z, hz⟩ : ↥Work.Top.exteriorDisc) : ℂ) := by
  have h1 := hN.he ⟨z, hz⟩
  rwa [Work.EL.dynPhi_of_notMem hz] at h1

/-- `φ` is injective on the escape set: there it agrees with the injective homeomorphism
`hN.e`. -/
theorem injOn_phi {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) :
    Set.InjOn φ (Work.Bottcher.EscapeSet c) := by
  intro z hz z' hz' h
  have hzK : z ∉ Work.EL.K c := (mem_EscapeSet_iff_notMem_K.mp hz)
  have hzK' : z' ∉ Work.EL.K c := (mem_EscapeSet_iff_notMem_K.mp hz')
  have h2 : Work.EL.dynPhi c φ z = Work.EL.dynPhi c φ z' := by
    rw [Work.EL.dynPhi_of_notMem hzK, Work.EL.dynPhi_of_notMem hzK', h]
  exact hN.injOn_Phi hzK hzK' h2

/-- The **inverse Böttcher coordinate**: the inverse of the Nakane homeomorphism, viewed as a
total function on `ℂ` (value `0` inside the closed unit disc). -/
noncomputable def invBottcher {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) : ℂ → ℂ :=
  fun w => if h : 1 < ‖w‖ then ((hN.e.symm ⟨w, h⟩ : ↥(Work.EL.K c)ᶜ) : ℂ) else 0

/-- `invBottcher hN` is a right inverse of `φ` on the exterior disc, with values in the escape
set. -/
theorem invBottcher_spec {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {w : ℂ} (hw : 1 < ‖w‖) :
    invBottcher hN w ∈ Work.Bottcher.EscapeSet c ∧ φ (invBottcher hN w) = w := by
  have hz : ((hN.e.symm ⟨w, hw⟩ : ↥(Work.EL.K c)ᶜ) : ℂ) ∉ Work.EL.K c := (hN.e.symm ⟨w, hw⟩).2
  have hspec : invBottcher hN w = ((hN.e.symm ⟨w, hw⟩ : ↥(Work.EL.K c)ᶜ) : ℂ) := by
    rw [invBottcher, dite_eq_left hw]
  constructor
  · rw [hspec]; exact mem_EscapeSet_iff_notMem_K.mpr hz
  · rw [hspec]
    have h1 : Work.EL.dynPhi c φ ((hN.e.symm ⟨w, hw⟩ : ↥(Work.EL.K c)ᶜ) : ℂ) = w := by
      rw [hN.he, Homeomorph.apply_symm_apply]
    rwa [Work.EL.dynPhi_of_notMem hz] at h1

/-- **The inverse Böttcher coordinate is analytic on the exterior disc.**

At `w₀` in the exterior disc, let `z₀ = invBottcher hN w₀`, so that `φ z₀ = w₀`.  Since `φ` is
analytic and injective on the open escape set, its derivative at `z₀` is nonzero
(`Work.ELRig.deriv_ne_zero_of_injOn`), and the analytic inverse function theorem
(`AnalyticAt.analyticAt_localInverse`) gives an analytic local inverse `g` of `φ` at `z₀`.  For
`w` near `w₀`, both `g w` and `invBottcher hN w` lie in the escape set (continuity, and the
interior of the exterior disc) and are both mapped to `w` by `φ`; injectivity of `φ` on the
escape set therefore gives `g w = invBottcher hN w`. -/
theorem analyticAt_invBottcher {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (han : AnalyticOnNhd ℂ φ (Work.Bottcher.EscapeSet c)) {w₀ : ℂ} (hw₀ : 1 < ‖w₀‖) :
    AnalyticAt ℂ (invBottcher hN) w₀ := by
  have hEopen : IsOpen (Work.Bottcher.EscapeSet c) := Work.Bottcher.Contraction.isOpen_escapeSet c
  have hinj := injOn_phi hN
  have hz₀ : invBottcher hN w₀ ∈ Work.Bottcher.EscapeSet c := (invBottcher_spec hN hw₀).1
  have hφw₀ : φ (invBottcher hN w₀) = w₀ := (invBottcher_spec hN hw₀).2
  have hφat : AnalyticAt ℂ φ (invBottcher hN w₀) := han _ hz₀
  have hd : deriv φ (invBottcher hN w₀) ≠ 0 :=
    Work.ELRig.deriv_ne_zero_of_injOn han.differentiableOn hEopen hinj hz₀
  set g : ℂ → ℂ :=
    hφat.hasStrictDerivAt.localInverse φ (deriv φ (invBottcher hN w₀)) (invBottcher hN w₀) hd
    with hgdef
  have hgan : AnalyticAt ℂ g (φ (invBottcher hN w₀)) :=
    hgdef ▸ hφat.analyticAt_localInverse hd
  have hgφ : g (φ (invBottcher hN w₀)) = invBottcher hN w₀ := by
    have h : ∀ᶠ x : ℂ in 𝓝 (invBottcher hN w₀), g (φ x) = x := by
      simpa [hgdef] using hφat.hasStrictDerivAt.eventually_left_inverse hd
    exact h.self_of_nhds
  have hright : ∀ᶠ w : ℂ in 𝓝 (φ (invBottcher hN w₀)), φ (g w) = w :=
    hgdef ▸ hφat.hasStrictDerivAt.eventually_right_inverse hd
  have hgmem : ∀ᶠ w : ℂ in 𝓝 (φ (invBottcher hN w₀)), g w ∈ Work.Bottcher.EscapeSet c := by
    have hcont : ContinuousAt g (φ (invBottcher hN w₀)) := hgan.continuousAt
    have : Work.Bottcher.EscapeSet c ∈ 𝓝 (g (φ (invBottcher hN w₀))) := by
      rw [hgφ]; exact hEopen.mem_nhds hz₀
    exact hcont.preimage_mem_nhds this
  have hbig : ∀ᶠ w : ℂ in 𝓝 (φ (invBottcher hN w₀)), 1 < ‖w‖ := by
    have hcont : ContinuousAt (fun w : ℂ => ‖w‖) (φ (invBottcher hN w₀)) :=
      continuous_norm.continuousAt
    refine hcont.eventually (isOpen_Ioi.mem_nhds ?_)
    rw [hφw₀]
    exact hw₀
  have huniq : ∀ w : ℂ, 1 < ‖w‖ → ∀ z : ℂ, z ∈ Work.Bottcher.EscapeSet c → φ z = w →
      z = invBottcher hN w := by
    intro w hw z hz hzw
    exact hinj hz (invBottcher_spec hN hw).1 (by rw [hzw, (invBottcher_spec hN hw).2])
  have heq : invBottcher hN =ᶠ[𝓝 (φ (invBottcher hN w₀))] g := by
    filter_upwards [hright, hgmem, hbig] with w hw1 hw2 hw3
    exact (huniq w hw3 (g w) hw2 hw1).symm
  rw [← hφw₀]
  exact hgan.congr heq.symm

/-- The level-`t` point of the dynamic ray of angle `θ` is the inverse Böttcher coordinate of
`rayPoint θ t = t * exp (2πiθ)`, for `t > 1`. -/
theorem invBottcher_rayPoint {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ t : ℝ} (ht : 1 < t) :
    Work.EL.rayPt hN θ t = invBottcher hN (Work.Top.NakaneData.rayPoint θ t) := by
  rw [Work.EL.rayPt, Work.Top.NakaneData.rayPt, dite_eq_left ht, invBottcher,
    dite_eq_left (show 1 < ‖Work.Top.NakaneData.rayPoint θ t‖ from
      Work.Top.NakaneData.rayPoint_mem_exteriorDisc ht)]

/-- **The dynamic ray is real-analytic in the level.**  For a dynamical `NakaneData` `hN` on
`K c` and a Böttcher coordinate `φ` that is analytic on the escape set, the level-`t` point
`Work.EL.rayPt hN θ t` of the dynamic ray of angle `θ` depends real-analytically on `t ∈ (1, ∞)`.

Route.  By definition `Work.EL.rayPt hN θ t = ↑(hN.e.symm (⟨rayPoint θ t, _⟩))` for `t > 1`, and
`t ↦ rayPoint θ t = t * exp (2πiθ)` is complex-linear, hence `ℝ`-analytic
(`Complex.ofRealCLM.analyticAt` + composition).  So it suffices that `e.symm : exteriorDisc →
(K c)ᶜ` (viewed as a function `ℂ → ℂ` by `if h : 1 < ‖w‖ then ↑(hN.e.symm ⟨w,h⟩) else 0`) is
analytic at every `w₀` with `1 < ‖w₀‖`.  Let `z₀ := e.symm w₀`.  Then:

* `φ z₀ = w₀`: `φ` and `dynPhi c φ` agree off `K c`, `dynPhi c φ` agrees with `hN.e` on `(K c)ᶜ`
  (`hN.he`), and `(K c)ᶜ = {z | 0 < Work.Bottcher.green c z}` (via
  `Work.Bottcher.Green.green_pos_iff` and `Work.ParamRays.compl_filledJulia`), so `han` gives
  analyticity of `φ` at `z₀`;
* `φ` is injective on `{z | 0 < Work.Bottcher.green c z}`: if `φ z = φ z'` there, then
  `hN.e ⟨z,_⟩ = hN.e ⟨z',_⟩`, so `z = z'` by injectivity of the homeomorphism;
* hence `deriv φ z₀ ≠ 0` (`Work.ELRig.deriv_ne_zero_of_injOn`, or
  `Work.ELRig.LocalInverse.deriv_ne_zero_of_injOn_ball`) and the analytic inverse function theorem
  (`Work.ELRig.LocalInverse.exists_analytic_localInverse`, in a local version with `AnalyticOnNhd`
  in place of global differentiability: copy that file's proof) yields `σ` analytic near `w₀` with
  `φ (σ z) = z`;
* for `z` near `w₀`, the points `σ z` and `e.symm z` both lie in a small ball around `z₀`
  (continuity, and `σ w₀ = z₀ = e.symm w₀`), where `φ` is injective, and both satisfy `φ · = z`;
  hence `σ z = e.symm z`, and `e.symm` is analytic at `w₀`. -/
theorem analyticOn_rayPt_of_analytic {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (han : AnalyticOnNhd ℂ φ (Work.Bottcher.EscapeSet c)) (θ : ℝ) :
    AnalyticOn ℝ (fun t : ℝ => Work.EL.rayPt hN θ t) (Set.Ioi 1) := by
  have hΨ : AnalyticOnNhd ℂ (invBottcher hN) Work.Top.exteriorDisc :=
    fun w hw => analyticAt_invBottcher hN han (show 1 < ‖w‖ from hw)
  refine (?_ : AnalyticOnNhd ℝ (fun t : ℝ => Work.EL.rayPt hN θ t) (Set.Ioi 1)).analyticOn
  intro t₀ ht₀
  set s : ℂ := Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) with hsdef
  have hray : ∀ t : ℝ, Work.Top.NakaneData.rayPoint θ t = (t : ℂ) * s := by
    intro t
    rw [Work.Top.NakaneData.rayPoint, hsdef]
  have hcomplex : AnalyticAt ℂ (fun u : ℂ => invBottcher hN (u * s)) (t₀ : ℂ) := by
    have h1 : AnalyticAt ℂ (invBottcher hN) ((t₀ : ℂ) * s) := by
      apply hΨ
      rw [← hray t₀]
      exact Work.Top.NakaneData.rayPoint_mem_exteriorDisc ht₀
    have h2 : AnalyticAt ℂ (fun u : ℂ => u * s) (t₀ : ℂ) := analyticAt_id.mul analyticAt_const
    exact AnalyticAt.comp (x := (t₀ : ℂ)) (f := fun u : ℂ => u * s) h1 h2
  have hreal : AnalyticAt ℝ (fun u : ℂ => invBottcher hN (u * s)) (t₀ : ℂ) :=
    hcomplex.restrictScalars
  have hofReal : AnalyticAt ℝ (fun t : ℝ => (t : ℂ)) t₀ := Complex.ofRealCLM.analyticAt t₀
  have hcomp : AnalyticAt ℝ (fun t : ℝ => invBottcher hN ((t : ℂ) * s)) t₀ :=
    AnalyticAt.comp (x := t₀) (f := fun t : ℝ => (t : ℂ)) hreal hofReal
  refine hcomp.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds ht₀] with t ht
  rw [← hray t]
  exact (invBottcher_rayPoint hN ht).symm

end Work.ELRig
