import Mathlib
import Submission.Work.ThomBordism.FrameSigns.germPullbackDefs
import Submission.Work.ThomBordism.FrameSigns.linearActionIsl
import Submission.Work.Thom.ATools
import Submission.Work.Cohomology.capRelAux
import Submission.Work.Thom.relCohMap_homotopic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped unitInterval Topology
open CategoryTheory

/-!
# The pullback along a germ diffeomorphism of `ℝ⁸` fixed at `0`

This is the statement of `Work.ThomBordism.FrameSigns.germPullback`
(`Submission/Work/ThomBordism/FrameSigns/germPullback.lean`), proved here from the objects of
`Submission/Work/ThomBordism/FrameSigns/germPullbackDefs.lean` (the open ball `gpU`, the closed ball
`gpCl` and the radial retraction `gpρ`):

* excision identifies the relative cohomology of `(↥W, W∖0)` with that of the open ball
  `(↥(gpU r W), gpAU r W)`;
* on the open ball, `F` and `L` are respectively homotopic to `(F|_cl) ∘ ρ` and `(L|_cl) ∘ ρ`
  (radial homotopies), and `(F|_cl)^* = (L|_cl)^*` by `germFDeriv`;
* `(L|_U)^* ξ = s • (inclusion)^* ξ` by `linearModelActionIsl`.

The result is used by `Work.ThomBordism.FrameSigns.chartCoh_compare`.
-/

namespace Work.ThomBordism.FrameSigns

noncomputable section

/-- **The pullback along a germ diffeomorphism of `ℝ⁸` fixed at `0` is `sign(det)` times the
pullback along the inclusion.**  Same statement as `Work.ThomBordism.FrameSigns.germPullback`,
proved from scratch so that it can be used without importing that module's `sorry`. -/
theorem germPullbackLocal {W : Set E8} (hW : IsOpen W) (h0 : 0 ∈ W)
    (F : E8 → E8) (hFc : ContinuousOn F W) (hF0 : F 0 = 0)
    (hnz : ∀ z ∈ W, z ≠ 0 → F z ≠ 0)
    (L : E8 →L[ℝ] E8) (hL : Function.Bijective L) (hdF : HasFDerivAt F L 0)
    (hdet : LinearMap.det L.toLinearMap ≠ 0) :
    ∀ ξ : Work.Thom.RelCoh ℤ 8 E8 gpB0,
      (Work.Thom.relCohMap (gpFW W F hFc) (gpBW W) gpB0
        (fun z hz => hnz (z : E8) z.2 hz) ℤ 8).hom ξ
        = (if 0 < LinearMap.det L.toLinearMap then (1 : ℤ) else -1) •
          (Work.Thom.relCohMap (gpiW W) (gpBW W) gpB0 (fun z hz => hz) ℤ 8).hom ξ := by
  intro ξ
  set s : ℤ := if 0 < LinearMap.det L.toLinearMap then (1 : ℤ) else -1 with hs_def
  -- a radius whose closed ball lies in `W`
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h0)
  set r : ℝ := ε / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  have hrW : Metric.closedBall (0 : E8) r ⊆ W := by
    intro z hz
    refine hεW (Metric.mem_ball.mpr ?_)
    have hz' : dist z (0 : E8) ≤ r := Metric.mem_closedBall.mp hz
    rw [hr_def] at hz'
    linarith
  -- the open ball as a subset of `↥W`, and the excision isomorphism
  have hU : IsOpen (gpU r W) := by
    show IsOpen ((fun z : ↥W => (z : E8)) ⁻¹' Metric.ball (0 : E8) r)
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  have hA : IsOpen (gpBW W) := by
    show IsOpen ((fun z : ↥W => (z : E8)) ⁻¹' ({0}ᶜ : Set E8))
    exact isClosed_singleton.isOpen_compl.preimage continuous_subtype_val
  have hcov : gpU r W ∪ gpBW W = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hz : (z : E8) = 0
    · exact Or.inl (by
        show (z : E8) ∈ Metric.ball (0 : E8) r
        rw [hz]; exact Metric.mem_ball_self hr)
    · exact Or.inr hz
  have hmemUW : ∀ z ∈ gpAU r W, (gpc r W) z ∈ gpBW W := fun z hz => hz
  haveI hIsoK : CategoryTheory.IsIso
      (Work.Thom.relCohMap (gpc r W) (gpAU r W) (gpBW W) (fun z hz => hz) ℤ 8) := by
    exact Work.Cohomology.capRel_excision_isIso (TopCat.of ↥W) (gpU r W) (gpBW W) hU hA
      hcov 8 (fun z hz => hz)
  have hKinj : Function.Injective
      (Work.Thom.relCohMap (gpc r W) (gpAU r W) (gpBW W) (fun z hz => hz) ℤ 8).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  -- the coefficient of the first homotopy
  have hcoef1_norm_le : ∀ u : unitInterval, ‖((1 - (u : ℝ)) + (u : ℝ) * (1 / 2))‖ ≤ 1 := by
    intro u
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [u.2.1, u.2.2], by linarith [u.2.1, u.2.2]⟩
  have h1mem : ∀ p : unitInterval × ↥(gpU r W),
      (((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (1 / 2)) • ((p.2 : ↥W) : E8)) ∈ W := by
    intro p
    refine hrW ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have hz : ‖((p.2 : ↥W) : E8)‖ ≤ r := by
      have h : ((p.2 : ↥W) : E8) ∈ Metric.ball (0 : E8) r := p.2.2
      rw [Metric.mem_ball, dist_zero_right] at h
      exact le_of_lt h
    calc ‖((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (1 / 2)) • ((p.2 : ↥W) : E8)‖
        = ‖((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (1 / 2))‖ * ‖((p.2 : ↥W) : E8)‖ := norm_smul _ _
      _ ≤ 1 * r := mul_le_mul (hcoef1_norm_le p.1) hz (norm_nonneg _) zero_le_one
      _ = r := one_mul r
  have h1cont : Continuous fun p : unitInterval × ↥(gpU r W) =>
      (((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (1 / 2)) • ((p.2 : ↥W) : E8)) :=
    (((continuous_const : Continuous fun _ : unitInterval × ↥(gpU r W) => (1 : ℝ)).sub
        (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  -- the first homotopy: `F|_U ≃ (F|_cl) ∘ ρ`
  let hH1 : (gpFU r W F hFc).Homotopy ((gpFCl r hr W F hFc hrW).comp (gpρ r W)) :=
    ContinuousMap.Homotopy.mk
      ⟨fun p => F (((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (1 / 2)) • ((p.2 : ↥W) : E8)),
        hFc.comp_continuous h1cont h1mem⟩
      (fun z => by
        show F (((1 - ((0 : unitInterval) : ℝ)) + ((0 : unitInterval) : ℝ) * (1 / 2)) •
          ((z : ↥W) : E8)) = gpFU r W F hFc z
        have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
        rw [h0]
        simp only [sub_zero, zero_mul, zero_add, add_zero, one_mul, zero_smul, one_smul, gpFU_apply])
      (fun z => by
        show F (((1 - ((1 : unitInterval) : ℝ)) + ((1 : unitInterval) : ℝ) * (1 / 2)) •
          ((z : ↥W) : E8)) = ((gpFCl r hr W F hFc hrW).comp (gpρ r W)) z
        have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
        rw [h1]
        simp only [sub_self, zero_mul, one_mul, zero_add, add_zero, zero_smul, one_smul]
        rw [ContinuousMap.comp_apply, gpFCl_apply, gpρ_apply])
  have hH1mem : ∀ (t : unitInterval) (z : ↥(gpU r W)), z ∈ gpAU r W → hH1 (t, z) ∈ gpB0 := by
    intro t z hz
    show F (((1 - (t : ℝ)) + (t : ℝ) * (1 / 2)) • ((z : ↥W) : E8)) ≠ 0
    refine hnz _ (h1mem (t, z)) ?_
    apply smul_ne_zero
    · intro hc
      have h := t.2
      nlinarith [h.1, h.2]
    · exact hz
  -- the second homotopy: `(L|_cl) ∘ ρ ≃ L|_U`
  have h2cont : Continuous fun p : unitInterval × ↥(gpU r W) =>
      (((1 - (p.1 : ℝ)) / 2 + (p.1 : ℝ)) • ((p.2 : ↥W) : E8)) :=
    ((((continuous_const : Continuous fun _ : unitInterval × ↥(gpU r W) => (1 : ℝ)).sub
        (continuous_subtype_val.comp continuous_fst)).div_const 2).add
      (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  let hH2 : ((gpLCl r L).comp (gpρ r W)).Homotopy (gpLU r W L) :=
    ContinuousMap.Homotopy.mk
      ⟨fun p => L (((1 - (p.1 : ℝ)) / 2 + (p.1 : ℝ)) • ((p.2 : ↥W) : E8)),
        L.continuous.comp h2cont⟩
      (fun z => by
        show L (((1 - ((0 : unitInterval) : ℝ)) / 2 + ((0 : unitInterval) : ℝ)) •
          ((z : ↥W) : E8)) = ((gpLCl r L).comp (gpρ r W)) z
        have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
        rw [h0]
        simp only [sub_zero, add_zero, zero_add, zero_smul]
        rw [ContinuousMap.comp_apply, gpLCl_apply, gpρ_apply])
      (fun z => by
        show L (((1 - ((1 : unitInterval) : ℝ)) / 2 + ((1 : unitInterval) : ℝ)) •
          ((z : ↥W) : E8)) = gpLU r W L z
        have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
        rw [h1]
        simp only [sub_self, zero_div, zero_add, one_smul, gpLU_apply])
  have hH2mem : ∀ (t : unitInterval) (z : ↥(gpU r W)), z ∈ gpAU r W → hH2 (t, z) ∈ gpB0 := by
    intro t z hz
    show L (((1 - (t : ℝ)) / 2 + (t : ℝ)) • ((z : ↥W) : E8)) ≠ 0
    intro h
    have hcoef : ((1 - (t : ℝ)) / 2 + (t : ℝ)) ≠ 0 := by
      intro hc
      have h' := t.2
      nlinarith [h'.1, h'.2]
    exact (smul_ne_zero hcoef hz) (hL.1 (by simpa using h))
  -- the pair conditions used below
  have hρmem : ∀ z ∈ gpAU r W, (gpρ r W) z ∈ gpACl r := by
    intro z hz
    show ((gpρ r W z : ↥(gpCl r)) : E8) ≠ 0
    rw [gpρ_apply]
    exact smul_ne_zero (by norm_num) hz
  have hFClρmem : ∀ z ∈ gpAU r W,
      ((gpFCl r hr W F hFc hrW).comp (gpρ r W)) z ∈ gpB0 :=
    fun z hz => gpFClmem r hr W F hFc hnz hrW (gpρ r W z) (hρmem z hz)
  have hLClρmem : ∀ z ∈ gpAU r W,
      ((gpLCl r L).comp (gpρ r W)) z ∈ gpB0 :=
    fun z hz => gpLClmem r L hL (gpρ r W z) (hρmem z hz)
  have hL8mem : ∀ z ∈ gpB0, (gpL8 L) z ∈ gpB0 := by
    intro z hz h
    have h' : L z = 0 := h
    exact hz (hL.1 (by rw [h', map_zero]))
  -- the linear step
  let e₀ : E8 ≃ₗ[ℝ] E8 := LinearEquiv.ofBijective (L : E8 →ₗ[ℝ] E8) hL
  let A : E8 ≃L[ℝ] E8 := e₀.toContinuousLinearEquiv
  have hAeq : ∀ z : E8, A z = L z := by
    intro z
    change e₀ z = L z
    rw [LinearEquiv.ofBijective_apply]
    rfl
  have hAclm : (A : E8 →L[ℝ] E8) = L := ContinuousLinearMap.ext hAeq
  have hAU : ∀ z ∈ gpB0, (A : C(E8, E8)) z ∈ gpB0 :=
    fun z hz h => hz ((A.map_eq_zero_iff).mp h)
  have hlin : (Work.Thom.relCohMap (gpL8 L) gpB0 gpB0 hL8mem ℤ 8).hom ξ = s • ξ := by
    have h1 := linearModelActionIsl A (by rw [hAclm]; exact hdet) ξ
    have hmap : (A : C(E8, E8)) = gpL8 L := by
      apply ContinuousMap.ext
      intro z
      exact hAeq z
    have hmorph : (Work.Thom.relCohMap (A : C(E8, E8)) gpB0 gpB0 hAU ℤ 8)
        = (Work.Thom.relCohMap (gpL8 L) gpB0 gpB0 hL8mem ℤ 8) :=
      Work.Thom.relCohMap_congrA gpB0 gpB0 hmap hAU hL8mem ℤ 8
    have hdetA : (if 0 < LinearMap.det (A : E8 →L[ℝ] E8).toLinearMap then (1 : ℤ) else -1)
        = (if 0 < LinearMap.det L.toLinearMap then (1 : ℤ) else -1) := by rw [hAclm]
    rw [hmorph, hdetA] at h1
    rw [h1, ← hs_def]
  -- the chain of equalities on the open ball
  have hchain : (Work.Thom.relCohMap (gpFU r W F hFc) (gpAU r W) gpB0
        (gpFUmem r W F hFc hnz) ℤ 8).hom ξ
      = s • (Work.Thom.relCohMap (gpiU r W) (gpAU r W) gpB0 (gpiUmem r W) ℤ 8).hom ξ := by
    have hstep1 := congrArg (fun φ => φ.hom ξ)
      (Work.Thom.relCohMap_homotopic (gpAU r W) gpB0 (gpFUmem r W F hFc hnz) hFClρmem hH1
        hH1mem ℤ 8)
    have hstep2 : (Work.Thom.relCohMap ((gpFCl r hr W F hFc hrW).comp (gpρ r W))
          (gpAU r W) gpB0 hFClρmem ℤ 8).hom ξ
        = (Work.Thom.relCohMap (gpρ r W) (gpAU r W) (gpACl r) hρmem ℤ 8).hom
            ((Work.Thom.relCohMap (gpFCl r hr W F hFc hrW) (gpACl r) gpB0
              (gpFClmem r hr W F hFc hnz hrW) ℤ 8).hom ξ) := by
      rw [Work.Thom.relCohMap_compA_apply (gpAU r W) (gpACl r) gpB0 (gpρ r W)
        (gpFCl r hr W F hFc hrW) hρmem (gpFClmem r hr W F hFc hnz hrW) hFClρmem ℤ 8 ξ]
    have hstep3 : (Work.Thom.relCohMap (gpFCl r hr W F hFc hrW) (gpACl r) gpB0
          (gpFClmem r hr W F hFc hnz hrW) ℤ 8).hom ξ
        = (Work.Thom.relCohMap (gpLCl r L) (gpACl r) gpB0 (gpLClmem r L hL) ℤ 8).hom ξ :=
      germFDeriv r hr F L (hFc.mono hrW) hL hF0 hdF
        (fun z hz hz0 => hnz z (hrW hz) hz0) (r / 2) (by linarith) (by linarith) ξ
    have hstep4 : (Work.Thom.relCohMap (gpρ r W) (gpAU r W) (gpACl r) hρmem ℤ 8).hom
          ((Work.Thom.relCohMap (gpLCl r L) (gpACl r) gpB0 (gpLClmem r L hL) ℤ 8).hom ξ)
        = (Work.Thom.relCohMap ((gpLCl r L).comp (gpρ r W)) (gpAU r W) gpB0
            hLClρmem ℤ 8).hom ξ := by
      rw [Work.Thom.relCohMap_compA_apply (gpAU r W) (gpACl r) gpB0 (gpρ r W) (gpLCl r L)
        hρmem (gpLClmem r L hL) hLClρmem ℤ 8 ξ]
    have hstep5 := congrArg (fun φ => φ.hom ξ)
      (Work.Thom.relCohMap_homotopic (gpAU r W) gpB0 hLClρmem (gpLUmem r W L hL) hH2
        hH2mem ℤ 8)
    have hstep6 : (Work.Thom.relCohMap (gpLU r W L) (gpAU r W) gpB0 (gpLUmem r W L hL) ℤ 8).hom ξ
        = s • (Work.Thom.relCohMap (gpiU r W) (gpAU r W) gpB0 (gpiUmem r W) ℤ 8).hom ξ := by
      have hc := Work.Thom.relCohMap_compA_apply (gpAU r W) gpB0 gpB0 (gpiU r W) (gpL8 L)
        (gpiUmem r W) hL8mem (gpLUmem r W L hL) ℤ 8 ξ
      have hf : (Work.Thom.relCohMap (gpLU r W L) (gpAU r W) gpB0 (gpLUmem r W L hL) ℤ 8).hom ξ
          = (Work.Thom.relCohMap ((gpL8 L).comp (gpiU r W)) (gpAU r W) gpB0
              (gpLUmem r W L hL) ℤ 8).hom ξ := rfl
      rw [hf, ← hc, hlin, map_zsmul]
    calc (Work.Thom.relCohMap (gpFU r W F hFc) (gpAU r W) gpB0 (gpFUmem r W F hFc hnz) ℤ 8).hom ξ
        = (Work.Thom.relCohMap ((gpFCl r hr W F hFc hrW).comp (gpρ r W)) (gpAU r W) gpB0
            hFClρmem ℤ 8).hom ξ := hstep1
      _ = (Work.Thom.relCohMap (gpρ r W) (gpAU r W) (gpACl r) hρmem ℤ 8).hom
            ((Work.Thom.relCohMap (gpFCl r hr W F hFc hrW) (gpACl r) gpB0
              (gpFClmem r hr W F hFc hnz hrW) ℤ 8).hom ξ) := hstep2
      _ = (Work.Thom.relCohMap (gpρ r W) (gpAU r W) (gpACl r) hρmem ℤ 8).hom
            ((Work.Thom.relCohMap (gpLCl r L) (gpACl r) gpB0 (gpLClmem r L hL) ℤ 8).hom ξ) := by
          rw [hstep3]
      _ = (Work.Thom.relCohMap ((gpLCl r L).comp (gpρ r W)) (gpAU r W) gpB0 hLClρmem ℤ 8).hom ξ :=
          hstep4
      _ = (Work.Thom.relCohMap (gpLU r W L) (gpAU r W) gpB0 (gpLUmem r W L hL) ℤ 8).hom ξ :=
          hstep5
      _ = s • (Work.Thom.relCohMap (gpiU r W) (gpAU r W) gpB0 (gpiUmem r W) ℤ 8).hom ξ :=
          hstep6
  -- transport along the inclusion of the open ball
  have hPW : (Work.Thom.relCohMap (gpc r W) (gpAU r W) (gpBW W) hmemUW ℤ 8).hom
        ((Work.Thom.relCohMap (gpFW W F hFc) (gpBW W) gpB0
          (fun z hz => hnz (z : E8) z.2 hz) ℤ 8).hom ξ)
      = s • (Work.Thom.relCohMap (gpc r W) (gpAU r W) (gpBW W) hmemUW ℤ 8).hom
        ((Work.Thom.relCohMap (gpiW W) (gpBW W) gpB0 (fun z hz => hz) ℤ 8).hom ξ) := by
    rw [Work.Thom.relCohMap_compA_apply (gpAU r W) (gpBW W) gpB0 (gpc r W) (gpFW W F hFc)
      hmemUW (fun z hz => hnz (z : E8) z.2 hz) (gpFUmem r W F hFc hnz) ℤ 8 ξ]
    rw [Work.Thom.relCohMap_compA_apply (gpAU r W) (gpBW W) gpB0 (gpc r W) (gpiW W)
      hmemUW (fun z hz => hz) (gpiUmem r W) ℤ 8 ξ]
    exact hchain
  refine hKinj ?_
  rw [map_zsmul]
  exact hPW

end

end Work.ThomBordism.FrameSigns
