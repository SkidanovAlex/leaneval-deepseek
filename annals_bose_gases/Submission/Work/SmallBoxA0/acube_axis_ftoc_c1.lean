import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.SmallBoxA0.acube_axis_ftoc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The axis fundamental theorem of calculus on the centred cube, `C¹` version

For a `C¹` map `φ : ℝ³ → ℝ` vanishing on the two faces `z j = ±s/2` of the centred cube
`acube s = [-s/2, s/2]³`, the integral over the cube of the `j`-th partial derivative
vanishes:

    ∫ z in acube s, fderiv ℝ φ z (kcStdBasis j) = 0 .

This is the `C¹` refinement of `Work.SmallBoxA0.acube_axis_ftoc` (which assumes `φ` smooth).
The proof is identical in structure: the only smoothness input actually needed is that the
derivative is continuous, which `ContDiff ℝ 1 φ` already provides
(`ContDiff.continuous_fderiv` with `n = 1`).  The generic slicing/chain-rule helpers are
imported from the smooth development.
-/

namespace Work.SmallBoxA0

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- One-dimensional FTC on a single `j`-slice of the centred cube (`C¹` version): if `ψ`
vanishes on the two faces `z j = ±s/2`, then the integral of the sliced derivative over the
slice vanishes. -/
lemma acubeAxis_slice_zero_c1 {s : ℝ} (hs : 0 < s) (j : Fin 3) {ψ : (Fin 3 → ℝ) → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hfront : ∀ z ∈ acubeF s, z j = s / 2 → ψ z = 0)
    (hback : ∀ z ∈ acubeF s, z j = -(s / 2) → ψ z = 0)
    (r : Fin 2 → ℝ) (hr : ∀ k : Fin 2, r k ∈ Set.Icc (-s/2) (s/2)) :
    ∫ t in Set.Icc (-s/2) (s/2),
        fderiv ℝ ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j).symm (t, r))
          (Pi.single j (1:ℝ)) = 0 := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j
  set g : ℝ → ℝ := fun t => fderiv ℝ ψ (e.symm (t, r)) (Pi.single j (1:ℝ))
  set f : ℝ → ℝ := fun t => ψ (e.symm (t, r))
  have hunfold : ∀ t : ℝ, e.symm (t, r) = Fin.insertNth (α := fun _ : Fin 3 => ℝ) j t r := by
    intro t
    simp only [e]
    exact acubeAxis_piFinSuccAbove_symm_eq3 j t r
  have hderiv : deriv f = g := by
    funext t
    simp only [f, g]
    rw [hunfold t]
    exact acubeAxis_deriv_ins3 ψ j r t ((hψ.differentiable (by simp)).differentiableAt)
  have hab : -s/2 ≤ s/2 := by linarith
  have hmain : ∫ t in (-s/2)..(s/2), g t = f (s/2) - f (-s/2) := by
    have haff : ∀ u : ℝ, e.symm (u, r)
        = Fin.insertNth (α := fun _ : Fin 3 => ℝ) j (0:ℝ) r + u • Pi.single j (1:ℝ) := by
      intro u; rw [hunfold u]; exact acubeAxis_ins3_affine j u r
    refine intervalIntegral.integral_deriv_eq_sub' f hderiv ?_ ?_
    · intro x hx
      have h1 : DifferentiableAt ℝ (fun u : ℝ => e.symm (u, r)) x := by
        rw [show (fun u : ℝ => e.symm (u, r))
            = fun u => Fin.insertNth (α := fun _ : Fin 3 => ℝ) j (0:ℝ) r + u • Pi.single j (1:ℝ)
            from funext haff]
        fun_prop
      exact ((hψ.differentiable (by simp)).differentiableAt).comp x h1
    · have hcontt : Continuous (fun t : ℝ => fderiv ℝ ψ (e.symm (t, r))) := by
        refine (hψ.continuous_fderiv (by simp)).comp ?_
        rw [show (fun u : ℝ => e.symm (u, r))
            = fun u => Fin.insertNth (α := fun _ : Fin 3 => ℝ) j (0:ℝ) r + u • Pi.single j (1:ℝ)
            from funext haff]
        fun_prop
      exact (hcontt.clm_apply continuous_const).continuousOn
  have hmem_s : e.symm (s/2, r) ∈ acubeF s := by
    simp only [acubeF]
    intro m
    rw [hunfold]
    by_cases hm : m = j
    · subst hm; rw [Fin.insertNth_apply_same]; exact ⟨by linarith, by linarith⟩
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hm
      rw [← hk, Fin.insertNth_apply_succAbove]; exact hr k
  have hmem_b : e.symm (-s/2, r) ∈ acubeF s := by
    simp only [acubeF]
    intro m
    rw [hunfold]
    by_cases hm : m = j
    · subst hm; rw [Fin.insertNth_apply_same]; exact ⟨by linarith, by linarith⟩
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hm
      rw [← hk, Fin.insertNth_apply_succAbove]; exact hr k
  have hfront0 : f (s/2) = 0 := by
    simp only [f]
    exact hfront _ hmem_s (by rw [hunfold]; exact Fin.insertNth_apply_same (α := fun _ : Fin 3 => ℝ) j (s/2) r)
  have hback0 : f (-s/2) = 0 := by
    simp only [f]
    refine hback _ hmem_b ?_
    rw [hunfold, Fin.insertNth_apply_same (α := fun _ : Fin 3 => ℝ) j (-s/2) r]
    exact (neg_div 2 s)
  calc ∫ t in Set.Icc (-s/2) (s/2), g t
      = ∫ t in Set.Ioc (-s/2) (s/2), g t := MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ t in (-s/2)..(s/2), g t := (intervalIntegral.integral_of_le hab).symm
    _ = f (s/2) - f (-s/2) := hmain
    _ = 0 := by rw [hfront0, hback0, sub_zero]

/-- The axis FTC on the coordinate cube `acubeF s ⊆ (Fin 3 → ℝ)` (`C¹` version), by Fubini and
the one-dimensional FTC on the slices. -/
lemma acubeAxis_box_c1 {s : ℝ} (hs : 0 < s) (j : Fin 3) {ψ : (Fin 3 → ℝ) → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hfront : ∀ z ∈ acubeF s, z j = s / 2 → ψ z = 0)
    (hback : ∀ z ∈ acubeF s, z j = -(s / 2) → ψ z = 0) :
    ∫ z in acubeF s, fderiv ℝ ψ z (Pi.single j (1:ℝ)) = 0 := by
  set μ₀ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (-s/2) (s/2)) with hμ₀def
  set μ₂ : Measure (Fin 2 → ℝ) := Measure.pi (fun _ : Fin 2 => μ₀) with hμ₂def
  set F : (Fin 3 → ℝ) → ℝ := fun z => fderiv ℝ ψ z (Pi.single j (1:ℝ)) with hFdef
  set Φ : ℝ × (Fin 2 → ℝ) → ℝ :=
    fun p => F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j).symm p) with hΦdef
  have hFcont : Continuous F := by
    rw [hFdef]
    exact (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hν : (volume : Measure (Fin 3 → ℝ)).restrict (acubeF s) = Measure.pi (fun _ : Fin 3 => μ₀) := by
    rw [acubeF_restrict_eq_pi s]
  have hmp : MeasurePreserving (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j))
      ((volume : Measure (Fin 3 → ℝ)).restrict (acubeF s)) (μ₀.prod μ₂) := by
    have h := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ₀) j
    rw [← hν] at h
    simpa only [hμ₂def] using h
  have hIntF : Integrable F ((volume : Measure (Fin 3 → ℝ)).restrict (acubeF s)) := by
    have hK : IsCompact (acubeF s) := by
      rw [acubeF_eq_pi]
      exact isCompact_univ_pi (fun _ => isCompact_Icc)
    exact ContinuousOn.integrableOn_compact hK hFcont.continuousOn
  have hIntΦ : Integrable Φ (μ₀.prod μ₂) := by
    rw [hΦdef]
    exact ((MeasurePreserving.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j) hmp).integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j).symm.measurableEmbedding).mpr hIntF
  have hstep1 : ∫ x, F x ∂((volume : Measure (Fin 3 → ℝ)).restrict (acubeF s)) = ∫ p, Φ p ∂(μ₀.prod μ₂) := by
    rw [hΦdef]
    exact ((MeasurePreserving.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j) hmp).integral_comp' F).symm
  have hstep2 : ∫ p, Φ p ∂(μ₀.prod μ₂) = ∫ p, Φ p.swap ∂(μ₂.prod μ₀) :=
    (MeasureTheory.integral_prod_swap Φ).symm
  have hstep3 : ∫ p, Φ p.swap ∂(μ₂.prod μ₀) = ∫ r, (∫ t, Φ (t, r) ∂μ₀) ∂μ₂ :=
    MeasureTheory.integral_prod (fun p : (Fin 2 → ℝ) × ℝ => Φ p.swap) hIntΦ.swap
  have hμ₂C : μ₂ = (volume : Measure (Fin 2 → ℝ)).restrict
      (Set.univ.pi (fun _ : Fin 2 => Set.Icc (-s/2) (s/2))) := by
    rw [hμ₂def]
    rw [show (volume : Measure (Fin 2 → ℝ)) = Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ)) from rfl]
    rw [Measure.restrict_pi_pi]
  have hC₂meas : MeasurableSet (Set.univ.pi (fun _ : Fin 2 => Set.Icc (-s/2) (s/2))) :=
    MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)
  have hpt : ∀ r : Fin 2 → ℝ, r ∈ Set.univ.pi (fun _ : Fin 2 => Set.Icc (-s/2) (s/2)) →
      ∫ t, Φ (t, r) ∂μ₀ = 0 := by
    intro r hr
    rw [hΦdef, hFdef]
    show ∫ t in Set.Icc (-s/2) (s/2),
        fderiv ℝ ψ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j).symm (t, r))
          (Pi.single j (1:ℝ)) = 0
    exact acubeAxis_slice_zero_c1 hs j hψ hfront hback r (fun k => Set.mem_univ_pi.mp hr k)
  have hstep4 : ∫ r, (∫ t, Φ (t, r) ∂μ₀) ∂μ₂ = 0 := by
    rw [hμ₂C]
    have hae : (fun r => ∫ t, Φ (t, r) ∂μ₀)
        =ᵐ[(volume : Measure (Fin 2 → ℝ)).restrict
            (Set.univ.pi (fun _ : Fin 2 => Set.Icc (-s/2) (s/2)))] 0 := by
      filter_upwards [ae_restrict_mem hC₂meas] with r hr
      exact hpt r hr
    rw [integral_congr_ae hae]
    simp
  calc ∫ z in acubeF s, F z
      = ∫ x, F x ∂((volume : Measure (Fin 3 → ℝ)).restrict (acubeF s)) := rfl
    _ = ∫ p, Φ p ∂(μ₀.prod μ₂) := hstep1
    _ = ∫ p, Φ p.swap ∂(μ₂.prod μ₀) := hstep2
    _ = ∫ r, (∫ t, Φ (t, r) ∂μ₀) ∂μ₂ := hstep3
    _ = 0 := hstep4

theorem acube_axis_ftoc_c1 {s : ℝ} (hs : 0 < s) (j : Fin 3) {φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hφ : ContDiff ℝ 1 φ)
    (hfront : ∀ z ∈ Submission.BoseGases.acube s, z j = s / 2 → φ z = 0)
    (hback : ∀ z ∈ Submission.BoseGases.acube s, z j = -(s / 2) → φ z = 0) :
    ∫ z in Submission.BoseGases.acube s, fderiv ℝ φ z (Submission.BoseGases.kcStdBasis j) = 0 := by
  let E3 : (Fin 3 → ℝ) ≃L[ℝ] ℝ³ := (EuclideanSpace.equiv (𝕜:=ℝ) (ι:=Fin 3)).symm
  let ψ : (Fin 3 → ℝ) → ℝ := fun x => φ (E3 x)
  have hψcd : ContDiff ℝ 1 ψ := by
    have h : ContDiff ℝ 1 ((⇑E3) : (Fin 3 → ℝ) → ℝ³) := E3.toContinuousLinearMap.contDiff
    exact hφ.comp h
  have key : ∀ x : Fin 3 → ℝ, fderiv ℝ φ (E3 x) (kcStdBasis j) = fderiv ℝ ψ x (Pi.single j (1:ℝ)) := by
    intro x
    have hE : HasFDerivAt (⇑E3) E3.toContinuousLinearMap x := E3.hasFDerivAt
    have hφd : HasFDerivAt φ (fderiv ℝ φ (E3 x)) (E3 x) :=
      (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hc := hφd.comp x hE
    have hfd : fderiv ℝ ψ x = (fderiv ℝ φ (E3 x)).comp E3.toContinuousLinearMap := by
      have h1 : ψ = φ ∘ (⇑E3) := rfl
      rw [h1, hc.fderiv]
    have hE3single : E3.toContinuousLinearMap (Pi.single j (1:ℝ)) = kcStdBasis j := by
      show WithLp.toLp 2 (Pi.single j (1:ℝ)) = EuclideanSpace.single j 1
      rfl
    rw [hfd, ContinuousLinearMap.comp_apply, hE3single]
  have hchange : ∫ z in acube s, fderiv ℝ φ z (kcStdBasis j)
      = ∫ x in acubeF s, fderiv ℝ φ (E3 x) (kcStdBasis j) := by
    rw [acube_restrict_eq_map s]
    exact MeasureTheory.integral_map (E3.continuous.measurable.aemeasurable)
      (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable)
  have hunit : ∀ x : Fin 3 → ℝ, (E3 x) j = x j := fun x => rfl
  have hfrontψ : ∀ z ∈ acubeF s, z j = s / 2 → ψ z = 0 := by
    intro z hz hzj
    have hz' : E3 z ∈ acube s := by
      rw [acube_eq_image]
      exact ⟨z, hz, rfl⟩
    exact hfront (E3 z) hz' (by rw [hunit z]; exact hzj)
  have hbackψ : ∀ z ∈ acubeF s, z j = -(s / 2) → ψ z = 0 := by
    intro z hz hzj
    have hz' : E3 z ∈ acube s := by
      rw [acube_eq_image]
      exact ⟨z, hz, rfl⟩
    exact hback (E3 z) hz' (by rw [hunit z]; exact hzj)
  have hbox := acubeAxis_box_c1 hs j hψcd hfrontψ hbackψ
  calc ∫ z in acube s, fderiv ℝ φ z (kcStdBasis j)
      = ∫ x in acubeF s, fderiv ℝ φ (E3 x) (kcStdBasis j) := hchange
    _ = ∫ x in acubeF s, fderiv ℝ ψ x (Pi.single j (1:ℝ)) := by
          exact MeasureTheory.setIntegral_congr_fun (acubeF_measurable s) (fun x _ => key x)
    _ = 0 := hbox

end Work.SmallBoxA0
