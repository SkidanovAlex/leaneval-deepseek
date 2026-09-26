import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.openTiltedSweepRegion_subset_dentOutRegion
import Submission.Work.Drive.Final.aboveGeneric_of_cut

/-!
# L6b's pointwise core: a regular level point of the surface in the box lies in `closure Ω₁`

`Work.Drive.Final.dentOutRegion D` (the lead's `Ω₁`) is the set of points of the surface whose image
under the dent deformation `D.deform` lies in the *interior* of the set removed at the level
`ℓ D.centre`:

  `Ω₁ = carrier ∩ interior (D.deform ⁻¹' tiltedLevelRemoved … (ℓ D.centre))`.

`Work.Drive.Final.openTiltedSweepRegion_subset_dentOutRegion` shows that the *open* sweep region at
that level is contained in `Ω₁`.  This module proves the pointwise core of L6b: at a point `z` of the
surface which lies in the box `PBox s c σ`, on the level `ℓ z = ℓ D.centre`, and whose parameter
point `p` (`par ψ p = z`) is a *regular* point of the sweep height `q ↦ ℓ (par ψ q)`, the point `z`
lies in `closure Ω₁`.

The proof is the one of `Work.Drive.Final.mem_closure_openTiltedSweepRegion_of_regular`: the
non-vanishing derivative of the sweep height gives a direction `w` along which the height strictly
increases, and the points `par ψ (p + t • w)`, `t → 0⁺`, are points of the surface in the box with
`ℓ > ℓ D.centre`, hence points of the open sweep region, tending to `z = par ψ p`.  The slab
hypothesis which the cited lemma carries is **not** used there and is *not* available here (a face
or corner event of an `AnyDentDatum` lies on the boundary of the box), so the argument is repeated
without it.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

namespace Work.Drive.Final

noncomputable section

/-- **The open region of the tilted sweep accumulates at a level point of the surface in the box at
which the sweep height is regular.**  No hypothesis on the slab is needed: the pushed points have
level strictly greater than `lam`, and such a point of the box region is in the open sweep region
whether or not it lies in the closed slab. -/
theorem mem_closure_openTiltedSweepRegion_of_fderiv_ne {ψ : Submission.Diffeo} {s : ℝ}
    {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    {p : ℝ × ℝ}
    (hpP : Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ)
    (hpℓ : ℓ (Work.BoxShrink.Pinch.par ψ p) = lam)
    (hder : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0) :
    Work.BoxShrink.Pinch.par ψ p ∈ closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion
      (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) := by
  classical
  -- a direction in which the height increases
  obtain ⟨w, hw⟩ : ∃ w : ℝ × ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hder (ContinuousLinearMap.ext hcon)
  set w' : ℝ × ℝ :=
    if 0 < fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w then w else -w with hw'def
  have hpos : 0 < fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w' := by
    have hval : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w' =
        if 0 < fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w then
          fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w
        else -(fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w) := by
      rw [hw'def]
      split_ifs with hh
      · rfl
      · simp
    rw [hval]
    split_ifs with hh
    · exact hh
    · exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hh) hw)
  -- differentiability of the sweep height
  have hfderiv : HasFDerivAt (Work.Drive.EpsForm.sweepHeight ψ ℓ)
      (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p) p := by
    have hcd : ContDiff ℝ (↑(⊤ : ℕ∞)) (Work.Drive.EpsForm.sweepHeight ψ ℓ) := by
      rw [Work.Drive.EpsForm.sweepHeight]
      exact Work.Smooth.Morse.pullback_contDiff ψ (ContinuousLinearMap.contDiff ℓ)
    exact ((hcd.differentiable (by simp)).differentiableAt).hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => p + t • w') w' 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • w') w' 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const w'
    simpa using h1.const_add p
  have hfderiv' : HasFDerivAt (Work.Drive.EpsForm.sweepHeight ψ ℓ)
      (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p) ((fun t : ℝ => p + t • w') 0) := by
    simpa using hfderiv
  have hcomp : HasDerivAt
      ((Work.Drive.EpsForm.sweepHeight ψ ℓ) ∘ fun t : ℝ => p + t • w')
      (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w') 0 :=
    hfderiv'.comp_hasDerivAt 0 hcurve
  have hzero : ((Work.Drive.EpsForm.sweepHeight ψ ℓ) ∘ fun t : ℝ => p + t • w') 0 = lam := by
    simp only [Function.comp_apply, zero_smul, add_zero]
    rw [sweepHeight_apply, hpℓ]
  -- the height strictly increases along the ray
  have hev_ht : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      lam < (Work.Drive.EpsForm.sweepHeight ψ ℓ) (p + t • w') := by
    have htend := hcomp.tendsto_slope_zero_right
    rw [hzero] at htend
    have hmem2 : Set.Ioi ((fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w') / 2) ∈
        𝓝 (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w') :=
      (isOpen_Ioi (a := (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w') / 2)).mem_nhds
        (by simp only [Set.mem_Ioi]; linarith)
    have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w') / 2 <
          t⁻¹ • ((Work.Drive.EpsForm.sweepHeight ψ ℓ) (p + (0 + t) • w') - lam) :=
      htend.eventually hmem2
    filter_upwards [hev2, self_mem_nhdsWithin] with t ht hgt
    have htpos : 0 < t := hgt
    simp only [zero_add, Function.comp_apply, zero_smul, add_zero] at ht
    rw [smul_eq_mul] at ht
    have hmul : t * ((fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w') / 2) <
        (Work.Drive.EpsForm.sweepHeight ψ ℓ) (p + t • w') - lam := by
      have h2 : t * (t⁻¹ * ((Work.Drive.EpsForm.sweepHeight ψ ℓ) (p + t • w') - lam)) =
          (Work.Drive.EpsForm.sweepHeight ψ ℓ) (p + t • w') - lam := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt htpos), one_mul]
      have h3 := mul_lt_mul_of_pos_left ht htpos
      rw [h2] at h3
      exact h3
    have h4 : 0 < t * ((fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p w') / 2) :=
      mul_pos htpos (by linarith)
    linarith
  -- the parametrised ray tends to the point
  have hray : Filter.Tendsto (fun t : ℝ => p + t • w') (𝓝 (0 : ℝ)) (𝓝 p) := by
    have hc : Continuous (fun t : ℝ => p + t • w') :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using hc.tendsto 0
  have htend_par : Filter.Tendsto (fun t : ℝ => Work.BoxShrink.Pinch.par ψ (p + t • w'))
      (𝓝[>] (0 : ℝ)) (𝓝 (Work.BoxShrink.Pinch.par ψ p)) :=
    ((continuous_par ψ).tendsto p).comp (hray.mono_left nhdsWithin_le_nhds)
  have hmemPBox : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Work.BoxShrink.Pinch.par ψ (p + t • w') ∈ Submission.PBox s c σ :=
    htend_par.eventually ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hpP)
  have hmemS : ∀ᶠ t in 𝓝[>] (0 : ℝ), Work.BoxShrink.Pinch.par ψ (p + t • w') ∈
      Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ
        u v h ℓ lam := by
    filter_upwards [hmemPBox, hev_ht] with t h1 h2
    have hcar : Work.BoxShrink.Pinch.par ψ (p + t • w') ∈
        (Work.Drive.EpsSphere.torusOf ψ).carrier := by
      rw [← Work.BoxShrink.PinchOff.torus_psi_eq_par]
      exact Work.CoreTopology.ParamTorus.psi_mem_carrier _ _ _
    rw [Work.Drive.Mono.mem_openTiltedSweepRegion_iff]
    refine ⟨hcar, h1, fun hcon => ?_⟩
    rw [sweepHeight_apply] at h2
    exact absurd hcon.2 (not_le.mpr h2)
  rw [mem_closure_iff]
  intro o ho hzo
  haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have h1 : (fun t : ℝ => Work.BoxShrink.Pinch.par ψ (p + t • w')) ⁻¹' o ∈ 𝓝[>] (0 : ℝ) :=
    htend_par.eventually (ho.mem_nhds hzo)
  obtain ⟨t, ht⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 hmemS)
  exact ⟨_, ht.1, ht.2⟩

/-- **L6b's pointwise core.**  A point `z` of the surface which lies in the box `PBox s c σ` and on
the level `ℓ = ℓ D.centre` of the dent datum, and whose parameter point `p` (`par ψ p = z`) is a
regular point of the sweep height, lies in the closure of the dent's preimage region `Ω₁`. -/
theorem mem_closure_dentOutRegion_of_mem_PBox_of_fderiv_ne {ψ : Submission.Diffeo}
    {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    {U : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U)
    {z : LeanEval.KnotTheory.PardonDistortion.R3}
    (hzc : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzb : z ∈ Submission.PBox s c σ) (hzl : ℓ z = ℓ D.centre) {p : ℝ × ℝ}
    (hp : Work.BoxShrink.Pinch.par ψ p = z)
    (hcrit : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0) :
    z ∈ closure (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) := by
  have hmem : Work.BoxShrink.Pinch.par ψ p ∈
      closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
        s c σ u v h ℓ (ℓ D.centre)) :=
    mem_closure_openTiltedSweepRegion_of_fderiv_ne (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u)
      (v := v) (h := h) (ℓ := ℓ) (lam := ℓ D.centre)
      (by rwa [hp]) (by rw [hp]; exact hzl) hcrit
  have hcl : Work.BoxShrink.Pinch.par ψ p ∈
      closure (Work.Drive.Final.dentOutRegion ψ s c σ u v h R ℓ D) :=
    closure_mono (openTiltedSweepRegion_subset_dentOutRegion D) hmem
  rwa [hp] at hcl

end

end Work.Drive.Final
