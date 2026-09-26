import Mathlib
import Submission.Work.Drive.Final.sweep_mono
import Submission.Work.Drive.Mono.Split
import Submission.Work.Topology.SphereSlicing.convex_PBox
import Submission.Work.Topology.SphereSlicing.isOpen_PBox

/-!
# Clause 2 of the trace data is free at every level that cuts the box

`Work.Drive.Mono.AboveGenericAt` (clause 2 of the tilted-sweep trace data) asks: every point of the
surface which lies in the **closure** of the box `PBox s c σ`, in the closed tilted slab, and on the
level `lam`, is either a limit of points of the level's region

  `X lam = P.carrier ∩ (PBox ∖ (slabClosed ∩ {ℓ ≤ lam}))`

or lies on the trace `P.carrier ∩ frontier (tiltedLevelRemoved … lam)`.

The clause is **not** a consequence of the genericity alone: at a level above the whole box and with
the box inside the slab the region and the trace are both empty, and the clause fails at every point
(`Submission/Work/Drive/Mono/NOTES_AboveGeneric_REFUTED.md`).  The missing hypothesis is that the
level **cuts the box**,

  `∃ y ∈ PBox s c σ, lam < ℓ y`,

and with it the clause is a theorem — this file proves that.  The proof is the one sketched in §3 of
the refutation note:

* at a point `z` *inside* the box, `z` is a regular point of the sweep height (`lam ∉ exc`, clause
  (i) of `Work.Drive.Final.TiltedGenericity`), so a small push of the parameter point along a
  direction in which the height increases strictly gives points of the surface in the box with
  `ℓ > lam`, i.e. points of the region, tending to `z`;
* at a point `z` on `∂PBox`, take `y ∈ PBox` with `ℓ y > lam` (the new hypothesis) and run the
  *segment* from `y` to `z`: its interior lies in the open box by convexity, its levels are `> lam`,
  and it tends to `z`, so `z ∈ closure (tiltedLevelRemoved … lam)`; and `z` is not in the interior of
  that set because it is not even in the box.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped Topology

namespace Work.Drive.Final

noncomputable section

variable {ψ : Submission.Diffeo} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
  {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam : ℝ}

/-- The sweep height is `ℓ` read on the parametrisation. -/
theorem sweepHeight_apply (ψ : Submission.Diffeo) (ℓ : R3 →L[ℝ] ℝ) (q : ℝ × ℝ) :
    Work.Drive.EpsForm.sweepHeight ψ ℓ q = ℓ (Work.BoxShrink.Pinch.par ψ q) := rfl

/-- The parametrisation `Work.BoxShrink.Pinch.par ψ` is continuous. -/
theorem continuous_par (ψ : Submission.Diffeo) : Continuous (Work.BoxShrink.Pinch.par ψ) := by
  have h : Continuous (fun q : ℝ × ℝ => (Work.Smooth.Morse.torus ψ).psi q.1 q.2) :=
    (Work.Smooth.Morse.torus ψ).cont
  simpa [Work.BoxShrink.Pinch.par, Work.BoxShrink.PinchOff.torus_psi_eq_par] using h

/-- A point of the closure of the box has its coordinates bounded by the box half-widths. -/
theorem abs_coord_le_of_mem_closure_PBox {z : R3} (hz : z ∈ closure (Submission.PBox s c σ))
    (i : Fin 3) :
    |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s :=
  closure_minimal (fun w hw => le_of_lt ((Submission.mem_PBox.mp hw) i))
    (isClosed_le (f := fun w : R3 => |w (σ i) - c (σ i)|)
      (g := fun _ : R3 => Submission.boxSide i * s) (by fun_prop) continuous_const) hz

/-- **The level region contains points of the surface tending to a point of the slab at which the
sweep height is regular.**  This is the first case of the argument: the derivative of the height at
the parameter point of `z` is non-zero, so pushing the parameter along a direction of strict increase
gives points of the box with level `> lam`, i.e. points of the region. -/
theorem mem_closure_openTiltedSweepRegion_of_regular (p : ℝ × ℝ)
    (hpP : Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ)
    (hpslab : |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| ≤ h)
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

/-- **Clause 2 of the trace data is free at every level at which the sweep height is regular on
the level's part of the box.**  This is the general form of the lemma below: the hypothesis is
directly that the height has non-vanishing derivative at every point of the surface in the (closed)
box and the closed slab at the level `lam`; the second hypothesis says that either the level cuts the
box, or the box pokes out of the slab (the latter is what is needed at the top of the box's
`ℓ`-range, where no point of the box lies above the level).

Neither hypothesis refers to the exceptional set: the lemma applies at *every* level at which the
level points are regular, which is exactly the case at which the pinch's dent is not needed. -/
theorem aboveGenericAt_of_mem_closure_levelRegion
    (hin : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| ≤ h →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
      Work.BoxShrink.Pinch.par ψ p ∈ closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion
        (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam))
    (hcut : ∃ y ∈ Submission.PBox s c σ, lam < ℓ y) :
    Work.Drive.Mono.AboveGenericAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  intro z hzc hzcl hslab hlam
  by_cases hzP : z ∈ Submission.PBox s c σ
  · -- inside the box: the regularity of the sweep height gives points of the region
    obtain ⟨x, y, hxy⟩ :=
      (Work.CoreTopology.ParamTorus.mem_carrier_iff (Work.Drive.EpsSphere.torusOf ψ) z).mp hzc
    have hpar : Work.BoxShrink.Pinch.par ψ (x, y) = z := by
      rw [← Work.BoxShrink.PinchOff.torus_psi_eq_par]
      exact hxy
    refine Or.inl ?_
    rw [← hpar]
    exact hin (x, y) (by rwa [hpar]) (by rwa [hpar]) (by rw [hpar]; exact hlam)
  · -- on the boundary of the box: the segment to a suitable point of the box
    obtain ⟨y, hyP, hycase⟩ := hcut
    refine Or.inr ⟨hzc, ?_⟩
    rw [frontier_eq_closure_inter_closure]
    refine ⟨?_, ?_⟩
    · rw [mem_closure_iff]
      intro o ho hzo
      set g : ℝ → R3 := fun t => (1 - t) • z + t • y with hgdef
      have hgcont : Continuous g := by
        rw [hgdef]
        exact ((continuous_const.sub continuous_id).smul continuous_const).add
          (continuous_id.smul continuous_const)
      have hgtend : Filter.Tendsto g (𝓝 (0 : ℝ)) (𝓝 z) := by
        have h0 : g 0 = z := by simp [hgdef]
        simpa [h0] using hgcont.tendsto 0
      have hev_lt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          ((isOpen_Iio (a := (1 : ℝ))).mem_nhds (by norm_num : (0 : ℝ) ∈ Set.Iio 1))
      have hmemR : ∀ᶠ t in 𝓝[>] (0 : ℝ),
          g t ∈ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam := by
        filter_upwards [hev_lt, self_mem_nhdsWithin] with t ht htpos
        have hgval : ∀ i : Fin 3,
            |g t (σ i) - c (σ i)| ≤ (1 - t) * |z (σ i) - c (σ i)| + t * |y (σ i) - c (σ i)| := by
          intro i
          have h1 : g t (σ i) - c (σ i) =
              (1 - t) * (z (σ i) - c (σ i)) + t * (y (σ i) - c (σ i)) := by
            simp only [hgdef, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
            ring
          calc |g t (σ i) - c (σ i)|
              = |(1 - t) * (z (σ i) - c (σ i)) + t * (y (σ i) - c (σ i))| := by rw [h1]
            _ ≤ |(1 - t) * (z (σ i) - c (σ i))| + |t * (y (σ i) - c (σ i))| := abs_add_le _ _
            _ = (1 - t) * |z (σ i) - c (σ i)| + t * |y (σ i) - c (σ i)| := by
                have h1t : (0 : ℝ) < 1 - t := by linarith
                have ht0 : (0 : ℝ) < t := htpos
                simp only [abs_mul, abs_of_pos h1t, abs_of_pos ht0]
        have hgPBox : g t ∈ Submission.PBox s c σ := by
          rw [Submission.mem_PBox]
          intro i
          have h1 := hgval i
          have h2 : |y (σ i) - c (σ i)| < Submission.boxSide i * s :=
            Submission.mem_PBox.mp hyP i
          have h3 := abs_coord_le_of_mem_closure_PBox (s := s) (c := c) (σ := σ) hzcl i
          have h4 : t * |y (σ i) - c (σ i)| < t * (Submission.boxSide i * s) :=
            mul_lt_mul_of_pos_left h2 htpos
          have h5 : (1 - t) * |z (σ i) - c (σ i)| ≤
              (1 - t) * (Submission.boxSide i * s) :=
            mul_le_mul_of_nonneg_left h3 (by linarith)
          linarith
        rw [Work.Drive.Mono.tiltedLevelRemoved]
        refine ⟨hgPBox, fun hcon => ?_⟩
        have hℓgt : lam < ℓ (g t) := by
          have h1 : ℓ (g t) = (1 - t) * ℓ z + t * ℓ y := by
            simp only [hgdef, map_add, map_smul, smul_eq_mul]
          have ht0 : (0 : ℝ) < t := htpos
          have hkey : 0 < t * (ℓ y - lam) := mul_pos ht0 (sub_pos.mpr hycase)
          rw [h1, hlam]
          linarith
        exact absurd hcon.2 (not_lt.mpr (le_of_lt hℓgt))
      haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
      have h1 : g ⁻¹' o ∈ 𝓝[>] (0 : ℝ) :=
        (hgtend.mono_left nhdsWithin_le_nhds).eventually (ho.mem_nhds hzo)
      obtain ⟨t, ht⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 hmemR)
      exact ⟨_, ht.1, ht.2⟩
    · rw [closure_compl]
      intro hint
      exact hzP (Set.sdiff_subset (interior_subset hint))

/-- **The regular case**: if the sweep height is regular at every point of the surface in the box
and the closed slab at the level `lam`, and the level cuts the box, then clause 2 holds. -/
theorem aboveGenericAt_of_regularLevel
    (hreg : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| ≤ h →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0)
    (hcut : ∃ y ∈ Submission.PBox s c σ, lam < ℓ y) :
    Work.Drive.Mono.AboveGenericAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam :=
  aboveGenericAt_of_mem_closure_levelRegion
    (fun p hpP hpslab hpℓ => mem_closure_openTiltedSweepRegion_of_regular p hpP hpslab hpℓ
      (hreg p hpP hpslab hpℓ)) hcut

theorem aboveGenericAt_of_tiltedGenericity_of_cutBox
    (hT : TiltedGenericity ψ s c σ u v h ℓ exc) (hnotexc : lam ∉ (exc : Set ℝ))
    (hcut : ∃ y ∈ Submission.PBox s c σ, lam < ℓ y) :
    Work.Drive.Mono.AboveGenericAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  obtain ⟨hregime, -, -, -⟩ := hT
  exact aboveGenericAt_of_regularLevel
    (fun p hpP hpslab hpℓ => hregime lam hnotexc p hpP hpslab hpℓ)
    hcut


/-- **The cover clause with the box-sphere trace on the right.**  The `∂PBox` half of
`aboveGenericAt_of_regularLevel` (and of `Work.Drive.Mono.AboveGenericAt`) can be discharged by *any*
family of closed curves covering `carrier ∩ frontier (PBox)`, and it is convenient to use the
box-sphere trace `Γ = carrier ∩ ∂PBox`: by the crux's counting it is a family of pairwise disjoint
simple **inessential** closed curves (`Work.EpsW.sphereTrace_inessential_of_countsWd`), whereas the
level trace of a saddle level is not.

So at every level which is regular on the box part of the surface and cuts the box, the clause holds
with the box-sphere trace in place of the level trace: the level's own trace then enters only through
the *clopen* clause `closure Ω ∩ (P.carrier ∖ ⋃ cs) = Ω` of
`Work.Drive.Final.noJumpBelow_of_region`. -/
theorem aboveGenericAt_of_regularLevel_of_boxTrace
    {n : ℕ} {cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)}
    (hreg : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| ≤ h →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0)
    (hcut : ∃ y ∈ Submission.PBox s c σ, lam < ℓ y)
    (hcover : (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier (Submission.PBox s c σ) ⊆
      ⋃ i, Set.range (cs i).γ) :
    ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lam →
      z ∈ closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion
            (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) ∪ ⋃ i, Set.range (cs i).γ := by
  intro z hzc hzcl hslab hlam
  by_cases hzP : z ∈ Submission.PBox s c σ
  · refine Or.inl ?_
    obtain ⟨x, y, hxy⟩ :=
      (Work.CoreTopology.ParamTorus.mem_carrier_iff (Work.Drive.EpsSphere.torusOf ψ) z).mp hzc
    have hpar : Work.BoxShrink.Pinch.par ψ (x, y) = z := by
      rw [← Work.BoxShrink.PinchOff.torus_psi_eq_par]
      exact hxy
    rw [← hpar]
    refine mem_closure_openTiltedSweepRegion_of_regular (ψ := ψ) (s := s) (c := c) (σ := σ)
      (u := u) (v := v) (h := h) (ℓ := ℓ) (lam := lam) (x, y) ?_ ?_ ?_ ?_
    · rwa [hpar]
    · rwa [hpar]
    · rw [hpar]; exact hlam
    · exact hreg (x, y) (by rwa [hpar]) (by rwa [hpar]) (by rw [hpar]; exact hlam)
  · -- on the boundary of the box: the box-sphere trace covers it
    refine Or.inr (hcover ⟨hzc, ?_⟩)
    rw [frontier_eq_closure_inter_closure]
    exact ⟨hzcl, by rw [closure_compl]; exact fun hcon => hzP (interior_subset hcon)⟩


end

end Work.Drive.Final
