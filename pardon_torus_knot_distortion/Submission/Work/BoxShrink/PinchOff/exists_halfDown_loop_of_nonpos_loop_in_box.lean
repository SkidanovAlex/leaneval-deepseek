import Mathlib
import Submission.Work.BoxShrink.PinchOff.Basic
import Submission.Work.BoxShrink.Pinch.Basic
import Submission.Work.BoxShrink.PinchOff.trace_loop_in_box_avoiding_plane
import Submission.Work.BoxShrink.PinchOff.TraceInBox

namespace Work.BoxShrink.PinchOff

open LeanEval.KnotTheory.PardonDistortion
open Set

set_option maxHeartbeats 4000000

noncomputable section

/-- **The one-sided push-off, at the level of a compact set of parameters.**

Let `G = planeG ψ c σ u` be the cutting-plane coordinate read in the parameter plane and
`W = descentField ψ (planeCoord c σ u)` the descent field of the plane coordinate.  For a compact
set `K` of parameters on which the box norm is `< s` and the plane coordinate is `≤ 0`, there is a
positive push time `ε` such that the one-step Euler map `q ↦ q + ε • W q` carries every `q ∈ K`
into `{planeG < 0} ∩ {boxB < s}`.

The proof is a compactness argument.  For a point `q` with `G q < 0` the map
`(q', x) ↦ G (q' + x • W q')` is continuous and `< 0` at `(q, 0)`, giving a neighbourhood of `q`
and a positive time; for a point `q` with `G q = 0` the local transversality `hT` makes the
derivative of the level along the segment `t ↦ G (q + t • W q)` strictly negative at `q`, and
continuity of the *pair* map `(p, r) ↦ fderiv G p (W r)` at `(q, q)` yields a neighbourhood of `q`
and a positive time on which the level decreases at a positive rate `cq`.  A finite subcover
supplies the minimum; the box condition uses `‖W‖ ≤ 1`. -/
private theorem exists_push_epsilon_nonpos
    (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hbox : ∀ q ∈ K, Work.BoxShrink.Pinch.boxB ψ c σ q < s)
    (hG : ∀ q ∈ K, Work.BoxShrink.Pinch.planeG ψ c σ u q ≤ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ K,
      Work.BoxShrink.Pinch.planeG ψ c σ u
          (pushMap ψ (Work.BoxShrink.Bubble.planeCoord c σ u) ε q) < 0 ∧
        Work.BoxShrink.Pinch.boxB ψ c σ
          (pushMap ψ (Work.BoxShrink.Bubble.planeCoord c σ u) ε q) < s := by
  classical
  set g : R3 → ℝ := Work.BoxShrink.Bubble.planeCoord c σ u with hg_def
  have hplaneg : Work.BoxShrink.Pinch.planeG ψ c σ u = Work.Smooth.Morse.pullback ψ g := rfl
  have hg2 : ContDiff ℝ 2 g := Work.BoxShrink.Bubble.contDiff_planeCoord c σ u
  have hg1 : ContDiff ℝ 1 g := hg2.of_le (by norm_num)
  have hGd : ContDiff ℝ 1 (Work.Smooth.Morse.pullback ψ g) :=
    Work.Smooth.Morse.pullback_contDiff_one ψ hg1
  have hfdcont : Continuous (fderiv ℝ (Work.Smooth.Morse.pullback ψ g)) :=
    hGd.continuous_fderiv one_ne_zero
  have hWcont : Continuous (Work.Smooth.Morse.descentField ψ g) :=
    (Work.Smooth.Morse.Flow.contDiff_descentField ψ hg2).continuous
  have hWle : ∀ q : ℝ × ℝ, ‖Work.Smooth.Morse.descentField ψ g q‖ ≤ 1 :=
    fun q => Work.Smooth.Morse.Flow.norm_descentField_le_one ψ g q
  -- per-point neighbourhoods with a positive descent time
  have hpoint : ∀ q ∈ K, ∃ εq : ℝ, 0 < εq ∧ ∃ Uq : Set (ℝ × ℝ), IsOpen Uq ∧ q ∈ Uq ∧
      ∀ q' ∈ Uq ∩ K, ∀ x ∈ Set.Ioc (0 : ℝ) εq,
        Work.Smooth.Morse.pullback ψ g (q' + x • Work.Smooth.Morse.descentField ψ g q') < 0 := by
    intro q hq
    rcases lt_or_eq_of_le (hG q hq) with hlt | heq
    · -- case 1: the level is already strictly below zero
      have hcont : Continuous (fun p : (ℝ × ℝ) × ℝ =>
          Work.Smooth.Morse.pullback ψ g
            (p.1 + p.2 • Work.Smooth.Morse.descentField ψ g p.1)) :=
        hGd.continuous.comp (continuous_fst.add
          (continuous_snd.smul (hWcont.comp continuous_fst)))
      have hopen : IsOpen {p : (ℝ × ℝ) × ℝ |
          Work.Smooth.Morse.pullback ψ g
            (p.1 + p.2 • Work.Smooth.Morse.descentField ψ g p.1) < 0} :=
        isOpen_lt hcont continuous_const
      have hmem : (q, (0 : ℝ)) ∈ {p : (ℝ × ℝ) × ℝ |
          Work.Smooth.Morse.pullback ψ g
            (p.1 + p.2 • Work.Smooth.Morse.descentField ψ g p.1) < 0} := by
        simp only [Set.mem_ofPred_eq, zero_smul, add_zero]
        exact hplaneg ▸ hlt
      obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
      refine ⟨r / 2, by linarith, Metric.ball q (r / 2), Metric.isOpen_ball, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_self]; linarith
      · intro q' hq' x hx
        have hd : dist (q', x) (q, (0 : ℝ)) < r := by
          rw [Prod.dist_eq]
          apply max_lt
          · have h1 := hq'.1; rw [Metric.mem_ball] at h1; linarith
          · rw [Real.dist_eq, sub_zero]
            have hx1 : 0 < x := hx.1
            rw [abs_of_pos hx1]
            linarith [hx.2]
        have h1 := hr (Metric.mem_ball.mpr hd)
        show (fun p : (ℝ × ℝ) × ℝ => Work.Smooth.Morse.pullback ψ g
            (p.1 + p.2 • Work.Smooth.Morse.descentField ψ g p.1) < 0) (q', x)
        exact h1
    · -- case 2: the level vanishes at `q`
      have hfd_ne : fderiv ℝ (Work.Smooth.Morse.pullback ψ g) q ≠ 0 := by
        show fderiv ℝ (Work.BoxShrink.Pinch.planeG ψ c σ u) q ≠ 0
        exact hT q (hbox q hq) heq
      have hrate_pos : 0 < Work.Smooth.Morse.descentRate ψ g q :=
        Work.Smooth.Morse.Flow.descentRate_pos_of_fderiv_ne_zero ψ g hfd_ne
      set cq : ℝ := Work.Smooth.Morse.descentRate ψ g q / 2 with hcq_def
      have hcqpos : 0 < cq := by rw [hcq_def]; linarith
      have hcontR : Continuous (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
          fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p.1
            (Work.Smooth.Morse.descentField ψ g p.2)) :=
        (hfdcont.comp continuous_fst).clm_apply (hWcont.comp continuous_snd)
      have hopen : IsOpen {p : (ℝ × ℝ) × (ℝ × ℝ) |
          fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p.1
            (Work.Smooth.Morse.descentField ψ g p.2) < -cq} :=
        isOpen_lt hcontR continuous_const
      have hmem0 : (q, q) ∈ {p : (ℝ × ℝ) × (ℝ × ℝ) |
          fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p.1
            (Work.Smooth.Morse.descentField ψ g p.2) < -cq} := by
        show fderiv ℝ (Work.Smooth.Morse.pullback ψ g) q
            (Work.Smooth.Morse.descentField ψ g q) < -cq
        rw [Work.Smooth.Morse.fderiv_pullback_descentField, hcq_def]
        linarith
      obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem0)
      refine ⟨r / 3, by linarith, Metric.ball q (r / 3), Metric.isOpen_ball, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_self]; linarith
      · intro q' hq' xx hx
        have hqdist : dist q' q < r / 3 := by
          have h1 := hq'.1; rw [Metric.mem_ball] at h1; exact h1
        have hxxle : xx ≤ r / 3 := hx.2
        have hxxpos : 0 < xx := hx.1
        have hbound : ∀ t ∈ Set.Icc (0 : ℝ) xx,
            fderiv ℝ (Work.Smooth.Morse.pullback ψ g)
              (q' + t • Work.Smooth.Morse.descentField ψ g q')
              (Work.Smooth.Morse.descentField ψ g q') < -cq := by
          intro t ht
          have htabs : |t| ≤ r / 3 := by
            rw [abs_of_nonneg ht.1]; linarith [ht.2]
          have hd1 : dist (q' + t • Work.Smooth.Morse.descentField ψ g q') q' ≤ |t| := by
            rw [dist_eq_norm]
            have hsub : q' + t • Work.Smooth.Morse.descentField ψ g q' - q'
                = t • Work.Smooth.Morse.descentField ψ g q' := by abel
            rw [hsub, norm_smul, Real.norm_eq_abs]
            calc |t| * ‖Work.Smooth.Morse.descentField ψ g q'‖ ≤ |t| * 1 := by
                  gcongr; exact hWle q'
              _ = |t| := mul_one _
          have hmemr : (q' + t • Work.Smooth.Morse.descentField ψ g q', q') ∈
              Metric.ball (q, q) r := by
            rw [Metric.mem_ball, Prod.dist_eq]
            apply max_lt
            · show dist (q' + t • Work.Smooth.Morse.descentField ψ g q') q < r
              calc dist (q' + t • Work.Smooth.Morse.descentField ψ g q') q
                  ≤ dist (q' + t • Work.Smooth.Morse.descentField ψ g q') q' + dist q' q :=
                    dist_triangle _ _ _
                _ ≤ |t| + dist q' q := by linarith [hd1]
                _ < r := by nlinarith [htabs, hqdist]
            · show dist q' q < r
              linarith
          have h1 := hr hmemr
          show (fun p : (ℝ × ℝ) × (ℝ × ℝ) => fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p.1
              (Work.Smooth.Morse.descentField ψ g p.2) < -cq)
              (q' + t • Work.Smooth.Morse.descentField ψ g q', q')
          exact h1
        let f : ℝ → ℝ := fun t => Work.Smooth.Morse.pullback ψ g
          (q' + t • Work.Smooth.Morse.descentField ψ g q')
        have hfderiv : ∀ t : ℝ, HasDerivAt f
            (fderiv ℝ (Work.Smooth.Morse.pullback ψ g)
              (q' + t • Work.Smooth.Morse.descentField ψ g q')
              (Work.Smooth.Morse.descentField ψ g q')) t := by
          intro t
          have hline : HasDerivAt
              (fun τ : ℝ => q' + τ • Work.Smooth.Morse.descentField ψ g q')
              (Work.Smooth.Morse.descentField ψ g q') t := by
            have h := ((hasDerivAt_id t).smul_const
              (Work.Smooth.Morse.descentField ψ g q')).const_add q'
            simpa using h
          have hGat : DifferentiableAt ℝ (Work.Smooth.Morse.pullback ψ g)
              (q' + t • Work.Smooth.Morse.descentField ψ g q') :=
            (hGd.differentiable one_ne_zero).differentiableAt
          exact (hGat.hasFDerivAt).comp_hasDerivAt t hline
        have hcontf : ContinuousOn f (Set.Icc (0 : ℝ) xx) := by
          have hc : Continuous f := hGd.continuous.comp
            (continuous_const.add (continuous_id.smul continuous_const))
          exact hc.continuousOn
        have hdiff : DifferentiableOn ℝ f (interior (Set.Icc (0 : ℝ) xx)) :=
          fun t _ => ((hfderiv t).differentiableAt).differentiableWithinAt
        have hderiv : ∀ t ∈ interior (Set.Icc (0 : ℝ) xx), deriv f t ≤ -cq := by
          intro t ht
          rw [(hfderiv t).deriv]
          exact le_of_lt (hbound t (interior_subset ht))
        have hkey := (convex_Icc (0 : ℝ) xx).image_sub_le_mul_sub_of_deriv_le hcontf hdiff
          (C := -cq) hderiv 0 ⟨le_rfl, hxxpos.le⟩ xx ⟨hxxpos.le, le_rfl⟩ hxxpos.le
        have hf0 : f 0 = Work.Smooth.Morse.pullback ψ g q' := by simp [f]
        have hGq' : Work.Smooth.Morse.pullback ψ g q' ≤ 0 := hplaneg ▸ hG q' hq'.2
        have hfx : f xx < 0 := by nlinarith [hkey, hf0, hGq', hcqpos, hxxpos]
        show Work.Smooth.Morse.pullback ψ g
          (q' + xx • Work.Smooth.Morse.descentField ψ g q') < 0
        simpa [f] using hfx
  -- assemble the finite subcover
  let E : K → ℝ := fun i => Classical.choose (hpoint i.val i.property)
  have hE : ∀ i : K, 0 < E i ∧ ∃ Uq : Set (ℝ × ℝ), IsOpen Uq ∧ i.val ∈ Uq ∧
      ∀ q' ∈ Uq ∩ K, ∀ x ∈ Set.Ioc (0 : ℝ) (E i),
        Work.Smooth.Morse.pullback ψ g
          (q' + x • Work.Smooth.Morse.descentField ψ g q') < 0 :=
    fun i => Classical.choose_spec (hpoint i.val i.property)
  let U : K → Set (ℝ × ℝ) := fun i => Classical.choose (hE i).2
  have hU : ∀ i : K, IsOpen (U i) ∧ i.val ∈ U i ∧
      ∀ q' ∈ U i ∩ K, ∀ x ∈ Set.Ioc (0 : ℝ) (E i),
        Work.Smooth.Morse.pullback ψ g
          (q' + x • Work.Smooth.Morse.descentField ψ g q') < 0 :=
    fun i => Classical.choose_spec (hE i).2
  by_cases hKne : K.Nonempty
  · have hcover : K ⊆ ⋃ i : K, U i :=
      fun q hq => Set.mem_iUnion.mpr ⟨⟨q, hq⟩, (hU ⟨q, hq⟩).2.1⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover U (fun i => (hU i).1) hcover
    have htne : t.Nonempty := by
      rcases hKne with ⟨q, hq⟩
      rcases Set.mem_iUnion₂.mp (ht hq) with ⟨i, hi, _⟩
      exact ⟨i, hi⟩
    have hOb : IsOpen {p : ℝ × ℝ | Work.BoxShrink.Pinch.boxB ψ c σ p < s} :=
      isOpen_lt (Work.BoxShrink.Pinch.boxB_continuous ψ c σ) continuous_const
    obtain ⟨ρb, hρbpos, hρb⟩ := hK.exists_cthickening_subset_open hOb hbox
    have hε0pos : 0 < t.inf' htne E := by
      rw [Finset.lt_inf'_iff htne]
      intro i _
      exact (hE i).1
    refine ⟨min (t.inf' htne E) ρb, lt_min hε0pos hρbpos, ?_⟩
    intro q hq
    rcases Set.mem_iUnion₂.mp (ht hq) with ⟨i, hi, hqi⟩
    have hεle : min (t.inf' htne E) ρb ≤ E i :=
      le_trans (min_le_left _ _) (Finset.inf'_le E hi)
    have hεpos : 0 < min (t.inf' htne E) ρb := lt_min hε0pos hρbpos
    have hxIoc : min (t.inf' htne E) ρb ∈ Set.Ioc (0 : ℝ) (E i) := ⟨hεpos, hεle⟩
    have hlt := (hU i).2.2 q ⟨hqi, hq⟩ (min (t.inf' htne E) ρb) hxIoc
    constructor
    · exact hlt
    · apply hρb
      refine Metric.mem_cthickening_of_dist_le
        (pushMap ψ (Work.BoxShrink.Bubble.planeCoord c σ u) (min (t.inf' htne E) ρb) q)
        q ρb K hq ?_
      rw [dist_eq_norm]
      have hsub : pushMap ψ (Work.BoxShrink.Bubble.planeCoord c σ u)
            (min (t.inf' htne E) ρb) q - q
          = min (t.inf' htne E) ρb •
              Work.Smooth.Morse.descentField ψ (Work.BoxShrink.Bubble.planeCoord c σ u) q := by
        simp only [pushMap]; abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hεpos.le]
      calc min (t.inf' htne E) ρb *
              ‖Work.Smooth.Morse.descentField ψ (Work.BoxShrink.Bubble.planeCoord c σ u) q‖
            ≤ min (t.inf' htne E) ρb * 1 := by
              gcongr
              exact Work.Smooth.Morse.Flow.norm_descentField_le_one ψ
                (Work.BoxShrink.Bubble.planeCoord c σ u) q
        _ = min (t.inf' htne E) ρb := mul_one _
        _ ≤ ρb := min_le_right _ _
  · refine ⟨1, one_pos, ?_⟩
    intro q hq
    exact absurd ⟨q, hq⟩ hKne

/-- **The one-sided push-off of a loop of the box region (lower side).**  Let `ψ` be a smooth
configuration of the challenge, `Ω = F ∩ PBox s c σ` the region of the surface inside the box, and
`γ` a closed curve of the surface whose image lies in `Ω` and which satisfies
`(γ t) (σ 2) ≤ c (σ 2) + u` for all `t` (it lies on or below the cutting plane).  If the cutting
plane is transverse to the surface along the slice *inside the box* (`TransverseSlice`), then `γ` is
homotopic in the surface to a closed curve of the **lower half-region**
`Ω₋ = F ∩ PBox s c σ ∩ {y (σ 2) < c (σ 2) + u}`, with the *same* winding vector.

This is the one-sided generalization of the already proved
`Work.BoxShrink.PinchOff.trace_loop_in_box_avoiding_plane` (which handles a loop lying *in* the
trace of the cutting plane, and needs the *global* transversality hypothesis `TransverseTrace`, which
is refuted for all configurations by `not_forall_transverseTrace`).  The proof is the same: the
descent field `W = -((1 + |∇G|²))⁻¹ ∇G` of the plane coordinate, pushed for a small time `ε`.  For a
point `q` with `G q ≤ 0` one has `G (q + ε W q) < 0`: the descent rate is nonnegative everywhere, so
`G` does not increase, and where `G q = 0` the box-local transversality gives a positive lower bound
`δ` for the descent rate on the compact set of trace points of the image of `γ`, whence
`G (q + ε W q) ≤ -(δ/2) ε` there.  The push stays inside the open box for `ε` small (the image of `γ`
is a compact subset of the open box and `‖W‖ ≤ 1`), and the winding vector is preserved because the
push is equivariant for the period lattice.

The point of the *box-local* hypothesis (in place of the refuted global one) is that this statement is
applicable at the configurations of the challenge; it makes the discharged case of the pinch residual
of `Work.BoxShrink.PinchOff.TraceInBox` (`traceMultipleRealisable_of_trace_loop_in_box`) usable
there. -/
theorem exists_halfDown_loop_of_nonpos_loop_in_box {ψ : Submission.Diffeo} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ))
    (hbox : ∀ t : ℝ, γ t ∈ Work.BoxShrink.PinchOff.Omega ψ s c σ)
    (hle : ∀ t : ℝ, (γ t) (σ 2) ≤ c (σ 2) + u) :
    ∃ γ' : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
      (∀ t : ℝ, γ' t ∈ Work.BoxShrink.PinchOff.HalfDown ψ s c σ u) ∧
      Work.SurgeryInvariance.windingOf (Work.Smooth.Morse.torus ψ) γ' =
        Work.SurgeryInvariance.windingOf (Work.Smooth.Morse.torus ψ) γ := by
  classical
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf (Work.Smooth.Morse.torus ψ) γ
  let Lp : ℝ → ℝ × ℝ := fun t => (L.Θ t, L.Φ t)
  have hLpc : Continuous Lp := L.contΘ.prodMk L.contΦ
  let K : Set (ℝ × ℝ) := Lp '' Set.Icc (0 : ℝ) (2 * Real.pi)
  have hK : IsCompact K := isCompact_Icc.image hLpc
  have hlift : ∀ t : ℝ, Work.BoxShrink.Pinch.par ψ (Lp t) = γ t := by
    intro t
    show (Work.Smooth.Morse.torus ψ).psi (L.Θ t) (L.Φ t) = γ.γ t
    exact L.lifts t
  have hboxK : ∀ q ∈ K, Work.BoxShrink.Pinch.boxB ψ c σ q < s := by
    rintro q ⟨t, -, rfl⟩
    have h1 : Lp t ∈ Work.BoxShrink.Pinch.par ψ ⁻¹'
        Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ := by
      rw [Set.mem_preimage, hlift t]
      exact hbox t
    rwa [Work.BoxShrink.Pinch.preimage_boxRegion] at h1
  have hGK : ∀ q ∈ K, Work.BoxShrink.Pinch.planeG ψ c σ u q ≤ 0 := by
    rintro q ⟨t, -, rfl⟩
    rw [Work.BoxShrink.Pinch.planeG_apply, hlift t, Work.BoxShrink.Bubble.planeCoord_apply]
    linarith [hle t]
  obtain ⟨ε, hεpos, hε⟩ :=
    exists_push_epsilon_nonpos ψ s c σ u hT hK hboxK hGK
  have hWcont : Continuous
      (Work.Smooth.Morse.descentField ψ (Work.BoxShrink.Bubble.planeCoord c σ u)) :=
    (Work.Smooth.Morse.Flow.contDiff_descentField ψ
      (Work.BoxShrink.Bubble.contDiff_planeCoord c σ u)).continuous
  obtain ⟨_, _, hWle, hWper⟩ :=
    Work.Smooth.Morse.Flow.lipschitzWith_descentField ψ
      (Work.BoxShrink.Bubble.contDiff_planeCoord c σ u)
  obtain ⟨γ', hγ'apply, hγ'wind⟩ :=
    Work.BoxShrink.Bubble.Flow.exists_curve_of_periodicFlow (Work.Smooth.Morse.torus ψ)
      (fun (_ : ℝ) (q : ℝ × ℝ) => pushMap ψ (Work.BoxShrink.Bubble.planeCoord c σ u) ε q)
      (by
        have hc : Continuous (fun p : ℝ × (ℝ × ℝ) =>
            p.2 + ε • Work.Smooth.Morse.descentField ψ
              (Work.BoxShrink.Bubble.planeCoord c σ u) p.2) :=
          continuous_snd.add
            ((continuous_const : Continuous fun _ : ℝ × (ℝ × ℝ) => ε).smul
              (hWcont.comp continuous_snd))
        exact hc)
      (by
        intro r q k l
        have hp := hWper q k l
        show (q.1 + ↑k * (2 * Real.pi), q.2 + ↑l * (2 * Real.pi)) + ε •
              Work.Smooth.Morse.descentField ψ (Work.BoxShrink.Bubble.planeCoord c σ u)
                (q.1 + ↑k * (2 * Real.pi), q.2 + ↑l * (2 * Real.pi)) =
            ((q + ε • Work.Smooth.Morse.descentField ψ
                (Work.BoxShrink.Bubble.planeCoord c σ u) q).1 + ↑k * (2 * Real.pi),
              (q + ε • Work.Smooth.Morse.descentField ψ
                (Work.BoxShrink.Bubble.planeCoord c σ u) q).2 + ↑l * (2 * Real.pi))
        rw [hp]
        ext <;> simp <;> ring)
      L
  refine ⟨γ', ?_, ?_⟩
  · intro t
    have hper : Function.Periodic γ'.γ (2 * Real.pi) := γ'.periodic
    set k : ℤ := ⌊t / (2 * Real.pi)⌋ with hk
    set t' : ℝ := t - (k : ℝ) * (2 * Real.pi) with ht'
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have ht'mem : t' ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
      constructor
      · have h := Int.floor_le (t / (2 * Real.pi))
        rw [← hk] at h
        have h2 : (k : ℝ) * (2 * Real.pi) ≤ (t / (2 * Real.pi)) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right h hπ.le
        rw [div_mul_cancel₀ _ (ne_of_gt hπ)] at h2
        simp only [ht']
        linarith
      · have h := Int.lt_floor_add_one (t / (2 * Real.pi))
        rw [← hk] at h
        have h3 : (t / (2 * Real.pi)) * (2 * Real.pi) < ((k : ℝ) + 1) * (2 * Real.pi) :=
          mul_lt_mul_of_pos_right h hπ
        rw [div_mul_cancel₀ _ (ne_of_gt hπ)] at h3
        simp only [ht']
        linarith
    have ht_eq : t = t' + (k : ℝ) * (2 * Real.pi) := by simp only [ht']; ring
    rw [ht_eq, (hper.int_mul k) t']
    have hq : Lp t' ∈ K := ⟨t', ht'mem, rfl⟩
    have hε' := hε (Lp t') hq
    rw [hγ'apply t']
    have hmem : Work.BoxShrink.Pinch.par ψ
        (pushMap ψ (Work.BoxShrink.Bubble.planeCoord c σ u) ε (Lp t')) ∈
        Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u := by
      rw [← Set.mem_preimage, Work.BoxShrink.Pinch.preimage_lowerRegion]
      exact ⟨hε'.2, hε'.1⟩
    rw [torus_psi_eq_par ψ (pushMap ψ (Work.BoxShrink.Bubble.planeCoord c σ u) ε (Lp t'))]
    exact hmem
  · rw [hγ'wind, ← Work.SurgeryInvariance.windingOf_eq (Work.Smooth.Morse.torus ψ) γ L]

end

end Work.BoxShrink.PinchOff
