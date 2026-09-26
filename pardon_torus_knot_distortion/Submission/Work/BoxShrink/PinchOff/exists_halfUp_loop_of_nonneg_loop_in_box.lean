import Mathlib
import Submission.Work.BoxShrink.PinchOff.Basic
import Submission.Work.BoxShrink.Pinch.Basic
import Submission.Work.BoxShrink.PinchOff.trace_loop_in_box_avoiding_plane
import Submission.Work.BoxShrink.PinchOff.exists_halfDown_loop_of_nonpos_loop_in_box

namespace Work.BoxShrink.PinchOff

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **The one-step push of a parameter along the ascent field of `g`**: the descent field of `-g`,
i.e. `q ↦ q + ε • descentField ψ (-g) q`.  Since `descentField ψ (-g) = +((1+|∇G|²))⁻¹ ∇G`
(with `G = pullback ψ g`), the level of `G` does not decrease along its flow, and it increases
strictly at the regular points of `G`. -/
def pushMapUp (ψ : Submission.Diffeo) (g : R3 → ℝ) (ε : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  q + ε • Work.Smooth.Morse.descentField ψ (-g) q

theorem pullback_neg (ψ : Submission.Diffeo) (g : R3 → ℝ) :
    Work.Smooth.Morse.pullback ψ (-g) = -Work.Smooth.Morse.pullback ψ g := by
  funext p
  rfl

theorem partialD₁_neg (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) :
    Work.Smooth.Morse.partialD₁ ψ (-g) p = -Work.Smooth.Morse.partialD₁ ψ g p := by
  simp only [Work.Smooth.Morse.partialD₁, pullback_neg, fderiv_neg, neg_apply]

theorem partialD₂_neg (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) :
    Work.Smooth.Morse.partialD₂ ψ (-g) p = -Work.Smooth.Morse.partialD₂ ψ g p := by
  simp only [Work.Smooth.Morse.partialD₂, pullback_neg, fderiv_neg, neg_apply]

theorem descentRate_neg (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) :
    Work.Smooth.Morse.descentRate ψ (-g) p = Work.Smooth.Morse.descentRate ψ g p := by
  simp only [Work.Smooth.Morse.descentRate, partialD₁_neg, partialD₂_neg]
  ring

/-- **The ascent field of `g` raises the level of `G = pullback ψ g` at the rate
`descentRate ψ g ≥ 0`.** -/
theorem fderiv_pullback_ascentField (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p (Work.Smooth.Morse.descentField ψ (-g) p) =
      Work.Smooth.Morse.descentRate ψ g p := by
  have h := Work.Smooth.Morse.fderiv_pullback_descentField ψ (-g) p
  rw [pullback_neg, fderiv_neg] at h
  simp only [neg_apply] at h
  rw [descentRate_neg] at h
  exact neg_inj.mp h

/-! ## The per-point push-time along the ascent field

Both cases of the compactness argument only use that the level of `G` along the one-step push
`q ↦ q + x • W q` is *continuous* in the pair `(q, x)` (so the set where it is `> 0` is open) and,
at the trace points of `G` (where `G = 0`), that the derivative of the level along the segment
`t ↦ q + t • W q` is *strictly positive* at the diagonal: `fderiv ℝ G q (W q) > 0`. -/

/-- **A positive push time at a single parameter.**  Let `G` be a `C¹` function of the parameter
plane, `W` a continuous field, `K` a set on which `G ≥ 0`, and `q ∈ K` a point at which either
`G q > 0` or `fderiv ℝ G q (W q) > 0`.  Then for every parameter `q' ∈ K` close enough to `q` and
every small enough positive time `x`, the one-step push `q' + x • W q'` lands strictly in
`{G > 0}`. -/
private theorem exists_push_time_at_point
    {G : ℝ × ℝ → ℝ} {W : ℝ × ℝ → ℝ × ℝ}
    (hGd : ContDiff ℝ 1 G) (hWc : Continuous W)
    {K : Set (ℝ × ℝ)} (hGK : ∀ q ∈ K, 0 ≤ G q)
    {q : ℝ × ℝ} (hq : q ∈ K)
    (hpos : G q = 0 → 0 < fderiv ℝ G q (W q)) :
    ∃ εq : ℝ, 0 < εq ∧
      ∀ q' ∈ K, dist q' q < εq → ∀ x ∈ Set.Ioc (0 : ℝ) εq, 0 < G (q' + x • W q') := by
  rcases lt_or_eq_of_le (hGK q hq) with hgt | heq
  · -- case 1: the level is already strictly above zero
    have hcont : Continuous (fun p : (ℝ × ℝ) × ℝ => G (p.1 + p.2 • W p.1)) :=
      hGd.continuous.comp (continuous_fst.add (continuous_snd.smul (hWc.comp continuous_fst)))
    have hopen : IsOpen {p : (ℝ × ℝ) × ℝ | 0 < G (p.1 + p.2 • W p.1)} :=
      isOpen_lt continuous_const hcont
    have hmem : (q, (0 : ℝ)) ∈ {p : (ℝ × ℝ) × ℝ | 0 < G (p.1 + p.2 • W p.1)} := by
      simp only [Set.mem_ofPred_eq, zero_smul, add_zero]
      exact hgt
    obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
    refine ⟨r / 2, by linarith, ?_⟩
    intro q' _ hdist x hx
    have hd : dist (q', x) (q, (0 : ℝ)) < r := by
      rw [Prod.dist_eq]
      apply max_lt
      · linarith
      · rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]; linarith [hx.2]
    exact hr (Metric.mem_ball.mpr hd)
  · -- case 2: the level vanishes at `q`, and the ascent rate is strictly positive there
    have hfdpos : 0 < fderiv ℝ G q (W q) := hpos heq.symm
    set cq : ℝ := fderiv ℝ G q (W q) / 2 with hcq
    have hcqpos : 0 < cq := by rw [hcq]; linarith
    have hfdcont : Continuous (fderiv ℝ G) := hGd.continuous_fderiv one_ne_zero
    have hcontR : Continuous (fun p : (ℝ × ℝ) × ℝ =>
        fderiv ℝ G (p.1 + p.2 • W p.1) (W p.1)) :=
      (hfdcont.comp (continuous_fst.add (continuous_snd.smul (hWc.comp continuous_fst)))).clm_apply
        (hWc.comp continuous_fst)
    have hopen : IsOpen {p : (ℝ × ℝ) × ℝ |
        cq < fderiv ℝ G (p.1 + p.2 • W p.1) (W p.1)} :=
      isOpen_lt continuous_const hcontR
    have hmem0 : (q, (0 : ℝ)) ∈ {p : (ℝ × ℝ) × ℝ |
        cq < fderiv ℝ G (p.1 + p.2 • W p.1) (W p.1)} := by
      simp only [Set.mem_ofPred_eq]
      have hz : q + (0 : ℝ) • W q = q := by simp
      rw [hz, hcq]
      linarith
    obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem0)
    refine ⟨r / 2, by linarith, ?_⟩
    intro q' hq' hqdist xx hx
    have hxxle : xx ≤ r / 2 := hx.2
    have hxxpos : 0 < xx := hx.1
    have hbound : ∀ t ∈ Set.Icc (0 : ℝ) xx,
        cq < fderiv ℝ G (q' + t • W q') (W q') := by
      intro t ht
      have hd : dist (q', t) (q, (0 : ℝ)) < r := by
        rw [Prod.dist_eq]
        apply max_lt
        · linarith
        · rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]; linarith [ht.2]
      exact hr (Metric.mem_ball.mpr hd)
    let f : ℝ → ℝ := fun t => G (q' + t • W q')
    let fN : ℝ → ℝ := fun t => -f t
    have hfderiv : ∀ t : ℝ, HasDerivAt f (fderiv ℝ G (q' + t • W q') (W q')) t := by
      intro t
      have hline : HasDerivAt (fun τ : ℝ => q' + τ • W q') (W q') t := by
        have h := ((hasDerivAt_id t).smul_const (W q')).const_add q'
        simpa using h
      have hGat : DifferentiableAt ℝ G (q' + t • W q') :=
        (hGd.differentiable one_ne_zero).differentiableAt
      exact (hGat.hasFDerivAt).comp_hasDerivAt t hline
    have hNderiv : ∀ t : ℝ,
        HasDerivAt fN (-(fderiv ℝ G (q' + t • W q') (W q'))) t :=
      fun t => (hfderiv t).neg
    have hcontf : ContinuousOn f (Set.Icc (0 : ℝ) xx) := by
      have hc : Continuous f :=
        hGd.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
      exact hc.continuousOn
    have hdiff : DifferentiableOn ℝ f (interior (Set.Icc (0 : ℝ) xx)) :=
      fun t _ => ((hfderiv t).differentiableAt).differentiableWithinAt
    have hcontN : ContinuousOn fN (Set.Icc (0 : ℝ) xx) := hcontf.neg
    have hdiffN : DifferentiableOn ℝ fN (interior (Set.Icc (0 : ℝ) xx)) := hdiff.neg
    -- the level is strictly increasing along the segment, so it can only become positive
    have hderiv : ∀ t ∈ interior (Set.Icc (0 : ℝ) xx), deriv fN t ≤ -cq := by
      intro t ht
      rw [(hNderiv t).deriv]
      have hb := hbound t (interior_subset ht)
      linarith
    have hkey := (convex_Icc (0 : ℝ) xx).image_sub_le_mul_sub_of_deriv_le
      hcontN hdiffN (C := -cq) hderiv 0 ⟨le_rfl, hxxpos.le⟩ xx
      ⟨hxxpos.le, le_rfl⟩ hxxpos.le
    have hf0 : f 0 = G q' := by simp [f]
    have hfx : 0 < f xx := by
      have h1 : fN xx = -f xx := rfl
      have h2 : fN 0 = -f 0 := rfl
      have hGq' : 0 ≤ G q' := hGK q' hq'
      nlinarith [hkey, h1, h2, hf0, hGq', hcqpos, hxxpos]
    show 0 < G (q' + xx • W q')
    simpa [f] using hfx

/-! ## The push-epsilon of the ascent field on a compact set -/

/-- **The one-sided push-off, at the level of a compact set of parameters.**  Let `G = pullback ψ g`
be the plane coordinate read in the parameter plane and `W = descentField ψ (-g)` its ascent field
(the descent field of `-g`).  For a compact set `K` of parameters on which the box norm `β` is
`< s` and the plane coordinate is `≥ 0`, and on which the derivative of `G` does not vanish at the
trace points of `G`, there is a positive push time `ε` such that the one-step map
`q ↦ q + ε • W q` carries every `q ∈ K` into `{0 < G} ∩ {β < s}`.

The proof is the compactness argument of the lower side: `K` is covered by the balls
`Metric.ball q (εq)` of the per-point push times `exists_push_time_at_point`, a finite subcover
supplies the minimum of the `εq`, and the box condition uses `‖W‖ ≤ 1`. -/
private theorem exists_push_epsilon_nonneg
    (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ 2 g) {s : ℝ}
    (β : ℝ × ℝ → ℝ) (hβ : Continuous β)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hbox : ∀ q ∈ K, β q < s)
    (hGK : ∀ q ∈ K, 0 ≤ Work.Smooth.Morse.pullback ψ g q)
    (hreg : ∀ q ∈ K, Work.Smooth.Morse.pullback ψ g q = 0 →
      fderiv ℝ (Work.Smooth.Morse.pullback ψ g) q ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ K,
      (0 < Work.Smooth.Morse.pullback ψ g (pushMapUp ψ g ε q)) ∧ β (pushMapUp ψ g ε q) < s := by
  classical
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hg2n : ContDiff ℝ 2 (-g) := hg.neg
  have hGd : ContDiff ℝ 1 (Work.Smooth.Morse.pullback ψ g) :=
    Work.Smooth.Morse.pullback_contDiff_one ψ hg1
  have hWcont : Continuous (Work.Smooth.Morse.descentField ψ (-g)) :=
    (Work.Smooth.Morse.Flow.contDiff_descentField ψ hg2n).continuous
  have hWle : ∀ q : ℝ × ℝ, ‖Work.Smooth.Morse.descentField ψ (-g) q‖ ≤ 1 :=
    fun q => Work.Smooth.Morse.Flow.norm_descentField_le_one ψ (-g) q
  have hpoint : ∀ q ∈ K, ∃ εq : ℝ, 0 < εq ∧
      ∀ q' ∈ K, dist q' q < εq → ∀ x ∈ Set.Ioc (0 : ℝ) εq,
        0 < Work.Smooth.Morse.pullback ψ g
          (q' + x • Work.Smooth.Morse.descentField ψ (-g) q') :=
    fun q hq => exists_push_time_at_point hGd hWcont hGK hq (fun h0 => by
      rw [fderiv_pullback_ascentField ψ g q]
      exact Work.Smooth.Morse.Flow.descentRate_pos_of_fderiv_ne_zero ψ g (hreg q hq h0))
  by_cases hKne : K.Nonempty
  · let E : K → ℝ := fun i => Classical.choose (hpoint i.val i.property)
    have hE : ∀ i : K, 0 < E i ∧ ∀ q' ∈ K, dist q' i.val < E i →
        ∀ x ∈ Set.Ioc (0 : ℝ) (E i), 0 < Work.Smooth.Morse.pullback ψ g
          (q' + x • Work.Smooth.Morse.descentField ψ (-g) q') :=
      fun i => Classical.choose_spec (hpoint i.val i.property)
    have hcover : K ⊆ ⋃ i : K, Metric.ball i.val (E i) := by
      intro q hq
      exact Set.mem_iUnion.mpr ⟨⟨q, hq⟩, by
        rw [Metric.mem_ball, dist_self]; exact (hE ⟨q, hq⟩).1⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : K => Metric.ball i.val (E i))
      (fun i => Metric.isOpen_ball) hcover
    have htne : t.Nonempty := by
      rcases hKne with ⟨q, hq⟩
      rcases Set.mem_iUnion₂.mp (ht hq) with ⟨i, hi, _⟩
      exact ⟨i, hi⟩
    have hOb : IsOpen {p : ℝ × ℝ | β p < s} := isOpen_lt hβ continuous_const
    obtain ⟨ρb, hρbpos, hρb⟩ := hK.exists_cthickening_subset_open hOb hbox
    have hε0pos : 0 < t.inf' htne E := by
      rw [Finset.lt_inf'_iff htne]
      intro i _
      exact (hE i).1
    refine ⟨min (t.inf' htne E) ρb, lt_min hε0pos hρbpos, ?_⟩
    intro q hq
    rcases Set.mem_iUnion₂.mp (ht hq) with ⟨i, hi, hqi⟩
    have hqi' : dist q i.val < E i := by rwa [Metric.mem_ball] at hqi
    have hεle : min (t.inf' htne E) ρb ≤ E i :=
      le_trans (min_le_left _ _) (Finset.inf'_le E hi)
    have hεpos : 0 < min (t.inf' htne E) ρb := lt_min hε0pos hρbpos
    have hxIoc : min (t.inf' htne E) ρb ∈ Set.Ioc (0 : ℝ) (E i) := ⟨hεpos, hεle⟩
    have hlt := (hE i).2 q hq hqi' (min (t.inf' htne E) ρb) hxIoc
    constructor
    · have heq : pushMapUp ψ g (min (t.inf' htne E) ρb) q
          = q + min (t.inf' htne E) ρb • Work.Smooth.Morse.descentField ψ (-g) q := rfl
      rw [heq]; exact hlt
    · have heq : pushMapUp ψ g (min (t.inf' htne E) ρb) q
          = q + min (t.inf' htne E) ρb • Work.Smooth.Morse.descentField ψ (-g) q := rfl
      rw [heq]
      apply hρb
      refine Metric.mem_cthickening_of_dist_le
        (q + min (t.inf' htne E) ρb • Work.Smooth.Morse.descentField ψ (-g) q) q ρb K hq ?_
      rw [dist_eq_norm]
      have hsub : q + min (t.inf' htne E) ρb • Work.Smooth.Morse.descentField ψ (-g) q - q
          = min (t.inf' htne E) ρb • Work.Smooth.Morse.descentField ψ (-g) q := by abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hεpos.le]
      calc min (t.inf' htne E) ρb * ‖Work.Smooth.Morse.descentField ψ (-g) q‖
            ≤ min (t.inf' htne E) ρb * 1 := by gcongr; exact hWle q
        _ = min (t.inf' htne E) ρb := mul_one _
        _ ≤ ρb := min_le_right _ _
  · refine ⟨1, one_pos, ?_⟩
    intro q hq
    exact absurd ⟨q, hq⟩ hKne

/-- **The one-sided push-off of a loop of the box region (upper side).**  The mirror image of
`Work.BoxShrink.PinchOff.exists_halfDown_loop_of_nonpos_loop_in_box`: a closed curve `γ` of the
surface whose image lies in the region `Ω = F ∩ PBox s c σ` inside the box and which satisfies
`c (σ 2) + u ≤ (γ t) (σ 2)` for all `t` (on or above the cutting plane) is, when the cutting plane is
transverse to the surface along the slice inside the box (`TransverseSlice`), carried to a closed
curve of the **upper half-region** `Ω₊ = F ∩ PBox s c σ ∩ {c (σ 2) + u < y (σ 2)}` with the same
winding vector.

The proof is the same as for the lower side, with the *ascent* field
`W = ((1 + |∇G|²))⁻¹ ∇G` in place of the descent field: the winding vector is preserved because the
push is equivariant for the period lattice, and the landing is strict because at the trace points of
the image of `γ` (a compact subset of the open box, where the box-local transversality
`TransverseSlice` gives `∇G ≠ 0`) the ascent rate is bounded below by a positive `δ`. -/
theorem exists_halfUp_loop_of_nonneg_loop_in_box {ψ : Submission.Diffeo} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ))
    (hbox : ∀ t : ℝ, γ t ∈ Work.BoxShrink.PinchOff.Omega ψ s c σ)
    (hge : ∀ t : ℝ, c (σ 2) + u ≤ (γ t) (σ 2)) :
    ∃ γ' : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
      (∀ t : ℝ, γ' t ∈ Work.BoxShrink.PinchOff.HalfUp ψ s c σ u) ∧
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
  have hGK : ∀ q ∈ K,
      0 ≤ Work.Smooth.Morse.pullback ψ (Work.BoxShrink.Bubble.planeCoord c σ u) q := by
    rintro q ⟨t, -, rfl⟩
    show 0 ≤ Work.BoxShrink.Bubble.planeCoord c σ u (Work.BoxShrink.Pinch.par ψ (Lp t))
    rw [hlift t, Work.BoxShrink.Bubble.planeCoord_apply]
    linarith [hge t]
  have hreg : ∀ q ∈ K,
      Work.Smooth.Morse.pullback ψ (Work.BoxShrink.Bubble.planeCoord c σ u) q = 0 →
        fderiv ℝ (Work.Smooth.Morse.pullback ψ
          (Work.BoxShrink.Bubble.planeCoord c σ u)) q ≠ 0 := by
    intro q hq h0
    have h1 : Work.BoxShrink.Pinch.planeG ψ c σ u q = 0 := h0
    have h2 := hT q (hboxK q hq) h1
    simpa only [Work.BoxShrink.Pinch.planeG] using h2
  obtain ⟨ε, hεpos, hε⟩ := exists_push_epsilon_nonneg ψ
    (Work.BoxShrink.Bubble.contDiff_planeCoord c σ u) (Work.BoxShrink.Pinch.boxB ψ c σ)
    (Work.BoxShrink.Pinch.boxB_continuous ψ c σ) hK hboxK hGK hreg
  have hWcont : Continuous
      (Work.Smooth.Morse.descentField ψ (-(Work.BoxShrink.Bubble.planeCoord c σ u))) :=
    (Work.Smooth.Morse.Flow.contDiff_descentField ψ
      (Work.BoxShrink.Bubble.contDiff_planeCoord c σ u).neg).continuous
  have hWper : ∀ (p : ℝ × ℝ) (k l : ℤ),
      Work.Smooth.Morse.descentField ψ (-(Work.BoxShrink.Bubble.planeCoord c σ u))
          (p.1 + (k : ℝ) * (2 * Real.pi), p.2 + (l : ℝ) * (2 * Real.pi)) =
        Work.Smooth.Morse.descentField ψ (-(Work.BoxShrink.Bubble.planeCoord c σ u)) p :=
    fun p k l => Work.Smooth.Morse.Flow.descentField_biperiodic ψ
      (Work.BoxShrink.Bubble.contDiff_planeCoord c σ u).neg p k l
  obtain ⟨γ', hγ'apply, hγ'wind⟩ :=
    Work.BoxShrink.Bubble.Flow.exists_curve_of_periodicFlow (Work.Smooth.Morse.torus ψ)
      (fun (_ : ℝ) (q : ℝ × ℝ) =>
        pushMapUp ψ (Work.BoxShrink.Bubble.planeCoord c σ u) ε q)
      (by
        have hc : Continuous (fun p : ℝ × (ℝ × ℝ) =>
            p.2 + ε • Work.Smooth.Morse.descentField ψ
              (-(Work.BoxShrink.Bubble.planeCoord c σ u)) p.2) :=
          continuous_snd.add
            ((continuous_const : Continuous fun _ : ℝ × (ℝ × ℝ) => ε).smul
              (hWcont.comp continuous_snd))
        exact hc)
      (by
        intro r q k l
        have hp := hWper q k l
        show (q.1 + ↑k * (2 * Real.pi), q.2 + ↑l * (2 * Real.pi)) + ε •
              Work.Smooth.Morse.descentField ψ (-(Work.BoxShrink.Bubble.planeCoord c σ u))
                (q.1 + ↑k * (2 * Real.pi), q.2 + ↑l * (2 * Real.pi)) =
            ((q + ε • Work.Smooth.Morse.descentField ψ
                (-(Work.BoxShrink.Bubble.planeCoord c σ u)) q).1 + ↑k * (2 * Real.pi),
              (q + ε • Work.Smooth.Morse.descentField ψ
                (-(Work.BoxShrink.Bubble.planeCoord c σ u)) q).2 + ↑l * (2 * Real.pi))
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
        (pushMapUp ψ (Work.BoxShrink.Bubble.planeCoord c σ u) ε (Lp t')) ∈
        Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u := by
      rw [← Set.mem_preimage, Work.BoxShrink.Pinch.preimage_upperRegion]
      exact ⟨hε'.2, hε'.1⟩
    rw [torus_psi_eq_par ψ
      (pushMapUp ψ (Work.BoxShrink.Bubble.planeCoord c σ u) ε (Lp t'))]
    exact hmem
  · rw [hγ'wind, ← Work.SurgeryInvariance.windingOf_eq (Work.Smooth.Morse.torus ψ) γ L]

end

end Work.BoxShrink.PinchOff
