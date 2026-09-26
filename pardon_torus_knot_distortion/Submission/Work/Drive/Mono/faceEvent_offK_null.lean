import Mathlib
import Submission.Work.Drive.Mono.faceEvent_degen_null
import Submission.Work.Drive.Final.LTypes
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.Band.BandChartDefs

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory

noncomputable section

/-!
# The type-2 `offK` clause is almost surely true

This file proves `Work.Drive.Mono.faceEvent_offK_null`: the set of pairs `(h, τ)` for which some
*face event* of the swept level (with the tilt family `ℓ_τ = ⟪dirOf τ a₀ b₀, ·⟫`) lies on the range of
the knot is null.

The proof is the analogue of `Work.Drive.Mono.faceEvent_degen_null` with the *critical set* of the band
chart replaced by the preimage `par ⁻¹' (range K)`, which is contained in countably many straight
lines of the parameter plane (the lifts of the knot along the `(pp,qq)`-line, translated by the
`2πℤ²`-lattice).  Two ingredients are new:

* `Work.Drive.Mono.faceEvent_chart` — a face event at which the surface point lies on the knot has,
  unconditionally, projective coordinate `τ` in the band chart (`betaV ≠ 0` and
  `alphaV / betaV = τ`); this is the first half of `Work.Drive.Mono.faceEvent_degen_crux`, without the
  second-order degeneracy hypothesis.
* `Work.Drive.Mono.volume_range_of_differentiable` — the image of a differentiable curve `ℝ → ℝ²` is
  null.  Applied to the straight lines, this makes `par ⁻¹' (range K)` null; then
  `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` gives the nullity of
  `bandMap '' (par ⁻¹' (range K))`, and the affine maps of `faceEvent_degen_null` finish the job.
-/

/-! ## The image of a curve is null -/

/-- **The range of a differentiable curve in the plane is null.**  The curve `f` is the first
coordinate of the "collapsed" map `(t, x) ↦ f t` on the plane, whose image of the null set
`univ × {0}` is exactly `range f`; the image of a null set under a differentiable map is null. -/
theorem volume_range_of_differentiable (f : ℝ → ℝ × ℝ) (hf : Differentiable ℝ f) :
    MeasureTheory.volume (Set.range f) = 0 := by
  have hdiff : DifferentiableOn ℝ (fun p : ℝ × ℝ => f p.1)
      ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)) :=
    (hf.comp differentiable_fst).differentiableOn
  have hnull : MeasureTheory.volume ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)) = 0 := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    simp
  have h := MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := MeasureTheory.volume) hdiff hnull
  have himg : (fun p : ℝ × ℝ => f p.1) '' ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ))
      = Set.range f := by
    ext y; constructor
    · rintro ⟨p, -, rfl⟩; exact ⟨p.1, rfl⟩
    · rintro ⟨t, rfl⟩; exact ⟨(t, 0), ⟨trivial, rfl⟩, rfl⟩
  rwa [himg] at h

/-- **A lift of the standard `(pp,qq)`-line is null in the parameter plane.** -/
theorem volume_range_liftLine (pp qq : ℕ) (k m : ℤ) :
    MeasureTheory.volume (Set.range (fun t : ℝ =>
      ((pp:ℝ)*t + (k:ℝ)*(2*Real.pi), (qq:ℝ)*t + (m:ℝ)*(2*Real.pi)))) = 0 :=
  volume_range_of_differentiable _ (by fun_prop)

/-! ## A face event on the knot has the tilt's projective coordinate -/

/-- **A face event is a point of the band chart with second coordinate the tilt.**  Let `p` be a face
event of the tilted sweep in the direction `ℓ = ⟪dirOf τ a₀ b₀, ·⟫`.  Then the projected Gauss normal
at `p` is not parallel to `v` and its projective coordinate in the orthonormal pair `(a₀,b₀)` is
exactly `τ`:

`betaV ψ v b₀ p ≠ 0` and `alphaV ψ v a₀ p / betaV ψ v b₀ p = τ`.

This is the first half of `Work.Drive.Mono.faceEvent_degen_crux`, with the second-order degeneracy
hypothesis dropped: the tangency `dF_τ = t · dG` makes `n - t v` a nonzero multiple of the Gauss
normal (`n = dirOf τ a₀ b₀`), so the normal lies in `span {v, n}` — exactly the "bad point"
condition of `Work.Drive.Mono.Band.badPoint_chart`. -/
theorem faceEvent_chart (ψ : Submission.Diffeo) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : R3) (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) (τ h : ℝ) {p : ℝ × ℝ}
    (hface : Work.Drive.Final.IsFaceEvent ψ s c σ u v h
      ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) p) :
    Work.Drive.Mono.Band.betaV ψ v b₀ p ≠ 0 ∧
      Work.Drive.Mono.Band.alphaV ψ v a₀ p / Work.Drive.Mono.Band.betaV ψ v b₀ p = τ := by
  classical
  set n : R3 := Work.Drive.Mono.Band.dirOf τ a₀ b₀ with hn
  set Φ : ℝ × ℝ → R3 := Work.BoxShrink.Pinch.par ψ with hΦdef
  obtain ⟨t, ht⟩ := hface.2.2
  -- the derivative formulas for the two heights
  have hFw : ∀ X : ℝ × ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) p X
      = inner ℝ n (fderiv ℝ Φ p X) := by
    intro X
    rw [Work.Drive.EpsForm.sweepHeight_innerSL]
    exact Work.Drive.Generic.fderiv_height_eq (Work.Drive.Mono.Band.par_contDiff_three ψ) n p X
  have hGw' : ∀ X : ℝ × ℝ, fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p X
      = inner ℝ v (fderiv ℝ Φ p X) := by
    intro X
    have hfun : Work.Drive.Final.slabFnPar ψ c u v
        = fun q => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u) := by
      funext q; rw [Work.Drive.Final.slabFnPar_apply, Work.Drive.Final.slabFn_apply]
    rw [hfun, fderiv_sub_const]
    exact Work.Drive.Generic.fderiv_height_eq (Work.Drive.Mono.Band.par_contDiff_three ψ) v p X
  -- the tangent multiplier
  set U : R3 := n - t • v with hU
  have hkey : inner ℝ n (Work.Drive.Generic.d1 Φ p)
      = t * inner ℝ v (Work.Drive.Generic.d1 Φ p) := by
    have h := congrArg (fun (L : (ℝ × ℝ) →L[ℝ] ℝ) => L (1, 0)) ht
    simp only [smul_apply, smul_eq_mul] at h
    rw [hFw (1, 0), hGw' (1, 0)] at h
    exact h
  have hkey2 : inner ℝ n (Work.Drive.Generic.d2 Φ p)
      = t * inner ℝ v (Work.Drive.Generic.d2 Φ p) := by
    have h := congrArg (fun (L : (ℝ × ℝ) →L[ℝ] ℝ) => L (0, 1)) ht
    simp only [smul_apply, smul_eq_mul] at h
    rw [hFw (0, 1), hGw' (0, 1)] at h
    exact h
  have hUd1 : inner ℝ U (Work.Drive.Generic.d1 Φ p) = 0 := by
    rw [hU, inner_sub_left, real_inner_smul_left, hkey]; ring
  have hUd2 : inner ℝ U (Work.Drive.Generic.d2 Φ p) = 0 := by
    rw [hU, inner_sub_left, real_inner_smul_left, hkey2]; ring
  have hUd1' : inner ℝ (Work.Drive.Generic.d1 Φ p) U = 0 := by
    rw [real_inner_comm]; exact hUd1
  -- `U ≠ 0`
  have hnv : inner ℝ n v = 0 := by
    have h2 := Work.Drive.Mono.Band.inner_v_dirOf hva hvb τ
    rw [← hn, real_inner_comm] at h2
    exact h2
  have hUne : U ≠ 0 := by
    intro h0
    have hn_eq : n = t • v := by
      have h1 : n - t • v = 0 := by rw [← hU]; exact h0
      exact sub_eq_zero.mp h1
    have htv : inner ℝ n v = t := by
      rw [hn_eq, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
      norm_num
    have htz : t = 0 := by rw [← htv]; exact hnv
    have hzero : n = 0 := by rw [hn_eq, htz, zero_smul]
    have hn1 : ‖n‖ = 1 := by rw [hn]; exact Work.Drive.Mono.Band.norm_dirOf ha hb hab τ
    rw [hzero, norm_zero] at hn1
    exact one_ne_zero hn1.symm
  -- `U` is a multiple of the Gauss normal
  have hcross : Work.Drive.Generic.crossE U (Work.Drive.Generic.normal Φ p) = 0 := by
    rw [Work.Drive.Generic.normal, Work.Drive.Generic.crossE_crossE, hUd2, hUd1']
    simp
  obtain ⟨lam, hlam⟩ := Work.Drive.Generic.exists_smul_of_crossE_eq_zero hcross
    (Work.Drive.Mono.Band.normal_par_ne_zero ψ p)
  have hlamne : lam ≠ 0 := by
    intro h0
    exact hUne (by rw [hlam, h0, zero_smul])
  -- the projected normal does not vanish
  have hprojne : Work.Drive.Mono.Band.projV Φ v p ≠ 0 := by
    intro h0
    obtain ⟨cc, hcc⟩ := (Work.Drive.Mono.Band.projV_eq_zero_iff hv p).mp h0
    have hn_eq : n = (t + lam * cc) • v := by
      have h1 : U = (lam * cc) • v := by rw [hlam, hcc, smul_smul]
      have h2 : n - t • v = (lam * cc) • v := by rw [← hU]; exact h1
      have h3 : n = (lam * cc) • v + t • v := by
        have := congrArg (fun x : R3 => x + t • v) h2
        simpa using this
      rw [h3, ← add_smul, add_comm]
    have hnv2 : inner ℝ n v = t + lam * cc := by
      rw [hn_eq, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]
      norm_num
    have hzero : n = 0 := by
      rw [hn_eq, show t + lam * cc = 0 from by rw [← hnv2]; exact hnv, zero_smul]
    have hn1 : ‖n‖ = 1 := by rw [hn]; exact Work.Drive.Mono.Band.norm_dirOf ha hb hab τ
    rw [hzero, norm_zero] at hn1
    exact one_ne_zero hn1.symm
  -- the "bad point" condition of the band chart
  have hbad : inner ℝ (Work.Drive.Generic.crossE v n) (Work.Drive.Generic.normal Φ p) = 0 := by
    have hN : Work.Drive.Generic.normal Φ p = lam⁻¹ • U := by
      rw [hlam, smul_smul, inv_mul_cancel₀ hlamne, one_smul]
    rw [hN, hU, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      inner_crossE_self_right v n, inner_crossE_self_left v n]
    ring
  obtain ⟨hchart, hβne⟩ :=
    Work.Drive.Mono.Band.badPoint_chart ψ hv ha hb hab hva hvb hbad hprojne
  exact ⟨hβne, hchart⟩

/-! ## The main statement -/

/-- **The type-2 `offK` is almost surely true: no face event of the swept family lies on the knot.**
For a fixed `u`, a fixed tilt family `ℓ_τ = ⟪dirOf τ a₀ b₀, ·⟫` and a knot whose range is the standard
`(pp,qq)` curve composed with `ψ`, the set of `(h, τ)` at which some *face event* of the swept level
lies on the range of the knot is null.  This is the type-2 clause of the `offK` field of
`Work.Drive.Final.GoodSweepData3` (project lead, `Submission/Work/Drive/Mono/NOTES_LEAD_geom3Producers.md`
§0.2 and §3): it is the analogue of `Work.Drive.Mono.faceEvent_degen_null` with the critical set
replaced by `par ⁻¹' (range K)`, which lies in countably many lines. -/
theorem faceEvent_offK_null (ψ : Submission.Diffeo)
    (K : LeanEval.KnotTheory.PardonDistortion.Knot) (pp qq : ℕ)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve pp qq)).γ)
    (s u : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3) (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1)
    (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0) (hva : inner ℝ v a₀ = 0)
    (hvb : inner ℝ v b₀ = 0) :
    MeasureTheory.volume {x : ℝ × ℝ | ∃ p : ℝ × ℝ,
      Work.Drive.Final.IsFaceEvent ψ s c σ u v x.1
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf x.2 a₀ b₀)) p ∧
      Work.BoxShrink.Pinch.par ψ p ∈ Set.range K.curve} = 0 := by
  classical
  -- the parameter points lying on the knot, and those of them in the chart domain
  set Lset : Set (ℝ × ℝ) := {q : ℝ × ℝ | Work.BoxShrink.Pinch.par ψ q ∈ Set.range K.curve}
    with hLset
  set chartDom : Set (ℝ × ℝ) := Work.Drive.Mono.Band.chartDomain ψ v b₀ with hchartDom
  -- the band chart
  set bandMap : ℝ × ℝ → ℝ × ℝ := fun q => (Work.Drive.Mono.Band.heightV ψ v q,
    Work.Drive.Mono.Band.alphaV ψ v a₀ q / Work.Drive.Mono.Band.betaV ψ v b₀ q) with hbandMap
  -- the preimage of the knot lies in countably many lifts of the `(pp,qq)`-line
  have hLsub : Lset ⊆ ⋃ km : ℤ × ℤ, Set.range (fun t : ℝ =>
      ((pp:ℝ)*t + (km.1:ℝ)*(2*Real.pi), (qq:ℝ)*t + (km.2:ℝ)*(2*Real.pi))) := by
    intro q hq
    rw [hLset] at hq
    obtain ⟨t, ht⟩ := hq
    have ht2 : K.curve t ∈ Set.range (Work.CoreTopology.ClosedCurve.mapHomeomorph
        ψ.toHomeomorph (Work.CoreTopology.standardCurve pp qq)).γ := by
      rw [← himg]; exact ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := ht2
    have hpar : Work.BoxShrink.Pinch.par ψ ((pp:ℝ)*s, (qq:ℝ)*s)
        = Work.BoxShrink.Pinch.par ψ q := by
      rw [← ht, ← hs]; rfl
    obtain ⟨k, m, hk, hm⟩ :=
      (Work.Drive.EpsForm.par_eq_iff ψ q ((pp:ℝ)*s, (qq:ℝ)*s)).mp hpar.symm
    refine Set.mem_iUnion.mpr ⟨(k, m), ?_⟩
    exact ⟨s, Prod.ext hk.symm hm.symm⟩
  have hLnull : MeasureTheory.volume Lset = 0 := by
    refine MeasureTheory.measure_mono_null hLsub ?_
    refine MeasureTheory.measure_iUnion_null fun km => ?_
    exact volume_range_liftLine pp qq km.1 km.2
  have hL'null : MeasureTheory.volume (Lset ∩ chartDom) = 0 :=
    MeasureTheory.measure_mono_null (Set.inter_subset_left) hLnull
  -- the image of `Lset ∩ chartDom` under the band chart is null
  have hmapnull : MeasureTheory.volume (bandMap '' (Lset ∩ chartDom)) = 0 := by
    refine MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (μ := MeasureTheory.volume) ?_ hL'null
    intro q hq
    refine ((hdiff_heightV ψ v q).prodMk (hdiff_chart ψ v a₀ b₀ q ?_)).differentiableWithinAt
    rw [hchartDom] at hq
    exact hq.2
  -- the two affine maps `(x,y) ↦ (x - c₀, y)` and `(x,y) ↦ (c₀ - x, y)`
  set c₀ : ℝ := inner ℝ v c + u with hc₀
  set g₁ : ℝ × ℝ → ℝ × ℝ := fun y => (y.1 - c₀, y.2) with hg₁
  set g₂ : ℝ × ℝ → ℝ × ℝ := fun y => (c₀ - y.1, y.2) with hg₂
  have hnull₁ : MeasureTheory.volume (g₁ '' (bandMap '' (Lset ∩ chartDom))) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (μ := MeasureTheory.volume) (s := bandMap '' (Lset ∩ chartDom)) (f := g₁)
      (by rw [hg₁]; fun_prop) hmapnull
  have hnull₂ : MeasureTheory.volume (g₂ '' (bandMap '' (Lset ∩ chartDom))) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (μ := MeasureTheory.volume) (s := bandMap '' (Lset ∩ chartDom)) (f := g₂)
      (by rw [hg₂]; fun_prop) hmapnull
  -- the failure set is contained in those two images
  refine MeasureTheory.measure_mono_null ?_
    (MeasureTheory.measure_union_null hnull₁ hnull₂)
  rintro x hx
  rw [Set.mem_ofPred_eq] at hx
  obtain ⟨p, hface, hK⟩ := hx
  obtain ⟨hβne, hchart⟩ := faceEvent_chart ψ s u c σ v a₀ b₀ hv ha hb hab hva hvb x.2 x.1 hface
  have hpS : p ∈ Lset ∩ chartDom := by
    refine ⟨?_, ?_⟩
    · rw [hLset]; exact hK
    · rw [hchartDom]; exact hβne
  have hband : bandMap p ∈ bandMap '' (Lset ∩ chartDom) := ⟨p, hpS, rfl⟩
  have habs : x.1 = |Work.Drive.Mono.Band.heightV ψ v p - (inner ℝ v c + u)| := by
    have h1 := hface.2.1
    rw [Work.Drive.Final.slabFn_apply] at h1
    rw [← h1]
    simp only [Work.Drive.Mono.Band.heightV, Work.BoxShrink.Pinch.par]
  by_cases hle : (inner ℝ v c + u) ≤ Work.Drive.Mono.Band.heightV ψ v p
  · left
    refine ⟨bandMap p, hband, ?_⟩
    rw [hg₁, hbandMap]
    refine Prod.ext ?_ ?_
    · rw [habs, abs_of_nonneg (by linarith [hc₀])]
    · exact hchart
  · right
    refine ⟨bandMap p, hband, ?_⟩
    rw [hg₂, hbandMap]
    refine Prod.ext ?_ ?_
    · rw [habs, abs_of_neg (by linarith [hc₀])]; ring
    · exact hchart

end

end Work.Drive.Mono
