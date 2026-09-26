import Mathlib
import Submission.Work.Drive.Mono.Geom3Defs
import Submission.Work.Drive.Final.LTypes
import Submission.Work.Drive.Mono.Band.BandChartDefs
import Submission.Work.Drive.Mono.Band.badPoint_chart
import Submission.Work.Drive.Mono.faceEvent_offK_null
import Submission.Work.Drive.Mono.Band.fundamentalDomain_reduction
import Submission.Work.Embedding.smooth_implicit_function_nhd

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set Filter
open scoped ContDiff

noncomputable section

/-!
# The type-2 `offK` face events are almost surely true (arbitrary knot)

The set of pairs `(h, τ)` for which some *face event* of the swept level (with the tilt family
`ℓ_τ = ⟪dirOf τ a₀ b₀, ·⟫`) lies on the range of an **arbitrary** smooth knot is null.

The proof has four ingredients.

* `Work.Drive.Mono.faceEvent_chart` (from `Work/Drive/Mono/faceEvent_offK_null.lean`) shows that a
  face event at `(h, τ)` whose surface point lies on the knot satisfies `τ = alphaV/betaV` and
  `h = |heightV - c₀|` there: the bad set is the image of `par ψ ⁻¹ (range K) ∩ chartDomain`
  under the band chart `(heightV, alphaV/betaV)` (up to the reflection `h ↦ c₀ - h`, which is
  handled by composing with the affine maps `g₁, g₂` as in that file).
* `exists_localSection`: the parametrisation `par ψ : ℝ² → ℝ³` has smooth local sections — the
  map is an immersion, so the implicit function theorem
  (`Work.Embedding.smooth_implicit_function_nhd`) inverts it locally, smoothly.
* The preimage of the knot is **periodic** in the parameter plane, so it suffices to control its
  intersection with the compact fundamental square `[0, 2π]²`; that is covered by *finitely many*
  local sections (`IsCompact.elim_finite_subcover`).  On one such local section `η`, the preimage
  of the knot is contained in `η '' (range K)`, which is a countable union of images of the smooth
  curves `t ↦ η (K.curve t)` (restricted to the open set where the chart is defined); each of those
  images is null because the image of a differentiable curve is null
  (`Work.Drive.Mono.volume_range_of_differentiable`), and where the chart's denominator vanishes the
  image lies on the horizontal axis, also null.
-/

/-! ## The Euclidean plane and the parameter plane -/

/-- **The parameter plane as a Euclidean space**, via `u ↦ (u 0, u 1)`. -/
def rhoE : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

lemma rhoE_apply (u : EuclideanSpace ℝ (Fin 2)) : rhoE u = (u 0, u 1) := rfl

/-- **The parametrisation of the surface of the challenge is smooth on the whole parameter
plane.** -/
theorem par_contDiff_infty (ψ : Submission.Diffeo) :
    ContDiff ℝ ∞ (Work.BoxShrink.Pinch.par ψ) := by
  rw [Work.BoxShrink.Pinch.par_def, Work.Smooth.Morse.param_def]
  exact Submission.contDiff_paramDiffeo ψ

/-! ## Smooth local sections of the parametrisation -/

/-- **A smooth local section of the parametrisation of the surface**, together with the data needed
downstream: an open set `V` of the parameter plane, an open set `O` of space, and a function `η`
which is smooth on `O` and inverts `par ψ` on `V`. -/
structure LocalSection (ψ : Submission.Diffeo) (p₀ : ℝ × ℝ) where
  /-- the open set of the parameter plane -/
  V : Set (ℝ × ℝ)
  /-- the open set of space -/
  O : Set R3
  /-- the section -/
  η : R3 → ℝ × ℝ
  /-- `V` is open -/
  isOpen_V : IsOpen V
  /-- `V` contains the base point -/
  mem_V : p₀ ∈ V
  /-- `O` is open -/
  isOpen_O : IsOpen O
  /-- `η` is smooth on `O` -/
  smooth_η : ContDiffOn ℝ ∞ η O
  /-- `η` inverts `par ψ` on `V` -/
  section_prop : ∀ q ∈ V, Work.BoxShrink.Pinch.par ψ q ∈ O ∧ η (Work.BoxShrink.Pinch.par ψ q) = q

/-- **The parametrisation has smooth local sections.**  For every parameter point `p₀` there are an
open neighbourhood `V` of `p₀`, an open neighbourhood `O` of `par ψ p₀` in space and a function
`η` which is smooth on `O` and is a section of `par ψ` on `V`:

`∀ q ∈ V, par ψ q ∈ O ∧ η (par ψ q) = q`.

This is the implicit function theorem applied to the normal equation of the immersion `par ψ`
(`Work.Embedding.smooth_implicit_function_nhd`), transferred from the Euclidean plane to the
parameter plane along the linear equivalence `rhoE`. -/
theorem exists_localSection (ψ : Submission.Diffeo) (p₀ : ℝ × ℝ) :
    Nonempty (LocalSection ψ p₀) := by
  classical
  set Φ : EuclideanSpace ℝ (Fin 2) → R3 := fun u => Work.BoxShrink.Pinch.par ψ (rhoE u) with hΦ
  set u₀ : EuclideanSpace ℝ (Fin 2) := rhoE.symm p₀ with hu₀
  have hu₀p : rhoE u₀ = p₀ := by simp [hu₀]
  have hΦp : Φ u₀ = Work.BoxShrink.Pinch.par ψ p₀ := by simp [hΦ, hu₀p]
  have hpar : ContDiff ℝ ∞ (Work.BoxShrink.Pinch.par ψ) := par_contDiff_infty ψ
  have hΦdiff : ContDiff ℝ ∞ Φ := by
    have h := hpar.comp rhoE.contDiff
    simpa only [hΦ, Function.comp_def] using h
  have hΦsmooth : ContDiffOn ℝ ∞ Φ Set.univ := hΦdiff.contDiffOn
  have hfderiv : fderiv ℝ Φ u₀
      = (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) (rhoE u₀)).comp
          (rhoE : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × ℝ)) := by
    have h1 : Φ = Work.BoxShrink.Pinch.par ψ ∘ (⇑rhoE) := by
      funext u; rfl
    rw [h1, fderiv_comp u₀ (hpar.differentiable (by norm_num)).differentiableAt
      rhoE.differentiableAt, rhoE.fderiv]
  have hinj : Function.Injective (fderiv ℝ Φ u₀) := by
    intro v w hvw
    rw [hfderiv] at hvw
    simp only [ContinuousLinearMap.comp_apply] at hvw
    have h0 : (rhoE : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × ℝ)) (v - w) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (Work.Drive.Mono.Band.par_immersion ψ (rhoE u₀) hvw)
    have h1 : v - w = 0 := rhoE.injective (by rw [map_zero]; exact h0)
    exact sub_eq_zero.mp h1
  obtain ⟨η, O, hOopen, hOmem, _hηself, hηsmooth, hηiff⟩ :=
    Work.Embedding.smooth_implicit_function_nhd (n := 2) (N := 3) Φ (V := Set.univ)
      isOpen_univ (Set.mem_univ _) hΦsmooth hinj
  set η' : R3 → ℝ × ℝ := fun z => rhoE (η z) with hη'
  have hη'smooth : ContDiffOn ℝ ∞ η' O := by
    have h := (rhoE.contDiff.contDiffOn (s := Set.univ)).comp hηsmooth (fun z _ => Set.mem_univ _)
    simpa only [hη', Function.comp_def] using h
  obtain ⟨U, hUsub, hUopen, hUmem⟩ := mem_nhds_iff.mp hηiff
  have hUmem' : (Work.BoxShrink.Pinch.par ψ p₀, u₀) ∈ U := by
    have h := hUmem
    rw [hΦp] at h
    exact h
  set Vset : Set (ℝ × ℝ) := {q : ℝ × ℝ | Work.BoxShrink.Pinch.par ψ q ∈ O ∧
    (Work.BoxShrink.Pinch.par ψ q, rhoE.symm q) ∈ U} with hVset
  have hVopen : IsOpen Vset :=
    (hOopen.preimage hpar.continuous).inter
      (hUopen.preimage (hpar.continuous.prodMk rhoE.symm.continuous))
  refine Nonempty.intro ({ V := Vset, O := O, η := η', isOpen_V := hVopen, mem_V := ⟨hOmem, hUmem'⟩, isOpen_O := hOopen, smooth_η := hη'smooth, section_prop := ?_ } : LocalSection ψ p₀)
  rintro q hq
  rw [hVset] at hq
  obtain ⟨hqO, hqU⟩ := hq
  have hz : (fderiv ℝ Φ (rhoE.symm q)).adjoint
      (Work.BoxShrink.Pinch.par ψ q - Φ (rhoE.symm q)) = 0 := by
    have hq' : Φ (rhoE.symm q) = Work.BoxShrink.Pinch.par ψ q := by
      simp only [hΦ]
      rw [rhoE.apply_symm_apply]
    rw [hq', sub_self, map_zero]
  have hiff := hUsub hqU
  simp only [Set.mem_ofPred_eq] at hiff
  rw [hz] at hiff
  have h2 : η (Work.BoxShrink.Pinch.par ψ q) = rhoE.symm q := hiff.mp rfl
  refine ⟨hqO, ?_⟩
  show rhoE (η (Work.BoxShrink.Pinch.par ψ q)) = q
  rw [h2, rhoE.apply_symm_apply]

/-! ## Periodicity of the parametrisation and of the band chart

`par ψ` is invariant under the period lattice `2πℤ²`; since `par ψ` is smooth, so is its
derivative, and therefore the Gauss normal and the whole band chart `(heightV, alphaV/betaV)`
are periodic as well.  This lets us reduce every statement about the preimage of the knot to the
fundamental square `[0, 2π]²`. -/

/-- The parametrisation is invariant under the period lattice. -/
theorem par_add_period (ψ : Submission.Diffeo) (k m : ℤ) (q : ℝ × ℝ) :
    Work.BoxShrink.Pinch.par ψ (q + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi)))
      = Work.BoxShrink.Pinch.par ψ q := by
  rw [Work.BoxShrink.Pinch.par_apply, Work.BoxShrink.Pinch.par_apply, Prod.mk_add_mk]
  refine congrArg ψ ((Work.Core.torusMap_eq_iff _ _ _ _).mpr ⟨⟨k, ?_⟩, ⟨m, ?_⟩⟩)
  · simp
  · simp

/-- The derivative of the parametrisation is invariant under the period lattice. -/
theorem fderiv_par_add_period (ψ : Submission.Diffeo) (k m : ℤ) (q : ℝ × ℝ) :
    fderiv ℝ (Work.BoxShrink.Pinch.par ψ)
        (q + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi)))
      = fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q := by
  have h1 : q + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi))
      = (q + (0, (m : ℝ) * (2 * Real.pi))) + ((k : ℝ) * (2 * Real.pi), 0) := by
    ext <;> simp
  rw [h1, Work.Drive.Mono.Band.fderiv_par_add_int_mul_two_pi_left,
    Work.Drive.Mono.Band.fderiv_par_add_int_mul_two_pi_right]

/-- The Gauss normal of the parametrisation is invariant under the period lattice. -/
theorem normal_par_add_period (ψ : Submission.Diffeo) (k m : ℤ) (q : ℝ × ℝ) :
    Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ)
        (q + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi)))
      = Work.Drive.Generic.normal (Work.BoxShrink.Pinch.par ψ) q := by
  simp only [Work.Drive.Generic.normal, Work.Drive.Generic.d1, Work.Drive.Generic.d2,
    fderiv_par_add_period]

/-- The height in the direction `v` is invariant under the period lattice. -/
theorem heightV_add_period (ψ : Submission.Diffeo) (v : R3) (k m : ℤ) (q : ℝ × ℝ) :
    Work.Drive.Mono.Band.heightV ψ v (q + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi)))
      = Work.Drive.Mono.Band.heightV ψ v q := by
  simp only [Work.Drive.Mono.Band.heightV, par_add_period]

/-- The projected normal is invariant under the period lattice. -/
theorem projVv_add_period (ψ : Submission.Diffeo) (v : R3) (k m : ℤ) (q : ℝ × ℝ) :
    Work.Drive.Mono.Band.projVv ψ v (q + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi)))
      = Work.Drive.Mono.Band.projVv ψ v q := by
  simp only [Work.Drive.Mono.Band.projVv, Work.Drive.Mono.Band.projV, normal_par_add_period]

/-- The `a₀`-component of the projected normal is invariant under the period lattice. -/
theorem alphaV_add_period (ψ : Submission.Diffeo) (v a₀ : R3) (k m : ℤ) (q : ℝ × ℝ) :
    Work.Drive.Mono.Band.alphaV ψ v a₀ (q + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi)))
      = Work.Drive.Mono.Band.alphaV ψ v a₀ q := by
  simp only [Work.Drive.Mono.Band.alphaV, projVv_add_period]

/-- The `b₀`-component of the projected normal is invariant under the period lattice. -/
theorem betaV_add_period (ψ : Submission.Diffeo) (v b₀ : R3) (k m : ℤ) (q : ℝ × ℝ) :
    Work.Drive.Mono.Band.betaV ψ v b₀ (q + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi)))
      = Work.Drive.Mono.Band.betaV ψ v b₀ q := by
  simp only [Work.Drive.Mono.Band.betaV, projVv_add_period]

/-- The chart domain is invariant under the period lattice. -/
theorem chartDomain_add_period (ψ : Submission.Diffeo) (v b₀ : R3) (k m : ℤ) (q : ℝ × ℝ) :
    q + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi))
        ∈ Work.Drive.Mono.Band.chartDomain ψ v b₀ ↔
      q ∈ Work.Drive.Mono.Band.chartDomain ψ v b₀ := by
  simp only [Work.Drive.Mono.Band.chartDomain, Set.mem_ofPred_eq, betaV_add_period]

/-- The band chart is invariant under the period lattice. -/
theorem bandChart_add_period (ψ : Submission.Diffeo) (v a₀ b₀ : R3) (k m : ℤ) (q : ℝ × ℝ) :
    Work.Drive.Mono.Band.bandChart ψ v a₀ b₀
        (q + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi)))
      = Work.Drive.Mono.Band.bandChart ψ v a₀ b₀ q := by
  simp only [Work.Drive.Mono.Band.bandChart, heightV_add_period, alphaV_add_period,
    betaV_add_period]


/-! ## The image of a curve is null -/

/-- **The image of a differentiable curve on an open interval is null.**  The curve is the first
coordinate of the "collapsed" map `(t, x) ↦ g t` on the plane, whose image of the null set
`(a,b) × {0}` is exactly `g '' (a,b)`; the image of a null set under a differentiable map is
null. -/
theorem volume_image_Ioo {g : ℝ → ℝ × ℝ} {a b : ℝ}
    (hg : DifferentiableOn ℝ g (Set.Ioo a b)) :
    MeasureTheory.volume (g '' Set.Ioo a b) = 0 := by
  have hU : DifferentiableOn ℝ (fun p : ℝ × ℝ => g p.1)
      (Set.Ioo a b ×ˢ (Set.univ : Set ℝ)) := by
    intro p hp
    exact ((hg.differentiableAt (isOpen_Ioo.mem_nhds hp.1)).comp p differentiableAt_fst)
      |>.differentiableWithinAt
  have hdiff : DifferentiableOn ℝ (fun p : ℝ × ℝ => g p.1)
      (Set.Ioo a b ×ˢ ({0} : Set ℝ)) :=
    hU.mono (Set.prod_mono_right (Set.singleton_subset_iff.mpr (Set.mem_univ 0)))
  have hnull : MeasureTheory.volume (Set.Ioo a b ×ˢ ({0} : Set ℝ)) = 0 := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    simp
  have h := MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (μ := MeasureTheory.volume) hdiff hnull
  have himg : (fun p : ℝ × ℝ => g p.1) '' (Set.Ioo a b ×ˢ ({0} : Set ℝ))
      = g '' Set.Ioo a b := by
    ext y; constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨p.1, hp.1, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨(t, 0), ⟨ht, rfl⟩, rfl⟩
  rwa [himg] at h

/-- **The image of a differentiable curve on an open set is null.**  The open set is the countable
union of the rational open intervals it contains. -/
theorem volume_image_isOpen {g : ℝ → ℝ × ℝ} {W : Set ℝ} (hW : IsOpen W)
    (hg : DifferentiableOn ℝ g W) : MeasureTheory.volume (g '' W) = 0 := by
  classical
  have hcover : W = ⋃ u : {u : ℚ × ℚ // (u.1 : ℝ) < u.2 ∧ Set.Ioo (u.1 : ℝ) (u.2 : ℝ) ⊆ W},
      Set.Ioo ((u : ℚ × ℚ).1 : ℝ) ((u : ℚ × ℚ).2 : ℝ) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hW x hx
      obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x - ε < x by linarith)
      obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x < x + ε by linarith)
      have hab : (a : ℝ) < (b : ℝ) := lt_trans ha2 hb1
      have hsub : Set.Ioo (a : ℝ) (b : ℝ) ⊆ W := by
        intro y hy
        exact hεsub (by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)
      exact Set.mem_iUnion.mpr ⟨⟨(a, b), ⟨hab, hsub⟩⟩, ⟨ha2, hb1⟩⟩
    · rintro x hx
      obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hx
      exact u.2.2 hu
  have himg : g '' W = Set.iUnion (fun u :
      {u : ℚ × ℚ // (u.1 : ℝ) < u.2 ∧ Set.Ioo (u.1 : ℝ) (u.2 : ℝ) ⊆ W} =>
      g '' Set.Ioo ((u : ℚ × ℚ).1 : ℝ) ((u : ℚ × ℚ).2 : ℝ)) := by
    conv_lhs => rw [hcover]
    exact Set.image_iUnion
  rw [himg]
  exact MeasureTheory.measure_iUnion_null fun u => volume_image_Ioo (hg.mono u.2.2)

/-! ## The band chart of a local section of the knot is null -/

/-- **The band chart of the pull-back of a curve along a smooth local section is null.**

Let `O` be an open set and `η` be smooth on `O`, and let `γ` be a smooth curve.  Then the band
chart of the points `η (γ t)` with `γ t ∈ O` is a null set of the plane.

Indeed the lifted curve `t ↦ η (γ t)` — which is smooth wherever `γ t ∈ O` — maps the open set
`{t | γ t ∈ O ∧ η (γ t) ∈ chartDomain}` into the chart, where the band chart is smooth, so the
image is null by `volume_image_isOpen`; and where the chart's denominator vanishes the band chart's
second coordinate is `0`, so the remaining image lies on the horizontal axis. -/
theorem bandChart_image_localSection_range_null (ψ : Submission.Diffeo) (v a₀ b₀ : R3)
    (γ : ℝ → R3) (hγ : ContDiff ℝ ∞ γ) (η : R3 → ℝ × ℝ) (O : Set R3) (hO : IsOpen O)
    (hη : ContDiffOn ℝ ∞ η O) :
    MeasureTheory.volume (Work.Drive.Mono.Band.bandChart ψ v a₀ b₀ ''
      (η '' (Set.range γ ∩ O))) = 0 := by
  classical
  have hAxisNull : MeasureTheory.volume {y : ℝ × ℝ | y.2 = 0} = 0 := by
    have hset : {y : ℝ × ℝ | y.2 = 0} = (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
      ext y; simp [Set.mem_prod]
    rw [hset, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    simp
  set A : Set ℝ := {t : ℝ | γ t ∈ O} with hA
  set S : Set ℝ := A ∩ {t : ℝ | η (γ t) ∈ Work.Drive.Mono.Band.chartDomain ψ v b₀} with hS
  have hAopen : IsOpen A := hO.preimage hγ.continuous
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hγO : γ t ∈ O := ht.1
    have hηc : ContinuousAt η (γ t) := (hη.contDiffAt (hO.mem_nhds hγO)).continuousAt
    have hϑc : ContinuousAt (fun s : ℝ => η (γ s)) t :=
      hηc.comp hγ.continuous.continuousAt
    have hdom : {t : ℝ | η (γ t) ∈ Work.Drive.Mono.Band.chartDomain ψ v b₀} ∈ nhds t :=
      hϑc.preimage_mem_nhds
        ((Work.Drive.Mono.Band.chartDomain_isOpen ψ v b₀).mem_nhds ht.2)
    exact Filter.inter_mem (hAopen.mem_nhds ht.1) hdom
  have hrange : η '' (Set.range γ ∩ O) = (fun s : ℝ => η (γ s)) '' A := by
    have h1 : Set.range γ ∩ O = γ '' A := by
      ext z; constructor
      · rintro ⟨⟨t, rfl⟩, hz⟩; exact ⟨t, hz, rfl⟩
      · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, rfl⟩, ht⟩
    rw [h1, Set.image_image]
  have hAeq : A = S ∪ (A \ S) := by
    ext t
    simp only [hS, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  rw [hrange]
  have hsplit : (fun s : ℝ => η (γ s)) '' A
      = (fun s : ℝ => η (γ s)) '' S ∪ (fun s : ℝ => η (γ s)) '' (A \ S) := by
    conv_lhs => rw [hAeq]
    rw [Set.image_union]
  rw [hsplit, Set.image_union]
  refine MeasureTheory.measure_union_null ?_ ?_
  · rw [Set.image_image]
    refine volume_image_isOpen hSopen ?_
    intro t ht
    have hγO : γ t ∈ O := ht.1
    have h1 : DifferentiableAt ℝ (fun s : ℝ => η (γ s)) t :=
      ((hη.contDiffAt (hO.mem_nhds hγO)).differentiableAt (by norm_num)).comp t
        ((hγ.differentiable (by norm_num)).differentiableAt)
    have h2 : DifferentiableAt ℝ (Work.Drive.Mono.Band.bandChart ψ v a₀ b₀) (η (γ t)) :=
      ((Work.Drive.Mono.Band.contDiffOn_bandChart ψ v a₀ b₀).contDiffAt
        ((Work.Drive.Mono.Band.chartDomain_isOpen ψ v b₀).mem_nhds ht.2)).differentiableAt
          (by norm_num)
    exact (h2.comp t h1).differentiableWithinAt
  · refine MeasureTheory.measure_mono_null ?_ hAxisNull
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hz
    have htA : t ∈ A := ht.1
    have htS : t ∉ S := ht.2
    have hβ : Work.Drive.Mono.Band.betaV ψ v b₀ (η (γ t)) = 0 := by
      by_contra hne
      exact htS ⟨htA, hne⟩
    show (Work.Drive.Mono.Band.bandChart ψ v a₀ b₀ (η (γ t))).2 = 0
    simp only [Work.Drive.Mono.Band.bandChart, hβ, div_zero]


/-! ## The parameter preimage of the knot -/

/-- The parameter points of the surface which lie on the knot, inside the chart. -/
def knotPreimage (ψ : Submission.Diffeo) (K : Knot) (v b₀ : R3) : Set (ℝ × ℝ) :=
  Work.BoxShrink.Pinch.par ψ ⁻¹' (Set.range K.curve) ∩
    Work.Drive.Mono.Band.chartDomain ψ v b₀

/-- The fundamental square `[0, 2π]²` of the parameter plane. -/
def fundSquare : Set (ℝ × ℝ) := Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)

theorem isCompact_fundSquare : IsCompact fundSquare := isCompact_Icc.prod isCompact_Icc

theorem mem_fundSquare {q : ℝ × ℝ} :
    q ∈ fundSquare ↔ q.1 ∈ Set.Icc 0 (2 * Real.pi) ∧ q.2 ∈ Set.Icc 0 (2 * Real.pi) :=
  Iff.rfl

/-- Membership in the knot preimage is invariant under the period lattice. -/
theorem mem_knotPreimage_add_period (ψ : Submission.Diffeo) (K : Knot) (v b₀ : R3) (k m : ℤ)
    (q : ℝ × ℝ) :
    q + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi)) ∈ knotPreimage ψ K v b₀ ↔
      q ∈ knotPreimage ψ K v b₀ := by
  rw [knotPreimage, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage,
    par_add_period, chartDomain_add_period]

/-- **The band chart of the knot preimage only involves the fundamental square.** -/
theorem bandChart_image_knotPreimage_eq_fund (ψ : Submission.Diffeo) (K : Knot) (v a₀ b₀ : R3) :
    Work.Drive.Mono.Band.bandChart ψ v a₀ b₀ '' knotPreimage ψ K v b₀
      = Work.Drive.Mono.Band.bandChart ψ v a₀ b₀ ''
          (knotPreimage ψ K v b₀ ∩ fundSquare) := by
  refine Set.Subset.antisymm ?_ (Set.image_mono Set.inter_subset_left)
  rintro z ⟨q, hq, rfl⟩
  obtain ⟨k, hk⟩ := Work.Drive.Mono.Band.exists_int_sub_mul_mem_Icc_two_pi q.1
  obtain ⟨m, hm⟩ := Work.Drive.Mono.Band.exists_int_sub_mul_mem_Icc_two_pi q.2
  set q₀ : ℝ × ℝ := (q.1 - (k : ℝ) * (2 * Real.pi), q.2 - (m : ℝ) * (2 * Real.pi)) with hq₀
  have hper : q₀ + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi)) = q := by
    rw [hq₀]; ext <;> simp
  have hq₀F : q₀ ∈ fundSquare := by
    rw [mem_fundSquare, hq₀]
    exact ⟨⟨hk.1, hk.2⟩, ⟨hm.1, hm.2⟩⟩
  have hq₀X : q₀ ∈ knotPreimage ψ K v b₀ := by
    refine (mem_knotPreimage_add_period ψ K v b₀ k m q₀).mp ?_
    rw [hper]; exact hq
  refine ⟨q₀, ⟨hq₀X, hq₀F⟩, ?_⟩
  rw [← hper, bandChart_add_period]

/-- **The band chart of the knot preimage is null.**

The knot preimage is invariant under the period lattice, so the band chart of the whole preimage is
the band chart of its intersection with the fundamental square.  That square is compact, so finitely
many smooth local sections of the parametrisation cover it, and on each of them the preimage of the
knot is contained in `η '' (range K)`, whose band chart is null
(`bandChart_image_localSection_range_null`). -/
theorem bandChart_image_knotPreimage_null (ψ : Submission.Diffeo) (K : Knot) (v a₀ b₀ : R3) :
    MeasureTheory.volume
      (Work.Drive.Mono.Band.bandChart ψ v a₀ b₀ '' knotPreimage ψ K v b₀) = 0 := by
  classical
  rw [bandChart_image_knotPreimage_eq_fund]
  let LS : (y : ℝ × ℝ) → LocalSection ψ y :=
    fun y => Classical.choice (exists_localSection ψ y)
  have hcov : fundSquare ⊆ ⋃ y : fundSquare, (LS (y : ℝ × ℝ)).V :=
    fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, (LS z).mem_V⟩
  obtain ⟨t, ht⟩ := isCompact_fundSquare.elim_finite_subcover
    (fun y : fundSquare => (LS (y : ℝ × ℝ)).V) (fun y => (LS (y : ℝ × ℝ)).isOpen_V) hcov
  have hcover : knotPreimage ψ K v b₀ ∩ fundSquare ⊆
      ⋃ i : {i : fundSquare // i ∈ t},
        knotPreimage ψ K v b₀ ∩ (LS (i : ℝ × ℝ)).V := by
    rintro q ⟨hqX, hqF⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht hqF)
    obtain ⟨hit, hiV⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨⟨i, hit⟩, ⟨hqX, hiV⟩⟩
  refine MeasureTheory.measure_mono_null (Set.image_mono hcover) ?_
  rw [Set.image_iUnion]
  refine MeasureTheory.measure_iUnion_null fun i => ?_
  refine MeasureTheory.measure_mono_null ?_
    (bandChart_image_localSection_range_null ψ v a₀ b₀ K.curve K.smooth
      (LS (i : ℝ × ℝ)).η (LS (i : ℝ × ℝ)).O (LS (i : ℝ × ℝ)).isOpen_O
      (LS (i : ℝ × ℝ)).smooth_η)
  rintro z ⟨q, ⟨hqX, hqV⟩, rfl⟩
  obtain ⟨hqO, hqq⟩ := (LS (i : ℝ × ℝ)).section_prop q hqV
  exact ⟨q, ⟨Work.BoxShrink.Pinch.par ψ q, ⟨hqX.1, hqO⟩, hqq⟩, rfl⟩


/-- **The type-2 `offK` clause is almost surely true for an arbitrary knot**: the set of pairs
`(h, τ)` at which some face event of the swept level (with the tilt family
`ℓ_τ = ⟪dirOf τ a₀ b₀, ·⟫`) lies on the range of the knot is null. -/
theorem g3_offKFace_bad_null (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3)
    (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) :
    MeasureTheory.volume {x : ℝ × ℝ |
        ∃ p : ℝ × ℝ,
          Work.Drive.Final.IsFaceEvent ψ s c σ u v x.1
            ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf x.2 a₀ b₀)) p ∧
          ∃ t : ℝ, K.curve t = Work.BoxShrink.Pinch.par ψ p} = 0 := by
  classical
  set c₀ : ℝ := inner ℝ v c + u with hc₀
  set S : Set (ℝ × ℝ) :=
    Work.Drive.Mono.Band.bandChart ψ v a₀ b₀ '' knotPreimage ψ K v b₀ with hS
  set g₁ : ℝ × ℝ → ℝ × ℝ := fun y => (y.1 - c₀, y.2) with hg₁
  set g₂ : ℝ × ℝ → ℝ × ℝ := fun y => (c₀ - y.1, y.2) with hg₂
  have hSnull : MeasureTheory.volume S = 0 := bandChart_image_knotPreimage_null ψ K v a₀ b₀
  have hnull₁ : MeasureTheory.volume (g₁ '' S) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (μ := MeasureTheory.volume) (by rw [hg₁]; fun_prop) hSnull
  have hnull₂ : MeasureTheory.volume (g₂ '' S) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (μ := MeasureTheory.volume) (by rw [hg₂]; fun_prop) hSnull
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_union_null hnull₁ hnull₂)
  rintro x ⟨p, hface, t, ht⟩
  obtain ⟨hβ, hchart⟩ :=
    faceEvent_chart ψ s u c σ v a₀ b₀ hv ha hb hab hva hvb x.2 x.1 hface
  have hpX : p ∈ knotPreimage ψ K v b₀ := ⟨⟨t, ht⟩, hβ⟩
  have habs : x.1 = |Work.Drive.Mono.Band.heightV ψ v p - c₀| := by
    rw [← hface.2.1, hc₀]
    simp only [Work.Drive.Final.slabFn_apply, Work.Drive.Mono.Band.heightV]
  have hbch : Work.Drive.Mono.Band.bandChart ψ v a₀ b₀ p ∈ S := ⟨p, hpX, rfl⟩
  by_cases hle : c₀ ≤ Work.Drive.Mono.Band.heightV ψ v p
  · left
    refine ⟨Work.Drive.Mono.Band.bandChart ψ v a₀ b₀ p, hbch, ?_⟩
    rw [hg₁]
    refine Prod.ext ?_ ?_
    · show Work.Drive.Mono.Band.heightV ψ v p - c₀ = x.1
      rw [habs]
      rw [abs_of_nonneg (by linarith)]
    · show Work.Drive.Mono.Band.alphaV ψ v a₀ p / Work.Drive.Mono.Band.betaV ψ v b₀ p = x.2
      exact hchart
  · right
    refine ⟨Work.Drive.Mono.Band.bandChart ψ v a₀ b₀ p, hbch, ?_⟩
    rw [hg₂]
    refine Prod.ext ?_ ?_
    · show c₀ - Work.Drive.Mono.Band.heightV ψ v p = x.1
      rw [habs]
      rw [abs_of_neg (by linarith)]
      ring
    · show Work.Drive.Mono.Band.alphaV ψ v a₀ p / Work.Drive.Mono.Band.betaV ψ v b₀ p = x.2
      exact hchart


end

end Work.Drive.Mono
