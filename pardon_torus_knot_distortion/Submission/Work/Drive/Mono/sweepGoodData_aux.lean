import Mathlib
import Submission.Work.Drive.Mono.JunctionGenC
import Submission.Work.Drive.Final.GoodSweepData2
import Submission.Work.Drive.Mono.BoxGen
import Submission.Work.Drive.Mono.CutTransverse
import Submission.Work.Drive.Mono.SlabCaps
import Submission.Work.Drive.Mono.junctionGoodAux
import Submission.Work.Drive.Mono.Band.BandChartDefs
import Submission.Work.Drive.Mono.Band.clauseTwo_exists
import Submission.Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic
import Submission.Work.Drive.Mono.ae_exists_goodV

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The closed tilted slab shrinks with its half-width. -/
theorem tiltedSlabClosed_mono {a : ℝ} {v : R3} {h h' : ℝ} (hh : h' ≤ h) :
    Work.Drive.EpsForm.tiltedSlabClosed a v h' ⊆ Work.Drive.EpsForm.tiltedSlabClosed a v h :=
  fun _ hy => le_trans hy hh

/-- **Clause (c) of `JunctionGenC` from the finiteness of the corner locus.** -/
theorem exists_exc_of_cornerLocus_finite {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} (hs : 0 < s)
    (hcorner : {z : R3 | z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
        ∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
          |z (σ j) - c (σ j)| = Submission.boxSide j * s}.Finite)
    (hwin : ∀ y ∈ closure (Submission.PBox s c σ), lam0 < ℓ y ∧ ℓ y < lam1)
    (hexc : ∀ t ∈ exc, lam0 < t ∧ t < lam1) :
    ∃ exc' : Finset ℝ, (∀ t ∈ exc, t ∈ exc') ∧ (∀ t ∈ exc', lam0 < t ∧ t < lam1) ∧
      ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| ≤ h →
        (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
          |z (σ j) - c (σ j)| = Submission.boxSide j * s) →
        ℓ z ∈ (exc' : Set ℝ) := by
  classical
  refine ⟨exc ∪ (hcorner.toFinset.filter (fun z : R3 => Submission.boxNorm c σ z = s)).image ℓ,
    ?_, ?_, ?_⟩
  · intro t ht
    exact Finset.mem_union_left _ ht
  · intro t ht
    rcases Finset.mem_union.mp ht with h1 | h2
    · exact hexc t h1
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h2
      have hbox : Submission.boxNorm c σ z = s := (Finset.mem_filter.mp hz).2
      refine hwin z ?_
      have hfr : z ∈ frontier (Submission.PBox s c σ) := by
        rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ]
        exact hbox
      exact frontier_subset_closure hfr
  · intro z hz hbox _ hext
    refine Finset.mem_union_right _ ?_
    rw [Finset.mem_image]
    refine ⟨z, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨hz, hext⟩, hbox⟩

/-- **The face regularity from the regularity of the two face levels.** -/
theorem faceReg_of_isRegularValue (ψ : Submission.Diffeo) (v : R3) (a h : ℝ) (hh : 0 < h)
    (hreg : Work.Smooth.Morse.IsRegularValue ψ (fun z : R3 => inner ℝ v z) (a + h))
    (hreg' : Work.Smooth.Morse.IsRegularValue ψ (fun z : R3 => inner ℝ v z) (a - h)) :
    ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      |inner ℝ v z - a| = h →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 := by
  intro z hz hzs
  have hzr : z ∈ Set.range (Work.Smooth.Morse.param ψ) := by
    simpa [Work.Drive.EpsSphere.torusOf, Work.TorusCover.psiMap_apply, Work.Smooth.Morse.param]
      using hz
  obtain ⟨p, hp⟩ := hzr
  refine ⟨p, by rw [Work.BoxShrink.Pinch.par_def]; exact hp, ?_⟩
  have hpull : Work.Smooth.Morse.pullback ψ (fun z : R3 => inner ℝ v z) p = inner ℝ v z := by
    simp [Work.Smooth.Morse.pullback, hp]
  have hfun : Work.Smooth.Morse.pullback ψ (fun z : R3 => inner ℝ v z)
      = fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) := rfl
  intro hder
  have hder' : fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun z : R3 => inner ℝ v z)) p = 0 := by
    rw [hfun]; exact hder
  rcases (abs_eq hh.le).mp hzs with h1 | h1
  · exact (Work.Smooth.Morse.isRegularValue_iff ψ _ _).mp hreg p (by rw [hpull]; linarith) hder'
  · exact (Work.Smooth.Morse.isRegularValue_iff ψ _ _).mp hreg' p (by rw [hpull]; linarith) hder'

/-- **Almost every half-width has the two face levels regular for the tilted height.** -/
theorem ae_isRegularValue_heightV (ψ : Submission.Diffeo) (v : R3) (a : ℝ) :
    ∀ᵐ h ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Smooth.Morse.IsRegularValue ψ (fun z : R3 => inner ℝ v z) (a + h) ∧
      Work.Smooth.Morse.IsRegularValue ψ (fun z : R3 => inner ℝ v z) (a - h) := by
  set G : ℝ × ℝ → ℝ := fun p => inner ℝ v (Work.BoxShrink.Pinch.par ψ p) with hGdef
  have hG : ContDiff ℝ 2 G := Work.Drive.Mono.Band.contDiff_heightV ψ v
  have hper1 : ∀ p : ℝ × ℝ, G (p.1 + 2 * Real.pi, p.2) = G p := by
    intro p
    simp only [hGdef]
    rw [Work.Drive.Mono.Band.par_add_two_pi_left ψ p]
  have hper2 : ∀ p : ℝ × ℝ, G (p.1, p.2 + 2 * Real.pi) = G p := by
    intro p
    simp only [hGdef]
    rw [Work.Drive.Mono.Band.par_add_two_pi_right ψ p]
  have hnull : MeasureTheory.volume {u : ℝ | ∃ p : ℝ × ℝ, G p = u ∧ fderiv ℝ G p = 0} = 0 :=
    Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic hG hper1 hper2
  have hfun : Work.Smooth.Morse.pullback ψ (fun z : R3 => inner ℝ v z)
      = G := funext (fun p => rfl)
  have hCV : Work.Smooth.Morse.criticalValues ψ (fun z : R3 => inner ℝ v z)
      = {u : ℝ | ∃ p : ℝ × ℝ, G p = u ∧ fderiv ℝ G p = 0} := by
    ext t
    rw [Work.Smooth.Morse.mem_criticalValues]
    constructor
    · rintro ⟨p, hd, hp⟩
      refine ⟨p, ?_, ?_⟩
      · rw [← hp]; exact congrFun hfun p
      · rwa [hfun] at hd
    · rintro ⟨p, hp, hd⟩
      refine ⟨p, ?_, ?_⟩
      · rwa [hfun]
      · rw [hfun]; exact hp
  have hCV0 : MeasureTheory.volume (Work.Smooth.Morse.criticalValues ψ
      (fun z : R3 => inner ℝ v z)) = 0 := by
    rw [hCV]; exact hnull
  have hae1 : ∀ᵐ h ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      a + h ∉ Work.Smooth.Morse.criticalValues ψ (fun z : R3 => inner ℝ v z) := by
    rw [MeasureTheory.ae_iff]
    have hset : {h : ℝ | ¬(a + h ∉ Work.Smooth.Morse.criticalValues ψ
        (fun z : R3 => inner ℝ v z))}
        = (fun h : ℝ => a + h) ⁻¹' Work.Smooth.Morse.criticalValues ψ
            (fun z : R3 => inner ℝ v z) := by
      ext h; simp
    rw [hset, MeasureTheory.measure_preimage_add]
    exact hCV0
  have hae2 : ∀ᵐ h ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      a - h ∉ Work.Smooth.Morse.criticalValues ψ (fun z : R3 => inner ℝ v z) := by
    rw [MeasureTheory.ae_iff]
    have hset : {h : ℝ | ¬(a - h ∉ Work.Smooth.Morse.criticalValues ψ
        (fun z : R3 => inner ℝ v z))}
        = (fun h : ℝ => a - h) ⁻¹' Work.Smooth.Morse.criticalValues ψ
            (fun z : R3 => inner ℝ v z) := by
      ext h; simp
    rw [hset]
    have hmap := MeasureTheory.Measure.map_sub_left_eq_self
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a
    have hle := MeasureTheory.Measure.le_map_apply
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := fun u : ℝ => a - u) (measurable_const.sub measurable_id).aemeasurable
      (Work.Smooth.Morse.criticalValues ψ (fun z : R3 => inner ℝ v z))
    rw [hmap, hCV0] at hle
    exact le_antisymm hle bot_le
  filter_upwards [hae1, hae2] with h h1 h2
  exact ⟨h1, h2⟩

/-- **Almost every half-width is regular for the knot's tilted height.** -/
theorem ae_knot_height_regular (K : Knot) (v : R3) (a : ℝ) :
    ∀ᵐ h ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      (∀ t : ℝ, inner ℝ v (K.curve t) = a + h →
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) ∧
      (∀ t : ℝ, inner ℝ v (K.curve t) = a - h →
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) := by
  set g : ℝ → ℝ := fun u => inner ℝ v (K.curve u) with hgdef
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    have h : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (innerSL ℝ v) (K.curve u)) :=
      ContDiff.continuousLinearMap_comp (innerSL ℝ v) K.smooth
    simpa [g] using h
  have hgd : ∀ t, HasDerivAt g (deriv g t) t := fun t =>
    (hg.differentiable (by simp)).differentiableAt.hasDerivAt
  have hnull : MeasureTheory.volume (g '' {t | deriv g t = 0}) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := MeasureTheory.volume)
      (f' := fun t => ContinuousLinearMap.toSpanSingleton ℝ (deriv g t)) ?_ ?_
    · intro t _
      exact (hgd t).hasFDerivAt.hasFDerivWithinAt
    · intro t ht
      rw [ht, ContinuousLinearMap.det_toSpanSingleton]
  have hae1 : ∀ᵐ h ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      a + h ∉ g '' {t | deriv g t = 0} := by
    rw [MeasureTheory.ae_iff]
    have hset : {h : ℝ | ¬(a + h ∉ g '' {t | deriv g t = 0})}
        = (fun h : ℝ => a + h) ⁻¹' (g '' {t | deriv g t = 0}) := by
      ext h; simp
    rw [hset, MeasureTheory.measure_preimage_add]
    exact hnull
  have hae2 : ∀ᵐ h ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      a - h ∉ g '' {t | deriv g t = 0} := by
    rw [MeasureTheory.ae_iff]
    have hset : {h : ℝ | ¬(a - h ∉ g '' {t | deriv g t = 0})}
        = (fun h : ℝ => a - h) ⁻¹' (g '' {t | deriv g t = 0}) := by
      ext h; simp
    rw [hset]
    have hmap := MeasureTheory.Measure.map_sub_left_eq_self
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) a
    have hle := MeasureTheory.Measure.le_map_apply
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (f := fun u : ℝ => a - u) (measurable_const.sub measurable_id).aemeasurable
      (g '' {t | deriv g t = 0})
    rw [hmap, hnull] at hle
    exact le_antisymm hle bot_le
  filter_upwards [hae1, hae2] with h h1 h2
  constructor
  · intro t ht
    exact fun hzero => h1 ⟨t, hzero, by rw [hgdef]; exact ht⟩
  · intro t ht
    exact fun hzero => h2 ⟨t, hzero, by rw [hgdef]; exact ht⟩

end

open scoped RealInnerProductSpace in
/-- **`haxis` for the no-graze witness.**  If `v` is a unit vector within `1/2` of
`shiftVσ σ 1` and distinct from it, then `v` is parallel to no coordinate direction — the hypothesis
`haxis` of `Work.Drive.Mono.tiltData_window_of_dir_export_axis`.  (`‖v - shiftVσ σ 1‖ = τ > 0` and
`‖v‖ = ‖shiftVσ σ 1‖ = 1` give `⟪v, shiftVσ σ 1⟫ = 1 - τ ^ 2 / 2 ≥ 7 / 8 > 0`, which excludes
`v = ± e_{σ i}` for every `i`.) -/
theorem haxis_of_close {σ : Equiv.Perm (Fin 3)} {v : R3} (hv : ‖v‖ = 1)
    (hve : ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ 1 / 2)
    (hne : v ≠ Work.BoxShrink.shiftVσ σ 1) :
    ∀ i : Fin 3, ∀ a : ℝ, EuclideanSpace.single (σ i) (1 : ℝ) ≠ a • v := by
  set e : R3 := Work.BoxShrink.shiftVσ σ 1 with he
  have he1 : ‖e‖ = 1 := by rw [he]; exact Work.Drive.EpsForm.norm_shiftVσ_one σ
  have hdiff : ∀ w w' : R3, ‖w - w'‖ ^ 2 = ‖w‖ ^ 2 + ‖w'‖ ^ 2 - 2 * inner ℝ w w' := by
    intro w w'
    rw [← real_inner_self_eq_norm_sq (w - w'), inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_comm w' w, real_inner_self_eq_norm_sq w, real_inner_self_eq_norm_sq w']
    ring
  have hinner : 7 / 8 ≤ inner ℝ v e := by
    have h5 : ‖v - e‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      have h := mul_self_le_mul_self (norm_nonneg (v - e)) hve
      simpa [sq] using h
    rw [hdiff v e, hv, he1] at h5
    linarith
  have hnonzero : inner ℝ v e ≠ 0 := by linarith [hinner]
  intro i a hcon
  have hsingle : ‖EuclideanSpace.single (σ i) (1 : ℝ)‖ = 1 := by simp
  have ha1 : |a| = 1 := by
    have h := congrArg norm hcon
    rw [hsingle, norm_smul, hv, mul_one, Real.norm_eq_abs] at h
    exact h.symm
  have hkey : inner ℝ (EuclideanSpace.single (σ i) (1 : ℝ)) e = a * inner ℝ v e := by
    rw [hcon, real_inner_smul_left]
  rcases eq_or_ne i 2 with rfl | hi
  · have hone : inner ℝ (EuclideanSpace.single (σ 2) (1 : ℝ)) e = 1 := by
      rw [real_inner_comm, he, inner_shiftVσ_one]; simp
    rw [hone] at hkey
    have hval : a * inner ℝ v e = 1 := hkey.symm
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp ha1 with ha | ha
    · rw [ha, one_mul] at hval
      have hv_eq : v = e := by
        have h2 : ‖v - e‖ ^ 2 = 0 := by
          rw [hdiff v e, hv, he1, hval]; norm_num
        have h3 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
        exact sub_eq_zero.mp (norm_eq_zero.mp h3)
      exact hne (by rw [hv_eq, he])
    · rw [ha] at hval
      linarith [hinner, hval]
  · have hzero : inner ℝ (EuclideanSpace.single (σ i) (1 : ℝ)) e = 0 := by
      rw [real_inner_comm, he, inner_shiftVσ_one, PiLp.single_apply]
      rw [if_neg (fun h : σ 2 = σ i => hi (σ.injective h.symm))]
    rw [hzero] at hkey
    have : a = 0 := (mul_eq_zero.mp hkey.symm).resolve_right hnonzero
    rw [this] at ha1
    norm_num at ha1

/-- **A sub-window of `(A₀, B₀)` avoiding a prescribed finite set of bad half-widths.**  The
producers of the tilt data return an *arbitrary* element of the window they are given, so to force
their output to avoid a finite set `F` one passes a window disjoint from `F`; this is possible
because `(A₀, B₀) \ F` is open and non-empty (a non-empty open interval minus a finite set).  This
is the device that keeps the produced half-width off the finitely many corner slab-values and the
finitely many critical heights of the knot's tilted coordinate. -/
theorem exists_subwindow_avoiding_finset {A₀ B₀ : ℝ} (hAB : A₀ < B₀) (F : Finset ℝ) :
    ∃ A B : ℝ, A₀ < A ∧ A < B ∧ B < B₀ ∧ ∀ t ∈ F, ¬ (A < t ∧ t < B) := by
  have hne : (Set.Ioo A₀ B₀ \ (F : Set ℝ)).Nonempty := by
    by_contra h
    have hsub : Set.Ioo A₀ B₀ ⊆ (F : Set ℝ) := by
      intro x hx
      by_contra hx'
      exact h ⟨x, hx, hx'⟩
    exact Set.Infinite.not_finite ((Set.Ioo_infinite hAB).mono hsub) F.finite_toSet
  obtain ⟨x, hxU⟩ := hne
  have hxIoo : x ∈ Set.Ioo A₀ B₀ := hxU.1
  have hUopen : IsOpen (Set.Ioo A₀ B₀ \ (F : Set ℝ)) :=
    isOpen_Ioo.sdiff F.finite_toSet.isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen x hxU
  have hmemL : x - 3 * ε / 4 ∈ Set.Ioo A₀ B₀ \ (F : Set ℝ) := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hε], by linarith [hε]⟩
  have hmemR : x + 3 * ε / 4 ∈ Set.Ioo A₀ B₀ \ (F : Set ℝ) := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hε], by linarith [hε]⟩
  refine ⟨x - ε / 2, x + ε / 2, ?_, ?_, ?_, ?_⟩
  · linarith [hmemL.1.1, hε]
  · linarith [hε]
  · linarith [hmemR.1.2, hε]
  · intro t ht hlt
    have hmem : t ∈ Set.Ioo A₀ B₀ \ (F : Set ℝ) := by
      refine hball ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hlt.1, hε], by linarith [hlt.2, hε]⟩
    exact hmem.2 (by simpa using ht)

/-- **The slab values of the corner locus form a finite set.**  By the hypothesis `hcorner` (the
corner locus of the box level is finite) the finitely many values `|⟪v, z⟫ - (⟪v,c⟫ + u)|` of the
corner points `z` of the box level form a finset `F`.  The producer may then be given a window
avoiding `F` (`Work.Drive.Mono.exists_subwindow_avoiding_finset`), which makes "no corner point lies
on the slab face" — the hypothesis `hnoCornerFace` of `Work.Drive.Mono.junctionGenC_of_arcs` —
available. -/
theorem exists_finset_cornerSlabValues {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)}
    (hcorner : {z : R3 | z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
        ∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
          |z (σ j) - c (σ j)| = Submission.boxSide j * s}.Finite) :
    ∃ F : Finset ℝ, ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) →
      |inner ℝ v z - (inner ℝ v c + u)| ∈ F := by
  refine ⟨(hcorner.toFinset.filter (fun z : R3 => Submission.boxNorm c σ z = s)).image
    (fun z : R3 => |inner ℝ v z - (inner ℝ v c + u)|), ?_⟩
  intro z hz hbox hext
  rw [Finset.mem_image]
  refine ⟨z, ?_, rfl⟩
  rw [Finset.mem_filter]
  exact ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨hz, hext⟩, hbox⟩

/-- **The slab values of the corner locus form a finite set** (without any condition on `boxNorm`).

The statement's `hcorner` is finiteness of the points of the surface with two extremal coordinates,
*without* the condition `boxNorm c σ z = s`; this form records all those values, and is what makes
`Work.Drive.Final.IsTriplePoint` vacuous at a level avoiding them (a triple point needs two extremal
coordinates and `|slabFn| = h`). -/
theorem exists_finset_cornerSlabValues_all {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)}
    (hcorner : {z : R3 | z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
        ∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
          |z (σ j) - c (σ j)| = Submission.boxSide j * s}.Finite) :
    ∃ F : Finset ℝ, ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) →
      |inner ℝ v z - (inner ℝ v c + u)| ∈ F := by
  refine ⟨hcorner.toFinset.image
    (fun z : R3 => |inner ℝ v z - (inner ℝ v c + u)|), ?_⟩
  intro z hz hext
  rw [Finset.mem_image]
  exact ⟨z, by rw [Set.Finite.mem_toFinset]; exact ⟨hz, hext⟩, rfl⟩

end Work.Drive.Mono
