import Mathlib
import Submission.Work.CoreTopology.Disk
import Submission.Work.Drive.Mono.GaugeRadialDefs
import Submission.Work.Drive.Mono.gaugeRadial_spec
import Submission.Work.Drive.Mono.separating_of_interior_inter_empty
import Submission.Work.Drive.Mono.eq_segment_of_convex_compact_interior_empty
import Submission.Work.Drive.Mono.HalfDiscAux
import Submission.Work.Drive.Mono.sphereArc_extension
import Submission.Work.Drive.Mono.frontier_union_eq_of_inter_segment
import Submission.Work.Drive.Mono.upperHalfDisc_map_of_segment_frontier

/-!
# Two convex bodies meeting in a segment: the union is a disc

If `A`, `B ⊆ ℝ²` are compact convex sets with non-empty interior whose intersection has empty
interior and at least two points, then `A ∪ B` is the injective continuous image of the closed
unit disc, the unit circle being carried onto `frontier (A ∪ B)`.

This file proves the complex-plane version (`emptyInterior_discParam_complex`) and transports it
to `EuclideanSpace ℝ (Fin 2)`.  The argument is:

1. `inter_eq_segment_of_interior_inter_empty`: `A ∩ B` is a non-degenerate segment `[m₁,m₂]`
   contained in `frontier A ∩ frontier B`, and `A`, `B` are separated by a non-zero linear
   functional `f` with `A ⊆ {f ≤ c}`, `B ⊆ {f ≥ c}`;
2. `frontier_union_eq_of_inter_segment` (imported): the frontier of the union;
3. `upperHalfDisc_map_of_segment_frontier` (imported): the closed upper (resp. lower) half-disc
   is mapped onto `A` (resp. `B`) by a continuous injective map which is affine on the common
   diameter and carries the closed semicircle onto `frontier A` (resp. `frontier B`) minus the
   open segment;
4. `exists_glued_discParam`: the two half-disc parametrisations glue to a parametrisation of the
   closed disc.
-/

namespace Work.Drive.Mono

open Set Metric
open scoped Convex Pointwise

noncomputable section

private lemma not_mem_interior_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Set E} {f : E →L[ℝ] ℝ} {c : ℝ} (hf : f ≠ 0)
    (hA : A ⊆ {x | f x ≤ c}) {x : E} (hxc : f x = c) : x ∉ interior A := by
  intro hxint
  obtain ⟨ε, hε, hsub⟩ : ∃ ε > 0, Metric.ball x ε ⊆ A := by
    rw [mem_interior_iff_mem_nhds] at hxint
    exact Metric.mem_nhds_iff.mp hxint
  obtain ⟨v, hv⟩ : ∃ v : E, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (by ext v; exact h v)
  set w : E := if 0 < f v then v else -v with hw
  have hwpos : 0 < f w := by
    by_cases h : 0 < f v
    · simp only [hw, if_pos h]; exact h
    · have hvlt : f v < 0 := lt_of_le_of_ne (le_of_not_gt h) hv
      simp only [hw, if_neg h, map_neg]
      linarith
  set t : ℝ := ε / (2 * (‖w‖ + 1)) with ht
  have htpos : 0 < t := by
    rw [ht]; positivity
  have htw : ‖t • w‖ < ε := by
    rw [norm_smul, Real.norm_of_nonneg htpos.le, ht, div_mul_eq_mul_div,
      div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (‖w‖ + 1))]
    nlinarith [norm_nonneg w]
  have hmem : x + t • w ∈ A := by
    apply hsub
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : x + t • w - x = t • w := by abel
    rw [h1]; exact htw
  have hle : f (x + t • w) ≤ c := hA hmem
  rw [map_add, map_smul, hxc, smul_eq_mul] at hle
  nlinarith [hwpos, htpos]

theorem inter_eq_segment_of_interior_inter_empty (A B : Set ℂ)
    (hAc : Convex ℝ A) (hAcl : IsCompact A) (hAne : (interior A).Nonempty)
    (hBc : Convex ℝ B) (hBcl : IsCompact B) (hBne : (interior B).Nonempty)
    (h2 : ∃ x : ℂ, x ∈ A ∩ B ∧ ∃ y : ℂ, y ∈ A ∩ B ∧ x ≠ y)
    (hint : ¬ (interior (A ∩ B)).Nonempty) :
    ∃ m₁ m₂ : ℂ, m₁ ≠ m₂ ∧ A ∩ B = segment ℝ m₁ m₂ ∧
      segment ℝ m₁ m₂ ⊆ frontier A ∩ frontier B ∧
      ∃ (f : ℂ →L[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ A ⊆ {x | f x ≤ c} ∧ B ⊆ {x | f x ≥ c} := by
  classical
  set φ : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr with hφ
  set A' : Set (EuclideanSpace ℝ (Fin 2)) := φ '' A with hA'
  set B' : Set (EuclideanSpace ℝ (Fin 2)) := φ '' B with hB'
  have hA'c : Convex ℝ A' := by
    rw [hA']; exact hAc.linear_image φ.toContinuousLinearEquiv.toLinearEquiv.toLinearMap
  have hB'c : Convex ℝ B' := by
    rw [hB']; exact hBc.linear_image φ.toContinuousLinearEquiv.toLinearEquiv.toLinearMap
  have hA'k : IsCompact A' := by rw [hA']; exact hAcl.image φ.continuous
  have hB'k : IsCompact B' := by rw [hB']; exact hBcl.image φ.continuous
  have hA'ne : (interior A').Nonempty := by
    obtain ⟨p, hp⟩ := hAne
    refine ⟨φ p, ?_⟩
    rw [hA']
    change φ p ∈ interior (φ.toHomeomorph '' A)
    rw [← Homeomorph.image_interior φ.toHomeomorph A]
    exact ⟨p, hp, rfl⟩
  have hB'ne : (interior B').Nonempty := by
    obtain ⟨p, hp⟩ := hBne
    refine ⟨φ p, ?_⟩
    rw [hB']
    change φ p ∈ interior (φ.toHomeomorph '' B)
    rw [← Homeomorph.image_interior φ.toHomeomorph B]
    exact ⟨p, hp, rfl⟩
  have hA'B' : A' ∩ B' = φ '' (A ∩ B) := by
    rw [hA', hB', Set.image_inter φ.injective]
  have hCint' : interior (A' ∩ B') = ∅ := by
    rw [hA'B']
    change interior (φ.toHomeomorph '' (A ∩ B)) = ∅
    rw [← Homeomorph.image_interior φ.toHomeomorph (A ∩ B),
      Set.not_nonempty_iff_eq_empty.mp hint, Set.image_empty]
  have h2' : ∃ x ∈ A' ∩ B', ∃ y ∈ A' ∩ B', x ≠ y := by
    obtain ⟨x, hx, y, hy, hxy⟩ := h2
    refine ⟨φ x, ?_, φ y, ?_, fun h => hxy (φ.injective h)⟩
    · rw [hA'B']; exact ⟨x, hx, rfl⟩
    · rw [hA'B']; exact ⟨y, hy, rfl⟩
  obtain ⟨x', hx', y', hy', hxy'⟩ := h2'
  obtain ⟨m₁', m₂', hm', hseg'⟩ :=
    eq_segment_of_convex_compact_interior_empty (hA'c.inter hB'c) (hA'k.inter hB'k) hCint'
      hx' hy' hxy'
  have hd : Disjoint (interior A') (interior B') := by
    rw [Set.disjoint_iff_inter_eq_empty, ← interior_inter]
    exact hCint'
  obtain ⟨f', c, hf'ne, hA'le, hB'ge, hAB'eq⟩ :=
    separating_of_interior_inter_empty hA'c hA'k.isClosed hA'ne hB'c hB'k.isClosed hB'ne hd
  have hsegC : A ∩ B = segment ℝ (φ.symm m₁') (φ.symm m₂') := by
    have h1 : φ.symm '' (A' ∩ B') = A ∩ B := by
      rw [hA'B', Set.image_image]
      have h2 : (fun z => φ.symm (φ z)) = id := funext (fun z => φ.symm_apply_apply z)
      rw [h2, Set.image_id]
    have h2 : φ.symm '' (segment ℝ m₁' m₂') = segment ℝ (φ.symm m₁') (φ.symm m₂') := by
      rw [segment_eq_image', Set.image_image, segment_eq_image']
      apply Set.image_congr
      intro t ht
      rw [map_add, map_smul, map_sub]
    rw [← h1, hseg', h2]
  have hABfront : A ∩ B ⊆ frontier A ∩ frontier B := by
    intro y hy
    have hyc : f' (φ y) = c := hAB'eq (by rw [hA'B']; exact ⟨y, hy, rfl⟩)
    refine ⟨?_, ?_⟩
    · rw [hAcl.isClosed.frontier_eq]
      refine ⟨hy.1, fun hmem => ?_⟩
      have hmem' : φ y ∈ interior A' := by
        rw [hA']
        change φ y ∈ interior (φ.toHomeomorph '' A)
        rw [← Homeomorph.image_interior φ.toHomeomorph A]
        exact ⟨y, hmem, rfl⟩
      exact not_mem_interior_of_le hf'ne hA'le hyc hmem'
    · rw [hBcl.isClosed.frontier_eq]
      refine ⟨hy.2, fun hmem => ?_⟩
      have hmem' : φ y ∈ interior B' := by
        rw [hB']
        change φ y ∈ interior (φ.toHomeomorph '' B)
        rw [← Homeomorph.image_interior φ.toHomeomorph B]
        exact ⟨y, hmem, rfl⟩
      refine not_mem_interior_of_le (f := -f') (c := -c) (neg_ne_zero.mpr hf'ne)
        (fun z hz => by
          have h1 : c ≤ f' z := hB'ge hz
          show (-f') z ≤ -c
          simp only [neg_apply]
          linarith)
        ?_ hmem'
      show (-f') (φ y) = -c
      rw [neg_apply, hyc]
  refine ⟨φ.symm m₁', φ.symm m₂', fun h => hm' (φ.symm.injective h), hsegC, ?_,
    f'.comp (φ.toContinuousLinearEquiv : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 2)), c, ?_, ?_, ?_⟩
  · rw [← hsegC]; exact hABfront
  · intro h
    have h0 : f' = 0 := by
      ext y
      obtain ⟨z, rfl⟩ := φ.surjective y
      have := congrArg (fun (g : ℂ →L[ℝ] ℝ) => g z) h
      simpa using this
    exact hf'ne h0
  · intro x hx
    exact hA'le (by rw [hA']; exact ⟨x, hx, rfl⟩)
  · intro x hx
    exact hB'ge (by rw [hB']; exact ⟨x, hx, rfl⟩)


private lemma segment_eq_image_sigma (m₁ m₂ : ℂ) :
    segment ℝ m₁ m₂
      = (fun t : ℝ => ((1 - t) / 2) • m₁ + ((1 + t) / 2) • m₂) '' Set.Icc (-1 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨b - a, ?_, ?_⟩
    · constructor <;> linarith
    · change ((1 - (b - a)) / 2) • m₁ + ((1 + (b - a)) / 2) • m₂ = a • m₁ + b • m₂
      rw [show (1 - (b - a)) / 2 = a by linarith, show (1 + (b - a)) / 2 = b by linarith]
  · rintro z ⟨t, ht, rfl⟩
    rw [segment]
    exact ⟨(1 - t) / 2, (1 + t) / 2, by linarith [ht.2], by linarith [ht.1], by ring, rfl⟩

/-- The intersection of the two closed half-discs is the diameter `[-1,1]`. -/
private lemma upperHalfDisc_inter_lowerHalfDisc :
    upperHalfDisc ∩ lowerHalfDisc
      = (fun t : ℝ => (t : ℂ)) '' Set.Icc (-1 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨hz1, hz2⟩
    have him : z.im = 0 := le_antisymm hz2.2 hz1.2
    have habs : |z.re| ≤ 1 := le_trans (Complex.abs_re_le_norm z) hz1.1
    refine ⟨z.re, abs_le.mp habs, ?_⟩
    exact Complex.ext (by simp) (by simp [him])
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨?_, by simp⟩, ⟨?_, by simp⟩⟩
    · rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]
      exact abs_le.mpr ⟨ht.1, ht.2⟩
    · rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]
      exact abs_le.mpr ⟨ht.1, ht.2⟩

private lemma norm_circlePoint (θ : ℝ) :
    ‖((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ = 1 := by
  rw [Work.CoreTopology.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

theorem exists_glued_discParam {A B : Set ℂ} {m₁ m₂ : ℂ} {fA fB : ℂ → ℂ}
    (hinter : A ∩ B = segment ℝ m₁ m₂)
    (hfront : frontier (A ∪ B) = (frontier A \ (segment ℝ m₁ m₂ \ {m₁, m₂})) ∪
      (frontier B \ (segment ℝ m₁ m₂ \ {m₁, m₂})))
    (hAcont : Continuous fA) (hAinj : Set.InjOn fA upperHalfDisc) (hAimg : fA '' upperHalfDisc = A)
    (hAdiam : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 →
      fA (t : ℂ) = ((1 - t) / 2) • m₁ + ((1 + t) / 2) • m₂)
    (hAfr : fA '' (upperHalfDisc ∩ {z : ℂ | ‖z‖ = 1}) =
      frontier A \ (segment ℝ m₁ m₂ \ {m₁, m₂}))
    (hBcont : Continuous fB) (hBinj : Set.InjOn fB lowerHalfDisc) (hBimg : fB '' lowerHalfDisc = B)
    (hBdiam : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 →
      fB (t : ℂ) = ((1 - t) / 2) • m₁ + ((1 + t) / 2) • m₂)
    (hBfr : fB '' (lowerHalfDisc ∩ {z : ℂ | ‖z‖ = 1}) =
      frontier B \ (segment ℝ m₁ m₂ \ {m₁, m₂})) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, ℂ), Function.Injective e ∧ Set.range e = A ∪ B ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier (A ∪ B) := by
  have hσ := segment_eq_image_sigma m₁ m₂
  have hUL := upperHalfDisc_inter_lowerHalfDisc
  obtain ⟨e₀, hcont, hinj, himg, hAeq, hBeq⟩ :=
    glued_disc_map hAcont.continuousOn hBcont.continuousOn hAinj hBinj hAimg hBimg
      (fun z hz => by
        have hz' : (z : ℂ) ∈ (fun t : ℝ => (t : ℂ)) '' Set.Icc (-1 : ℝ) 1 := by
          rw [← hUL]; exact hz
        obtain ⟨t, ht, rfl⟩ := hz'
        rw [hAdiam t ht, hBdiam t ht])
      (by
        have h1 : fA '' (upperHalfDisc ∩ lowerHalfDisc)
            = fA '' ((fun t : ℝ => (t : ℂ)) '' Set.Icc (-1 : ℝ) 1) := by rw [hUL]
        rw [h1, Set.image_image]
        trans (fun t : ℝ => ((1 - t) / 2) • m₁ + ((1 + t) / 2) • m₂) '' Set.Icc (-1 : ℝ) 1
        · apply Set.image_congr
          intro t ht
          exact hAdiam t ht
        · rw [← hσ, ← hinter])
  refine ⟨⟨Set.domRestrict (Metric.closedBall (0 : ℂ) 1) e₀, hcont.domRestrict⟩, ?_, ?_, ?_⟩
  · intro z w hzw
    exact Subtype.ext (hinj z.2 w.2 hzw)
  · change Set.range (Set.domRestrict (Metric.closedBall (0 : ℂ) 1) e₀) = A ∪ B
    rw [Set.range_domRestrict, himg]
  · change Set.range (fun θ : ℝ =>
        e₀ ((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ))
      = frontier (A ∪ B)
    rw [hfront]
    apply Set.Subset.antisymm
    · rintro w ⟨θ, rfl⟩
      have hn := norm_circlePoint θ
      have hmem' : ((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ)
          ∈ Metric.closedBall (0 : ℂ) 1 := by
        simp [Metric.mem_closedBall, dist_zero_right, hn]
      rcases le_total 0 (((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ).im)
        with h | h
      · left
        show e₀ (((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1)) : ℂ)
            ∈ frontier A \ (segment ℝ m₁ m₂ \ {m₁, m₂})
        rw [hAeq _ hmem' h, ← hAfr]
        exact Set.mem_image_of_mem fA ⟨mem_upperHalfDisc.mpr
          ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hmem', h⟩, hn⟩
      · right
        show e₀ (((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1)) : ℂ)
            ∈ frontier B \ (segment ℝ m₁ m₂ \ {m₁, m₂})
        rw [hBeq _ hmem' h, ← hBfr]
        exact Set.mem_image_of_mem fB ⟨mem_lowerHalfDisc.mpr
          ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hmem', h⟩, hn⟩
    · intro w hw
      rcases hw with hw | hw
      · rw [← hAfr] at hw
        obtain ⟨z, hz, hzw⟩ := hw
        obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff z).mp hz.2
        refine ⟨θ, ?_⟩
        show e₀ (((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1)) : ℂ) = w
        rw [show ((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ) = z by
          rw [Work.CoreTopology.circlePoint_coe, hθ]]
        rw [hAeq z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz.1.1) hz.1.2, hzw]
      · rw [← hBfr] at hw
        obtain ⟨z, hz, hzw⟩ := hw
        obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff z).mp hz.2
        refine ⟨θ, ?_⟩
        show e₀ (((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1)) : ℂ) = w
        rw [show ((Work.CoreTopology.circlePoint θ : Metric.closedBall (0 : ℂ) 1) : ℂ) = z by
          rw [Work.CoreTopology.circlePoint_coe, hθ]]
        rw [hBeq z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz.1.1) hz.1.2, hzw]


private lemma star_image_lowerHalfDisc : (starRingEnd ℂ) '' lowerHalfDisc = upperHalfDisc := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mem_upperHalfDisc.mpr ⟨by simpa using hw.1, by simp [Complex.conj_im, hw.2]⟩
  · intro hz
    refine ⟨(starRingEnd ℂ) z, ?_, by simp⟩
    exact mem_lowerHalfDisc.mpr ⟨by simpa using hz.1, by simp [Complex.conj_im, hz.2]⟩

private lemma star_image_sphere : (starRingEnd ℂ) '' {z : ℂ | ‖z‖ = 1} = {z : ℂ | ‖z‖ = 1} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa using hw
  · intro hz; exact ⟨(starRingEnd ℂ) z, by simpa using hz, by simp⟩


/-- STUB (to be replaced by the delegated lemma). -/

theorem emptyInterior_discParam_complex (A B : Set ℂ)
    (hAc : Convex ℝ A) (hAcl : IsCompact A) (hAne : (interior A).Nonempty)
    (hBc : Convex ℝ B) (hBcl : IsCompact B) (hBne : (interior B).Nonempty)
    (h2 : ∃ x : ℂ, x ∈ A ∩ B ∧ ∃ y : ℂ, y ∈ A ∩ B ∧ x ≠ y)
    (hint : ¬ (interior (A ∩ B)).Nonempty) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, ℂ), Function.Injective e ∧ Set.range e = A ∪ B ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier (A ∪ B) := by
  obtain ⟨m₁, m₂, hm, hseg, hsegfront, f, c, hf, hAf, hBf⟩ :=
    inter_eq_segment_of_interior_inter_empty A B hAc hAcl hAne hBc hBcl hBne h2 hint
  have hfront := frontier_union_eq_of_inter_segment hAc hAcl hAne hBc hBcl hBne hm hseg
    ⟨f, c, hf, hAf, hBf⟩
  obtain ⟨pA, hpA⟩ := hAne
  obtain ⟨pB, hpB⟩ := hBne
  obtain ⟨fA, hAcont, hAinj, hAimg, hAdiam, hAfr⟩ :=
    upperHalfDisc_map_of_segment_frontier A hAc hAcl.isClosed hAcl.isBounded ⟨pA, hpA⟩ hm
      (fun x hx => (hsegfront hx).1) pA hpA
  obtain ⟨gB, gBcont, gBinj, gBimg, gBdiam, gBfr⟩ :=
    upperHalfDisc_map_of_segment_frontier B hBc hBcl.isClosed hBcl.isBounded ⟨pB, hpB⟩ hm
      (fun x hx => (hsegfront hx).2) pB hpB
  set fB : ℂ → ℂ := fun z => gB ((starRingEnd ℂ) z) with hfB
  have hstarij : Function.Injective (starRingEnd ℂ) := fun z w h => by
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  obtain ⟨e, he1, he2, he3⟩ :=
    exists_glued_discParam (fB := fB) hseg hfront hAcont hAinj hAimg hAdiam hAfr
      (by rw [hfB]; exact gBcont.comp continuous_star)
      (by
        rw [hfB]
        intro z hz w hw hzw
        simp only [] at hzw
        exact hstarij (gBinj (by rw [← star_image_lowerHalfDisc]; exact ⟨z, hz, rfl⟩)
          (by rw [← star_image_lowerHalfDisc]; exact ⟨w, hw, rfl⟩) hzw))
      (by rw [hfB, ← gBimg, ← star_image_lowerHalfDisc, Set.image_image])
      (by
        intro t ht
        rw [hfB]
        have h1 : ((starRingEnd ℂ) (t : ℂ)) = (t : ℂ) := by simp
        simp only [Function.comp_apply, h1]
        exact gBdiam t ht)
      (by
        rw [hfB, ← gBfr, ← Set.image_image, Set.image_inter hstarij,
          star_image_lowerHalfDisc, star_image_sphere])
  exact ⟨e, he1, he2, he3⟩

/-- **The target statement, transported from the complex plane.** -/
theorem emptyInterior_discParam (A B : Set (EuclideanSpace ℝ (Fin 2)))
    (hAc : Convex ℝ A) (hAcl : IsCompact A) (hAne : (interior A).Nonempty)
    (hBc : Convex ℝ B) (hBcl : IsCompact B) (hBne : (interior B).Nonempty)
    (h2 : ∃ x : EuclideanSpace ℝ (Fin 2), x ∈ A ∩ B ∧
      ∃ y : EuclideanSpace ℝ (Fin 2), y ∈ A ∩ B ∧ x ≠ y)
    (hint : ¬ (interior (A ∩ B)).Nonempty) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = A ∪ B ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier (A ∪ B) := by
  set φ : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr with hφ
  set A' : Set ℂ := φ.symm '' A with hA'
  set B' : Set ℂ := φ.symm '' B with hB'
  have hA'c : Convex ℝ A' := by
    rw [hA']; exact hAc.linear_image φ.symm.toContinuousLinearEquiv.toLinearEquiv.toLinearMap
  have hB'c : Convex ℝ B' := by
    rw [hB']; exact hBc.linear_image φ.symm.toContinuousLinearEquiv.toLinearEquiv.toLinearMap
  have hA'k : IsCompact A' := by rw [hA']; exact hAcl.image φ.symm.continuous
  have hB'k : IsCompact B' := by rw [hB']; exact hBcl.image φ.symm.continuous
  have hA'ne : (interior A').Nonempty := by
    obtain ⟨p, hp⟩ := hAne
    refine ⟨φ.symm p, ?_⟩
    rw [hA']
    change φ.symm p ∈ interior (φ.symm.toHomeomorph '' A)
    rw [← Homeomorph.image_interior φ.symm.toHomeomorph A]
    exact ⟨p, hp, rfl⟩
  have hB'ne : (interior B').Nonempty := by
    obtain ⟨p, hp⟩ := hBne
    refine ⟨φ.symm p, ?_⟩
    rw [hB']
    change φ.symm p ∈ interior (φ.symm.toHomeomorph '' B)
    rw [← Homeomorph.image_interior φ.symm.toHomeomorph B]
    exact ⟨p, hp, rfl⟩
  have hAB : A' ∩ B' = φ.symm '' (A ∩ B) := by
    rw [hA', hB', Set.image_inter φ.symm.injective]
  have h2' : ∃ x ∈ A' ∩ B', ∃ y ∈ A' ∩ B', x ≠ y := by
    obtain ⟨x, hx, y, hy, hxy⟩ := h2
    refine ⟨φ.symm x, ?_, φ.symm y, ?_, fun h => hxy (φ.symm.injective h)⟩
    · rw [hAB]; exact ⟨x, hx, rfl⟩
    · rw [hAB]; exact ⟨y, hy, rfl⟩
  have hint' : ¬ (interior (A' ∩ B')).Nonempty := by
    intro hcon
    apply hint
    have h1 : interior (A' ∩ B') = φ.symm '' interior (A ∩ B) := by
      rw [hAB]
      change interior (φ.symm.toHomeomorph '' (A ∩ B))
        = φ.symm.toHomeomorph '' interior (A ∩ B)
      rw [← Homeomorph.image_interior φ.symm.toHomeomorph (A ∩ B)]
    rw [h1] at hcon
    obtain ⟨z, hz⟩ := hcon
    obtain ⟨w, hw, -⟩ := hz
    exact ⟨w, hw⟩
  obtain ⟨e', he'1, he'2, he'3⟩ :=
    emptyInterior_discParam_complex A' B' hA'c hA'k hA'ne hB'c hB'k hB'ne h2' hint'
  have hφA : φ '' A' = A := by
    rw [hA', Set.image_image]
    have h : (fun z => φ (φ.symm z)) = id := funext (fun z => φ.apply_symm_apply z)
    rw [h, Set.image_id]
  have hφB : φ '' B' = B := by
    rw [hB', Set.image_image]
    have h : (fun z => φ (φ.symm z)) = id := funext (fun z => φ.apply_symm_apply z)
    rw [h, Set.image_id]
  refine ⟨⟨fun z => φ (e' z), φ.continuous.comp e'.continuous⟩, ?_, ?_, ?_⟩
  · intro z w h
    exact he'1 (φ.injective h)
  · change Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => φ (e' z)) = A ∪ B
    have h : Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => φ (e' z))
        = φ '' Set.range e' := Set.range_comp (fun z : ℂ => φ z) e'
    rw [h, he'2, Set.image_union, hφA, hφB]
  · change Set.range (fun θ : ℝ => φ (e' (Work.CoreTopology.circlePoint θ)))
      = frontier (A ∪ B)
    have h : Set.range (fun θ : ℝ => φ (e' (Work.CoreTopology.circlePoint θ)))
        = φ '' Set.range (fun θ : ℝ => e' (Work.CoreTopology.circlePoint θ)) :=
      Set.range_comp (fun z : ℂ => φ z) (fun θ : ℝ => e' (Work.CoreTopology.circlePoint θ))
    rw [h, he'3]
    change φ.toHomeomorph '' frontier (A' ∪ B') = frontier (A ∪ B)
    rw [Homeomorph.image_frontier, Set.image_union]
    change frontier (φ '' A' ∪ φ '' B') = frontier (A ∪ B)
    rw [hφA, hφB]


end

end Work.Drive.Mono
