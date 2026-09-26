import Mathlib
import Submission.BandArcCover

/-! # The round circle: no trisecants, and a non-injective chord square

This module records verified facts about Kuperberg's objects on the *round
unknot*, needed to delimit what the "ruled route" to
`Work.Drive.unknotted_of_avoidingArc` can and cannot do.

* `trisecantSet_standardCircle_eq_empty`: the trisecant locus `O` of the round
  circle is **empty** — a line meets a circle in at most two points, so no
  chord of the round circle carries a third (middle) point of the circle.
  Equivalently (`trisecantSet` is Kuperberg's `O`): the round unknot has no
  trisecants at all.
* `circleBandArc`: an explicit non-separating band arc of the secant Möbius
  band over the round circle, with branches `a s = 2·period·s` and
  `b s = 3·period·s`; `circleBandArc_nonSeparating` proves the two real lifts
  `ta s = 2·period·s`, `tb s = 3·period·s` satisfy `ta 0 = tb 0` and
  `tb 1 = ta 1 + period`.
* `nonSeparatingArcAvoidingO_standardCircle`: consequently the round circle
  satisfies the brick-(d) hypothesis `NonSeparatingArcAvoidingO` — the
  hypothesis of the Layer-B pin is *satisfiable* (not vacuous), and its
  conclusion `IsUnknotted standardCircle` is true (`standardCircle_isUnknotted`).
* `not_injective_chordFamilyDisk_circleBandArc`: **but the chord square over
  this avoiding non-separating arc is not injective.**  The chord at `s = 1/2`
  is the diameter from `standardCircle 0` to `standardCircle π`, the chord at
  `s = 3/5` joins the points at angles `2π/5` and `8π/5`, and the two chords
  cross at `(cos(2π/5), 0, 0)`, which is hit by both `(s,t) = (1/2, (1-cos(2π/5))/2)`
  and `(s,t) = (3/5, 1/2)`.  Hence the ruled surface spanned by an
  `O`-avoiding non-separating band arc is in general a *genuinely singular*
  disc, and no proof of the Layer-B step can rest on the chord square being
  embedded: a uniform proof has to handle singular spanning discs, i.e. the
  content of Dehn's lemma.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section
open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

set_option linter.unnecessarySeqFocus false

namespace Work.Drive

/-! ## 1. The round circle has no trisecants -/

/-- The round circle has unit norm. -/
lemma norm_standardCircle (t : ℝ) : ‖standardCircle t‖ = 1 := by
  have h : ‖standardCircle t‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [standardCircle, Fin.sum_univ_three]
  nlinarith [norm_nonneg (standardCircle t)]

/-- Every point of the knot of the round circle has unit norm. -/
lemma norm_knotMap_standardCircle (z : AddCircle period) :
    ‖knotMap standardCircle z‖ = 1 := by
  rcases knotMap_representative z with ⟨t, ht, htz⟩
  rw [← htz, knotMap_coe standardCircle ht, norm_standardCircle]

/-- **No knot point of the round circle lies strictly inside a chord**: the
open segment between two distinct points of the unit circle stays strictly
inside the open unit ball (strict convexity of the Euclidean norm). -/
lemma not_mem_openSegment_standardCircle {a b m : AddCircle period} (hab : a ≠ b) :
    ¬ IsMiddleOnChord standardCircle a b m := by
  rintro ⟨s1, s2, hs1, hs2, hsum, hz⟩
  have hne : knotMap standardCircle a ≠ knotMap standardCircle b := by
    intro hc; exact hab (knotMap_injective standardCircle_isSmoothKnot hc)
  have h1 : ‖knotMap standardCircle a‖ ≤ 1 := le_of_eq (norm_knotMap_standardCircle a)
  have h2 : ‖knotMap standardCircle b‖ ≤ 1 := le_of_eq (norm_knotMap_standardCircle b)
  have hlt := norm_combo_lt_of_ne h1 h2 hne hs1 hs2 hsum
  rw [hz, norm_knotMap_standardCircle m] at hlt
  exact lt_irrefl 1 hlt

/-- **The trisecant locus `O` of the round circle is empty.** -/
theorem trisecantSet_standardCircle_eq_empty : trisecantSet standardCircle = ∅ := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨m, p, -, hm⟩
  exact not_mem_openSegment_standardCircle p.2 hm

/-! ## 2. An explicit non-separating band arc over the round circle -/

/-- The affine band arc over the round circle: the two branches are the
parameter classes `2·period·s` and `3·period·s`; the corresponding chords
sweep the knot once (the branch `3·period·s` gains exactly one period on the
branch `2·period·s`). -/
noncomputable def circleBandArc : BandArcData where
  a s := ((2 * period * (s : ℝ) : ℝ) : AddCircle period)
  b s := ((3 * period * (s : ℝ) : ℝ) : AddCircle period)
  cont_a := by fun_prop
  cont_b := by fun_prop
  collapse_left := by simp
  collapse_right := by
    have h1 : ((1 : I) : ℝ) = 1 := rfl
    rw [h1]
    have h2 : (2 * period * (1 : ℝ) : ℝ) = (period : ℝ) + period := by ring
    have h3 : (3 * period * (1 : ℝ) : ℝ) = (period : ℝ) + ((period : ℝ) + period) := by ring
    rw [h2, h3, AddCircle.coe_add, AddCircle.coe_add, AddCircle.coe_add, AddCircle.coe_period]
    abel
  offdiag := by
    intro s hs0 hs1 hPa
    have hzero : ((period * (s : ℝ) : ℝ) : AddCircle period) = 0 := by
      have hsub : ((3 * period * (s : ℝ) : ℝ) : AddCircle period) -
            ((2 * period * (s : ℝ) : ℝ) : AddCircle period) =
          ((period * (s : ℝ) : ℝ) : AddCircle period) := by
        rw [← AddCircle.coe_sub]
        congr 1
        ring
      rw [hPa, sub_self] at hsub
      exact hsub.symm
    rw [AddCircle.coe_eq_zero_iff] at hzero
    obtain ⟨n, hn⟩ := hzero
    have hn' : (n : ℝ) * period = period * (s : ℝ) := by
      rw [zsmul_eq_mul] at hn
      linarith
    have hs : (s : ℝ) = (n : ℝ) := by
      have hcancel : period * (n : ℝ) = period * (s : ℝ) := by linarith
      exact (mul_left_cancel₀ period_ne_zero hcancel).symm
    have hn0 : (0 : ℤ) ≤ n := by
      have : (0 : ℝ) ≤ (n : ℝ) := by rw [← hs]; exact s.2.1
      exact_mod_cast this
    have hn1 : n ≤ 1 := by
      have : (n : ℝ) ≤ 1 := by rw [← hs]; exact s.2.2
      exact_mod_cast this
    interval_cases n
    · exact hs0 (by rw [hs]; norm_num)
    · exact hs1 (by rw [hs]; norm_num)

/-- The affine band arc is non-separating. -/
lemma circleBandArc_nonSeparating : BandArcNonSeparating circleBandArc := by
  refine ⟨fun s : I => 2 * period * (s : ℝ), fun s : I => 3 * period * (s : ℝ),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · fun_prop
  · intro s; rfl
  · intro s; rfl
  · simp
  · show 3 * period * ((1 : I) : ℝ) = 2 * period * ((1 : I) : ℝ) + period
    have h1 : ((1 : I) : ℝ) = 1 := rfl
    rw [h1]; ring

/-- **The brick-(d) hypothesis is satisfiable**: the round circle admits a
non-separating band arc avoiding its (empty) trisecant locus. -/
theorem nonSeparatingArcAvoidingO_standardCircle :
    NonSeparatingArcAvoidingO standardCircle := by
  refine ⟨circleBandArc, circleBandArc_nonSeparating, ?_⟩
  intro s hs0 hs1
  rw [trisecantSet_standardCircle_eq_empty]
  simp

/-! ## 3. The chord square over `circleBandArc` is not injective -/

/-- The chord parameter `s = 1/2`. -/
noncomputable def halfI : I := ⟨1/2, by constructor <;> norm_num⟩

/-- The chord parameter `s = 3/5`. -/
noncomputable def threeFifthsI : I := ⟨3/5, by constructor <;> norm_num⟩

/-- The chord fraction `(1 - cos(2π/5))/2` at which the chord of `s = 1/2`
meets the chord of `s = 3/5`. -/
noncomputable def crossingParam : I := ⟨(1 - Real.cos (2 * Real.pi / 5)) / 2, by
  constructor
  · have h := Real.cos_le_one (2 * Real.pi / 5); linarith
  · have h := Real.neg_one_le_cos (2 * Real.pi / 5); linarith⟩

/-- The chord over `s = 1/2` is the diameter from `standardCircle 0` to
`standardCircle π`; the parametrized chord square at the crossing fraction
`(1 - cos(2π/5))/2` is `(cos(2π/5), 0, 0)`. -/
lemma chordFamilyDisk_circleBandArc_left :
    chordFamilyDisk standardCircle circleBandArc (halfI, crossingParam)
      = (!₂[Real.cos (2 * Real.pi / 5), 0, 0] : Space) := by
  have ha1 : circleBandArc.a halfI = 0 := by
    show ((2 * period * (halfI : ℝ) : ℝ) : AddCircle period) = 0
    have h : (2 * period * (halfI : ℝ) : ℝ) = (period : ℝ) := by
      show 2 * period * (1/2) = (period : ℝ); ring
    rw [h]; exact AddCircle.coe_period period
  have hb1 : circleBandArc.b halfI = ((Real.pi : ℝ) : AddCircle period) := by
    show ((3 * period * (halfI : ℝ) : ℝ) : AddCircle period) = _
    have h : (3 * period * (halfI : ℝ) : ℝ) = Real.pi + period := by
      show 3 * period * (1/2) = Real.pi + period
      rw [period]; ring
    rw [h, AddCircle.coe_add_period]
  have hK0 : knotMap standardCircle (0 : AddCircle period) = (!₂[(1:ℝ), 0, 0] : Space) := by
    have h := knotMap_coe standardCircle
      (show (0:ℝ) ∈ Set.Ico 0 period from ⟨le_rfl, period_pos⟩)
    simpa [standardCircle] using h
  have hKpi : knotMap standardCircle ((Real.pi : ℝ) : AddCircle period) =
      (!₂[(-1:ℝ), 0, 0] : Space) := by
    have hmem : (Real.pi : ℝ) ∈ Set.Ico 0 period :=
      ⟨Real.pi_pos.le, by rw [period]; linarith [Real.pi_pos]⟩
    rw [knotMap_coe standardCircle hmem]
    ext i; fin_cases i <;> simp [standardCircle, Real.cos_pi, Real.sin_pi]
  unfold chordFamilyDisk
  simp only [ha1, hb1, hK0, hKpi, crossingParam]
  ext i
  fin_cases i <;> simp <;> ring

/-- The chord over `s = 3/5` joins the points of the round circle at angles
`2π/5` and `8π/5`; its midpoint is again `(cos(2π/5), 0, 0)`. -/
lemma chordFamilyDisk_circleBandArc_right :
    chordFamilyDisk standardCircle circleBandArc (threeFifthsI, halfI)
      = (!₂[Real.cos (2 * Real.pi / 5), 0, 0] : Space) := by
  have ha2 : circleBandArc.a threeFifthsI = ((2 * Real.pi / 5 : ℝ) : AddCircle period) := by
    show ((2 * period * (threeFifthsI : ℝ) : ℝ) : AddCircle period) = _
    have h : (2 * period * (threeFifthsI : ℝ) : ℝ) = 2 * Real.pi / 5 + period := by
      show 2 * period * (3/5) = 2 * Real.pi / 5 + period
      rw [period]; ring
    rw [h, AddCircle.coe_add_period]
  have hb2 : circleBandArc.b threeFifthsI = ((8 * Real.pi / 5 : ℝ) : AddCircle period) := by
    show ((3 * period * (threeFifthsI : ℝ) : ℝ) : AddCircle period) = _
    have h : (3 * period * (threeFifthsI : ℝ) : ℝ) = 8 * Real.pi / 5 + period := by
      show 3 * period * (3/5) = 8 * Real.pi / 5 + period
      rw [period]; ring
    rw [h, AddCircle.coe_add_period]
  have hA : knotMap standardCircle ((2 * Real.pi / 5 : ℝ) : AddCircle period) =
      (!₂[Real.cos (2 * Real.pi / 5), Real.sin (2 * Real.pi / 5), 0] : Space) := by
    have hmem : (2 * Real.pi / 5 : ℝ) ∈ Set.Ico 0 period :=
      ⟨by linarith [Real.pi_pos], by rw [period]; linarith [Real.pi_pos]⟩
    rw [knotMap_coe standardCircle hmem]
    ext i; fin_cases i <;> simp [standardCircle]
  have hB : knotMap standardCircle ((8 * Real.pi / 5 : ℝ) : AddCircle period) =
      (!₂[Real.cos (8 * Real.pi / 5), Real.sin (8 * Real.pi / 5), 0] : Space) := by
    have hmem : (8 * Real.pi / 5 : ℝ) ∈ Set.Ico 0 period :=
      ⟨by linarith [Real.pi_pos], by rw [period]; linarith [Real.pi_pos]⟩
    rw [knotMap_coe standardCircle hmem]
    ext i; fin_cases i <;> simp [standardCircle]
  have hcos : Real.cos (8 * Real.pi / 5) = Real.cos (2 * Real.pi / 5) := by
    rw [show 8 * Real.pi / 5 = 2 * Real.pi - 2 * Real.pi / 5 by ring, Real.cos_two_pi_sub]
  have hsin : Real.sin (8 * Real.pi / 5) = -Real.sin (2 * Real.pi / 5) := by
    rw [show 8 * Real.pi / 5 = 2 * Real.pi - 2 * Real.pi / 5 by ring, Real.sin_two_pi_sub]
  unfold chordFamilyDisk
  simp only [ha2, hb2, hA, hB, hcos, hsin, halfI]
  ext i
  fin_cases i <;> simp <;> ring

/-- **The chord square over the avoiding non-separating band arc
`circleBandArc` is not injective.**  The two distinct square parameters
`(1/2, (1-cos(2π/5))/2)` and `(3/5, 1/2)` have the same image: the two chords
cross at `(cos(2π/5), 0, 0)`.  Hence an `O`-avoiding non-separating band arc
need not span an *embedded* disc. -/
theorem not_injective_chordFamilyDisk_circleBandArc :
    ¬ Function.Injective (chordFamilyDisk standardCircle circleBandArc) := by
  intro hinj
  have hval : chordFamilyDisk standardCircle circleBandArc (halfI, crossingParam) =
      chordFamilyDisk standardCircle circleBandArc (threeFifthsI, halfI) := by
    rw [chordFamilyDisk_circleBandArc_left, chordFamilyDisk_circleBandArc_right]
  have hne : (halfI, crossingParam) ≠ (threeFifthsI, halfI) := by
    intro h
    have h₁ : (halfI : ℝ) = (threeFifthsI : ℝ) :=
      congrArg (fun q : I × I => (q.1 : ℝ)) h
    simp only [halfI, threeFifthsI] at h₁
    norm_num at h₁
  exact hne (hinj hval)

end Work.Drive
