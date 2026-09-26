import Mathlib
import Submission.Work.Smooth.SphereJordan.planeThetaCurves
import Submission.Work.Smooth.SphereJordan.DiscCurve
import Submission.Work.Smooth.SphereJordan.discCurveSpans
import Submission.Work.SphereJordan.incrOn
import Submission.Work.SphereJordan.odd_windNumber_of_mem_V
import Submission.Work.Smooth.SphereJordan.thetaTwoHalvesSphereOfPlane
import Submission.Work.Smooth.SphereJordan.windNumber_eq_zero_or_odd

/-!
# The winding numbers of the four-arc curves of the plane theta graph

The side determination for the plane theta graph (`Work.Smooth.SphereJordan.thetaSideDetermination`)
is reduced here to the computation of the winding numbers of the four-arc curves
`ThetaSetup.cur i j` about points of the two discs.

The engine is the *argument increment* `Work.SphereJordan.incr` of a nowhere vanishing path: the
increment of two closed curves differs by the difference of the increments of the pieces in which
they differ.  Concretely, with `angPath F x = (ψ ↦ F (e^{iψ}) - x)`,

* the increment of the boundary arc `discArc F a b` of the disc `F` is the increment of the
  straight angle path `seg (angPath F x) a b` (`incr_discArc_eq`),
* the increments of the straight angle paths are additive in the angle interval, invariant under
  translation by `2π` and change sign under reversal (`incr_seg_add`, `incr_seg_periodic`,
  `incr_seg_rev`),
* therefore the two boundary arcs of `F` between the same two boundary angles, `discArc F a b` and
  `discArc F a (b - 2π)`, have increments differing by the increment of a full turn
  (`incr_discArc_diff`),
* and the increment of a full turn starting at any angle is `2πI` times the winding number of the
  boundary curve of `F` about `x` (`incr_seg_full`, `incr_seg_windNumber`).

Since the four-arc curves `cur true j` and `cur false j` differ exactly in one boundary arc of `D₁`
(the arcs `α`, `arcB j` and `β` being common), their winding numbers about a point `x` off `D₁`
differ by the winding number of `∂D₁` about `x` — which is odd, hence non-zero, when `x` is an
interior point of `D₁`.  And each of the two winding numbers is either `0` or odd (a point off a
simple closed curve lies on one of its two sides, where the winding number is `0`, respectively
odd).  Hence exactly one of the two curves has winding number `0` about `x`, which is
`thetaSideDetermination`'s side choice.
-/

set_option maxHeartbeats 1000000

open Set

namespace Work.Smooth.SphereJordan

open Work.SphereJordan

noncomputable section

/-! ## The angle path of a disc map -/

/-- The path `ψ ↦ F (e^{iψ}) - x` in the angle variable. -/
def angPath (F : C(Disc, ℂ)) (x : ℂ) : ℝ → ℂ := fun ψ => F (circlePoint ψ) - x

theorem continuous_angPath (F : C(Disc, ℂ)) (x : ℂ) : Continuous (angPath F x) :=
  (F.continuous.comp Work.Smooth.SphereJordan.continuous_circlePoint).sub continuous_const

theorem angPath_periodic (F : C(Disc, ℂ)) (x : ℂ) :
    Function.Periodic (angPath F x) (2 * Real.pi) := by
  intro ψ
  simp only [angPath]
  rw [circlePoint_add_two_pi]

@[simp] theorem angPath_apply (F : C(Disc, ℂ)) (x : ℂ) (ψ : ℝ) :
    angPath F x ψ = F (circlePoint ψ) - x := rfl

theorem angPath_ne (F : C(Disc, ℂ)) {x : ℂ} (hx : ∀ ψ : ℝ, F (circlePoint ψ) ≠ x) :
    ∀ ψ : ℝ, angPath F x ψ ≠ 0 := fun ψ => sub_ne_zero.mpr (hx ψ)

/-- The straight path `t ↦ N (a + (b - a) t)` in the angle variable. -/
def seg (N : ℝ → ℂ) (hN : Continuous N) (a b : ℝ) : C(unitInterval, ℂ) :=
  ⟨fun t => N (a + (b - a) * (t : ℝ)), hN.comp (by fun_prop)⟩

@[simp] theorem seg_apply (N : ℝ → ℂ) (hN : Continuous N) (a b : ℝ) (t : unitInterval) :
    seg N hN a b t = N (a + (b - a) * (t : ℝ)) := rfl

theorem seg_zero (N : ℝ → ℂ) (hN : Continuous N) (a b : ℝ) : seg N hN a b 0 = N a := by
  rw [seg_apply]
  norm_num

theorem seg_one (N : ℝ → ℂ) (hN : Continuous N) (a b : ℝ) : seg N hN a b 1 = N b := by
  rw [seg_apply]
  congr 1
  push_cast
  ring

/-- A straight angle path is nowhere vanishing when the angle path is. -/
theorem seg_ne {N : ℝ → ℂ} {hN : Continuous N} (h : ∀ ψ, N ψ ≠ 0) (a b : ℝ) :
    ∀ t : unitInterval, seg N hN a b t ≠ 0 := fun t => h _

/-- A path, translated by `-x`, as a path on the unit interval. -/
def subC (u : C(unitInterval, ℂ)) (x : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => u t - x, u.continuous.sub continuous_const⟩

@[simp] theorem subC_apply (u : C(unitInterval, ℂ)) (x : ℂ) (t : unitInterval) :
    subC u x t = u t - x := rfl

/-! ## Elementary reparametrisations of the unit interval -/

private theorem one_sub_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    1 - x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by linarith [hx.2], by linarith [hx.1]⟩

private theorem mul_mem {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    r * x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨mul_nonneg h0 hx.1, by nlinarith [hx.1, hx.2, h0, h1]⟩

private theorem aff_mem {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    r + (1 - r) * x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by nlinarith [hx.1, hx.2, h0, h1], by nlinarith [hx.1, hx.2, h0, h1]⟩

/-- The reversal `t ↦ 1 - t` of the unit interval. -/
abbrev flip : C(unitInterval, unitInterval) :=
  ⟨fun t => ⟨1 - (t : ℝ), one_sub_mem t.2⟩,
    Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) (fun t => one_sub_mem t.2)⟩

@[simp] theorem flip_apply (t : unitInterval) : ((flip t : unitInterval) : ℝ) = 1 - (t : ℝ) := rfl

theorem flip_zero : flip 0 = 1 := by
  apply Subtype.ext
  simp [flip]

theorem flip_one : flip 1 = 0 := by
  apply Subtype.ext
  simp [flip]

/-- The affine reparametrisation `t ↦ r * t` of the unit interval onto `[0,r]`. -/
abbrev firstMap (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : C(unitInterval, unitInterval) :=
  ⟨fun t => ⟨r * (t : ℝ), mul_mem h0 h1 t.2⟩,
    Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) (fun t => mul_mem h0 h1 t.2)⟩

/-- The affine reparametrisation `t ↦ r + (1 - r) * t` of the unit interval onto `[r,1]`. -/
abbrev secondMap (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : C(unitInterval, unitInterval) :=
  ⟨fun t => ⟨r + (1 - r) * (t : ℝ), aff_mem h0 h1 t.2⟩,
    Continuous.subtype_mk
      (continuous_const.add ((continuous_const.sub continuous_const).mul continuous_subtype_val))
      (fun t => aff_mem h0 h1 t.2)⟩

@[simp] theorem firstMap_apply (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (t : unitInterval) :
    ((firstMap r h0 h1 t : unitInterval) : ℝ) = r * (t : ℝ) := rfl

@[simp] theorem secondMap_apply (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (t : unitInterval) :
    ((secondMap r h0 h1 t : unitInterval) : ℝ) = r + (1 - r) * (t : ℝ) := rfl

theorem firstMap_zero (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : firstMap r h0 h1 0 = 0 := by
  apply Subtype.ext
  simp [firstMap]

theorem firstMap_one (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    firstMap r h0 h1 1 = ⟨r, h0, h1⟩ := by
  apply Subtype.ext
  simp [firstMap]

theorem secondMap_zero (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    secondMap r h0 h1 0 = ⟨r, h0, h1⟩ := by
  apply Subtype.ext
  simp [secondMap]

theorem secondMap_one (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : secondMap r h0 h1 1 = 1 := by
  apply Subtype.ext
  simp [secondMap]

/-! ## The increments of the straight angle paths -/

/-- **The increment changes sign under reversal of the path.** -/
theorem incr_flip {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) :
    incr (c := c.comp flip) (fun t => hc _) = - incr hc := by
  have hlift : ∀ t, Complex.exp (((liftOf hc).comp flip) t) = (c.comp flip) t := by
    intro t
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
    exact exp_liftOf hc (flip t)
  have h1 := incr_spec (c := c.comp flip) (fun t => hc _) ((liftOf hc).comp flip) hlift
  rw [show incr (c := c.comp flip) (fun t => hc _)
      = (liftOf hc) (flip 1) - (liftOf hc) (flip 0) from h1.symm, flip_one, flip_zero, incr]
  ring

/-- **Splitting the increment of a path at an intermediate point.** -/
theorem incr_split {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) {r : ℝ} (h0 : 0 ≤ r)
    (h1 : r ≤ 1) :
    incr hc =
      incr (c := c.comp (firstMap r h0 h1)) (fun t => hc _) +
      incr (c := c.comp (secondMap r h0 h1)) (fun t => hc _) := by
  have hΛ : ∀ t, Complex.exp (liftOf hc t) = c t := exp_liftOf hc
  have key : ∀ (σ : C(unitInterval, unitInterval)),
      incr (c := c.comp σ) (fun t => hc _) = (liftOf hc) (σ 1) - (liftOf hc) (σ 0) := by
    intro σ
    have hlift : ∀ t, Complex.exp (((liftOf hc).comp σ) t) = (c.comp σ) t := by
      intro t
      rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
      exact hΛ (σ t)
    exact (incr_spec (c := c.comp σ) (fun t => hc _) ((liftOf hc).comp σ) hlift).symm
  have e1 := key (firstMap r h0 h1)
  have e2 := key (secondMap r h0 h1)
  rw [e1, e2, firstMap_one, firstMap_zero, secondMap_one, secondMap_zero]
  simp only [incr]
  ring

/-- **The increment of a straight angle path is additive in the angle interval.** -/
theorem incr_seg_add {N : ℝ → ℂ} {hN : Continuous N} (h : ∀ ψ, N ψ ≠ 0) {a b c : ℝ}
    (hab : a < b) (hbc : b < c) :
    incr (c := seg N hN a c) (seg_ne (hN := hN) h a c) =
      incr (c := seg N hN a b) (seg_ne (hN := hN) h a b) +
        incr (c := seg N hN b c) (seg_ne (hN := hN) h b c) := by
  have hden : (0 : ℝ) < c - a := by linarith
  have hr0 : 0 ≤ (b - a) / (c - a) := div_nonneg (by linarith) hden.le
  have hr1 : (b - a) / (c - a) ≤ 1 := by
    rw [div_le_one hden]; linarith
  have hsplit := incr_split (c := seg N hN a c) (r := (b - a) / (c - a))
    (seg_ne (hN := hN) h a c) hr0 hr1
  rw [hsplit]
  have hkey : (c - a) * ((b - a) / (c - a)) = b - a := by field_simp
  have hkey2 : (c - a) * (1 - (b - a) / (c - a)) = c - b := by
    rw [mul_sub, mul_one, hkey]; ring
  have h1 : (seg N hN a c).comp (firstMap ((b - a) / (c - a)) hr0 hr1) = seg N hN a b := by
    ext t
    rw [ContinuousMap.comp_apply, seg_apply, seg_apply, firstMap_apply]
    congr 1
    rw [← mul_assoc, hkey]
  have h2 : (seg N hN a c).comp (secondMap ((b - a) / (c - a)) hr0 hr1) = seg N hN b c := by
    ext t
    rw [ContinuousMap.comp_apply, seg_apply, seg_apply, secondMap_apply]
    congr 1
    rw [mul_add, hkey, ← mul_assoc, hkey2]
    ring
  have e1 : incr (c := (seg N hN a c).comp (firstMap ((b - a) / (c - a)) hr0 hr1))
      (fun t => seg_ne (hN := hN) h a c _) = incr (c := seg N hN a b) (seg_ne (hN := hN) h a b) :=
    incr_congr _ _ (fun t => by rw [h1])
  have e2 : incr (c := (seg N hN a c).comp (secondMap ((b - a) / (c - a)) hr0 hr1))
      (fun t => seg_ne (hN := hN) h a c _) = incr (c := seg N hN b c) (seg_ne (hN := hN) h b c) :=
    incr_congr _ _ (fun t => by rw [h2])
  rw [e1, e2]

/-- **The increment of a straight angle path is invariant under translation by a period.** -/
theorem incr_seg_periodic {N : ℝ → ℂ} {hN : Continuous N} (hper : Function.Periodic N (2 * Real.pi))
    (h : ∀ ψ, N ψ ≠ 0) (a b : ℝ) :
    incr (c := seg N hN (a + 2 * Real.pi) (b + 2 * Real.pi)) (seg_ne (hN := hN) h _ _) =
      incr (c := seg N hN a b) (seg_ne (hN := hN) h a b) := by
  refine incr_congr (seg_ne (hN := hN) h _ _) (seg_ne (hN := hN) h a b) (fun t => ?_)
  rw [seg_apply, seg_apply]
  have h1 : a + 2 * Real.pi + (b + 2 * Real.pi - (a + 2 * Real.pi)) * (t : ℝ)
      = (a + (b - a) * (t : ℝ)) + 2 * Real.pi := by ring
  rw [h1, hper]

/-- **Reversal of the angle interval negates the increment.** -/
theorem incr_seg_rev {N : ℝ → ℂ} {hN : Continuous N} (h : ∀ ψ, N ψ ≠ 0) (a b : ℝ) :
    incr (c := seg N hN b a) (seg_ne (hN := hN) h b a) =
      - incr (c := seg N hN a b) (seg_ne (hN := hN) h a b) := by
  have hcomp : ∀ t : unitInterval, (seg N hN a b).comp flip t ≠ 0 :=
    fun t => seg_ne (hN := hN) h a b (flip t)
  have hrev := incr_flip (c := seg N hN a b) (seg_ne (hN := hN) h a b)
  have hcongr : incr (c := seg N hN b a) (seg_ne (hN := hN) h b a) =
      incr (c := (seg N hN a b).comp flip) hcomp := by
    refine incr_congr (seg_ne (hN := hN) h b a) hcomp (fun t => ?_)
    rw [seg_apply, ContinuousMap.comp_apply, seg_apply, flip_apply]
    congr 1
    ring
  rw [hcongr, hrev]

/-- **The increment of a full turn is independent of the starting angle.** -/
theorem incr_seg_full {N : ℝ → ℂ} {hN : Continuous N} (hper : Function.Periodic N (2 * Real.pi))
    (h : ∀ ψ, N ψ ≠ 0) (b : ℝ) :
    incr (c := seg N hN b (b + 2 * Real.pi)) (seg_ne (hN := hN) h _ _) =
      incr (c := seg N hN 0 (2 * Real.pi)) (seg_ne (hN := hN) h 0 (2 * Real.pi)) := by
  have hclosed₁ : (seg N hN b (b + 2 * Real.pi)) 0 = (seg N hN b (b + 2 * Real.pi)) 1 := by
    rw [seg_zero, seg_one]
    exact (hper b).symm
  have hclosed₂ : (seg N hN 0 (2 * Real.pi)) 0 = (seg N hN 0 (2 * Real.pi)) 1 := by
    rw [seg_zero, seg_one]
    simpa using (hper 0).symm
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => N (b * (p.2 : ℝ) + 2 * Real.pi * (p.1 : ℝ)), by fun_prop⟩
  have hHne : ∀ p : unitInterval × unitInterval, H p ≠ 0 := by
    rintro ⟨t, s⟩
    show N (b * (s : ℝ) + 2 * Real.pi * (t : ℝ)) ≠ 0
    exact h _
  have hH0 : ∀ t : unitInterval, H (t, 0) = seg N hN 0 (2 * Real.pi) t := by
    intro t
    have hzero : (((0 : unitInterval)) : ℝ) = 0 := by norm_num
    show N (b * (((0 : unitInterval)) : ℝ) + 2 * Real.pi * (t : ℝ))
      = N (0 + (2 * Real.pi - 0) * (t : ℝ))
    rw [hzero]
    congr 1
    ring
  have hH1 : ∀ t : unitInterval, H (t, 1) = seg N hN b (b + 2 * Real.pi) t := by
    intro t
    have hone : (((1 : unitInterval)) : ℝ) = 1 := by norm_num
    show N (b * (((1 : unitInterval)) : ℝ) + 2 * Real.pi * (t : ℝ))
      = N (b + (b + 2 * Real.pi - b) * (t : ℝ))
    rw [hone]
    congr 1
    ring
  have hHloop : ∀ s : unitInterval, H (0, s) = H (1, s) := by
    intro s
    have hzero : (((0 : unitInterval)) : ℝ) = 0 := by norm_num
    have hone : (((1 : unitInterval)) : ℝ) = 1 := by norm_num
    show N (b * (s : ℝ) + 2 * Real.pi * (((0 : unitInterval)) : ℝ))
      = N (b * (s : ℝ) + 2 * Real.pi * (((1 : unitInterval)) : ℝ))
    rw [hzero, hone]
    rw [show b * (s : ℝ) + 2 * Real.pi * 0 = b * (s : ℝ) from by ring,
      show b * (s : ℝ) + 2 * Real.pi * 1 = b * (s : ℝ) + 2 * Real.pi from by ring, hper]
  have hmain : loopIndex (seg N hN 0 (2 * Real.pi)) = loopIndex (seg N hN b (b + 2 * Real.pi)) :=
    loopIndex_eq_of_homotopy (seg_ne (hN := hN) h 0 (2 * Real.pi))
      (seg_ne (hN := hN) h b (b + 2 * Real.pi)) H hHne hH0 hH1 hHloop
  rw [incr_eq_loopIndex (c := seg N hN b (b + 2 * Real.pi)) (seg_ne (hN := hN) h b (b + 2 * Real.pi)) hclosed₁,
    incr_eq_loopIndex (c := seg N hN 0 (2 * Real.pi)) (seg_ne (hN := hN) h 0 (2 * Real.pi)) hclosed₂, hmain]

private theorem sub_eq_of_add_eq_neg {A B B' C : ℂ} (h1 : B = -B') (h2 : A + B' = C) : A - B = C := by
  rw [h1, sub_neg_eq_add]
  exact h2

/-- **The difference of the increments of complementary angle intervals.**  The two intervals
`[a,b]` and `[a,b-2π]` of the angle circle have increments differing by the increment of a full
turn, which is independent of its starting angle. -/
theorem incr_seg_complementary {N : ℝ → ℂ} {hN : Continuous N} (hper : Function.Periodic N (2 * Real.pi))
    (h : ∀ ψ, N ψ ≠ 0) {a b : ℝ} (hab : a < b) (hub : b < a + 2 * Real.pi) :
    incr (c := seg N hN a b) (seg_ne (hN := hN) h a b) -
        incr (c := seg N hN a (b - 2 * Real.pi)) (seg_ne (hN := hN) h a (b - 2 * Real.pi))
      = incr (c := seg N hN 0 (2 * Real.pi)) (seg_ne (hN := hN) h 0 (2 * Real.pi)) := by
  have hlow : b - 2 * Real.pi < a := by linarith
  have hadd := incr_seg_add (hN := hN) h hlow hab
  have hshift := incr_seg_periodic (hN := hN) hper h (b - 2 * Real.pi) b
  have hbase := incr_seg_full (hN := hN) hper h b
  have hrev : incr (c := seg N hN a (b - 2 * Real.pi)) (seg_ne (hN := hN) h a (b - 2 * Real.pi))
      = - incr (c := seg N hN (b - 2 * Real.pi) a) (seg_ne (hN := hN) h (b - 2 * Real.pi) a) :=
    incr_seg_rev (hN := hN) h (b - 2 * Real.pi) a
  have e1 : incr (c := seg N hN a b) (seg_ne (hN := hN) h a b)
      - incr (c := seg N hN a (b - 2 * Real.pi)) (seg_ne (hN := hN) h a (b - 2 * Real.pi))
      = incr (c := seg N hN a b) (seg_ne (hN := hN) h a b)
        + incr (c := seg N hN (b - 2 * Real.pi) a) (seg_ne (hN := hN) h (b - 2 * Real.pi) a) := by
    rw [hrev]; ring
  have e2 : incr (c := seg N hN a b) (seg_ne (hN := hN) h a b)
      + incr (c := seg N hN (b - 2 * Real.pi) a) (seg_ne (hN := hN) h (b - 2 * Real.pi) a)
      = incr (c := seg N hN (b - 2 * Real.pi) b) (seg_ne (hN := hN) h (b - 2 * Real.pi) b) := by
    simpa [add_comm] using hadd.symm
  have hshift' : incr (c := seg N hN b (b + 2 * Real.pi)) (seg_ne (hN := hN) h b (b + 2 * Real.pi))
      = incr (c := seg N hN (b - 2 * Real.pi) b) (seg_ne (hN := hN) h (b - 2 * Real.pi) b) := by
    simpa using hshift
  exact e1.trans (e2.trans (by rw [← hshift', hbase]))

/-! ## The boundary arcs of a disc map -/

theorem discArc_sub_ne (F : C(Disc, ℂ)) {x : ℂ} (hx : ∀ ψ : ℝ, F (circlePoint ψ) ≠ x) (a b : ℝ) :
    ∀ t : unitInterval, subC (discArc F a b) x t ≠ 0 := by
  intro t h
  exact hx (a + (t : ℝ) * (b - a)) (by rw [← discArc_apply]; exact sub_eq_zero.mp h)

theorem seg_angPath_ne (F : C(Disc, ℂ)) {x : ℂ} (hx : ∀ ψ : ℝ, F (circlePoint ψ) ≠ x) (a b : ℝ) :
    ∀ t : unitInterval, seg (angPath F x) (continuous_angPath F x) a b t ≠ 0 :=
  seg_ne (hN := continuous_angPath F x) (angPath_ne F hx) a b

theorem seg_angPath_eq_subC_discArc (F : C(Disc, ℂ)) (x : ℂ) (a b : ℝ) (t : unitInterval) :
    seg (angPath F x) (continuous_angPath F x) a b t = subC (discArc F a b) x t := by
  rw [seg_apply, subC_apply, discArc_apply, angPath_apply, mul_comm]

/-- The increment of a boundary arc of a disc map is the increment of the corresponding straight
angle path. -/
theorem incr_discArc_eq (F : C(Disc, ℂ)) {x : ℂ} (hx : ∀ ψ : ℝ, F (circlePoint ψ) ≠ x) (a b : ℝ) :
    incr (c := subC (discArc F a b) x) (discArc_sub_ne F hx a b) =
      incr (c := seg (angPath F x) (continuous_angPath F x) a b) (seg_angPath_ne F hx a b) :=
  (incr_congr (seg_angPath_ne F hx a b) (discArc_sub_ne F hx a b)
    (fun t => seg_angPath_eq_subC_discArc F x a b t)).symm

/-- **The difference of the increments of the two boundary arcs of a disc map.**  The arcs
`discArc F a b` and `discArc F a (b - 2π)` are the two arcs of the boundary circle of `F` between
the angles `a` and `b`; the difference of their increments relative to a point `x ∉ range F` is the
increment of one full turn. -/
theorem incr_discArc_diff (F : C(Disc, ℂ)) {x : ℂ} (hx : ∀ ψ : ℝ, F (circlePoint ψ) ≠ x) {a b : ℝ}
    (hab : a < b) (hub : b < a + 2 * Real.pi) :
    incr (c := subC (discArc F a b) x) (discArc_sub_ne F hx a b) -
        incr (c := subC (discArc F a (b - 2 * Real.pi)) x) (discArc_sub_ne F hx a (b - 2 * Real.pi))
      = incr (c := seg (angPath F x) (continuous_angPath F x) 0 (2 * Real.pi))
          (seg_angPath_ne F hx 0 (2 * Real.pi)) := by
  rw [incr_discArc_eq F hx a b, incr_discArc_eq F hx a (b - 2 * Real.pi)]
  exact incr_seg_complementary (N := angPath F x) (hN := continuous_angPath F x)
    (angPath_periodic F x) (angPath_ne F hx) hab hub

/-- **The increment of a full angle turn is the winding number of the boundary curve.** -/
theorem incr_seg_windNumber (F : C(Disc, ℂ)) {x : ℂ} (hx : ∀ ψ : ℝ, F (circlePoint ψ) ≠ x) :
    incr (c := seg (angPath F x) (continuous_angPath F x) 0 (2 * Real.pi))
        (seg_angPath_ne F hx 0 (2 * Real.pi))
      = (windNumber (discCurve F).γ (discCurve F).cont x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hclosed : (seg (angPath F x) (continuous_angPath F x) 0 (2 * Real.pi)) 0
      = (seg (angPath F x) (continuous_angPath F x) 0 (2 * Real.pi)) 1 := by
    rw [seg_zero, seg_one]
    simpa using (angPath_periodic F x 0).symm
  have hc1 : ∀ t : unitInterval, (seg (angPath F x) (continuous_angPath F x) 0 (2 * Real.pi)) t ≠ 0 :=
    seg_angPath_ne F hx 0 (2 * Real.pi)
  have hc2 : ∀ t : unitInterval,
      curveLoop (fun t => (discCurve F).γ t - x)
        ((discCurve F).cont.sub continuous_const) t ≠ 0 := by
    intro t h
    exact (hx (2 * Real.pi * (t : ℝ))) (sub_eq_zero.mp h)
  have hld : curveLoop (fun t => (discCurve F).γ t - x)
        ((discCurve F).cont.sub continuous_const) 0
      = curveLoop (fun t => (discCurve F).γ t - x)
        ((discCurve F).cont.sub continuous_const) 1 := by
    show (discCurve F).γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - x
      = (discCurve F).γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - x
    rw [show (2 : ℝ) * Real.pi * ((0 : unitInterval) : ℝ) = 0 from by simp,
      show (2 : ℝ) * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi from by simp]
    rw [show (2 * Real.pi : ℝ) = 0 + 2 * Real.pi from by ring, (discCurve F).periodic_apply 0]
  have hmain : loopIndex (seg (angPath F x) (continuous_angPath F x) 0 (2 * Real.pi))
      = loopIndex (curveLoop (fun t => (discCurve F).γ t - x)
          ((discCurve F).cont.sub continuous_const)) :=
    loopIndex_congr (fun t => by
      show seg (angPath F x) (continuous_angPath F x) 0 (2 * Real.pi) t
        = (discCurve F).γ (2 * Real.pi * (t : ℝ)) - x
      rw [seg_apply, angPath_apply, discCurve_apply]
      congr 1
      ring_nf) hc1 hc2 hclosed hld
  rw [incr_eq_loopIndex (c := seg (angPath F x) (continuous_angPath F x) 0 (2 * Real.pi))
    (seg_angPath_ne F hx 0 (2 * Real.pi)) hclosed, hmain]
  simp only [windNumber]


/-! ## The increment of a pointwise product and quotient -/

/-- **The increment is additive under pointwise products.** -/
theorem incr_mul {c d : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0) (hd : ∀ t, d t ≠ 0) :
    incr (c := c * d) (fun t => mul_ne_zero (hc t) (hd t)) = incr hc + incr hd := by
  have hlift : ∀ t, Complex.exp (((liftOf hc) + (liftOf hd)) t) = (c * d) t := by
    intro t
    rw [ContinuousMap.add_apply, Complex.exp_add, exp_liftOf hc t, exp_liftOf hd t]
    rfl
  have h1 : ((liftOf hc) + (liftOf hd)) 1 - ((liftOf hc) + (liftOf hd)) 0
      = incr (c := c * d) (fun t => mul_ne_zero (hc t) (hd t)) :=
    incr_spec (c := c * d) (fun t => mul_ne_zero (hc t) (hd t)) ((liftOf hc) + (liftOf hd)) hlift
  rw [← h1]
  simp only [ContinuousMap.add_apply, incr]
  ring

/-- The pointwise quotient of two paths. -/
def divC (u v : C(unitInterval, ℂ)) (hv : ∀ t, v t ≠ 0) : C(unitInterval, ℂ) :=
  ⟨fun t => u t / v t, u.continuous.div v.continuous hv⟩

@[simp] theorem divC_apply (u v : C(unitInterval, ℂ)) (hv : ∀ t, v t ≠ 0) (t : unitInterval) :
    divC u v hv t = u t / v t := rfl

/-- The pointwise quotient of a path by a nowhere vanishing path is nowhere vanishing. -/
theorem divC_ne {u v : C(unitInterval, ℂ)} (hu : ∀ t, u t ≠ 0) (hv : ∀ t, v t ≠ 0) :
    ∀ t, divC u v hv t ≠ 0 := fun t => div_ne_zero (hu t) (hv t)

/-- **The increment is additive under pointwise quotients.** -/
theorem incr_divC {u v : C(unitInterval, ℂ)} (hu : ∀ t, u t ≠ 0) (hv : ∀ t, v t ≠ 0) :
    incr (c := divC u v hv) (divC_ne hu hv) = incr hu - incr hv := by
  have hmul := incr_mul (c := divC u v hv) (d := v) (divC_ne hu hv) hv
  have hcongr : incr (c := divC u v hv * v)
      (fun t => mul_ne_zero (divC_ne hu hv t) (hv t)) = incr hu := by
    refine incr_congr _ hu (fun t => ?_)
    rw [ContinuousMap.mul_apply, divC_apply, div_mul_cancel₀ _ (hv t)]
  rw [hcongr] at hmul
  rw [hmul]
  ring

/-- **The increment of a constant path is zero.** -/
theorem incr_const (a : ℂ) (ha : a ≠ 0) :
    incr (c := ContinuousMap.const unitInterval a) (fun _ => ha) = 0 := by
  have hclosed : (ContinuousMap.const unitInterval a) 0 = (ContinuousMap.const unitInterval a) 1 := rfl
  have hΛ : ∀ t : unitInterval,
      Complex.exp ((ContinuousMap.const unitInterval (Complex.log a)) t)
        = (ContinuousMap.const unitInterval a) t := by
    intro t
    rw [ContinuousMap.const_apply, ContinuousMap.const_apply, Complex.exp_log ha]
  have h := loopIndex_eq_zero_of_lift (ContinuousMap.const unitInterval a) (fun _ => ha) hclosed
    (ContinuousMap.const unitInterval (Complex.log a)) hΛ rfl
  rw [incr_eq_loopIndex (c := ContinuousMap.const unitInterval a) (fun _ => ha) hclosed, h]
  simp

/-! ## The winding number of a four-arc curve as the index of its loop -/

/-- For a parameter in `[0,2π)` the boundary curve of the loop of the four arcs is the loop. -/
theorem curCurve_apply_of_lt {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂) (i j : Bool)
    {t : unitInterval} (ht : (t : ℝ) < 1) :
    (T.cur i j).γ (2 * Real.pi * (t : ℝ)) = T.loopC i j t := by
  have hmem : 2 * Real.pi * (t : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨mul_nonneg (by positivity) t.2.1, by nlinarith [t.2.1, ht, Real.pi_pos]⟩
  show (loopCurve (T.loopCf i j) (T.loopC_closed i j)).γ (2 * Real.pi * (t : ℝ)) = T.loopC i j t
  rw [loopCurve_apply_of_Ico (T.loopCf i j) (T.loopC_closed i j) hmem,
    loopFn_of_mem (T.loopCf i j) ⟨hmem.1, hmem.2.le⟩]
  change T.loopC i j ⟨2 * Real.pi * (t : ℝ) / (2 * Real.pi),
    ⟨div_nonneg hmem.1 Real.two_pi_pos.le, (div_le_one Real.two_pi_pos).mpr hmem.2.le⟩⟩
    = T.loopC i j t
  congr 1
  apply Subtype.ext
  field_simp

/-- **The winding number of a four-arc curve is the index of its translated loop.** -/
theorem cur_windNumber_eq {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂) (i j : Bool) {x : ℂ}
    (hx : x ∉ (T.cur i j).trace) :
    windNumber (T.cur i j).γ (T.cur i j).cont x = loopIndex (subC (T.loopCf i j) x) := by
  have hx' : x ∉ Set.range (T.loopCf i j) := by
    rw [← range_loopCurve (T.loopCf i j) (T.loopC_closed i j)]
    exact hx
  have hc1 : ∀ t : unitInterval,
      (curveLoop (fun s => (T.cur i j).γ s - x) ((T.cur i j).cont.sub continuous_const)) t ≠ 0 := by
    intro t h
    exact hx ⟨2 * Real.pi * (t : ℝ), sub_eq_zero.mp h⟩
  have hc2 : ∀ t : unitInterval, subC (T.loopCf i j) x t ≠ 0 :=
    fun t => sub_ne_zero.mpr (fun h => hx' ⟨t, h⟩)
  have hcl1 : (curveLoop (fun s => (T.cur i j).γ s - x)
      ((T.cur i j).cont.sub continuous_const)) 0
      = (curveLoop (fun s => (T.cur i j).γ s - x)
        ((T.cur i j).cont.sub continuous_const)) 1 := by
    show (T.cur i j).γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - x
      = (T.cur i j).γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - x
    rw [show (2 : ℝ) * Real.pi * ((0 : unitInterval) : ℝ) = 0 from by simp,
      show (2 : ℝ) * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi from by simp]
    rw [show (2 * Real.pi : ℝ) = 0 + 2 * Real.pi from by ring, (T.cur i j).periodic_apply 0]
  have hcl2 : subC (T.loopCf i j) x 0 = subC (T.loopCf i j) x 1 := by
    rw [subC_apply, subC_apply, show T.loopCf i j 0 = T.q from T.loopC_zero i j,
      show T.loopCf i j 1 = T.q from T.loopC_one i j]
  refine loopIndex_congr (fun t => ?_) hc1 hc2 hcl1 hcl2
  show (T.cur i j).γ (2 * Real.pi * (t : ℝ)) - x = T.loopC i j t - x
  rcases lt_or_eq_of_le t.2.2 with ht | ht
  · rw [curCurve_apply_of_lt T i j ht]
  · have ht1 : ((t : unitInterval) : ℝ) = 1 := by linarith [t.2.1]
    have hper : (T.cur i j).γ (2 * Real.pi * ((1 : unitInterval) : ℝ))
        = T.loopC i j (0 : unitInterval) := by
      have h1 : (2 : ℝ) * Real.pi * ((1 : unitInterval) : ℝ) = 0 + 2 * Real.pi := by
        simp only [Set.Icc.coe_one]; ring
      have h2 : (2 * Real.pi * ((0 : unitInterval) : ℝ)) = (0 : ℝ) := by
        simp only [Set.Icc.coe_zero]; ring
      rw [h1, (T.cur i j).periodic_apply 0, ← h2]
      exact curCurve_apply_of_lt T i j (t := 0) (by norm_num)
    rw [show t = (1 : unitInterval) from Subtype.ext ht1, hper]
    rw [show T.loopC i j (0 : unitInterval) = T.q from T.loopC_zero i j,
      show T.loopC i j 1 = T.q from T.loopC_one i j]

/-- The increment of the path `c` translated by `-x`, for a point `x` missed by `c`. -/
noncomputable def incrSub (c : C(unitInterval, ℂ)) (x : ℂ) (h : ∀ t : unitInterval, c t ≠ x) : ℂ :=
  incr (c := subC c x) (fun t => by rw [subC_apply]; exact sub_ne_zero.mpr (h t))

/-- **The increment of a concatenation of two paths** is the sum of the increments of the two
parts. -/
theorem incr_trans {A B D : ℂ} (p : Path A B) (q : Path B D) {x : ℂ}
    (hz : ∀ t : unitInterval, (p.trans q).toContinuousMap t ≠ x)
    (hp : ∀ t : unitInterval, p.toContinuousMap t ≠ x)
    (hq : ∀ t : unitInterval, q.toContinuousMap t ≠ x) :
    incrSub (p.trans q).toContinuousMap x hz
      = incrSub p.toContinuousMap x hp + incrSub q.toContinuousMap x hq := by
  have hz' : ∀ t : unitInterval, subC (p.trans q).toContinuousMap x t ≠ 0 :=
    fun t => by rw [subC_apply]; exact sub_ne_zero.mpr (hz t)
  have hp' : ∀ t : unitInterval, subC p.toContinuousMap x t ≠ 0 :=
    fun t => by rw [subC_apply]; exact sub_ne_zero.mpr (hp t)
  have hq' : ∀ t : unitInterval, subC q.toContinuousMap x t ≠ 0 :=
    fun t => by rw [subC_apply]; exact sub_ne_zero.mpr (hq t)
  show incr (c := subC (p.trans q).toContinuousMap x) hz'
    = incr (c := subC p.toContinuousMap x) hp' + incr (c := subC q.toContinuousMap x) hq'
  have h0 : (0:ℝ) ≤ 1/2 := by norm_num
  have h1 : (1/2:ℝ) ≤ 1 := by norm_num
  rw [incr_split (c := subC (p.trans q).toContinuousMap x) hz' h0 h1]
  congr 1
  · have key : ∀ t : unitInterval,
        ((subC (p.trans q).toContinuousMap x).comp (firstMap (1/2) h0 h1)) t
          = subC p.toContinuousMap x t := by
      intro t
      change (p.trans q) (firstMap (1/2) h0 h1 t) - x = p t - x
      congr 1
      rw [Path.trans_apply, dif_pos (by rw [firstMap_apply]; linarith [t.2.2])]
      congr 1
      apply Subtype.ext
      change (2 * ((firstMap (1/2) h0 h1 t : unitInterval) : ℝ)) = (t : ℝ)
      rw [firstMap_apply]
      ring
    exact incr_congr (fun t => by rw [key t]; exact hp' t) hp' key
  · have key : ∀ t : unitInterval,
        ((subC (p.trans q).toContinuousMap x).comp (secondMap (1/2) h0 h1)) t
          = subC q.toContinuousMap x t := by
      intro t
      change (p.trans q) (secondMap (1/2) h0 h1 t) - x = q t - x
      by_cases ht : (t:ℝ) = 0
      · have ht0 : t = (0 : unitInterval) := Subtype.ext (by rw [ht]; norm_num)
        rw [ht0]
        change (p.trans q) (secondMap (1/2) h0 h1 (0 : unitInterval)) - x = q 0 - x
        rw [show secondMap (1/2) h0 h1 (0 : unitInterval)
            = (⟨1/2, by norm_num⟩ : unitInterval) from
          Subtype.ext (by rw [secondMap_apply]; norm_num)]
        congr 1
        rw [Path.trans_apply, dif_pos (by norm_num)]
        rw [show (⟨2 * (1/2 : ℝ), by norm_num⟩ : unitInterval) = (1 : unitInterval) from
          Subtype.ext (by norm_num), Path.target, Path.source]
      · congr 1
        rw [Path.trans_apply, dif_neg (by
          rw [secondMap_apply]
          intro hcon
          exact ht (by linarith [t.2.1, hcon]))]
        congr 1
        apply Subtype.ext
        change (2 * ((secondMap (1/2) h0 h1 t : unitInterval) : ℝ)) - 1 = (t : ℝ)
        rw [secondMap_apply]
        ring
    exact incr_congr (fun t => by rw [key t]; exact hq' t) hq' key

/-- The value of a concatenation at the left endpoint. -/
theorem trans_zero {A B D : ℂ} (p : Path A B) (q : Path B D) :
    (p.trans q) (0 : unitInterval) = p 0 := by
  rw [Path.trans_apply, dif_pos (by norm_num)]
  congr 1
  apply Subtype.ext
  norm_num

/-- The value of a concatenation at the right endpoint. -/
theorem trans_one {A B D : ℂ} (p : Path A B) (q : Path B D) :
    (p.trans q) (1 : unitInterval) = q 1 := by
  rw [Path.trans_apply, dif_neg (by norm_num)]
  congr 1
  apply Subtype.ext
  norm_num

/-- **A point missed by a concatenation is missed by both parts.** -/
theorem trans_ne {A B D : ℂ} (p : Path A B) (q : Path B D) {x : ℂ}
    (hp : ∀ t : unitInterval, p.toContinuousMap t ≠ x)
    (hq : ∀ t : unitInterval, q.toContinuousMap t ≠ x) :
    ∀ t : unitInterval, (p.trans q).toContinuousMap t ≠ x := by
  intro t ht
  change (p.trans q) t = x at ht
  rw [Path.trans_apply] at ht
  split_ifs at ht
  · exact hp _ ht
  · exact hq _ ht


/-- **The difference of the winding numbers of the two four-arc curves differing in the `D₁`-arc.**
For a point `x` off both curves and off the boundary curve of `D₁`, the winding numbers of
`cur true j` and `cur false j` about `x` differ by the winding number of `∂D₁` about `x`. -/
theorem windNumber_cur_arcA_diff {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂) (j : Bool) {x : ℂ}
    (hx1 : x ∉ (T.cur true j).trace) (hx2 : x ∉ (T.cur false j).trace)
    (hxcirc : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ x) :
    windNumber (T.cur true j).γ (T.cur true j).cont x
      - windNumber (T.cur false j).γ (T.cur false j).cont x
      = windNumber (discCurve T.f).γ (discCurve T.f).cont x := by
  rw [cur_windNumber_eq T true j hx1, cur_windNumber_eq T false j hx2]
  rw [show T.loopCf true j
      = (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap
      from rfl,
    show T.loopCf false j
      = (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap
      from rfl]
  have hA1 : ∀ t : unitInterval, (T.pathA true).toContinuousMap t ≠ x := by
    intro t ht
    refine hx1 ?_
    rw [T.cur_range true j]
    exact Or.inl (Or.inl (Or.inl ⟨t, ht⟩))
  have hA2 : ∀ t : unitInterval, (T.pathA false).toContinuousMap t ≠ x := by
    intro t ht
    refine hx2 ?_
    rw [T.cur_range false j]
    exact Or.inl (Or.inl (Or.inl ⟨t, ht⟩))
  have hAl : ∀ t : unitInterval, T.pathα.toContinuousMap t ≠ x := by
    intro t ht
    refine hx1 ?_
    rw [T.cur_range true j]
    exact Or.inl (Or.inl (Or.inr ⟨t, ht⟩))
  have hB : ∀ t : unitInterval, (T.pathB j).toContinuousMap t ≠ x := by
    intro t ht
    refine hx1 ?_
    rw [T.cur_range true j]
    exact Or.inl (Or.inr ⟨t, ht⟩)
  have hxβ : x ∉ Set.range T.β := by
    intro hmem
    exact hx1 (by rw [T.cur_range true j]; exact Or.inr hmem)
  have hBe : ∀ t : unitInterval, T.pathβ.toContinuousMap t ≠ x := by
    intro t ht
    have hmem : x ∈ Set.range (T.pathβ).toContinuousMap := ⟨t, ht⟩
    rw [show (T.pathβ).toContinuousMap = ⇑((⟨T.β, rfl, rfl⟩ : Path T.q T.b).symm) from rfl,
      Path.symm_range] at hmem
    exact hxβ hmem
  have hcat : ∀ t : unitInterval, ((T.pathα).trans (T.pathB j)).toContinuousMap t ≠ x :=
    trans_ne T.pathα (T.pathB j) hAl hB
  have hhalf1 : ∀ t : unitInterval,
      ((T.pathA true).trans ((T.pathα).trans (T.pathB j))).toContinuousMap t ≠ x :=
    trans_ne (T.pathA true) ((T.pathα).trans (T.pathB j)) hA1 hcat
  have hhalf2 : ∀ t : unitInterval,
      ((T.pathA false).trans ((T.pathα).trans (T.pathB j))).toContinuousMap t ≠ x :=
    trans_ne (T.pathA false) ((T.pathα).trans (T.pathB j)) hA2 hcat
  have hz1 : ∀ t : unitInterval,
      (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap t
        ≠ x :=
    trans_ne ((T.pathA true).trans ((T.pathα).trans (T.pathB j))) (T.pathβ) hhalf1 hBe
  have hz2 : ∀ t : unitInterval,
      (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap t
        ≠ x :=
    trans_ne ((T.pathA false).trans ((T.pathα).trans (T.pathB j))) (T.pathβ) hhalf2 hBe
  have d1 : incrSub (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x hz1
      = incrSub (T.pathA true).toContinuousMap x hA1
        + incrSub T.pathα.toContinuousMap x hAl
        + incrSub (T.pathB j).toContinuousMap x hB
        + incrSub T.pathβ.toContinuousMap x hBe := by
    rw [incr_trans ((T.pathA true).trans ((T.pathα).trans (T.pathB j))) (T.pathβ) hz1 hhalf1 hBe,
      incr_trans (T.pathA true) ((T.pathα).trans (T.pathB j)) hhalf1 hA1 hcat,
      incr_trans T.pathα (T.pathB j) hcat hAl hB]
    ring
  have d2 : incrSub (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x hz2
      = incrSub (T.pathA false).toContinuousMap x hA2
        + incrSub T.pathα.toContinuousMap x hAl
        + incrSub (T.pathB j).toContinuousMap x hB
        + incrSub T.pathβ.toContinuousMap x hBe := by
    rw [incr_trans ((T.pathA false).trans ((T.pathα).trans (T.pathB j))) (T.pathβ) hz2 hhalf2 hBe,
      incr_trans (T.pathA false) ((T.pathα).trans (T.pathB j)) hhalf2 hA2 hcat,
      incr_trans T.pathα (T.pathB j) hcat hAl hB]
    ring
  have hdiff : incrSub (T.pathA true).toContinuousMap x hA1
      - incrSub (T.pathA false).toContinuousMap x hA2
      = ((windNumber (discCurve T.f).γ (discCurve T.f).cont x : ℤ) : ℂ)
        * (2 * (Real.pi : ℂ) * Complex.I) := by
    have e1 : incrSub (T.pathA true).toContinuousMap x hA1
        = incr (c := subC (discArc T.f T.θq T.θp) x)
            (discArc_sub_ne T.f hxcirc T.θq T.θp) := rfl
    have e2 : incrSub (T.pathA false).toContinuousMap x hA2
        = incr (c := subC (discArc T.f T.θq (T.θp - 2 * Real.pi)) x)
            (discArc_sub_ne T.f hxcirc T.θq (T.θp - 2 * Real.pi)) := rfl
    rw [e1, e2, incr_discArc_diff T.f hxcirc T.hθp_lt T.hθp_ub, incr_seg_windNumber T.f hxcirc]
  have hcl1 : subC (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x
        (0 : unitInterval)
      = subC (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x 1 := by
    have hL : (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap
        (0 : unitInterval) = T.q := by
      change (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)) (0 : unitInterval)
        = T.q
      rw [trans_zero, trans_zero, Path.source]
    have hR : (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap
        (1 : unitInterval) = T.q := by
      change (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)) (1 : unitInterval)
        = T.q
      rw [trans_one, Path.target]
    rw [subC_apply, subC_apply, hL, hR]
  have hcl2 : subC (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x
        (0 : unitInterval)
      = subC (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x 1 := by
    have hL : (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap
        (0 : unitInterval) = T.q := by
      change (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)) (0 : unitInterval)
        = T.q
      rw [trans_zero, trans_zero, Path.source]
    have hR : (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap
        (1 : unitInterval) = T.q := by
      change (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)) (1 : unitInterval)
        = T.q
      rw [trans_one, Path.target]
    rw [subC_apply, subC_apply, hL, hR]
  have key1 : ((loopIndex (subC (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans
          (T.pathβ)).toContinuousMap x) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      = incrSub (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x hz1 := by
    rw [incrSub]
    exact (incr_eq_loopIndex (c := subC (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans
      (T.pathβ)).toContinuousMap x) _ hcl1).symm
  have key2 : ((loopIndex (subC (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans
          (T.pathβ)).toContinuousMap x) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      = incrSub (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x hz2 := by
    rw [incrSub]
    exact (incr_eq_loopIndex (c := subC (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans
      (T.pathβ)).toContinuousMap x) _ hcl2).symm
  have hmain : (((loopIndex (subC (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans
          (T.pathβ)).toContinuousMap x)
        - loopIndex (subC (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans
          (T.pathβ)).toContinuousMap x)) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      = ((windNumber (discCurve T.f).γ (discCurve T.f).cont x : ℤ) : ℂ)
        * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [Int.cast_sub, sub_mul, key1, key2, d1, d2]
    have h := hdiff
    ring_nf at h ⊢
    exact h
  exact Int.cast_inj.mp (mul_right_cancel₀ two_pi_I_ne_zero hmain)


/-- **The difference of the increments of the two boundary arcs of a disc map**, in the form in
which the second arc is named by a parameter `c` with `c = b - 2π`. -/
theorem incr_discArc_diff' (F : C(Disc, ℂ)) {x : ℂ} (hx : ∀ ψ : ℝ, F (circlePoint ψ) ≠ x)
    {a b c : ℝ} (hab : a < b) (hub : b < a + 2 * Real.pi) (hbc : c = b - 2 * Real.pi) :
    incr (c := subC (discArc F a b) x) (discArc_sub_ne F hx a b)
        - incr (c := subC (discArc F a c) x) (discArc_sub_ne F hx a c)
      = incr (c := seg (angPath F x) (continuous_angPath F x) 0 (2 * Real.pi))
          (seg_angPath_ne F hx 0 (2 * Real.pi)) := by
  rw [hbc]
  exact incr_discArc_diff F hx hab hub


/-- **A point outside the image of a disc map is wound zero times round by its boundary curve.** -/
theorem windNumber_discCurve_eq_zero (h : PlaneHypothesis) {F : C(Disc, ℂ)}
    (hF : Function.Injective F) {z : ℂ} (hz : z ∉ Set.range F) :
    windNumber (discCurve F).γ (discCurve F).cont z = 0 := by
  obtain ⟨S⟩ := h (discCurve F) (discCurve_isSimple hF)
  obtain ⟨-, hopen⟩ := discCurveSpans hF S
  have hztrace : z ∉ (discCurve F).trace := by
    rintro ⟨θ, hθ⟩
    exact hz ⟨circlePoint θ, hθ⟩
  have hzV : z ∉ S.V := by
    rw [← hopen]
    rintro ⟨w, -, rfl⟩
    exact hz ⟨w, rfl⟩
  have hzU : z ∈ S.U := by
    have hmem : z ∈ S.U ∪ S.V := by rw [S.union_eq]; exact hztrace
    rcases hmem with h | h
    · exact h
    · exact absurd h hzV
  exact windNumber_eq_zero_of_mem_U S.toPlaneSeparation hzU

/-- **The winding number of the boundary curve of a disc about an interior point is odd.** -/
theorem odd_windNumber_discCurve_center (h : PlaneHypothesis) {F : C(Disc, ℂ)}
    (hF : Function.Injective F) (z : Disc) (hz : ‖(z : ℂ)‖ < 1) :
    Odd (windNumber (discCurve F).γ (discCurve F).cont (F z)) := by
  obtain ⟨S⟩ := h (discCurve F) (discCurve_isSimple hF)
  obtain ⟨-, hopen⟩ := discCurveSpans hF S
  have hzV : F z ∈ S.V := by
    rw [← hopen]
    exact ⟨z, hz, rfl⟩
  exact Work.SphereJordan.odd_windNumber_of_mem_V S hzV

namespace ThetaSetup

variable {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂)

/-- **The difference of the winding numbers of the two four-arc curves differing in the `D₁`-arc.**
For a point `x` off both curves and off the boundary curve of `D₁`, the winding numbers of
`cur true j` and `cur false j` about `x` differ by the winding number of `∂D₁` about `x`. -/
theorem windNumber_cur_arcA_diff {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂) (j : Bool) {x : ℂ}
    (hx1 : x ∉ (T.cur true j).trace) (hx2 : x ∉ (T.cur false j).trace)
    (hxcirc : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ x) :
    windNumber (T.cur true j).γ (T.cur true j).cont x
      - windNumber (T.cur false j).γ (T.cur false j).cont x
      = windNumber (discCurve T.f).γ (discCurve T.f).cont x := by
  rw [cur_windNumber_eq T true j hx1, cur_windNumber_eq T false j hx2]
  rw [show T.loopCf true j
      = (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap
      from rfl,
    show T.loopCf false j
      = (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap
      from rfl]
  have hA1 : ∀ t : unitInterval, (T.pathA true).toContinuousMap t ≠ x := by
    intro t ht
    refine hx1 ?_
    rw [T.cur_range true j]
    exact Or.inl (Or.inl (Or.inl ⟨t, ht⟩))
  have hA2 : ∀ t : unitInterval, (T.pathA false).toContinuousMap t ≠ x := by
    intro t ht
    refine hx2 ?_
    rw [T.cur_range false j]
    exact Or.inl (Or.inl (Or.inl ⟨t, ht⟩))
  have hAl : ∀ t : unitInterval, T.pathα.toContinuousMap t ≠ x := by
    intro t ht
    refine hx1 ?_
    rw [T.cur_range true j]
    exact Or.inl (Or.inl (Or.inr ⟨t, ht⟩))
  have hB : ∀ t : unitInterval, (T.pathB j).toContinuousMap t ≠ x := by
    intro t ht
    refine hx1 ?_
    rw [T.cur_range true j]
    exact Or.inl (Or.inr ⟨t, ht⟩)
  have hxβ : x ∉ Set.range T.β := by
    intro hmem
    exact hx1 (by rw [T.cur_range true j]; exact Or.inr hmem)
  have hBe : ∀ t : unitInterval, T.pathβ.toContinuousMap t ≠ x := by
    intro t ht
    have hmem : x ∈ Set.range (T.pathβ).toContinuousMap := ⟨t, ht⟩
    rw [show (T.pathβ).toContinuousMap = ⇑((⟨T.β, rfl, rfl⟩ : Path T.q T.b).symm) from rfl,
      Path.symm_range] at hmem
    exact hxβ hmem
  have hcat : ∀ t : unitInterval, ((T.pathα).trans (T.pathB j)).toContinuousMap t ≠ x :=
    trans_ne T.pathα (T.pathB j) hAl hB
  have hhalf1 : ∀ t : unitInterval,
      ((T.pathA true).trans ((T.pathα).trans (T.pathB j))).toContinuousMap t ≠ x :=
    trans_ne (T.pathA true) ((T.pathα).trans (T.pathB j)) hA1 hcat
  have hhalf2 : ∀ t : unitInterval,
      ((T.pathA false).trans ((T.pathα).trans (T.pathB j))).toContinuousMap t ≠ x :=
    trans_ne (T.pathA false) ((T.pathα).trans (T.pathB j)) hA2 hcat
  have hz1 : ∀ t : unitInterval,
      (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap t
        ≠ x :=
    trans_ne ((T.pathA true).trans ((T.pathα).trans (T.pathB j))) (T.pathβ) hhalf1 hBe
  have hz2 : ∀ t : unitInterval,
      (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap t
        ≠ x :=
    trans_ne ((T.pathA false).trans ((T.pathα).trans (T.pathB j))) (T.pathβ) hhalf2 hBe
  have d1 : incrSub (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x hz1
      = incrSub (T.pathA true).toContinuousMap x hA1
        + incrSub T.pathα.toContinuousMap x hAl
        + incrSub (T.pathB j).toContinuousMap x hB
        + incrSub T.pathβ.toContinuousMap x hBe := by
    rw [incr_trans ((T.pathA true).trans ((T.pathα).trans (T.pathB j))) (T.pathβ) hz1 hhalf1 hBe,
      incr_trans (T.pathA true) ((T.pathα).trans (T.pathB j)) hhalf1 hA1 hcat,
      incr_trans T.pathα (T.pathB j) hcat hAl hB]
    ring
  have d2 : incrSub (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x hz2
      = incrSub (T.pathA false).toContinuousMap x hA2
        + incrSub T.pathα.toContinuousMap x hAl
        + incrSub (T.pathB j).toContinuousMap x hB
        + incrSub T.pathβ.toContinuousMap x hBe := by
    rw [incr_trans ((T.pathA false).trans ((T.pathα).trans (T.pathB j))) (T.pathβ) hz2 hhalf2 hBe,
      incr_trans (T.pathA false) ((T.pathα).trans (T.pathB j)) hhalf2 hA2 hcat,
      incr_trans T.pathα (T.pathB j) hcat hAl hB]
    ring
  have hdiff : incrSub (T.pathA true).toContinuousMap x hA1
      - incrSub (T.pathA false).toContinuousMap x hA2
      = ((windNumber (discCurve T.f).γ (discCurve T.f).cont x : ℤ) : ℂ)
        * (2 * (Real.pi : ℂ) * Complex.I) := by
    have e1 : incrSub (T.pathA true).toContinuousMap x hA1
        = incr (c := subC (discArc T.f T.θq T.θp) x)
            (discArc_sub_ne T.f hxcirc T.θq T.θp) := rfl
    have e2 : incrSub (T.pathA false).toContinuousMap x hA2
        = incr (c := subC (discArc T.f T.θq (T.θp - 2 * Real.pi)) x)
            (discArc_sub_ne T.f hxcirc T.θq (T.θp - 2 * Real.pi)) := rfl
    rw [e1, e2, incr_discArc_diff T.f hxcirc T.hθp_lt T.hθp_ub, incr_seg_windNumber T.f hxcirc]
  have hcl1 : subC (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x
        (0 : unitInterval)
      = subC (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x 1 := by
    have hL : (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap
        (0 : unitInterval) = T.q := by
      change (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)) (0 : unitInterval)
        = T.q
      rw [trans_zero, trans_zero, Path.source]
    have hR : (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap
        (1 : unitInterval) = T.q := by
      change (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)) (1 : unitInterval)
        = T.q
      rw [trans_one, Path.target]
    rw [subC_apply, subC_apply, hL, hR]
  have hcl2 : subC (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x
        (0 : unitInterval)
      = subC (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x 1 := by
    have hL : (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap
        (0 : unitInterval) = T.q := by
      change (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)) (0 : unitInterval)
        = T.q
      rw [trans_zero, trans_zero, Path.source]
    have hR : (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap
        (1 : unitInterval) = T.q := by
      change (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)) (1 : unitInterval)
        = T.q
      rw [trans_one, Path.target]
    rw [subC_apply, subC_apply, hL, hR]
  have key1 : ((loopIndex (subC (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans
          (T.pathβ)).toContinuousMap x) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      = incrSub (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x hz1 := by
    rw [incrSub]
    exact (incr_eq_loopIndex (c := subC (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans
      (T.pathβ)).toContinuousMap x) _ hcl1).symm
  have key2 : ((loopIndex (subC (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans
          (T.pathβ)).toContinuousMap x) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      = incrSub (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans (T.pathβ)).toContinuousMap x hz2 := by
    rw [incrSub]
    exact (incr_eq_loopIndex (c := subC (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans
      (T.pathβ)).toContinuousMap x) _ hcl2).symm
  have hmain : (((loopIndex (subC (((T.pathA true).trans ((T.pathα).trans (T.pathB j))).trans
          (T.pathβ)).toContinuousMap x)
        - loopIndex (subC (((T.pathA false).trans ((T.pathα).trans (T.pathB j))).trans
          (T.pathβ)).toContinuousMap x)) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      = ((windNumber (discCurve T.f).γ (discCurve T.f).cont x : ℤ) : ℂ)
        * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [Int.cast_sub, sub_mul, key1, key2, d1, d2]
    have h := hdiff
    ring_nf at h ⊢
    exact h
  exact Int.cast_inj.mp (mul_right_cancel₀ two_pi_I_ne_zero hmain)

/-- **The difference of the winding numbers of the two four-arc curves differing in the `D₂`-arc.**
For a point `x` off both curves and off the boundary curve of `D₂`, the winding numbers of
`cur i true` and `cur i false` about `x` differ by the winding number of `∂D₂` about `x`. -/
theorem windNumber_cur_arcB_diff {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂) (i : Bool) {x : ℂ}
    (hx1 : x ∉ (T.cur i true).trace) (hx2 : x ∉ (T.cur i false).trace)
    (hxcirc : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ x) :
    windNumber (T.cur i true).γ (T.cur i true).cont x
      - windNumber (T.cur i false).γ (T.cur i false).cont x
      = windNumber (discCurve T.g).γ (discCurve T.g).cont x := by
  rw [cur_windNumber_eq T i true hx1, cur_windNumber_eq T i false hx2]
  rw [show T.loopCf i true
      = (((T.pathA i).trans ((T.pathα).trans (T.pathB true))).trans (T.pathβ)).toContinuousMap
      from rfl,
    show T.loopCf i false
      = (((T.pathA i).trans ((T.pathα).trans (T.pathB false))).trans (T.pathβ)).toContinuousMap
      from rfl]
  have hAi : ∀ t : unitInterval, (T.pathA i).toContinuousMap t ≠ x := by
    intro t ht
    refine hx1 ?_
    rw [T.cur_range i true]
    exact Or.inl (Or.inl (Or.inl ⟨t, ht⟩))
  have hB1 : ∀ t : unitInterval, (T.pathB true).toContinuousMap t ≠ x := by
    intro t ht
    refine hx1 ?_
    rw [T.cur_range i true]
    exact Or.inl (Or.inr ⟨t, ht⟩)
  have hB2 : ∀ t : unitInterval, (T.pathB false).toContinuousMap t ≠ x := by
    intro t ht
    refine hx2 ?_
    rw [T.cur_range i false]
    exact Or.inl (Or.inr ⟨t, ht⟩)
  have hAl : ∀ t : unitInterval, T.pathα.toContinuousMap t ≠ x := by
    intro t ht
    refine hx1 ?_
    rw [T.cur_range i true]
    exact Or.inl (Or.inl (Or.inr ⟨t, ht⟩))
  have hxβ : x ∉ Set.range T.β := by
    intro hmem
    exact hx1 (by rw [T.cur_range i true]; exact Or.inr hmem)
  have hBe : ∀ t : unitInterval, T.pathβ.toContinuousMap t ≠ x := by
    intro t ht
    have hmem : x ∈ Set.range (T.pathβ).toContinuousMap := ⟨t, ht⟩
    rw [show (T.pathβ).toContinuousMap = ⇑((⟨T.β, rfl, rfl⟩ : Path T.q T.b).symm) from rfl,
      Path.symm_range] at hmem
    exact hxβ hmem
  have hcat1 : ∀ t : unitInterval, ((T.pathα).trans (T.pathB true)).toContinuousMap t ≠ x :=
    trans_ne T.pathα (T.pathB true) hAl hB1
  have hcat2 : ∀ t : unitInterval, ((T.pathα).trans (T.pathB false)).toContinuousMap t ≠ x :=
    trans_ne T.pathα (T.pathB false) hAl hB2
  have hhalf1 : ∀ t : unitInterval,
      ((T.pathA i).trans ((T.pathα).trans (T.pathB true))).toContinuousMap t ≠ x :=
    trans_ne (T.pathA i) ((T.pathα).trans (T.pathB true)) hAi hcat1
  have hhalf2 : ∀ t : unitInterval,
      ((T.pathA i).trans ((T.pathα).trans (T.pathB false))).toContinuousMap t ≠ x :=
    trans_ne (T.pathA i) ((T.pathα).trans (T.pathB false)) hAi hcat2
  have hz1 : ∀ t : unitInterval,
      (((T.pathA i).trans ((T.pathα).trans (T.pathB true))).trans (T.pathβ)).toContinuousMap t
        ≠ x :=
    trans_ne ((T.pathA i).trans ((T.pathα).trans (T.pathB true))) (T.pathβ) hhalf1 hBe
  have hz2 : ∀ t : unitInterval,
      (((T.pathA i).trans ((T.pathα).trans (T.pathB false))).trans (T.pathβ)).toContinuousMap t
        ≠ x :=
    trans_ne ((T.pathA i).trans ((T.pathα).trans (T.pathB false))) (T.pathβ) hhalf2 hBe
  have d1 : incrSub (((T.pathA i).trans ((T.pathα).trans (T.pathB true))).trans (T.pathβ)).toContinuousMap x hz1
      = incrSub (T.pathA i).toContinuousMap x hAi
        + incrSub T.pathα.toContinuousMap x hAl
        + incrSub (T.pathB true).toContinuousMap x hB1
        + incrSub T.pathβ.toContinuousMap x hBe := by
    rw [incr_trans ((T.pathA i).trans ((T.pathα).trans (T.pathB true))) (T.pathβ) hz1 hhalf1 hBe,
      incr_trans (T.pathA i) ((T.pathα).trans (T.pathB true)) hhalf1 hAi hcat1,
      incr_trans T.pathα (T.pathB true) hcat1 hAl hB1]
    ring
  have d2 : incrSub (((T.pathA i).trans ((T.pathα).trans (T.pathB false))).trans (T.pathβ)).toContinuousMap x hz2
      = incrSub (T.pathA i).toContinuousMap x hAi
        + incrSub T.pathα.toContinuousMap x hAl
        + incrSub (T.pathB false).toContinuousMap x hB2
        + incrSub T.pathβ.toContinuousMap x hBe := by
    rw [incr_trans ((T.pathA i).trans ((T.pathα).trans (T.pathB false))) (T.pathβ) hz2 hhalf2 hBe,
      incr_trans (T.pathA i) ((T.pathα).trans (T.pathB false)) hhalf2 hAi hcat2,
      incr_trans T.pathα (T.pathB false) hcat2 hAl hB2]
    ring
  have hdiff : incrSub (T.pathB true).toContinuousMap x hB1
      - incrSub (T.pathB false).toContinuousMap x hB2
      = ((windNumber (discCurve T.g).γ (discCurve T.g).cont x : ℤ) : ℂ)
        * (2 * (Real.pi : ℂ) * Complex.I) := by
    have e1 : incrSub (T.pathB true).toContinuousMap x hB1
        = incr (c := subC (discArc T.g T.φa (T.φb + 2 * Real.pi)) x)
            (discArc_sub_ne T.g hxcirc T.φa (T.φb + 2 * Real.pi)) := rfl
    have e2 : incrSub (T.pathB false).toContinuousMap x hB2
        = incr (c := subC (discArc T.g T.φa T.φb) x)
            (discArc_sub_ne T.g hxcirc T.φa T.φb) := rfl
    rw [e1, e2,
      incr_discArc_diff' T.g hxcirc (by linarith [T.hφa_ub]) (by linarith [T.hφa_lt])
        (by ring : T.φb = (T.φb + 2 * Real.pi) - 2 * Real.pi),
      incr_seg_windNumber T.g hxcirc]
  have hcl1 : subC (((T.pathA i).trans ((T.pathα).trans (T.pathB true))).trans (T.pathβ)).toContinuousMap x
        (0 : unitInterval)
      = subC (((T.pathA i).trans ((T.pathα).trans (T.pathB true))).trans (T.pathβ)).toContinuousMap x 1 := by
    have hL : (((T.pathA i).trans ((T.pathα).trans (T.pathB true))).trans (T.pathβ)).toContinuousMap
        (0 : unitInterval) = T.q := by
      change (((T.pathA i).trans ((T.pathα).trans (T.pathB true))).trans (T.pathβ)) (0 : unitInterval)
        = T.q
      rw [trans_zero, trans_zero, Path.source]
    have hR : (((T.pathA i).trans ((T.pathα).trans (T.pathB true))).trans (T.pathβ)).toContinuousMap
        (1 : unitInterval) = T.q := by
      change (((T.pathA i).trans ((T.pathα).trans (T.pathB true))).trans (T.pathβ)) (1 : unitInterval)
        = T.q
      rw [trans_one, Path.target]
    rw [subC_apply, subC_apply, hL, hR]
  have hcl2 : subC (((T.pathA i).trans ((T.pathα).trans (T.pathB false))).trans (T.pathβ)).toContinuousMap x
        (0 : unitInterval)
      = subC (((T.pathA i).trans ((T.pathα).trans (T.pathB false))).trans (T.pathβ)).toContinuousMap x 1 := by
    have hL : (((T.pathA i).trans ((T.pathα).trans (T.pathB false))).trans (T.pathβ)).toContinuousMap
        (0 : unitInterval) = T.q := by
      change (((T.pathA i).trans ((T.pathα).trans (T.pathB false))).trans (T.pathβ)) (0 : unitInterval)
        = T.q
      rw [trans_zero, trans_zero, Path.source]
    have hR : (((T.pathA i).trans ((T.pathα).trans (T.pathB false))).trans (T.pathβ)).toContinuousMap
        (1 : unitInterval) = T.q := by
      change (((T.pathA i).trans ((T.pathα).trans (T.pathB false))).trans (T.pathβ)) (1 : unitInterval)
        = T.q
      rw [trans_one, Path.target]
    rw [subC_apply, subC_apply, hL, hR]
  have key1 : ((loopIndex (subC (((T.pathA i).trans ((T.pathα).trans (T.pathB true))).trans
          (T.pathβ)).toContinuousMap x) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      = incrSub (((T.pathA i).trans ((T.pathα).trans (T.pathB true))).trans (T.pathβ)).toContinuousMap x hz1 := by
    rw [incrSub]
    exact (incr_eq_loopIndex (c := subC (((T.pathA i).trans ((T.pathα).trans (T.pathB true))).trans
      (T.pathβ)).toContinuousMap x) _ hcl1).symm
  have key2 : ((loopIndex (subC (((T.pathA i).trans ((T.pathα).trans (T.pathB false))).trans
          (T.pathβ)).toContinuousMap x) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      = incrSub (((T.pathA i).trans ((T.pathα).trans (T.pathB false))).trans (T.pathβ)).toContinuousMap x hz2 := by
    rw [incrSub]
    exact (incr_eq_loopIndex (c := subC (((T.pathA i).trans ((T.pathα).trans (T.pathB false))).trans
      (T.pathβ)).toContinuousMap x) _ hcl2).symm
  have hmain : (((loopIndex (subC (((T.pathA i).trans ((T.pathα).trans (T.pathB true))).trans
          (T.pathβ)).toContinuousMap x)
        - loopIndex (subC (((T.pathA i).trans ((T.pathα).trans (T.pathB false))).trans
          (T.pathβ)).toContinuousMap x)) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      = ((windNumber (discCurve T.g).γ (discCurve T.g).cont x : ℤ) : ℂ)
        * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [Int.cast_sub, sub_mul, key1, key2, d1, d2]
    have h := hdiff
    ring_nf at h ⊢
    exact h
  exact Int.cast_inj.mp (mul_right_cancel₀ two_pi_I_ne_zero hmain)

/-! ## The structure of the four-arc loop along its four pieces

The loop `loopC i j` of the four arcs is the concatenation `arcA i · α · arcB j · β` in the
parametrisation of `Path.trans`, so its restriction to the successive quarters `[0,1/4]`, `[1/4,3/8]`,
`[3/8,1/2]`, `[1/2,1]` (in `Path.trans`-normalised form `[0,1/2]`, `[1/2,3/4]`, `[3/4,7/8]`, `[7/8,1]`)
is the corresponding arc.  These are the pointwise inputs of the comparison of the winding numbers
of `cur i j` and `cur i' j'`. -/

/-- **The first quarter of the loop is the boundary arc `arcA i`.** -/
theorem loopC_quarter (i j : Bool) {t : Set.Icc (0:ℝ) 1} (ht : (t:ℝ) ≤ 1/4) :
    T.loopC i j t = T.arcA i ⟨4*(t:ℝ), by constructor <;> linarith [t.2.1, t.2.2]⟩ := by
  rw [loopC, loopP, Path.trans_apply]
  rw [dif_pos (show (t:ℝ) ≤ 1/2 by linarith [t.2.1])]
  rw [halfP, Path.trans_apply]
  rw [dif_pos (show 2*(t:ℝ) ≤ 1/2 by linarith)]
  change T.arcA i (⟨2 * (2 * (t:ℝ)), _⟩ : Set.Icc (0:ℝ) 1)
    = T.arcA i ⟨4*(t:ℝ), by constructor <;> linarith [t.2.1, t.2.2]⟩
  congr 1
  apply Subtype.ext
  ring

/-- **The piece of the loop between the first quarter and three eighths is the joining arc
`α`.** -/
theorem loopC_alpha (i j : Bool) {t : Set.Icc (0:ℝ) 1} (h1 : 1/4 < (t:ℝ))
    (h2 : (t:ℝ) ≤ 3/8) :
    T.loopC i j t = T.α ⟨8*(t:ℝ) - 2, by constructor <;> linarith [t.2.1, t.2.2]⟩ := by
  rw [loopC, loopP, Path.trans_apply, dif_pos (by linarith)]
  rw [halfP, Path.trans_apply, dif_neg (by simp only [Subtype.coe_mk]; linarith)]
  rw [Path.trans_apply, dif_pos (by simp only [Subtype.coe_mk]; linarith)]
  change T.α (⟨2 * (2 * (2 * (t:ℝ)) - 1), _⟩ : Set.Icc (0:ℝ) 1)
    = T.α ⟨8*(t:ℝ) - 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
  congr 1
  apply Subtype.ext
  ring

/-- **The piece of the loop between three eighths and one half is the boundary arc `arcB j`.** -/
theorem loopC_arcB (i j : Bool) {t : Set.Icc (0:ℝ) 1} (h1 : 3/8 ≤ (t:ℝ)) (h2 : (t:ℝ) ≤ 1/2) :
    T.loopC i j t = T.arcB j ⟨8*(t:ℝ) - 3, by constructor <;> linarith [t.2.1, t.2.2]⟩ := by
  by_cases hlt : (3/8 : ℝ) < (t:ℝ)
  · rw [loopC, loopP, Path.trans_apply, dif_pos (by linarith)]
    rw [halfP, Path.trans_apply, dif_neg (by simp only [Subtype.coe_mk]; linarith)]
    rw [Path.trans_apply, dif_neg (by simp only [Subtype.coe_mk]; linarith)]
    change T.arcB j (⟨2 * (2 * (2 * (t:ℝ)) - 1) - 1, _⟩ : Set.Icc (0:ℝ) 1)
      = T.arcB j ⟨8*(t:ℝ) - 3, by constructor <;> linarith [t.2.1, t.2.2]⟩
    congr 1
    apply Subtype.ext
    ring
  · have ht : (t:ℝ) = 3/8 := le_antisymm (le_of_not_gt hlt) h1
    rw [loopC, loopP, Path.trans_apply, dif_pos (by linarith)]
    rw [halfP, Path.trans_apply, dif_neg (by simp only [Subtype.coe_mk]; linarith)]
    rw [Path.trans_apply, dif_pos (by simp only [Subtype.coe_mk]; linarith)]
    rw [show (⟨2 * (2 * (2 * (t:ℝ)) - 1),
          by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0:ℝ) 1) = ⟨1, by norm_num⟩
        from Subtype.ext (by simp only [Subtype.coe_mk]; linarith),
      show (⟨8 * (t:ℝ) - 3, by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0:ℝ) 1)
          = ⟨0, by norm_num⟩
        from Subtype.ext (by simp only [Subtype.coe_mk]; linarith),
      T.arcB_zero j]
    rfl



/-- **The loop is independent of `i` after the first quarter.** -/
theorem loopC_eq_of_quarter_le (j : Bool) {t : Set.Icc (0:ℝ) 1} (ht : 1/4 ≤ (t:ℝ)) :
    T.loopC true j t = T.loopC false j t := by
  by_cases h : (t:ℝ) ≤ 1/4
  · rw [loopC_quarter T true j h, loopC_quarter T false j h]
    rw [show (⟨4*(t:ℝ), by constructor <;> linarith [t.2.1, t.2.2]⟩ : Set.Icc (0:ℝ) 1)
        = ⟨1, by norm_num⟩ from Subtype.ext (by simp only [Subtype.coe_mk]; linarith)]
    rw [T.arcA_one true, T.arcA_one false]
  · by_cases h2 : (t:ℝ) ≤ 3/8
    · rw [loopC_alpha T true j (not_le.mp h) h2, loopC_alpha T false j (not_le.mp h) h2]
    · by_cases h3 : (t:ℝ) ≤ 1/2
      · rw [loopC_arcB (t := t) T true j (le_of_lt (not_le.mp h2)) h3,
          loopC_arcB (t := t) T false j (le_of_lt (not_le.mp h2)) h3]
      · rw [loopC, loopP, Path.trans_apply, dif_neg h3]
        rw [loopC, loopP, Path.trans_apply, dif_neg h3]

/-- **The loop is independent of `j` up to three eighths.** -/
theorem loopC_eq_of_le_threeEighth (i : Bool) {t : Set.Icc (0:ℝ) 1} (ht : (t:ℝ) ≤ 3/8) :
    T.loopC i true t = T.loopC i false t := by
  by_cases h : (t:ℝ) ≤ 1/4
  · rw [loopC_quarter T i true h, loopC_quarter T i false h]
  · rw [loopC_alpha T i true (not_le.mp h) ht, loopC_alpha T i false (not_le.mp h) ht]



/-- A point of the boundary circle is not an interior point. -/
theorem circlePoint_ne_of_norm_lt {z : Disc} (hz : ‖(z : ℂ)‖ < 1) (τ : ℝ) :
    T.f (circlePoint τ) ≠ T.f z := by
  intro hcon
  have h1 : ((circlePoint τ : Disc) : ℂ) = (z : ℂ) := congrArg (fun w : Disc => (w : ℂ)) (T.hf hcon)
  have h2 : ‖((circlePoint τ : Disc) : ℂ)‖ = ‖(z : ℂ)‖ := congrArg (fun w : ℂ => ‖w‖) h1
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I] at h2
  linarith

theorem circlePoint_ne_of_norm_lt_g {z : Disc} (hz : ‖(z : ℂ)‖ < 1) (τ : ℝ) :
    T.g (circlePoint τ) ≠ T.g z := by
  intro hcon
  have h1 : ((circlePoint τ : Disc) : ℂ) = (z : ℂ) := congrArg (fun w : Disc => (w : ℂ)) (T.hg hcon)
  have h2 : ‖((circlePoint τ : Disc) : ℂ)‖ = ‖(z : ℂ)‖ := congrArg (fun w : ℂ => ‖w‖) h1
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I] at h2
  linarith



/-- The interior points of `D₁` avoid the trace of every four-arc curve. -/
theorem f_notMem_cur_trace (z : Disc) (hz : ‖(z : ℂ)‖ < 1) (i j : Bool) :
    T.f z ∉ (T.cur i j).trace := by
  have hfD₁ : T.f z ∈ D₁ := by
    have h : T.f z ∈ Set.range T.f := ⟨z, rfl⟩
    rwa [T.hfr] at h
  have hcirc : ∀ τ : ℝ, T.f (circlePoint τ) ≠ T.f z := circlePoint_ne_of_norm_lt T hz
  rw [T.cur_range i j]
  intro hmem
  simp only [Set.mem_union] at hmem
  rcases hmem with ((h | h) | h) | h
  · obtain ⟨t, ht⟩ := h
    cases i
    · refine hcirc (T.θq + (t:ℝ) * ((T.θp - 2 * Real.pi) - T.θq)) ?_
      rw [← ht, show T.arcA false = discArc T.f T.θq (T.θp - 2 * Real.pi) from rfl, discArc_apply]
    · refine hcirc (T.θq + (t:ℝ) * (T.θp - T.θq)) ?_
      rw [← ht, show T.arcA true = discArc T.f T.θq T.θp from rfl, discArc_apply]
  · obtain ⟨t, ht⟩ := h
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have ht0 : t = (⟨0, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h0.symm
      refine hcirc T.θp ?_
      rw [← ht, ht0]
      exact T.hθp
    rcases lt_or_eq_of_le t.2.2 with h1 | h1
    · exact T.hαint t ⟨h0, h1⟩ (by rw [ht]; exact Or.inl hfD₁)
    · have ht1 : t = (⟨1, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h1
      have ha : T.a ∈ D₂ := T.hα₁
      exact Set.disjoint_left.mp T.hdisj hfD₁ (by rw [← ht, ht1]; exact ha)
  · obtain ⟨t, ht⟩ := h
    have h1 : T.arcB j t ∈ D₂ := T.range_arcB_subset j ⟨t, rfl⟩
    exact Set.disjoint_left.mp T.hdisj hfD₁ (by rw [← ht]; exact h1)
  · obtain ⟨t, ht⟩ := h
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have ht0 : t = (⟨0, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h0.symm
      refine hcirc T.θq ?_
      rw [← ht, ht0]
      exact T.hθq
    rcases lt_or_eq_of_le t.2.2 with h1 | h1
    · exact T.hβint t ⟨h0, h1⟩ (by rw [ht]; exact Or.inl hfD₁)
    · have ht1 : t = (⟨1, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h1
      have hb : T.b ∈ D₂ := T.hβ₁
      exact Set.disjoint_left.mp T.hdisj hfD₁ (by rw [← ht, ht1]; exact hb)

/-- The interior points of `D₂` avoid the trace of every four-arc curve. -/
theorem g_notMem_cur_trace (z : Disc) (hz : ‖(z : ℂ)‖ < 1) (i j : Bool) :
    T.g z ∉ (T.cur i j).trace := by
  have hgD₂ : T.g z ∈ D₂ := by
    have h : T.g z ∈ Set.range T.g := ⟨z, rfl⟩
    rwa [T.hgr] at h
  have hcirc : ∀ τ : ℝ, T.g (circlePoint τ) ≠ T.g z := circlePoint_ne_of_norm_lt_g T hz
  rw [T.cur_range i j]
  intro hmem
  simp only [Set.mem_union] at hmem
  rcases hmem with ((h | h) | h) | h
  · obtain ⟨t, ht⟩ := h
    have h1 : T.arcA i t ∈ D₁ := T.range_arcA_subset i ⟨t, rfl⟩
    exact Set.disjoint_left.mp T.hdisj (by rw [← ht]; exact h1) hgD₂
  · obtain ⟨t, ht⟩ := h
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have ht0 : t = (⟨0, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h0.symm
      have hp : T.p ∈ D₁ := by
        have h : T.f (circlePoint T.θp) ∈ Set.range T.f := ⟨circlePoint T.θp, rfl⟩
        rw [T.hθp] at h
        rwa [T.hfr] at h
      exact Set.disjoint_left.mp T.hdisj (by rw [← ht, ht0]; exact hp) hgD₂
    rcases lt_or_eq_of_le t.2.2 with h1 | h1
    · exact T.hαint t ⟨h0, h1⟩ (by rw [ht]; exact Or.inr hgD₂)
    · have ht1 : t = (⟨1, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h1
      refine hcirc T.φa ?_
      rw [← ht, ht1]
      exact T.hφa
  · obtain ⟨t, ht⟩ := h
    cases j
    · refine hcirc (T.φa + (t:ℝ) * (T.φb - T.φa)) ?_
      rw [← ht, show T.arcB false = discArc T.g T.φa T.φb from rfl, discArc_apply]
    · refine hcirc (T.φa + (t:ℝ) * ((T.φb + 2 * Real.pi) - T.φa)) ?_
      rw [← ht, show T.arcB true = discArc T.g T.φa (T.φb + 2 * Real.pi) from rfl, discArc_apply]
  · obtain ⟨t, ht⟩ := h
    rcases eq_or_lt_of_le t.2.1 with h0 | h0
    · have ht0 : t = (⟨0, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h0.symm
      have hq : T.q ∈ D₁ := by
        have h : T.f (circlePoint T.θq) ∈ Set.range T.f := ⟨circlePoint T.θq, rfl⟩
        rw [T.hθq] at h
        rwa [T.hfr] at h
      exact Set.disjoint_left.mp T.hdisj (by rw [← ht, ht0]; exact hq) hgD₂
    rcases lt_or_eq_of_le t.2.2 with h1 | h1
    · exact T.hβint t ⟨h0, h1⟩ (by rw [ht]; exact Or.inr hgD₂)
    · have ht1 : t = (⟨1, by norm_num⟩ : Set.Icc (0:ℝ) 1) := Subtype.ext h1
      refine hcirc T.φb ?_
      rw [← ht, ht1]
      exact T.hφb

/-- **The centre points of the two discs avoid the trace of every four-arc curve.** -/
theorem center_notMem_cur_trace (z : Disc) (hz : ‖(z : ℂ)‖ < 1) (i j : Bool) :
    T.f z ∉ (T.cur i j).trace ∧ T.g z ∉ (T.cur i j).trace :=
  ⟨f_notMem_cur_trace T z hz i j, g_notMem_cur_trace T z hz i j⟩


/-- **The winding number of `cur i j` about a point outside `D₂` is independent of `j`.** -/
theorem windNumber_cur_indep_j (i j : Bool) {x : ℂ}
    (hx1 : x ∉ (T.cur i true).trace) (hx2 : x ∉ (T.cur i false).trace)
    (hxcirc : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ x)
    (hW : windNumber (discCurve T.g).γ (discCurve T.g).cont x = 0) :
    windNumber (T.cur i j).γ (T.cur i j).cont x
      = windNumber (T.cur i false).γ (T.cur i false).cont x := by
  cases j
  · rfl
  · have hd := windNumber_cur_arcB_diff T i hx1 hx2 hxcirc
    rw [hW] at hd
    linarith

/-- **The winding number of `cur i j` about a point outside `D₁` is independent of `i`.** -/
theorem windNumber_cur_indep_i (i j : Bool) {y : ℂ}
    (hy1 : y ∉ (T.cur true j).trace) (hy2 : y ∉ (T.cur false j).trace)
    (hycirc : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ y)
    (hW : windNumber (discCurve T.f).γ (discCurve T.f).cont y = 0) :
    windNumber (T.cur i j).γ (T.cur i j).cont y
      = windNumber (T.cur true j).γ (T.cur true j).cont y := by
  cases i
  · have hd := windNumber_cur_arcA_diff T j hy1 hy2 hycirc
    rw [hW] at hd
    linarith
  · rfl

/-- **Exactly one of the two curves `cur true j`, `cur false j` winds zero times about a point of
the interior of `D₁`.** -/
theorem exists_zero_index_arcA (h : PlaneHypothesis) (j : Bool) {x : ℂ}
    (hx1 : x ∉ (T.cur true j).trace) (hx2 : x ∉ (T.cur false j).trace)
    (hxcirc : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ x)
    (hW : Odd (windNumber (discCurve T.f).γ (discCurve T.f).cont x)) :
    ∃ i : Bool, windNumber (T.cur i j).γ (T.cur i j).cont x = 0 ∧
      ∀ i' : Bool, windNumber (T.cur i' j).γ (T.cur i' j).cont x = 0 → i' = i := by
  have h1 := windNumber_eq_zero_or_odd h (T.cur true j) (T.cur_isSimple true j) hx1
  have h2 := windNumber_eq_zero_or_odd h (T.cur false j) (T.cur_isSimple false j) hx2
  have hd := windNumber_cur_arcA_diff T j hx1 hx2 hxcirc
  have hne : windNumber (discCurve T.f).γ (discCurve T.f).cont x ≠ 0 := by
    obtain ⟨m, hm⟩ := hW
    rw [hm]
    omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have hzero : windNumber (discCurve T.f).γ (discCurve T.f).cont x = 0 := by
      rw [h1, h2, sub_zero] at hd
      exact hd.symm
    exact absurd hzero hne
  · refine ⟨true, h1, fun i' hi' => ?_⟩
    cases i' with
    | true => rfl
    | false =>
      obtain ⟨m, hm⟩ := h2
      rw [hi'] at hm
      omega
  · refine ⟨false, h2, fun i' hi' => ?_⟩
    cases i' with
    | true =>
      obtain ⟨m, hm⟩ := h1
      rw [hi'] at hm
      omega
    | false => rfl
  · exfalso
    obtain ⟨m, hm⟩ := h1
    obtain ⟨k, hk⟩ := h2
    obtain ⟨l, hl⟩ := hW
    rw [hm, hk, hl] at hd
    omega

/-- **Exactly one of the two curves `cur i true`, `cur i false` winds zero times about a point of
the interior of `D₂`.** -/
theorem exists_zero_index_arcB (h : PlaneHypothesis) (i : Bool) {y : ℂ}
    (hy1 : y ∉ (T.cur i true).trace) (hy2 : y ∉ (T.cur i false).trace)
    (hycirc : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ y)
    (hW : Odd (windNumber (discCurve T.g).γ (discCurve T.g).cont y)) :
    ∃ j : Bool, windNumber (T.cur i j).γ (T.cur i j).cont y = 0 ∧
      ∀ j' : Bool, windNumber (T.cur i j').γ (T.cur i j').cont y = 0 → j' = j := by
  have h1 := windNumber_eq_zero_or_odd h (T.cur i true) (T.cur_isSimple i true) hy1
  have h2 := windNumber_eq_zero_or_odd h (T.cur i false) (T.cur_isSimple i false) hy2
  have hd := windNumber_cur_arcB_diff T i hy1 hy2 hycirc
  have hne : windNumber (discCurve T.g).γ (discCurve T.g).cont y ≠ 0 := by
    obtain ⟨m, hm⟩ := hW
    rw [hm]
    omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · have hzero : windNumber (discCurve T.g).γ (discCurve T.g).cont y = 0 := by
      rw [h1, h2, sub_zero] at hd
      exact hd.symm
    exact absurd hzero hne
  · refine ⟨true, h1, fun j' hj' => ?_⟩
    cases j' with
    | true => rfl
    | false =>
      obtain ⟨m, hm⟩ := h2
      rw [hj'] at hm
      omega
  · refine ⟨false, h2, fun j' hj' => ?_⟩
    cases j' with
    | true =>
      obtain ⟨m, hm⟩ := h1
      rw [hj'] at hm
      omega
    | false => rfl
  · exfalso
    obtain ⟨m, hm⟩ := h1
    obtain ⟨k, hk⟩ := h2
    obtain ⟨l, hl⟩ := hW
    rw [hm, hk, hl] at hd
    omega


/-- **Swapping the first index changes the winding number about a point outside `D₁` by at most
the sign of the winding number of `∂D₁`.**  (Here that number vanishes.) -/
theorem windNumber_cur_swap_i (i j : Bool) {y : ℂ}
    (hy1 : y ∉ (T.cur true j).trace) (hy2 : y ∉ (T.cur false j).trace)
    (hycirc : ∀ ψ : ℝ, T.f (circlePoint ψ) ≠ y)
    (hW : windNumber (discCurve T.f).γ (discCurve T.f).cont y = 0) :
    windNumber (T.cur i j).γ (T.cur i j).cont y
      = windNumber (T.cur (!i) j).γ (T.cur (!i) j).cont y := by
  cases i
  · simp only [Bool.not_false]
    have hd := windNumber_cur_arcA_diff T j hy1 hy2 hycirc
    rw [hW] at hd
    linarith
  · simp only [Bool.not_true]
    have hd := windNumber_cur_arcA_diff T j hy1 hy2 hycirc
    rw [hW] at hd
    linarith

/-- **Swapping the second index changes the winding number about a point outside `D₂` by at most
the sign of the winding number of `∂D₂`.**  (Here that number vanishes.) -/
theorem windNumber_cur_swap_j (i j : Bool) {x : ℂ}
    (hx1 : x ∉ (T.cur i true).trace) (hx2 : x ∉ (T.cur i false).trace)
    (hxcirc : ∀ ψ : ℝ, T.g (circlePoint ψ) ≠ x)
    (hW : windNumber (discCurve T.g).γ (discCurve T.g).cont x = 0) :
    windNumber (T.cur i j).γ (T.cur i j).cont x
      = windNumber (T.cur i (!j)).γ (T.cur i (!j)).cont x := by
  cases j
  · simp only [Bool.not_false]
    have hd := windNumber_cur_arcB_diff T i hx1 hx2 hxcirc
    rw [hW] at hd
    linarith
  · simp only [Bool.not_true]
    have hd := windNumber_cur_arcB_diff T i hx1 hx2 hxcirc
    rw [hW] at hd
    linarith
end ThetaSetup

end

end Work.Smooth.SphereJordan
