import Mathlib
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.capSideLift
import Submission.Work.Drive.capSide_capPiece
import Submission.Work.Drive.omegaChainInterface
import Submission.Work.Drive.cappedPlane

namespace Work.Drive

noncomputable section

set_option maxHeartbeats 800000

/-! # The side half of the core-loop vs rotated-plane disjointness

This module proves `Work.Drive.coreLoopCapDisjoint`, the exact statement of the `sorry` of
`Work.Drive.coreLoop_disjoint_rotCapping_capPart`: a point of the **core loop** of a plane chart
(`Q z` with `‖z‖ = 1`) is never the rotation (by *any* `w`) of a point of the **cap part** of the
chart (`‖z'‖ < 1/2`).  (Note that this module deliberately does *not* import
`coreLoop_disjoint_rotCapping.lean`, so that the latter can import this one and discharge its
`sorry` without a cycle.)

## The route taken

The two pieces of the capping space `CappingSpace` meet only along the glued boundary torus: a point
whose `ConfigPiece` disk coordinate is *strictly* inner, `‖d‖ < 1`, can never be presented by a
`CapPiece` at all (`Work.Drive.mk_inl_ne_mk_inr_of_norm_lt_one`, in `cappedPlane.lean`).  So it
suffices to know that the loop value `Q z` is **strictly** configuration side, i.e. that the chord of
`γ` it encodes has positive length.

* by the strip clause of `IsPlaneChart` (applied at `‖z‖ = 1`) the loop value is
  `stripChart γ hγne 0 (mk2 (arg z + s) (arg z - s))` with `s = √(π²(‖z‖ - 1/2)/2) = π/2`, i.e. the
  **maximal chord** of `γ` at the parameters `arg z ± π/2`;
* `stripData_snd_norm_lt_one_of_chord_ne` shows that the disk coordinate `d = midpoint/R` of a chord
  has `‖d‖ < 1` as soon as the chord is non-degenerate: `R = √(‖midpoint‖² + length²)` and
  `length > 0` gives `‖midpoint‖ < R`;
* the two parameters of a maximal chord differ by `π`, which is not a multiple of `2π`, so the two
  circle points are distinct (`Circle.exp_eq_exp`), and `Function.Injective γ` — the hypothesis the
  review gate found to be genuinely necessary — makes the chord non-degenerate;
* the cap clause of `IsPlaneChart` presents `Q z'` as the class of a `CapPiece` `c`, and
  `Work.Drive.rotCapping_mk` shows that `rotCapping w (mk (inr c))` is the class of `rotCap w c`
  (the rotation adds to the `S¹`-coordinate of the cap piece and leaves its disk coordinate alone) —
  again a `CapPiece`.

No `IsCapVec`/projective-lift computation is needed: the *interior vs boundary* dichotomy of the two
pieces of the capping space already separates the sides, and it also settles the boundary case
`‖d‖ = 1` of the cap piece (there the point lies on the gluing torus and carries **no** configuration
presentation with `‖d‖ < 1` either, by `mk_inl_ne_mk_inr_of_norm_lt_one`). -/

/-! ## Elementary inputs -/

/-- **The disk coordinate of a configuration point of positive chord length is strictly inside the
disk.**  For `(midpoint, η, length)` with `length ≠ 0` the capping disk coordinate is
`midpoint / √(‖midpoint‖² + length²)`, whose norm is `< 1`. -/
lemma confOf_snd_norm_lt_one_of_ne_zero (p : (ℝ × ℝ) × UnitAddCircle × ℝ) (h : p.2.2 ≠ 0) :
    ‖(confOf p).2.1‖ < 1 := by
  have hS : 0 < Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_ne_zero h, sq_nonneg p.1.1, sq_nonneg p.1.2])
  have hS2 : Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) ^ 2
      = p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2 := Real.sq_sqrt (by positivity)
  have hnorm2 : ‖(confOf p).2.1‖ ^ 2 < 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [confOf]
    rw [← sq, ← sq, div_pow, div_pow, ← add_div, hS2]
    rw [div_lt_one (by positivity)]
    nlinarith [sq_pos_of_ne_zero h]
  nlinarith [norm_nonneg (confOf p).2.1, sq_nonneg (‖(confOf p).2.1‖ - 1)]

/-- **The strip disk coordinate of a non-degenerate chord is strictly inside the disk.**  This is the
`stripData` form of `confOf_snd_norm_lt_one_of_ne_zero`.  The strictness is exactly what the strip
clause of `IsPlaneChart` does *not* provide by itself (that clause only pins `‖d‖ ≤ 1`); it is what
`Function.Injective γ` supplies at every point of the core loop, and it is what rules out the
counterexample of the review gate (the constant chart of a constant curve). -/
lemma stripData_snd_norm_lt_one_of_chord_ne {γ : Circle → ℝ × ℝ} {w : EuclideanSpace ℝ (Fin 2)}
    (h : γ (Circle.exp (w 0)) ≠ γ (Circle.exp (w 1))) :
    ‖(stripData γ w).2.1‖ < 1 := by
  show ‖(confOf (Submission.Configuration.muOrd γ
    (Circle.exp (w 0), Circle.exp (w 1)))).2.1‖ < 1
  refine confOf_snd_norm_lt_one_of_ne_zero _ ?_
  show Submission.Geometry.eucNorm (γ (Circle.exp (w 0)) - γ (Circle.exp (w 1))) ≠ 0
  intro hz
  exact h (sub_eq_zero.mp (Submission.Geometry.eucNorm_eq_zero.mp hz))

/-- **The strip chart as an explicit configuration class.**  The rotated strip chart is the class of
the configuration point whose capping coordinates are the strip data of the parameter; this is the
form in which the disk coordinate of a strip value can be read off.  (It is the `v = 0` case of the
same computation as `Work.Drive.stripChart_eq_mk` of `exists_contMDiffAt_stripChart_closed.lean`.) -/
private lemma stripChart_eq_mk_piece (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (v : UnitAddCircle) (w : EuclideanSpace ℝ (Fin 2)) :
    stripChart γ hγne v w = Quotient.mk''
      (Sum.inl (⟨((stripData γ w).1, (stripData γ w).2.1, (stripData γ w).2.2 + v),
        stripData_pos hγne w,
        confOf_snd_norm_le_one
          (Submission.Configuration.muOrd γ (Circle.exp (w 0), Circle.exp (w 1)))⟩
        : ConfigPiece) : ConfigPiece ⊕ CapPiece) := by
  unfold stripChart confPiece stripData rotConfig
  rfl

/-- The two circle points of a maximal chord (`θ ± π/2`) are distinct: their parameters differ by
`π`, which is not a multiple of `2π`. -/
private lemma exp_arg_add_ne_exp_arg_sub (θ : ℝ) :
    Circle.exp (θ + Real.pi / 2) ≠ Circle.exp (θ - Real.pi / 2) := by
  intro hc
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hc
  have h2 : (2 * m : ℤ) = 1 := by
    have h3 : ((2 * m : ℤ) : ℝ) = 1 := by
      push_cast
      have h4 : (m : ℝ) * (2 * Real.pi) = Real.pi := by linarith
      nlinarith [Real.pi_pos]
    exact_mod_cast h3
  omega

/-- **A strip value over a non-degenerate chord is strictly configuration side**: it is not the class
of any cap point.  This is the exact statement consumed by `coreLoopCapDisjoint`; it holds because
the configuration representative of the strip value has disk coordinate `‖d‖ < 1`, and the only
classes of `CappingSpace` with such a representative are strictly configuration side. -/
private lemma stripChart_ne_mk_inr_of_chord_ne {γ : Circle → ℝ × ℝ}
    (hγne : ∀ x : Circle, γ x ≠ 0) {w : EuclideanSpace ℝ (Fin 2)}
    (hw : γ (Circle.exp (w 0)) ≠ γ (Circle.exp (w 1))) {q : CapPiece} :
    stripChart γ hγne 0 w ≠ Quotient.mk'' (Sum.inr q) := by
  let p : ConfigPiece :=
    ⟨((stripData γ w).1, (stripData γ w).2.1, (stripData γ w).2.2 + 0), stripData_pos hγne w,
      confOf_snd_norm_le_one
        (Submission.Configuration.muOrd γ (Circle.exp (w 0), Circle.exp (w 1)))⟩
  have hnorm : ‖(p : ℝ × ℂ × UnitAddCircle).2.1‖ < 1 :=
    stripData_snd_norm_lt_one_of_chord_ne hw
  intro h
  have heq : (Quotient.mk'' (Sum.inl p) : CappingSpace) = Quotient.mk'' (Sum.inr q) :=
    (stripChart_eq_mk_piece γ hγne 0 w).trans h
  exact mk_inl_ne_mk_inr_of_norm_lt_one hnorm heq

/-! ## The theorem -/

/-- **The side half of the core-loop vs rotated-plane disjointness** (it discharges the `sorry` of
`Work.Drive.coreLoop_disjoint_rotCapping_capPart`, whose version without `hγinj` was refuted by the
review gate: for constant `γ ≡ p ≠ 0` the constant chart satisfies every clause of `IsPlaneChart`,
since the clauses pin only `‖d‖ ≤ 1`, and `Q 1 = rotCapping 0 (Q 0)`).  A point of the core loop of a
plane chart (`Q` at `‖z‖ = 1`) is never the rotation by *any* `w` of a point of the *cap* part of the
chart (`‖z'‖ < 1/2`).

`IsPlaneChart`'s cap clause gives `Q z' = Quotient.mk'' (Sum.inr c)` for a `CapPiece` `c`, which is
strictly cap side (`IsCapVec`, `Work.Drive.isCapVec_capProjVecOf`), the boundary `‖d‖ = 1` being glued
by `cappingRel` to the configuration side.  The loop point `Q z` is a `stripChart` value with disk
coordinate `‖d‖ = ‖midpoint‖/R < 1` — strict because the maximal chord is non-degenerate
(`γ (exp (i (arg z + π/2))) ≠ γ (exp (i (arg z - π/2)))`, supplied by `hγinj`) — hence `¬IsCapVec`.
`rotCapping w` multiplies both complex coordinates of the lift by unit complex numbers, preserving
`‖c₁‖`, `‖c₂‖` and the side; `IsCapVec` and its complement are complementary, so the points differ.

(Formalisation note: the proof below does not compute the projective lift at all — the equivalent but
strictly weaker input it needs is the *interior*-vs-*boundary* dichotomy of the two pieces of
`CappingSpace`, `‖d‖ < 1` on the closed loop and a `CapPiece` on the rotated cap side.  See the module
docstring.) -/
theorem coreLoopCapDisjoint {γ : Circle → ℝ × ℝ}
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    ⦃w : UnitAddCircle⦄ ⦃z z' : ℂ⦄
    (hz : ‖z‖ = 1) (hz' : ‖z'‖ < 1 / 2) :
    Q z ≠ Work.Drive.rotCapping w (Q z') := by
  -- the strip clause at the loop point: the value is the maximal chord `arg z ± π/2`
  have hsz : Real.sqrt (Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2) = Real.pi / 2 := by
    have h1 : Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2 = (Real.pi / 2) ^ 2 := by rw [hz]; ring
    rw [h1, Real.sqrt_sq (by positivity)]
  have hstrip : Q z = stripChart γ hγne 0
      (mk2 (Complex.arg z + Real.pi / 2) (Complex.arg z - Real.pi / 2)) := by
    have h := hQ.2.1 z (by rw [hz]; norm_num) (le_of_eq hz)
    rwa [hsz] at h
  -- the cap clause at the cap point
  obtain ⟨c, hc⟩ := hQ.2.2.2 z' hz'
  intro hcon
  -- the rotation of a cap point is again a cap point
  have hrot : rotCapping w (Q z') = Quotient.mk'' (Sum.inr (rotCap w c)) := by
    rw [hc, rotCapping_mk, rotSum_inr]
  -- the loop point is strictly configuration side, so the two classes differ
  exact stripChart_ne_mk_inr_of_chord_ne hγne
    (fun h => exp_arg_add_ne_exp_arg_sub (Complex.arg z) (hγinj h))
    (hstrip.symm.trans (hcon.trans hrot))

end

end Work.Drive
