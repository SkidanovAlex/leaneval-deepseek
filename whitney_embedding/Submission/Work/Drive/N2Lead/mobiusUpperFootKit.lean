import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperStarRowKit
import Submission.Work.Drive.N2C.lowerCert

/-!
# The `mobiusUpperStarRows` foot kit

See `NOTES_S49_starRows_MISSING_ROWS.md`.  The picture `mobiusTwisted D η S ε εp Dp` at the level
`f p + 3η/2` has two kinds of pieces:

* the *model* part (`y` in `saddleRegion`): the pushed, twisted arcs `mobiusAlpha`/`mobiusBeta`
  (`Work.Drive.N2Lead.model_value`), whose angular rate about `0` is provided by
  `mobius_pushedStar` + `mobius_upperArcs` + `mobiusModelImSubmersion`;
* the *foot* part (`y` outside the region): `pushY ∘ twistX` of the polar picture `S.C₀` at
  `footMap … y` — the `twistY S.a' 1` of the park picture `S.A` cancels against the ambient
  `twistY S.a' (-1)` exactly (this file).

This file records the value identification and the elementary norm bounds of the foot part.  The
*rate* rows of the foot part need the shape of the polar profile `S.r` on the park range, which
`MobiusPacket` does not export (see the NOTES file).
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-! ## The value of the foot part -/

/-- **The foot part of the twisted picture.**  Outside the model region the drawing is the park
picture `S.A` at the foot, and the ambient `twistY S.a' (-1)` of the twisted picture cancels the
`twistY S.a' 1` of `S.A = twistY S.a' 1 ∘ S.C₀`. -/
theorem mobiusTwisted_foot {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    {S : MobiusPacket D η} {ε εp Dp : ℝ} {y : M}
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20)) :
    mobiusTwisted D η S ε εp Dp y = pushY Dp εp 1
      (twistX ε (-1) (S.C₀ (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y))) := by
  rw [mobiusTwisted, mobiusWindowDrawing, if_neg hyD, S.hAeq,
    show twistY S.a' (-1) (twistY S.a' 1
        (S.C₀ (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y)))
      = S.C₀ (Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y) from by
        rw [twistY_comp, neg_add_cancel, twistY_zero]]

/-! ## Norm bounds -/

/-- The vertical profile of the push moves the `y`-coordinate by at most `D`. -/
theorem abs_pushProf_sub_le (D ε : ℝ) (hD : 0 ≤ D) (y : ℝ) :
    |pushProf D ε 1 y - y| ≤ D := by
  rw [pushProf]
  have h : |2 * Real.smoothTransition ((y + ε) / (2 * ε)) - 1| ≤ 1 := by
    have h1 := Real.smoothTransition.nonneg ((y + ε) / (2 * ε))
    have h2 := Real.smoothTransition.le_one ((y + ε) / (2 * ε))
    rw [abs_le]; constructor <;> linarith
  have hst : Real.smoothTransition (1 : ℝ) = 1 := Real.smoothTransition.one_of_one_le le_rfl
  rw [hst, one_mul]
  calc |y + D * (2 * Real.smoothTransition ((y + ε) / (2 * ε)) - 1) - y|
      = |D * (2 * Real.smoothTransition ((y + ε) / (2 * ε)) - 1)| := by ring_nf
    _ = |D| * |2 * Real.smoothTransition ((y + ε) / (2 * ε)) - 1| := abs_mul _ _
    _ ≤ D * 1 := by
        rw [abs_of_nonneg hD]
        exact mul_le_mul_of_nonneg_left h hD
    _ = D := by ring

/-- **The push does not increase the norm by more than `D`** (for `D ≥ 0`). -/
theorem norm_pushY_le (D ε : ℝ) (hD : 0 ≤ D) (v : E3) : ‖pushY D ε 1 v‖ ≤ ‖v‖ + D := by
  have hcoord : pushY D ε 1 v = v + WithLp.toLp 2 ![0, pushProf D ε 1 (v 1) - v 1, 0] := by
    ext i; fin_cases i <;> simp [pushY_eq_prof]
  rw [hcoord]
  have hbd : ‖(WithLp.toLp 2 ![0, pushProf D ε 1 (v 1) - v 1, 0] : E3)‖
      = |pushProf D ε 1 (v 1) - v 1| := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  calc ‖v + _‖ ≤ ‖v‖ + ‖_‖ := norm_add_le _ _
    _ = ‖v‖ + |pushProf D ε 1 (v 1) - v 1| := by rw [hbd]
    _ ≤ ‖v‖ + D := by
        have := abs_pushProf_sub_le D ε hD (v 1)
        linarith

/-- The norm of the polar curve value at `Θ t` is at most `3` (`hrR`). -/
theorem polar_norm_le_three {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    (S : MobiusPacket D η) (t : ℝ) :
    ‖(S.r (S.Θ t) : ℂ) * Complex.exp (((S.Θ t : ℝ) : ℂ) * Complex.I)‖ ≤ 3 := by
  rw [norm_mul]
  have h1 : ‖((S.r (S.Θ t) : ℝ) : ℂ)‖ = S.r (S.Θ t) :=
    Complex.norm_of_nonneg (le_of_lt (S.hrpos _))
  have h2 : ((((S.Θ t : ℝ) : ℂ) * Complex.I)).re = 0 := by simp
  rw [h1, Complex.norm_exp, h2, Real.exp_zero, mul_one]
  exact S.hrR _

/-- **The norm bound of the foot part on the marked component.**  If the foot of `y` is the marked
anchor point `L.γ i t`, then the twisted picture of `y` is within `Dp + 3` of the origin. -/
theorem mobiusTwisted_norm_le_marked {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p}
    {η : ℝ} {S : MobiusPacket D η} {ε εp Dp : ℝ} (hDp : 0 ≤ Dp) {y : M} {t : ℝ}
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20))
    (hfoot : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ S.i t) :
    ‖mobiusTwisted D η S ε εp Dp y‖ ≤ Dp + 3 := by
  rw [mobiusTwisted_foot hyD, hfoot, S.hC₀val t]
  refine le_trans (norm_pushY_le Dp εp hDp _) ?_
  rw [norm_twistX]
  have h3 : ‖Work.Drive.N2.cE3 ((S.r (S.Θ t) : ℂ)
      * Complex.exp (((S.Θ t : ℝ) : ℂ) * Complex.I))‖ ≤ 3 := by
    rw [norm_cE3_eq_engine]
    exact polar_norm_le_three S t
  linarith

/-! ## The far part of the picture -/

/-- The planar projection of the vertical shift `(0, D, 0)`. -/
lemma proj2_shift_vert (D : ℝ) :
    proj2 (WithLp.toLp 2 ![(0:ℝ), D, 0] : E3) = (D : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [proj2, Complex.mul_re, Complex.mul_im]

/-- The planar projection of the push, on the side `εp ≤ v 1` of the band: the rigid translation
`y ↦ y + D`. -/
lemma proj2_pushY_of_le {D εp : ℝ} (hεp : 0 < εp) {v : E3} (hv : εp ≤ v 1) :
    proj2 (pushY D εp 1 v) = proj2 v + (D : ℂ) * Complex.I := by
  have h : pushProf D εp 1 (v 1) = v 1 + D := pushProf_one_eq_of_le hεp hv
  apply Complex.ext <;> simp [proj2, pushY_eq_prof, h, Complex.mul_re, Complex.mul_im]

/-- **The far part of the upper picture is a circle of radius `1`** about the shifted parking spot:
for `j ≠ i` and a level point whose foot is the far component `L.γ j t`, the planar picture is the
projection of the parking spot plus `Dp I` plus the round circle.  (In particular it lies in the
disc of radius `2` about `proj2 (farPos S.n j) + Dp I`, which is the far region of the star
rows.) -/
theorem mobiusTwisted_far_proj {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p}
    {η : ℝ} {S : MobiusPacket D η} {ε εp Dp : ℝ}
    (hε : 0 < ε) (hε19 : ε ≤ 19) (hεp : 0 < εp) (hεp19 : εp ≤ 19)
    {j : Fin S.n} (hj : j ≠ S.i) {y : M} {t : ℝ}
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z
      (39 / 20))
    (hfoot : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ j t) :
    proj2 (mobiusTwisted D η S ε εp Dp y)
      = proj2 (farPos S.n j) + (Dp : ℂ) * Complex.I + proj2 (Work.Drive.N2.ang t) := by
  rw [mobiusTwisted_foot hyD, hfoot, S.hC₀far j hj t]
  have hx : (farCurve S.n j t) 0 ≤ -ε := by
    have h := Work.Drive.N2C.re_proj2_farCurve S.n j t
    have h1 : Real.cos (2 * Real.pi * t) ≤ 1 := Real.cos_le_one _
    simp only [proj2] at h
    linarith
  have hy : εp ≤ (farCurve S.n j t) 1 := by
    have h := Work.Drive.N2C.im_proj2_farCurve S.n j t
    have h1 : -1 ≤ Real.sin (2 * Real.pi * t) := Real.neg_one_le_sin _
    have h3 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [proj2] at h
    linarith
  rw [twistX_eq_self hε hx, proj2_pushY_of_le hεp hy, Work.Drive.N2C.proj2_farCurve]
  ring

end

end Work.Drive.N2Lead
