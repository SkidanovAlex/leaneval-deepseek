import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.HopfK.Basic

/-!
# Coordinates on the target sphere `Tgt m = S^{2m}`, and the meridian formula

`Tgt m = Sph (EuclideanSpace ℝ (Fin (2 * m + 1)))` is identified with the unit sphere of
`WithLp 2 (Eu m × ℝ)` by the linear isometry equivalence `euclTgtIso m`; the second coordinate is
the height `tgtHeight m`, and `tgtCoords m x = (a, s)` collects the two coordinates of a point of
`Tgt m`, so that `‖a‖ ^ 2 + s ^ 2 = 1`.

The central object is the *meridian formula* `merCoord m η z`: on the unit sphere it moves the point
`z = (a, s)` along the meridian through it to the point of the same meridian whose height is
`-1 + η (s + 1)`.  For `η = 1` this is the identity, and for `η = 0` it is the south pole `(0, -1)`.
Since the height `-1 + η (s + 1)` is increasing in `η ≤ 1`, the formula keeps the point inside the
closed cap `{s ≤ 1/2}`; this is what makes the cap contractible.
-/

namespace Work.KT

noncomputable section

open scoped Topology

/-! ## Coordinates on `Tgt m` -/

/-- A point of `Tgt m`, viewed in the coordinates `WithLp 2 (Eu m × ℝ)` of `euclTgtIso`. -/
def tgtLp (m : ℕ) (x : Tgt m) : WithLp 2 (Eu m × ℝ) :=
  (euclTgtIso m).symm (x : EuclideanSpace ℝ (Fin (2 * m + 1)))

/-- The coordinates `(a, s)` of a point of `Tgt m`: `s = tgtHeight m x` is the height and `a` the
horizontal part.  They satisfy `‖a‖ ^ 2 + s ^ 2 = 1`. -/
def tgtCoords (m : ℕ) (x : Tgt m) : Eu m × ℝ := WithLp.ofLp (tgtLp m x)

lemma tgtHeight_eq_snd (m : ℕ) (x : Tgt m) : tgtHeight m x = (tgtCoords m x).2 := rfl

lemma norm_tgtLp (m : ℕ) (x : Tgt m) : ‖tgtLp m x‖ = 1 := by
  rw [tgtLp, LinearIsometryEquiv.norm_map]
  exact mem_sphere_zero_iff_norm.mp x.2

lemma norm_sq_tgtCoords (m : ℕ) (x : Tgt m) :
    ‖(tgtCoords m x).1‖ ^ 2 + (tgtCoords m x).2 ^ 2 = 1 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (tgtLp m x)
  rw [norm_tgtLp m x, one_pow] at h
  rw [h]
  simp [tgtCoords]

lemma continuous_tgtCoords (m : ℕ) : Continuous (tgtCoords m) :=
  (WithLp.prod_continuous_ofLp 2 (Eu m) ℝ).comp
    ((euclTgtIso m).symm.continuous.comp continuous_subtype_val)

/-- `euclTgtIso m` applied to the coordinates of a point of `Tgt m` returns that point. -/
lemma euclTgtIso_toLp_tgtCoords (m : ℕ) (x : Tgt m) :
    euclTgtIso m (WithLp.toLp 2 (tgtCoords m x)) = (x : EuclideanSpace ℝ (Fin (2 * m + 1))) := by
  rw [tgtCoords, tgtLp, WithLp.toLp_ofLp, LinearIsometryEquiv.apply_symm_apply]

lemma tgtCoords_southPt (m : ℕ) : tgtCoords m (southPt m) = ((0 : Eu m), (-1 : ℝ)) := by
  rw [tgtCoords, tgtLp, southPt]
  simp

lemma southPt_mem_capTminus (m : ℕ) : southPt m ∈ capTminus m := by
  show tgtHeight m (southPt m) ≤ 1 / 2
  rw [tgtHeight_eq_snd, tgtCoords_southPt]
  norm_num

/-! ## The meridian formula -/

/-- The meridian map in coordinates: it sends `z = (a, s)` to the point of the same meridian whose
height is `-1 + η (s + 1)`, rescaling the horizontal part so that the result has norm `1` whenever
`z` has.  `η = 1` gives the identity and `η = 0` the south pole `(0, -1)`. -/
def merCoord (m : ℕ) (η : ℝ) (z : Eu m × ℝ) : Eu m × ℝ :=
  (Real.sqrt (η * (2 - η * (z.2 + 1)) / (1 - z.2)) • z.1, -1 + η * (z.2 + 1))

lemma merCoord_zero (m : ℕ) (z : Eu m × ℝ) : merCoord m 0 z = ((0 : Eu m), (-1 : ℝ)) := by
  simp [merCoord]

lemma merCoord_one (m : ℕ) {z : Eu m × ℝ} (hz : z.2 ≠ 1) : merCoord m 1 z = z := by
  have h : (1 : ℝ) - z.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have harg : (1 : ℝ) * (2 - 1 * (z.2 + 1)) / (1 - z.2) = 1 := by
    rw [show (1 : ℝ) * (2 - 1 * (z.2 + 1)) = 1 - z.2 by ring, div_self h]
  simp only [merCoord, harg, Real.sqrt_one, one_smul]
  ext <;> simp

lemma merCoord_snd_le (m : ℕ) {z : Eu m × ℝ} {η : ℝ} (hz2 : -1 ≤ z.2) (hs : z.2 ≤ 1 / 2)
    (_hη0 : 0 ≤ η) (hη1 : η ≤ 1) : (merCoord m η z).2 ≤ 1 / 2 := by
  have h : (merCoord m η z).2 = -1 + η * (z.2 + 1) := rfl
  rw [h]
  nlinarith [hη1, hz2, hs]

end

end Work.KT
