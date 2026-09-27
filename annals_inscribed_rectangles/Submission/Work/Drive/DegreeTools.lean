import Mathlib
import Submission.Work.Drive.WindingNumber
import Submission.Work.Drive.winding_zero_far

/-!
# Tools for the degree of a circle map

`Work.Drive.degree` (in `Submission.Work.Drive.WindingNumber`) is the monodromy of a lift of a
continuous circle map.  This file supplies the elementary algebra of the degree used by the
*computational* description of the winding number (`Work.Drive.degree_crossing_count`,
`Work.Drive.winding_eq_crossing_sum`, `Work.Drive.winding_values`) and by the capping step of
Hugelmeyer's order theory (`∂M` is a `(2,1)`-torus knot, i.e. the `S¹`-coordinate of the boundary of
the configuration Möbius strip traverses the circle with degree `±2`):

* `degree_neg` — the degree of the pointwise negative is the negative of the degree;
* `degree_sub` — the degree is additive for the pointwise difference (this is what turns the ratio of
  two direction maps into the *difference* of two winding numbers);
* `liftOf_add_nat` — the monodromy bookkeeping behind `degree_nsmul_comp`;
* `degree_nsmul_comp` — precomposition with multiplication by `n` on the circle multiplies the degree
  by `n` (the doubling `n = 2` is exactly the `(2,1)`-knot structure of `∂M`).

It also records the multiplicativity of the direction class, read on `ℂ` (`dirCz`): the direction class
of a product of non-zero complex numbers is the sum of the direction classes.  This is what turns a
*ratio* of two direction maps into the difference of two of them, which together with `degree_sub` is
the local computation behind "the winding number jumps by `±2` across a transversal crossing of the
curve" (see `WINDING_STATUS.md`).
-/

namespace Work.Drive

open scoped Topology

/-- **The degree of the pointwise negative.** -/
theorem degree_neg (f : UnitAddCircle → UnitAddCircle) (hf : Continuous f) :
    degree (fun u => -f u) hf.neg = -degree f hf := by
  refine (degree_eq_of_lift hf.neg (G := fun t => -(liftOf f hf t)) (liftOf_continuous f hf).neg
    ?_ (n := -degree f hf) ?_).symm
  · intro t
    show ((-(liftOf f hf t) : ℝ) : UnitAddCircle) = -(f (t : UnitAddCircle))
    rw [AddCircle.coe_neg, liftOf_lifts]
  · intro t
    show -(liftOf f hf (t + 1)) = -(liftOf f hf t) + ((↑(-degree f hf) : ℤ) : ℝ)
    rw [liftOf_add_one, Int.cast_neg]
    ring

/-- **The degree of the pointwise difference.**  Combined with the multiplicativity of the direction
class this computes the degree of a ratio of directions, which is the local computation behind the
fact that the winding number jumps by `±2` across a transversal crossing of the curve. -/
theorem degree_sub (f g : UnitAddCircle → UnitAddCircle) (hf : Continuous f) (hg : Continuous g) :
    degree (fun u => f u - g u) (hf.sub hg) = degree f hf - degree g hg := by
  refine (degree_eq_of_lift (hf.sub hg)
    (G := fun t => liftOf f hf t - liftOf g hg t)
    ((liftOf_continuous f hf).sub (liftOf_continuous g hg)) ?_ (n := degree f hf - degree g hg) ?_).symm
  · intro t
    show (((liftOf f hf t - liftOf g hg t : ℝ) : UnitAddCircle)) = f (t : UnitAddCircle) - g (t : UnitAddCircle)
    rw [AddCircle.coe_sub, liftOf_lifts, liftOf_lifts]
  · intro t
    show liftOf f hf (t + 1) - liftOf g hg (t + 1)
      = (liftOf f hf t - liftOf g hg t) + ((↑(degree f hf - degree g hg) : ℤ) : ℝ)
    rw [liftOf_add_one, liftOf_add_one]
    push_cast
    ring

/-- The lift shifts by `n` times the degree over a shift of `n` periods. -/
lemma liftOf_add_nat (f : UnitAddCircle → UnitAddCircle) (hf : Continuous f) (n : ℕ) (t : ℝ) :
    liftOf f hf (t + n) = liftOf f hf t + (n : ℝ) * (degree f hf : ℝ) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h1 : t + (k + 1 : ℕ) = (t + k) + 1 := by push_cast; ring
      rw [h1, liftOf_add_one, ih]
      push_cast
      ring

/-- **Precomposition with `n`-fold multiplication multiplies the degree by `n`.**  The case `n = 2` is
the `(2,1)`-knot structure: the doubled tangent direction of a smooth Jordan curve winds twice, which
is what makes `∂M` a meridian after the capping. -/
theorem degree_nsmul_comp (f : UnitAddCircle → UnitAddCircle) (hf : Continuous f) (n : ℕ) :
    degree (fun u : UnitAddCircle => f (n • u)) (hf.comp (continuous_nsmul n))
      = (n : ℤ) * degree f hf := by
  refine (degree_eq_of_lift (hf.comp (continuous_nsmul n))
    (G := fun t : ℝ => liftOf f hf ((n : ℝ) * t))
    ((liftOf_continuous f hf).comp (continuous_const.mul continuous_id)) ?_
    (n := (n : ℤ) * degree f hf) ?_).symm
  · intro t
    show ((liftOf f hf ((n : ℝ) * t) : ℝ) : UnitAddCircle) = f (n • (t : UnitAddCircle))
    rw [liftOf_lifts, ← AddCircle.coe_nsmul]
    congr 1
    rw [nsmul_eq_mul]
  · intro t
    have h1 : (n : ℝ) * (t + 1) = (n : ℝ) * t + n := by ring
    rw [h1, liftOf_add_nat]
    push_cast
    ring

/-! ## The direction class on `ℂ` -/

/-- The direction class of `Submission.Collision.dirC`, read on `ℂ`: it is the *doubled*, undirected
direction `arg z / π` in `ℝ/ℤ`, so `dirCz (-z) = dirCz z` and `dirCz (z * w) = dirCz z + dirCz w`. -/
noncomputable def dirCz (z : ℂ) : UnitAddCircle := ((Complex.arg z / Real.pi : ℝ) : UnitAddCircle)

/-- Equality of two classes in `ℝ/ℤ`: two real representatives give the same class exactly when they
differ by an integer. -/
lemma unitAddCircle_coe_eq_iff (a b : ℝ) :
    ((a : ℝ) : UnitAddCircle) = ((b : ℝ) : UnitAddCircle) ↔ ∃ k : ℤ, a = b + (k : ℝ) := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    have hk' : (k : ℝ) = a - b := by simpa using hk
    exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hk' : (k : ℝ) = a - b := by linarith
    simpa using hk'

/-- **The direction class is multiplicative**: the (doubled) direction of a product of non-zero complex
numbers is the sum of the directions.  Consequently the direction of a *ratio* is the difference, so
`degree_sub` computes the change of the winding number across a crossing of the curve. -/
theorem dirCz_mul {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    dirCz (z * w) = dirCz z + dirCz w := by
  have h := Complex.arg_mul_coe_angle hz hw
  have h2 : ((Complex.arg (z * w) - Complex.arg z - Complex.arg w : ℝ) : Real.Angle) = 0 := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_sub, h]
    abel
  obtain ⟨n, hn⟩ := Real.Angle.coe_eq_zero_iff.mp h2
  rw [dirCz, dirCz, dirCz, ← AddCircle.coe_add]
  refine (unitAddCircle_coe_eq_iff _ _).mpr ⟨2 * n, ?_⟩
  have hn' : Complex.arg (z * w) - Complex.arg z - Complex.arg w
      = (n : ℝ) * (2 * Real.pi) := by
    rw [← hn]; simp [zsmul_eq_mul, mul_comm]
  have hkey : (((2 * n : ℤ)) : ℝ)
      = (Complex.arg (z * w) - Complex.arg z - Complex.arg w) / Real.pi := by
    rw [hn']; push_cast; field_simp
  rw [hkey]
  field_simp
  ring

/-- **The direction class of an inverse is the negative of the direction class.** -/
theorem dirCz_inv {z : ℂ} (hz : z ≠ 0) : dirCz z⁻¹ = -dirCz z := by
  rw [dirCz, dirCz, Complex.arg_inv]
  by_cases h : Complex.arg z = Real.pi
  · rw [if_pos h, h]
    have h1 : Real.pi / Real.pi = (1 : ℝ) := by field_simp
    rw [h1, AddCircle.coe_period]
    simp
  · rw [if_neg h]
    rw [show -Complex.arg z / Real.pi = -(Complex.arg z / Real.pi) by ring, AddCircle.coe_neg]

/-! ## Two vanishing criteria for the winding number -/

/-- **The winding number vanishes for a curve whose direction map is null-homotopic.**  In particular
it vanishes for every `p` in an unbounded piece of the complement of the curve. -/
theorem winding_eq_zero_of_homotopic_const (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ)
    {p : ℝ × ℝ} (hp : p ∉ Set.range γ) {c : UnitAddCircle}
    (h : ContinuousMap.Homotopic
      ⟨dirCurve γ hγ p hp, continuous_dirCurve γ hγ p hp⟩ (ContinuousMap.const _ c)) :
    winding γ hγ hp = 0 := by
  rw [winding]
  simpa using (degree_homotopic h).trans (degree_const c)

/-- **The winding number is `0` far out along any line through `p`.**  This is the endpoint
computation of the "signed crossing count" route to `winding_values`: along the line
`τ ↦ p + τ • u`, for `|τ|` larger than the diameter of the curve the point is outside the ball
containing `γ`, where the winding vanishes (`Work.Drive.winding_zero_far`). -/
theorem exists_winding_eq_zero_far (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ)
    {p : ℝ × ℝ} (hp : p ∉ Set.range γ) {u : ℝ × ℝ} (hu : u ≠ 0) :
    ∃ R : ℝ, ∀ t : ℝ, R < |t| → ∀ (h : p + t • u ∉ Set.range γ), winding γ hγ h = 0 := by
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ∀ x : UnitAddCircle, dist (γ x) (γ 0) ≤ D := by
    obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp (isCompact_range hγ).isBounded
    exact ⟨D, fun x => hD (x := γ x) ⟨x, rfl⟩ (y := γ 0) ⟨0, rfl⟩⟩
  have hu' : 0 < ‖u‖ := norm_pos_iff.mpr hu
  refine ⟨(D + dist p (γ 0) + 1) / ‖u‖, fun t ht h => ?_⟩
  refine winding_zero_far hγ h (c := γ 0) fun x => ?_
  have hnorm : ‖t • u‖ = |t| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
  have htri : ‖t • u‖ ≤ dist (p + t • u) (γ 0) + dist p (γ 0) := by
    have h1 : dist (p + t • u) p ≤ dist (p + t • u) (γ 0) + dist (γ 0) p :=
      dist_triangle (p + t • u) (γ 0) p
    rw [dist_comm (γ 0) p] at h1
    have h2 : dist (p + t • u) p = ‖t • u‖ := by
      rw [dist_eq_norm]; congr 1; abel
    rwa [h2] at h1
  have hlarge : D + dist p (γ 0) < |t| * ‖u‖ := by
    rw [div_lt_iff₀ hu'] at ht
    linarith
  linarith [hD x, htri, hnorm]

end Work.Drive
