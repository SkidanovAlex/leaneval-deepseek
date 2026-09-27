import Mathlib
import Submission.Work.Surf.defs
import Submission.Work.Drive.Surf.Model
import Submission.Work.Drive.ParityDegreeDefs

/-!
# A smooth parametrisation of the boundary of the unit square

`sqPar : ℝ → ℝ × ℝ` is a `C¹`, `1`-periodic parametrisation of `∂[0,1]²` whose velocity vanishes at
the four corners.  It is the antiderivative of the `1`-periodic velocity `sqVelPer`; the velocity is
built from the kernel `sqK x = 24 x (1 - x)`, whose primitive `sqRamp t = t² (3 - 2 t)` (divided by
`4`) is the smooth increasing bijection `[0,1] → [0,1]` with flat ends.

The construction is designed so that `sqPar` is differentiable everywhere — the naive parametrisation
of the square has corners — which is what the degree machinery of
`Submission/Work/Drive/winding_eq_crossing_sum.lean` needs.
-/

namespace Work.Surf

open Set MeasureTheory

noncomputable section

/-- The smooth nonnegative kernel on the unit interval, with `∫_0^1 sqK = 4`. -/
def sqK (x : ℝ) : ℝ := 24 * x * (1 - x)

/-- The primitive of `sqK` divided by `4`: the smooth increasing bijection `[0,1] → [0,1]` with
vanishing derivative at both endpoints. -/
def sqRamp (t : ℝ) : ℝ := t ^ 2 * (3 - 2 * t)

@[fun_prop]
lemma continuous_sqK : Continuous sqK := by unfold sqK; fun_prop

lemma continuous_sqRamp : Continuous sqRamp := by unfold sqRamp; fun_prop

lemma sqRamp_zero : sqRamp 0 = 0 := by norm_num [sqRamp]

lemma sqRamp_one : sqRamp 1 = 1 := by norm_num [sqRamp]

lemma sqRamp_hasDerivAt (t : ℝ) : HasDerivAt sqRamp (sqK t / 4) t := by
  have hA : HasDerivAt (fun x : ℝ => (3:ℝ) * x ^ 2) (3 * (2 * t ^ (2 - 1))) t :=
    (hasDerivAt_pow 2 t).const_mul 3
  have hB : HasDerivAt (fun x : ℝ => (2:ℝ) * x ^ 3) (2 * (3 * t ^ (3 - 1))) t :=
    (hasDerivAt_pow 3 t).const_mul 2
  have hC := hA.sub hB
  have hD : HasDerivAt (fun x : ℝ => 3 * x ^ 2 - 2 * x ^ 3)
      (3 * (2 * t ^ (2 - 1)) - 2 * (3 * t ^ (3 - 1))) t :=
    hC.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by simp only [Pi.sub_apply])
  have hE : HasDerivAt (fun x : ℝ => x ^ 2 * (3 - 2 * x))
      (3 * (2 * t ^ (2 - 1)) - 2 * (3 * t ^ (3 - 1))) t :=
    hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by ring)
  convert hE using 1
  · rfl
  · unfold sqK; ring

lemma sqRamp_deriv (t : ℝ) : deriv sqRamp t = sqK t / 4 := (sqRamp_hasDerivAt t).deriv

lemma integral_sqK (t : ℝ) : ∫ x in (0 : ℝ)..t, sqK x = 4 * sqRamp t := by
  have hder : ∀ x : ℝ, HasDerivAt (fun y : ℝ => 4 * sqRamp y) (sqK x) x := by
    intro x
    have h : HasDerivAt (fun y : ℝ => 4 * sqRamp y) (4 * (sqK x / 4)) x :=
      (sqRamp_hasDerivAt x).const_mul 4
    convert h using 1
    ring
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (f := fun y : ℝ => 4 * sqRamp y) (fun x _ => hder x) (continuous_sqK.intervalIntegrable 0 t)
  rw [this, sqRamp_zero]
  ring

lemma sqRamp_strictMonoOn : StrictMonoOn sqRamp (Icc 0 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) continuous_sqRamp.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [sqRamp_deriv]
  unfold sqK
  nlinarith [hx.1, hx.2]

lemma sqRamp_monotoneOn : MonotoneOn sqRamp (Icc 0 1) := sqRamp_strictMonoOn.monotoneOn

lemma sqRamp_mem_Icc {t : ℝ} (ht : t ∈ Icc 0 1) : sqRamp t ∈ Icc 0 1 :=
  ⟨by simpa [sqRamp_zero] using sqRamp_monotoneOn (left_mem_Icc.mpr zero_le_one) ht ht.1,
   by simpa [sqRamp_one] using sqRamp_monotoneOn ht (right_mem_Icc.mpr zero_le_one) ht.2⟩

lemma sqRamp_surjOn {y : ℝ} (hy : y ∈ Icc (0:ℝ) 1) : ∃ t ∈ Icc (0:ℝ) 1, sqRamp t = y := by
  have hmem : y ∈ sqRamp '' Set.Icc (0:ℝ) 1 :=
    intermediate_value_Icc zero_le_one continuous_sqRamp.continuousOn
      ⟨by rw [sqRamp_zero]; exact hy.1, by rw [sqRamp_one]; exact hy.2⟩
  obtain ⟨t, ht, ht'⟩ := hmem
  exact ⟨t, ht, ht'⟩

lemma sqRamp_injOn : InjOn sqRamp (Icc (0:ℝ) 1) := sqRamp_strictMonoOn.injOn

lemma sqRamp_eq_zero_iff {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : sqRamp t = 0 ↔ t = 0 :=
  ⟨fun h => sqRamp_injOn ht (left_mem_Icc.mpr zero_le_one) (by rw [h, sqRamp_zero]),
   fun h => by rw [h, sqRamp_zero]⟩

lemma sqRamp_eq_one_iff {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : sqRamp t = 1 ↔ t = 1 :=
  ⟨fun h => sqRamp_injOn ht (right_mem_Icc.mpr zero_le_one) (by rw [h, sqRamp_one]),
   fun h => by rw [h, sqRamp_one]⟩

/-! ## The velocity and the parametrisation -/

/-- The kernel `sqK` cut off at the unit interval (continuous, not differentiable at `0` and `1`). -/
def sqPhi (x : ℝ) : ℝ := if x ∈ Set.Icc (0:ℝ) 1 then sqK x else 0

@[fun_prop]
lemma continuous_sqPhi : Continuous sqPhi := by
  unfold sqPhi
  refine continuous_if (p := fun x : ℝ => x ∈ Set.Icc (0:ℝ) 1) ?_ continuous_sqK.continuousOn
    continuous_const.continuousOn
  intro x hx
  rw [show {x : ℝ | x ∈ Set.Icc (0:ℝ) 1} = Set.Icc (0:ℝ) 1 from Set.ext fun x => Iff.rfl,
    frontier_Icc zero_le_one] at hx
  rcases hx with rfl | rfl
  · norm_num [sqK]
  · norm_num [sqK]

lemma sqPhi_eq {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : sqPhi x = sqK x := by
  simp only [sqPhi, if_pos hx]

lemma sqPhi_eq_zero_of_notMem {x : ℝ} (hx : x ∉ Set.Icc (0:ℝ) 1) : sqPhi x = 0 := by
  simp only [sqPhi, if_neg hx]

lemma sqPhi_lt_zero {x : ℝ} (hx : x < 0) : sqPhi x = 0 :=
  sqPhi_eq_zero_of_notMem (fun h => absurd h.1 (not_le.mpr hx))

lemma sqPhi_gt_one {x : ℝ} (hx : 1 < x) : sqPhi x = 0 :=
  sqPhi_eq_zero_of_notMem (fun h => absurd h.2 (not_le.mpr hx))

lemma sqPhi_zero : sqPhi 0 = 0 := by simp only [sqPhi_eq (by norm_num : (0:ℝ) ∈ Set.Icc 0 1), sqK]; norm_num

lemma sqPhi_one : sqPhi 1 = 0 := by simp only [sqPhi_eq (by norm_num : (1:ℝ) ∈ Set.Icc 0 1), sqK]; norm_num

/-- The `x`-component of the velocity of the square's boundary. -/
def sqVX (u : ℝ) : ℝ := sqPhi (4 * u) - sqPhi (4 * u - 2)

/-- The `y`-component of the velocity of the square's boundary. -/
def sqVY (u : ℝ) : ℝ := sqPhi (4 * u - 1) - sqPhi (4 * u - 3)

/-- The velocity of the square's boundary, supported in `[0,1]`. -/
def sqVel (u : ℝ) : ℝ × ℝ := (sqVX u, sqVY u)

@[fun_prop]
lemma continuous_sqVel : Continuous sqVel := by
  unfold sqVel sqVX sqVY
  fun_prop

lemma sqVel_zero : sqVel 0 = 0 := by
  simp only [sqVel, sqVX, sqVY]
  norm_num
  rw [sqPhi_zero, sqPhi_lt_zero (by norm_num : (-2:ℝ) < 0), sqPhi_lt_zero (by norm_num : (-1:ℝ) < 0),
    sqPhi_lt_zero (by norm_num : (-3:ℝ) < 0)]
  norm_num

lemma sqVel_one : sqVel 1 = 0 := by
  simp only [sqVel, sqVX, sqVY]
  norm_num
  rw [sqPhi_gt_one (by norm_num : (1:ℝ) < 4), sqPhi_gt_one (by norm_num : (1:ℝ) < 2),
    sqPhi_gt_one (by norm_num : (1:ℝ) < 3), sqPhi_one]
  norm_num

lemma sqPhi_le_zero {x : ℝ} (hx : x ≤ 0) : sqPhi x = 0 := by
  rcases lt_or_eq_of_le hx with h | h
  · exact sqPhi_lt_zero h
  · rw [h]; exact sqPhi_zero

lemma sqPhi_ge_one {x : ℝ} (hx : 1 ≤ x) : sqPhi x = 0 := by
  rcases lt_or_eq_of_le hx with h | h
  · exact sqPhi_gt_one h
  · rw [← h]; exact sqPhi_one

/-! ## The velocity on the four edges -/

/-- On the first edge the velocity is `sqK` times the rightward unit vector. -/
lemma sqVel_eq_edge1 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 4) : sqVel u = (sqK (4 * u), 0) := by
  have h5 : (4 * u : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  simp only [sqVel, sqVX, sqVY]
  rw [show sqPhi (4 * u) = sqK (4 * u) from sqPhi_eq h5,
    show sqPhi (4 * u - 2) = 0 from sqPhi_le_zero (by linarith),
    show sqPhi (4 * u - 1) = 0 from sqPhi_le_zero (by linarith),
    show sqPhi (4 * u - 3) = 0 from sqPhi_le_zero (by linarith)]
  simp

/-- On the second edge the velocity is `sqK` times the upward unit vector. -/
lemma sqVel_eq_edge2 {u : ℝ} (h1 : 1 / 4 ≤ u) (h2 : u ≤ 1 / 2) : sqVel u = (0, sqK (4 * u - 1)) := by
  have h5 : (4 * u - 1 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  simp only [sqVel, sqVX, sqVY]
  rw [show sqPhi (4 * u) = 0 from sqPhi_ge_one (by linarith),
    show sqPhi (4 * u - 2) = 0 from sqPhi_le_zero (by linarith),
    show sqPhi (4 * u - 1) = sqK (4 * u - 1) from sqPhi_eq h5,
    show sqPhi (4 * u - 3) = 0 from sqPhi_le_zero (by linarith)]
  simp

/-- On the third edge the velocity is `sqK` times the leftward unit vector. -/
lemma sqVel_eq_edge3 {u : ℝ} (h2 : 1 / 2 ≤ u) (h3 : u ≤ 3 / 4) : sqVel u = (-(sqK (4 * u - 2)), 0) := by
  have h5 : (4 * u - 2 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  simp only [sqVel, sqVX, sqVY]
  rw [show sqPhi (4 * u) = 0 from sqPhi_ge_one (by linarith),
    show sqPhi (4 * u - 2) = sqK (4 * u - 2) from sqPhi_eq h5,
    show sqPhi (4 * u - 1) = 0 from sqPhi_ge_one (by linarith),
    show sqPhi (4 * u - 3) = 0 from sqPhi_le_zero (by linarith)]
  simp

/-- On the fourth edge the velocity is `sqK` times the downward unit vector. -/
lemma sqVel_eq_edge4 {u : ℝ} (h3 : 3 / 4 ≤ u) (h4 : u ≤ 1) : sqVel u = (0, -(sqK (4 * u - 3))) := by
  have h5 : (4 * u - 3 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  simp only [sqVel, sqVX, sqVY]
  rw [show sqPhi (4 * u) = 0 from sqPhi_ge_one (by linarith),
    show sqPhi (4 * u - 2) = 0 from sqPhi_ge_one (by linarith),
    show sqPhi (4 * u - 1) = 0 from sqPhi_ge_one (by linarith),
    show sqPhi (4 * u - 3) = sqK (4 * u - 3) from sqPhi_eq h5]
  simp

/-! ## The periodic velocity and the parametrisation -/

/-- The `1`-periodic velocity of the square's boundary: `sqVel` read on the circle. -/
def sqVelPer (u : UnitAddCircle) : ℝ × ℝ := AddCircle.liftIco 1 0 sqVel u

lemma continuous_sqVelPer : Continuous sqVelPer :=
  AddCircle.liftIco_continuous (by rw [sqVel_zero, zero_add, sqVel_one]) continuous_sqVel.continuousOn

lemma continuous_sqVelPer_coe : Continuous fun x : ℝ => sqVelPer (x : UnitAddCircle) :=
  continuous_sqVelPer.comp (AddCircle.continuous_mk' (1:ℝ))

/-- The parametrisation of the boundary of the unit square: the antiderivative of `sqVelPer`. -/
def sqPar (u : ℝ) : ℝ × ℝ := ∫ x in (0 : ℝ)..u, sqVelPer (x : UnitAddCircle)

lemma sqPar_zero : sqPar 0 = 0 := by simp [sqPar]

lemma hasDerivAt_sqPar (u : ℝ) : HasDerivAt sqPar (sqVelPer (u : UnitAddCircle)) u :=
  intervalIntegral.integral_hasDerivAt_right (continuous_sqVelPer_coe.intervalIntegrable 0 u)
    continuous_sqVelPer_coe.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_sqVelPer_coe.continuousAt

lemma deriv_sqPar (u : ℝ) : deriv sqPar u = sqVelPer (u : UnitAddCircle) :=
  (hasDerivAt_sqPar u).deriv

lemma contDiff_sqPar : ContDiff ℝ 1 sqPar := by
  rw [contDiff_one_iff_deriv]
  exact ⟨fun u => (hasDerivAt_sqPar u).differentiableAt,
    continuous_sqVelPer_coe.congr (fun u => (deriv_sqPar u).symm)⟩


/-! ## The explicit formulas for the parametrisation -/

lemma sqVelPer_coe_eq {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) : sqVelPer (x : UnitAddCircle) = sqVel x :=
  AddCircle.liftIco_coe_apply (a := (0:ℝ)) (p := (1:ℝ)) (by simpa using hx)

lemma sqVelPer_coe_eq' {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : sqVelPer (x : UnitAddCircle) = sqVel x := by
  rcases lt_or_eq_of_le hx.2 with h | h
  · exact sqVelPer_coe_eq ⟨hx.1, h⟩
  · rw [h, sqVel_one]
    rw [AddCircle.coe_period (1:ℝ)]
    exact sqVelPer_coe_eq (x := (0:ℝ)) (by norm_num : (0:ℝ) ∈ Set.Ico 0 1) |>.trans sqVel_zero

lemma integral_pair_eq (f g : ℝ → ℝ) (a b : ℝ) (hf : Continuous f) (hg : Continuous g) :
    ∫ x in a..b, (f x, g x) = (∫ x in a..b, f x, ∫ x in a..b, g x) := by
  have hc : Continuous fun x : ℝ => (f x, g x) := by fun_prop
  have hint : IntervalIntegrable (fun x : ℝ => (f x, g x)) volume a b := hc.intervalIntegrable a b
  refine Prod.ext ?_ ?_
  · exact (ContinuousLinearMap.intervalIntegral_comp_comm (ContinuousLinearMap.fst ℝ ℝ ℝ) hint).symm
  · exact (ContinuousLinearMap.intervalIntegral_comp_comm (ContinuousLinearMap.snd ℝ ℝ ℝ) hint).symm

/-- The derivative of `y ↦ sqRamp (4 y - c)`. -/
lemma hasDerivAt_sqRamp_shift (c x : ℝ) :
    HasDerivAt (fun y : ℝ => sqRamp (4 * y - c)) (sqK (4 * x - c)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 4 * y - c) 4 x := by
    simpa using ((hasDerivAt_id x).const_mul 4).sub_const c
  have h2 := (sqRamp_hasDerivAt (4 * x - c)).comp x h1
  have h2' : HasDerivAt (fun y : ℝ => sqRamp (4 * y - c)) (sqK (4 * x - c) / 4 * 4) x :=
    h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)
  exact h2'.congr_deriv (by ring)

lemma hasDerivAt_neg_sqRamp_shift (c x : ℝ) :
    HasDerivAt (fun y : ℝ => -(sqRamp (4 * y - c))) (-(sqK (4 * x - c))) x := by
  have h := (hasDerivAt_sqRamp_shift c x).neg
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)

lemma continuous_sqK_shift (c : ℝ) : Continuous fun x : ℝ => sqK (4 * x - c) :=
  continuous_sqK.comp (by fun_prop)

lemma integral_sqK_four (u : ℝ) : ∫ x in (0 : ℝ)..u, sqK (4 * x) = sqRamp (4 * u) := by
  have hder : ∀ x ∈ Set.uIcc (0:ℝ) u, HasDerivAt (fun y : ℝ => sqRamp (4 * y - 0)) (sqK (4 * x)) x :=
    fun x _ => by simpa using hasDerivAt_sqRamp_shift 0 x
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((continuous_sqK.comp (by fun_prop : Continuous fun x : ℝ => 4 * x)).intervalIntegrable 0 u)]
  rw [show (4:ℝ) * 0 - 0 = 0 by norm_num, sqRamp_zero, sub_zero]
  simp

lemma integral_sqK_four_sub_one {u : ℝ} :
    ∫ x in (1 / 4 : ℝ)..u, sqK (4 * x - 1) = sqRamp (4 * u - 1) := by
  have hder : ∀ x ∈ Set.uIcc ((1:ℝ)/4) u, HasDerivAt (fun y : ℝ => sqRamp (4 * y - 1)) (sqK (4 * x - 1)) x :=
    fun x _ => hasDerivAt_sqRamp_shift 1 x
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder ((continuous_sqK_shift 1).intervalIntegrable _ _)]
  rw [show (4:ℝ) * ((1:ℝ)/4) - 1 = 0 by norm_num, sqRamp_zero, sub_zero]

lemma integral_sqK_four_sub_two {u : ℝ} :
    ∫ x in (1 / 2 : ℝ)..u, -(sqK (4 * x - 2)) = -(sqRamp (4 * u - 2)) := by
  have hder : ∀ x ∈ Set.uIcc ((1:ℝ)/2) u, HasDerivAt (fun y : ℝ => -(sqRamp (4 * y - 2))) (-(sqK (4 * x - 2))) x :=
    fun x _ => hasDerivAt_neg_sqRamp_shift 2 x
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder ((continuous_sqK_shift 2).neg.intervalIntegrable _ _)]
  rw [show (4:ℝ) * ((1:ℝ)/2) - 2 = 0 by norm_num, sqRamp_zero, neg_zero, sub_zero]

lemma integral_sqK_four_sub_three {u : ℝ} :
    ∫ x in (3 / 4 : ℝ)..u, -(sqK (4 * x - 3)) = -(sqRamp (4 * u - 3)) := by
  have hder : ∀ x ∈ Set.uIcc ((3:ℝ)/4) u, HasDerivAt (fun y : ℝ => -(sqRamp (4 * y - 3))) (-(sqK (4 * x - 3))) x :=
    fun x _ => hasDerivAt_neg_sqRamp_shift 3 x
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder ((continuous_sqK_shift 3).neg.intervalIntegrable _ _)]
  rw [show (4:ℝ) * ((3:ℝ)/4) - 3 = 0 by norm_num, sqRamp_zero, neg_zero, sub_zero]

/-- The parametrisation traverses the first (bottom) edge. -/
lemma sqPar_eq_edge1 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 4) : sqPar u = (sqRamp (4 * u), 0) := by
  have hsub : ∀ x ∈ Set.uIcc (0:ℝ) u, x ∈ Set.Icc (0:ℝ) (1/4) := by
    rw [Set.uIcc_of_le (a := (0:ℝ)) (b := u) h0]
    exact fun x hx => ⟨hx.1, le_trans hx.2 h1⟩
  rw [sqPar, intervalIntegral.integral_congr (fun x hx => ?_)]
  · rw [integral_pair_eq (fun x : ℝ => sqK (4 * x)) (fun _ => 0) 0 u
      ((continuous_sqK.comp (by fun_prop : Continuous fun x : ℝ => 4 * x))) continuous_const,
      integral_sqK_four, intervalIntegral.integral_const]
    simp
  · obtain ⟨hx0, hx1⟩ := hsub x hx
    rw [sqVelPer_coe_eq ⟨hx0, lt_of_le_of_lt hx1 (by norm_num)⟩,
      sqVel_eq_edge1 hx0 hx1]

/-- The parametrisation traverses the second (right) edge. -/
lemma sqPar_eq_edge2 {u : ℝ} (h1 : 1 / 4 ≤ u) (h2 : u ≤ 1 / 2) : sqPar u = (1, sqRamp (4 * u - 1)) := by
  have hsub1 : ∀ x ∈ Set.uIcc (0:ℝ) (1/4), x ∈ Set.Icc (0:ℝ) (1/4) := by
    rw [Set.uIcc_of_le (a := (0:ℝ)) (b := (1:ℝ)/4) (by norm_num)]
    exact fun x hx => hx
  have hsub2 : ∀ x ∈ Set.uIcc ((1:ℝ)/4) u, x ∈ Set.Icc ((1:ℝ)/4) (1/2) := by
    rw [Set.uIcc_of_le (a := (1:ℝ)/4) (b := u) h1]
    exact fun x hx => ⟨hx.1, le_trans hx.2 h2⟩
  have hsplit : sqPar u = (∫ x in (0:ℝ)..(1/4), sqVelPer (x : UnitAddCircle))
      + (∫ x in (1/4:ℝ)..u, sqVelPer (x : UnitAddCircle)) := by
    rw [sqPar]
    exact (intervalIntegral.integral_add_adjacent_intervals
      (continuous_sqVelPer_coe.intervalIntegrable (a := (0:ℝ)) (b := (1:ℝ)/4))
      (continuous_sqVelPer_coe.intervalIntegrable (a := (1:ℝ)/4) (b := u))).symm
  rw [hsplit]
  have e1 : (∫ x in (0:ℝ)..(1/4), sqVelPer (x : UnitAddCircle)) = (1, 0) := by
    rw [intervalIntegral.integral_congr (fun x hx => ?_)]
    · rw [integral_pair_eq (fun x : ℝ => sqK (4 * x)) (fun _ => 0) 0 (1/4)
        ((continuous_sqK.comp (by fun_prop : Continuous fun x : ℝ => 4 * x))) continuous_const,
        integral_sqK_four, intervalIntegral.integral_const]
      norm_num [sqRamp_one]
    · obtain ⟨hx0, hx1⟩ := hsub1 x hx
      rw [sqVelPer_coe_eq ⟨hx0, lt_of_le_of_lt hx1 (by norm_num)⟩, sqVel_eq_edge1 hx0 hx1]
  have e2 : (∫ x in (1/4:ℝ)..u, sqVelPer (x : UnitAddCircle)) = (0, sqRamp (4 * u - 1)) := by
    rw [intervalIntegral.integral_congr (fun x hx => ?_)]
    · rw [integral_pair_eq (fun _ => (0:ℝ)) (fun x : ℝ => sqK (4 * x - 1)) (1/4) u
        continuous_const ((continuous_sqK.comp (by fun_prop : Continuous fun x : ℝ => 4 * x - 1))),
        integral_sqK_four_sub_one, intervalIntegral.integral_const]
      simp
    · obtain ⟨hx0, hx1⟩ := hsub2 x hx
      rw [sqVelPer_coe_eq ⟨le_of_lt (lt_of_lt_of_le (show (0:ℝ) < 1/4 by norm_num) hx0), lt_of_le_of_lt hx1 (by norm_num)⟩,
        sqVel_eq_edge2 hx0 hx1]
  rw [e1, e2]
  norm_num

/-- The parametrisation traverses the third (top) edge. -/
lemma sqPar_eq_edge3 {u : ℝ} (h2 : 1 / 2 ≤ u) (h3 : u ≤ 3 / 4) :
    sqPar u = (1 - sqRamp (4 * u - 2), 1) := by
  have hsub1 : ∀ x ∈ Set.uIcc (0:ℝ) (1/4), x ∈ Set.Icc (0:ℝ) (1/4) := by
    rw [Set.uIcc_of_le (a := (0:ℝ)) (b := (1:ℝ)/4) (by norm_num)]
    exact fun x hx => hx
  have hsub2 : ∀ x ∈ Set.uIcc ((1:ℝ)/4) (1/2), x ∈ Set.Icc ((1:ℝ)/4) (1/2) := by
    rw [Set.uIcc_of_le (a := (1:ℝ)/4) (b := (1:ℝ)/2) (by norm_num)]
    exact fun x hx => hx
  have hsub3 : ∀ x ∈ Set.uIcc ((1:ℝ)/2) u, x ∈ Set.Icc ((1:ℝ)/2) (3/4) := by
    rw [Set.uIcc_of_le (a := (1:ℝ)/2) (b := u) h2]
    exact fun x hx => ⟨hx.1, le_trans hx.2 h3⟩
  have hsplit : sqPar u = ((∫ x in (0:ℝ)..(1/4), sqVelPer (x : UnitAddCircle))
      + (∫ x in (1/4:ℝ)..(1/2), sqVelPer (x : UnitAddCircle)))
      + (∫ x in (1/2:ℝ)..u, sqVelPer (x : UnitAddCircle)) := by
    have hAB : (∫ x in (0:ℝ)..(1/4), sqVelPer (x : UnitAddCircle))
        + (∫ x in (1/4:ℝ)..(1/2), sqVelPer (x : UnitAddCircle))
        = ∫ x in (0:ℝ)..(1/2), sqVelPer (x : UnitAddCircle) :=
      intervalIntegral.integral_add_adjacent_intervals
        (continuous_sqVelPer_coe.intervalIntegrable (a := (0:ℝ)) (b := (1:ℝ)/4))
        (continuous_sqVelPer_coe.intervalIntegrable (a := (1:ℝ)/4) (b := (1:ℝ)/2))
    have hABC : (∫ x in (0:ℝ)..(1/2), sqVelPer (x : UnitAddCircle))
        + (∫ x in (1/2:ℝ)..u, sqVelPer (x : UnitAddCircle))
        = ∫ x in (0:ℝ)..u, sqVelPer (x : UnitAddCircle) :=
      intervalIntegral.integral_add_adjacent_intervals
        (continuous_sqVelPer_coe.intervalIntegrable (a := (0:ℝ)) (b := (1:ℝ)/2))
        (continuous_sqVelPer_coe.intervalIntegrable (a := (1:ℝ)/2) (b := u))
    rw [sqPar, ← hABC, ← hAB]
  rw [hsplit]
  have e1 : (∫ x in (0:ℝ)..(1/4), sqVelPer (x : UnitAddCircle)) = (1, 0) := by
    rw [intervalIntegral.integral_congr (fun x hx => ?_)]
    · rw [integral_pair_eq (fun x : ℝ => sqK (4 * x)) (fun _ => 0) 0 (1/4)
        ((continuous_sqK.comp (by fun_prop : Continuous fun x : ℝ => 4 * x))) continuous_const,
        integral_sqK_four, intervalIntegral.integral_const]
      norm_num [sqRamp_one]
    · obtain ⟨hx0, hx1⟩ := hsub1 x hx
      rw [sqVelPer_coe_eq ⟨hx0, lt_of_le_of_lt hx1 (by norm_num)⟩, sqVel_eq_edge1 hx0 hx1]
  have e2 : (∫ x in (1/4:ℝ)..(1/2), sqVelPer (x : UnitAddCircle)) = (0, 1) := by
    rw [intervalIntegral.integral_congr (fun x hx => ?_)]
    · rw [integral_pair_eq (fun _ => (0:ℝ)) (fun x : ℝ => sqK (4 * x - 1)) (1/4) (1/2)
        continuous_const ((continuous_sqK.comp (by fun_prop : Continuous fun x : ℝ => 4 * x - 1))),
        integral_sqK_four_sub_one, intervalIntegral.integral_const]
      norm_num [sqRamp_one]
    · obtain ⟨hx0, hx1⟩ := hsub2 x hx
      rw [sqVelPer_coe_eq ⟨le_of_lt (lt_of_lt_of_le (show (0:ℝ) < 1/4 by norm_num) hx0), lt_of_le_of_lt hx1 (by norm_num)⟩,
        sqVel_eq_edge2 hx0 hx1]
  have e3 : (∫ x in (1/2:ℝ)..u, sqVelPer (x : UnitAddCircle)) = (-(sqRamp (4 * u - 2)), 0) := by
    rw [intervalIntegral.integral_congr (fun x hx => ?_)]
    · rw [integral_pair_eq (fun x : ℝ => -(sqK (4 * x - 2))) (fun _ => 0) (1/2) u
        ((continuous_sqK.comp (by fun_prop : Continuous fun x : ℝ => 4 * x - 2)).neg) continuous_const,
        integral_sqK_four_sub_two, intervalIntegral.integral_const]
      simp
    · obtain ⟨hx0, hx1⟩ := hsub3 x hx
      rw [sqVelPer_coe_eq ⟨le_of_lt (lt_of_lt_of_le (show (0:ℝ) < 1/4 by norm_num)
          (le_trans (by norm_num : (1:ℝ)/4 ≤ 1/2) hx0)), lt_of_le_of_lt hx1 (by norm_num)⟩,
        sqVel_eq_edge3 hx0 hx1]
  rw [e1, e2, e3]
  norm_num
  ring

/-- The parametrisation traverses the fourth (left) edge. -/
lemma sqPar_eq_edge4 {u : ℝ} (h3 : 3 / 4 ≤ u) (h4 : u ≤ 1) :
    sqPar u = (0, 1 - sqRamp (4 * u - 3)) := by
  have hsub1 : ∀ x ∈ Set.uIcc (0:ℝ) (1/4), x ∈ Set.Icc (0:ℝ) (1/4) := by
    rw [Set.uIcc_of_le (a := (0:ℝ)) (b := (1:ℝ)/4) (by norm_num)]
    exact fun x hx => hx
  have hsub2 : ∀ x ∈ Set.uIcc ((1:ℝ)/4) (1/2), x ∈ Set.Icc ((1:ℝ)/4) (1/2) := by
    rw [Set.uIcc_of_le (a := (1:ℝ)/4) (b := (1:ℝ)/2) (by norm_num)]
    exact fun x hx => hx
  have hsub3 : ∀ x ∈ Set.uIcc ((1:ℝ)/2) (3/4), x ∈ Set.Icc ((1:ℝ)/2) (3/4) := by
    rw [Set.uIcc_of_le (a := (1:ℝ)/2) (b := (3:ℝ)/4) (by norm_num)]
    exact fun x hx => hx
  have hsub4 : ∀ x ∈ Set.uIcc ((3:ℝ)/4) u, x ∈ Set.Icc ((3:ℝ)/4) 1 := by
    rw [Set.uIcc_of_le (a := (3:ℝ)/4) (b := u) h3]
    exact fun x hx => ⟨hx.1, le_trans hx.2 h4⟩
  have hsplit : sqPar u = (((∫ x in (0:ℝ)..(1/4), sqVelPer (x : UnitAddCircle))
      + (∫ x in (1/4:ℝ)..(1/2), sqVelPer (x : UnitAddCircle)))
      + (∫ x in (1/2:ℝ)..(3/4), sqVelPer (x : UnitAddCircle)))
      + (∫ x in (3/4:ℝ)..u, sqVelPer (x : UnitAddCircle)) := by
    have hAB : (∫ x in (0:ℝ)..(1/4), sqVelPer (x : UnitAddCircle))
        + (∫ x in (1/4:ℝ)..(1/2), sqVelPer (x : UnitAddCircle))
        = ∫ x in (0:ℝ)..(1/2), sqVelPer (x : UnitAddCircle) :=
      intervalIntegral.integral_add_adjacent_intervals
        (continuous_sqVelPer_coe.intervalIntegrable (a := (0:ℝ)) (b := (1:ℝ)/4))
        (continuous_sqVelPer_coe.intervalIntegrable (a := (1:ℝ)/4) (b := (1:ℝ)/2))
    have hBC : (∫ x in (0:ℝ)..(1/2), sqVelPer (x : UnitAddCircle))
        + (∫ x in (1/2:ℝ)..(3/4), sqVelPer (x : UnitAddCircle))
        = ∫ x in (0:ℝ)..(3/4), sqVelPer (x : UnitAddCircle) :=
      intervalIntegral.integral_add_adjacent_intervals
        (continuous_sqVelPer_coe.intervalIntegrable (a := (0:ℝ)) (b := (1:ℝ)/2))
        (continuous_sqVelPer_coe.intervalIntegrable (a := (1:ℝ)/2) (b := (3:ℝ)/4))
    have hCD : (∫ x in (0:ℝ)..(3/4), sqVelPer (x : UnitAddCircle))
        + (∫ x in (3/4:ℝ)..u, sqVelPer (x : UnitAddCircle))
        = ∫ x in (0:ℝ)..u, sqVelPer (x : UnitAddCircle) :=
      intervalIntegral.integral_add_adjacent_intervals
        (continuous_sqVelPer_coe.intervalIntegrable (a := (0:ℝ)) (b := (3:ℝ)/4))
        (continuous_sqVelPer_coe.intervalIntegrable (a := (3:ℝ)/4) (b := u))
    rw [sqPar, ← hCD, ← hBC, ← hAB]
  rw [hsplit]
  have e1 : (∫ x in (0:ℝ)..(1/4), sqVelPer (x : UnitAddCircle)) = (1, 0) := by
    rw [intervalIntegral.integral_congr (fun x hx => ?_)]
    · rw [integral_pair_eq (fun x : ℝ => sqK (4 * x)) (fun _ => 0) 0 (1/4)
        ((continuous_sqK.comp (by fun_prop : Continuous fun x : ℝ => 4 * x))) continuous_const,
        integral_sqK_four, intervalIntegral.integral_const]
      norm_num [sqRamp_one]
    · obtain ⟨hx0, hx1⟩ := hsub1 x hx
      rw [sqVelPer_coe_eq ⟨hx0, lt_of_le_of_lt hx1 (by norm_num)⟩, sqVel_eq_edge1 hx0 hx1]
  have e2 : (∫ x in (1/4:ℝ)..(1/2), sqVelPer (x : UnitAddCircle)) = (0, 1) := by
    rw [intervalIntegral.integral_congr (fun x hx => ?_)]
    · rw [integral_pair_eq (fun _ => (0:ℝ)) (fun x : ℝ => sqK (4 * x - 1)) (1/4) (1/2)
        continuous_const ((continuous_sqK.comp (by fun_prop : Continuous fun x : ℝ => 4 * x - 1))),
        integral_sqK_four_sub_one, intervalIntegral.integral_const]
      norm_num [sqRamp_one]
    · obtain ⟨hx0, hx1⟩ := hsub2 x hx
      rw [sqVelPer_coe_eq ⟨le_of_lt (lt_of_lt_of_le (show (0:ℝ) < 1/4 by norm_num) hx0), lt_of_le_of_lt hx1 (by norm_num)⟩,
        sqVel_eq_edge2 hx0 hx1]
  have e3 : (∫ x in (1/2:ℝ)..(3/4), sqVelPer (x : UnitAddCircle)) = (-1, 0) := by
    rw [intervalIntegral.integral_congr (fun x hx => ?_)]
    · rw [integral_pair_eq (fun x : ℝ => -(sqK (4 * x - 2))) (fun _ => 0) (1/2) (3/4)
        ((continuous_sqK.comp (by fun_prop : Continuous fun x : ℝ => 4 * x - 2)).neg) continuous_const,
        integral_sqK_four_sub_two, intervalIntegral.integral_const]
      norm_num [sqRamp_one]
    · obtain ⟨hx0, hx1⟩ := hsub3 x hx
      rw [sqVelPer_coe_eq ⟨le_of_lt (lt_of_lt_of_le (show (0:ℝ) < 1/4 by norm_num)
          (le_trans (by norm_num : (1:ℝ)/4 ≤ 1/2) hx0)), lt_of_le_of_lt hx1 (by norm_num)⟩,
        sqVel_eq_edge3 hx0 hx1]
  have e4 : (∫ x in (3/4:ℝ)..u, sqVelPer (x : UnitAddCircle)) = (0, -(sqRamp (4 * u - 3))) := by
    rw [intervalIntegral.integral_congr (fun x hx => ?_)]
    · rw [integral_pair_eq (fun _ => (0:ℝ)) (fun x : ℝ => -(sqK (4 * x - 3))) (3/4) u
        continuous_const ((continuous_sqK.comp (by fun_prop : Continuous fun x : ℝ => 4 * x - 3)).neg),
        integral_sqK_four_sub_three, intervalIntegral.integral_const]
      simp
    · obtain ⟨hx0, hx1⟩ := hsub4 x hx
      rw [sqVelPer_coe_eq' ⟨le_trans (by norm_num : (0:ℝ) ≤ 3/4) hx0, hx1⟩, sqVel_eq_edge4 hx0 hx1]
  rw [e1, e2, e3, e4]
  norm_num
  ring

/-! ## Periodicity, corners and the bijection onto the boundary -/

lemma integral_sqVelPer_zero : ∫ x in (0:ℝ)..1, sqVelPer (x : UnitAddCircle) = 0 := by
  have h := sqPar_eq_edge4 (u := 1) (by norm_num) (le_refl 1)
  rw [sqPar] at h
  rw [h]
  norm_num [sqRamp_one]

lemma sqPar_add_one (u : ℝ) : sqPar (u + 1) = sqPar u := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => sqVelPer (x : UnitAddCircle)) volume a b :=
    fun a b => continuous_sqVelPer_coe.intervalIntegrable a b
  have hper : Function.Periodic (fun x : ℝ => sqVelPer (x : UnitAddCircle)) 1 := fun x =>
    congrArg sqVelPer (AddCircle.coe_add_period 1 x)
  have hper' : (∫ x in u..u + 1, sqVelPer (x : UnitAddCircle)) = 0 := by
    have h := hper.intervalIntegral_add_eq u 0
    simp only [zero_add] at h
    rw [h, integral_sqVelPer_zero]
  rw [sqPar, sqPar, ← intervalIntegral.integral_add_adjacent_intervals (hint 0 u) (hint u (u+1)),
    hper', add_zero]

lemma sqPar_add_intCast (u : ℝ) (n : ℤ) : sqPar (u + n) = sqPar u := by
  have h1 : ∀ x : ℝ, sqPar (x + 1) = sqPar x := sqPar_add_one
  have h2 : ∀ x : ℝ, sqPar (x - 1) = sqPar x := fun x => by
    simpa using (sqPar_add_one (x - 1)).symm
  have key1 : ∀ m : ℕ, sqPar (u + (m : ℝ)) = sqPar u := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [show u + (((m : ℕ) + 1 : ℕ) : ℝ) = (u + (m : ℝ)) + 1 by push_cast; ring, h1, ih]
  have key2 : ∀ m : ℕ, sqPar (u + (-(m : ℝ))) = sqPar u := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [show u + (-(((m : ℕ) + 1 : ℕ) : ℝ)) = (u + (-(m : ℝ))) - 1 by push_cast; ring, h2, ih]
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hn
    rw [hm]
    exact key1 m
  · obtain ⟨m, hm⟩ := Int.eq_negSucc_of_lt_zero hn
    rw [hm]
    have : ((Int.negSucc m : ℤ) : ℝ) = -(((m : ℕ) + 1 : ℕ) : ℝ) := by push_cast [Int.negSucc]; ring
    rw [this]
    exact key2 (m + 1)

lemma zero_le_sqRamp {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : 0 ≤ sqRamp t := (sqRamp_mem_Icc ht).1

lemma sqRamp_le_one {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : sqRamp t ≤ 1 := (sqRamp_mem_Icc ht).2

lemma sqRamp_pos {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) : 0 < sqRamp t := by
  have h := sqRamp_strictMonoOn (left_mem_Icc.mpr zero_le_one) ⟨le_of_lt h0, h1⟩ h0
  rwa [sqRamp_zero] at h

lemma sqRamp_lt_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : sqRamp t < 1 := by
  have h := sqRamp_strictMonoOn ⟨h0, le_of_lt h1⟩ (right_mem_Icc.mpr zero_le_one) h1
  rwa [sqRamp_one] at h

lemma sqPar_quarter : sqPar (1/4) = (1, 0) := by
  rw [sqPar_eq_edge1 (by norm_num) (le_refl (1/4))]
  norm_num [sqRamp_one]

lemma sqPar_half : sqPar (1/2) = (1, 1) := by
  rw [sqPar_eq_edge2 (by norm_num) (le_refl (1/2))]
  norm_num [sqRamp_one]

lemma sqPar_three_quarter : sqPar (3/4) = (0, 1) := by
  rw [sqPar_eq_edge3 (by norm_num) (le_refl (3/4))]
  norm_num [sqRamp_one]

lemma sqPar_one : sqPar 1 = 0 := by
  rw [sqPar_eq_edge4 (by norm_num) (le_refl 1)]
  norm_num [sqRamp_one]

lemma sqPar_mem_sqBoxBdry (u : ℝ) : sqPar u ∈ Work.Drive.sqBoxBdry := by
  set x := u - (⌊u⌋ : ℝ) with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; exact sub_nonneg.mpr (Int.floor_le u)
  have hx1 : x < 1 := by rw [hxdef]; linarith [Int.lt_floor_add_one u]
  have hper : sqPar u = sqPar x := by
    rw [hxdef]
    conv_lhs => rw [show u = (u - (⌊u⌋ : ℝ)) + (⌊u⌋ : ℝ) by ring]
    exact sqPar_add_intCast (u - (⌊u⌋ : ℝ)) ⌊u⌋
  rw [hper]
  rcases le_or_gt x (1/4) with h | h
  · rw [sqPar_eq_edge1 hx0 h]
    exact ⟨⟨sqRamp_mem_Icc (t := 4 * x) ⟨by linarith, by linarith⟩, ⟨by norm_num, by norm_num⟩⟩,
      Or.inr (Or.inr (Or.inl rfl))⟩
  rcases le_or_gt x (1/2) with h2 | h2
  · rw [sqPar_eq_edge2 (le_of_lt h) h2]
    exact ⟨⟨⟨by norm_num, by norm_num⟩,
      sqRamp_mem_Icc (t := 4 * x - 1) ⟨by linarith, by linarith⟩⟩, Or.inr (Or.inl rfl)⟩
  rcases le_or_gt x (3/4) with h3 | h3
  · rw [sqPar_eq_edge3 (le_of_lt h2) h3]
    exact ⟨⟨⟨sub_nonneg.mpr (sqRamp_le_one (t := 4 * x - 2) ⟨by linarith, by linarith⟩),
      by linarith [(sqRamp_mem_Icc (t := 4 * x - 2) ⟨by linarith, by linarith⟩).1]⟩,
      ⟨by norm_num, by norm_num⟩⟩, Or.inr (Or.inr (Or.inr rfl))⟩
  · rw [sqPar_eq_edge4 (le_of_lt h3) (le_of_lt hx1)]
    exact ⟨⟨⟨by norm_num, by norm_num⟩,
      ⟨sub_nonneg.mpr (sqRamp_le_one (t := 4 * x - 3) ⟨by linarith, by linarith⟩),
      by linarith [(sqRamp_mem_Icc (t := 4 * x - 3) ⟨by linarith, by linarith⟩).1]⟩⟩,
      Or.inl rfl⟩

lemma sqPar_snd_pos {u : ℝ} (h1 : 1/4 < u) (hu : u < 1) : 0 < (sqPar u).2 := by
  rcases le_or_gt u (1/2) with h2 | h2
  · rw [sqPar_eq_edge2 (le_of_lt h1) h2]
    exact sqRamp_pos (by linarith) (by linarith)
  rcases le_or_gt u (3/4) with h3 | h3
  · rw [sqPar_eq_edge3 (le_of_lt h2) h3]
    norm_num
  · rw [sqPar_eq_edge4 (le_of_lt h3) (le_of_lt hu)]
    have := sqRamp_lt_one (show (0:ℝ) ≤ 4*u-3 by linarith) (show 4*u-3 < 1 by linarith)
    linarith

lemma sqPar_snd_eq_zero_iff {u : ℝ} (h0 : 0 ≤ u) (hu : u < 1) : (sqPar u).2 = 0 ↔ u ≤ 1/4 := by
  constructor
  · intro h
    by_contra hc
    exact absurd h (ne_of_gt (sqPar_snd_pos (not_le.mp hc) hu))
  · intro h
    rw [sqPar_eq_edge1 h0 h]

lemma sqPar_fst_eq_one_iff {u : ℝ} (h0 : 0 ≤ u) (hu : u < 1) :
    (sqPar u).1 = 1 ↔ 1/4 ≤ u ∧ u ≤ 1/2 := by
  constructor
  · intro h
    by_cases h1 : u ≤ 1/2
    · refine ⟨?_, h1⟩
      by_contra hc
      have h2 : u < 1/4 := not_le.mp hc
      rw [sqPar_eq_edge1 h0 (le_of_lt h2)] at h
      have h3 : sqRamp (4*u) = 1 := h
      have h4 : 4*u = 1 := (sqRamp_eq_one_iff ⟨by linarith, by linarith⟩).mp h3
      linarith
    · exfalso
      have h2 : 1/2 < u := not_le.mp h1
      rcases le_or_gt u (3/4) with h3 | h3
      · rw [sqPar_eq_edge3 (le_of_lt h2) h3] at h
        have h4 : sqRamp (4*u-2) = 0 := by linarith [h]
        have h5 : 4*u-2 = 0 := (sqRamp_eq_zero_iff ⟨by linarith, by linarith⟩).mp h4
        linarith
      · rw [sqPar_eq_edge4 (le_of_lt h3) (le_of_lt hu)] at h
        exact absurd h (by norm_num)
  · rintro ⟨h1, h2⟩
    rw [sqPar_eq_edge2 h1 h2]

lemma sqPar_snd_eq_one_iff {u : ℝ} (h0 : 0 ≤ u) (hu : u < 1) :
    (sqPar u).2 = 1 ↔ 1/2 ≤ u ∧ u ≤ 3/4 := by
  constructor
  · intro h
    by_cases h1 : u ≤ 3/4
    · refine ⟨?_, h1⟩
      by_contra hc
      have h2 : u < 1/2 := not_le.mp hc
      rcases le_or_gt u (1/4) with h3 | h3
      · rw [sqPar_eq_edge1 h0 h3] at h
        exact absurd h (by norm_num)
      · rw [sqPar_eq_edge2 (le_of_lt h3) (le_of_lt h2)] at h
        have h4 : sqRamp (4*u-1) = 1 := h
        have h5 : 4*u-1 = 1 := (sqRamp_eq_one_iff ⟨by linarith, by linarith⟩).mp h4
        linarith
    · exfalso
      have h2 : 3/4 < u := not_le.mp h1
      rw [sqPar_eq_edge4 (le_of_lt h2) (le_of_lt hu)] at h
      have h4 : sqRamp (4*u-3) = 0 := by linarith [h]
      have h5 : 4*u-3 = 0 := (sqRamp_eq_zero_iff ⟨by linarith, by linarith⟩).mp h4
      linarith
  · rintro ⟨h1, h2⟩
    rw [sqPar_eq_edge3 h1 h2]

lemma sqPar_fst_eq_zero_iff {u : ℝ} (h0 : 0 < u) (hu : u < 1) : (sqPar u).1 = 0 ↔ 3/4 ≤ u := by
  constructor
  · intro h
    by_contra hc
    have h3 : u < 3/4 := not_le.mp hc
    rcases le_or_gt u (1/4) with h1 | h1
    · rw [sqPar_eq_edge1 (le_of_lt h0) h1] at h
      have h4 : sqRamp (4*u) = 0 := h
      have h5 : 4*u = 0 := (sqRamp_eq_zero_iff ⟨by linarith, by linarith⟩).mp h4
      linarith
    rcases le_or_gt u (1/2) with h2 | h2
    · rw [sqPar_eq_edge2 (le_of_lt h1) h2] at h
      exact absurd h (by norm_num)
    · rw [sqPar_eq_edge3 (le_of_lt h2) (le_of_lt h3)] at h
      have h4 : sqRamp (4*u-2) = 1 := by linarith [h]
      have h5 : 4*u-2 = 1 := (sqRamp_eq_one_iff ⟨by linarith, by linarith⟩).mp h4
      linarith
  · intro h
    rw [sqPar_eq_edge4 h (le_of_lt hu)]

theorem sqPar_injOn : Set.InjOn sqPar (Set.Ico (0:ℝ) 1) := by
  intro u hu v hv huv
  have hu0 : 0 ≤ u := hu.1
  have hv0 : 0 ≤ v := hv.1
  by_cases h2 : (sqPar u).2 = 0
  · have hu4 : u ≤ 1/4 := (sqPar_snd_eq_zero_iff hu0 hu.2).mp h2
    have hv4 : v ≤ 1/4 := (sqPar_snd_eq_zero_iff hv0 hv.2).mp (by rw [← huv]; exact h2)
    rw [sqPar_eq_edge1 hu0 hu4, sqPar_eq_edge1 hv0 hv4] at huv
    have h : sqRamp (4*u) = sqRamp (4*v) := congrArg Prod.fst huv
    have h' := sqRamp_injOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h
    linarith
  by_cases h1 : (sqPar u).1 = 1
  · have hu2 : 1/4 ≤ u ∧ u ≤ 1/2 := (sqPar_fst_eq_one_iff hu0 hu.2).mp h1
    have hv2 : 1/4 ≤ v ∧ v ≤ 1/2 := (sqPar_fst_eq_one_iff hv0 hv.2).mp (by rw [← huv]; exact h1)
    rw [sqPar_eq_edge2 hu2.1 hu2.2, sqPar_eq_edge2 hv2.1 hv2.2] at huv
    have h : sqRamp (4*u-1) = sqRamp (4*v-1) := congrArg Prod.snd huv
    have h' := sqRamp_injOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h
    linarith
  by_cases h3 : (sqPar u).2 = 1
  · have hu2 : 1/2 ≤ u ∧ u ≤ 3/4 := (sqPar_snd_eq_one_iff hu0 hu.2).mp h3
    have hv2 : 1/2 ≤ v ∧ v ≤ 3/4 := (sqPar_snd_eq_one_iff hv0 hv.2).mp (by rw [← huv]; exact h3)
    rw [sqPar_eq_edge3 hu2.1 hu2.2, sqPar_eq_edge3 hv2.1 hv2.2] at huv
    have h : sqRamp (4*u-2) = sqRamp (4*v-2) := by
      have := congrArg Prod.fst huv
      linarith [this]
    have h' := sqRamp_injOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h
    linarith
  · have hval : (sqPar u).1 = 0 := by
      have := (sqPar_mem_sqBoxBdry u).2
      rcases this with hh | hh | hh | hh
      · exact hh
      · exact absurd hh h1
      · exact absurd hh h2
      · exact absurd hh h3
    have hu_ne : 0 < u := by
      rcases eq_or_lt_of_le hu0 with h | h
      · exfalso
        have hz : (sqPar u).2 = 0 := by rw [← h, sqPar_zero]; rfl
        exact h2 hz
      · exact h
    have hv_ne : 0 < v := by
      rcases eq_or_lt_of_le hv0 with h | h
      · exfalso
        have hz : (sqPar v).2 = 0 := by rw [← h, sqPar_zero]; rfl
        exact h2 (by rw [huv]; exact hz)
      · exact h
    have hu4 : 3/4 ≤ u := (sqPar_fst_eq_zero_iff hu_ne hu.2).mp hval
    have hv4 : 3/4 ≤ v := (sqPar_fst_eq_zero_iff hv_ne hv.2).mp (by rw [← huv]; exact hval)
    rw [sqPar_eq_edge4 hu4 (le_of_lt hu.2), sqPar_eq_edge4 hv4 (le_of_lt hv.2)] at huv
    have h : sqRamp (4*u-3) = sqRamp (4*v-3) := by
      have := congrArg Prod.snd huv
      linarith [this]
    have h' := sqRamp_injOn (show (4*u-3 : ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨by linarith [hu4], by linarith [hu.2]⟩)
      (show (4*v-3 : ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨by linarith [hv4], by linarith [hv.2]⟩) h
    linarith

lemma one_sub_mem_Icc {x : ℝ} (h : x ∈ Set.Icc (0:ℝ) 1) : 1 - x ∈ Set.Icc (0:ℝ) 1 :=
  ⟨by linarith [h.2], by linarith [h.1]⟩

lemma quarter_mem_Icc0 {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    t / 4 ∈ Set.Icc (0:ℝ) (1/4) := ⟨by linarith [ht.1], by linarith [ht.2]⟩

lemma quarter_mem_Icc1 {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (1 + t) / 4 ∈ Set.Icc ((1:ℝ)/4) (1/2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩

lemma quarter_mem_Icc2 {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (2 + t) / 4 ∈ Set.Icc ((1:ℝ)/2) (3/4) := ⟨by linarith [ht.1], by linarith [ht.2]⟩

lemma quarter_mem_Icc3 {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (3 + t) / 4 ∈ Set.Icc ((3:ℝ)/4) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem sqPar_surjOn : Work.Drive.sqBoxBdry ⊆ sqPar '' Set.Ico (0:ℝ) 1 := by
  rintro ⟨x1, x2⟩ ⟨⟨hx1, hx2⟩, hb⟩
  have hx1' : x1 ∈ Set.Icc (0:ℝ) 1 := hx1
  have hx2' : x2 ∈ Set.Icc (0:ℝ) 1 := hx2
  have hx0 : (0:ℝ) ≤ x1 := hx1'.1
  have hx1u : x1 ≤ 1 := hx1'.2
  have hx0' : (0:ℝ) ≤ x2 := hx2'.1
  have hx2u : x2 ≤ 1 := hx2'.2
  rcases hb with h | h | h | h
  · -- x1 = 0 : the fourth edge
    rcases eq_or_lt_of_le hx0' with h2 | h2
    · exact ⟨0, by norm_num, by rw [sqPar_zero]; exact Prod.ext h.symm h2⟩
    · obtain ⟨t, ht, ht'⟩ := sqRamp_surjOn (y := 1 - x2) (one_sub_mem_Icc hx2')
      have ht1 : t < 1 := by
        by_contra hc
        rw [not_lt] at hc
        rw [le_antisymm ht.2 hc, sqRamp_one] at ht'
        linarith
      have hq := quarter_mem_Icc3 ht
      refine ⟨(3 + t)/4, ⟨by linarith [hq.1], by linarith [ht.2]⟩, ?_⟩
      rw [sqPar_eq_edge4 hq.1 hq.2]
      have h4 : 4 * ((3 + t)/4) - 3 = t := by ring
      rw [h4, ht']
      exact Prod.ext h.symm (by linarith)
  · -- x1 = 1 : the second edge
    rcases eq_or_lt_of_le hx0' with h2 | h2
    · exact ⟨1/4, by norm_num, by rw [sqPar_quarter]; exact Prod.ext h.symm h2⟩
    · obtain ⟨t, ht, ht'⟩ := sqRamp_surjOn (y := x2) hx2'
      have hq := quarter_mem_Icc1 ht
      refine ⟨(1 + t)/4, ⟨by linarith [hq.1], by linarith [ht.2]⟩, ?_⟩
      rw [sqPar_eq_edge2 hq.1 hq.2]
      have h4 : 4 * ((1 + t)/4) - 1 = t := by ring
      rw [h4, ht']
      exact Prod.ext h.symm rfl
  · -- x2 = 0 : the first edge
    obtain ⟨t, ht, ht'⟩ := sqRamp_surjOn (y := x1) hx1'
    have hq := quarter_mem_Icc0 ht
    refine ⟨t/4, ⟨by linarith [hq.1], by linarith [hq.2]⟩, ?_⟩
    rw [sqPar_eq_edge1 hq.1 hq.2]
    have h4 : 4 * (t/4) = t := by ring
    rw [h4, ht']
    exact Prod.ext rfl h.symm
  · -- x2 = 1 : the third edge
    obtain ⟨t, ht, ht'⟩ := sqRamp_surjOn (y := 1 - x1) (one_sub_mem_Icc hx1')
    have hq := quarter_mem_Icc2 ht
    refine ⟨(2 + t)/4, ⟨by linarith [hq.1], by linarith [ht.2]⟩, ?_⟩
    rw [sqPar_eq_edge3 hq.1 hq.2]
    have h4 : 4 * ((2 + t)/4) - 2 = t := by ring
    rw [h4, ht']
    exact Prod.ext (by linarith) h.symm

theorem sqPar_corner_data {u : ℝ} (hu : u ∈ Set.Ico (0:ℝ) 1) :
    (sqPar u = (0,0) ↔ u = 0) ∧ (sqPar u = (1,0) ↔ u = 1/4) ∧
    (sqPar u = (1,1) ↔ u = 1/2) ∧ (sqPar u = (0,1) ↔ u = 3/4) := by
  have h0 : 0 ≤ u := hu.1
  have hu1 : u < 1 := hu.2
  have hz1 : sqPar u = (0,0) → u = 0 := by
    intro h
    have h2 : (sqPar u).2 = 0 := by rw [h]
    have h4 : u ≤ 1/4 := (sqPar_snd_eq_zero_iff h0 hu1).mp h2
    rw [sqPar_eq_edge1 h0 h4] at h
    have h5 : sqRamp (4*u) = 0 := congrArg Prod.fst h
    have h6 : 4*u = 0 := (sqRamp_eq_zero_iff ⟨by linarith, by linarith⟩).mp h5
    linarith
  refine ⟨⟨hz1, fun h => by rw [h, sqPar_zero]; rfl⟩, ?_, ?_, ?_⟩
  · refine ⟨fun h => ?_, fun h => by rw [h, sqPar_quarter]⟩
    have h1 : (sqPar u).1 = 1 := by rw [h]
    have hu2 := (sqPar_fst_eq_one_iff h0 hu1).mp h1
    rw [sqPar_eq_edge2 hu2.1 hu2.2] at h
    have h5 : sqRamp (4*u-1) = 0 := congrArg Prod.snd h
    have h6 : 4*u-1 = 0 := (sqRamp_eq_zero_iff ⟨by linarith, by linarith⟩).mp h5
    linarith
  · refine ⟨fun h => ?_, fun h => by rw [h, sqPar_half]⟩
    have h1 : (sqPar u).2 = 1 := by rw [h]
    have hu2 := (sqPar_snd_eq_one_iff h0 hu1).mp h1
    rw [sqPar_eq_edge3 hu2.1 hu2.2] at h
    have h5 : sqRamp (4*u-2) = 0 := by
      have := congrArg Prod.fst h; linarith [this]
    have h6 : 4*u-2 = 0 := (sqRamp_eq_zero_iff ⟨by linarith, by linarith⟩).mp h5
    linarith
  · refine ⟨fun h => ?_, fun h => by rw [h]; exact sqPar_three_quarter⟩
    have h1 : (sqPar u).1 = 0 := by rw [h]
    have h2' : (sqPar u).2 = 1 := by rw [h]
    have hu_ne : 0 < u := by
      rcases eq_or_lt_of_le h0 with hh | hh
      · exfalso
        rw [← hh, sqPar_zero] at h2'
        exact absurd h2' (by norm_num)
      · exact hh
    have h4 : 3/4 ≤ u := (sqPar_fst_eq_zero_iff hu_ne hu1).mp h1
    rw [sqPar_eq_edge4 h4 (le_of_lt hu1)] at h
    have hz : 1 - sqRamp (4*u-3) = 1 := congrArg Prod.snd h
    have h5 : sqRamp (4*u-3) = 0 := by linarith
    have h6 : 4*u-3 = 0 := (sqRamp_eq_zero_iff ⟨by linarith [h4], by linarith [hu1]⟩).mp h5
    linarith


end

end Work.Surf
