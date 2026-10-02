import Mathlib
import Submission.Work.StemsB.SphLoopRelPair
import Submission.Work.StemsB.bundlePullback_homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The standard ball, its cover by two thick half-balls, and the pieces

For the sphere-specific computation of the rational homology of the loop space of a sphere
(`CONTRACTS.md` §F, Step I) one recurses on the dimension using the cover of the closed unit ball
`B^j ⊆ ℝ^{j+1}` by the two "thick half-balls"

  `U = {x : x_j > -1/4}` ,  `V = {x : x_j < 1/4}`

whose intersection `B^j ∩ {|x_j| < 1/4}` is, through an explicit homeomorphism, the product
`B^{j-1} × (-1/4,1/4)`, and whose parts of the boundary sphere are mapped to `S^{j-2} × (-1/4,1/4)`.

This file sets up the cover and the pieces, together with their convexity (hence contractibility).
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.StemsB

noncomputable section

/-- The closed unit ball in `ℝ^{j+1}`. -/
abbrev ballSet (j : ℕ) : Set (EuclideanSpace ℝ (Fin (j+1))) := Metric.closedBall 0 1

/-- The closed unit ball in `ℝ^{j+1}`, as a type. -/
abbrev Ball (j : ℕ) : Type := ↥(ballSet j)

/-- The unit sphere in `ℝ^{j+1}`. -/
abbrev sphJ (j : ℕ) : Set (EuclideanSpace ℝ (Fin (j+1))) := Metric.sphere 0 1

/-- The first standard basis vector of `ℝ^{j+1}`. -/
def evec (j : ℕ) : EuclideanSpace ℝ (Fin (j+1)) :=
  (WithLp.equiv 2 (Fin (j+1) → ℝ)).symm (Pi.single 0 1)

theorem evec_ofLp (j : ℕ) (i : Fin (j+1)) : (evec j).ofLp i = if i = 0 then 1 else 0 := by
  simp [evec]

theorem norm_evec (j : ℕ) : ‖evec j‖ = 1 := by
  simp [evec]

theorem ballSet_convex (j : ℕ) : Convex ℝ (ballSet j) := convex_closedBall 0 1

/-- The last coordinate functional on `ℝ^{j+1}`. -/
def lastCoord (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) : ℝ := x.ofLp ⟨j, Nat.lt_succ_self j⟩

theorem continuous_lastCoord (j : ℕ) : Continuous (lastCoord j) :=
  PiLp.continuous_apply 2 (fun _ : Fin (j+1) => ℝ) ⟨j, Nat.lt_succ_self j⟩

theorem isLinearMap_lastCoord (j : ℕ) : IsLinearMap ℝ (lastCoord j) where
  map_add a b := by simp [lastCoord]
  map_smul c a := by simp [lastCoord]

/-- The first "thick half-ball" `B^j ∩ {x_j > -1/4}`. -/
def halfU (j : ℕ) : Set (EuclideanSpace ℝ (Fin (j+1))) :=
  ballSet j ∩ {x | -1/4 < lastCoord j x}

/-- The second "thick half-ball" `B^j ∩ {x_j < 1/4}`. -/
def halfV (j : ℕ) : Set (EuclideanSpace ℝ (Fin (j+1))) :=
  ballSet j ∩ {x | lastCoord j x < 1/4}

theorem halfU_convex (j : ℕ) : Convex ℝ (halfU j) :=
  (ballSet_convex j).inter (convex_halfSpace_gt (isLinearMap_lastCoord j) (-1/4))

theorem halfV_convex (j : ℕ) : Convex ℝ (halfV j) :=
  (ballSet_convex j).inter (convex_halfSpace_lt (isLinearMap_lastCoord j) (1/4))

theorem evec_mem_halfU (j : ℕ) : evec j ∈ halfU j := by
  refine ⟨?_, ?_⟩
  · simp [ballSet, Metric.mem_closedBall, dist_zero_right, norm_evec]
  · show (-1/4 : ℝ) < (evec j).ofLp ⟨j, Nat.lt_succ_self j⟩
    rw [evec_ofLp]
    by_cases h : (⟨j, Nat.lt_succ_self j⟩ : Fin (j+1)) = 0
    · rw [if_pos h]; norm_num
    · rw [if_neg h]; norm_num

theorem evec_mem_halfV (j : ℕ) (hj : 0 < j) : evec j ∈ halfV j := by
  refine ⟨?_, ?_⟩
  · simp [ballSet, Metric.mem_closedBall, dist_zero_right, norm_evec]
  · show (evec j).ofLp ⟨j, Nat.lt_succ_self j⟩ < (1/4 : ℝ)
    rw [evec_ofLp]
    by_cases h : (⟨j, Nat.lt_succ_self j⟩ : Fin (j+1)) = 0
    · have h0 : j = 0 := Fin.ext_iff.mp h
      omega
    · rw [if_neg h]; norm_num

theorem halfU_contractible (j : ℕ) : ContractibleSpace ↥(halfU j) :=
  Convex.contractibleSpace (halfU_convex j) ⟨evec j, evec_mem_halfU j⟩

theorem halfV_contractible (j : ℕ) (hj : 0 < j) : ContractibleSpace ↥(halfV j) :=
  Convex.contractibleSpace (halfV_convex j) ⟨evec j, evec_mem_halfV j hj⟩

/-- The first half-ball as a subset of the ball. -/
def BallU (j : ℕ) : Set (Ball j) := {x | (x : EuclideanSpace ℝ (Fin (j+1))) ∈ halfU j}

/-- The second half-ball as a subset of the ball. -/
def BallV (j : ℕ) : Set (Ball j) := {x | (x : EuclideanSpace ℝ (Fin (j+1))) ∈ halfV j}

/-- The boundary of the ball. -/
def bdry (j : ℕ) : Set (Ball j) := {x | (x : EuclideanSpace ℝ (Fin (j+1))) ∈ sphJ j}

/-- Identification of a subtype of a subtype with the corresponding ambient subset. -/
def subtypeHomeo {α : Type*} [TopologicalSpace α] {s : Set α} {t : Set ↥s} {w : Set α}
    (hw : w ⊆ s) (h : ∀ x : ↥s, x ∈ t ↔ (x : α) ∈ w) : ↥t ≃ₜ ↥w where
  toFun x := ⟨x.1.1, (h x.1).mp x.2⟩
  invFun y := ⟨⟨y.1, hw y.2⟩, (h ⟨y.1, hw y.2⟩).mpr y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val _) _

theorem BallU_mem (j : ℕ) (x : ↥(BallU j)) : (x.1 : EuclideanSpace ℝ (Fin (j+1))) ∈ halfU j :=
  x.2

/-- The first half-ball, as a subset of the ball, is contractible. -/
theorem BallU_contractible (j : ℕ) : ContractibleSpace ↥(BallU j) := by
  have h := subtypeHomeo (α := EuclideanSpace ℝ (Fin (j+1))) (s := ballSet j)
    (t := BallU j) (w := halfU j) (fun x hx => hx.1) (fun x => Iff.rfl)
  exact h.contractibleSpace_iff.mpr (halfU_contractible j)

/-- The second half-ball, as a subset of the ball, is contractible. -/
theorem BallV_contractible (j : ℕ) (hj : 0 < j) : ContractibleSpace ↥(BallV j) := by
  have h := subtypeHomeo (α := EuclideanSpace ℝ (Fin (j+1))) (s := ballSet j)
    (t := BallV j) (w := halfV j) (fun x hx => hx.1) (fun x => Iff.rfl)
  exact h.contractibleSpace_iff.mpr (halfV_contractible j hj)

/-! ## The poles and the geodesic segment to the pole -/

/-- The `j`-th ("last") standard basis vector of `ℝ^{j+1}`: the north pole of `S^j`. -/
def npole (j : ℕ) : EuclideanSpace ℝ (Fin (j+1)) :=
  (WithLp.equiv 2 (Fin (j+1) → ℝ)).symm (fun i => if i = Fin.last j then (1:ℝ) else 0)

/-- The south pole of `S^j`. -/
def spole (j : ℕ) : EuclideanSpace ℝ (Fin (j+1)) := -npole j

theorem npole_ofLp (j : ℕ) (i : Fin (j+1)) :
    (npole j).ofLp i = if i = Fin.last j then 1 else 0 := by
  simp [npole]

theorem norm_npole (j : ℕ) : ‖npole j‖ = 1 := by
  rw [PiLp.norm_eq_of_L2]; simp [npole]

theorem norm_spole (j : ℕ) : ‖spole j‖ = 1 := by
  rw [spole, norm_neg, norm_npole]

theorem inner_npole (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) :
    inner ℝ x (npole j) = lastCoord j x := by
  rw [PiLp.inner_apply, lastCoord]
  simp only [npole_ofLp]
  rw [show (∑ i, inner ℝ (x.ofLp i) (if i = Fin.last j then (1:ℝ) else 0)) =
      x.ofLp (Fin.last j) by
    simp [Finset.sum_ite_eq', Finset.mem_univ]]
  rfl

theorem inner_spole (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) :
    inner ℝ x (spole j) = -lastCoord j x := by
  rw [spole, inner_neg_right, inner_npole]

/-- The squared norm of the point of the segment from `x` (with `‖x‖ = 1`) to the pole. -/
theorem norm_sq_segment (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (hx : ‖x‖ = 1) (t : ℝ) :
    ‖(1 - t) • x + t • npole j‖ ^ 2 =
      (1 - t) ^ 2 + t ^ 2 + 2 * t * (1 - t) * lastCoord j x := by
  have hN := norm_npole j
  have hinner := inner_npole j x
  have h1 : ‖(1 - t) • x‖ ^ 2 = (1 - t) ^ 2 := by
    rw [norm_smul, hx, mul_one, Real.norm_eq_abs, sq_abs]
  have h2 : ‖t • npole j‖ ^ 2 = t ^ 2 := by
    rw [norm_smul, hN, mul_one, Real.norm_eq_abs, sq_abs]
  rw [norm_add_sq_real, h1, h2, real_inner_smul_left, real_inner_smul_right, hinner]
  ring

theorem norm_sq_segment_spole (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (hx : ‖x‖ = 1)
    (t : ℝ) :
    ‖(1 - t) • x + t • spole j‖ ^ 2 =
      (1 - t) ^ 2 + t ^ 2 - 2 * t * (1 - t) * lastCoord j x := by
  have hN := norm_spole j
  have hinner := inner_spole j x
  have h1 : ‖(1 - t) • x‖ ^ 2 = (1 - t) ^ 2 := by
    rw [norm_smul, hx, mul_one, Real.norm_eq_abs, sq_abs]
  have h2 : ‖t • spole j‖ ^ 2 = t ^ 2 := by
    rw [norm_smul, hN, mul_one, Real.norm_eq_abs, sq_abs]
  rw [norm_add_sq_real, h1, h2, real_inner_smul_left, real_inner_smul_right, hinner]
  ring

/-- Uniform lower bound for the norm of the segment to the north pole over the piece
`{x_j > -1/4}` of the sphere. -/
theorem segment_norm_sq_lower (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (hx : ‖x‖ = 1)
    (hxj : -1/4 < lastCoord j x) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    3/8 ≤ ‖(1 - t) • x + t • npole j‖ ^ 2 := by
  rw [norm_sq_segment j x hx t]
  have hnn : (0:ℝ) ≤ 2*t*(1-t) := by nlinarith [ht0, ht1]
  have hb : 2*t*(1-t)*(-1/4) ≤ 2*t*(1-t)*lastCoord j x :=
    mul_le_mul_of_nonneg_left hxj.le hnn
  nlinarith [sq_nonneg (t - 1/2), hb]

/-- Uniform lower bound for the norm of the segment to the south pole over the piece
`{x_j < 1/4}` of the sphere. -/
theorem segment_norm_sq_lower_spole (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (hx : ‖x‖ = 1)
    (hxj : lastCoord j x < 1/4) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    3/8 ≤ ‖(1 - t) • x + t • spole j‖ ^ 2 := by
  rw [norm_sq_segment_spole j x hx t]
  have hnn : (0:ℝ) ≤ 2*t*(1-t) := by nlinarith [ht0, ht1]
  have hb : 2*t*(1-t)*(-1/4) ≤ 2*t*(1-t)*(-lastCoord j x) :=
    mul_le_mul_of_nonneg_left (by linarith) hnn
  nlinarith [sq_nonneg (t - 1/2), hb]

theorem segment_ofLp (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (t : ℝ) (i : Fin (j+1)) :
    ((1 - t) • x + t • npole j).ofLp i =
      (1 - t) * x.ofLp i + t * (if i = Fin.last j then (1:ℝ) else 0) := by
  simp [npole]

theorem segment_ofLp_spole (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (t : ℝ)
    (i : Fin (j+1)) :
    ((1 - t) • x + t • spole j).ofLp i =
      (1 - t) * x.ofLp i - t * (if i = Fin.last j then (1:ℝ) else 0) := by
  by_cases h : i = Fin.last j <;> simp [spole, npole, h] <;> ring

theorem normalized_ofLp (j : ℕ) (a : EuclideanSpace ℝ (Fin (j+1))) (i : Fin (j+1)) :
    (((‖a‖)⁻¹ : ℝ) • a).ofLp i = a.ofLp i / ‖a‖ := by
  rw [PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul]

theorem norm_normalized (j : ℕ) (a : EuclideanSpace ℝ (Fin (j+1))) (ha : a ≠ 0) :
    ‖(((‖a‖)⁻¹ : ℝ) • a)‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg a),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]

/-! ## Coordinate bounds and the exact squared-norm identity for the segment -/

theorem sq_lastCoord_le_one (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (hx : ‖x‖ = 1) :
    (lastCoord j x) ^ 2 ≤ 1 := by
  have h1 : (lastCoord j x) ^ 2 ≤ ∑ i, (x.ofLp i) ^ 2 :=
    Finset.single_le_sum (f := fun i => (x.ofLp i) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ (Fin.last j))
  have h2 : ∑ i, (x.ofLp i) ^ 2 = ‖x‖ ^ 2 := by
    rw [PiLp.norm_eq_of_L2, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
    simp [Real.norm_eq_abs, sq_abs]
  rw [h2, hx] at h1
  simpa using h1

/-- The exact identity `s = (segment coordinate)^2 + (1-t)^2 (1 - x_j^2)` for the squared norm
of the segment from `x` (with `‖x‖ = 1`) to the pole. -/
theorem norm_sq_segment_eq (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (hx : ‖x‖ = 1) (t : ℝ) :
    ‖(1 - t) • x + t • npole j‖ ^ 2 =
      ((1 - t) * lastCoord j x + t) ^ 2 + (1 - t) ^ 2 * (1 - (lastCoord j x) ^ 2) := by
  rw [norm_sq_segment j x hx t]; ring

/-- The key inequality: on the piece `{x_j > -1/4}`, when the `j`-coordinate of the segment is
negative, the "horizontal" part dominates it by a factor `15`. -/
theorem seg_horizontal_dominates (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (hx : ‖x‖ = 1)
    (hxj : -1/4 < lastCoord j x) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : (1 - t) * lastCoord j x + t ≤ 0) :
    15 * ((1 - t) * lastCoord j x + t) ^ 2 ≤ (1 - t) ^ 2 * (1 - (lastCoord j x) ^ 2) := by
  have hle : 1 - (lastCoord j x) ^ 2 ≥ 0 := by linarith [sq_lastCoord_le_one j x hx]
  nlinarith [sq_nonneg ((1-t)*lastCoord j x + t), sq_nonneg (1-t),
    sq_nonneg (1 + lastCoord j x), sq_nonneg (lastCoord j x), hle,
    mul_nonneg ht0 (sub_nonneg.mpr ht1), hxj]

/-- Strict form of `seg_horizontal_dominates`. -/
theorem seg_horizontal_dominates_strict (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1)))
    (hx : ‖x‖ = 1) (hxj : -1/4 < lastCoord j x) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : (1 - t) * lastCoord j x + t ≤ 0) :
    15 * ((1 - t) * lastCoord j x + t) ^ 2 < (1 - t) ^ 2 * (1 - (lastCoord j x) ^ 2) := by
  have hle : 1 - (lastCoord j x) ^ 2 ≥ 0 := by linarith [sq_lastCoord_le_one j x hx]
  nlinarith [sq_nonneg ((1-t)*lastCoord j x + t), sq_nonneg (1-t),
    sq_nonneg (1 + lastCoord j x), sq_nonneg (lastCoord j x), hle,
    mul_nonneg ht0 (sub_nonneg.mpr ht1), sq_nonneg (t - 1/2), sq_nonneg (1 - lastCoord j x)]

/-! ## The geodesic contraction of the sphere pieces -/

/-- The piece `{x ∈ S^j : x_j > -1/4}` of the sphere. -/
def sphPieceUp (j : ℕ) : Set (EuclideanSpace ℝ (Fin (j+1))) :=
  sphJ j ∩ {x | -1/4 < lastCoord j x}

/-- The piece `{x ∈ S^j : x_j < 1/4}` of the sphere. -/
def sphPieceDn (j : ℕ) : Set (EuclideanSpace ℝ (Fin (j+1))) :=
  sphJ j ∩ {x | lastCoord j x < 1/4}

/-- The `t`-th point of the geodesic from `x` to the north pole, renormalised to the sphere. -/
def segPoint (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (t : ℝ) :
    EuclideanSpace ℝ (Fin (j+1)) :=
  ((‖(1 - t) • x + t • npole j‖)⁻¹ : ℝ) • ((1 - t) • x + t • npole j)

theorem segPoint_ofLp (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (t : ℝ) (i : Fin (j+1)) :
    (segPoint j x t).ofLp i = ((1 - t) • x + t • npole j).ofLp i /
      ‖(1 - t) • x + t • npole j‖ :=
  normalized_ofLp j _ i

theorem segPoint_lastCoord (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (t : ℝ) :
    lastCoord j (segPoint j x t) =
      ((1 - t) * lastCoord j x + t) / ‖(1 - t) • x + t • npole j‖ := by
  rw [lastCoord, segPoint_ofLp, segment_ofLp]
  simp only [Fin.last, ↓reduceIte, mul_one]
  rfl

theorem segNorm_pos (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (hx : ‖x‖ = 1)
    (hxj : -1/4 < lastCoord j x) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < ‖(1 - t) • x + t • npole j‖ := by
  have h := segment_norm_sq_lower j x hx hxj t ht0 ht1
  nlinarith [norm_nonneg ((1 - t) • x + t • npole j)]

theorem segPoint_mem_sphJ (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (hx : ‖x‖ = 1)
    (hxj : -1/4 < lastCoord j x) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segPoint j x t ∈ sphJ j := by
  rw [sphJ, Metric.mem_sphere, dist_zero_right]
  exact norm_normalized j _ (norm_pos_iff.mp (segNorm_pos j x hx hxj t ht0 ht1))

theorem segPoint_coord_gt (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (hx : ‖x‖ = 1)
    (hxj : -1/4 < lastCoord j x) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    -1/4 < lastCoord j (segPoint j x t) := by
  have hpos := segNorm_pos j x hx hxj t ht0 ht1
  rw [segPoint_lastCoord]
  rcases lt_or_ge 0 ((1 - t) * lastCoord j x + t) with hu | hu
  · have := div_pos hu hpos
    linarith
  · have hw := seg_horizontal_dominates_strict j x hx hxj t ht0 ht1 hu
    have hsq : ‖(1 - t) • x + t • npole j‖ ^ 2 >
        16 * ((1 - t) * lastCoord j x + t) ^ 2 := by
      rw [norm_sq_segment_eq j x hx t]; linarith
    set u := (1 - t) * lastCoord j x + t with hudef
    have hnorm : ‖(1 - t) • x + t • npole j‖ > 4 * |u| := by
      have h4 : (4 * |u|) ^ 2 < ‖(1 - t) • x + t • npole j‖ ^ 2 := by
        rw [mul_pow, sq_abs]; linarith
      nlinarith [norm_nonneg ((1 - t) • x + t • npole j), abs_nonneg u]
    rw [abs_of_nonpos hu] at hnorm
    have h2 : -1/4 * ‖(1 - t) • x + t • npole j‖ < u := by linarith
    have h3 : (-1/4 * ‖(1 - t) • x + t • npole j‖) *
        (‖(1 - t) • x + t • npole j‖)⁻¹ <
        u * (‖(1 - t) • x + t • npole j‖)⁻¹ :=
      mul_lt_mul_of_pos_right h2 (inv_pos.mpr hpos)
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), mul_one] at h3
    rwa [div_eq_mul_inv]

theorem segPoint_zero (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) (hx : ‖x‖ = 1) :
    segPoint j x 0 = x := by
  have h1 : (1 - (0:ℝ)) • x + (0:ℝ) • npole j = x := by simp
  rw [segPoint, h1, hx]
  simp

theorem segPoint_one (j : ℕ) (x : EuclideanSpace ℝ (Fin (j+1))) :
    segPoint j x 1 = npole j := by
  have h1 : (1 - (1:ℝ)) • x + (1:ℝ) • npole j = npole j := by simp
  rw [segPoint, h1, norm_npole]
  simp

theorem segPoint_pole (j : ℕ) (t : ℝ) : segPoint j (npole j) t = npole j := by
  have : (1 - t) • npole j + t • npole j = npole j := by
    rw [← add_smul]
    norm_num
  rw [segPoint, this, norm_npole]
  simp

end

end Work.StemsB
