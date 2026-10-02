import Mathlib
import Submission.Work.CharacteristicClasses.Invariants

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The power maps `q ↦ qᵐ` on `S³`, and their degrees

The bundles `L^a R^b` over `S⁴` of `Submission/NOTES.md` §9.1 have spin decomposition
`(L^a, R^b)` with clutching functions `q ↦ q^a` and `q ↦ q^{-b}`: integer powers of a unit
quaternion.  This file provides the continuous maps `s3NatPowCm n` (`q ↦ qⁿ`, `n : ℕ`) and
`s3ZPowCm m` (`q ↦ qᵐ`, `m : ℤ`), together with the computation of their degrees,

* `chern2_natPowCm` : `chern2 (q ↦ qⁿ) = n`,
* `chern2_zPowCm`  : `chern2 (q ↦ qᵐ) = m`,

which is the general form of `chern2_sq` (`m = 2`) and `chern2_inv` (`m = -1`).  The proof is the
H-space induction: `q^(n+1) = qⁿ · q` pointwise, so `chern2_mul` (the Hopf formula) gives
`chern2 (q ↦ qⁿ⁺¹) = chern2 (q ↦ qⁿ) + 1`.

With these, the framework computes the full family `p₁(L^aR^b) = 2(a-b)`, `e(L^aR^b) = a+b` of
`Submission/NOTES.md` §9.1; see `Submission/Work/CharacteristicClasses/Family.lean`.
-/

namespace Work.CharacteristicClasses

open scoped Topology

noncomputable section

/-- `star x = x⁻¹` for unit quaternions (the conjugate is the inverse). -/
lemma star_eq_inv_of_s3 (x : S3) : star (x : Quaternion ℝ) = ((x : Quaternion ℝ))⁻¹ := by
  have hx : (x : Quaternion ℝ) ≠ 0 := by
    intro h
    have h1 := Submission.Milnor.norm_coe x
    rw [h, norm_zero] at h1
    norm_num at h1
  have h : (x : Quaternion ℝ) * star (x : Quaternion ℝ) = 1 := by
    have h2 := s3Mul_inv x
    simpa using congrArg (fun z : S3 => (z : Quaternion ℝ)) h2
  exact (inv_eq_of_mul_eq_one_right h).symm

/-- The `n`-th power map `q ↦ qⁿ` on `S³`, as a continuous map. -/
def s3NatPowCm : ℕ → C(S3, S3)
  | 0 => s3OneCm
  | n + 1 => s3MulCm (s3NatPowCm n) (ContinuousMap.id S3)

@[simp] lemma s3NatPowCm_zero : s3NatPowCm 0 = s3OneCm := rfl

@[simp] lemma s3NatPowCm_succ (n : ℕ) :
    s3NatPowCm (n + 1) = s3MulCm (s3NatPowCm n) (ContinuousMap.id S3) := rfl

/-- The underlying quaternionic formula for the power maps. -/
lemma s3NatPowCm_coe (n : ℕ) (q : S3) :
    ((s3NatPowCm n q : S3) : Quaternion ℝ) = (q : Quaternion ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [s3NatPowCm_succ, s3MulCm_apply, s3Mul_coe, ih, ContinuousMap.id_apply, pow_succ]

/-- The power map `q ↦ qᵐ` on `S³` for an integer exponent (for `m < 0` it is the inverse of the
`(-m)`-th power map, `q ↦ (q^{-m})⁻¹`). -/
def s3ZPowCm (m : ℤ) : C(S3, S3) :=
  if 0 ≤ m then s3NatPowCm m.toNat else s3InvCm.comp (s3NatPowCm (-m).toNat)

@[simp] lemma s3ZPowCm_of_nonneg {m : ℤ} (hm : 0 ≤ m) : s3ZPowCm m = s3NatPowCm m.toNat := by
  rw [s3ZPowCm, if_pos hm]

@[simp] lemma s3ZPowCm_of_neg {m : ℤ} (hm : ¬ 0 ≤ m) :
    s3ZPowCm m = s3InvCm.comp (s3NatPowCm (-m).toNat) := by
  rw [s3ZPowCm, if_neg hm]

/-- The underlying quaternionic formula for the integer power maps. -/
lemma s3ZPowCm_coe (m : ℤ) (q : S3) :
    ((s3ZPowCm m q : S3) : Quaternion ℝ) = (q : Quaternion ℝ) ^ m := by
  by_cases hm : 0 ≤ m
  · rw [s3ZPowCm_of_nonneg hm, s3NatPowCm_coe, ← zpow_natCast, Int.toNat_of_nonneg hm]
  · rw [s3ZPowCm_of_neg hm, ContinuousMap.comp_apply, s3InvCm_apply, s3Inv_coe,
      star_eq_inv_of_s3 (s3NatPowCm (-m).toNat q), s3NatPowCm_coe, ← zpow_natCast,
      Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -m), zpow_neg, inv_inv]

@[simp] lemma s3ZPowCm_one : s3ZPowCm 1 = ContinuousMap.id S3 := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  rw [s3ZPowCm_coe, ContinuousMap.id_apply]
  simp

@[simp] lemma s3ZPowCm_zero : s3ZPowCm 0 = s3OneCm := by
  rw [s3ZPowCm_of_nonneg (le_refl (0 : ℤ))]
  norm_num

@[simp] lemma s3ZPowCm_two : s3ZPowCm 2 = s3Sq := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  rw [s3ZPowCm_coe, s3Sq_apply, s3Mul_coe,
    show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]

/-- **The degree of the `n`-th power map on `S³` is `n`.** -/
theorem chern2_natPowCm (n : ℕ) : chern2 (s3NatPowCm n) = n := by
  induction n with
  | zero => rw [s3NatPowCm_zero, chern2_oneCm]; rfl
  | succ n ih => rw [s3NatPowCm_succ, chern2_mul, ih, chern2_id]; push_cast; ring

/-- **The degree of the integer power map `q ↦ qᵐ` on `S³` is `m`.** -/
theorem chern2_zPowCm (m : ℤ) : chern2 (s3ZPowCm m) = m := by
  by_cases hm : 0 ≤ m
  · rw [s3ZPowCm_of_nonneg hm, chern2_natPowCm, Int.toNat_of_nonneg hm]
  · rw [s3ZPowCm_of_neg hm, chern2_comp, chern2_inv, chern2_natPowCm,
      Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -m)]
    ring

end

end Work.CharacteristicClasses
