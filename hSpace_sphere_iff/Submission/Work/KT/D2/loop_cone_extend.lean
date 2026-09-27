import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.D2.Basic

/-!
# Extending a based homotopy of loops in the units of `M_n(ℂ)` over a contractible disc

`D²` is the cone on `S¹`: the map `q(x, t) = t • x` from `S¹ × [0,1]` onto the closed disc
`D² ⊂ ℝ²` is a quotient map whose only non-trivial fibre is `S¹ × {0}`.  Because the homotopy `F`
is constant on that fibre (its base is the constant loop `1`), it descends to a continuous map
`G` on the disc.  Every property of `F` (unit values, commuting with an idempotent `e`, and its
value on the boundary `S¹ × {1}`) is inherited by `G`, and the centre of the disc is `1`.
-/

namespace Work.KT.D2

open Matrix
open Classical

noncomputable section

/-! ## The quotient map `S¹ × [0,1] → D²` -/

/-- Every point of the closed unit disc has norm at most `1`. -/
lemma norm_le_one_ball (y : Ball (Euc 2)) : ‖(y : Euc 2)‖ ≤ 1 := by
  have h := y.2
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  exact h

/-- The radial coordinate of a point of the disc, as an element of `[0,1]`. -/
def radU (y : Ball (Euc 2)) : unitInterval :=
  ⟨‖(y : Euc 2)‖, norm_nonneg _, norm_le_one_ball y⟩

@[simp] lemma radU_coe (y : Ball (Euc 2)) : (radU y : ℝ) = ‖(y : Euc 2)‖ := rfl

/-- The direction of a non-zero point of the disc, as a point of the unit circle. -/
def dirOf (y : Ball (Euc 2)) (h : (y : Euc 2) ≠ 0) : Sph (Euc 2) :=
  ⟨‖(y : Euc 2)‖⁻¹ • (y : Euc 2), by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)⟩

@[simp] lemma dirOf_coe (y : Ball (Euc 2)) (h : (y : Euc 2) ≠ 0) :
    (dirOf y h : Euc 2) = ‖(y : Euc 2)‖⁻¹ • (y : Euc 2) := rfl

lemma smul_mem_ball (p : Sph (Euc 2) × unitInterval) :
    (p.2 : ℝ) • (p.1 : Euc 2) ∈ Metric.closedBall (0 : Euc 2) 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg p.2.2.1, mem_sphere_zero_iff_norm.mp p.1.2, mul_one]
  exact p.2.2.2

/-- The quotient map `S¹ × [0,1] → D²`, `(x, t) ↦ t • x`. -/
def qfun : Sph (Euc 2) × unitInterval → Ball (Euc 2) :=
  fun p => ⟨(p.2 : ℝ) • (p.1 : Euc 2), smul_mem_ball p⟩

@[simp] lemma qfun_coe (p : Sph (Euc 2) × unitInterval) :
    (qfun p : Euc 2) = (p.2 : ℝ) • (p.1 : Euc 2) := rfl

lemma continuous_qfun : Continuous qfun := by
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.comp continuous_snd).smul
    (continuous_subtype_val.comp continuous_fst))

lemma qfun_surjective : Function.Surjective qfun := by
  intro y
  by_cases h : (y : Euc 2) = 0
  · refine ⟨(⟨unitVec 2 (by norm_num), by rw [mem_sphere_zero_iff_norm, norm_unitVec]⟩, 0), ?_⟩
    apply Subtype.ext
    show (0 : ℝ) • (unitVec 2 (by norm_num) : Euc 2) = (y : Euc 2)
    rw [zero_smul, h]
  · refine ⟨(dirOf y h, radU y), ?_⟩
    apply Subtype.ext
    show (radU y : ℝ) • (dirOf y h : Euc 2) = (y : Euc 2)
    rw [radU_coe, dirOf_coe, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h), one_smul]

/-- The boundary circle sits at `t = 1`: `q(x, 1) = x`. -/
lemma qfun_one (x : Sph (Euc 2)) : qfun (x, 1) = inBall x := by
  apply Subtype.ext
  show ((1 : unitInterval) : ℝ) • (x : Euc 2) = (x : Euc 2)
  rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_smul]

/-! ## The candidate extension of `F` -/

/-- The candidate extension `G(z) = F(z/‖z‖, ‖z‖)` for `z ≠ 0`, with `G(0) = 1`. -/
def Gfun (n : ℕ) (F : C(Sph (Euc 2) × unitInterval, Matrix (Fin n) (Fin n) ℂ))
    (y : Ball (Euc 2)) : Matrix (Fin n) (Fin n) ℂ :=
  if h : (y : Euc 2) = 0 then 1 else F (dirOf y h, radU y)

lemma radU_qfun (x : Sph (Euc 2)) (t : unitInterval) : radU (qfun (x, t)) = t := by
  apply Subtype.ext
  simp only [radU_coe, qfun_coe]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1, mem_sphere_zero_iff_norm.mp x.2, mul_one]

lemma dirOf_qfun (x : Sph (Euc 2)) (t : unitInterval) (ht : (t : ℝ) ≠ 0)
    (hne : (qfun (x, t) : Euc 2) ≠ 0) : dirOf (qfun (x, t)) hne = x := by
  apply Subtype.ext
  simp only [dirOf_coe, qfun_coe]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.2.1, mem_sphere_zero_iff_norm.mp x.2, mul_one,
    smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- `Gfun` is constant on the fibres of `q`: it descends to a well-defined map on the disc. -/
lemma Gfun_qfun (n : ℕ) (F : C(Sph (Euc 2) × unitInterval, Matrix (Fin n) (Fin n) ℂ))
    (hzero : ∀ x, F (x, 0) = 1) (p : Sph (Euc 2) × unitInterval) :
    Gfun n F (qfun p) = F p := by
  by_cases ht : (p.2 : ℝ) = 0
  · have hq : qfun p = (⟨0, by simp [Metric.mem_closedBall]⟩ : Ball (Euc 2)) := by
      apply Subtype.ext
      rw [qfun_coe, ht, zero_smul]
    rw [hq, Gfun, dif_pos rfl]
    have hp2 : p.2 = 0 := Subtype.ext ht
    rw [show p = (p.1, (0 : unitInterval)) from Prod.ext rfl hp2, hzero]
  · have hx0 : (p.1 : Euc 2) ≠ 0 := by
      intro h
      have h1 : ‖(p.1 : Euc 2)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
      rw [h, norm_zero] at h1
      exact one_ne_zero h1.symm
    have hne : (qfun p : Euc 2) ≠ 0 := by
      rw [qfun_coe]
      exact smul_ne_zero ht hx0
    rw [Gfun, dif_neg hne]
    rw [dirOf_qfun p.1 p.2 ht hne, radU_qfun p.1 p.2]

/-- `Gfun` is continuous, because it is the descent of the continuous map `F` along the quotient
map `q`. -/
lemma continuous_Gfun (n : ℕ) (F : C(Sph (Euc 2) × unitInterval, Matrix (Fin n) (Fin n) ℂ))
    (hzero : ∀ x, F (x, 0) = 1) : Continuous (Gfun n F) := by
  have hq : Topology.IsQuotientMap qfun :=
    Topology.IsQuotientMap.of_surjective_continuous qfun_surjective continuous_qfun
  refine (hq.continuous_iff (g := Gfun n F)).mpr ?_
  exact F.continuous.congr (fun p => (Gfun_qfun n F hzero p).symm)

theorem loop_cone_extend (n : ℕ) (e : Matrix (Fin n) (Fin n) ℂ)
    (F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × unitInterval,
      Matrix (Fin n) (Fin n) ℂ))
    (hunit : ∀ p, IsUnit (F p)) (hzero : ∀ x, F (x, 0) = 1)
    (hstab : ∀ p, F p * e = e * F p) :
    ∃ G : C(Work.KT.Ball (EuclideanSpace ℝ (Fin 2)), Matrix (Fin n) (Fin n) ℂ),
      (∀ y, IsUnit (G y)) ∧
      G (⟨0, by simp [Metric.mem_closedBall]⟩ : Work.KT.Ball (EuclideanSpace ℝ (Fin 2))) = 1 ∧
      (∀ y, G y * e = e * G y) ∧
      (∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        G (Work.KT.D2.inBall x) = F (x, 1)) := by
  have hcont : Continuous (Gfun n F) := continuous_Gfun n F hzero
  refine ⟨⟨Gfun n F, hcont⟩, ?_, ?_, ?_, ?_⟩
  · intro y
    change IsUnit (Gfun n F y)
    by_cases h : (y : Euc 2) = 0
    · rw [Gfun, dif_pos h]; exact isUnit_one
    · rw [Gfun, dif_neg h]; exact hunit _
  · change Gfun n F (⟨0, by simp [Metric.mem_closedBall]⟩ : Ball (Euc 2)) = 1
    rw [Gfun, dif_pos rfl]
  · intro y
    change Gfun n F y * e = e * Gfun n F y
    by_cases h : (y : Euc 2) = 0
    · rw [Gfun, dif_pos h]; simp
    · rw [Gfun, dif_neg h]; exact hstab _
  · intro x
    change Gfun n F (inBall x) = F (x, 1)
    rw [← qfun_one x]
    exact Gfun_qfun n F hzero (x, 1)

end

end Work.KT.D2
