import Mathlib.Data.Int.Star
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Submission.Work.BoseBoxFock.LatVec
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 800000

namespace Work.BoseBoxFock

open MeasureTheory Real
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ## The lattice norm -/

/-- The squared Euclidean norm of the lattice vector `latVec m`, as a natural number. -/
def nSq (m : Fin 3 → ℤ) : ℕ := ∑ i, (m i).natAbs ^ 2

lemma cast_natAbs_sq (n : ℤ) : ((n.natAbs : ℕ) : ℝ) ^ 2 = ((n : ℝ)) ^ 2 := by
  have h1 : ((n.natAbs : ℕ) : ℝ) = ((n.natAbs : ℤ) : ℝ) := by norm_num
  rw [h1, Int.natCast_natAbs, Int.cast_abs, sq_abs]

lemma nSq_cast (m : Fin 3 → ℤ) : (nSq m : ℝ) = ∑ i, ((m i : ℤ) : ℝ) ^ 2 := by
  simp only [nSq, Nat.cast_sum, Nat.cast_pow]
  exact Finset.sum_congr rfl fun i _ => cast_natAbs_sq (m i)

/-- The squared norm of the lattice vector is the sum of the squares of the coordinates. -/
lemma latVec_norm_sq (m : Fin 3 → ℤ) : ‖latVec m‖ ^ 2 = (nSq m : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq, nSq_cast]
  exact Finset.sum_congr rfl fun i _ => by
    rw [latVec, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]

lemma coord_sq_le_nSq (m : Fin 3 → ℤ) (i : Fin 3) : (m i).natAbs ^ 2 ≤ nSq m :=
  Finset.single_le_sum (f := fun j => (m j).natAbs ^ 2) (fun j _ => Nat.zero_le _)
    (Finset.mem_univ i)

/-- A coordinate bound for the lattice points with `nSq m ≤ K`. -/
lemma natAbs_le_of_nSq_le {m : Fin 3 → ℤ} {K : ℕ} (h : nSq m ≤ K) (i : Fin 3) :
    (m i).natAbs ≤ K := by
  have h1 : (m i).natAbs ^ 2 ≤ K := le_trans (coord_sq_le_nSq m i) h
  nlinarith [Nat.zero_le (m i).natAbs]

/-- `nSq m = 0` forces `m = 0`. -/
lemma eq_zero_of_nSq_eq_zero {m : Fin 3 → ℤ} (h : nSq m = 0) : m = 0 := by
  funext i
  have h1 : (m i).natAbs ≤ 0 := natAbs_le_of_nSq_le (le_of_eq h) i
  have h2 : (m i).natAbs = 0 := Nat.eq_zero_of_le_zero h1
  simpa using h2

lemma nSq_eq_zero_iff (m : Fin 3 → ℤ) : nSq m = 0 ↔ m = 0 :=
  ⟨eq_zero_of_nSq_eq_zero, fun h => by subst h; simp [nSq]⟩

@[simp] lemma nSq_zero : nSq (0 : Fin 3 → ℤ) = 0 := by simp [nSq]

/-! ## The theta functions -/

/-- The one-dimensional theta function `θ₁ a = Σ_{n ∈ ℤ} exp (-π a n²)`. -/
def theta1 (a : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-(π * a * (n : ℝ) ^ 2))

/-- The three-dimensional lattice theta function
`θ a = Σ_{m ∈ ℤ³} exp (-π a ‖latVec m‖²)`. -/
def thetaLat (a : ℝ) : ℝ := ∑' m : Fin 3 → ℤ, Real.exp (-(π * a * ‖latVec m‖ ^ 2))

/-- The lattice theta function with the origin removed: `Σ_{m ≠ 0} exp (-π a ‖latVec m‖²)`. -/
def thetaLat0 (a : ℝ) : ℝ :=
  ∑' m : Fin 3 → ℤ, if m = 0 then 0 else Real.exp (-(π * a * ‖latVec m‖ ^ 2))

/-! ## Summability -/

lemma summable_natAbs_pow {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun n : ℤ => r ^ n.natAbs := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor <;> simpa using summable_geometric_of_lt_one h0 h1

/-- Summability of the one-dimensional theta summand. -/
lemma theta1_summable (a : ℝ) (ha : 0 < a) :
    Summable fun n : ℤ => Real.exp (-(π * a * (n : ℝ) ^ 2)) := by
  have hpi : 0 < π * a := mul_pos pi_pos ha
  have hr0 : 0 ≤ Real.exp (-(π * a)) := Real.exp_nonneg _
  have hr1 : Real.exp (-(π * a)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun n => Real.exp_nonneg _) (fun n => ?_)
    (summable_natAbs_pow hr0 hr1)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hk : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn
    have hcast : ((n.natAbs : ℝ)) ^ 2 = ((n : ℝ)) ^ 2 := cast_natAbs_sq n
    have hle : (n.natAbs : ℝ) ≤ (n : ℝ) ^ 2 := by
      rw [← hcast]
      have hk1 : (1 : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hk
      nlinarith
    calc Real.exp (-(π * a * (n : ℝ) ^ 2)) ≤ Real.exp (-(π * a * (n.natAbs : ℝ))) :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp (-(π * a)) ^ n.natAbs := by
          rw [show -(π * a * (n.natAbs : ℝ)) = (n.natAbs : ℝ) * (-(π * a)) by ring,
            Real.exp_nat_mul]

lemma theta1_even (a : ℝ) : Function.Even fun n : ℤ => Real.exp (-(π * a * (n : ℝ) ^ 2)) := by
  intro n
  simp [Int.cast_neg]

/-! ## Product decomposition over `Fin 3 → ℤ` -/

/-- Reindexing a product over `Fin 3 → ℤ` as a triple. -/
def fin3Equiv : (Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ where
  toFun m := (m 0, m 1, m 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv m := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    obtain ⟨a, b, c⟩ := p
    rfl

@[simp] lemma fin3Equiv_apply (m : Fin 3 → ℤ) : fin3Equiv m = (m 0, m 1, m 2) := rfl

/-- Summability of a product of three copies of a nonnegative summable family over `ℤ`,
in the `ℤ × ℤ × ℤ` model. -/
lemma summable_triple {g : ℤ → ℝ} (hg : Summable g) (hnn : ∀ n, 0 ≤ g n) :
    Summable fun p : ℤ × ℤ × ℤ => g p.1 * g p.2.1 * g p.2.2 := by
  have h2 : Summable fun q : ℤ × ℤ => g q.1 * g q.2 := Summable.mul_of_nonneg hg hg hnn hnn
  have h3 : Summable fun p : ℤ × ℤ × ℤ => g p.1 * (g p.2.1 * g p.2.2) :=
    Summable.mul_of_nonneg hg h2 hnn (fun q => mul_nonneg (hnn _) (hnn _))
  exact h3.congr fun p => by ring

/-- **Factorisation of the lattice sum in the `ℤ × ℤ × ℤ` model.** -/
lemma tsum_triple {g : ℤ → ℝ} (hg : Summable g) (hnn : ∀ n, 0 ≤ g n) :
    (∑' p : ℤ × ℤ × ℤ, g p.1 * g p.2.1 * g p.2.2) = (∑' n : ℤ, g n) ^ 3 := by
  have hga : Summable fun n : ℤ => |g n| := hg.congr fun n => (abs_of_nonneg (hnn n)).symm
  have h2 : Summable fun q : ℤ × ℤ => g q.1 * g q.2 := Summable.mul_of_nonneg hg hg hnn hnn
  have h2nn : ∀ q : ℤ × ℤ, 0 ≤ g q.1 * g q.2 := fun q => mul_nonneg (hnn _) (hnn _)
  have h2a : Summable fun q : ℤ × ℤ => |g q.1 * g q.2| :=
    h2.congr fun q => (abs_of_nonneg (h2nn q)).symm
  have hA : (∑' n : ℤ, g n) * (∑' n : ℤ, g n) = ∑' q : ℤ × ℤ, g q.1 * g q.2 :=
    tsum_mul_tsum_of_summable_norm hga hga
  have hB : (∑' n : ℤ, g n) * (∑' q : ℤ × ℤ, g q.1 * g q.2)
      = ∑' p : ℤ × ℤ × ℤ, g p.1 * (g p.2.1 * g p.2.2) :=
    tsum_mul_tsum_of_summable_norm hga h2a
  calc (∑' p : ℤ × ℤ × ℤ, g p.1 * g p.2.1 * g p.2.2)
      = ∑' p : ℤ × ℤ × ℤ, g p.1 * (g p.2.1 * g p.2.2) :=
        tsum_congr fun p => by ring
    _ = (∑' n : ℤ, g n) * (∑' q : ℤ × ℤ, g q.1 * g q.2) := hB.symm
    _ = (∑' n : ℤ, g n) * ((∑' n : ℤ, g n) * (∑' n : ℤ, g n)) := by rw [hA]
    _ = (∑' n : ℤ, g n) ^ 3 := by ring

/-- **The three-dimensional theta function factorises** as the cube of the one-dimensional one. -/
lemma thetaLat_eq_theta1_cube (a : ℝ) (ha : 0 < a) : thetaLat a = theta1 a ^ 3 := by
  have hg := theta1_summable a ha
  have hnn : ∀ n : ℤ, 0 ≤ Real.exp (-(π * a * (n : ℝ) ^ 2)) := fun n => Real.exp_nonneg _
  have key : ∀ A B C : ℝ,
      Real.exp (-(π * a * A)) * Real.exp (-(π * a * B)) * Real.exp (-(π * a * C))
        = Real.exp (-(π * a * (A + B + C))) := by
    intro A B C
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hstep : thetaLat a = ∑' p : ℤ × ℤ × ℤ,
      Real.exp (-(π * a * (p.1 : ℝ) ^ 2)) * Real.exp (-(π * a * (p.2.1 : ℝ) ^ 2))
        * Real.exp (-(π * a * (p.2.2 : ℝ) ^ 2)) := by
    rw [thetaLat, ← Equiv.tsum_eq fin3Equiv]
    refine tsum_congr fun m => ?_
    have hnorm : ‖latVec m‖ ^ 2 = (m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2 + (m 2 : ℝ) ^ 2 := by
      rw [latVec_norm_sq, nSq_cast, Fin.sum_univ_three]
    simp only [fin3Equiv_apply]
    rw [hnorm]
    exact (key _ _ _).symm
  rw [hstep, tsum_triple hg hnn, theta1]

/-! ## The functional equation -/

/-- **The functional equation of the lattice theta function** (3D Poisson summation):
`θ a = a^{-3/2} θ (1/a)` for `a > 0`. -/
lemma thetaLat_modular (a : ℝ) (ha : 0 < a) :
    thetaLat a = (Real.sqrt a)⁻¹ ^ 3 * thetaLat a⁻¹ := by
  have h1 := Real.tsum_exp_neg_mul_int_sq ha
  have h1' : theta1 a = (Real.sqrt a)⁻¹ * theta1 a⁻¹ := by
    rw [theta1, theta1]
    rw [show (∑' n : ℤ, Real.exp (-(π * a * (n : ℝ) ^ 2)))
          = ∑' n : ℤ, Real.exp (-π * a * (n : ℝ) ^ 2) from
        tsum_congr fun n => by congr 1; ring]
    rw [show (∑' n : ℤ, Real.exp (-(π * a⁻¹ * (n : ℝ) ^ 2)))
          = ∑' n : ℤ, Real.exp (-π / a * (n : ℝ) ^ 2) from
        tsum_congr fun n => by congr 1; rw [div_eq_mul_inv]; ring]
    rw [h1]
    congr 1
    rw [← Real.sqrt_eq_rpow, one_div]
  rw [thetaLat_eq_theta1_cube a ha, thetaLat_eq_theta1_cube a⁻¹ (by positivity), h1']
  ring

/-! ## Removing the origin -/

lemma thetaLat_summable (a : ℝ) (ha : 0 < a) :
    Summable fun m : Fin 3 → ℤ => Real.exp (-(π * a * ‖latVec m‖ ^ 2)) := by
  have hg := theta1_summable a ha
  have hnn : ∀ n : ℤ, 0 ≤ Real.exp (-(π * a * (n : ℝ) ^ 2)) := fun n => Real.exp_nonneg _
  have h3 : Summable fun p : ℤ × ℤ × ℤ =>
      Real.exp (-(π * a * (p.1 : ℝ) ^ 2)) * Real.exp (-(π * a * (p.2.1 : ℝ) ^ 2))
        * Real.exp (-(π * a * (p.2.2 : ℝ) ^ 2)) := summable_triple hg hnn
  refine (h3.comp_injective fin3Equiv.injective).congr fun m => ?_
  show Real.exp (-(π * a * ((fin3Equiv m).1 : ℝ) ^ 2))
        * Real.exp (-(π * a * ((fin3Equiv m).2.1 : ℝ) ^ 2))
        * Real.exp (-(π * a * ((fin3Equiv m).2.2 : ℝ) ^ 2))
      = Real.exp (-(π * a * ‖latVec m‖ ^ 2))
  simp only [fin3Equiv_apply]
  have hnorm : ‖latVec m‖ ^ 2 = (m 0 : ℝ) ^ 2 + (m 1 : ℝ) ^ 2 + (m 2 : ℝ) ^ 2 := by
    rw [latVec_norm_sq, nSq_cast, Fin.sum_univ_three]
  rw [hnorm, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The removal of the origin: `θ a = Σ_{m ≠ 0} exp (-π a ‖latVec m‖²) + 1`. -/
lemma thetaLat_eq_thetaLat0_add_one (a : ℝ) (ha : 0 < a) :
    thetaLat a = thetaLat0 a + 1 := by
  have hsum := thetaLat_summable a ha
  rw [thetaLat, thetaLat0, hsum.tsum_eq_add_tsum_ite 0]
  have h0 : ‖latVec (0 : Fin 3 → ℤ)‖ ^ 2 = 0 := by
    rw [latVec_norm_sq]; simp
  rw [h0]
  norm_num
  ring

end

end Work.BoseBoxFock
