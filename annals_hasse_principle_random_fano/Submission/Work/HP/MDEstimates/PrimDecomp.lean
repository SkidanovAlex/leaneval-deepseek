import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux

/-!
# The primitive decomposition of an integer vector

For `a : ι → ℤ` with `a ≠ 0` we write `a = pFac a • pDir a`, where `pFac a` is the absolute value
of the gcd of the coordinates and `pDir a` has coordinates `a i / gcd a`.  This is the unique
decomposition of `a` as `k • b` with `k ≥ 1` (a natural number) and `b` primitive
(`IsPrim b`, i.e. coordinate gcd `1`).

This file contains the definitions and the elementary arithmetic API: the gcd of a scalar
multiple, the scaling of the Euclidean norm `eNorm`, injectivity of the scaling map, and the
existence, primitivity, size and uniqueness of the decomposition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.HP.MDEstimates

open Finset

variable {ι : Type*} [Fintype ι]

/-- The scaling factor of the primitive decomposition of `a`: the absolute value of the gcd of
the coordinates of `a`. -/
def pFac (a : ι → ℤ) : ℕ := (Finset.univ.gcd a).natAbs

/-- The primitive direction of `a`: the coordinates of `a` divided by their gcd. -/
def pDir (a : ι → ℤ) : ι → ℤ := fun i => a i / Finset.univ.gcd a

/-- Pointwise scaling of an integer vector by a natural number. -/
def scale (k : ℕ) (b : ι → ℤ) : ι → ℤ := fun i => (k : ℤ) * b i

@[simp] lemma scale_one (b : ι → ℤ) : scale 1 b = b := by
  funext i; simp [scale]

@[simp] lemma scale_zero (b : ι → ℤ) : scale 0 b = 0 := by
  funext i; simp [scale]

lemma scale_eq_smul (k : ℕ) (b : ι → ℤ) : scale k b = (k : ℤ) • b := by
  funext i
  show (k : ℤ) * b i = ((k : ℤ) • b) i
  rw [Pi.smul_apply, smul_eq_mul]

lemma scale_smul (k : ℕ) (b : ι → ℤ) : scale k b = k • b := by
  funext i
  show (k : ℤ) * b i = (k • b) i
  rw [Pi.smul_apply, nsmul_eq_mul]

/-- The gcd of the coordinates of a pointwise scalar multiple. -/
lemma gcd_scale (k : ℕ) (b : ι → ℤ) :
    Finset.univ.gcd (scale k b) = (k : ℤ) * Finset.univ.gcd b := by
  show Finset.univ.gcd (fun i => (k : ℤ) * b i) = (k : ℤ) * Finset.univ.gcd b
  rw [Finset.gcd_mul_left, Int.normalize_coe_nat]

/-- For a primitive `b`, the gcd of the coordinates of `k • b` is `k`. -/
lemma gcd_scale_of_isPrim (k : ℕ) {b : ι → ℤ} (hb : IsPrim b) :
    Finset.univ.gcd (scale k b) = (k : ℤ) := by
  rw [gcd_scale, show Finset.univ.gcd b = 1 from hb, mul_one]

/-- The gcd of the coordinates is non-negative. -/
lemma gcd_nonneg (a : ι → ℤ) : 0 ≤ Finset.univ.gcd a := by
  have h : |Finset.univ.gcd a| = Finset.univ.gcd a :=
    (Int.abs_eq_normalize _).trans (Finset.normalize_gcd (f := a))
  rw [← h]; exact abs_nonneg _

/-- `(pFac a : ℤ)` is the gcd of the coordinates of `a`. -/
lemma coe_pFac (a : ι → ℤ) : ((pFac a : ℕ) : ℤ) = Finset.univ.gcd a :=
  Int.ofNat_natAbs_of_nonneg (gcd_nonneg a)

/-- A nonzero integer vector has nonzero coordinate gcd. -/
lemma gcd_ne_zero_of_ne_zero {a : ι → ℤ} (ha : a ≠ 0) : Finset.univ.gcd a ≠ 0 := by
  intro h
  apply ha
  funext i
  exact (Finset.gcd_eq_zero_iff.mp h) i (Finset.mem_univ i)

/-- The scaling factor of a nonzero vector is at least one. -/
lemma one_le_pFac {a : ι → ℤ} (ha : a ≠ 0) : 1 ≤ pFac a := by
  have h : 0 < pFac a := by
    rw [pFac, Int.natAbs_pos]
    exact gcd_ne_zero_of_ne_zero ha
  omega

/-- Scaling preserves the Euclidean norm. -/
lemma eNorm_scale (k : ℕ) (a : ι → ℤ) : eNorm (scale k a) = (k : ℝ) * eNorm a := by
  have h1 : ∑ i, (((scale k a) i : ℝ)) ^ 2 = ((k : ℝ)) ^ 2 * ∑ i, ((a i : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show (((k : ℤ) * a i : ℤ) : ℝ) ^ 2 = (k : ℝ) ^ 2 * ((a i : ℝ)) ^ 2
    push_cast
    ring
  rw [eNorm, eNorm, h1, Real.sqrt_mul (sq_nonneg (k : ℝ)),
    Real.sqrt_sq (Nat.cast_nonneg k)]

/-- The scaling map on integer vectors is injective for nonzero scale factors. -/
lemma scale_injective (k : ℕ) (hk : 1 ≤ k) : Function.Injective (scale k : (ι → ℤ) → ι → ℤ) := by
  intro a b hab
  have hkz : (k : ℤ) ≠ 0 := by
    have : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    omega
  funext i
  have hi := congrFun hab i
  simp only [scale] at hi
  exact mul_left_cancel₀ hkz hi

/-- The decomposition `a = pFac a • pDir a` for nonzero `a`. -/
lemma scale_pFac_pDir {a : ι → ℤ} (_ha : a ≠ 0) : scale (pFac a) (pDir a) = a := by
  funext i
  show (pFac a : ℤ) * (a i / Finset.univ.gcd a) = a i
  rw [coe_pFac]
  exact Int.mul_ediv_cancel' (Finset.gcd_dvd (Finset.mem_univ i))

/-- The primitive direction of a nonzero vector is primitive. -/
lemma isPrim_pDir {a : ι → ℤ} (ha : a ≠ 0) : IsPrim (pDir a) := by
  have hg : Finset.univ.gcd a ≠ 0 := gcd_ne_zero_of_ne_zero ha
  have h1 : Finset.univ.gcd a = (pFac a : ℤ) * Finset.univ.gcd (pDir a) := by
    conv_lhs => rw [← scale_pFac_pDir ha]
    exact gcd_scale (pFac a) (pDir a)
  rw [coe_pFac] at h1
  have h2 : (1 : ℤ) = Finset.univ.gcd (pDir a) :=
    mul_left_cancel₀ hg (by rw [mul_one]; exact h1)
  exact h2.symm

/-- The scaling factor of `k • b` for primitive `b` is `k`. -/
lemma pFac_scale_of_isPrim (k : ℕ) {b : ι → ℤ} (hb : IsPrim b) : pFac (scale k b) = k := by
  rw [pFac, gcd_scale_of_isPrim k hb, Int.natAbs_natCast]

/-- The primitive direction of `k • b` for primitive `b` is `b`. -/
lemma pDir_scale_of_isPrim (k : ℕ) {b : ι → ℤ} (hb : IsPrim b) (hk : 1 ≤ k) :
    pDir (scale k b) = b := by
  have hkz : (k : ℤ) ≠ 0 := by
    have : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    omega
  funext i
  show ((k : ℤ) * b i) / Finset.univ.gcd (scale k b) = b i
  rw [gcd_scale_of_isPrim k hb]
  exact Int.mul_ediv_cancel_left (b i) hkz

end Work.HP.MDEstimates
