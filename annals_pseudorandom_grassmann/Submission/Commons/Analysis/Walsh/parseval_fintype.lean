import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.Analysis.Walsh.sum_chi_index
import Submission.Commons.Analysis.Walsh.sum_norm_sq_chi_orthogonal

namespace Commons.Analysis.Walsh

open Finset BigOperators

noncomputable section

/-- The norm of the inverse of `(2 : ℂ) ^ n` is `((2 : ℝ) ^ n)⁻¹`. -/
lemma norm_inv_two_pow (n : ℕ) : ‖((2 : ℂ) ^ n)⁻¹‖ = ((2 : ℝ) ^ n)⁻¹ := by
  rw [norm_inv, norm_pow]
  norm_num

/-- For `p ≠ 0`, `p * (p⁻¹)^2 = p⁻¹`. -/
lemma mul_inv_sq_eq_inv {p : ℝ} (hp : p ≠ 0) : p * p⁻¹ ^ 2 = p⁻¹ := by
  rw [sq, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]

/-- The Walsh-character sum over all subsets of `ι`: for `z : ι → ZMod 2`,
`∑_{S} ∏_{i ∈ S} χ (z i)` equals `2 ^ #ι` when `z = 0` and `0` otherwise. -/
lemma sum_prod_stdAddChar_eq_ite {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι → ZMod 2) :
    (∑ S : Finset ι, ∏ i ∈ S, ZMod.stdAddChar (z i)) =
      if z = 0 then (2 : ℂ) ^ Fintype.card ι else 0 := by
  rw [sum_prod_eq_prod_one_add]
  simp only [one_add_stdAddChar]
  rw [prod_ite_eq_zero]

/-- In `(ZMod 2)^ι` two functions are equal iff their sum is zero. -/
lemma add_eq_zero_iff_eq_fun {ι : Type*} (x y : ι → ZMod 2) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi : x i + y i = 0 := by simpa using congrFun h i
    calc x i = - y i := add_eq_zero_iff_eq_neg.mp hi
      _ = y i := (eq_neg_iff_add_eq_zero.mpr (CharTwo.add_self_eq_zero (y i))).symm
  · intro h
    subst h
    funext i
    exact CharTwo.add_self_eq_zero (x i)

/-- Orthogonality of the Walsh characters, summed over the character index `S`:
`∑_{S} χ_S(x) χ_S(y) = 2 ^ #ι` if `x = y` and `0` otherwise. -/
lemma sum_chi_mul_chi_eq_ite {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → ZMod 2) :
    (∑ S : Finset ι,
        (∏ i ∈ S, ZMod.stdAddChar (x i)) * (∏ i ∈ S, ZMod.stdAddChar (y i)))
      = if x = y then (2 : ℂ) ^ Fintype.card ι else 0 := by
  have hpoint : ∀ S : Finset ι,
      (∏ i ∈ S, ZMod.stdAddChar (x i)) * (∏ i ∈ S, ZMod.stdAddChar (y i))
        = ∏ i ∈ S, ZMod.stdAddChar ((x + y) i) := by
    intro S
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← AddChar.map_add_eq_mul]
    rfl
  rw [Finset.sum_congr rfl (fun S _ => hpoint S), sum_prod_stdAddChar_eq_ite]
  by_cases h : x = y
  · subst h
    have : x + x = 0 := by funext i; exact CharTwo.add_self_eq_zero (x i)
    rw [if_pos this, if_pos rfl]
  · have hne : x + y ≠ 0 := fun hxy => h ((add_eq_zero_iff_eq_fun x y).mp hxy)
    rw [if_neg hne, if_neg h]

/-- Parseval's identity, "sum over the character index" form: the squared norms of the
(un-normalised) Fourier coefficients of `a` sum to `2 ^ #ι` times the squared norms of `a`. -/
theorem sum_norm_sq_chi_fst {ι : Type*} [Fintype ι] [DecidableEq ι] (a : (ι → ZMod 2) → ℂ) :
    (∑ S : Finset ι, ‖∑ x : ι → ZMod 2, a x * ∏ i ∈ S, ZMod.stdAddChar (x i)‖ ^ 2)
      = (2 : ℝ) ^ Fintype.card ι * ∑ x : ι → ZMod 2, ‖a x‖ ^ 2 := by
  classical
  have hstar : ∀ (S : Finset ι) (z : ι → ZMod 2),
      (starRingEnd ℂ) (∏ i ∈ S, ZMod.stdAddChar (z i)) = ∏ i ∈ S, ZMod.stdAddChar (z i) := by
    intro S z
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => starRingEnd_stdAddChar_two (z i))
  have hcomplex :
      (∑ S : Finset ι,
          (Complex.normSq (∑ x : ι → ZMod 2, a x * ∏ i ∈ S, ZMod.stdAddChar (x i)) : ℂ))
        = (2 : ℂ) ^ Fintype.card ι * ∑ x : ι → ZMod 2, (Complex.normSq (a x) : ℂ) := by
    have hsq : ∀ z : ℂ, (Complex.normSq z : ℂ) = z * (starRingEnd ℂ) z :=
      fun z => (Complex.mul_conj z).symm
    have hstarS : ∀ (S : Finset ι),
        (starRingEnd ℂ) (∑ x : ι → ZMod 2, a x * ∏ i ∈ S, ZMod.stdAddChar (x i))
          = ∑ y : ι → ZMod 2, (starRingEnd ℂ) (a y) * ∏ i ∈ S, ZMod.stdAddChar (y i) := by
      intro S
      rw [map_sum]
      exact Finset.sum_congr rfl (fun y _ => by rw [map_mul, hstar S y])
    have hexpand : ∀ S : Finset ι,
        (∑ x : ι → ZMod 2, a x * ∏ i ∈ S, ZMod.stdAddChar (x i)) *
          (starRingEnd ℂ) (∑ x : ι → ZMod 2, a x * ∏ i ∈ S, ZMod.stdAddChar (x i))
          = ∑ x : ι → ZMod 2, ∑ y : ι → ZMod 2,
              a x * (starRingEnd ℂ) (a y) *
                ((∏ i ∈ S, ZMod.stdAddChar (x i)) * (∏ i ∈ S, ZMod.stdAddChar (y i))) := by
      intro S
      rw [hstarS S, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      ring
    rw [Finset.sum_congr rfl (fun S _ => hsq _),
        Finset.sum_congr rfl (fun x _ => hsq _)]
    rw [Finset.sum_congr rfl (fun S _ => hexpand S)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm)]
    simp_rw [← Finset.mul_sum]
    simp only [sum_chi_mul_chi_eq_ite]
    have hinner : ∀ x : ι → ZMod 2,
        (∑ y : ι → ZMod 2,
            a x * (starRingEnd ℂ) (a y) * (if x = y then (2 : ℂ) ^ Fintype.card ι else 0))
          = a x * (starRingEnd ℂ) (a x) * (2 : ℂ) ^ Fintype.card ι := by
      intro x
      rw [Finset.sum_eq_single x]
      · rw [if_pos rfl]
      · intro y _ hy
        rw [if_neg (Ne.symm hy), mul_zero]
      · intro hx; exact absurd (Finset.mem_univ x) hx
    rw [Finset.sum_congr rfl (fun x _ => hinner x), ← Finset.sum_mul, mul_comm]
  have hreal : (∑ S : Finset ι,
        Complex.normSq (∑ x : ι → ZMod 2, a x * ∏ i ∈ S, ZMod.stdAddChar (x i)))
      = (2 : ℝ) ^ Fintype.card ι * ∑ x : ι → ZMod 2, Complex.normSq (a x) := by
    apply Complex.ofReal_inj.mp
    rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sum,
      Complex.ofReal_ofNat]
    simpa using hcomplex
  calc (∑ S : Finset ι, ‖∑ x : ι → ZMod 2, a x * ∏ i ∈ S, ZMod.stdAddChar (x i)‖ ^ 2)
      = ∑ S : Finset ι,
          Complex.normSq (∑ x : ι → ZMod 2, a x * ∏ i ∈ S, ZMod.stdAddChar (x i)) :=
        Finset.sum_congr rfl fun S _ => (Complex.normSq_eq_norm_sq _).symm
    _ = (2 : ℝ) ^ Fintype.card ι * ∑ x : ι → ZMod 2, Complex.normSq (a x) := hreal
    _ = (2 : ℝ) ^ Fintype.card ι * ∑ x : ι → ZMod 2, ‖a x‖ ^ 2 := by
        congr 1
        exact Finset.sum_congr rfl fun x _ => Complex.normSq_eq_norm_sq (a x)

/-- Parseval's identity with the normalised Walsh–Fourier transform on `(ZMod 2)^ι`. -/
theorem sum_norm_sq_chi_fst_normalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : (ι → ZMod 2) → ℂ) :
    (∑ S : Finset ι, ‖((2 : ℂ) ^ Fintype.card ι)⁻¹ *
        ∑ x : ι → ZMod 2, a x * ∏ i ∈ S, ZMod.stdAddChar (x i)‖ ^ 2)
      = ((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ x : ι → ZMod 2, ‖a x‖ ^ 2 := by
  classical
  have hfirst : (∑ S : Finset ι, ‖((2 : ℂ) ^ Fintype.card ι)⁻¹ *
        ∑ x : ι → ZMod 2, a x * ∏ i ∈ S, ZMod.stdAddChar (x i)‖ ^ 2)
      = ∑ S : Finset ι, ‖∑ x : ι → ZMod 2, ((2 : ℂ) ^ Fintype.card ι)⁻¹ * a x *
          ∏ i ∈ S, ZMod.stdAddChar (x i)‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun S _ => ?_)
    have hsum : ((2 : ℂ) ^ Fintype.card ι)⁻¹ *
          ∑ x : ι → ZMod 2, a x * ∏ i ∈ S, ZMod.stdAddChar (x i)
        = ∑ x : ι → ZMod 2, ((2 : ℂ) ^ Fintype.card ι)⁻¹ * a x *
            ∏ i ∈ S, ZMod.stdAddChar (x i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hsum]
  rw [hfirst, sum_norm_sq_chi_fst (fun x => ((2 : ℂ) ^ Fintype.card ι)⁻¹ * a x)]
  have h2 : ∀ x : ι → ZMod 2,
      ‖((2 : ℂ) ^ Fintype.card ι)⁻¹ * a x‖ ^ 2
        = ‖((2 : ℂ) ^ Fintype.card ι)⁻¹‖ ^ 2 * ‖a x‖ ^ 2 := by
    intro x
    rw [norm_mul, mul_pow]
  rw [Finset.sum_congr rfl (fun x _ => h2 x)]
  rw [← Finset.mul_sum]
  rw [norm_inv_two_pow]
  rw [← mul_assoc, mul_inv_sq_eq_inv (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]

/-- **Parseval's identity** for the Walsh–Fourier transform on `(ZMod 2)^ι`: the squared
norms of the (normalised) Fourier coefficients of `f` sum to `2 ^ -#ι` times the squared
norms of `f`. -/
theorem parseval_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ZMod 2) → ℂ) :
    (∑ S : Finset ι, ‖(((2 : ℂ) ^ Fintype.card ι)⁻¹ *
        ∑ x : ι → ZMod 2, f x * ∏ i ∈ S, ZMod.stdAddChar (x i))‖ ^ 2)
      = ((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ x : ι → ZMod 2, ‖f x‖ ^ 2 :=
  sum_norm_sq_chi_fst_normalized f

end

end Commons.Analysis.Walsh