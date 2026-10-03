import Mathlib
import Submission.Commons.Analysis.ContDiff.exists_smooth_cutoff_infty
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Ad_sub_Md_eq_fract
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Submission.Commons.Analysis.ExponentialSums.large_sieve
import Submission.Commons.Analysis.ExponentialSums.third_derivative_test
import Submission.Commons.Analysis.Fourier.fourier_quadratic_eq
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Sqrt
import Submission.Commons.Analysis.Fourier.poisson_cos_residue
import Submission.Commons.Analysis.FriedlanderIwaniec.sum_coprime_sqrt_sub_pow_four
import Submission.Commons.Analysis.FriedlanderIwaniec.sum_gcd_class_natSqrt_eq_uniform
import Submission.Commons.Analysis.Sum.inv_sqrt_shell_bound
import Submission.Commons.Analysis.Sum.sum_inv_sqrt_le
import Submission.Commons.NumberTheory.ArithmeticFunction.card_divisors_le_rpow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_intpairs_ncard
import Submission.Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_sum_int_sqrt
import Submission.Commons.NumberTheory.FriedlanderIwaniec.MdNum_grouped_by_gcd
import Submission.Commons.NumberTheory.FriedlanderIwaniec.MdNum_reindex_squares
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_gdens_cubefree_eq_prod
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_card
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_sq_card
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mul_of_coprime
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_intpairs_asymptotic
import Submission.Commons.NumberTheory.FriedlanderIwaniec.gdens_mul_eq_divisor_sum
import Submission.Commons.NumberTheory.FriedlanderIwaniec.shell_count_intpairs
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sqZero_card_le_sqrt
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_one
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_zero_card
import Submission.Commons.NumberTheory.FriedlanderIwaniec.square_divisor_max_characterization
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_Icc_sq_eq_sum_Z
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_Z_mul_reindex
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_an_mul_eq_sum_box
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_rho_sq_div_le
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.Analysis.Fourier.fourier_integral_decay
import Submission.Commons.Analysis.Fourier.integral_cos_quadratic_subst
import Submission.Commons.Analysis.PSeries.tsum_int_abs_pow_neg_tail_le
import Submission.Commons.Analysis.Integral.sum_intervalIntegral_Icc_swap
import Submission.Commons.NumberTheory.FriedlanderIwaniec.linear_form_rho_bound_uniform
import Submission.Commons.NumberTheory.ZMod.tsum_int_quadratic_coset
import Submission.Commons.Analysis.Integral.mesh_riemann_sum_sub_integral_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

/-!  Copy of the team's §3 development (Submission/S3,S3b,S3c,S3d) inlined, since only
    Mathlib and commons may be imported. -/


/-!
# §3 of Friedlander–Iwaniec, "The polynomial X² + Y⁴ captures its primes"

Local definitions of the objects of §3 of the paper, together with elementary
identities about them.

The sequence of the sieve is
  `a_n = #{(a, c) ∈ ℤ × ℤ : a ^ 2 + c ^ 4 = n}`
(paper (3.1) with `Z` the indicator of the squares counted with multiplicity,
`Z(b) = #{c : ℤ // c ^ 2 = b}`).

The expected main term for the congruence sums is (paper §3, just above (3.1))
  `M_d(x) = d⁻¹ · ∑_{0 < a² + b² ≤ x} Z(b) · ρ(b; d)`,
where `ρ(b; d) = #{α : ZMod d // α ^ 2 + b ^ 2 = 0}`.  Since `Z` is supported on
the squares `b = c ^ 2` and `#{a : ℤ // a ^ 2 ≤ m} = 2⌊√m⌋ + 1`, this is the
explicit finite sum recorded below as `MdNum` (which equals `d * M_d(x)`).
-/

namespace Submission

set_option maxHeartbeats 4000000

open Finset MeasureTheory intervalIntegral

/-- `Z(b) = #{c : ℤ // c ^ 2 = b}`: the indicator of the squares, with
multiplicity (so `Z(0) = 1` and `Z(c ^ 2) = 2` for `c ≠ 0`). -/
noncomputable def Z (b : ℕ) : ℕ := if b = 0 then 1 else if Nat.sqrt b ^ 2 = b then 2 else 0

/-- `ρ(b; d) = #{α : ZMod d // α ^ 2 + b ^ 2 = 0}`, the number of roots of the
quadratic congruence `α ^ 2 + b ^ 2 ≡ 0 (mod d)`. -/
noncomputable def rho (b d : ℕ) : ℕ := ({α : ZMod d | α ^ 2 + (b : ZMod d) ^ 2 = 0}).ncard

/-- `a_n = #{(a, c) ∈ ℤ × ℤ : a ^ 2 + c ^ 4 = n}`, paper (3.1). -/
noncomputable def an (n : ℕ) : ℕ := ({x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 4 = n}).ncard

/-- `A(x) = ∑_{n ≤ x} a_n`, the summatory function of the sequence. -/
noncomputable def Aseq (x : ℕ) : ℕ := ∑ n ∈ Finset.range (x + 1), an n

/-- `A_d(x) = ∑_{n ≤ x, d ∣ n} a_n`, the congruence sums, paper (2.3). -/
noncomputable def Ad (d x : ℕ) : ℕ :=
  ∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n), an n

/-- `d · M_d(x)`, the expected main term for `A_d(x)` in the explicit form
`∑_{b ≤ √x} Z(b) ρ(b; d) (2⌊√(x − b²)⌋ + 1) − ρ(0; d)`, the last subtraction
removing the pair `(a, b) = (0, 0)`. -/
noncomputable def MdNum (d x : ℕ) : ℕ :=
  (∑ b ∈ Finset.range (Nat.sqrt x + 1),
      Z b * rho b d * (2 * Nat.sqrt (x - b ^ 2) + 1)) - rho 0 d

/-- The expected main term `M_d(x)`. -/
noncomputable def Md (d x : ℕ) : ℚ := (MdNum d x : ℚ) / d

/-! ### Elementary facts about `Z` -/

lemma Z_zero : Z 0 = 1 := by unfold Z; simp

lemma Z_sq (c : ℕ) : Z (c ^ 2) = if c = 0 then 1 else 2 := by
  by_cases hc : c = 0
  · subst hc; simp [Z_zero]
  · unfold Z
    rw [if_neg (pow_ne_zero 2 hc), if_pos (by rw [Nat.sqrt_eq' c])]
    simp [hc]

lemma Z_le_two (b : ℕ) : Z b ≤ 2 := by
  unfold Z
  by_cases h1 : b = 0
  · simp [h1]
  · by_cases h2 : Nat.sqrt b ^ 2 = b <;> simp [h1, h2]

lemma Z_eq_two_of_sq {c : ℕ} (hc : c ≠ 0) : Z (c ^ 2) = 2 := by
  rw [Z_sq]; simp [hc]

lemma Z_eq_zero_of_not_sq {b : ℕ} (hb : b ≠ 0) (h : Nat.sqrt b ^ 2 ≠ b) : Z b = 0 := by
  unfold Z; simp [hb, h]

lemma Z_pos_iff {b : ℕ} : 0 < Z b ↔ b = 0 ∨ Nat.sqrt b ^ 2 = b := by
  unfold Z
  by_cases h1 : b = 0
  · simp [h1]
  · by_cases h2 : Nat.sqrt b ^ 2 = b <;> simp [h1, h2]

/-! ### Elementary facts about `rho` -/

/-- `ρ(b; d)` with `d = 1` is `1`. -/
lemma rho_one (b : ℕ) : rho b 1 = 1 := by
  rw [rho]
  have : ({α : ZMod 1 | α ^ 2 + (b : ZMod 1) ^ 2 = 0}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro α
    simp only [Set.mem_ofPred_eq]
    exact Subsingleton.elim _ _
  rw [this, Set.ncard_univ, Nat.card_zmod]

/-- `ρ(1; d)` is the number of square roots of `-1` modulo `d`. -/
lemma rho_one_one (d : ℕ) : rho 1 d = ({α : ZMod d | α ^ 2 = -1}).ncard := by
  rw [rho]
  congr 1
  ext α
  simp only [Set.mem_ofPred_eq, Nat.cast_one, one_pow]
  exact add_eq_zero_iff_eq_neg

/-! ### Counting the `a`'s for fixed `b` -/

/-- The number of integers `a` with `a ^ 2 ≤ m` is `2⌊√m⌋ + 1`. -/
lemma ncard_int_sq_le (m : ℕ) :
    ({a : ℤ | a ^ 2 ≤ (m : ℤ)}).ncard = 2 * Nat.sqrt m + 1 := by
  have key : ∀ a : ℤ, (a ^ 2 ≤ (m:ℤ) ↔ a.natAbs ^ 2 ≤ m) := by
    intro a
    constructor
    · intro h
      have h' : ((a.natAbs : ℤ)) ^ 2 ≤ (m : ℤ) := by rw [Int.natAbs_sq]; exact h
      exact_mod_cast h'
    · intro h
      have h5 : ((a.natAbs : ℤ)) ^ 2 ≤ (m : ℤ) := by exact_mod_cast h
      rwa [Int.natAbs_sq] at h5
  have key2 : ∀ a : ℤ, (|a| ≤ (((Nat.sqrt m : ℕ)) : ℤ) ↔ a.natAbs ≤ Nat.sqrt m) := by
    intro a
    rw [← Int.natCast_natAbs]
    exact Nat.cast_le
  have hset : {a : ℤ | a ^ 2 ≤ (m : ℤ)}
      = ↑(Finset.Icc (-(((Nat.sqrt m : ℕ) : ℤ))) (((Nat.sqrt m : ℕ) : ℤ))) := by
    ext a
    simp only [Set.mem_ofPred_eq, Finset.coe_Icc, Set.mem_Icc]
    rw [← abs_le, key a, key2 a, Nat.le_sqrt']
  rw [hset, Set.ncard_coe_finset, Int.card_Icc]
  have h1 : (((Nat.sqrt m : ℕ) : ℤ) + 1 - -(((Nat.sqrt m : ℕ)) : ℤ))
      = ((2 * Nat.sqrt m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h1, Int.toNat_natCast]

/-- **The expected main term in `ℤ`-form.**  For `d ≥ 1`,
`d · M_d(x) = ∑_{b ≤ √x} Z(b) ρ(b; d) #{a : ℤ // a² + b² ≤ x} − ρ(0; d)`. -/
theorem MdNum_eq_intSum (d x : ℕ) :
    MdNum d x = (∑ b ∈ Finset.range (Nat.sqrt x + 1),
        Z b * rho b d * ({a : ℤ | a ^ 2 + (b : ℤ) ^ 2 ≤ (x : ℤ)}).ncard) - rho 0 d := by
  rw [MdNum]
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb' : b ≤ Nat.sqrt x := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
  have hb2 : b ^ 2 ≤ x := by
    calc b ^ 2 ≤ (Nat.sqrt x) ^ 2 := Nat.pow_le_pow_left hb' 2
      _ ≤ x := Nat.sqrt_le' x
  have hcast : ((x : ℤ) - (b : ℤ) ^ 2) = (((x - b ^ 2 : ℕ)) : ℤ) := by
    rw [Nat.cast_sub hb2]; push_cast; ring
  have hsetb : {a : ℤ | a ^ 2 + (b : ℤ) ^ 2 ≤ (x : ℤ)}
      = {a : ℤ | a ^ 2 ≤ (((x - b ^ 2 : ℕ)) : ℤ)} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    rw [← hcast]
    constructor <;> intro h <;> linarith
  rw [hsetb, ncard_int_sq_le]

/-- `ρ(0; d)` is the largest square root: `∏_{p ∣ d} p ^ (v_p(d) / 2) = ⌊√d⌋`. -/
lemma rho_zero_eq (d : ℕ) (hd : 0 < d) : rho 0 d = Nat.floorRoot 2 d := by
  have hd0 : d ≠ 0 := hd.ne'
  have hset : {α : ZMod d | α ^ 2 + ((0 : ℕ) : ZMod d) ^ 2 = 0} = {α : ZMod d | α ^ 2 = 0} := by
    congr 1
    ext α
    simp
  rw [rho, hset, Commons.NumberTheory.FriedlanderIwaniec.sq_roots_zero_card hd]
  rw [Nat.floorRoot, if_neg (by omega), Finsupp.prod, Nat.support_factorization]

/-! ### The local density `g(d) = N(d)/d²` (paper §2 (2.3), §3 (3.16)) -/

/-- `N(d) = #{(α, γ) ∈ (ZMod d)² : α² + γ⁴ = 0}`, the number of roots of the
quartic congruence modulo `d`. -/
noncomputable def N (d : ℕ) : ℕ := ({x : ZMod d × ZMod d | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard

/-- The local density of the sequence: `g(d) = N(d) / d²`. -/
noncomputable def gdens (d : ℕ) : ℚ := (N d : ℚ) / (d : ℚ) ^ 2

/-- The character `χ₄` of conductor four, evaluated on a natural number. -/
noncomputable def chi4 (n : ℕ) : ℤ := ZMod.χ₄ (n : ZMod 4)

lemma chi4_one_mod_four {n : ℕ} (h : n % 4 = 1) : chi4 n = 1 := by
  rw [chi4]; exact ZMod.χ₄_nat_one_mod_four h

lemma chi4_three_mod_four {n : ℕ} (h : n % 4 = 3) : chi4 n = -1 := by
  rw [chi4]; exact ZMod.χ₄_nat_three_mod_four h

lemma gdens_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    gdens (m * n) = gdens m * gdens n := by
  have hN := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mul_of_coprime h
  simp only [gdens, N] at hN ⊢
  rw [hN]
  push_cast
  rw [mul_pow]
  field_simp

lemma gdens_one : gdens 1 = 1 := by
  simp only [gdens, N]
  have : ({x : ZMod 1 × ZMod 1 | x.1 ^ 2 + x.2 ^ 4 = 0}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Subsingleton.elim _ _
  rw [this, Set.ncard_univ]
  simp

/-- `(3.16)`, first line: `g(p) · p = 1 + χ₄(p)(1 − 1/p)`, for odd primes `p`. -/
theorem gdens_prime_mul {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    gdens p * p = 1 + (chi4 p : ℚ) * (1 - 1 / p) := by
  have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
    exact Nat.odd_mod_four_iff.mp hodd
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hNd := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_card hp
  rcases hpmod with h1 | h3
  · have hvalQ : (N p : ℚ) = 2 * (p : ℚ) - 1 := by
      have h : N p + 1 = 2 * p := by
        simp only [N]
        rw [hNd, if_neg (by omega : ¬ p % 4 = 3), if_neg h2]
        omega
      have := congrArg (fun k : ℕ => (k : ℚ)) h
      push_cast at this
      linarith
    rw [gdens, hvalQ, chi4_one_mod_four h1]
    field_simp
    push_cast
    ring
  · have hvalQ : (N p : ℚ) = 1 := by
      simp only [N]
      rw [hNd, if_pos h3]
      norm_num
    rw [gdens, hvalQ, chi4_three_mod_four h3]
    field_simp
    push_cast
    ring

/-- `(3.16)`, second line: `g(p²) · p² = 1 + ρ(p)(1 − 1/p)` with `ρ(p) = 1 + χ₄(p)`,
for odd primes `p`.  (`p = 2` is the exceptional `g(4) = 1/4`.) -/
theorem gdens_prime_sq_mul {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    gdens (p ^ 2) * (p : ℚ) ^ 2 =
      1 + (1 + (chi4 p : ℚ)) * (1 - 1 / p) := by
  have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
    exact Nat.odd_mod_four_iff.mp hodd
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hNd := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_sq_card hp
  rcases hpmod with h1 | h3
  · have hle : 2 * p ≤ 3 * p ^ 2 := by
      have hp2 : 2 ≤ p := hp.two_le
      nlinarith
    have hvalQ : (N (p ^ 2) : ℚ) = 3 * (p : ℚ) ^ 2 - 2 * p := by
      simp only [N]
      rw [hNd, if_neg h2, if_pos h1, Nat.cast_sub hle]
      push_cast
      ring
    rw [gdens, hvalQ, chi4_one_mod_four h1]
    field_simp
    push_cast
    ring
  · have hvalQ : (N (p ^ 2) : ℚ) = (p : ℚ) ^ 2 := by
      simp only [N]
      rw [hNd, if_neg h2, if_neg (by omega : ¬ p % 4 = 1)]
      push_cast
      ring
    rw [gdens, hvalQ, chi4_three_mod_four h3]
    field_simp
    push_cast
    ring

lemma N_prime_two : N 2 = 2 := by
  have hNd := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_card
    Nat.prime_two
  simp only [N]
  rw [hNd]; norm_num

/-- Hypothesis `(2.4)` of the sieve: `g(p) < 1`. -/
theorem gdens_prime_lt_one {p : ℕ} (hp : p.Prime) : gdens p < 1 := by
  by_cases h2 : p = 2
  · subst h2
    rw [gdens, N_prime_two]; norm_num
  · have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by
      have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
      exact Nat.odd_mod_four_iff.mp hodd
    have hp2 : 2 ≤ p := hp.two_le
    have hNd := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_card hp
    rcases hpmod with h1 | h3
    · have hval : (N p : ℚ) = 2 * p - 1 := by
        have h : N p + 1 = 2 * p := by
          simp only [N]
          rw [hNd, if_neg (by omega : ¬ p % 4 = 3), if_neg h2]; omega
        have := congrArg (fun k : ℕ => (k : ℚ)) h
        push_cast at this
        linarith
      rw [gdens, hval, div_lt_one (by positivity : (0:ℚ) < (p:ℚ)^2)]
      have hp3 : (3:ℚ) ≤ p := by exact_mod_cast (by omega : 3 ≤ p)
      nlinarith [sq_nonneg ((p:ℚ) - 1)]
    · have hval : (N p : ℚ) = 1 := by
        simp only [N]; rw [hNd, if_pos h3]; norm_num
      rw [gdens, hval, div_lt_one (by positivity : (0:ℚ) < (p:ℚ)^2)]
      have hp1 : (1:ℚ) < p ^ 2 := by
        have : (2:ℚ) ≤ p := by exact_mod_cast hp2
        nlinarith
      linarith

/-- Hypothesis `(2.4)` of the sieve: `g(p²) ≤ g(p)`. -/
theorem gdens_prime_sq_le {p : ℕ} (hp : p.Prime) : gdens (p ^ 2) ≤ gdens p := by
  by_cases h2 : p = 2
  · subst h2
    have hNd := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_sq_card
      (p := 2) Nat.prime_two
    have hval : (N (2 ^ 2) : ℚ) = 4 := by
      simp only [N]; rw [hNd]; norm_num
    rw [gdens, hval, gdens, N_prime_two]
    norm_num
  · have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by
      have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
      exact Nat.odd_mod_four_iff.mp hodd
    have hp2 : 2 ≤ p := hp.two_le
    have hNd := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_card hp
    have hNdsq := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_sq_card hp
    rcases hpmod with h1 | h3
    · have hle : 2 * p ≤ 3 * p ^ 2 := by nlinarith
      have hval : (N p : ℚ) = 2 * p - 1 := by
        have h : N p + 1 = 2 * p := by
          simp only [N]
          rw [hNd, if_neg (by omega : ¬ p % 4 = 3), if_neg h2]; omega
        have := congrArg (fun k : ℕ => (k : ℚ)) h
        push_cast at this
        linarith
      have hvalsq : (N (p ^ 2) : ℚ) = 3 * (p : ℚ) ^ 2 - 2 * p := by
        simp only [N]
        rw [hNdsq, if_neg h2, if_pos h1, Nat.cast_sub hle]
        push_cast; ring
      rw [gdens, hvalsq, gdens, hval]
      have hp3 : (3:ℚ) ≤ p := by exact_mod_cast (by omega : 3 ≤ p)
      push_cast
      have key : (0:ℚ) ≤ 2 * (p:ℚ)^3 * ((p:ℚ) - 1)^2 :=
        mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by linarith) 3)) (sq_nonneg _)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [key]
    · have hval : (N p : ℚ) = 1 := by
        simp only [N]; rw [hNd, if_pos h3]; norm_num
      have hvalsq : (N (p ^ 2) : ℚ) = (p : ℚ) ^ 2 := by
        simp only [N]; rw [hNdsq, if_neg h2, if_neg (by omega : ¬ p % 4 = 1)]
        push_cast; ring
      rw [gdens, hvalsq, gdens, hval]
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((p:ℚ) - 1)]

/-- Hypothesis `(2.5)` of the sieve: `g(p) · p` is bounded. -/
theorem gdens_prime_mul_le {p : ℕ} (hp : p.Prime) : gdens p * p ≤ 2 := by
  by_cases h2 : p = 2
  · subst h2
    rw [gdens, N_prime_two]; norm_num
  · have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by
      have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
      exact Nat.odd_mod_four_iff.mp hodd
    have hNd := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_card hp
    rcases hpmod with h1 | h3
    · have hval : (N p : ℚ) = 2 * p - 1 := by
        have h : N p + 1 = 2 * p := by
          simp only [N]
          rw [hNd, if_neg (by omega : ¬ p % 4 = 3), if_neg h2]; omega
        have := congrArg (fun k : ℕ => (k : ℚ)) h
        push_cast at this
        linarith
      rw [gdens, hval]
      have hp0 : (0:ℚ) < p := by exact_mod_cast hp.pos
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    · have hval : (N p : ℚ) = 1 := by
        simp only [N]; rw [hNd, if_pos h3]; norm_num
      rw [gdens, hval]
      have hp0 : (0:ℚ) < p := by exact_mod_cast hp.pos
      have hp1 : (1:ℚ) ≤ p := by exact_mod_cast hp.one_le
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hp0, hp1, sq_nonneg (p:ℚ)]

/-- Hypothesis `(2.6)` of the sieve: `g(p²) · p²` is bounded. -/
theorem gdens_prime_sq_mul_le {p : ℕ} (hp : p.Prime) : gdens (p ^ 2) * (p : ℚ) ^ 2 ≤ 3 := by
  by_cases h2 : p = 2
  · subst h2
    have hNd := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_sq_card
      (p := 2) Nat.prime_two
    have hval : (N (2 ^ 2) : ℚ) = 4 := by
      simp only [N]; rw [hNd]; norm_num
    rw [gdens, hval]; norm_num
  · have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by
      have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
      exact Nat.odd_mod_four_iff.mp hodd
    have hp2 : 2 ≤ p := hp.two_le
    have hNdsq := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_sq_card hp
    rcases hpmod with h1 | h3
    · have hle : 2 * p ≤ 3 * p ^ 2 := by nlinarith
      have hvalsq : (N (p ^ 2) : ℚ) = 3 * (p : ℚ) ^ 2 - 2 * p := by
        simp only [N]
        rw [hNdsq, if_neg h2, if_pos h1, Nat.cast_sub hle]
        push_cast; ring
      rw [gdens, hvalsq]
      have hp0 : (0:ℚ) < p := by exact_mod_cast hp.pos
      push_cast
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hp0, sq_nonneg (p:ℚ)]
    · have hvalsq : (N (p ^ 2) : ℚ) = (p : ℚ) ^ 2 := by
        simp only [N]
        rw [hNdsq, if_neg h2, if_neg (by omega : ¬ p % 4 = 1)]
        push_cast; ring
      rw [gdens, hvalsq]
      have hp0 : (0:ℚ) < p := by exact_mod_cast hp.pos
      push_cast
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hp0, sq_nonneg (p:ℚ)]

/-- `g(4) = 1/4`: the exceptional value for `d` divisible by `4`. -/
theorem gdens_four : gdens 4 = 1 / 4 := by
  have hNd := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_sq_card
    (p := 2) Nat.prime_two
  have hval : (N (2 ^ 2) : ℚ) = 4 := by
    simp only [N]
    rw [hNd]; norm_num
  have h : gdens (2 ^ 2) = 1 / 4 := by
    rw [gdens, hval]; norm_num
  simpa using h

lemma rho_zero_eq_sqZero (d : ℕ) :
    rho 0 d = ({α : ZMod d | α ^ 2 = 0}).ncard := by
  rw [rho]; congr 1; ext α; simp

/-- The closed form of `d · M_d(x)` in terms of the roots `ρ(c²; d)` for `1 ≤ c ≤ ⌊x^{1/4}⌋`. -/
theorem MdNum_reindex (d x : ℕ) :
    MdNum d x = 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
        rho (c ^ 2) d * (2 * Nat.sqrt (x - c ^ 4) + 1))
      + 2 * Nat.sqrt x * rho 0 d := by
  simp only [MdNum, Z, rho]
  rw [show ({α : ZMod d | α ^ 2 + (((0 : ℕ)) : ZMod d) ^ 2 = 0})
        = ({α : ZMod d | α ^ 2 = 0}) from by
    congr 1; ext α; simp]
  exact Commons.NumberTheory.FriedlanderIwaniec.MdNum_reindex_squares d x

/-- `M_1(x)`: since `ρ(b; 1) = 1`, the main term for `d = 1` is the plain count
`2∑_{c ≤ ⌊x^{1/4}⌋}(2⌊√(x − c⁴)⌋ + 1) + 2⌊√x⌋`. -/
theorem MdNum_one (x : ℕ) :
    MdNum 1 x = 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
        (2 * Nat.sqrt (x - c ^ 4) + 1)) + 2 * Nat.sqrt x := by
  rw [MdNum_reindex]
  simp [rho_one]

/-- `A(x)` is the number of integer pairs `(a, c)` with `a² + c⁴ ≤ x`. -/
theorem Aseq_eq_ncard (x : ℕ) :
    Aseq x = ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}).ncard := by
  simp only [Aseq, an]
  exact Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_intpairs_ncard x

/-- **(3.18)**: `A(x) = 4κx^{3/4} + O(√x)`. -/
theorem Aseq_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
      |(Aseq x : ℝ) -
        4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)| ≤ C * Real.sqrt x := by
  obtain ⟨C, hC, hbound⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_intpairs_asymptotic
  exact ⟨C, hC, fun x hx => by rw [Aseq_eq_ncard]; exact hbound x hx⟩

/-- `A(x) = M_1(x) + 1`: the only difference between the count and the `d = 1`
main term is the origin `(a, c) = (0, 0)`. -/
theorem Aseq_eq_MdNum_one_add_one (x : ℕ) : Aseq x = MdNum 1 x + 1 := by
  rw [Aseq, MdNum_one]
  simp only [an]
  rw [Commons.NumberTheory.FriedlanderIwaniec.Aseq_eq_sum_int_sqrt x]
  ring

/-- **Lemma 3.4 for `d = 1`**: `M_1(x) = A(x) − 1 = 4κx^{3/4} + O(√x)`. -/
theorem Md_one_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
      |(Md 1 x : ℝ) - 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)|
        ≤ C * Real.sqrt x + 1 := by
  obtain ⟨C, hC, hb⟩ := Aseq_asymptotic
  refine ⟨C, hC, fun x hx => ?_⟩
  have hA : (Aseq x : ℝ) = (MdNum 1 x : ℝ) + 1 := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) (Aseq_eq_MdNum_one_add_one x)
    push_cast at h
    linarith
  have hM : (Md 1 x : ℝ) = (MdNum 1 x : ℝ) := by
    rw [Md]
    push_cast
    ring
  have hM' : (MdNum 1 x : ℝ) = (Aseq x : ℝ) - 1 := by linarith
  have hb' := hb x hx
  rw [hM, hM']
  rw [abs_le] at hb' ⊢
  constructor <;> linarith [hb'.1, hb'.2]

/-- The product form of `g(d)` for cubefree `d = d₁d₂²` (`d₁,d₂` squarefree, coprime, `4∤d`),
which is exactly (3.16) read multiplicatively. -/
theorem gdens_cubefree_eq_prod {d₁ d₂ : ℕ} (hs₁ : Squarefree d₁) (hs₂ : Squarefree d₂)
    (hcop : Nat.Coprime d₁ d₂) (h4 : ¬ 4 ∣ d₁ * d₂ ^ 2) :
    gdens (d₁ * d₂ ^ 2)
      = (∏ p ∈ d₁.primeFactors, (((1 : ℚ) + (chi4 p : ℚ)) * ((p : ℚ) - 1) + 1) / (p : ℚ) ^ 2)
        * (∏ p ∈ d₂.primeFactors,
            (((1 : ℚ) + (chi4 p : ℚ)) * ((p : ℚ) - 1) + (p : ℚ)) / (p : ℚ) ^ 3) := by
  have h := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_gdens_cubefree_eq_prod hs₁ hs₂ hcop h4
  simpa only [gdens, N, chi4] using h

/-- `d · g(d)` as the divisor sum that arises from Lemma 3.4's evaluation. -/
theorem gdens_mul_eq_sum {d₁ d₂ : ℕ} (hs₁ : Squarefree d₁) (hs₂ : Squarefree d₂)
    (hcop : Nat.Coprime d₁ d₂) (h4 : ¬ 4 ∣ d₁ * d₂ ^ 2) :
    ((d₁ * d₂ ^ 2 : ℕ) : ℚ) * gdens (d₁ * d₂ ^ 2)
      = ∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
          (ν₂ : ℚ) * (({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard : ℕ) : ℚ)
            * (Nat.totient ((d₁ * d₂) / (ν₁ * ν₂)) : ℚ) / ((d₁ * d₂ : ℕ) : ℚ) := by
  rw [gdens_cubefree_eq_prod hs₁ hs₂ hcop h4]
  exact Commons.NumberTheory.FriedlanderIwaniec.gdens_mul_eq_divisor_sum hs₁ hs₂ hcop h4

/-- The error coefficient `h(d)` of Lemma 3.4, for the decomposition `d = d₁ d₂²`:
`h(d₁,d₂) = (2/(d₁d₂²)) ∑_{ν₁|d₁,ν₂|d₂} ν₂ ρ(d₁d₂/(ν₁ν₂)) (τ(d₁d₂/(ν₁ν₂)) + 1)`. -/
noncomputable def hdens (d₁ d₂ : ℕ) : ℚ :=
  (2 / (((d₁ * d₂ ^ 2 : ℕ)) : ℚ)) *
    (∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
      (ν₂ : ℚ) * (({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard : ℕ) : ℚ) *
        ((((Nat.divisors ((d₁ * d₂) / (ν₁ * ν₂))).card : ℕ) : ℚ) + 1))

/-- For squarefree coprime `d₁, d₂` the "square part" of `d₁ d₂²` is `d₂`. -/
lemma floorRoot_two_mul_sq {d₁ d₂ : ℕ} (hs₁ : Squarefree d₁) (hs₂ : Squarefree d₂)
    (hcop : Nat.Coprime d₁ d₂) : Nat.floorRoot 2 (d₁ * d₂ ^ 2) = d₂ := by
  have h₁0 : d₁ ≠ 0 := hs₁.ne_zero
  have h₂0 : d₂ ≠ 0 := hs₂.ne_zero
  have hP0 : d₁ * d₂ ^ 2 ≠ 0 := mul_ne_zero h₁0 (pow_ne_zero 2 h₂0)
  have hR0 : Nat.floorRoot 2 (d₁ * d₂ ^ 2) ≠ 0 := by
    rw [Nat.floorRoot, if_neg (by omega : ¬ (2 = 0 ∨ d₁ * d₂ ^ 2 = 0)),
        Finsupp.prod, Nat.support_factorization]
    exact Finset.prod_ne_zero_iff.mpr
      (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hle₁ := (Nat.squarefree_iff_factorization_le_one h₁0).mp hs₁
  have hle₂ := (Nat.squarefree_iff_factorization_le_one h₂0).mp hs₂
  refine Nat.eq_of_factorization_eq hR0 h₂0 fun p => ?_
  rw [Nat.factorization_floorRoot]
  simp only [Finsupp.floorDiv_apply]
  rw [Nat.factorization_mul h₁0 (pow_ne_zero 2 h₂0), Nat.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have hcase : d₁.factorization p = 0 ∨ d₂.factorization p = 0 := by
    by_contra h
    push Not at h
    have hp1 : p.Prime := by
      by_contra hp
      rw [Nat.factorization_eq_zero_of_not_prime d₁ hp] at h
      exact h.1 rfl
    have hd1 : p ∣ d₁ := (hp1.dvd_iff_one_le_factorization h₁0).mpr (Nat.pos_iff_ne_zero.mpr h.1)
    have hd2 : p ∣ d₂ := (hp1.dvd_iff_one_le_factorization h₂0).mpr (Nat.pos_iff_ne_zero.mpr h.2)
    exact hp1.not_dvd_one (hcop ▸ Nat.dvd_gcd hd1 hd2)
  rcases hcase with h1 | h2
  · rw [h1, zero_add]; simp
  · have hle := hle₁ p
    rw [h2, mul_zero, add_zero,
      show d₁.factorization p ⌊/⌋ 2 = d₁.factorization p / 2 from rfl]
    omega

/-- For `d = d₁ d₂²` as above, `ρ(0; d) = ⌊√d⌋ = d₂`. -/
lemma rho_zero_cubefree {d₁ d₂ : ℕ} (hs₁ : Squarefree d₁) (hs₂ : Squarefree d₂)
    (hcop : Nat.Coprime d₁ d₂) (hpos : 0 < d₁ * d₂ ^ 2) :
    rho 0 (d₁ * d₂ ^ 2) = d₂ := by
  rw [rho_zero_eq _ hpos, floorRoot_two_mul_sq hs₁ hs₂ hcop]

/-- **Lemma 3.4 of Friedlander–Iwaniec, uniform in the modulus.**  For all
squarefree coprime `d₁, d₂` with `4 ∤ d₁d₂²` one has
`M_d(x) = 4 g(d) κ x^{3/4} + O(h(d₁,d₂) √x)`, with the implied constant absolute.
(The statement of the `Md_cubefree_asymptotic` corollary below specialises this to
a fixed pair; the *uniformity* is what the `prop35` assembly needs.) -/
theorem Md_cubefree_asymptotic_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ d₁ d₂ : ℕ, Squarefree d₁ → Squarefree d₂ →
      Nat.Coprime d₁ d₂ → ¬ 4 ∣ d₁ * d₂ ^ 2 → ∀ x : ℕ, 1 ≤ x →
      |(Md (d₁ * d₂ ^ 2) x : ℝ) - 4 * (gdens (d₁ * d₂ ^ 2) : ℝ)
          * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)|
        ≤ C * (hdens d₁ d₂ : ℝ) * Real.sqrt x := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.Analysis.FriedlanderIwaniec.sum_gcd_class_natSqrt_eq_uniform
  refine ⟨2 * C₀ + 1, by linarith, ?_⟩
  intro d₁ d₂ hs₁ hs₂ hcop h4 x hx
  have h₁0 : d₁ ≠ 0 := hs₁.ne_zero
  have h₂0 : d₂ ≠ 0 := hs₂.ne_zero
  have hm0 : 0 < d₁ * d₂ := Nat.mul_pos (Nat.pos_of_ne_zero h₁0) (Nat.pos_of_ne_zero h₂0)
  have hd0 : 0 < d₁ * d₂ ^ 2 :=
    Nat.mul_pos (Nat.pos_of_ne_zero h₁0) (Nat.pow_pos (Nat.pos_of_ne_zero h₂0))
  have hdR : (0 : ℝ) < ((d₁ * d₂ ^ 2 : ℕ) : ℝ) := by exact_mod_cast hd0
  set K : ℝ := ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) with hK_def
  set Rv : ℕ → ℝ := fun ν => (({α : ZMod ((d₁ * d₂) / ν) | α ^ 2 = -1}.ncard : ℕ) : ℝ)
    with hRv_def
  set Tv : ℕ → ℝ := fun ν => ((Nat.divisors ((d₁ * d₂) / ν)).card : ℝ) with hTv_def
  set T : ℕ → ℝ := fun ν =>
    ∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter
        (fun c => Nat.gcd c (d₁ * d₂) = ν), ((2 * Nat.sqrt (x - c ^ 4) + 1 : ℕ) : ℝ) with hT_def
  set Mv : ℕ → ℝ := fun ν =>
    2 * (Nat.totient ((d₁ * d₂) / ν) : ℝ) * K * (x : ℝ) ^ (3 / 4 : ℝ) / ((d₁ * d₂ : ℕ) : ℝ)
    with hMv_def
  set SV : ℝ := ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) with hSV_def
  set SX : ℝ := Real.sqrt x with hSX_def
  set SXN : ℝ := ((Nat.sqrt x : ℕ) : ℝ) with hSXN_def
  set rhov : ℝ := (({α : ZMod (d₁ * d₂ ^ 2) | α ^ 2 = 0}.ncard : ℕ) : ℝ) with hrhov_def
  have hrhov_nonneg : (0:ℝ) ≤ rhov := by simp only [hrhov_def]; positivity
  set A : ℝ := ∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
      (ν₂ : ℝ) * Rv (ν₁ * ν₂) * T (ν₁ * ν₂) with hA_def
  set B : ℝ := ∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
      (ν₂ : ℝ) * Rv (ν₁ * ν₂) * Mv (ν₁ * ν₂) with hB_def
  set Esum : ℝ := ∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
      (ν₂ : ℝ) * Rv (ν₁ * ν₂) * (C₀ * Tv (ν₁ * ν₂) * SX + C₀ * SV) with hEsum_def
  set Sig : ℝ := ∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
      (ν₂ : ℝ) * Rv (ν₁ * ν₂) * (Tv (ν₁ * ν₂) + 1) with hSig_def
  have hSXnonneg : (0:ℝ) ≤ SX := by rw [hSX_def]; exact Real.sqrt_nonneg _
  have hSVle : SV ≤ SX := by
    rw [hSV_def, hSX_def]
    have h1 : Nat.sqrt (Nat.sqrt x) ≤ Nat.sqrt x := Nat.sqrt_le_sqrt (Nat.sqrt_le_self x)
    have h1' : ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ≤ ((Nat.sqrt x : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 : ((Nat.sqrt x : ℕ) : ℝ) ≤ Real.sqrt x := by
      rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      have hc : (((Nat.sqrt x : ℕ) : ℝ)) ^ 2 = (((Nat.sqrt x : ℕ) ^ 2 : ℕ) : ℝ) := by push_cast; ring
      rw [hc]; exact_mod_cast Nat.sqrt_le' x
    linarith
  have hSXNnonneg : (0:ℝ) ≤ SXN := by rw [hSXN_def]; positivity
  have hSXNleSX : SXN ≤ SX := by
    rw [hSXN_def, hSX_def]
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    have hc : ((Nat.sqrt x : ℕ) : ℝ) ^ 2 = (((Nat.sqrt x : ℕ) ^ 2 : ℕ) : ℝ) := by push_cast; ring
    rw [hc]; exact_mod_cast Nat.sqrt_le' x
  have hrhov_nonneg' : (0:ℝ) ≤ rhov := hrhov_nonneg
  have hgroup := Commons.NumberTheory.FriedlanderIwaniec.MdNum_grouped_by_gcd
    (d₁ := d₁) (d₂ := d₂) (x := x) hs₁ hs₂ hcop h4
  have hgroupR : (MdNum (d₁ * d₂ ^ 2) x : ℝ) = 2 * A + 2 * SXN * rhov := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hgroup
    have hz : rho 0 (d₁ * d₂ ^ 2) = ({α : ZMod (d₁ * d₂ ^ 2) | α ^ 2 = 0}).ncard :=
      rho_zero_eq_sqZero _
    simp only [MdNum, Z, hz, rho, hT_def, hA_def, hRv_def, hSXN_def, hrhov_def] at h ⊢
    push_cast at h ⊢
    rw [show ({α : ZMod (d₁ * d₂ ^ 2) | α ^ 2 + (0 : ZMod (d₁ * d₂ ^ 2)) ^ 2 = 0})
        = ({α : ZMod (d₁ * d₂ ^ 2) | α ^ 2 = 0}) from by congr 1; ext α; simp] at ⊢
    exact h
  have hM : (Md (d₁ * d₂ ^ 2) x : ℝ) = (MdNum (d₁ * d₂ ^ 2) x : ℝ) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) := by
    rw [Md]; push_cast; ring
  have hterm : ∀ ν₁ ∈ Nat.divisors d₁, ∀ ν₂ ∈ Nat.divisors d₂,
      |T (ν₁ * ν₂) - Mv (ν₁ * ν₂)| ≤ C₀ * Tv (ν₁ * ν₂) * SX + C₀ * SV := by
    intro ν₁ hν₁ ν₂ hν₂
    have hdvd₁ : ν₁ ∣ d₁ := (Nat.mem_divisors.mp hν₁).1
    have hdvd₂ : ν₂ ∣ d₂ := (Nat.mem_divisors.mp hν₂).1
    have hpos : 0 < ν₁ * ν₂ :=
      Nat.mul_pos (Nat.pos_of_dvd_of_pos hdvd₁ (Nat.pos_of_ne_zero h₁0))
        (Nat.pos_of_dvd_of_pos hdvd₂ (Nat.pos_of_ne_zero h₂0))
    have hdiv : ν₁ * ν₂ ∣ d₁ * d₂ := Nat.mul_dvd_mul hdvd₁ hdvd₂
    have h := hC₀ (d₁ * d₂) (ν₁ * ν₂) x hm0 hpos hdiv hx
    simp only [hT_def, hMv_def, hK_def, hTv_def, hRv_def, hSV_def, hSX_def] at h ⊢
    exact h
  have hAB : A - B = ∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
      (ν₂ : ℝ) * Rv (ν₁ * ν₂) * (T (ν₁ * ν₂) - Mv (ν₁ * ν₂)) := by
    simp only [hA_def, hB_def]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ν₁ hν₁
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ν₂ hν₂
    ring
  have hkey : |A - B| ≤ Esum := by
    rw [hAB, hEsum_def]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun ν₁ _ => Finset.abs_sum_le_sum_abs _ _)) ?_
    apply Finset.sum_le_sum
    intro ν₁ hν₁
    apply Finset.sum_le_sum
    intro ν₂ hν₂
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ν₂ : ℝ) * Rv (ν₁ * ν₂))]
    exact mul_le_mul_of_nonneg_left (hterm ν₁ hν₁ ν₂ hν₂) (by positivity)
  have hqR : ((d₁ * d₂ ^ 2 : ℕ) : ℝ) * (gdens (d₁ * d₂ ^ 2) : ℝ)
      = ∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
          (ν₂ : ℝ) * Rv (ν₁ * ν₂) *
            (Nat.totient ((d₁ * d₂) / (ν₁ * ν₂)) : ℝ) / ((d₁ * d₂ : ℕ) : ℝ) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (gdens_mul_eq_sum hs₁ hs₂ hcop h4)
    push_cast at h ⊢
    simp only [hRv_def] at ⊢
    exact h
  have hBval : B = 2 * K * (x : ℝ) ^ (3 / 4 : ℝ) *
      (((d₁ * d₂ ^ 2 : ℕ) : ℝ) * (gdens (d₁ * d₂ ^ 2) : ℝ)) := by
    have hfac : (∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
          (ν₂ : ℝ) * Rv (ν₁ * ν₂) * Mv (ν₁ * ν₂))
        = 2 * K * (x : ℝ) ^ (3 / 4 : ℝ) *
            (∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
              (ν₂ : ℝ) * Rv (ν₁ * ν₂) *
                ((Nat.totient ((d₁ * d₂) / (ν₁ * ν₂)) : ℝ) / ((d₁ * d₂ : ℕ) : ℝ))) := by
      simp only [hMv_def]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν₁ hν₁
      apply Finset.sum_congr rfl
      intro ν₂ hν₂
      ring
    rw [hB_def, hfac, hqR]
    congr 1
    apply Finset.sum_congr rfl
    intro ν₁ hν₁
    apply Finset.sum_congr rfl
    intro ν₂ hν₂
    ring
  have hdensSig : (hdens d₁ d₂ : ℝ) = (2 / ((d₁ * d₂ ^ 2 : ℕ) : ℝ)) * Sig := by
    rw [hdens, hSig_def]
    simp only [hRv_def, hTv_def]
    push_cast
    ring
  have hSig_nonneg : (0:ℝ) ≤ Sig := by
    rw [hSig_def]
    apply Finset.sum_nonneg
    intro ν₁ hν₁
    apply Finset.sum_nonneg
    intro ν₂ hν₂
    have h2 : (0:ℝ) ≤ (ν₂ : ℝ) := Nat.cast_nonneg _
    have h3 : (0:ℝ) ≤ Rv (ν₁ * ν₂) := by simp only [hRv_def]; positivity
    have h4 : (0:ℝ) ≤ (Tv (ν₁ * ν₂) + 1) := by simp only [hTv_def]; positivity
    exact mul_nonneg (mul_nonneg h2 h3) h4
  have hEsum_le : Esum ≤ C₀ * SX * Sig := by
    have h1 : Esum ≤ ∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
        (ν₂ : ℝ) * Rv (ν₁ * ν₂) * (C₀ * (Tv (ν₁ * ν₂) + 1) * SX) := by
      rw [hEsum_def]
      apply Finset.sum_le_sum
      intro ν₁ hν₁
      apply Finset.sum_le_sum
      intro ν₂ hν₂
      have hw : (0:ℝ) ≤ (ν₂ : ℝ) * Rv (ν₁ * ν₂) :=
        mul_nonneg (Nat.cast_nonneg _) (by simp only [hRv_def]; positivity)
      have hτ1 : (1:ℝ) ≤ Tv (ν₁ * ν₂) := by
        simp only [hTv_def]
        have hdv : ν₁ * ν₂ ∣ d₁ * d₂ :=
          Nat.mul_dvd_mul (Nat.mem_divisors.mp hν₁).1 (Nat.mem_divisors.mp hν₂).1
        have hposν : 0 < ν₁ * ν₂ :=
          Nat.mul_pos (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hν₁).1 (Nat.pos_of_ne_zero h₁0))
            (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hν₂).1 (Nat.pos_of_ne_zero h₂0))
        have hq : 0 < (d₁ * d₂) / (ν₁ * ν₂) := Nat.div_pos (Nat.le_of_dvd hm0 hdv) hposν
        have hc : 0 < (Nat.divisors ((d₁ * d₂) / (ν₁ * ν₂))).card :=
          Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hq.ne'⟩
        have hc2 : (1:ℕ) ≤ (Nat.divisors ((d₁ * d₂) / (ν₁ * ν₂))).card := hc
        exact_mod_cast hc2
      have hCS : C₀ * SV ≤ C₀ * SX := mul_le_mul_of_nonneg_left hSVle hC₀pos.le
      have key : C₀ * Tv (ν₁ * ν₂) * SX + C₀ * SV ≤ C₀ * (Tv (ν₁ * ν₂) + 1) * SX := by
        nlinarith [hCS, hC₀pos.le, hSXnonneg, hτ1]
      exact mul_le_mul_of_nonneg_left key hw
    have h2 : (∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
        (ν₂ : ℝ) * Rv (ν₁ * ν₂) * (C₀ * (Tv (ν₁ * ν₂) + 1) * SX)) = C₀ * SX * Sig := by
      rw [hSig_def]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν₁ hν₁
      apply Finset.sum_congr rfl
      intro ν₂ hν₂
      ring
    exact h1.trans h2.le
  have hE : 2 * Esum / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) ≤ C₀ * (hdens d₁ d₂ : ℝ) * SX := by
    have h1 : 2 * Esum / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) ≤ 2 * (C₀ * SX * Sig) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hdR.le
      linarith [hEsum_le]
    have h2 : 2 * (C₀ * SX * Sig) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ)
        = C₀ * ((2 / ((d₁ * d₂ ^ 2 : ℕ) : ℝ)) * Sig) * SX := by
      field_simp
    rw [hdensSig]
    exact h1.trans h2.le
  have hρ0val : rhov = (d₂ : ℝ) := by
    simp only [hrhov_def]
    have h : ({α : ZMod (d₁ * d₂ ^ 2) | α ^ 2 = 0}).ncard = d₂ := by
      rw [← rho_zero_eq_sqZero]
      exact rho_zero_cubefree hs₁ hs₂ hcop hd0
    rw [h]
  have hSig_ge : 2 * (d₂ : ℝ) ≤ Sig := by
    rw [hSig_def]
    have hmem₁ : d₁ ∈ Nat.divisors d₁ := Nat.mem_divisors.mpr ⟨dvd_rfl, h₁0⟩
    have hmem₂ : d₂ ∈ Nat.divisors d₂ := Nat.mem_divisors.mpr ⟨dvd_rfl, h₂0⟩
    have hinner : ∀ ν₁ ∈ Nat.divisors d₁, ∀ ν₂ ∈ Nat.divisors d₂,
        (0:ℝ) ≤ (ν₂ : ℝ) * Rv (ν₁ * ν₂) * (Tv (ν₁ * ν₂) + 1) := by
      intro ν₁ _ ν₂ _
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by simp only [hRv_def]; positivity))
        (by simp only [hTv_def]; positivity)
    have h2 := Finset.single_le_sum (fun ν₂ hν₂ => hinner d₁ hmem₁ ν₂ hν₂) hmem₂
    have h1 := Finset.single_le_sum
      (fun ν₁ hν₁ => Finset.sum_nonneg (fun ν₂ hν₂ => hinner ν₁ hν₁ ν₂ hν₂)) hmem₁
    have hval : (d₂ : ℝ) * Rv (d₁ * d₂) * (Tv (d₁ * d₂) + 1) = 2 * (d₂ : ℝ) := by
      have hdiv : (d₁ * d₂) / (d₁ * d₂) = 1 := Nat.div_self hm0
      have hRv1 : Rv (d₁ * d₂) = 1 := by
        have h : (({α : ZMod 1 | α ^ 2 = -1}.ncard : ℕ) : ℝ) = 1 := by
          rw [Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_one]
          norm_num
        simp only [hRv_def]
        rw [hdiv]
        exact h
      have hTv1 : Tv (d₁ * d₂) = 1 := by
        simp only [hTv_def, hdiv, Nat.divisors_one, Finset.card_singleton]
        norm_num
      rw [hRv1, hTv1]
      ring
    rw [hval] at h2
    exact h2.trans h1
  have hge : (4 : ℝ) * (d₂ : ℝ) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) ≤ (hdens d₁ d₂ : ℝ) := by
    have h1 : (4 : ℝ) * (d₂ : ℝ) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) ≤ 2 * Sig / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hdR.le
      have h4 : (4 : ℝ) * (d₂ : ℝ) ≤ 2 * Sig := by linarith [hSig_ge]
      linarith [h4]
    have h2 : 2 * Sig / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) = (2 / ((d₁ * d₂ ^ 2 : ℕ) : ℝ)) * Sig := by ring
    rw [hdensSig]
    exact h1.trans h2.le
  have hρ0 : 2 * (SXN * rhov) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) ≤ (hdens d₁ d₂ : ℝ) * SXN := by
    rw [hρ0val]
    have h2d : 2 * (SXN * (d₂ : ℝ)) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ)
        ≤ (4 : ℝ) * (d₂ : ℝ) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) * SXN := by
      rw [div_le_iff₀ hdR]
      rw [show (4 : ℝ) * (d₂ : ℝ) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) * SXN * ((d₁ * d₂ ^ 2 : ℕ) : ℝ)
          = 4 * ((d₂ : ℝ) * SXN) from by field_simp]
      have h2 : (2:ℝ) * (SXN * (d₂:ℝ)) ≤ 4 * (SXN * (d₂:ℝ)) :=
        mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ) ≤ 4) (by positivity)
      rw [mul_comm (d₂ : ℝ) SXN]
      exact h2
    have h3 := mul_le_mul_of_nonneg_right hge hSXNnonneg
    exact h2d.trans h3
  have hcore : |(2 * A + 2 * (SXN * rhov)) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ)
        - 4 * (gdens (d₁ * d₂ ^ 2) : ℝ) * K * (x : ℝ) ^ (3 / 4 : ℝ)|
      ≤ 2 * Esum / ((d₁ * d₂ ^ 2 : ℕ) : ℝ)
        + 2 * (SXN * rhov) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) := by
    have hB2 : 2 * B / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) =
        4 * (gdens (d₁ * d₂ ^ 2) : ℝ) * K * (x : ℝ) ^ (3 / 4 : ℝ) := by
      rw [hBval]; field_simp; ring
    have heq : (2 * A + 2 * (SXN * rhov)) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ)
          - 4 * (gdens (d₁ * d₂ ^ 2) : ℝ) * K * (x : ℝ) ^ (3 / 4 : ℝ)
        = (2 * (A - B) + 2 * (SXN * rhov)) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) := by
      rw [← hB2]; ring
    rw [heq, abs_div, abs_of_nonneg (le_of_lt hdR)]
    rw [div_le_iff₀ hdR]
    have hexp : (2 * Esum / ((d₁ * d₂ ^ 2 : ℕ) : ℝ)
          + 2 * (SXN * rhov) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ)) * ((d₁ * d₂ ^ 2 : ℕ) : ℝ)
        = 2 * Esum + 2 * (SXN * rhov) := by
      field_simp
    rw [hexp]
    have htri : |2 * (A - B) + 2 * (SXN * rhov)| ≤ 2 * Esum + 2 * (SXN * rhov) := by
      have h1 : 2 * (A - B) + 2 * (SXN * rhov) = 2 * ((A - B) + SXN * rhov) := by ring
      rw [h1, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have h2 : |(A - B) + SXN * rhov| ≤ |A - B| + |SXN * rhov| := abs_add_le _ _
      have h3 : |SXN * rhov| = SXN * rhov := abs_of_nonneg (mul_nonneg hSXNnonneg hrhov_nonneg)
      rw [h3] at h2
      linarith [h2, hkey]
    exact htri
  calc |(Md (d₁ * d₂ ^ 2) x : ℝ) - 4 * (gdens (d₁ * d₂ ^ 2) : ℝ)
        * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)|
      = |(Md (d₁ * d₂ ^ 2) x : ℝ) - 4 * (gdens (d₁ * d₂ ^ 2) : ℝ) * K * (x : ℝ) ^ (3 / 4 : ℝ)| := by
        rw [hK_def]
    _ = |(2 * A + 2 * (SXN * rhov)) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ)
          - 4 * (gdens (d₁ * d₂ ^ 2) : ℝ) * K * (x : ℝ) ^ (3 / 4 : ℝ)| := by
        rw [hM, hgroupR]
        congr 1
        ring_nf
    _ ≤ 2 * Esum / ((d₁ * d₂ ^ 2 : ℕ) : ℝ)
        + 2 * (SXN * rhov) / ((d₁ * d₂ ^ 2 : ℕ) : ℝ) := hcore
    _ ≤ C₀ * (hdens d₁ d₂ : ℝ) * SX + (hdens d₁ d₂ : ℝ) * SXN := add_le_add hE hρ0
    _ ≤ (2 * C₀ + 1) * (hdens d₁ d₂ : ℝ) * (Real.sqrt x) := by
        have hhd : (0:ℝ) ≤ (hdens d₁ d₂ : ℝ) := by
          rw [hdensSig]
          exact mul_nonneg (by positivity) hSig_nonneg
        have hp : (hdens d₁ d₂ : ℝ) * SXN ≤ (hdens d₁ d₂ : ℝ) * SX :=
          mul_le_mul_of_nonneg_left hSXNleSX hhd
        have h3 : (0:ℝ) ≤ C₀ * (hdens d₁ d₂ : ℝ) * SX := by positivity
        have key : C₀ * (hdens d₁ d₂ : ℝ) * SX + (hdens d₁ d₂ : ℝ) * SXN
            ≤ (2 * C₀ + 1) * (hdens d₁ d₂ : ℝ) * SX := by
          nlinarith [hp, hhd, h3, hC₀pos.le, hSXnonneg]
        calc C₀ * (hdens d₁ d₂ : ℝ) * SX + (hdens d₁ d₂ : ℝ) * SXN
            ≤ (2 * C₀ + 1) * (hdens d₁ d₂ : ℝ) * SX := key
          _ = (2 * C₀ + 1) * (hdens d₁ d₂ : ℝ) * (Real.sqrt x) := by rw [hSX_def]


/-- Lemma 3.4 in its original (fixed-modulus) form, deduced from the uniform version. -/
theorem Md_cubefree_asymptotic {d₁ d₂ : ℕ} (hs₁ : Squarefree d₁) (hs₂ : Squarefree d₂)
    (hcop : Nat.Coprime d₁ d₂) (h4 : ¬ 4 ∣ d₁ * d₂ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
      |(Md (d₁ * d₂ ^ 2) x : ℝ) - 4 * (gdens (d₁ * d₂ ^ 2) : ℝ)
          * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ (3 / 4 : ℝ)|
        ≤ C * (hdens d₁ d₂ : ℝ) * Real.sqrt x := by
  obtain ⟨C, hC, h⟩ := Md_cubefree_asymptotic_uniform
  exact ⟨C, hC, fun x hx => h d₁ d₂ hs₁ hs₂ hcop h4 x hx⟩

end Submission


set_option maxHeartbeats 4000000

/-!
# §3 of Friedlander–Iwaniec, part 2: the smoothing step (3.10)

This file continues `Submission/S3.lean`.  Its content is the first ingredient of
Lemma 3.1 of the paper: the "trivial estimation" comparing the sharp congruence
sum `A_d(x)` with its smoothed version `A_d(f)`.

Given a weight `f : ℕ → ℝ` with `0 ≤ f ≤ 1`, equal to `1` up to `x - y`, the
difference is supported on the shell `x - y < n ≤ x`, and summing over `d ≤ D`
produces the divisor function `τ(n)`:

  `∑_{d ≤ D} |A_d(x) - A_d(f)| ≤ ∑_{x-y < n ≤ x} a_n τ(n) ≤ x^ε (A(x) - A(x-y))`,
  `≪_ε x^ε (y x^{-1/4} + √x)`,

i.e. the paper's (3.10) (with the harmless `√x` boundary term which is dominated
by `y x^{-1/4}` in the range of application, `x^{1/2} < y < x`).
-/

namespace Submission

open Finset

/-- The smoothed congruence sum `A_d(f) = ∑_{n ≤ x, d | n} a_n f(n)`. -/
noncomputable def AdF (f : ℕ → ℝ) (d x : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n), (an n : ℝ) * f n

/-- **(3.10)**: smoothing the congruence sum changes it by at most
`x^ε (y x^{-1/4} + √x)` on average over `d ≤ D`. -/
theorem Ad_smooth_diff_le (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ D x y : ℕ, 1 ≤ D → 1 ≤ x → y ≤ x / 2 →
      ∀ f : ℕ → ℝ, (∀ n, n ≤ x → 0 ≤ f n) → (∀ n, n ≤ x → f n ≤ 1) →
      (∀ n, n ≤ x - y → f n = 1) →
      ∑ d ∈ Finset.Icc 1 D, |(Ad d x : ℝ) - AdF f d x|
        ≤ C * (x : ℝ) ^ eps * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + Real.sqrt x) := by
  obtain ⟨Cτ, hCτpos, hCτ⟩ :=
    Commons.NumberTheory.ArithmeticFunction.card_divisors_le_rpow eps heps
  obtain ⟨Cs, hCspos, hCs⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.shell_count_intpairs
  refine ⟨Cτ * Cs, mul_pos hCτpos hCspos, ?_⟩
  intro D x y hD hx hy f hf0 hf1 hfeq
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hyx : y ≤ x := by omega
  -- the difference, for a fixed `d`, is a sum of nonnegative terms
  have step1 : ∀ d : ℕ, |(Ad d x : ℝ) - AdF f d x|
      = ∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n), (an n : ℝ) * (1 - f n) := by
    intro d
    have hcast : (Ad d x : ℝ)
        = ∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n), (an n : ℝ) := by
      rw [Ad]; push_cast; rfl
    have hdiff : (Ad d x : ℝ) - AdF f d x
        = ∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n), (an n : ℝ) * (1 - f n) := by
      rw [hcast, AdF, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [hdiff]
    apply Finset.abs_sum_of_nonneg
    intro n hn
    have hnx : n ≤ x := by
      have h := (Finset.mem_filter.mp hn).1
      simp only [Finset.mem_range] at h
      omega
    exact mul_nonneg (by positivity) (by linarith [hf1 n hnx])
  -- bound the terms by the indicator of the shell
  have step2 : ∑ d ∈ Finset.Icc 1 D, ∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n),
        (an n : ℝ) * (1 - f n)
      ≤ ∑ d ∈ Finset.Icc 1 D, ∑ n ∈ Finset.range (x + 1),
          (if d ∣ n then (an n : ℝ) * (if x - y < n then (1 : ℝ) else 0) else 0) := by
    apply Finset.sum_le_sum
    intro d _
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro n hn
    by_cases hd : d ∣ n
    · simp only [hd, if_true]
      by_cases hsh : x - y < n
      · simp only [hsh, if_true, mul_one]
        have hnx : n ≤ x := by
          simp only [Finset.mem_range] at hn; omega
        have h1 : (1 : ℝ) - f n ≤ 1 := by linarith [hf0 n hnx]
        have h2 : (0 : ℝ) ≤ (an n : ℝ) := by positivity
        exact mul_le_of_le_one_right h2 h1
      · simp only [hsh, if_false, mul_zero]
        have hnx : n ≤ x := by
          simp only [Finset.mem_range] at hn; omega
        have hf1' : f n = 1 := hfeq n (by omega)
        simp [hf1']
    · simp only [hd, if_false]
      exact le_refl 0
  -- swap the order of summation
  have step3 : ∑ d ∈ Finset.Icc 1 D, ∑ n ∈ Finset.range (x + 1),
          (if d ∣ n then (an n : ℝ) * (if x - y < n then (1 : ℝ) else 0) else 0)
      = ∑ n ∈ Finset.range (x + 1),
          (an n : ℝ) * (if x - y < n then (1 : ℝ) else 0)
            * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  -- bound the number of divisors
  have step4 : ∑ n ∈ Finset.range (x + 1),
        (an n : ℝ) * (if x - y < n then (1 : ℝ) else 0)
          * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
      ≤ (Cτ * (x : ℝ) ^ eps) * ((Aseq x : ℝ) - (Aseq (x - y) : ℝ)) := by
    have hpt : ∀ n ∈ Finset.range (x + 1),
        (an n : ℝ) * (if x - y < n then (1 : ℝ) else 0)
          * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
        ≤ (Cτ * (x : ℝ) ^ eps) * ((an n : ℝ) * (if x - y < n then (1 : ℝ) else 0)) := by
      intro n hn
      have hnx : n ≤ x := by simp only [Finset.mem_range] at hn; omega
      by_cases hsh : x - y < n
      · simp only [hsh, if_true, mul_one]
        have hn1 : 1 ≤ n := by omega
        have hsub : ((Finset.Icc 1 D).filter (fun d => d ∣ n)).card ≤ (Nat.divisors n).card := by
          apply Finset.card_le_card
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
          rw [Nat.mem_divisors]
          exact ⟨hd.2, by omega⟩
        have hcard : (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
            ≤ Cτ * (x : ℝ) ^ eps := by
          refine le_trans (by exact_mod_cast hsub) (le_trans (hCτ n hn1) ?_)
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hCτpos)
          exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnx) (le_of_lt heps)
        have hnn : (0 : ℝ) ≤ (an n : ℝ) := by positivity
        calc (an n : ℝ) * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
            ≤ (an n : ℝ) * (Cτ * (x : ℝ) ^ eps) := mul_le_mul_of_nonneg_left hcard hnn
          _ = (Cτ * (x : ℝ) ^ eps) * (an n : ℝ) := by ring
      · simp only [hsh, if_false, mul_zero, zero_mul]
        exact le_refl 0
    have hshell : ∑ n ∈ Finset.range (x + 1),
          (an n : ℝ) * (if x - y < n then (1 : ℝ) else 0)
        = (Aseq x : ℝ) - (Aseq (x - y) : ℝ) := by
      have h1 : ∀ n, (an n : ℝ) * (if x - y < n then (1 : ℝ) else 0)
          = if x - y < n then (an n : ℝ) else 0 := by
        intro n; split <;> simp
      simp only [h1]
      rw [← Finset.sum_filter]
      have hset : (Finset.range (x + 1)).filter (fun n => x - y < n)
          = (Finset.range (x + 1)) \ (Finset.range (x - y + 1)) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
        omega
      rw [hset, eq_sub_iff_add_eq, Aseq, Aseq]
      push_cast
      exact Finset.sum_sdiff (Finset.range_mono (Nat.succ_le_succ (Nat.sub_le x y)))
    calc ∑ n ∈ Finset.range (x + 1),
            (an n : ℝ) * (if x - y < n then (1 : ℝ) else 0)
              * (((Finset.Icc 1 D).filter (fun d => d ∣ n)).card : ℝ)
        ≤ ∑ n ∈ Finset.range (x + 1),
            (Cτ * (x : ℝ) ^ eps) * ((an n : ℝ) * (if x - y < n then (1 : ℝ) else 0)) :=
          Finset.sum_le_sum hpt
      _ = (Cτ * (x : ℝ) ^ eps)
            * ∑ n ∈ Finset.range (x + 1), (an n : ℝ) * (if x - y < n then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
      _ = (Cτ * (x : ℝ) ^ eps) * ((Aseq x : ℝ) - (Aseq (x - y) : ℝ)) := by
          rw [hshell]
  -- combine
  have hkey : ∑ d ∈ Finset.Icc 1 D, |(Ad d x : ℝ) - AdF f d x|
      ≤ (Cτ * (x : ℝ) ^ eps) * ((Aseq x : ℝ) - (Aseq (x - y) : ℝ)) := by
    calc ∑ d ∈ Finset.Icc 1 D, |(Ad d x : ℝ) - AdF f d x|
        = ∑ d ∈ Finset.Icc 1 D, ∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n),
            (an n : ℝ) * (1 - f n) := Finset.sum_congr rfl (fun d _ => step1 d)
      _ ≤ _ := le_trans step2 (le_trans (le_of_eq step3) step4)
  -- the shell count
  have hAseq : (Aseq x : ℝ) - (Aseq (x - y) : ℝ)
      ≤ Cs * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + Real.sqrt x) := by
    rw [Aseq_eq_ncard x, Aseq_eq_ncard (x - y)]
    exact hCs x y hx hy
  have hCτxpos : 0 < Cτ * (x : ℝ) ^ eps := by
    exact mul_pos hCτpos (Real.rpow_pos_of_pos (by linarith) _)
  calc ∑ d ∈ Finset.Icc 1 D, |(Ad d x : ℝ) - AdF f d x|
      ≤ (Cτ * (x : ℝ) ^ eps) * ((Aseq x : ℝ) - (Aseq (x - y) : ℝ)) := hkey
    _ ≤ (Cτ * (x : ℝ) ^ eps) * (Cs * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + Real.sqrt x)) :=
        mul_le_mul_of_nonneg_left hAseq (le_of_lt hCτxpos)
    _ = Cτ * Cs * (x : ℝ) ^ eps
          * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + Real.sqrt x) := by ring

end Submission


namespace Submission

/-! ### The comparison of the smoothed integral with the sharp count

The paper's (3.12) uses the estimate `2I(0,b;d) = ∑_{a²+b²≤x}1 + O(y(x+y-b²)^{-1/2})`
for the `k = 0` Fourier integral.  We only need the comparison with the real number
`2√(x - b²)`: the `+1` in the count contributes an unavoidable `O(1)` per `b`,
which is harmless for our purposes (it is summed against `ρ(b;d)/d`).
-/

theorem integral_vs_sqrt_local (f : ℝ → ℝ) (x y b : ℕ) (hf : Continuous f)
    (hf0 : ∀ u, 0 ≤ f u) (hf1 : ∀ u, f u ≤ 1)
    (hfeq : ∀ u, u ≤ (x : ℝ) - (y : ℝ) → f u = 1)
    (hfz : ∀ u, (x : ℝ) ≤ u → f u = 0) (hb : b ≤ Nat.sqrt x) :
    |2 * (∫ t in Set.Ici (0 : ℝ), f (t ^ 2 + (b : ℝ) ^ 2))
        - 2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 2)|
      ≤ 3 * (y : ℝ) * ((x : ℝ) + (y : ℝ) - (b : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) := by
  rcases eq_or_ne y 0 with hy0 | hyne
  · -- `y = 0` makes the hypotheses contradictory
    exfalso
    have h1 : f (x : ℝ) = 1 := hfeq _ (by simp [hy0])
    have h2 : f (x : ℝ) = 0 := hfz _ le_rfl
    rw [h1] at h2; norm_num at h2
  have hypos : 0 < (y : ℝ) := by
    have : 0 < y := Nat.pos_of_ne_zero hyne
    exact_mod_cast this
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := le_of_lt hypos
  have hb2 : b ^ 2 ≤ x := by have := (Nat.le_sqrt).mp hb; simpa [pow_two] using this
  have hb2R : (b : ℝ) ^ 2 ≤ (x : ℝ) := by exact_mod_cast hb2
  set R : ℝ := Real.sqrt ((x : ℝ) - (b : ℝ) ^ 2) with hRdef
  set D : ℝ := (x : ℝ) + (y : ℝ) - (b : ℝ) ^ 2 with hDdef
  set R' : ℝ := Real.sqrt (max 0 ((x : ℝ) - (y : ℝ) - (b : ℝ) ^ 2)) with hR'def
  have hR2 : R ^ 2 = (x : ℝ) - (b : ℝ) ^ 2 := by
    rw [hRdef]; exact Real.sq_sqrt (by linarith)
  have hRnn : 0 ≤ R := by rw [hRdef]; exact Real.sqrt_nonneg _
  have hR'nn : 0 ≤ R' := by rw [hR'def]; exact Real.sqrt_nonneg _
  have hDpos : 0 < D := by rw [hDdef]; linarith
  have hR'le : R' ≤ R := by
    rw [hR'def, hRdef]
    apply Real.sqrt_le_sqrt
    rw [max_le_iff]
    exact ⟨by linarith, by linarith⟩
  have hgcont : Continuous (fun t : ℝ => f (t ^ 2 + (b : ℝ) ^ 2)) := hf.comp (by continuity)
  -- Step 1: replace the integral over `[0,∞)` by the one over `[0,R]`
  have hIci_Icc : (∫ t in Set.Ici (0 : ℝ), f (t ^ 2 + (b : ℝ) ^ 2))
      = ∫ t in Set.Icc (0 : ℝ) R, f (t ^ 2 + (b : ℝ) ^ 2) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ici,
        ← MeasureTheory.integral_indicator measurableSet_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Set.Ici (0 : ℝ)
    · rw [Set.indicator_of_mem ht]
      by_cases htR : t ≤ R
      · rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨ht, htR⟩)]
      · rw [Set.indicator_of_notMem (fun hh => htR hh.2)]
        have ht' : R < t := lt_of_not_ge htR
        have hx : (x : ℝ) ≤ t ^ 2 + (b : ℝ) ^ 2 := by
          have hsq : R ^ 2 < t ^ 2 := by nlinarith
          rw [hR2] at hsq; linarith
        exact hfz _ hx
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (fun hh => ht hh.1)]
  have hIcc_int : (∫ t in Set.Icc (0 : ℝ) R, f (t ^ 2 + (b : ℝ) ^ 2))
      = ∫ t in (0 : ℝ)..R, f (t ^ 2 + (b : ℝ) ^ 2) := by
    rw [intervalIntegral.integral_of_le hRnn]
    exact MeasureTheory.integral_Icc_eq_integral_Ioc
  -- Step 2: upper bound
  have hub : (∫ t in (0 : ℝ)..R, f (t ^ 2 + (b : ℝ) ^ 2)) ≤ R := by
    calc (∫ t in (0 : ℝ)..R, f (t ^ 2 + (b : ℝ) ^ 2))
        ≤ ∫ t in (0 : ℝ)..R, (1 : ℝ) :=
          intervalIntegral.integral_mono_on hRnn (hgcont.intervalIntegrable 0 R)
            (continuous_const.intervalIntegrable 0 R) (fun t _ => hf1 _)
      _ = R := by rw [intervalIntegral.integral_const]; simp
  -- Step 3: lower bound
  have hlb : R' ≤ ∫ t in (0 : ℝ)..R, f (t ^ 2 + (b : ℝ) ^ 2) := by
    rcases lt_or_ge (0 : ℝ) ((x : ℝ) - (y : ℝ) - (b : ℝ) ^ 2) with h | h
    · have hR'val : R' = Real.sqrt ((x : ℝ) - (y : ℝ) - (b : ℝ) ^ 2) := by
        rw [hR'def, max_eq_right h.le]
      have hR'2 : R' ^ 2 = (x : ℝ) - (y : ℝ) - (b : ℝ) ^ 2 := by
        rw [hR'val]; exact Real.sq_sqrt h.le
      have hmono : (∫ t in (0 : ℝ)..R', f (t ^ 2 + (b : ℝ) ^ 2))
          ≤ ∫ t in (0 : ℝ)..R, f (t ^ 2 + (b : ℝ) ^ 2) :=
        intervalIntegral.integral_mono_interval (le_refl 0) hR'nn hR'le
          (Filter.Eventually.of_forall fun t => hf0 _) (hgcont.intervalIntegrable 0 R)
      have h1 : R' ≤ ∫ t in (0 : ℝ)..R', f (t ^ 2 + (b : ℝ) ^ 2) := by
        calc R' = ∫ t in (0 : ℝ)..R', (1 : ℝ) := by
              rw [intervalIntegral.integral_const]; simp
          _ ≤ ∫ t in (0 : ℝ)..R', f (t ^ 2 + (b : ℝ) ^ 2) := by
              apply intervalIntegral.integral_mono_on hR'nn
                (continuous_const.intervalIntegrable 0 R')
                (hgcont.intervalIntegrable 0 R')
              intro t ht
              have ht2 : t ^ 2 ≤ (x : ℝ) - (y : ℝ) - (b : ℝ) ^ 2 := by
                calc t ^ 2 ≤ R' ^ 2 := by nlinarith [ht.1, ht.2]
                  _ = (x : ℝ) - (y : ℝ) - (b : ℝ) ^ 2 := hR'2
              rw [hfeq _ (by linarith : t ^ 2 + (b : ℝ) ^ 2 ≤ (x : ℝ) - (y : ℝ))]
      linarith
    · have hR'val : R' = 0 := by rw [hR'def, max_eq_left h, Real.sqrt_zero]
      rw [hR'val]
      exact intervalIntegral.integral_nonneg hRnn (fun t _ => hf0 _)
  -- Step 4: combine
  have hInt : (∫ t in Set.Ici (0 : ℝ), f (t ^ 2 + (b : ℝ) ^ 2))
      = ∫ t in (0 : ℝ)..R, f (t ^ 2 + (b : ℝ) ^ 2) := hIci_Icc.trans hIcc_int
  rw [hInt]
  set I : ℝ := ∫ t in (0 : ℝ)..R, f (t ^ 2 + (b : ℝ) ^ 2) with hIdef
  have hIle : I ≤ R := hub
  have hIge : R' ≤ I := hlb
  have habs : |2 * I - 2 * R| = 2 * R - 2 * I := by
    have h : (2 : ℝ) * I - 2 * R ≤ 0 := by linarith [hIle]
    rw [abs_of_nonpos h]; ring
  rw [habs]
  have hmain : 2 * R - 2 * I ≤ 2 * (R - R') := by linarith
  refine le_trans hmain ?_
  -- the arithmetic
  have hDinv : D ^ (-(1 / 2 : ℝ)) = (Real.sqrt D)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hDpos), Real.sqrt_eq_rpow]
  rcases lt_or_ge (0 : ℝ) ((x : ℝ) - (y : ℝ) - (b : ℝ) ^ 2) with h | h
  · have hR'val : R' = Real.sqrt ((x : ℝ) - (y : ℝ) - (b : ℝ) ^ 2) := by
      rw [hR'def, max_eq_right h.le]
    have hR'2 : R' ^ 2 = (x : ℝ) - (y : ℝ) - (b : ℝ) ^ 2 := by
      rw [hR'val]; exact Real.sq_sqrt h.le
    have hRpos : 0 < R := by rw [hRdef]; exact Real.sqrt_pos.mpr (by linarith)
    have hRP : 0 < R + R' := by linarith
    have hfac : (R - R') * (R + R') = (y : ℝ) := by nlinarith [hR2, hR'2]
    have hquot : R - R' = (y : ℝ) / (R + R') := by
      rw [eq_div_iff (ne_of_gt hRP)]; exact hfac
    have hbound : R - R' ≤ (y : ℝ) / R := by
      rw [hquot]
      exact div_le_div_of_nonneg_left hy0 hRpos (by linarith)
    have hsq : D ≤ 2 * ((x : ℝ) - (b : ℝ) ^ 2) := by rw [hDdef]; linarith
    have hsqrt : Real.sqrt D ≤ Real.sqrt 2 * R := by
      have h' := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← hRdef] at h'
      exact h'
    have hsqrtpos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDpos
    have hstep : (y : ℝ) / R ≤ Real.sqrt 2 * (y : ℝ) * D ^ (-(1 / 2 : ℝ)) := by
      rw [hDinv, ← div_eq_mul_inv, div_le_iff₀ hRpos]
      rw [show Real.sqrt 2 * (y : ℝ) / Real.sqrt D * R
            = (Real.sqrt 2 * (y : ℝ) * R) / Real.sqrt D by ring]
      rw [le_div_iff₀ hsqrtpos]
      nlinarith [hsqrt, hy0]
    have hfin : 2 * (R - R') ≤ 3 * (y : ℝ) * D ^ (-(1 / 2 : ℝ)) := by
      have h1 : R - R' ≤ Real.sqrt 2 * ((y : ℝ) * D ^ (-(1 / 2 : ℝ))) := by
        rw [← mul_assoc]; exact le_trans hbound hstep
      have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      have h4 : 2 * Real.sqrt 2 ≤ 3 := by nlinarith [hs2, Real.sqrt_nonneg 2]
      have hDn : 0 ≤ D ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (le_of_lt hDpos) _
      have ht : 0 ≤ (y : ℝ) * D ^ (-(1 / 2 : ℝ)) := mul_nonneg hy0 hDn
      calc 2 * (R - R') ≤ 2 * (Real.sqrt 2 * ((y : ℝ) * D ^ (-(1 / 2 : ℝ)))) := by linarith [h1]
        _ = (2 * Real.sqrt 2) * ((y : ℝ) * D ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ 3 * ((y : ℝ) * D ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_right h4 ht
        _ = 3 * (y : ℝ) * D ^ (-(1 / 2 : ℝ)) := by ring
    exact hfin
  · have hR'val : R' = 0 := by rw [hR'def, max_eq_left h, Real.sqrt_zero]
    have hRy : R ≤ Real.sqrt (y : ℝ) := by
      rw [hRdef]
      exact Real.sqrt_le_sqrt (by linarith)
    have hsq : D ≤ 2 * (y : ℝ) := by rw [hDdef]; linarith
    have hsq2 : Real.sqrt D ≤ Real.sqrt 2 * Real.sqrt (y : ℝ) := by
      have h' := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h'
    have hstep : 2 * (R - R') ≤ 3 * (y : ℝ) * D ^ (-(1 / 2 : ℝ)) := by
      rw [hR'val, sub_zero, hDinv, ← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.mpr hDpos)]
      have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      have h4 : 2 * Real.sqrt 2 ≤ 3 := by nlinarith [hs2, Real.sqrt_nonneg 2]
      have hyy : Real.sqrt (y : ℝ) ^ 2 = (y : ℝ) := Real.sq_sqrt hy0
      have h1 : R * Real.sqrt D ≤ Real.sqrt (y : ℝ) * Real.sqrt D :=
        mul_le_mul_of_nonneg_right hRy (Real.sqrt_nonneg D)
      have h2 : Real.sqrt (y : ℝ) * Real.sqrt D
          ≤ Real.sqrt (y : ℝ) * (Real.sqrt 2 * Real.sqrt (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq2 (Real.sqrt_nonneg (y : ℝ))
      have h3 : Real.sqrt (y : ℝ) * (Real.sqrt 2 * Real.sqrt (y : ℝ)) = Real.sqrt 2 * (y : ℝ) := by
        calc Real.sqrt (y : ℝ) * (Real.sqrt 2 * Real.sqrt (y : ℝ))
            = Real.sqrt 2 * (Real.sqrt (y : ℝ)) ^ 2 := by ring
          _ = Real.sqrt 2 * (y : ℝ) := by rw [hyy]
      calc 2 * R * Real.sqrt D = 2 * (R * Real.sqrt D) := by ring
        _ ≤ 2 * (Real.sqrt (y : ℝ) * Real.sqrt D) := by linarith [h1]
        _ ≤ 2 * (Real.sqrt (y : ℝ) * (Real.sqrt 2 * Real.sqrt (y : ℝ))) := by linarith [h2]
        _ = 2 * (Real.sqrt 2 * (y : ℝ)) := by rw [h3]
        _ = (2 * Real.sqrt 2) * (y : ℝ) := by ring
        _ ≤ 3 * (y : ℝ) := mul_le_mul_of_nonneg_right h4 hy0
    exact hstep

end Submission


set_option maxHeartbeats 4000000

/-!
# §3 of Friedlander–Iwaniec, part 3: the main term difference (3.12)

This file proves the second ingredient of Lemma 3.1: the comparison between the
expected main term `M_d(x)` and its smoothed version
`M_d(f) = (2/d) ∑_b Z(b) ρ(b;d) ∫₀^∞ f(t²+b²) dt`.

The paper's displayed estimate `M_d(f) − M_d(x) ≪ (y/d) ∑_{c⁴≤x} ρ(c²;d)(x+y−c⁴)^{−1/2}`
is not literally correct (the rounding error `2√(x−b²) − (2⌊√(x−b²)⌋+1)` is bounded
but not small); we prove the corrected version

  `∑_{d≤D} |M_d(f) − M_d(x)| ≪ (log 2D)^6 ( y x^{-1/4} + x^{1/4} + y x^{-1/2} ) + √D`,

valid for `x ≤ y²` (which holds in the application, where `y = D^{1/4}x^{13/16}`).
-/

namespace Submission

open Finset MeasureTheory intervalIntegral

/-- The `k = 0` Fourier integral `I(0,b;d) = ∫₀^∞ f(t²+b²) dt` (independent of `d`). -/
noncomputable def I0 (f : ℝ → ℝ) (b : ℕ) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ), f (t ^ 2 + (b : ℝ) ^ 2)

/-- The sharp count `2⌊√(x−b²)⌋ + 1` of integers `a` with `a² + b² ≤ x`. -/
noncomputable def sqrtTerm (x b : ℕ) : ℝ := 2 * (Nat.sqrt (x - b ^ 2) : ℝ) + 1

/-- The smoothed main term `M_d(f)`. -/
noncomputable def MdF (f : ℝ → ℝ) (d x : ℕ) : ℝ :=
  (2 / (d : ℝ)) * ∑ b ∈ Finset.range (Nat.sqrt x + 1),
      (Z b : ℝ) * (rho b d : ℝ) * I0 f b

/-- The rounding error of the sharp count. -/
lemma abs_sqrt_sub_floor (m : ℕ) :
    |2 * Real.sqrt m - (2 * (Nat.sqrt m : ℝ) + 1)| ≤ 2 := by
  have hsq : ((Nat.sqrt m : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) := by
    have h := (Nat.le_sqrt').mp (le_refl (Nat.sqrt m))
    exact_mod_cast h
  have h1 : (Nat.sqrt m : ℝ) ≤ Real.sqrt m := by
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (Nat.cast_nonneg _)] at this
  have h2 : Real.sqrt m < (Nat.sqrt m : ℝ) + 1 := by
    have hlt : m < (Nat.sqrt m + 1) ^ 2 := by
      have := (Nat.sqrt_lt').mp (Nat.lt_succ_self (Nat.sqrt m))
      simpa using this
    have hltR : (m : ℝ) < ((Nat.sqrt m : ℝ) + 1) ^ 2 := by exact_mod_cast hlt
    exact (Real.sqrt_lt' (x := (m : ℝ))
      (by positivity : (0:ℝ) < (Nat.sqrt m : ℝ) + 1)).mpr hltR
  rw [abs_le]; constructor <;> linarith

/-- The reindexing of the weight `Z`. -/
lemma Z_cast (b : ℕ) :
    (Z b : ℝ) = (if b = 0 then (1 : ℝ) else if Nat.sqrt b ^ 2 = b then 2 else 0) := by
  rw [Z]; split <;> simp [*]

/-- **The exact decomposition of `M_d(f) − M_d(x)`.** -/
theorem MdF_sub_Md_eq (f : ℝ → ℝ) (d x : ℕ) (hd : 0 < d) :
    MdF f d x - (Md d x : ℝ)
      = (1 / (d : ℝ)) * ∑ b ∈ Finset.range (Nat.sqrt x + 1),
          (Z b : ℝ) * (rho b d : ℝ) * (2 * I0 f b - sqrtTerm x b)
        + (rho 0 d : ℝ) / (d : ℝ) := by
  have hle : rho 0 d ≤ ∑ b ∈ Finset.range (Nat.sqrt x + 1),
      Z b * rho b d * (2 * Nat.sqrt (x - b ^ 2) + 1) := by
    have hmem : 0 ∈ Finset.range (Nat.sqrt x + 1) := by simp
    have h := Finset.single_le_sum
      (f := fun b => Z b * rho b d * (2 * Nat.sqrt (x - b ^ 2) + 1))
      (fun b _ => Nat.zero_le _) hmem
    have h' : rho 0 d * 1 ≤ rho 0 d * (2 * Nat.sqrt x + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    exact le_trans (by simpa using h') (by simpa [Z_zero, Nat.sub_zero] using h)
  have hMd : (Md d x : ℝ) = (1 / (d : ℝ)) * (∑ b ∈ Finset.range (Nat.sqrt x + 1),
        (Z b : ℝ) * (rho b d : ℝ) * sqrtTerm x b)
      - (rho 0 d : ℝ) / (d : ℝ) := by
    have hc : (Md d x : ℝ) = (MdNum d x : ℝ) / (d : ℝ) := by rw [Md]; push_cast; ring
    rw [hc, MdNum, Nat.cast_sub hle]
    push_cast [sqrtTerm]
    ring
  have h1 : (∑ b ∈ Finset.range (Nat.sqrt x + 1),
        (Z b : ℝ) * (rho b d : ℝ) * (2 * I0 f b - sqrtTerm x b))
      = 2 * (∑ b ∈ Finset.range (Nat.sqrt x + 1), (Z b : ℝ) * (rho b d : ℝ) * I0 f b)
        - (∑ b ∈ Finset.range (Nat.sqrt x + 1),
            (Z b : ℝ) * (rho b d : ℝ) * sqrtTerm x b) := by
    have e : ∀ b : ℕ, (Z b : ℝ) * (rho b d : ℝ) * (2 * I0 f b - sqrtTerm x b)
        = 2 * ((Z b : ℝ) * (rho b d : ℝ) * I0 f b)
          - (Z b : ℝ) * (rho b d : ℝ) * sqrtTerm x b := by
      intro b; ring
    simp only [e]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hMd, MdF, h1]
  ring

/-- The pointwise bound for the `k = 0` integral. -/
lemma I0_bound (f : ℝ → ℝ) (x y b : ℕ) (hf : Continuous f) (hy : 1 ≤ y)
    (hf0 : ∀ u, 0 ≤ f u) (hf1 : ∀ u, f u ≤ 1)
    (hfeq : ∀ u, u ≤ (x : ℝ) - (y : ℝ) → f u = 1) (hfz : ∀ u, (x : ℝ) ≤ u → f u = 0)
    (hb : b ≤ Nat.sqrt x) :
    |2 * I0 f b - sqrtTerm x b|
      ≤ 3 * (y : ℝ) * ((x : ℝ) + (y : ℝ) - (b : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) + 2 := by
  have hb2 : b ^ 2 ≤ x := (Nat.le_sqrt').mp hb
  have hcast : ((x - b ^ 2 : ℕ) : ℝ) = (x : ℝ) - (b : ℝ) ^ 2 := by
    rw [Nat.cast_sub hb2]; push_cast; ring
  have h1 : |2 * I0 f b - 2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 2)|
      ≤ 3 * (y : ℝ) * ((x : ℝ) + (y : ℝ) - (b : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) := by
    have h := integral_vs_sqrt_local f x y b hf hf0 hf1 hfeq hfz hb
    simpa only [I0, sqrtTerm, hcast] using h
  have h2 : |2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 2) - sqrtTerm x b| ≤ 2 := by
    have h := abs_sqrt_sub_floor (x - b ^ 2)
    simpa only [sqrtTerm, hcast] using h
  calc |2 * I0 f b - sqrtTerm x b|
      = |(2 * I0 f b - 2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 2))
          + (2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 2) - sqrtTerm x b)| := by ring_nf
    _ ≤ |2 * I0 f b - 2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 2)|
          + |2 * Real.sqrt ((x : ℝ) - (b : ℝ) ^ 2) - sqrtTerm x b| := abs_add_le _ _
    _ ≤ 3 * (y : ℝ) * ((x : ℝ) + (y : ℝ) - (b : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) + 2 := by
        linarith [h1, h2]

/-- The per-modulus bound. -/
theorem MdF_sub_Md_le_d (f : ℝ → ℝ) (d x y : ℕ) (hf : Continuous f) (hd : 1 ≤ d)
    (hy : 1 ≤ y) (hf0 : ∀ u, 0 ≤ f u) (hf1 : ∀ u, f u ≤ 1)
    (hfeq : ∀ u, u ≤ (x : ℝ) - (y : ℝ) → f u = 1) (hfz : ∀ u, (x : ℝ) ≤ u → f u = 0) :
    |MdF f d x - (Md d x : ℝ)|
      ≤ (1 / (d : ℝ)) * (∑ b ∈ Finset.range (Nat.sqrt x + 1),
          (Z b : ℝ) * (rho b d : ℝ)
            * (3 * (y : ℝ) * ((x : ℝ) + (y : ℝ) - (b : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) + 2))
        + (rho 0 d : ℝ) / (d : ℝ) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [MdF_sub_Md_eq f d x (by omega)]
  have hS : |∑ b ∈ Finset.range (Nat.sqrt x + 1),
        (Z b : ℝ) * (rho b d : ℝ) * (2 * I0 f b - sqrtTerm x b)|
      ≤ ∑ b ∈ Finset.range (Nat.sqrt x + 1),
          (Z b : ℝ) * (rho b d : ℝ)
            * (3 * (y : ℝ) * ((x : ℝ) + (y : ℝ) - (b : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) + 2) := by
    calc |∑ b ∈ Finset.range (Nat.sqrt x + 1),
          (Z b : ℝ) * (rho b d : ℝ) * (2 * I0 f b - sqrtTerm x b)|
        ≤ ∑ b ∈ Finset.range (Nat.sqrt x + 1),
            |(Z b : ℝ) * (rho b d : ℝ) * (2 * I0 f b - sqrtTerm x b)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ b ∈ Finset.range (Nat.sqrt x + 1),
            (Z b : ℝ) * (rho b d : ℝ) * |2 * I0 f b - sqrtTerm x b| := by
          apply Finset.sum_congr rfl
          intro b _
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro b hb
          have hbs : b ≤ Nat.sqrt x := by simpa using hb
          have := I0_bound f x y b hf hy hf0 hf1 hfeq hfz hbs
          have hnn : 0 ≤ (Z b : ℝ) * (rho b d : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left this hnn
  calc |(1 / (d : ℝ)) * (∑ b ∈ Finset.range (Nat.sqrt x + 1),
          (Z b : ℝ) * (rho b d : ℝ) * (2 * I0 f b - sqrtTerm x b)) + (rho 0 d : ℝ) / (d : ℝ)|
      ≤ |(1 / (d : ℝ)) * (∑ b ∈ Finset.range (Nat.sqrt x + 1),
          (Z b : ℝ) * (rho b d : ℝ) * (2 * I0 f b - sqrtTerm x b))|
        + |(rho 0 d : ℝ) / (d : ℝ)| := abs_add_le _ _
    _ = (1 / (d : ℝ)) * |∑ b ∈ Finset.range (Nat.sqrt x + 1),
          (Z b : ℝ) * (rho b d : ℝ) * (2 * I0 f b - sqrtTerm x b)| + (rho 0 d : ℝ) / (d : ℝ) := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (d:ℝ)),
          abs_of_nonneg (div_nonneg (by positivity) (by positivity : (0:ℝ) ≤ (d:ℝ)))]
    _ ≤ (1 / (d : ℝ)) * (∑ b ∈ Finset.range (Nat.sqrt x + 1),
          (Z b : ℝ) * (rho b d : ℝ)
            * (3 * (y : ℝ) * ((x : ℝ) + (y : ℝ) - (b : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) + 2))
        + (rho 0 d : ℝ) / (d : ℝ) := by
        have hpos : 0 ≤ (1 : ℝ) / (d : ℝ) := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left hS hpos) (le_refl _)


/-- `√n` (as a natural) is at most the real square root of `n`. -/
lemma natSqrt_cast_le_sqrt (n : ℕ) : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n := by
  have hsq : ((Nat.sqrt n : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) := by
    have h := (Nat.le_sqrt').mp (le_refl (Nat.sqrt n))
    exact_mod_cast h
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (Nat.cast_nonneg _)] at this

lemma rho_sq_eq (c d : ℕ) :
    rho (c ^ 2) d = ({α : ZMod d | α ^ 2 + (c : ZMod d) ^ 4 = 0}).ncard := by
  rw [rho]
  congr 1
  ext α
  simp only [Set.mem_setOf_eq, Nat.cast_pow]
  ring_nf

/-- **(3.12)**, corrected form: the smoothed main term differs from `M_d(x)` by
`≪ (log 2D)^6 (y x^{-1/4} + x^{1/4}) + √D` on average over `d ≤ D`. -/
theorem MdF_sub_Md_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (D x y : ℕ), Continuous f →
      1 ≤ D → 1 ≤ x → 1 ≤ y → x ≤ y ^ 2 →
      (∀ u, 0 ≤ f u) → (∀ u, f u ≤ 1) →
      (∀ u, u ≤ (x : ℝ) - (y : ℝ) → f u = 1) → (∀ u, (x : ℝ) ≤ u → f u = 0) →
      ∑ d ∈ Finset.Icc 1 D, |MdF f d x - (Md d x : ℝ)|
        ≤ C * (Real.log (2 * (D : ℝ) + 2)) ^ 6
            * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + (x : ℝ) ^ (1 / 4 : ℝ)) := by
  obtain ⟨Cρ, hCρpos, hCρ⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.sum_rho_sq_div_le
  obtain ⟨Cs, hCspos, hCs⟩ := Commons.Analysis.Sum.inv_sqrt_shell_bound
  have hCtpos : (0 : ℝ) < 2 := by norm_num
  have hCt : ∀ D : ℕ, (∑ d ∈ Finset.Icc 1 D, (Real.sqrt (d : ℝ))⁻¹) ≤ 2 * Real.sqrt D :=
    fun D => Commons.Analysis.Sum.sum_inv_sqrt_le D
  have hCq : ∀ d : ℕ, 1 ≤ d → (({α : ZMod d | α ^ 2 = 0}).ncard : ℝ) ≤ Real.sqrt d :=
    fun d hd => Commons.NumberTheory.FriedlanderIwaniec.sqZero_card_le_sqrt d hd
  refine ⟨(Cρ + 1) * (6 * Cs + 10), by positivity, ?_⟩
  intro f D x y hf hD hx hy hxy hf0 hf1 hfeq hfz
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have hD0 : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hlog0 : 0 ≤ Real.log (2 * (D : ℝ) + 2) := by
    apply Real.log_nonneg; linarith
  -- the weight `A b = 3y ((x)+(y)-(b)²)^{-1/2} + 2`
  set A : ℕ → ℝ := fun b => 3 * (y : ℝ) * ((x : ℝ) + (y : ℝ) - (b : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) + 2
    with hA
  -- Step 1: per-modulus bound
  have hstep1 : ∑ d ∈ Finset.Icc 1 D, |MdF f d x - (Md d x : ℝ)|
      ≤ ∑ d ∈ Finset.Icc 1 D, ((1 / (d : ℝ)) * (∑ b ∈ Finset.range (Nat.sqrt x + 1),
            (Z b : ℝ) * (rho b d : ℝ) * A b) + (rho 0 d : ℝ) / (d : ℝ)) := by
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have := MdF_sub_Md_le_d f d x y hf hd1 hy hf0 hf1 hfeq hfz
    simpa [A] using this
  rw [Finset.sum_add_distrib] at hstep1
  -- Step 2: swap the order of summation
  have hswap : (∑ d ∈ Finset.Icc 1 D, (1 / (d : ℝ)) * (∑ b ∈ Finset.range (Nat.sqrt x + 1),
        (Z b : ℝ) * (rho b d : ℝ) * A b))
      = ∑ b ∈ Finset.range (Nat.sqrt x + 1), (Z b : ℝ) * A b *
          (∑ d ∈ Finset.Icc 1 D, (rho b d : ℝ) / (d : ℝ)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    ring
  -- Step 3: `∑_d ρ(0;d)/d ≤ Cρ (log 2D)^6`
  have hrho0log : (∑ d ∈ Finset.Icc 1 D, (rho 0 d : ℝ) / (d : ℝ))
      ≤ Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6 := by
    have hset : ∀ d : ℕ, ({α : ZMod d | α ^ 2 = 0} : Set (ZMod d))
        = {α : ZMod d | α ^ 2 + (0 : ZMod d) ^ 4 = 0} := fun d => by ext α; simp
    have h : (∑ d ∈ Finset.Icc 1 D, (rho 0 d : ℝ) / (d : ℝ))
        = (∑ d ∈ Finset.Icc 1 D,
            (({α : ZMod d | α ^ 2 + (0 : ZMod d) ^ 4 = 0}).ncard : ℝ) / (d : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [rho_zero_eq_sqZero, hset d]
    rw [h]
    simpa using hCρ D 0
  -- Step 4: split off the `b = 0` term and reindex the square terms
  have hAreindex : (∑ b ∈ Finset.range (Nat.sqrt x + 1), (Z b : ℝ) * A b *
        (∑ d ∈ Finset.Icc 1 D, (rho b d : ℝ) / (d : ℝ)))
      = (A 0 * (∑ d ∈ Finset.Icc 1 D, (rho 0 d : ℝ) / (d : ℝ)))
        + 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
            A (c ^ 2) * (∑ d ∈ Finset.Icc 1 D, (rho (c ^ 2) d : ℝ) / (d : ℝ))) := by
    have h1 : (∑ b ∈ Finset.range (Nat.sqrt x + 1), (Z b : ℝ) * A b *
          (∑ d ∈ Finset.Icc 1 D, (rho b d : ℝ) / (d : ℝ)))
        = ∑ b ∈ Finset.range (Nat.sqrt x + 1),
            (if b = 0 then (1 : ℝ) else if Nat.sqrt b ^ 2 = b then 2 else 0) *
              (A b * (∑ d ∈ Finset.Icc 1 D, (rho b d : ℝ) / (d : ℝ))) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Z_cast]; ring
    rw [h1, Commons.NumberTheory.FriedlanderIwaniec.sum_Z_mul_reindex]
  -- Step 5: the `b = 0` term
  have hφ0 : A 0 * (∑ d ∈ Finset.Icc 1 D, (rho 0 d : ℝ) / (d : ℝ))
      ≤ A 0 * (Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6) := by
    have hAnneg : 0 ≤ A 0 := by
      have hval : A 0 = 3 * (y : ℝ) * ((x : ℝ) + (y : ℝ)) ^ (-(1 / 2 : ℝ)) + 2 := by
        rw [hA]; simp
      rw [hval]
      have := Real.rpow_nonneg (by linarith [hx0, hy0] : (0:ℝ) ≤ (x:ℝ) + (y:ℝ)) (-(1 / 2 : ℝ))
      nlinarith [this, hy0]
    exact mul_le_mul_of_nonneg_left hrho0log hAnneg
  -- Step 6: the square terms
  have hφc : 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
        A (c ^ 2) * (∑ d ∈ Finset.Icc 1 D, (rho (c ^ 2) d : ℝ) / (d : ℝ)))
      ≤ 2 * Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6
          * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2)) := by
    have hρc : ∀ c : ℕ, (∑ d ∈ Finset.Icc 1 D, (rho (c ^ 2) d : ℝ) / (d : ℝ))
        ≤ Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6 := by
      intro c
      refine le_trans (le_of_eq (Finset.sum_congr rfl (fun d _ => ?_))) (hCρ D c)
      rw [rho_sq_eq]
    have hpt : ∀ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
        A (c ^ 2) * (∑ d ∈ Finset.Icc 1 D, (rho (c ^ 2) d : ℝ) / (d : ℝ))
          ≤ A (c ^ 2) * (Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6) := by
      intro c hc
      refine mul_le_mul_of_nonneg_left (hρc c) ?_
      have hc2 : c ^ 2 ≤ Nat.sqrt x := (Nat.le_sqrt').mp (Finset.mem_Icc.mp hc).2
      have hc4 : c ^ 4 ≤ x := by
        have h4 := (Nat.le_sqrt').mp hc2
        rwa [show (c ^ 2) ^ 2 = c ^ 4 by ring] at h4
      have hbR : ((c : ℝ)) ^ 4 ≤ (x : ℝ) := by exact_mod_cast hc4
      have hnon : (0 : ℝ) ≤ (x : ℝ) + (y : ℝ) - (c : ℝ) ^ 4 := by linarith
      have hrp := Real.rpow_nonneg hnon (-(1 / 2 : ℝ))
      have hval : A (c ^ 2) = 3 * (y : ℝ) * ((x : ℝ) + (y : ℝ) - (c : ℝ) ^ 4) ^ (-(1 / 2 : ℝ)) + 2 := by
        simp only [hA]
        push_cast
        ring
      rw [hval]
      nlinarith [hrp, hy0]
    calc 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
            A (c ^ 2) * (∑ d ∈ Finset.Icc 1 D, (rho (c ^ 2) d : ℝ) / (d : ℝ)))
        ≤ 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
            A (c ^ 2) * (Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6)) := by
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (by norm_num)
      _ = 2 * Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6
            * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2)) := by
          rw [← Finset.sum_mul]; ring
  -- Step 7: the arithmetic bound for the square terms
  have hsum_c : (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2))
      ≤ 3 * (y : ℝ) * (Cs * (x : ℝ) ^ (-(1 / 4 : ℝ))) + 2 * (x : ℝ) ^ (1 / 4 : ℝ) := by
    have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hcard : (((Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).card : ℕ) : ℝ)
        ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
      rw [Nat.card_Icc]
      have h1 : ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ≤ Real.sqrt (Real.sqrt (x : ℝ)) :=
        le_trans (natSqrt_cast_le_sqrt _) (Real.sqrt_le_sqrt (natSqrt_cast_le_sqrt x))
      have h2 : Real.sqrt (Real.sqrt (x : ℝ)) = (x : ℝ) ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hx0)]
        norm_num
      rw [h2] at h1
      have h3 : ((Nat.sqrt (Nat.sqrt x) + 1 - 1 : ℕ) : ℝ)
          = ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) := by norm_num
      rw [h3]; exact h1
    have hAa : ∀ c : ℕ, A (c ^ 2)
        = 3 * (y : ℝ) * ((x : ℝ) + (y : ℝ) - (c : ℝ) ^ 4) ^ (-(1 / 2 : ℝ)) + 2 := by
      intro c
      simp only [hA]
      push_cast
      ring
    have hsplit : (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2))
        = 3 * (y : ℝ) * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
            ((x : ℝ) + (y : ℝ) - (c : ℝ) ^ 4) ^ (-(1 / 2 : ℝ)))
          + 2 * (((Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).card : ℕ) : ℝ) := by
      simp only [hAa]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hsplit]
    have hshell := hCs x y hx hxy
    have hcard' : 0 ≤ 3 * (y : ℝ) := by positivity
    have h1 : 3 * (y : ℝ) * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
          ((x : ℝ) + (y : ℝ) - (c : ℝ) ^ 4) ^ (-(1 / 2 : ℝ)))
        ≤ 3 * (y : ℝ) * (Cs * (x : ℝ) ^ (-(1 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left hshell hcard'
    have h2 : 2 * (((Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).card : ℕ) : ℝ)
        ≤ 2 * (x : ℝ) ^ (1 / 4 : ℝ) := by linarith [hcard]
    linarith
  -- Step 8: conclude
  have hlogpos : 0 < Real.log (2 * (D : ℝ) + 2) ^ 6 := by
    apply pow_pos
    apply Real.log_pos
    linarith
  have hlog0 : 0 ≤ Real.log (2 * (D : ℝ) + 2) ^ 6 := le_of_lt hlogpos
  have hCsnn : 0 ≤ Cs := le_of_lt hCspos
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hx14 : (1 : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hxnn : 0 ≤ (x : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (le_of_lt hx0) _
  have hxhnn : 0 ≤ (x : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (le_of_lt hx0) _
  have hxqnn : 0 ≤ (x : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (le_of_lt hx0) _
  have hyl : 0 ≤ (y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) := mul_nonneg hy0 hxqnn
  have hys : 0 ≤ (y : ℝ) * (x : ℝ) ^ (-(1 / 2 : ℝ)) := mul_nonneg hy0 hxhnn
  -- combine `A 0 + 2 ∑_c A(c²) + 1`
  have hAcomb : A 0 + 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2)) + 1
      ≤ (6 * Cs + 7)
          * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + (x : ℝ) ^ (1 / 4 : ℝ)) := by
    have h1 : A 0 ≤ 3 * (y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + 2 * (x : ℝ) ^ (1 / 4 : ℝ) := by
      have hA0 : A 0 ≤ 3 * (y : ℝ) * (x : ℝ) ^ (-(1 / 2 : ℝ)) + 2 := by
        have hval : A 0 = 3 * (y : ℝ) * ((x : ℝ) + (y : ℝ)) ^ (-(1 / 2 : ℝ)) + 2 := by
          rw [hA]; simp
        rw [hval]
        have hbase : ((x : ℝ) + (y : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ (x : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by norm_num)
        nlinarith [hbase, hy0]
      have e1 : (y : ℝ) * (x : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hy0
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      have e2 : (2 : ℝ) ≤ 2 * (x : ℝ) ^ (1 / 4 : ℝ) := by nlinarith [hx14]
      linarith
    have h2 : 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2))
        ≤ 6 * (y : ℝ) * (Cs * (x : ℝ) ^ (-(1 / 4 : ℝ))) + 4 * (x : ℝ) ^ (1 / 4 : ℝ) := by
      linarith [hsum_c]
    have h3 : (1 : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := hx14
    have hCsyn : 0 ≤ Cs * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ))) := mul_nonneg hCsnn hyl
    nlinarith [h1, h2, h3, hyl, hxnn, hCsyn]
  -- the product form
  have hfinal1 : A 0 * (Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6)
        + 2 * Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6
            * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2))
        + Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6
      ≤ Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6
          * (A 0 + 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2)) + 1) := by
    apply le_of_eq
    ring
  have hfinal2 : Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6
        * (A 0 + 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2)) + 1)
      ≤ Cρ * (6 * Cs + 7) * (Real.log (2 * (D : ℝ) + 2)) ^ 6
          * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + (x : ℝ) ^ (1 / 4 : ℝ)) := by
    have h0 : 0 ≤ Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6 := mul_nonneg (le_of_lt hCρpos) hlog0
    have h1 : Cρ * (A 0 + 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2)) + 1)
        ≤ Cρ * ((6 * Cs + 7) * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + (x : ℝ) ^ (1 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left hAcomb (le_of_lt hCρpos)
    calc Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6
          * (A 0 + 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2)) + 1)
        = (Real.log (2 * (D : ℝ) + 2)) ^ 6
            * (Cρ * (A 0 + 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2)) + 1)) := by ring
      _ ≤ (Real.log (2 * (D : ℝ) + 2)) ^ 6
            * (Cρ * ((6 * Cs + 7) * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + (x : ℝ) ^ (1 / 4 : ℝ)))) :=
          mul_le_mul_of_nonneg_left h1 hlog0
      _ = Cρ * (6 * Cs + 7) * (Real.log (2 * (D : ℝ) + 2)) ^ 6
            * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + (x : ℝ) ^ (1 / 4 : ℝ)) := by ring
  have hfac3 : Cρ * (6 * Cs + 7) ≤ (Cρ + 1) * (6 * Cs + 10) := by
    nlinarith [hCρpos, hCsnn]
  have hg1 : (y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + (x : ℝ) ^ (1 / 4 : ℝ) ≥ 0 := by
    linarith [hyl, hxnn]
  calc ∑ d ∈ Finset.Icc 1 D, |MdF f d x - (Md d x : ℝ)|
      ≤ (∑ d ∈ Finset.Icc 1 D, (1 / (d : ℝ)) * (∑ b ∈ Finset.range (Nat.sqrt x + 1),
            (Z b : ℝ) * (rho b d : ℝ) * A b))
          + ∑ d ∈ Finset.Icc 1 D, (rho 0 d : ℝ) / (d : ℝ) := hstep1
    _ = ((A 0 * (∑ d ∈ Finset.Icc 1 D, (rho 0 d : ℝ) / (d : ℝ)))
            + 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
                A (c ^ 2) * (∑ d ∈ Finset.Icc 1 D, (rho (c ^ 2) d : ℝ) / (d : ℝ))))
          + ∑ d ∈ Finset.Icc 1 D, (rho 0 d : ℝ) / (d : ℝ) := by rw [hswap, hAreindex]
    _ ≤ A 0 * (Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6)
          + 2 * Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6
            * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2))
          + Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6 := by
        have := hrho0log
        linarith [hφ0, hφc]
    _ ≤ Cρ * (Real.log (2 * (D : ℝ) + 2)) ^ 6
          * (A 0 + 2 * (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)), A (c ^ 2)) + 1) := hfinal1
    _ ≤ Cρ * (6 * Cs + 7) * (Real.log (2 * (D : ℝ) + 2)) ^ 6
          * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + (x : ℝ) ^ (1 / 4 : ℝ)) := hfinal2
    _ ≤ (Cρ + 1) * (6 * Cs + 10) * (Real.log (2 * (D : ℝ) + 2)) ^ 6
          * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + (x : ℝ) ^ (1 / 4 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hg1
        exact mul_le_mul_of_nonneg_right hfac3 hlog0

end Submission


set_option maxHeartbeats 4000000

/-!
# §3 of Friedlander–Iwaniec, part 4: the Poisson expansion (3.11), (3.13)

This file develops the harmonic analysis underlying the paper's estimate (3.13).
The smoothed congruence sum admits the Fourier expansion

  `A_d(f) = (2/d) ∑_b Z(b) ∑_k ρ(k,b;d) I(k,b;d)`,

with main term `M_d(f)` given by the term `k = 0`.  Its proof is a combination of
Poisson summation on each residue class `a ≡ α (mod d)` with `α² + b² ≡ 0` and of
the reindexing of the `b`-sum by the square roots of `b`.
-/

namespace Submission

open Finset MeasureTheory
open scoped FourierTransform

/-- The Fourier integral `I(k,b;d) = ∫₀^∞ f(t² + b²) cos(2π k t / d) dt`, paper (3.11). -/
noncomputable def Icos (f : ℝ → ℝ) (d b : ℕ) (k : ℤ) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ), f (t ^ 2 + (b : ℝ) ^ 2) * Real.cos (2 * Real.pi * (k : ℝ) * t / (d : ℝ))

/-- The root sum `ρ(k,b;d) = ∑_{0 ≤ r < d, d ∣ r² + b²} cos(2π r k / d)`, the real part of
the "Weyl harmonic" attached to the congruence `r² + b² ≡ 0 (mod d)`. -/
noncomputable def rhoRe (d b : ℕ) (k : ℤ) : ℝ :=
  ∑ r ∈ (Finset.range d).filter (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) ^ 2 + (b : ℤ) ^ 2),
    Real.cos (2 * Real.pi * (r : ℝ) * (k : ℝ) / (d : ℝ))

/-- The same root sum in complex exponential form (matching the statement of
`Commons.NumberTheory.FriedlanderIwaniec.linear_form_rho_bound`). -/
noncomputable def rhoC (d b : ℕ) (k : ℤ) : ℂ :=
  ∑ r ∈ (Finset.range d).filter (fun r : ℕ => (r ^ 2 + b ^ 2) % d = 0),
    Commons.Analysis.ExponentialSums.ch ((r : ℝ) * (k : ℝ) / d)

/-- The filter conditions `d ∣ r² + b²` (over `ℤ`) and `(r² + b²) % d = 0` agree. -/
lemma dvd_int_iff_mod_eq_zero {d r b : ℕ} :
    ((d : ℤ) ∣ (r : ℤ) ^ 2 + (b : ℤ) ^ 2) ↔ (r ^ 2 + b ^ 2) % d = 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero, ← Int.natCast_dvd_natCast]
  push_cast
  ring_nf

/-- The Fourier transform of `t ↦ f (t² + b²)` is the cosine integral. -/
lemma fourier_quad_eq (f : ℝ → ℝ) (b : ℕ) (hf : ContDiff ℝ 2 f)
    (hcs : HasCompactSupport fun t : ℝ => f (t ^ 2 + (b : ℝ) ^ 2)) (ξ : ℝ) :
    (𝓕 fun t : ℝ => ((f (t ^ 2 + (b : ℝ) ^ 2) : ℝ) : ℂ)) ξ
      = ((2 * ∫ t in Set.Ici (0 : ℝ), f (t ^ 2 + (b : ℝ) ^ 2) * Real.cos (2 * Real.pi * ξ * t)
          : ℝ) : ℂ) :=
  Commons.Analysis.Fourier.fourier_quadratic_eq f (b : ℝ) ξ hf.continuous hcs


/-- `I(k,b;d)` is half the Fourier transform of `t ↦ f (t² + b²)`, evaluated at `k / d`. -/
lemma Icos_eq (f : ℝ → ℝ) (d b : ℕ) (hd : 0 < d) (hf : ContDiff ℝ 2 f)
    (hcs : HasCompactSupport fun t : ℝ => f (t ^ 2 + (b : ℝ) ^ 2)) (k : ℤ) :
    Icos f d b k
      = (1 / 2) * ((𝓕 fun t : ℝ => ((f (t ^ 2 + (b : ℝ) ^ 2) : ℝ) : ℂ)) ((k : ℝ) / (d : ℝ))).re := by
  have hξ : Icos f d b k
      = ∫ t in Set.Ici (0 : ℝ), f (t ^ 2 + (b : ℝ) ^ 2) * Real.cos (2 * Real.pi * ((k : ℝ) / (d : ℝ)) * t) := by
    unfold Icos
    apply setIntegral_congr_fun measurableSet_Ici
    intro t _
    have harg : 2 * Real.pi * (k : ℝ) * t / (d : ℝ) = 2 * Real.pi * ((k : ℝ) / (d : ℝ)) * t := by
      field_simp
    simp only [harg]
  rw [hξ, fourier_quad_eq f b hf hcs]
  simp only [Complex.ofReal_re]
  ring

/-- A compactly supported function is summable over the lattice `ℤ ⊂ ℝ`. -/
lemma summable_int_of_hasCompactSupport {g : ℝ → ℝ} (hcs : HasCompactSupport g) :
    Summable fun a : ℤ => g (a : ℝ) := by
  have hb : Bornology.IsBounded (tsupport g) := (hcs.isCompact).isBounded
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hb
  set n : ℕ := Nat.ceil R with hn
  have hRn : R ≤ (n : ℝ) := Nat.le_ceil R
  apply summable_of_hasFiniteSupport
  refine (Set.finite_Icc (-(n : ℤ)) (n : ℤ)).subset ?_
  intro a ha
  have ha' : g (a : ℝ) ≠ 0 := ha
  have h1 : (a : ℝ) ∈ tsupport g := subset_tsupport g ha'
  have h2 : (a : ℝ) ∈ Metric.closedBall (0 : ℝ) R := hR h1
  simp only [Metric.mem_closedBall, dist_zero_right] at h2
  rw [Set.mem_Icc]
  have h2' : |(a : ℝ)| ≤ (n : ℝ) := le_trans h2 hRn
  have h3 : ((|a| : ℤ) : ℝ) ≤ (n : ℝ) := by
    rw [Int.cast_abs]; exact h2'
  exact abs_le.mp (Int.cast_le.mp h3)

/-- The sequence of Fourier integrals `k ↦ I(k,b;d)` is summable. -/
lemma summable_Icos (f : ℝ → ℝ) (d b : ℕ) (hd : 0 < d) (hf : ContDiff ℝ 2 f)
    (hcs : HasCompactSupport fun t : ℝ => f (t ^ 2 + (b : ℝ) ^ 2)) :
    Summable fun k : ℤ => Icos f d b k := by
  have hGcd : ContDiff ℝ 2 (fun t : ℝ => ((f (t ^ 2 + (b : ℝ) ^ 2) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hf.comp (by fun_prop))
  have hGcs : HasCompactSupport (fun t : ℝ => ((f (t ^ 2 + (b : ℝ) ^ 2) : ℝ) : ℂ)) :=
    hcs.comp_left (g := Complex.ofReal) (by simp)
  have hO := Commons.Analysis.Fourier.fourier_isBigO_rpow_neg_two hGcd hGcs
  have hsum := Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow one_lt_two hO
    (d := (d : ℝ)) (by positivity)
  refine Summable.of_norm_bounded (hsum.norm.mul_left (1 / 2)) (fun k => ?_)
  rw [Icos_eq f d b hd hf hcs k]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)


/-- Summing a function of the least nonnegative representative over `ZMod d` equals the
corresponding sum over `Finset.range d`. -/
lemma sum_range_eq_sum_zmod (d : ℕ) [NeZero d] (G : ℕ → ℝ) :
    (∑ α : ZMod d, G α.val) = ∑ r ∈ Finset.range d, G r := by
  have h2 : (∑ r ∈ Finset.range d, G r) = ∑ i : Fin d, G (i : ℕ) := Finset.sum_range G
  rw [h2]
  refine Finset.sum_bij (fun (α : ZMod d) _ => (⟨α.val, ZMod.val_lt α⟩ : Fin d)) ?_ ?_ ?_ ?_
  · intro a ha; simp
  · intro a₁ _ a₂ _ h
    have h1 : a₁.val = a₂.val := by simpa using h
    conv_lhs => rw [← ZMod.natCast_zmod_val a₁]
    conv_rhs => rw [← ZMod.natCast_zmod_val a₂]
    rw [h1]
  · intro b _
    exact ⟨(b.val : ZMod d), Finset.mem_univ _, by ext; exact ZMod.val_cast_of_lt b.isLt⟩
  · intro a _
    rfl

/-- The condition `ZMod`: `α² + b² = 0` matches the divisibility condition on representatives. -/
lemma zmod_cond_iff (d r b : ℕ) :
    ((r : ZMod d) ^ 2 + (b : ZMod d) ^ 2 = 0) ↔ (d : ℤ) ∣ (r : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  ring_nf

/-- Sum of the indicator of a predicate over a finite type is the cardinality of the filtered
`Finset`. -/
lemma sum_ite_one_eq_card {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    (∑ a : α, (if P a then (1 : ℝ) else 0)) = ((Finset.univ.filter P).card : ℝ) := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The two descriptions of the root count `ρ(b;d)` agree: the representatives `0 ≤ r < d`
with `d ∣ r² + b²` and the residues `α` of `ZMod d` with `α² + b² = 0`. -/
lemma card_range_filter_eq_card_zmod (d b : ℕ) [NeZero d] :
    ((Finset.range d).filter (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) ^ 2 + (b : ℤ) ^ 2)).card
      = (Finset.univ.filter (fun α : ZMod d => α ^ 2 + (b : ZMod d) ^ 2 = 0)).card := by
  have himg : (Finset.range d).filter (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) ^ 2 + (b : ℤ) ^ 2)
      = (Finset.univ.filter (fun α : ZMod d => α ^ 2 + (b : ZMod d) ^ 2 = 0)).image
          (fun α : ZMod d => α.val) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hr, hdvd⟩
      refine ⟨(r : ZMod d), ?_, ZMod.val_cast_of_lt hr⟩
      rw [← ZMod.natCast_zmod_val ((r : ZMod d)), ZMod.val_cast_of_lt hr]
      exact (zmod_cond_iff d r b).mpr hdvd
    · rintro ⟨α, hα, rfl⟩
      refine ⟨ZMod.val_lt α, ?_⟩
      rw [← zmod_cond_iff d α.val b, ZMod.natCast_zmod_val]
      exact hα
  rw [himg, Finset.card_image_of_injective _
    (fun a b hab => ZMod.val_injective d hab)]


/-- `I(0,b;d) = ∫₀^∞ f(t²+b²) dt`, the `k = 0` Fourier integral. -/
lemma Icos_zero (f : ℝ → ℝ) (d b : ℕ) : Icos f d b 0 = I0 f b := by
  simp [Icos, I0]

/-- `ρ(0,b;d) = ρ(b;d)`, the number of roots of `α² + b² ≡ 0 (mod d)`. -/
lemma rhoRe_zero (d b : ℕ) [NeZero d] : rhoRe d b 0 = (rho b d : ℝ) := by
  have h1 : rhoRe d b 0
      = (((Finset.range d).filter
          (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) ^ 2 + (b : ℤ) ^ 2)).card : ℝ) := by
    rw [rhoRe]
    simp only [Int.cast_zero, mul_zero, zero_div, Real.cos_zero]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : (rho b d : ℝ)
      = ((Finset.univ.filter (fun α : ZMod d => α ^ 2 + (b : ZMod d) ^ 2 = 0)).card : ℝ) := by
    have hset : ({α : ZMod d | α ^ 2 + (b : ZMod d) ^ 2 = 0} : Set (ZMod d))
        = ↑(Finset.univ.filter (fun α : ZMod d => α ^ 2 + (b : ZMod d) ^ 2 = 0)) := by
      ext α; simp
    rw [rho, hset, Set.ncard_coe_finset]
  rw [h1, card_range_filter_eq_card_zmod d b, ← h2]

/-- `ρ(k,b;d)` is even in `k`. -/
lemma rhoRe_neg (d b : ℕ) (k : ℤ) : rhoRe d b (-k) = rhoRe d b k := by
  rw [rhoRe, rhoRe]
  apply Finset.sum_congr rfl
  intro r _
  have h : 2 * Real.pi * (r : ℝ) * ((-k : ℤ) : ℝ) / (d : ℝ)
      = -(2 * Real.pi * (r : ℝ) * (k : ℝ) / (d : ℝ)) := by
    push_cast; ring
  rw [h, Real.cos_neg]


/-- **The Poisson expansion of a single residue class sum** (paper (3.11)).
For `f` of class `C²` with `t ↦ f (t² + b²)` compactly supported,
`∑_{a ∈ ℤ, d ∣ a² + b²} f (a² + b²) = (2/d) ∑_k ρ(k,b;d) I(k,b;d)`. -/
theorem tsum_dvd_quad_eq_rhoRe (f : ℝ → ℝ) (d b : ℕ) (hd : 0 < d) (hf : ContDiff ℝ 2 f)
    (hcs : HasCompactSupport fun t : ℝ => f (t ^ 2 + (b : ℝ) ^ 2)) :
    (∑' a : ℤ, (if (d : ℤ) ∣ a ^ 2 + (b : ℤ) ^ 2 then f ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) else 0))
      = (2 / (d : ℝ)) * ∑' k : ℤ, Icos f d b k * rhoRe d b k := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hdR : (0 : ℝ) < (d : ℝ) := by positivity
  set GG : ZMod d → ℤ → ℝ := fun α k =>
    (if α ^ 2 + (b : ZMod d) ^ 2 = 0 then
      Icos f d b k * Real.cos (2 * Real.pi * (α.val : ℝ) * (k : ℝ) / (d : ℝ)) else 0) with hGG
  have hsumm : Summable fun a : ℤ => f ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) :=
    summable_int_of_hasCompactSupport (g := fun t : ℝ => f (t ^ 2 + (b : ℝ) ^ 2)) hcs
  have hsumm' : Summable fun a : ℤ =>
      (if (d : ℤ) ∣ a ^ 2 + (b : ℤ) ^ 2 then f ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) else 0) := by
    exact (hsumm.indicator {a : ℤ | (d : ℤ) ∣ a ^ 2 + (b : ℤ) ^ 2}).congr
      (fun a => by simp only [Set.indicator_apply, Set.mem_ofPred_eq])
  -- bounded multiplier of a summable sequence
  have hmul : ∀ c : ℤ → ℝ, (∀ k, ‖c k‖ ≤ 1) →
      Summable fun k : ℤ => Icos f d b k * c k := by
    intro c hc
    refine Summable.of_norm_bounded (summable_Icos f d b hd hf hcs).norm (fun k => ?_)
    rw [norm_mul]
    calc ‖Icos f d b k‖ * ‖c k‖ ≤ ‖Icos f d b k‖ * 1 :=
          mul_le_mul_of_nonneg_left (hc k) (norm_nonneg _)
      _ = ‖Icos f d b k‖ := mul_one _
  have hGsumm : ∀ α : ZMod d, Summable (GG α) := by
    intro α
    by_cases hc : α ^ 2 + (b : ZMod d) ^ 2 = 0
    · rw [show GG α = fun k : ℤ => Icos f d b k *
          Real.cos (2 * Real.pi * (α.val : ℝ) * (k : ℝ) / (d : ℝ)) from by
        funext k; simp only [hGG, if_pos hc]]
      refine hmul _ (fun k => ?_)
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    · rw [show GG α = fun _ : ℤ => (0 : ℝ) from by funext k; simp only [hGG, if_neg hc]]
      exact summable_zero
  rw [Commons.NumberTheory.ZMod.tsum_int_quadratic_coset (d := d) (b := b)
        (g := fun a : ℤ => f ((a : ℝ) ^ 2 + (b : ℝ) ^ 2)) hsumm]
  -- Poisson summation on each residue class
  have hpois : ∀ α : ZMod d,
      (∑' m : ℤ, f (((α.val : ℝ) + m * (d : ℝ)) ^ 2 + (b : ℝ) ^ 2))
        = (2 / (d : ℝ)) * ∑' k : ℤ, Icos f d b k
            * Real.cos (2 * Real.pi * (α.val : ℝ) * (k : ℝ) / (d : ℝ)) := by
    intro α
    have h := Commons.Analysis.Fourier.poisson_cos_residue f (b : ℝ) hf hcs d hd (α.val : ℝ)
    simpa [Icos] using h
  have hstep : ∀ α : ZMod d,
      (if α ^ 2 + (b : ZMod d) ^ 2 = 0 then
        ∑' m : ℤ, f ((((α.val : ℤ) + m * (d : ℤ) : ℤ) : ℝ) ^ 2 + (b : ℝ) ^ 2) else 0)
      = (2 / (d : ℝ)) * ∑' k : ℤ, GG α k := by
    intro α
    by_cases hc : α ^ 2 + (b : ZMod d) ^ 2 = 0
    · rw [if_pos hc]
      have hcast : (∑' m : ℤ, f ((((α.val : ℤ) + m * (d : ℤ) : ℤ) : ℝ) ^ 2 + (b : ℝ) ^ 2))
          = ∑' m : ℤ, f (((α.val : ℝ) + m * (d : ℝ)) ^ 2 + (b : ℝ) ^ 2) := by
        apply tsum_congr
        intro m
        congr 2
        push_cast
        ring
      rw [hcast, hpois α]
      congr 1
      apply tsum_congr
      intro k
      simp only [hGG, if_pos hc]
    · rw [if_neg hc]
      have hzero : GG α = fun _ : ℤ => (0 : ℝ) := by funext k; simp only [hGG, if_neg hc]
      rw [hzero, tsum_zero, mul_zero]
  rw [Finset.sum_congr rfl (fun α _ => hstep α), ← Finset.mul_sum]
  -- interchange the `α`-sum with the `k`-sum
  have hcomm : (∑ α : ZMod d, ∑' k : ℤ, GG α k) = ∑' k : ℤ, ∑ α : ZMod d, GG α k :=
    (Summable.tsum_finsetSum (s := Finset.univ) (f := GG) (fun α _ => hGsumm α)).symm
  rw [hcomm]
  congr 1
  apply tsum_congr
  intro k
  simp only [hGG]
  rw [show (∑ α : ZMod d, (if α ^ 2 + (b : ZMod d) ^ 2 = 0 then
        Icos f d b k * Real.cos (2 * Real.pi * (α.val : ℝ) * (k : ℝ) / (d : ℝ)) else 0))
      = Icos f d b k * ∑ α : ZMod d, (if α ^ 2 + (b : ZMod d) ^ 2 = 0 then
        Real.cos (2 * Real.pi * (α.val : ℝ) * (k : ℝ) / (d : ℝ)) else 0) from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    by_cases hc : α ^ 2 + (b : ZMod d) ^ 2 = 0
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, mul_zero]]
  congr 1
  rw [rhoRe, Finset.sum_filter]
  have hkey : (∑ α : ZMod d, (if α ^ 2 + (b : ZMod d) ^ 2 = 0 then
        Real.cos (2 * Real.pi * (α.val : ℝ) * (k : ℝ) / (d : ℝ)) else 0))
      = ∑ r ∈ Finset.range d, (if ((r : ZMod d) ^ 2 + (b : ZMod d) ^ 2 = 0) then
        Real.cos (2 * Real.pi * (r : ℝ) * (k : ℝ) / (d : ℝ)) else 0) := by
    rw [← sum_range_eq_sum_zmod d (fun r => (if ((r : ZMod d) ^ 2 + (b : ZMod d) ^ 2 = 0)
        then Real.cos (2 * Real.pi * (r : ℝ) * (k : ℝ) / (d : ℝ)) else 0))]
    apply Finset.sum_congr rfl
    intro α _
    have hsq : ((α.val : ZMod d)) ^ 2 = α ^ 2 := by rw [ZMod.natCast_zmod_val]
    rw [← hsq]
  rw [hkey]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hc : ((r : ZMod d) ^ 2 + (b : ZMod d) ^ 2 = 0)
  · rw [if_pos hc, if_pos ((zmod_cond_iff d r b).mp hc)]
  · rw [if_neg hc, if_neg (fun h => hc ((zmod_cond_iff d r b).mpr h))]

/-! ### Reindexing the smoothed congruence sum -/

/-- If `f` vanishes above `x`, then `t ↦ f (t² + b²)` has compact support. -/
lemma hasCompactSupport_quad' (f : ℝ → ℝ) (b x : ℝ) (hsupp : ∀ u, x ≤ u → f u = 0) :
    HasCompactSupport fun t : ℝ => f (t ^ 2 + b ^ 2) := by
  set c : ℝ := max (x - b ^ 2) 0 with hc
  have hc_nonneg : 0 ≤ c := le_max_right _ _
  have hxle : x - b ^ 2 ≤ c := le_max_left _ _
  have hs2 : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc_nonneg
  refine HasCompactSupport.intro' (K := Set.Icc (-(Real.sqrt c)) (Real.sqrt c))
    isCompact_Icc isClosed_Icc ?_
  intro t ht
  rw [Set.mem_Icc] at ht
  have ht' : t < -(Real.sqrt c) ∨ Real.sqrt c < t := by
    rcases not_and_or.mp ht with h | h
    · exact Or.inl (not_le.mp h)
    · exact Or.inr (not_le.mp h)
  apply hsupp
  have hs : Real.sqrt c < |t| := by
    rcases ht' with ht | ht
    · rw [abs_of_neg (by linarith [Real.sqrt_nonneg c])]
      linarith
    · rw [abs_of_pos (by linarith [Real.sqrt_nonneg c])]
      linarith
  have h2 : (Real.sqrt c) ^ 2 < t ^ 2 :=
    sq_lt_sq.mpr (by rwa [abs_of_nonneg (Real.sqrt_nonneg c)])
  have hsq_c : c < t ^ 2 := by rw [← hs2]; exact h2
  nlinarith [hsq_c, hxle]

/-- The weighted `a`-sum over a residue class modulo `d`: `∑_{a ∈ ℤ, d ∣ a²+b²} f (a²+b²)`. -/
noncomputable def ASum (f : ℝ → ℝ) (d b : ℕ) : ℝ :=
  ∑' a : ℤ, (if (d : ℤ) ∣ a ^ 2 + (b : ℤ) ^ 2 then f ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) else 0)

/-- If `f` vanishes beyond `X`, then `ASum f d b = 0` as soon as `b² > X`. -/
lemma ASum_eq_zero_of_gt {f : ℝ → ℝ} {X : ℝ} (hsupp : ∀ u, X ≤ u → f u = 0)
    (d b : ℕ) (hb : X < (b : ℝ) ^ 2) : ASum f d b = 0 := by
  unfold ASum
  rw [show (fun a : ℤ => (if (d : ℤ) ∣ a ^ 2 + (b : ℤ) ^ 2 then
        f ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) else 0)) = fun _ : ℤ => (0 : ℝ) from by
    funext a
    by_cases h : (d : ℤ) ∣ a ^ 2 + (b : ℤ) ^ 2
    · rw [if_pos h]
      exact hsupp _ (by nlinarith [sq_nonneg (a : ℝ), hb])
    · rw [if_neg h]]
  rw [tsum_zero]

/-- The lattice sum `ASum f d b` restricted to `|a| ≤ x` (for `f` vanishing beyond `x`). -/
lemma ASum_eq_finset_sum (f : ℝ → ℝ) (d b x : ℕ) (hx : 1 ≤ x)
    (hsupp : ∀ u, (x : ℝ) ≤ u → f u = 0) :
    ASum f d b = ∑ a ∈ Finset.Icc (-(x : ℤ)) (x : ℤ),
      (if (d : ℤ) ∣ a ^ 2 + (b : ℤ) ^ 2 then f ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) else 0) := by
  unfold ASum
  rw [tsum_eq_sum (s := Finset.Icc (-(x : ℤ)) (x : ℤ)) (fun a ha => ?_)]
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  by_cases h : (d : ℤ) ∣ a ^ 2 + (b : ℤ) ^ 2
  · rw [if_pos h]
    exact hsupp _ (by
      rw [Finset.mem_Icc, not_and_or] at ha
      have hg : (x : ℝ) < (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
        have habs : (x : ℝ) < |(a : ℝ)| := by
          have h1 : (x : ℤ) < |a| := by
            rcases ha with h' | h'
            · have : a < 0 := by omega
              rw [abs_of_neg this]; omega
            · have : 0 < a := by omega
              rw [abs_of_pos this]; omega
          calc (x : ℝ) < ((|a| : ℤ) : ℝ) := by exact_mod_cast h1
            _ = |(a : ℝ)| := Int.cast_abs
        have := abs_nonneg (a : ℝ)
        nlinarith [sq_abs (a : ℝ), sq_nonneg (|(a : ℝ)|), le_refl (0:ℝ)]
      exact le_of_lt hg)
  · rw [if_neg h]

/-- The box sum over pairs `(a,c)` decomposes as the `c`-sum of the `a`-sums `ASum`. -/
lemma box_sum_eq_sum_ASum (f : ℝ → ℝ) (d x : ℕ) (hx : 1 ≤ x)
    (hsupp : ∀ u, (x : ℝ) ≤ u → f u = 0) :
    (∑ p ∈ ((Finset.Icc (-(x : ℤ)) (x : ℤ)) ×ˢ (Finset.Icc (-(x : ℤ)) (x : ℤ))).filter
              (fun p => p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)),
        (if (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4 then f ((p.1 ^ 2 + p.2 ^ 4).toNat : ℝ) else 0))
      = ∑ c ∈ Finset.Icc (-(x : ℤ)) (x : ℤ), ASum f d (c.natAbs ^ 2) := by
  rw [Finset.sum_filter, Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro c _
  rw [ASum_eq_finset_sum f d (c.natAbs ^ 2) x hx hsupp]
  apply Finset.sum_congr rfl
  intro a _
  have hval : (((a ^ 2 + c ^ 4 : ℤ)).toNat : ℝ) = (a : ℝ) ^ 2 + (c : ℝ) ^ 4 := by
    have h1 : (((a ^ 2 + c ^ 4 : ℤ)).toNat : ℤ) = a ^ 2 + c ^ 4 :=
      Int.toNat_of_nonneg (by positivity)
    have h2 : ((((a ^ 2 + c ^ 4 : ℤ)).toNat : ℤ) : ℝ) = ((a ^ 2 + c ^ 4 : ℤ) : ℝ) := by rw [h1]
    rw [← Int.cast_natCast, h2]
    push_cast
    ring
  have hbc : (((c.natAbs ^ 2 : ℕ) : ℤ)) = c ^ 2 := by
    rw [Nat.cast_pow, Int.natAbs_sq]
  have hbR : (((c.natAbs ^ 2 : ℕ) : ℝ)) = (c : ℝ) ^ 2 := by
    rw [Nat.cast_pow]
    rw [show (((c.natAbs : ℕ)) : ℝ) = |(c : ℝ)| from by
      rw [Nat.cast_natAbs c]
      exact Int.cast_abs]
    rw [sq_abs]
  by_cases hQ : a ^ 2 + c ^ 4 ≤ (x : ℤ)
  · rw [if_pos hQ]
    have hcond : ((d : ℤ) ∣ a ^ 2 + c ^ 4) ↔
        ((d : ℤ) ∣ a ^ 2 + ((c.natAbs ^ 2 : ℕ) : ℤ) ^ 2) := by
      rw [hbc]; ring_nf
    have harg : (((a ^ 2 + c ^ 4 : ℤ)).toNat : ℝ) = (a : ℝ) ^ 2 + (((c.natAbs ^ 2 : ℕ) : ℝ)) ^ 2 := by
      rw [hval, hbR]; ring
    by_cases hc : (d : ℤ) ∣ a ^ 2 + c ^ 4
    · rw [if_pos hc, if_pos (hcond.mp hc), harg]
    · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h))]
  · rw [if_neg hQ]
    by_cases hd : (d : ℤ) ∣ a ^ 2 + ((c.natAbs ^ 2 : ℕ) : ℤ) ^ 2
    · rw [if_pos hd]
      have hzero : f ((a : ℝ) ^ 2 + (((c.natAbs ^ 2 : ℕ) : ℝ)) ^ 2) = 0 := by
        refine hsupp _ ?_
        have hgt : (x : ℝ) < (a : ℝ) ^ 2 + (((c.natAbs ^ 2 : ℕ) : ℝ)) ^ 2 := by
          rw [hbR]
          have h' : (x : ℝ) < (a : ℝ) ^ 2 + (c : ℝ) ^ 4 := by
            have : (x : ℤ) < a ^ 2 + c ^ 4 := lt_of_not_ge hQ
            exact_mod_cast this
          linarith
        exact le_of_lt hgt
      rw [hzero]
    · rw [if_neg hd]

/-- **The reindexing of the smoothed congruence sum.**  Summing over the pairs `(a,c)` with
`a² + c⁴ ≤ x` and grouping by `b = c²` gives the weighted sum over `b ≤ √x`. -/
theorem AdF_eq_sum_Z_mul_ASum (f : ℝ → ℝ) (d x : ℕ) (hd : 0 < d) (hx : 1 ≤ x)
    (hsupp : ∀ u, (x : ℝ) ≤ u → f u = 0) :
    AdF (fun n : ℕ => f n) d x
      = ∑ b ∈ Finset.range (Nat.sqrt x + 1), (Z b : ℝ) * ASum f d b := by
  have hf0 : ∀ n : ℕ, x < n → f (n : ℝ) = 0 := by
    intro n hn
    exact hsupp _ (by
      have h2 : (x : ℝ) < (n : ℝ) := by exact_mod_cast hn
      linarith)
  rw [show AdF (fun n : ℕ => f n) d x
      = (∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n),
          (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard : ℝ) * f n) from rfl]
  rw [Commons.NumberTheory.FriedlanderIwaniec.sum_an_mul_eq_sum_box d x (fun n : ℕ => f n) hx hf0]
  rw [box_sum_eq_sum_ASum f d x hx hsupp]
  rw [Commons.NumberTheory.FriedlanderIwaniec.sum_Icc_sq_eq_sum_Z x (fun b => ASum f d b) ?_]
  · apply Finset.sum_congr rfl
    intro b _
    rw [Z_cast]
  · intro b hb
    exact ASum_eq_zero_of_gt (X := (x : ℝ)) hsupp d b (by exact_mod_cast hb)

/-- **The difference between the smoothed congruence sum and its main term.** -/
theorem AdF_sub_MdF_eq (f : ℝ → ℝ) (d x : ℕ) (hd : 0 < d) (hx : 1 ≤ x) (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, (x : ℝ) ≤ u → f u = 0) :
    AdF (fun n : ℕ => f n) d x - MdF f d x
      = (2 / (d : ℝ)) * ∑ b ∈ Finset.range (Nat.sqrt x + 1), (Z b : ℝ) *
          (∑' k : ℤ, Icos f d b k * rhoRe d b k - Icos f d b 0 * rhoRe d b 0) := by
  classical
  haveI : NeZero d := ⟨hd.ne'⟩
  have hkey : ∀ b : ℕ, ASum f d b
      = (2 / (d : ℝ)) * ∑' k : ℤ, Icos f d b k * rhoRe d b k := fun b =>
    tsum_dvd_quad_eq_rhoRe f d b hd hf
      (hasCompactSupport_quad' f (b : ℝ) (x : ℝ) hsupp)
  have hsum : (∑ b ∈ Finset.range (Nat.sqrt x + 1), (Z b : ℝ) * ASum f d b)
      = ∑ b ∈ Finset.range (Nat.sqrt x + 1), (Z b : ℝ) *
          ((2 / (d : ℝ)) * ∑' k : ℤ, Icos f d b k * rhoRe d b k) :=
    Finset.sum_congr rfl (fun b _ => by rw [hkey b])
  have hMdF : MdF f d x = (2 / (d : ℝ)) * ∑ b ∈ Finset.range (Nat.sqrt x + 1),
      (Z b : ℝ) * (Icos f d b 0 * rhoRe d b 0) := by
    rw [MdF]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    rw [Icos_zero, rhoRe_zero]
    ring
  rw [AdF_eq_sum_Z_mul_ASum f d x hd hx hsupp, hsum, hMdF, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- `I(k,b;d)` is even in `k`. -/
lemma Icos_neg (f : ℝ → ℝ) (d b : ℕ) (k : ℤ) : Icos f d b (-k) = Icos f d b k := by
  unfold Icos
  apply setIntegral_congr_fun measurableSet_Ici
  intro t _
  have h : 2 * Real.pi * ((-k : ℤ) : ℝ) * t / (d : ℝ)
      = -(2 * Real.pi * (k : ℝ) * t / (d : ℝ)) := by push_cast; ring
  simp only [h, Real.cos_neg]

/-- The positive half-line part of a summable `ℤ`-sequence is summable. -/
lemma summable_ite_pos (g : ℤ → ℝ) (hg : Summable g) :
    Summable fun k : ℤ => if 0 < k then g k else 0 :=
  Summable.of_norm_bounded hg.norm (fun k => by
    rw [Real.norm_eq_abs]
    by_cases h : 0 < k <;> simp [h, abs_nonneg])

/-- The negative half-line part of a summable `ℤ`-sequence is summable. -/
lemma summable_ite_neg (g : ℤ → ℝ) (hg : Summable g) :
    Summable fun k : ℤ => if k < 0 then g k else 0 :=
  Summable.of_norm_bounded hg.norm (fun k => by
    rw [Real.norm_eq_abs]
    by_cases h : k < 0 <;> simp [h, abs_nonneg])

/-- For an even summable sequence, the sum over `k ≠ 0` is twice the sum over `k > 0`. -/
lemma tsum_even_eq_two_mul_pos (g : ℤ → ℝ) (heven : ∀ k, g (-k) = g k) (hg : Summable g) :
    (∑' k : ℤ, (if k = 0 then 0 else g k))
      = 2 * ∑' k : ℤ, (if 0 < k then g k else 0) := by
  have hsum_pos := summable_ite_pos g hg
  have hsum_neg := summable_ite_neg g hg
  have hneg : (∑' k : ℤ, (if k < 0 then g k else 0))
      = ∑' k : ℤ, (if 0 < k then g k else 0) := by
    rw [← tsum_comp_neg (fun k : ℤ => if 0 < k then g k else 0)]
    apply tsum_congr
    intro k
    by_cases h : k < 0
    · have h' : (0 : ℤ) < -k := by omega
      rw [if_pos h, if_pos h', heven k]
    · have h' : ¬ ((0 : ℤ) < -k) := by omega
      rw [if_neg h, if_neg h']
  have hsplit : ∀ k : ℤ, (if k = 0 then (0 : ℝ) else g k)
      = (if k < 0 then g k else 0) + (if 0 < k then g k else 0) := by
    intro k
    rcases lt_trichotomy k 0 with h | h | h
    · rw [if_neg (by omega), if_pos h, if_neg (by omega)]; ring
    · subst h; simp
    · rw [if_neg (by omega), if_neg (by omega), if_pos h]; ring
  calc (∑' k : ℤ, (if k = 0 then 0 else g k))
      = ∑' k : ℤ, ((if k < 0 then g k else 0) + (if 0 < k then g k else 0)) :=
        tsum_congr hsplit
    _ = (∑' k : ℤ, (if k < 0 then g k else 0)) + ∑' k : ℤ, (if 0 < k then g k else 0) :=
        Summable.tsum_add hsum_neg hsum_pos
    _ = 2 * ∑' k : ℤ, (if 0 < k then g k else 0) := by rw [hneg]; ring

/-- `|ρ(k,b;d)| ≤ d` (there are at most `d` residue classes). -/
lemma abs_rhoRe_le (d b : ℕ) (k : ℤ) : |rhoRe d b k| ≤ (d : ℝ) := by
  set S : Finset ℕ := (Finset.range d).filter
    (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) ^ 2 + (b : ℤ) ^ 2) with hS
  have hcard : S.card ≤ d := by
    have := Finset.card_le_card
      (Finset.filter_subset (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) ^ 2 + (b : ℤ) ^ 2) (Finset.range d))
    simpa using this
  calc |rhoRe d b k|
      = |∑ r ∈ S, Real.cos (2 * Real.pi * (r : ℝ) * (k : ℝ) / (d : ℝ))| := by
        rw [rhoRe, hS]
    _ ≤ ∑ r ∈ S, |Real.cos (2 * Real.pi * (r : ℝ) * (k : ℝ) / (d : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun r _ => by
        simpa using Real.abs_cos_le_one (2 * Real.pi * (r : ℝ) * (k : ℝ) / (d : ℝ)))
    _ = (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (d : ℝ) := by exact_mod_cast hcard

/-- **The positive-frequency form of the difference identity** (paper (3.11) with the
`k ↦ −k` symmetry used). -/
theorem AdF_sub_MdF_eq_kpos (f : ℝ → ℝ) (d x : ℕ) (hd : 0 < d) (hx : 1 ≤ x)
    (hf : ContDiff ℝ 2 f) (hsupp : ∀ u, (x : ℝ) ≤ u → f u = 0) :
    AdF (fun n : ℕ => f n) d x - MdF f d x
      = (4 / (d : ℝ)) * ∑ b ∈ Finset.range (Nat.sqrt x + 1), (Z b : ℝ) *
          ∑' k : ℤ, (if 0 < k then Icos f d b k * rhoRe d b k else 0) := by
  classical
  haveI : NeZero d := ⟨hd.ne'⟩
  have hper : ∀ b : ℕ,
      (∑' k : ℤ, Icos f d b k * rhoRe d b k) - Icos f d b 0 * rhoRe d b 0
        = 2 * ∑' k : ℤ, (if 0 < k then Icos f d b k * rhoRe d b k else 0) := by
    intro b
    have hb : Summable fun k : ℤ => Icos f d b k * rhoRe d b k := by
      refine Summable.of_norm_bounded ((summable_Icos f d b hd hf
        (hasCompactSupport_quad' f (b : ℝ) (x : ℝ) hsupp)).norm.mul_left (d : ℝ))
        (fun k => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      calc |Icos f d b k| * |rhoRe d b k| ≤ |Icos f d b k| * (d : ℝ) :=
            mul_le_mul_of_nonneg_left (abs_rhoRe_le d b k) (abs_nonneg _)
        _ = (d : ℝ) * |Icos f d b k| := by ring
    have h1 : (∑' k : ℤ, Icos f d b k * rhoRe d b k) - Icos f d b 0 * rhoRe d b 0
        = ∑' k : ℤ, (if k = 0 then 0 else Icos f d b k * rhoRe d b k) := by
      rw [Summable.tsum_eq_add_tsum_ite hb 0]; ring
    rw [h1]
    exact tsum_even_eq_two_mul_pos _ (fun k => by rw [Icos_neg, rhoRe_neg]) hb
  have hS : (∑ b ∈ Finset.range (Nat.sqrt x + 1), (Z b : ℝ) *
        ((∑' k : ℤ, Icos f d b k * rhoRe d b k) - Icos f d b 0 * rhoRe d b 0))
      = ∑ b ∈ Finset.range (Nat.sqrt x + 1), (Z b : ℝ) *
        (2 * ∑' k : ℤ, (if 0 < k then Icos f d b k * rhoRe d b k else 0)) :=
    Finset.sum_congr rfl (fun b _ => by rw [hper b])
  rw [AdF_sub_MdF_eq f d x hd hx hf hsupp, hS, show (4 : ℝ) / (d : ℝ) = 2 * (2 / (d : ℝ)) by ring,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

end Submission



/-! ## THE KEY POINT: the published proof of (3.3) is complete after Abel summation

The published proof (Annals §3, and Fouvry–Iwaniec, *Gaussian primes*, Lemma 5) estimates, via
Lemma 3.3 (the large sieve = `linear_rho_bound_uniform`, already in the commons),

  `Σ_{d≤D} d·|A_d(f) − M_d(f)| ≪ D^{3/2} y^{-1} x^{11/8+ε}`   ("the weighted bound"),

and then asserts the **unweighted** estimate

  `(3.13)   Σ_{d≤D} |A_d(f) − M_d(f)| ≪ D^{1/2} y^{-1} x^{11/8+ε}`.

The printed proofs jump from the first to the second display; `d ≥ 1` alone gives only
`Σ_d |·| ≤ Σ_d d |·|`, the wrong direction.  **This is not a gap**: writing
`a_d = d·|A_d(f) − M_d(f)| ≥ 0` and `A(n) = Σ_{d≤n} a_d`, Abel summation gives the exact identity

  `Σ_{d≤n} |A_d(f) − M_d(f)| = Σ_{d≤n} a_d / d
      = A(n)/n + Σ_{i<n-1} (1/(i+1) − 1/(i+2))·A(i+1)`,

so `A(n) ≤ K n^{3/2} T` yields `Σ_{d≤n}|A_d(f) − M_d(f)| ≤ 3KT n^{1/2}`.  Thus (3.13) is a
*consequence* of the weighted bound, and Lemma 3.1 / (3.3) (our target statement) is TRUE and
provable by the published chain.  (Numerically the truth is `Σ_{d≤x^{3/4}}|A_d − M_d| ≈ 3 x^{3/4}`,
comfortably inside `C D^{1/4} x^{9/16} x^{1/100}`.)

The *only* remaining task is therefore a formalisation task: the Poisson expansion is already
available (`AdF_sub_MdF_eq_kpos` etc. above), and the remaining glue is

1. truncate the `k`-sum at `K = D y^{-1} x^{1/2+ε}` (`Commons.Analysis.Fourier.tsum_tail_Icos_le`),
2. substitute `t = u√x/k` (`Commons.Analysis.Fourier.integral_cos_quadratic_subst`) and swap sum
   and integral (`Commons.Analysis.Integral.sum_intervalIntegral_Icc_swap`) to get

     `d·|A_d(f) − M_d(f)| ≤ 4√x ∫_0^K |Y_d(u)| du`,
     `Y_d(u) = Σ_b Z(b) Σ_{u<k≤K} (1/k) f(xu²/k²+b²) rhoRe d b k`,

3. apply `linear_rho_bound_uniform` (Lemma 3.3) with `ξ_u(k,l) = (1/k) Z(l) f(xu²/k²+l²)`,
   `L = ⌊√x⌋`, giving `Σ_{d≤D'}|Y_d(u)| ≤ C(D'+√(D'KL))(D'KL)^ε ‖ξ_u‖` with `‖ξ_u‖ ≤ 2x^{1/8}/√u`,
4. integrate `∫_0^K ‖ξ_u‖du ≪ x^{1/8}√K` and sum over the dyadic `D'` via the Abel lemma above,
5. handle `b = 0` (`tsum_int_sq_dvd_le`) and the tail,
6. assemble with (3.10) (`Ad_smooth_diff_le`) and (3.12) (`MdF_sub_Md_sum_le`), choosing `f` from
   `exists_smooth_cutoff_infty` with `y = D^{1/4} x^{13/16}`, and compare the statement's `√`-main
   term with the floor main term `Md` (difference `≪ x^{1/4} log x ≪ D^{1/4}x^{9/16}`). -/

namespace Submission

/-- Reindex `∑_{d ∈ Icc 1 n} f d = ∑_{i < n} f (i+1)`. -/
lemma reindex_Icc_real (f : ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 n, f d) = ∑ i ∈ Finset.range n, f (i + 1) := by
  refine Finset.sum_bij (fun d _ => d - 1) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    simp only [Finset.mem_range]
    omega
  · intro d1 hd1 d2 hd2 h
    simp only [Finset.mem_Icc] at hd1 hd2
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    exact ⟨i + 1, by simp only [Finset.mem_Icc]; omega, by omega⟩
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    congr 1
    omega

/-- **Abel-summation bridge.**  A bound `K·D^{3/2}·T` for the `d`-weighted sum of a nonnegative
sequence `d·|R d|` propagates to `3·K·T·√D` for the unweighted sum.  This converts the weighted
large-sieve estimate of §3 into the unweighted (3.13). -/
theorem abel_sqrt_bound {R : ℕ → ℝ} {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    (h : ∀ D : ℕ, (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * |R d|)
      ≤ K * (D : ℝ) ^ ((3 : ℝ) / 2) * T) :
    ∀ D : ℕ, (∑ d ∈ Finset.Icc 1 D, |R d|) ≤ 3 * K * T * (D : ℝ) ^ ((1 : ℝ) / 2) := by
  intro D
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; simp
  have hSdef : ∀ n, (∑ i ∈ Finset.range n, |R (i + 1)|) = (∑ d ∈ Finset.Icc 1 n, |R d|) := by
    intro n; rw [reindex_Icc_real (fun d => |R d|) n]
  have hWdef : ∀ n, (∑ i ∈ Finset.range n, ((i : ℝ) + 1) * |R (i + 1)|)
      = (∑ d ∈ Finset.Icc 1 n, (d : ℝ) * |R d|) := by
    intro n
    rw [reindex_Icc_real (fun d => (d : ℝ) * |R d|) n]
    apply Finset.sum_congr rfl
    intro i _
    push_cast; ring
  -- summation by parts
  have hbp := Finset.sum_range_by_parts (fun i : ℕ => (((i : ℝ) + 1)⁻¹ : ℝ))
      (fun i : ℕ => ((i : ℝ) + 1) * |R (i + 1)|) D
  simp only [smul_eq_mul] at hbp
  have hLHS : (∑ i ∈ Finset.range D, (((i : ℝ) + 1)⁻¹) * (((i : ℝ) + 1) * |R (i + 1)|))
      = (∑ d ∈ Finset.Icc 1 D, |R d|) := by
    rw [← hSdef D]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hkey : (∑ d ∈ Finset.Icc 1 D, |R d|)
      = ((D : ℝ))⁻¹ * (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * |R d|)
        - ∑ i ∈ Finset.range (D - 1),
            ((((i : ℝ) + 2)⁻¹) - (((i : ℝ) + 1)⁻¹))
              * (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|) := by
    rw [← hLHS, hbp, hWdef D]
    congr 1
    · congr 1
      push_cast [Nat.cast_sub hD]; ring
    · apply Finset.sum_congr rfl
      intro i _
      rw [← hWdef (i + 1)]
      push_cast; ring
  rw [hkey]
  have h1 : ((D : ℝ))⁻¹ * (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * |R d|)
      ≤ K * T * (D : ℝ) ^ ((1 : ℝ) / 2) := by
    have hD0 : (0 : ℝ) < (D : ℝ) := by positivity
    have hle := h D
    have hstep : ((D : ℝ))⁻¹ * (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * |R d|)
        ≤ ((D : ℝ))⁻¹ * (K * (D : ℝ) ^ ((3 : ℝ) / 2) * T) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    rw [show ((3 : ℝ) / 2) = 1 + (1 : ℝ) / 2 by norm_num, Real.rpow_add hD0, Real.rpow_one]
    field_simp
  have h2 : -(∑ i ∈ Finset.range (D - 1),
        ((((i : ℝ) + 2)⁻¹) - (((i : ℝ) + 1)⁻¹)) * (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|))
      ≤ 2 * K * T * (D : ℝ) ^ ((1 : ℝ) / 2) := by
    have hrew : -(∑ i ∈ Finset.range (D - 1),
        ((((i : ℝ) + 2)⁻¹) - (((i : ℝ) + 1)⁻¹)) * (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|))
        = ∑ i ∈ Finset.range (D - 1),
            ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _; ring
    rw [hrew]
    have hstep : (∑ i ∈ Finset.range (D - 1),
            ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|))
        ≤ ∑ i ∈ Finset.range (D - 1),
            ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (K * ((i : ℝ) + 1) ^ ((3 : ℝ) / 2) * T) := by
      apply Finset.sum_le_sum
      intro i _
      have hh := h (i + 1)
      simp only [Nat.cast_add, Nat.cast_one] at hh
      refine mul_le_mul_of_nonneg_left hh ?_
      have h1 : (0:ℝ) < (i:ℝ)+1 := by positivity
      have := inv_anti₀ h1 (by linarith : ((i:ℝ)+1) ≤ ((i:ℝ)+2))
      linarith
    refine le_trans hstep ?_
    have hsimp : (∑ i ∈ Finset.range (D - 1),
            ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (K * ((i : ℝ) + 1) ^ ((3 : ℝ) / 2) * T))
        = K * T * ∑ i ∈ Finset.range (D - 1),
            ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (((i : ℝ) + 1) ^ ((3 : ℝ) / 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; ring
    rw [hsimp]
    have hpoint : ∀ i ∈ Finset.range (D - 1),
        ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (((i : ℝ) + 1) ^ ((3 : ℝ) / 2))
          ≤ (((i : ℝ) + 1)) ^ (-(1 : ℝ) / 2) := by
      intro i _
      have h1 : (0:ℝ) < (i:ℝ)+1 := by positivity
      have h2 : (0:ℝ) < (i:ℝ)+2 := by positivity
      have hpow : ((i:ℝ)+1) ^ ((3:ℝ)/2) = ((i:ℝ)+1) * (((i:ℝ)+1) ^ ((1:ℝ)/2)) := by
        rw [show ((3:ℝ)/2) = 1 + (1:ℝ)/2 by norm_num, Real.rpow_add h1, Real.rpow_one]
      have hcar : (((i:ℝ)+1)⁻¹ - ((i:ℝ)+2)⁻¹) * (((i:ℝ)+1) * ((i:ℝ)+1)^((1:ℝ)/2))
          = ((i:ℝ)+2)⁻¹ * ((i:ℝ)+1)^((1:ℝ)/2) := by
        field_simp; ring
      rw [hpow, hcar]
      have hApos : 0 < ((i:ℝ)+1) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos h1 _
      have hAsq : ((i:ℝ)+1) ^ ((1:ℝ)/2) * ((i:ℝ)+1) ^ ((1:ℝ)/2) = ((i:ℝ)+1) := by
        rw [← Real.rpow_add h1]; norm_num
      rw [show (((i:ℝ)+1)) ^ (-(1:ℝ)/2) = (((i:ℝ)+1)^((1:ℝ)/2))⁻¹ from by
        rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by norm_num, Real.rpow_neg (le_of_lt h1)]]
      -- `(1/(i+2))·A ≤ A⁻¹` since `A² = i+1 ≤ i+2`
      rw [← sub_nonneg]
      have hexp : (((i:ℝ)+1)^((1:ℝ)/2))⁻¹ - ((i:ℝ)+2)⁻¹ * ((i:ℝ)+1)^((1:ℝ)/2)
          = (((i:ℝ)+2) - ((i:ℝ)+1)^((1:ℝ)/2) * ((i:ℝ)+1)^((1:ℝ)/2)) / (((i:ℝ)+2) * ((i:ℝ)+1)^((1:ℝ)/2)) := by
        field_simp
      rw [hexp]
      apply div_nonneg _ (by positivity)
      rw [hAsq]; linarith
    have hsum : (∑ i ∈ Finset.range (D - 1), (((i : ℝ) + 1)) ^ (-(1 : ℝ) / 2))
        ≤ 2 * (D : ℝ) ^ ((1 : ℝ) / 2) := by
      have hshift : (∑ i ∈ Finset.range (D - 1), (((i : ℝ) + 1)) ^ (-(1 : ℝ) / 2))
          = ∑ d ∈ Finset.Icc 1 (D - 1), ((d : ℝ)) ^ (-(1 : ℝ) / 2) := by
        rw [reindex_Icc_real (fun d : ℕ => ((d : ℝ)) ^ (-(1 : ℝ) / 2)) (D - 1)]
        apply Finset.sum_congr rfl
        intro i _; push_cast; ring_nf
      rw [hshift]
      have hpt : ∀ d ∈ Finset.Icc 1 (D - 1), ((d : ℝ)) ^ (-(1 : ℝ) / 2) = (Real.sqrt (d : ℝ))⁻¹ := by
        intro d _
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity : (0:ℝ) ≤ (d:ℝ))]
        norm_num
      calc (∑ d ∈ Finset.Icc 1 (D - 1), ((d : ℝ)) ^ (-(1 : ℝ) / 2))
          = ∑ d ∈ Finset.Icc 1 (D - 1), (Real.sqrt (d : ℝ))⁻¹ := Finset.sum_congr rfl hpt
        _ ≤ 2 * Real.sqrt ((D - 1 : ℕ) : ℝ) := Commons.Analysis.Sum.sum_inv_sqrt_le (D - 1)
        _ ≤ 2 * (D : ℝ) ^ ((1 : ℝ) / 2) := by
            have h1 : Real.sqrt ((D - 1 : ℕ) : ℝ) ≤ Real.sqrt (D : ℝ) := by
              apply Real.sqrt_le_sqrt
              push_cast [Nat.cast_sub hD]; linarith
            have h2 : Real.sqrt (D : ℝ) = (D : ℝ) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow D
            nlinarith [h1, h2]
    calc K * T * (∑ i ∈ Finset.range (D - 1), ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (((i : ℝ) + 1) ^ ((3 : ℝ) / 2)))
        ≤ K * T * (∑ i ∈ Finset.range (D - 1), (((i : ℝ) + 1)) ^ (-(1 : ℝ) / 2)) := by
          apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) (by positivity)
      _ ≤ K * T * (2 * (D : ℝ) ^ ((1:ℝ)/2)) := by
          apply mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 2 * K * T * (D : ℝ) ^ ((1:ℝ)/2) := by
          have : K * T * (2 * (D : ℝ) ^ ((1:ℝ)/2)) = 2 * K * T * (D : ℝ) ^ ((1:ℝ)/2) := by ring
          rw [this]
  have hDnn : 0 ≤ (D : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg D) _
  linarith [h1, h2]


/-- **Hybrid Abel-summation bridge.**  If the `d`-weighted partial sums are `≪ n^{3/2}` for
`n ≥ D₀` and `≪ n²` for `n ≤ D₀`, then the unweighted sum is `≪ √D + D₀`. -/
theorem abel_sqrt_bound_hybrid (D₀ : ℕ) {R : ℕ → ℝ} {K T B : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (h1 : ∀ D : ℕ, D₀ ≤ D → (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * |R d|)
      ≤ K * (D : ℝ) ^ ((3 : ℝ) / 2) * T)
    (h2 : ∀ D : ℕ, D ≤ D₀ → (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * |R d|)
      ≤ B * (D : ℝ) ^ 2) :
    ∀ D : ℕ, 1 ≤ D → D₀ ≤ D →
      (∑ d ∈ Finset.Icc 1 D, |R d|)
        ≤ 3 * K * T * (D : ℝ) ^ ((1 : ℝ) / 2) + 2 * B * (D₀ : ℝ) := by
  intro D hD1 hD0
  have hD : 0 < D := hD1
  have hSdef : ∀ n, (∑ i ∈ Finset.range n, |R (i + 1)|) = (∑ d ∈ Finset.Icc 1 n, |R d|) := by
    intro n; rw [reindex_Icc_real (fun d => |R d|) n]
  have hWdef : ∀ n, (∑ i ∈ Finset.range n, ((i : ℝ) + 1) * |R (i + 1)|)
      = (∑ d ∈ Finset.Icc 1 n, (d : ℝ) * |R d|) := by
    intro n
    rw [reindex_Icc_real (fun d => (d : ℝ) * |R d|) n]
    apply Finset.sum_congr rfl
    intro i _
    push_cast; ring
  have hbp := Finset.sum_range_by_parts (fun i : ℕ => (((i : ℝ) + 1)⁻¹ : ℝ))
      (fun i : ℕ => ((i : ℝ) + 1) * |R (i + 1)|) D
  simp only [smul_eq_mul] at hbp
  have hLHS : (∑ i ∈ Finset.range D, (((i : ℝ) + 1)⁻¹) * (((i : ℝ) + 1) * |R (i + 1)|))
      = (∑ d ∈ Finset.Icc 1 D, |R d|) := by
    rw [← hSdef D]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hkey : (∑ d ∈ Finset.Icc 1 D, |R d|)
      = ((D : ℝ))⁻¹ * (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * |R d|)
        - ∑ i ∈ Finset.range (D - 1),
            ((((i : ℝ) + 2)⁻¹) - (((i : ℝ) + 1)⁻¹))
              * (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|) := by
    rw [← hLHS, hbp, hWdef D]
    congr 1
    · congr 1
      push_cast [Nat.cast_sub hD]; ring
    · apply Finset.sum_congr rfl
      intro i _
      rw [← hWdef (i + 1)]
      push_cast; ring
  rw [hkey]
  have h1' : ((D : ℝ))⁻¹ * (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * |R d|)
      ≤ K * T * (D : ℝ) ^ ((1 : ℝ) / 2) := by
    have hD0' : (0 : ℝ) < (D : ℝ) := by positivity
    have hle := h1 D hD0
    have hstep : ((D : ℝ))⁻¹ * (∑ d ∈ Finset.Icc 1 D, (d : ℝ) * |R d|)
        ≤ ((D : ℝ))⁻¹ * (K * (D : ℝ) ^ ((3 : ℝ) / 2) * T) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    rw [show ((3 : ℝ) / 2) = 1 + (1 : ℝ) / 2 by norm_num, Real.rpow_add hD0', Real.rpow_one]
    field_simp
  have h2' : -(∑ i ∈ Finset.range (D - 1),
        ((((i : ℝ) + 2)⁻¹) - (((i : ℝ) + 1)⁻¹)) * (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|))
      ≤ 2 * K * T * (D : ℝ) ^ ((1 : ℝ) / 2) + 2 * B * (D₀ : ℝ) := by
    have hrew : -(∑ i ∈ Finset.range (D - 1),
        ((((i : ℝ) + 2)⁻¹) - (((i : ℝ) + 1)⁻¹)) * (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|))
        = ∑ i ∈ Finset.range (D - 1),
            ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _; ring
    rw [hrew]
    -- the weights are nonnegative
    have hw : ∀ i : ℕ, (0:ℝ) ≤ ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) := by
      intro i
      have h1 : (0:ℝ) < (i:ℝ)+1 := by positivity
      have := inv_anti₀ h1 (by linarith : ((i:ℝ)+1) ≤ ((i:ℝ)+2))
      linarith
    -- pointwise: bound `W(i+1)` by the appropriate regime
    have hpoint : ∀ i ∈ Finset.range (D - 1),
        ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|)
        ≤ ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹))
            * (K * ((i : ℝ) + 1) ^ ((3 : ℝ) / 2) * T)
          + ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹))
            * (if (i + 1) < D₀ then B * ((i : ℝ) + 1) ^ 2 else 0) := by
      intro i _
      have hw' := hw i
      by_cases hc : D₀ ≤ i + 1
      · have hh := h1 (i + 1) hc
        have hh' : (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|)
            ≤ K * ((i:ℝ)+1)^((3:ℝ)/2) * T := by
          simpa [Nat.cast_add, Nat.cast_one] using hh
        have hz : (if (i + 1) < D₀ then B * ((i : ℝ) + 1) ^ 2 else 0) = 0 := by
          rw [if_neg (by omega)]
        rw [hz, mul_zero, add_zero]
        exact mul_le_mul_of_nonneg_left hh' hw'
      · have hh := h2 (i + 1) (by omega)
        have hh' : (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|) ≤ B * ((i:ℝ)+1)^2 := by
          simpa [Nat.cast_add, Nat.cast_one] using hh
        rw [if_pos (by omega)]
        calc ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|)
            ≤ ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (B * ((i : ℝ) + 1) ^ 2) :=
              mul_le_mul_of_nonneg_left hh' hw'
          _ ≤ ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (K * ((i : ℝ) + 1) ^ ((3 : ℝ) / 2) * T)
                + ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (B * ((i : ℝ) + 1) ^ 2) := by
              have hKA : (0:ℝ) ≤ ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹))
                  * (K * ((i : ℝ) + 1) ^ ((3 : ℝ) / 2) * T) := by positivity
              linarith
    have hsum := Finset.sum_le_sum hpoint
    -- bound the two pieces
    have hA : (∑ i ∈ Finset.range (D - 1),
          ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (K * ((i : ℝ) + 1) ^ ((3 : ℝ) / 2) * T))
        ≤ 2 * K * T * (D : ℝ) ^ ((1 : ℝ) / 2) := by
      have hsimp : (∑ i ∈ Finset.range (D - 1),
              ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (K * ((i : ℝ) + 1) ^ ((3 : ℝ) / 2) * T))
          = K * T * ∑ i ∈ Finset.range (D - 1),
              ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (((i : ℝ) + 1) ^ ((3 : ℝ) / 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _; ring
      rw [hsimp]
      have hpoint2 : ∀ i ∈ Finset.range (D - 1),
          ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (((i : ℝ) + 1) ^ ((3 : ℝ) / 2))
            ≤ (((i : ℝ) + 1)) ^ (-(1 : ℝ) / 2) := by
        intro i _
        have h1 : (0:ℝ) < (i:ℝ)+1 := by positivity
        have h2 : (0:ℝ) < (i:ℝ)+2 := by positivity
        have hpow : ((i:ℝ)+1) ^ ((3:ℝ)/2) = ((i:ℝ)+1) * (((i:ℝ)+1) ^ ((1:ℝ)/2)) := by
          rw [show ((3:ℝ)/2) = 1 + (1:ℝ)/2 by norm_num, Real.rpow_add h1, Real.rpow_one]
        have hcar : (((i:ℝ)+1)⁻¹ - ((i:ℝ)+2)⁻¹) * (((i:ℝ)+1) * ((i:ℝ)+1)^((1:ℝ)/2))
            = ((i:ℝ)+2)⁻¹ * ((i:ℝ)+1)^((1:ℝ)/2) := by
          field_simp; ring
        rw [hpow, hcar]
        have hAsq : ((i:ℝ)+1) ^ ((1:ℝ)/2) * ((i:ℝ)+1) ^ ((1:ℝ)/2) = ((i:ℝ)+1) := by
          rw [← Real.rpow_add h1]; norm_num
        rw [show (((i:ℝ)+1)) ^ (-(1:ℝ)/2) = (((i:ℝ)+1)^((1:ℝ)/2))⁻¹ from by
          rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by norm_num, Real.rpow_neg (le_of_lt h1)]]
        rw [← sub_nonneg]
        have hexp : (((i:ℝ)+1)^((1:ℝ)/2))⁻¹ - ((i:ℝ)+2)⁻¹ * ((i:ℝ)+1)^((1:ℝ)/2)
            = (((i:ℝ)+2) - ((i:ℝ)+1)^((1:ℝ)/2) * ((i:ℝ)+1)^((1:ℝ)/2))
                / (((i:ℝ)+2) * ((i:ℝ)+1)^((1:ℝ)/2)) := by
          field_simp
        rw [hexp]
        apply div_nonneg _ (by positivity)
        rw [hAsq]; linarith
      have hsum2 : (∑ i ∈ Finset.range (D - 1), (((i : ℝ) + 1)) ^ (-(1 : ℝ) / 2))
          ≤ 2 * (D : ℝ) ^ ((1 : ℝ) / 2) := by
        have hshift : (∑ i ∈ Finset.range (D - 1), (((i : ℝ) + 1)) ^ (-(1 : ℝ) / 2))
            = ∑ d ∈ Finset.Icc 1 (D - 1), ((d : ℝ)) ^ (-(1 : ℝ) / 2) := by
          rw [reindex_Icc_real (fun d : ℕ => ((d : ℝ)) ^ (-(1 : ℝ) / 2)) (D - 1)]
          apply Finset.sum_congr rfl
          intro i _; push_cast; ring_nf
        rw [hshift]
        have hmain := Commons.Analysis.Sum.sum_inv_sqrt_le (D - 1)
        have hconv : (∑ d ∈ Finset.Icc 1 (D - 1), ((d : ℝ)) ^ (-(1 : ℝ) / 2))
            = ∑ d ∈ Finset.Icc 1 (D - 1), (Real.sqrt (d:ℝ))⁻¹ := by
          apply Finset.sum_congr rfl
          intro d _
          rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by norm_num, Real.rpow_neg (by positivity),
              Real.sqrt_eq_rpow]
        rw [hconv]
        have hcast : Real.sqrt (((D - 1 : ℕ) : ℝ)) ≤ (D:ℝ) ^ ((1:ℝ)/2) := by
          rw [Real.sqrt_eq_rpow]
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
          exact_mod_cast Nat.sub_le D 1
        linarith [hmain, hcast]
      have hsumA : (∑ i ∈ Finset.range (D - 1),
          ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (((i : ℝ) + 1) ^ ((3 : ℝ) / 2)))
          ≤ 2 * (D : ℝ) ^ ((1 : ℝ) / 2) := by
        calc (∑ i ∈ Finset.range (D - 1),
              ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (((i : ℝ) + 1) ^ ((3 : ℝ) / 2)))
            ≤ ∑ i ∈ Finset.range (D - 1), (((i : ℝ) + 1)) ^ (-(1 : ℝ) / 2) :=
              Finset.sum_le_sum hpoint2
          _ ≤ 2 * (D : ℝ) ^ ((1 : ℝ) / 2) := hsum2
      calc K * T * ∑ i ∈ Finset.range (D - 1),
              ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (((i : ℝ) + 1) ^ ((3 : ℝ) / 2))
          ≤ K * T * (2 * (D : ℝ) ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hsumA (by positivity)
        _ = 2 * K * T * (D : ℝ) ^ ((1 : ℝ) / 2) := by ring
    have hB1 : (∑ i ∈ Finset.range (D - 1),
          ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹))
            * (if (i + 1) < D₀ then B * ((i : ℝ) + 1) ^ 2 else 0))
        ≤ 2 * B * (D₀ : ℝ) := by
      have hpoint3 : ∀ i ∈ Finset.range (D - 1),
          ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹))
            * (if (i + 1) < D₀ then B * ((i : ℝ) + 1) ^ 2 else 0)
          ≤ (if (i + 1) < D₀ then B * 1 else 0) := by
        intro i _
        by_cases hc : (i + 1) < D₀
        · rw [if_pos hc, if_pos hc]
          have h1 : (0:ℝ) < (i:ℝ)+1 := by positivity
          have h2 : (0:ℝ) < (i:ℝ)+2 := by positivity
          have hw' : (((i:ℝ)+1)⁻¹ - ((i:ℝ)+2)⁻¹) * ((i:ℝ)+1)^2 ≤ 1 := by
            have h3 : (((i:ℝ)+1)⁻¹ - ((i:ℝ)+2)⁻¹) * ((i:ℝ)+1)^2 = ((i:ℝ)+1)/((i:ℝ)+2) := by
              field_simp; ring
            rw [h3, div_le_one h2]
            linarith
          calc (((i:ℝ)+1)⁻¹ - ((i:ℝ)+2)⁻¹) * (B * ((i:ℝ)+1)^2)
              = B * ((((i:ℝ)+1)⁻¹ - ((i:ℝ)+2)⁻¹) * ((i:ℝ)+1)^2) := by ring
            _ ≤ B * 1 := mul_le_mul_of_nonneg_left hw' hB
            _ = B * 1 := rfl
        · rw [if_neg hc, if_neg hc, mul_zero]
      calc (∑ i ∈ Finset.range (D - 1),
            ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹))
              * (if (i + 1) < D₀ then B * ((i : ℝ) + 1) ^ 2 else 0))
          ≤ ∑ i ∈ Finset.range (D - 1), (if (i + 1) < D₀ then B * 1 else 0) :=
            Finset.sum_le_sum hpoint3
        _ = B * ((Finset.range (D - 1)).filter (fun i => i + 1 < D₀)).card := by
            rw [show (∑ i ∈ Finset.range (D-1), (if (i+1) < D₀ then B*1 else 0))
                = B * (∑ i ∈ Finset.range (D-1), (if (i+1) < D₀ then (1:ℝ) else 0)) from by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              by_cases h : i + 1 < D₀ <;> simp [h]]
            rw [Finset.sum_boole]
        _ ≤ 2 * B * (D₀ : ℝ) := by
            have hcard : ((Finset.range (D - 1)).filter (fun i => i + 1 < D₀)).card ≤ D₀ := by
              calc ((Finset.range (D - 1)).filter (fun i => i + 1 < D₀)).card
                  ≤ (Finset.range D₀).card := by
                    apply Finset.card_le_card
                    intro i hi
                    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
                    omega
                _ = D₀ := Finset.card_range D₀
            have hcast : (((Finset.range (D - 1)).filter (fun i => i + 1 < D₀)).card : ℝ)
                ≤ (D₀ : ℝ) := by exact_mod_cast hcard
            have h2 : (B * ((Finset.range (D - 1)).filter (fun i => i + 1 < D₀)).card : ℝ)
                ≤ B * (D₀ : ℝ) := mul_le_mul_of_nonneg_left hcast hB
            have hBnn : (0:ℝ) ≤ B * (D₀:ℝ) := mul_nonneg hB (Nat.cast_nonneg D₀)
            linarith [h2, hBnn]
    have hsplit : (∑ i ∈ Finset.range (D - 1),
          ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|))
        ≤ (∑ i ∈ Finset.range (D - 1),
            ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (K * ((i : ℝ) + 1) ^ ((3 : ℝ) / 2) * T))
          + (∑ i ∈ Finset.range (D - 1),
            ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹))
              * (if (i + 1) < D₀ then B * ((i : ℝ) + 1) ^ 2 else 0)) := by
      calc (∑ i ∈ Finset.range (D - 1),
            ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (∑ d ∈ Finset.Icc 1 (i + 1), (d : ℝ) * |R d|))
          ≤ ∑ i ∈ Finset.range (D - 1),
              (((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹)) * (K * ((i : ℝ) + 1) ^ ((3 : ℝ) / 2) * T)
                + ((((i : ℝ) + 1)⁻¹) - (((i : ℝ) + 2)⁻¹))
                  * (if (i + 1) < D₀ then B * ((i : ℝ) + 1) ^ 2 else 0)) := hsum
        _ = _ := Finset.sum_add_distrib
    linarith [hsplit, hA, hB1]
  linarith [h1', h2']

end Submission

namespace Submission

/- ### The `b = 0` (lattice) part of the smoothed remainder estimate. -/


open Finset MeasureTheory
open Submission

noncomputable def sqrtK (d : ℕ) : ℕ := ∏ p ∈ d.primeFactors, p ^ ((d.factorization p + 1) / 2)

lemma sqrtK_pos (d : ℕ) : 0 < sqrtK d := by
  rw [sqrtK]
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.mem_primeFactors.mp hp).1.pos _

lemma sqrtK_ne_zero (d : ℕ) : sqrtK d ≠ 0 := (sqrtK_pos d).ne'

lemma sqrtK_factorization (d q : ℕ) :
    (sqrtK d).factorization q
      = if q ∈ d.primeFactors then (d.factorization q + 1) / 2 else 0 := by
  have hterm : ∀ x ∈ d.primeFactors,
      ((d.factorization x + 1) / 2) * x.factorization q = if x = q then (d.factorization x + 1) / 2 else 0 := by
    intro x hx
    rw [(Nat.mem_primeFactors.mp hx).1.factorization, Finsupp.single_apply]
    by_cases hxq : x = q <;> simp [hxq]
  rw [sqrtK, Nat.factorization_prod
    (fun p hp => pow_ne_zero _ (Nat.mem_primeFactors.mp hp).1.ne_zero)]
  rw [Finsupp.finsetSum_apply]
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']

lemma div_two_arith (v : ℕ) : (v + 1) / 2 + v / 2 = v := by omega

lemma div_two_arith' (v m : ℕ) : (v + 1) / 2 ≤ m ↔ v ≤ 2 * m := by
  rw [Nat.div_le_iff_le_mul_add_pred (by norm_num : (0:ℕ) < 2)]
  omega

lemma dvd_sq_iff_sqrtK_dvd (d a : ℕ) (hd : 1 ≤ d) (ha : 1 ≤ a) : d ∣ a ^ 2 ↔ sqrtK d ∣ a := by
  have hd0 : d ≠ 0 := by omega
  have ha0 : a ≠ 0 := by omega
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero _ ha0
  rw [← Nat.factorization_le_iff_dvd hd0 ha2, ← Nat.factorization_le_iff_dvd (sqrtK_ne_zero d) ha0]
  rw [Nat.factorization_pow, Finsupp.le_def, Finsupp.le_def]
  constructor
  · intro h q
    rw [sqrtK_factorization]
    by_cases hqs : q ∈ d.primeFactors
    · rw [if_pos hqs, div_two_arith']
      have := h q
      rw [Finsupp.smul_apply, smul_eq_mul] at this
      linarith
    · rw [if_neg hqs]; exact Nat.zero_le _
  · intro h q
    rw [Finsupp.smul_apply, smul_eq_mul]
    by_cases hqs : q ∈ d.primeFactors
    · have hq := h q
      rw [sqrtK_factorization, if_pos hqs, div_two_arith'] at hq
      linarith
    · have hzero : d.factorization q = 0 := by
        by_contra hne
        exact hqs (by
          have : q ∈ d.factorization.support := by rwa [Finsupp.mem_support_iff]
          rwa [Nat.support_factorization] at this)
      rw [hzero]; exact Nat.zero_le _

lemma sqrtK_mul_rho_zero_eq (d : ℕ) (hd : 1 ≤ d) : sqrtK d * rho 0 d = d := by
  have hd0 : d ≠ 0 := by omega
  rw [rho_zero_eq_sqZero]
  rw [Commons.NumberTheory.FriedlanderIwaniec.sq_roots_zero_card (by omega)]
  rw [sqrtK, ← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl (g := fun p => p ^ d.factorization p) (fun p hp => by
    rw [← pow_add, div_two_arith])]
  exact (Nat.prod_primeFactors_pow_factorization hd0).symm

/-- Integer form of the lattice description of `{a : d ∣ a²}`. -/
lemma int_dvd_sq_iff_sqrtK_dvd (d : ℕ) (hd : 1 ≤ d) (a : ℤ) :
    (d : ℤ) ∣ a ^ 2 ↔ (sqrtK d : ℤ) ∣ a := by
  have h1 : (d : ℤ) ∣ a ^ 2 ↔ d ∣ a.natAbs ^ 2 := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow, Int.natAbs_natCast]
  have h2 : (sqrtK d : ℤ) ∣ a ↔ sqrtK d ∣ a.natAbs := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
  rcases eq_or_ne a 0 with rfl | ha
  · constructor <;> intro h
    · rw [h2]; exact dvd_zero _
    · exact dvd_zero _
  · have ha0 : 0 < a.natAbs := Int.natAbs_pos.mpr ha
    have ha1 : 1 ≤ a.natAbs := by omega
    rw [h1, h2, dvd_sq_iff_sqrtK_dvd d a.natAbs hd ha1]

/-- The `b = 0` sum reduces to a finite sum over `|a| ≤ x`. -/
lemma ASum_zero_eq_finset (f : ℝ → ℝ) (d x : ℕ) (hx : 1 ≤ x)
    (hsupp : ∀ u, (x : ℝ) ≤ u → f u = 0) :
    ASum f d 0 = ∑ a ∈ Finset.Icc (-(x : ℤ)) (x : ℤ),
      (if (d : ℤ) ∣ a ^ 2 then f ((a : ℝ) ^ 2) else 0) := by
  have hsimp : ∀ a : ℤ, (if (d : ℤ) ∣ a ^ 2 + (0:ℤ)^2 then f ((a:ℝ)^2 + ((0:ℕ):ℝ)^2) else 0)
      = (if (d : ℤ) ∣ a ^ 2 then f ((a:ℝ)^2) else 0) := by
    intro a; norm_num
  unfold ASum
  rw [show (fun a : ℤ => (if (d : ℤ) ∣ a ^ 2 + ((0:ℕ):ℤ) ^ 2 then
        f ((a : ℝ) ^ 2 + ((0:ℕ):ℝ) ^ 2) else 0))
      = fun a : ℤ => (if (d : ℤ) ∣ a ^ 2 then f ((a : ℝ) ^ 2) else 0) from funext hsimp]
  rw [tsum_eq_sum (s := Finset.Icc (-(x : ℤ)) (x : ℤ)) (fun a ha => ?_)]
  · by_cases h : (d : ℤ) ∣ a ^ 2
    · rw [if_pos h]
      refine hsupp _ ?_
      rw [Finset.mem_Icc, not_and_or] at ha
      have hxk : (x : ℤ) < |a| := by
        rcases ha with h' | h'
        · have : a < 0 := by omega
          rw [abs_of_neg this]; omega
        · have : 0 < a := by omega
          rw [abs_of_pos this]; omega
      have hxR : (x : ℝ) < |(a : ℝ)| := by
        calc (x : ℝ) < ((|a| : ℤ) : ℝ) := by exact_mod_cast hxk
          _ = |(a : ℝ)| := Int.cast_abs
      have habs : |(x : ℝ)| < |(a : ℝ)| := by
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (x:ℝ))]; exact hxR
      have h2 : (x : ℝ) ^ 2 < (a : ℝ) ^ 2 := sq_lt_sq.mpr habs
      have : (x : ℝ) ≤ (x : ℝ) ^ 2 := by
        have h1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
        nlinarith
      linarith
    · rw [if_neg h]



/-- The `b = 0` sum, reindexed onto the lattice `sqrtK d · ℤ`. -/
lemma ASum_zero_eq_lattice (f : ℝ → ℝ) (d x : ℕ) (hd : 1 ≤ d) (hx : 1 ≤ x)
    (hsupp : ∀ u, (x : ℝ) ≤ u → f u = 0) :
    ASum f d 0
      = ∑ j ∈ Finset.Icc (-((x / sqrtK d : ℕ) : ℤ)) ((x / sqrtK d : ℕ) : ℤ),
          f ((((sqrtK d : ℤ) * j : ℤ) : ℝ) ^ 2) := by
  have hm : 1 ≤ sqrtK d := sqrtK_pos d
  have hm0 : (sqrtK d : ℤ) ≠ 0 := by
    simp only [ne_eq, Int.natCast_eq_zero]; exact (sqrtK_pos d).ne'
  rw [ASum_zero_eq_finset f d x hx hsupp]
  have hsimp : ∀ a : ℤ, (if (d : ℤ) ∣ a ^ 2 then f ((a : ℝ) ^ 2) else 0)
      = (if (sqrtK d : ℤ) ∣ a then f ((a : ℝ) ^ 2) else 0) := by
    intro a
    simp only [int_dvd_sq_iff_sqrtK_dvd d hd a]
  simp only [hsimp]
  rw [← Finset.sum_filter]
  set K : ℕ := x / sqrtK d with hK
  have himg : (Finset.Icc (-(x : ℤ)) (x : ℤ)).filter (fun a : ℤ => (sqrtK d : ℤ) ∣ a)
      = (Finset.Icc (-(K : ℤ)) (K : ℤ)).image (fun j : ℤ => ((sqrtK d : ℤ) * j : ℤ)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, ⟨j, rfl⟩⟩
      have habs : |(sqrtK d : ℤ) * j| ≤ (x : ℤ) := by rw [abs_le]; exact ⟨hlo, hhi⟩
      rw [Int.abs_eq_natAbs, Int.natAbs_mul, Int.natAbs_natCast] at habs
      have h3 : j.natAbs ≤ K := by
        rw [hK, Nat.le_div_iff_mul_le (by omega : 0 < sqrtK d), mul_comm]
        exact_mod_cast habs
      have h4 : |j| ≤ (K : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h3
      exact ⟨j, abs_le.mp h4, rfl⟩
    · rintro ⟨j, ⟨hlo, hhi⟩, rfl⟩
      have h4 : |j| ≤ (K : ℤ) := abs_le.mpr ⟨hlo, hhi⟩
      rw [Int.abs_eq_natAbs] at h4
      have h3 : j.natAbs ≤ K := by exact_mod_cast h4
      have h5 : j.natAbs * sqrtK d ≤ x := by
        rw [hK, Nat.le_div_iff_mul_le (by omega : 0 < sqrtK d)] at h3
        exact h3
      have habs : |(sqrtK d : ℤ) * j| ≤ (x : ℤ) := by
        rw [Int.abs_eq_natAbs, Int.natAbs_mul, Int.natAbs_natCast]
        rw [mul_comm]; exact_mod_cast h5
      exact ⟨abs_le.mp habs, ⟨j, rfl⟩⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hm0 h)]


/-- A symmetric sum of an even function over `Icc (-n) n`. -/
lemma sum_Icc_neg_even (ψ : ℤ → ℝ) (heven : ∀ j, ψ (-j) = ψ j) (n : ℕ) :
    ∑ j ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), ψ j
      = ψ 0 + 2 * ∑ j ∈ Finset.Icc (1:ℤ) (n:ℤ), ψ j := by
  rcases Nat.eq_zero_or_pos n with h | hn
  · subst h
    simp [Finset.Icc_self]
  have hunion : Finset.Icc (-(n:ℤ)) (n:ℤ) = Finset.Icc (-(n:ℤ)) (-1) ∪ Finset.Icc (0:ℤ) (n:ℤ) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc (-(n:ℤ)) (-1)) (Finset.Icc (0:ℤ) (n:ℤ)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  have hneg : ∑ j ∈ Finset.Icc (-(n:ℤ)) (-1), ψ j = ∑ j ∈ Finset.Icc (1:ℤ) (n:ℤ), ψ j := by
    have himg : Finset.Icc (-(n:ℤ)) (-1) = (Finset.Icc (1:ℤ) (n:ℤ)).image (fun i : ℤ => -i) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_image]
      constructor
      · intro ⟨h1, h2⟩
        exact ⟨-j, by omega, by omega⟩
      · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
        omega
    rw [himg, Finset.sum_image (by
      intro a _ b _ h
      exact neg_injective h)]
    exact Finset.sum_congr rfl (fun i _ => heven i)
  have hpos : ∑ j ∈ Finset.Icc (0:ℤ) (n:ℤ), ψ j
      = ψ 0 + ∑ j ∈ Finset.Icc (1:ℤ) (n:ℤ), ψ j := by
    have hun2 : Finset.Icc (0:ℤ) (n:ℤ) = {0} ∪ Finset.Icc (1:ℤ) (n:ℤ) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
      omega
    have hd2 : Disjoint ({0} : Finset ℤ) (Finset.Icc (1:ℤ) (n:ℤ)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_singleton] at ha
      simp only [Finset.mem_Icc] at hb
      omega
    rw [hun2, Finset.sum_union hd2, Finset.sum_singleton]
  rw [hunion, Finset.sum_union hdisj, hneg, hpos]
  ring



/-- Reindex a `ℤ`-`Icc` starting at `1` as a `ℕ`-`range`. -/
lemma sum_Icc_int_cast (g : ℤ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.Icc (1:ℤ) (n:ℤ), g j = ∑ j ∈ Finset.range n, g ((j:ℤ)+1) := by
  refine Finset.sum_bij' (fun (j:ℤ) _ => (j-1).toNat) (fun (j:ℕ) _ => (j:ℤ)+1)
    ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_range]
    simp only [Finset.mem_Icc] at ha
    have h : ((a-1).toNat : ℤ) = a - 1 := Int.toNat_of_nonneg (by omega)
    omega
  · intro a ha
    simp only [Finset.mem_Icc]
    simp only [Finset.mem_range] at ha
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    have h : ((a-1).toNat : ℤ) = a - 1 := Int.toNat_of_nonneg (by omega)
    omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    have h : ((a:ℤ)+1-1).toNat = a := by
      rw [show (a:ℤ)+1-1 = (a:ℤ) by ring, Int.toNat_natCast]
    rw [h]
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    have h : ((a-1).toNat : ℤ) = a - 1 := Int.toNat_of_nonneg (by omega)
    congr 1
    omega

/-- The `b = 0` sum equals twice a `ℕ`-range sum minus the `0`-term. -/
lemma ASum_zero_eq_range (f : ℝ → ℝ) (d x : ℕ) (hd : 1 ≤ d) (hx : 1 ≤ x)
    (hsupp : ∀ u, (x : ℝ) ≤ u → f u = 0) :
    ASum f d 0
      = 2 * (∑ j ∈ Finset.range (Nat.sqrt x / sqrtK d + 1),
          f (((((sqrtK d * j : ℕ)) : ℝ)) ^ 2)) - f 0 := by
  set m : ℕ := sqrtK d with hmdef
  have hm1 : 1 ≤ m := sqrtK_pos d
  set K : ℕ := x / m with hKdef
  set N : ℕ := Nat.sqrt x / m + 1 with hNdef
  have hNpos : 1 ≤ N := by rw [hNdef]; exact Nat.le_add_left 1 _
  have hmN : Nat.sqrt x < m * N := by
    rw [hNdef]
    have h1 := Nat.div_add_mod (Nat.sqrt x) m
    have h2 := Nat.mod_lt (Nat.sqrt x) hm1
    have h3 : m * (Nat.sqrt x / m + 1) = m * (Nat.sqrt x / m) + m := by ring
    omega
  have hKN : N - 1 ≤ K := by
    rw [hKdef, hNdef, Nat.add_sub_cancel]
    exact Nat.div_le_div_right (Nat.sqrt_le_self x)
  set n : ℕ := N - 1 with hndef
  have hNn : N = n + 1 := by rw [hndef]; omega
  set ψ : ℤ → ℝ := fun j => f (((((m : ℤ) * j : ℤ) : ℝ)) ^ 2) with hψdef
  have heven : ∀ j, ψ (-j) = ψ j := by
    intro j
    simp only [hψdef]
    congr 1
    push_cast
    ring
  have hvan : ∀ j : ℤ, N ≤ j.natAbs → ψ j = 0 := by
    intro j hj
    simp only [hψdef]
    apply hsupp
    have h1 : ((m : ℤ) * j).natAbs = m * j.natAbs := by rw [Int.natAbs_mul, Int.natAbs_natCast]
    have h2 : Nat.sqrt x < ((m : ℤ) * j).natAbs := by
      rw [h1]; exact lt_of_lt_of_le hmN (Nat.mul_le_mul_left m hj)
    have h2r : (((Nat.sqrt x : ℕ) : ℝ) + 1) ≤ ((((m : ℤ) * j).natAbs : ℕ) : ℝ) := by
      have : Nat.sqrt x + 1 ≤ ((m : ℤ) * j).natAbs := by omega
      exact_mod_cast this
    have hx1 : (x : ℝ) < (((Nat.sqrt x : ℕ) : ℝ) + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt' x
      push_cast
      exact_mod_cast this
    have heq : ((((m : ℤ) * j).natAbs : ℕ) : ℝ) ^ 2 = ((((m : ℤ) * j : ℤ) : ℝ)) ^ 2 := by
      have h0 := Int.natAbs_sq ((m : ℤ) * j)
      have h1 : (((((m : ℤ) * j)).natAbs : ℤ) : ℝ) ^ 2 = ((((m : ℤ) * j : ℤ) : ℝ)) ^ 2 := by
        exact_mod_cast h0
      simpa using h1
    have hnn : (0 : ℝ) ≤ (((Nat.sqrt x : ℕ) : ℝ) + 1) := by positivity
    have hsq : (((Nat.sqrt x : ℕ) : ℝ) + 1) ^ 2 ≤ ((((m : ℤ) * j).natAbs : ℕ) : ℝ) ^ 2 := by
      nlinarith [h2r, hnn, (by positivity : (0:ℝ) ≤ ((((m : ℤ) * j).natAbs : ℕ) : ℝ))]
    rw [heq] at hsq
    linarith [hx1, hsq]
  have hzero : ∀ j ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), j ∉ Finset.Icc (-(n:ℤ)) (n:ℤ) → ψ j = 0 := by
    intro j hj hj'
    apply hvan
    rw [hNn]
    simp only [Finset.mem_Icc, not_and_or, not_le] at hj'
    have habs : (n : ℤ) + 1 ≤ |j| := by
      rcases hj' with h | h
      · have hj0 : j < 0 := by
          have : (0:ℤ) ≤ (n:ℤ) := by positivity
          omega
        rw [abs_of_neg hj0]; omega
      · have hj0 : (0:ℤ) < j := by
          have : (0:ℤ) ≤ (n:ℤ) := by positivity
          omega
        rw [abs_of_pos hj0]; omega
    rw [Int.abs_eq_natAbs] at habs
    have : n + 1 ≤ j.natAbs := by exact_mod_cast habs
    omega
  have hsub : Finset.Icc (-(n:ℤ)) (n:ℤ) ⊆ Finset.Icc (-(K:ℤ)) (K:ℤ) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    have : n ≤ K := by omega
    omega
  rw [ASum_zero_eq_lattice f d x hd hx hsupp]
  rw [← Finset.sum_subset hsub hzero]
  rw [sum_Icc_neg_even ψ heven n]
  rw [sum_Icc_int_cast ψ n]
  have h0 : ψ 0 = f 0 := by simp only [hψdef]; norm_num
  have hpt : ∀ j : ℕ, ψ ((j:ℤ)+1) = f (((((m * (j+1) : ℕ)) : ℝ)) ^ 2) := by
    intro j
    simp only [hψdef]
    push_cast
    rfl
  rw [hNn, Finset.sum_range_succ', Finset.sum_congr rfl (fun j _ => hpt j), h0]
  rw [show f (((m * 0 : ℕ) : ℝ) ^ 2) = f 0 by norm_num]
  ring


/-- If `f` vanishes above `x` then `I0 f 0 = ∫_0^c f (t²)` for any `c ≥ √x`. -/
lemma I0_eq_interval (f : ℝ → ℝ) (X c : ℝ) (hX : 0 ≤ X) (hxc : Real.sqrt X ≤ c)
    (hfsup : ∀ t, X ≤ t → f t = 0) :
    I0 f 0 = ∫ t in (0:ℝ)..c, f (t^2) := by
  have hc0 : (0:ℝ) ≤ c := le_trans (Real.sqrt_nonneg X) hxc
  have hsub : Set.Icc (0:ℝ) c ⊆ Set.Ici (0:ℝ) := fun t ht => ht.1
  have hdiff : ∀ t ∈ Set.Ici (0:ℝ) \ Set.Icc (0:ℝ) c, f (t^2) = 0 := by
    intro t ht
    rw [Set.mem_sdiff, Set.mem_Ici, Set.mem_Icc] at ht
    have ht' : c < t := by
      by_contra hle
      exact ht.2 ⟨ht.1, le_of_not_gt hle⟩
    apply hfsup
    have h2 : X ≤ c^2 := by
      nlinarith [hxc, Real.sq_sqrt hX, Real.sqrt_nonneg X, sq_nonneg c]
    nlinarith [h2, ht', sq_pos_of_pos (sub_pos.mpr ht')]
  calc I0 f 0 = ∫ t in Set.Ici (0:ℝ), f (t^2) := by simp [I0]
    _ = ∫ t in Set.Icc (0:ℝ) c, f (t^2) :=
        MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici hsub hdiff
    _ = ∫ t in Set.Ioc (0:ℝ) c, f (t^2) := MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ t in (0:ℝ)..c, f (t^2) := (intervalIntegral.integral_of_le hc0).symm


/-- **The `b = 0` contribution.**  For `1 ≤ y ≤ x`, `0 < A`, a `C¹` function `f : ℝ → ℝ` with
`0 ≤ f ≤ 1`, `f u = 0` for `u ≥ x` and `|f'| ≤ A/y` on `[0,x]`, the `b = 0` part of
`A_d(f) - M_d(f)` is `O(A x / y + 1)` uniformly in `d`. -/
theorem ASum_zero_sub_MdF_zero_le (f : ℝ → ℝ) (d x : ℕ) (A y : ℝ)
    (hd : 1 ≤ d) (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x) (hA : 0 < A)
    (hf : ContDiff ℝ 1 f)
    (hf01 : ∀ u, 0 ≤ f u ∧ f u ≤ 1)
    (hfsup : ∀ u, (x : ℝ) ≤ u → f u = 0)
    (hfd : ∀ u ∈ Set.Icc 0 (x : ℝ), |deriv f u| ≤ A / y) :
    |ASum f d 0 - (2 / (d : ℝ)) * (rho 0 d : ℝ) * I0 f 0| ≤ (8 * A + 5) * (x : ℝ) / y := by
  set m : ℕ := sqrtK d with hmdef
  have hm1 : 1 ≤ m := sqrtK_pos d
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
  have hxR : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by positivity
  have hms : m * rho 0 d = d := sqrtK_mul_rho_zero_eq d hd
  have hmsR : (m:ℝ) * (rho 0 d : ℝ) = (d:ℝ) := by exact_mod_cast hms
  have hApos : 0 < A / y := div_pos hA (by linarith)
  have hxy : (1:ℝ) ≤ (x:ℝ) / y := by rw [le_div_iff₀ (by linarith : (0:ℝ) < y)]; linarith
  -- the derivative vanishes above `x`
  have hderiv_zero : ∀ u : ℝ, (x : ℝ) < u → deriv f u = 0 := by
    intro u hu
    have hev : f =ᶠ[nhds u] (fun _ : ℝ => (0:ℝ)) := by
      filter_upwards [eventually_gt_nhds hu] with v hv
      exact hfsup v (le_of_lt hv)
    simpa using hev.deriv_eq
  have hfd' : ∀ u : ℝ, 0 ≤ u → |deriv f u| ≤ A / y := by
    intro u hu
    rcases le_or_gt u (x:ℝ) with h | h
    · exact hfd u ⟨hu, h⟩
    · rw [hderiv_zero u h, abs_zero]; exact le_of_lt hApos
  set N : ℕ := Nat.sqrt x / m + 1 with hNdef
  have hmN : Nat.sqrt x < m * N := by
    rw [hNdef]
    have h1 := Nat.div_add_mod (Nat.sqrt x) m
    have h2 := Nat.mod_lt (Nat.sqrt x) hm1
    have h3 : m * (Nat.sqrt x / m + 1) = m * (Nat.sqrt x / m) + m := by ring
    omega
  have hsqrt_le : Real.sqrt (x:ℝ) ≤ (m:ℝ) * (N:ℝ) := by
    have h1 : (Nat.sqrt x : ℝ) < (m:ℝ) * (N:ℝ) := by
      have : ((m * N : ℕ) : ℝ) = (m:ℝ) * (N:ℝ) := by push_cast; ring
      rw [← this]; exact_mod_cast hmN
    have h2 : Real.sqrt (x:ℝ) < (Nat.sqrt x : ℝ) + 1 := by
      rw [Real.sqrt_lt' (by positivity : (0:ℝ) < (Nat.sqrt x : ℝ) + 1)]
      have := Nat.lt_succ_sqrt' x
      push_cast
      exact_mod_cast this
    have h3 : (Nat.sqrt x : ℝ) + 1 ≤ (m:ℝ) * (N:ℝ) := by
      have : ((m * N : ℕ) : ℝ) ≥ ((Nat.sqrt x + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : Nat.sqrt x + 1 ≤ m * N)
      push_cast at this
      linarith
    linarith
  set G : ℝ → ℝ := fun t => f (((m:ℝ)*t)^2) with hGdef
  have hGderiv : ∀ t : ℝ, HasDerivAt G ((2*(m:ℝ)^2*t) * deriv f (((m:ℝ)*t)^2)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (m:ℝ)*s) (m:ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul ((m:ℝ))
    have h2 : HasDerivAt (fun s : ℝ => ((m:ℝ)*s)^2) (2*(m:ℝ)^2*t) t := by
      have h2' := h1.pow 2
      refine h2'.congr_deriv ?_
      ring
    have h3 : HasDerivAt f (deriv f (((m:ℝ)*t)^2)) (((m:ℝ)*t)^2) :=
      ((hf.differentiable_one).differentiableAt).hasDerivAt
    have h4 := h3.comp t h2
    refine h4.congr_deriv ?_
    ring
  have hsubst : ∫ t in (0:ℝ)..(N:ℝ), G t = (1/(m:ℝ)) * I0 f 0 := by
    have hI := I0_eq_interval f (x:ℝ) ((m:ℝ)*(N:ℝ)) hx0 hsqrt_le hfsup
    have h1 : ∫ t in (0:ℝ)..(N:ℝ), G t
        = (m:ℝ)⁻¹ * ∫ u in (0:ℝ)..((m:ℝ)*(N:ℝ)), f (u^2) := by
      have := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := (N:ℝ))
        (c := (m:ℝ)) (f := fun u : ℝ => f (u^2)) (ne_of_gt hmpos)
      rw [hGdef]
      simpa only [mul_zero, smul_eq_mul] using this
    rw [← hI] at h1
    rw [h1]; ring
  have hsum_eq : (∑ j ∈ Finset.range N, f (((((m * j : ℕ)) : ℝ)) ^ 2))
      = ∑ j ∈ Finset.range N, G (j:ℝ) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [hGdef]
    push_cast
    rfl
  have hcoef : (2 / (d : ℝ)) * (rho 0 d : ℝ) = 2 / (m : ℝ) := by
    rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity : (d:ℝ) ≠ 0) (ne_of_gt hmpos)]
    rw [show (2:ℝ) * (rho 0 d : ℝ) * (m:ℝ) = 2 * ((m:ℝ) * (rho 0 d : ℝ)) by ring, hmsR]
  have hR : ASum f d 0 - (2 / (d : ℝ)) * (rho 0 d : ℝ) * I0 f 0
      = 2 * ((∑ j ∈ Finset.range N, G (j:ℝ)) - (1/(m:ℝ)) * I0 f 0) - f 0 := by
    rw [ASum_zero_eq_range f d x hd hx hfsup, hsum_eq, hcoef]
    ring
  rw [hR]
  set S : ℝ := (∑ j ∈ Finset.range N, G (j:ℝ)) - (1/(m:ℝ)) * I0 f 0 with hSdef
  have hstep : |2 * S - f 0| ≤ 2 * |S| + |f 0| := by
    calc |2 * S - f 0| = |2 * S + -(f 0)| := by ring_nf
      _ ≤ |2 * S| + |-(f 0)| := abs_add_le _ _
      _ = 2 * |S| + |f 0| := by rw [abs_mul, abs_neg]; norm_num
  have hf0 : |f 0| ≤ 1 := by
    rw [abs_of_nonneg (hf01 0).1]; exact (hf01 0).2
  rcases le_or_gt (m:ℝ) (Real.sqrt (x:ℝ)) with hcase | hcase
  · -- case A: `m ≤ √x`
    have hMnn : (0:ℝ) ≤ 2*(m:ℝ)*Real.sqrt (x:ℝ)*(A/y) := by positivity
    have hbound : ∀ t ∈ Set.Icc (0:ℝ) ((N:ℝ)*1),
        ‖((((2*(m:ℝ)^2*t) * deriv f (((m:ℝ)*t)^2) : ℝ)) : ℂ)‖
          ≤ 2*(m:ℝ)*Real.sqrt (x:ℝ)*(A/y) := by
      intro t ht
      rw [Complex.norm_real, Real.norm_eq_abs]
      have ht0 : (0:ℝ) ≤ t := ht.1
      have hsplit : |(2*(m:ℝ)^2*t) * deriv f (((m:ℝ)*t)^2)|
          = (2*(m:ℝ)^2*t) * |deriv f (((m:ℝ)*t)^2)| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
      rw [hsplit]
      by_cases hd0 : deriv f (((m:ℝ)*t)^2) = 0
      · rw [hd0, abs_zero, mul_zero]; positivity
      · have hle : ((m:ℝ)*t)^2 ≤ (x:ℝ) := by
          by_contra hlt
          rw [hderiv_zero _ (lt_of_not_ge hlt)] at hd0
          exact hd0 rfl
        have hmt0 : (0:ℝ) ≤ (m:ℝ)*t := by positivity
        have hmt : (m:ℝ)*t ≤ Real.sqrt (x:ℝ) := by
          rw [← Real.sqrt_sq hmt0]; exact Real.sqrt_le_sqrt hle
        have hb : |deriv f (((m:ℝ)*t)^2)| ≤ A/y := hfd' _ (by positivity)
        calc (2*(m:ℝ)^2*t) * |deriv f (((m:ℝ)*t)^2)|
            = (2*(m:ℝ)*((m:ℝ)*t)) * |deriv f (((m:ℝ)*t)^2)| := by ring
          _ ≤ (2*(m:ℝ)*Real.sqrt (x:ℝ)) * |deriv f (((m:ℝ)*t)^2)| := by
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
              nlinarith [hmpos, hmt, ht0]
          _ ≤ (2*(m:ℝ)*Real.sqrt (x:ℝ)) * (A/y) := by
              apply mul_le_mul_of_nonneg_left hb (by positivity)
    have hmesh := Commons.Analysis.Integral.mesh_riemann_sum_sub_integral_le (n := N)
      (F := fun t : ℝ => ((G t : ℝ) : ℂ))
      (F' := fun t : ℝ => (((2*(m:ℝ)^2*t) * deriv f (((m:ℝ)*t)^2) : ℝ) : ℂ))
      (h := 1) (M := 2*(m:ℝ)*Real.sqrt (x:ℝ)*(A/y)) (by norm_num) hMnn
      (fun t ht => by simpa using (hGderiv t).ofReal_comp) hbound
    simp only [Complex.ofReal_one, one_mul, mul_one] at hmesh
    rw [intervalIntegral.integral_ofReal] at hmesh
    have hcast : ‖(∑ j ∈ Finset.range N, ((G (j:ℝ) : ℝ) : ℂ))
        - ((∫ t in (0:ℝ)..(N:ℝ), G t : ℝ) : ℂ)‖
        = |(∑ j ∈ Finset.range N, G (j:ℝ)) - ∫ t in (0:ℝ)..(N:ℝ), G t| := by
      have h1 : ((∑ j ∈ Finset.range N, ((G (j:ℝ) : ℝ) : ℂ))
          - ((∫ t in (0:ℝ)..(N:ℝ), G t : ℝ) : ℂ))
          = (((∑ j ∈ Finset.range N, G (j:ℝ)) - ∫ t in (0:ℝ)..(N:ℝ), G t : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [h1, Complex.norm_real, Real.norm_eq_abs]
    rw [hcast] at hmesh
    have hNM : (N:ℝ) * (2*(m:ℝ)*Real.sqrt (x:ℝ)*(A/y)) ≤ 4*(x:ℝ)*A/y := by
      have hNm : (N:ℝ) * (m:ℝ) ≤ Real.sqrt (x:ℝ) + (m:ℝ) := by
        have hN' : (N:ℝ) = ((Nat.sqrt x / m : ℕ) : ℝ) + 1 := by rw [hNdef]; push_cast; ring
        rw [hN']
        have h1 : ((Nat.sqrt x / m : ℕ) : ℝ) * (m:ℝ) ≤ (Nat.sqrt x : ℝ) := by
          have := Nat.div_mul_le_self (Nat.sqrt x) m
          exact_mod_cast this
        have h2 : (Nat.sqrt x : ℝ) ≤ Real.sqrt (x:ℝ) := by
          rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (Nat.sqrt x : ℝ))]
          exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le' x)
        linarith
      calc (N:ℝ) * (2*(m:ℝ)*Real.sqrt (x:ℝ)*(A/y))
          = 2 * ((N:ℝ)*(m:ℝ)) * Real.sqrt (x:ℝ) * (A/y) := by ring
        _ ≤ 2 * (Real.sqrt (x:ℝ) + (m:ℝ)) * Real.sqrt (x:ℝ) * (A/y) := by
            nlinarith [hNm, Real.sqrt_nonneg (x:ℝ), hApos]
        _ ≤ 4 * (x:ℝ) * A / y := by
            have hsx : Real.sqrt (x:ℝ) * Real.sqrt (x:ℝ) = (x:ℝ) := by
              rw [← pow_two, Real.sq_sqrt hx0]
            have hle : Real.sqrt (x:ℝ) + (m:ℝ) ≤ 2 * Real.sqrt (x:ℝ) := by linarith [hcase]
            have hh := mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg (x:ℝ))
            have h2 : (2 * Real.sqrt (x:ℝ)) * Real.sqrt (x:ℝ) = 2 * (x:ℝ) := by
              rw [mul_assoc, hsx]
            rw [h2] at hh
            have hmid : 2 * (Real.sqrt (x:ℝ) + (m:ℝ)) * Real.sqrt (x:ℝ) ≤ 4 * (x:ℝ) := by linarith [hh]
            have hgoal : 2 * (Real.sqrt (x:ℝ) + (m:ℝ)) * Real.sqrt (x:ℝ) * (A/y) ≤ 4 * (x:ℝ) * (A/y) :=
              mul_le_mul_of_nonneg_right hmid (le_of_lt hApos)
            have heq : 4 * (x:ℝ) * (A / y) = 4 * (x:ℝ) * A / y := by ring
            linarith [hgoal, heq]
    have hfin : |S| ≤ 4*(x:ℝ)*A/y := by
      rw [hSdef, ← hsubst]
      exact le_trans hmesh hNM
    have h2 : |2 * S - f 0| ≤ (8 * A + 5) * (x : ℝ) / y := by
      have h1 : 2 * |S| + |f 0| ≤ 2 * (4*(x:ℝ)*A/y) + 1 := by
        have := mul_le_mul_of_nonneg_left hfin (by norm_num : (0:ℝ) ≤ 2)
        linarith
      have h2' : 2 * (4*(x:ℝ)*A/y) + 1 ≤ (8 * A + 5) * (x : ℝ) / y := by
        have h3 : (1:ℝ) ≤ 5 * ((x:ℝ)/y) := by nlinarith [hxy]
        have heq : (8 * A + 5) * (x : ℝ) / y - 2 * (4*(x:ℝ)*A/y) = 5 * ((x:ℝ)/y) := by ring
        linarith [h3, heq]
      linarith [hstep, h1, h2']
    simpa only [hSdef] using h2
  · -- case B: `m > √x`
    have hN1 : N = 1 := by
      rw [hNdef]
      have h1 : Nat.sqrt x < m := by
        have h2 : (Nat.sqrt x : ℝ) ≤ Real.sqrt (x:ℝ) := by
          rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (Nat.sqrt x : ℝ))]
          exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le' x)
        exact_mod_cast (by linarith : (Nat.sqrt x : ℝ) < (m:ℝ))
      rw [Nat.div_eq_of_lt h1]
    have hG0 : G 0 = f 0 := by simp only [hGdef]; norm_num
    have hsum1 : (∑ j ∈ Finset.range N, G (j:ℝ)) = f 0 := by
      rw [hN1]; simp [hG0]
    have hint : |∫ t in (0:ℝ)..(N:ℝ), G t| ≤ 1 := by
      have hb : ∀ x ∈ Set.uIoc (0:ℝ) (N:ℝ), ‖G x‖ ≤ 1 := by
        intro x _
        rw [Real.norm_eq_abs, abs_of_nonneg (hf01 _).1]
        exact (hf01 _).2
      have := intervalIntegral.norm_integral_le_of_norm_le_const hb (C := 1)
      rw [Real.norm_eq_abs] at this
      simpa [hN1] using this
    have hfin : |S| ≤ 2 := by
      rw [hSdef, ← hsubst, hsum1]
      calc |f 0 - ∫ t in (0:ℝ)..(N:ℝ), G t| ≤ |f 0| + |∫ t in (0:ℝ)..(N:ℝ), G t| := by
            rw [sub_eq_add_neg]
            calc |f 0 + -(∫ t in (0:ℝ)..(N:ℝ), G t)| ≤ |f 0| + |-(∫ t in (0:ℝ)..(N:ℝ), G t)| := abs_add_le _ _
              _ = |f 0| + |∫ t in (0:ℝ)..(N:ℝ), G t| := by rw [abs_neg]
        _ ≤ 2 := by linarith
    have h2 : |2 * S - f 0| ≤ (8 * A + 5) * (x : ℝ) / y := by
      have h1 : 2 * |S| + |f 0| ≤ 2 * 2 + 1 := by
        have := mul_le_mul_of_nonneg_left hfin (by norm_num : (0:ℝ) ≤ 2)
        linarith
      have h2' : (2 * 2 + 1 : ℝ) ≤ (8 * A + 5) * (x : ℝ) / y := by
        have h3 : (1:ℝ) ≤ (x:ℝ)/y := hxy
        have h5 : (5:ℝ) ≤ (8 * A + 5) * ((x:ℝ)/y) := by
          nlinarith [hA, h3]
        rw [mul_div_assoc'] at h5
        linarith [h5]
      linarith [hstep, h1, h2']
    simpa only [hSdef] using h2


end Submission

namespace Submission

/- ### Main chain of the §3 estimate (3.13): norm bound, Fourier decay, substitution.
   Names in this block are provisional and merged from the development scratch. -/


open Finset MeasureTheory
open Submission

/-- `(Z l)^2 ≤ 4` times the indicator of `l` being a square. -/
lemma Z_sq_le_four (l : ℕ) : (Z l : ℝ)^2 ≤ 4 * (if Nat.sqrt l ^ 2 = l then (1:ℝ) else 0) := by
  rcases eq_or_ne l 0 with rfl | hl
  · rw [Z_zero]; norm_num
  · rw [show Z l = if Nat.sqrt l ^ 2 = l then 2 else 0 from by rw [Z, if_neg hl]]
    by_cases h : Nat.sqrt l ^ 2 = l <;> simp only [h, if_true, if_false, mul_one, mul_zero] <;> norm_num

/-- The number of squares in `[1, L]` is `⌊√L⌋`. -/
lemma card_sq_Icc (L : ℕ) :
    ((Finset.Icc 1 L).filter (fun l => Nat.sqrt l ^ 2 = l)).card = Nat.sqrt L := by
  have hcard : (Finset.Icc 1 (Nat.sqrt L)).card = Nat.sqrt L := by
    rw [Nat.card_Icc]; omega
  rw [← hcard]
  refine Finset.card_bij (fun l _ => Nat.sqrt l) ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_Icc] at hl
    simp only [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · rw [Nat.le_sqrt']; simpa using hl.1.1
    · rw [Nat.le_sqrt']; rw [hl.2]; exact hl.1.2
  · intro l1 hl1 l2 hl2 h
    simp only [Finset.mem_filter, Finset.mem_Icc] at hl1 hl2
    rw [← hl1.2, ← hl2.2, h]
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    refine ⟨b ^ 2, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by nlinarith [hb.1], ?_⟩, ?_⟩
      · exact Nat.le_sqrt'.mp hb.2
      · rw [Nat.sqrt_eq']
    · exact Nat.sqrt_eq' b

/-- Telescoping bound: `Σ_{k = n}^{K} 1/k² ≤ 2/n` for `n ≥ 2`. -/
lemma sum_Icc_inv_sq_le_ge2 (n : ℕ) (hn : 2 ≤ n) (K : ℕ) :
    (∑ k ∈ Finset.Icc n K, (1:ℝ)/(k:ℝ)^2) ≤ 2/(n:ℝ) := by
  rcases Nat.lt_or_ge K n with h | h
  · rw [Finset.Icc_eq_empty (by omega : ¬ n ≤ K)]; simp
    positivity
  have hterm : ∀ k ∈ Finset.Icc n K, (1:ℝ)/(k:ℝ)^2 ≤ (1:ℝ)/((k:ℝ)-1) - 1/(k:ℝ) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
    have h1 : (0:ℝ) < (k:ℝ) * ((k:ℝ)-1) := by nlinarith
    have h2 : (k:ℝ) * ((k:ℝ)-1) ≤ (k:ℝ)^2 := by nlinarith
    have h3 : (1:ℝ)/((k:ℝ)^2) ≤ 1/((k:ℝ)*((k:ℝ)-1)) :=
      one_div_le_one_div_of_le h1 h2
    have h4 : (1:ℝ)/((k:ℝ)-1) - 1/(k:ℝ) = 1/((k:ℝ)*((k:ℝ)-1)) := by
      rw [div_sub_div _ _ (by nlinarith) (by nlinarith)]
      ring_nf
    rw [h4]
    exact h3
  have htel : (∑ k ∈ Finset.Icc n K, ((1:ℝ)/((k:ℝ)-1) - 1/(k:ℝ)))
      = 1/((n:ℝ)-1) - 1/(K:ℝ) := by
    have hsub := Finset.sum_Icc_sub (m := n) (n := K) h (fun i : ℕ => -(1:ℝ)/((i:ℝ)-1))
    have h1 : (∑ i ∈ Finset.Icc n K, ((1:ℝ)/((i:ℝ)-1) - 1/(i:ℝ)))
        = ∑ i ∈ Finset.Icc n K, (-(1:ℝ)/((((i+1:ℕ)):ℝ)-1) - -(1:ℝ)/((i:ℝ)-1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hii : (((i+1:ℕ)):ℝ) - 1 = (i:ℝ) := by push_cast; ring
      rw [hii]; ring
    rw [h1, hsub]
    rw [show (((K+1:ℕ)):ℝ) - 1 = (K:ℝ) by push_cast; ring]
    ring
  calc (∑ k ∈ Finset.Icc n K, (1:ℝ)/(k:ℝ)^2)
      ≤ ∑ k ∈ Finset.Icc n K, ((1:ℝ)/((k:ℝ)-1) - 1/(k:ℝ)) := Finset.sum_le_sum hterm
    _ = 1/((n:ℝ)-1) - 1/(K:ℝ) := htel
    _ ≤ 2/(n:ℝ) := by
        have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
        have hKn : (0:ℝ) ≤ 1/(K:ℝ) := by positivity
        have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        have h1 : 1/((n:ℝ)-1) ≤ 2/(n:ℝ) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          linarith
        linarith

/-- Telescoping bound: `Σ_{k = n}^{K} 1/k² ≤ 2/n` for `n ≥ 1`. -/
lemma sum_Icc_inv_sq_le (n : ℕ) (hn : 1 ≤ n) (K : ℕ) :
    (∑ k ∈ Finset.Icc n K, (1:ℝ)/(k:ℝ)^2) ≤ 2/(n:ℝ) := by
  rcases Nat.eq_or_lt_of_le hn with h1 | h2
  · subst h1
    rcases Nat.lt_or_ge K 1 with h | h
    · rw [Finset.Icc_eq_empty (by omega : ¬ 1 ≤ K)]; simp
    have hins : Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    have hb := sum_Icc_inv_sq_le_ge2 2 (by norm_num) K
    norm_num at hb ⊢
    linarith
  · exact sum_Icc_inv_sq_le_ge2 n h2 K

/-- `Σ_{k ≤ K, u < k} 1/k² ≤ 4/(u+1)`. -/
lemma sum_Icc_inv_sq_filter_le (u : ℝ) (hu : 0 < u) (K : ℕ) :
    (∑ k ∈ (Finset.Icc 1 K).filter (fun k : ℕ => u < (k:ℝ)), (1:ℝ)/(k:ℝ)^2) ≤ 4/(u+1) := by
  rcases lt_or_ge u 1 with h1 | h1
  · have hsub : (Finset.Icc 1 K).filter (fun k : ℕ => u < (k:ℝ)) ⊆ Finset.Icc 1 K :=
      Finset.filter_subset _ _
    have h2 : (∑ k ∈ (Finset.Icc 1 K).filter (fun k : ℕ => u < (k:ℝ)), (1:ℝ)/(k:ℝ)^2)
        ≤ ∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(k:ℝ)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    have h3 : (∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(k:ℝ)^2) ≤ 2 := by
      have h := sum_Icc_inv_sq_le 1 (le_refl 1) K
      simp only [Nat.cast_one, div_one] at h
      exact h
    have h4 : (2:ℝ) ≤ 4/(u+1) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    linarith
  · set j : ℕ := ⌊u⌋₊ with hjdef
    have hj1 : 1 ≤ j := (Nat.one_le_floor_iff u).mpr h1
    have hsub : (Finset.Icc 1 K).filter (fun k : ℕ => u < (k:ℝ)) ⊆ Finset.Icc (j+1) K := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk
      simp only [Finset.mem_Icc]
      refine ⟨?_, hk.1.2⟩
      have hk' : u < (k:ℝ) := hk.2
      have h4 : (j:ℝ) < (k:ℝ) := lt_of_le_of_lt (Nat.floor_le (le_of_lt hu)) hk'
      have h5 : j < k := by exact_mod_cast h4
      omega
    have h2 : (∑ k ∈ (Finset.Icc 1 K).filter (fun k : ℕ => u < (k:ℝ)), (1:ℝ)/(k:ℝ)^2)
        ≤ ∑ k ∈ Finset.Icc (j+1) K, (1:ℝ)/(k:ℝ)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    have h3 : (∑ k ∈ Finset.Icc (j+1) K, (1:ℝ)/(k:ℝ)^2) ≤ 2/((j:ℝ)+1) := by
      have h := sum_Icc_inv_sq_le (j+1) (by omega) K
      rw [Nat.cast_add, Nat.cast_one] at h
      exact h
    have h4 : (2:ℝ)/((j:ℝ)+1) ≤ 4/(u+1) := by
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      have hju : u < (j:ℝ) + 1 := Nat.lt_floor_add_one u
      nlinarith [hju, hu, hj1]
    linarith


/-- **The `ℓ²` bound** for the weight `ξ(k,l) = k⁻¹ Z(l) f (x u²/k² + l²)`: the square sum over
`k ≤ K`, `l ≤ √x` is `≪ x^{1/4}/(u+1)`. -/
lemma l2_weight_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (x K : ℕ) (f : ℝ → ℝ) (u : ℝ), 1 ≤ x → 0 < u →
      (∀ v : ℝ, v ∉ Set.Icc 0 (x : ℝ) → f v = 0) →
      (∀ v : ℝ, 0 ≤ f v) → (∀ v : ℝ, f v ≤ 1) →
      (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
        (1 / (k : ℝ) ^ 2) * (Z l : ℝ) ^ 2
          * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2)
        ≤ C * (x : ℝ) ^ ((1 : ℝ) / 4) / (u + 1) := by
  refine ⟨16, by norm_num, ?_⟩
  intro x K f u hx hu hfsup hf0 hf1
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by positivity
  have hxq : (0:ℝ) < (x:ℝ) ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos (by positivity) _
  have hinner : ∀ k : ℕ, (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
      (Z l : ℝ) ^ 2 * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2)
        ≤ 4 * (x : ℝ) ^ ((1 : ℝ) / 4) := by
    intro k
    have h1 : (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
        (Z l : ℝ) ^ 2 * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2)
        ≤ ∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
            4 * (if Nat.sqrt l ^ 2 = l then (1:ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro l hl
      have hZ := Z_sq_le_four l
      have hf2 : f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2 ≤ 1 := by
        have h1 := hf0 ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2)
        have h2 := hf1 ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2)
        nlinarith
      have hind : (0:ℝ) ≤ (if Nat.sqrt l ^ 2 = l then (1:ℝ) else 0) := by
        split <;> norm_num
      have hZnn : (0:ℝ) ≤ (Z l : ℝ)^2 := by positivity
      nlinarith [hZ, hf2, hind, hZnn]
    have h2 : (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
        4 * (if Nat.sqrt l ^ 2 = l then (1:ℝ) else 0))
        = 4 * ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) := by
      rw [← Finset.mul_sum, Finset.sum_boole, card_sq_Icc]
    have h3 : ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1:ℝ)/4) := by
      have h1 : ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ≤ Real.sqrt (Nat.sqrt x : ℝ) :=
        natSqrt_cast_le_sqrt (Nat.sqrt x)
      have h2 : Real.sqrt (Nat.sqrt x : ℝ) ≤ Real.sqrt (Real.sqrt (x:ℝ)) :=
        Real.sqrt_le_sqrt (natSqrt_cast_le_sqrt x)
      have h3 : Real.sqrt (Real.sqrt (x:ℝ)) = (x:ℝ) ^ ((1:ℝ)/4) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0]
        norm_num
      linarith [h1, h2, h3.le, h3.ge]
    rw [h2] at h1
    linarith [h1, mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 4)]
  have hstep : (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
        (1 / (k : ℝ) ^ 2) * (Z l : ℝ) ^ 2
          * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2)
      = ∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ)^2) * (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
          (Z l : ℝ) ^ 2 * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hstep]
  have hkey : ∀ k ∈ Finset.Icc 1 K,
      (1/(k:ℝ)^2) * (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
          (Z l : ℝ) ^ 2 * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2)
        ≤ (1/(k:ℝ)^2) * (if u < (k:ℝ) then 4 * (x:ℝ)^((1:ℝ)/4) else 0) := by
    intro k hk
    by_cases h : u < (k:ℝ)
    · rw [if_pos h]
      exact mul_le_mul_of_nonneg_left (hinner k) (by positivity)
    · rw [if_neg h]
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have huk : (k:ℝ) ≤ u := le_of_not_gt h
      have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
      have hzero : (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
          (Z l : ℝ) ^ 2 * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro l hl
        have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
        have harg : (x:ℝ) < (x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2 := by
          have hk2 : (0:ℝ) < (k:ℝ)^2 := by positivity
          have h1 : (x:ℝ) ≤ (x:ℝ) * u^2/(k:ℝ)^2 := by
            rw [le_div_iff₀ hk2]
            have hkk : (k:ℝ)^2 ≤ u^2 := by nlinarith [huk, hkpos]
            nlinarith [hx0, hkk]
          have h2 : (1:ℝ) ≤ (l:ℝ)^2 := by
            have : (1:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl1
            nlinarith
          linarith
        have hnotmem : ¬ ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2 ∈ Set.Icc 0 (x:ℝ)) :=
          fun hmem => absurd (Set.mem_Icc.mp hmem).2 (not_le.mpr harg)
        rw [show f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2 = 0 by
          rw [hfsup _ hnotmem]; norm_num]
        ring
      rw [hzero, mul_zero]
  calc (∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ)^2) * (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
          (Z l : ℝ) ^ 2 * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2))
      ≤ ∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ)^2) * (if u < (k:ℝ) then 4 * (x:ℝ)^((1:ℝ)/4) else 0) :=
        Finset.sum_le_sum hkey
    _ = 4 * (x:ℝ)^((1:ℝ)/4) * ∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ)^2) * (if u < (k:ℝ) then 1 else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        by_cases h : u < (k:ℝ) <;> simp [h]; ring
    _ ≤ 4 * (x:ℝ)^((1:ℝ)/4) * (4/(u+1)) := by
        have h := sum_Icc_inv_sq_filter_le u hu K
        rw [Finset.sum_filter] at h
        have hEq : (∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ)^2) * (if u < (k:ℝ) then 1 else 0))
            = ∑ k ∈ Finset.Icc 1 K, (if u < (k:ℝ) then 1/(k:ℝ)^2 else 0) := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hh : u < (k:ℝ) <;> simp [hh]
        have h4 : (0:ℝ) ≤ 4 * (x:ℝ)^((1:ℝ)/4) := by positivity
        calc 4 * (x:ℝ)^((1:ℝ)/4) * (∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ)^2) * (if u < (k:ℝ) then 1 else 0))
            = 4 * (x:ℝ)^((1:ℝ)/4) * (∑ k ∈ Finset.Icc 1 K, (if u < (k:ℝ) then 1/(k:ℝ)^2 else 0)) := by
              rw [hEq]
          _ ≤ 4 * (x:ℝ)^((1:ℝ)/4) * (4/(u+1)) := mul_le_mul_of_nonneg_left h h4
    _ = 16 * (x:ℝ)^((1:ℝ)/4) / (u+1) := by ring


/-! ## Weak-support versions of the Fourier decay machinery (= support only above `x`) -/

lemma iteratedDeriv_quad_comp_eq_zero_of_gt_weak (K : ℕ) (x b : ℝ) (f : ℝ → ℝ)
    (hsupp : ∀ u, x ≤ u → f u = 0) (s : ℝ) (hs : x * s^2 + b^2 > x) :
    iteratedDeriv K (fun s => f (x * s^2 + b^2)) s = 0 := by
  have hcont : Continuous (fun t : ℝ => x * t^2 + b^2) := by fun_prop
  have hU : IsOpen {t : ℝ | x * t^2 + b^2 > x} := hcont.isOpen_preimage _ isOpen_Ioi
  have hEq : Set.EqOn (fun s => f (x * s^2 + b^2)) (fun _ => (0:ℝ)) {t | x * t^2 + b^2 > x} := by
    intro t ht
    exact hsupp _ ht.le
  have h := (hEq.iteratedDeriv_of_isOpen hU K) hs
  rw [h]
  simp

lemma iteratedDeriv_quad_comp_le_weak (K : ℕ) (x y b : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (f : ℝ → ℝ) (hf : ContDiff ℝ K f)
    (hbd : ∀ j ≤ K, ∀ u ∈ Set.Icc 0 x, |iteratedDeriv j f u| ≤ (y ^ j)⁻¹)
    (hsupp : ∀ u, x ≤ u → f u = 0) (s : ℝ) :
    |iteratedDeriv K (fun s => f (x * s^2 + b^2)) s| ≤
      (Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  by_cases h : x * s^2 + b^2 ≤ x
  · have hmem : x * s^2 + b^2 ∈ Set.Icc 0 x := ⟨by nlinarith [sq_nonneg s, sq_nonneg b, hx], h⟩
    exact Commons.Analysis.Fourier.iteratedDeriv_comp_quad_bound K x y b hx hy hyx f hf hbd K le_rfl s hmem
  · rw [iteratedDeriv_quad_comp_eq_zero_of_gt_weak K x b f hsupp s (not_le.mp h), abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg (by nlinarith [hx0]) hy0.le) K)

lemma fourier_decay_one_const_weak (K : ℕ) (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (f : ℝ → ℝ) (hf : ContDiff ℝ K f) (hsupp : ∀ u, x ≤ u → f u = 0)
    (hbd : ∀ j ≤ K, ∀ u ∈ Set.Icc 0 x, |iteratedDeriv j f u| ≤ (y ^ j)⁻¹) :
    ∀ c b : ℝ, 0 < c → b ^ 2 ≤ x →
      |∫ t in Set.Ici (0 : ℝ), f (t ^ 2 + b ^ 2) * Real.cos (c * t)| ≤
        ((Fintype.card (OrderedFinpartition K) : ℝ) + 1) * 2^K * Real.sqrt x * (Real.sqrt x / (c * y)) ^ K := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  intro c b hc hb2
  let r : ℝ := Real.sqrt x
  have hr0 : 0 < r := by
    change 0 < Real.sqrt x
    exact Real.sqrt_pos.mpr hx0
  have hr2 : r^2 = x := by
    change (Real.sqrt x)^2 = x
    exact Real.sq_sqrt hx0.le
  let l : ℝ := c * r
  have hl0 : 0 < l := by
    change 0 < c * r
    positivity
  let F : ℝ → ℝ := fun s => f (x * s^2 + b^2)
  have hFcd : ContDiff ℝ K F := by
    change ContDiff ℝ K (fun s : ℝ => f (x * s^2 + b^2))
    have hq : ContDiff ℝ (K : WithTop ℕ∞) (fun s : ℝ => x * s^2 + b^2) := by fun_prop
    have := hf.comp hq
    simpa [Function.comp_def] using this
  have hFc : HasCompactSupport F := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    rw [Function.support_subset_iff]
    intro s hs
    have hu : x * s^2 + b^2 ∈ Set.Icc 0 x := by
      by_contra h
      have h0 : (0:ℝ) ≤ x * s^2 + b^2 := by positivity
      have hgt : x ≤ x * s^2 + b^2 := by
        by_contra hlt
        exact h ⟨h0, le_of_not_ge hlt⟩
      exact hs (hsupp _ hgt)
    have hs2 : s^2 ≤ 1 := by nlinarith [hu.2, sq_nonneg b, hx0]
    have hsabs : |s| ≤ 1 := by nlinarith [sq_abs s, abs_nonneg s]
    simpa only [Set.mem_Icc] using (abs_le.mp hsabs)
  have key1 : (∫ t in Set.Ici (0:ℝ), f (t^2 + b^2) * Real.cos (c*t))
      = r * ∫ s in Set.Ici (0:ℝ), F s * Real.cos (l*s) := by
    rw [Commons.Analysis.Fourier.integral_Ici_comp_mul_right_pos (r := r)
        (fun t : ℝ => f (t^2 + b^2) * Real.cos (c*t)) hr0]
    congr 1
    apply integral_congr_ae
    filter_upwards with s
    change f ((r*s)^2 + b^2) * Real.cos (c*(r*s)) = f (x*s^2+b^2) * Real.cos ((c*r)*s)
    rw [show (r*s)^2 = r^2 * s^2 by ring, hr2, show c*(r*s) = (c*r)*s by ring]
  have heven : ∀ s, (fun s => F s * Real.cos (l*s)) (-s) = (fun s => F s * Real.cos (l*s)) s := by
    intro s
    change f (x * (-s)^2 + b^2) * Real.cos ((c*r) * (-s)) = f (x * s^2 + b^2) * Real.cos ((c*r) * s)
    rw [show x * (-s)^2 + b^2 = x * s^2 + b^2 by ring,
        show (c*r) * (-s) = -((c*r) * s) by ring, Real.cos_neg]
  have key2 : ∫ s in Set.Ici (0:ℝ), F s * Real.cos (l*s) = (1/2) * ∫ s, F s * Real.cos (l*s) :=
    Commons.Analysis.Fourier.integral_Ici_zero_eq_half_of_even _ heven
  have hzero : ∀ s, x * s^2 + b^2 > x → iteratedDeriv K F s = 0 := by
    intro s hs
    change iteratedDeriv K (fun s : ℝ => f (x*s^2+b^2)) s = 0
    exact iteratedDeriv_quad_comp_eq_zero_of_gt_weak K x b f hsupp s hs
  have hsuppK : ∀ s, s ∉ Set.Icc (-1:ℝ) 1 → |iteratedDeriv K F s| = 0 := by
    intro s hs
    have hs' : (1:ℝ) < |s| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
      rcases hs with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hsq : 1 < s^2 := by nlinarith [sq_abs s, abs_nonneg s]
    have hgt : x * s^2 + b^2 > x := by nlinarith [hsq, hx0, sq_nonneg b]
    rw [hzero s hgt, abs_zero]
  have hC0nn : 0 ≤ (Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg (by linarith [hx0]) hy0.le) K)
  have hint : ∫ s, |iteratedDeriv K F s| ≤ 2 * ((Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K) := by
    have hbnd : ∀ s ∈ Set.Icc (-1:ℝ) 1,
        |iteratedDeriv K F s| ≤ (Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K := by
      intro s _
      change |iteratedDeriv K (fun s : ℝ => f (x*s^2+b^2)) s| ≤ _
      exact iteratedDeriv_quad_comp_le_weak K x y b hx hy hyx f hf hbd hsupp s
    have hnle : ‖∫ s in Set.Icc (-1:ℝ) 1, |iteratedDeriv K F s|‖
        ≤ ((Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K)
            * volume.real (Set.Icc (-1:ℝ) 1) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume)
        isCompact_Icc.measure_lt_top
        (fun s hs => by rw [Real.norm_eq_abs, abs_abs]; exact hbnd s hs)
    have hnn : 0 ≤ ∫ s in Set.Icc (-1:ℝ) 1, |iteratedDeriv K F s| :=
      setIntegral_nonneg measurableSet_Icc (fun s _ => abs_nonneg _)
    calc ∫ s, |iteratedDeriv K F s|
        = ∫ s in Set.Icc (-1:ℝ) 1, |iteratedDeriv K F s| :=
          (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsuppK).symm
      _ = ‖∫ s in Set.Icc (-1:ℝ) 1, |iteratedDeriv K F s|‖ := (Real.norm_of_nonneg hnn).symm
      _ ≤ (Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K * volume.real (Set.Icc (-1:ℝ) 1) := hnle
      _ = 2 * ((Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K) := by
          rw [Real.volume_real_Icc]; norm_num; ring
  have hPF := Commons.Analysis.Fourier.fourier_cos_decay K F hFcd hFc l hl0
  rw [key1, abs_mul, abs_of_pos hr0, key2, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < (1:ℝ)/2)]
  calc r * ((1/2) * |∫ s, F s * Real.cos (l*s)|)
      ≤ r * ((1/2) * ((l⁻¹)^K * (2 * ((Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K)))) := by
        apply mul_le_mul_of_nonneg_left _ hr0.le
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact le_trans hPF (mul_le_mul_of_nonneg_left hint (by positivity))
    _ = r * (l⁻¹)^K * ((Fintype.card (OrderedFinpartition K) : ℝ) * (2 * x / y)^K) := by ring
    _ = ((Fintype.card (OrderedFinpartition K) : ℝ) * 2^K) * (r * (r/(c*y))^K) := by
        rw [show l = c * r from rfl]
        exact Commons.Analysis.Fourier.algebra_key K x y c r hr2 hc hy0 hr0
    _ ≤ (((Fintype.card (OrderedFinpartition K) : ℝ) + 1) * 2^K) * (r * (r/(c*y))^K) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        · positivity
    _ = (((Fintype.card (OrderedFinpartition K) : ℝ) + 1) * 2^K) * Real.sqrt x * (Real.sqrt x / (c*y))^K := by
        change _ = (((Fintype.card (OrderedFinpartition K) : ℝ) + 1) * 2^K) * r * (r/(c*y))^K
        ring


lemma fourier_integral_decay_uniform_weak (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x y A : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x) (hA : 0 < A)
      (f : ℝ → ℝ), ContDiff ℝ K f → (∀ u, x ≤ u → f u = 0) →
      (∀ i ≤ K, ∀ u ∈ Set.Icc 0 x, |iteratedDeriv i f u| ≤ A * (y ^ i)⁻¹) →
      ∀ c b : ℝ, 0 < c → b ^ 2 ≤ x →
      |∫ t in Set.Ici (0:ℝ), f (t ^ 2 + b ^ 2) * Real.cos (c * t)| ≤
        C * A * Real.sqrt x * (Real.sqrt x / (c * y)) ^ K := by
  refine ⟨((Fintype.card (OrderedFinpartition K) : ℝ) + 1) * 2^K, by positivity, ?_⟩
  intro x y A hx hy hyx hA f hf hsupp hbd c b hc hb2
  let g : ℝ → ℝ := fun u => f u / A
  have hgcd : ContDiff ℝ K g := by
    dsimp only [g]
    exact hf.div_const A
  have hgsupp : ∀ u, x ≤ u → g u = 0 := by
    intro u hu
    dsimp only [g]
    rw [hsupp u hu, zero_div]
  have hgderiv : ∀ j u, iteratedDeriv j g u = iteratedDeriv j f u / A := by
    intro j u
    exact iteratedDeriv_div_const (x := u) (n := j) f A
  have hgbd : ∀ j ≤ K, ∀ u ∈ Set.Icc 0 x, |iteratedDeriv j g u| ≤ (y ^ j)⁻¹ := by
    intro j hj u hu
    rw [hgderiv j u, abs_div, abs_of_pos hA]
    have h1 := hbd j hj u hu
    rw [div_le_iff₀ hA]
    simpa [mul_comm] using h1
  have hbnd := fourier_decay_one_const_weak K x y hx hy hyx g hgcd hgsupp hgbd c b hc hb2
  have hint : (∫ t in Set.Ici (0:ℝ), f (t^2 + b^2) * Real.cos (c*t))
      = A * ∫ t in Set.Ici (0:ℝ), g (t^2 + b^2) * Real.cos (c*t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [g]
    field_simp
  rw [hint, abs_mul, abs_of_pos hA]
  calc A * |∫ t in Set.Ici (0:ℝ), g (t^2 + b^2) * Real.cos (c*t)|
      ≤ A * (((Fintype.card (OrderedFinpartition K) : ℝ) + 1) * 2^K * Real.sqrt x * (Real.sqrt x / (c*y))^K) :=
        mul_le_mul_of_nonneg_left hbnd hA.le
    _ = (((Fintype.card (OrderedFinpartition K) : ℝ) + 1) * 2^K) * A * Real.sqrt x * (Real.sqrt x / (c*y))^K := by
        ring

private lemma summable_int_abs_pow_inv (j : ℕ) (hj : 2 ≤ j) :
    Summable (fun k : ℤ => ((|(k : ℝ)|) ^ j)⁻¹) := by
  have hj1 : (1 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 1 < j)
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩
  · have hcast : (fun n : ℕ => ((|(((n : ℤ) : ℝ))|) ^ j)⁻¹)
        = (fun n : ℕ => (((n : ℝ)) ^ j)⁻¹) := by
      ext n; congr 2; rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
    rw [hcast]
    refine ((Real.summable_nat_rpow (p := (-(j : ℝ)))).mpr (by linarith)).congr ?_
    intro n
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast]
  · have hcast : (fun n : ℕ => ((|((-(n : ℤ) : ℤ) : ℝ)|) ^ j)⁻¹)
        = (fun n : ℕ => (((n : ℝ)) ^ j)⁻¹) := by
      ext n; congr 2
      rw [show ((-(n : ℤ) : ℤ) : ℝ) = -(n : ℝ) by push_cast; ring, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg n)]
    rw [hcast]
    refine ((Real.summable_nat_rpow (p := (-(j : ℝ)))).mpr (by linarith)).congr ?_
    intro n
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast]

theorem tsum_tail_Icos_le_weak (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (X y A D : ℝ) (hX : 1 ≤ X) (hy : 1 ≤ y) (hyX : y ≤ X)
      (hA : 0 < A) (hD : 0 < D) (b : ℝ) (hb : b ^ 2 ≤ X) (K : ℝ) (hK : 1 ≤ K),
      ContDiff ℝ j f → (∀ u, X ≤ u → f u = 0) →
      (∀ i ≤ j, ∀ u ∈ Set.Icc 0 X, |iteratedDeriv i f u| ≤ A * (y ^ i)⁻¹) →
      (∑' k : ℤ, (if K ≤ |(k : ℝ)| then
          |∫ t in Set.Ici (0 : ℝ), f (t ^ 2 + b ^ 2) * Real.cos (2 * Real.pi * (k : ℝ) * t / D)|
          else 0))
        ≤ C * A * Real.sqrt X * (D * Real.sqrt X / (K * y)) ^ j * K := by
  obtain ⟨c0, hc0pos, hc0⟩ := fourier_integral_decay_uniform_weak j
  obtain ⟨ct, hctpos, hct⟩ := Commons.Analysis.PSeries.tsum_int_abs_pow_neg_tail_le
  refine ⟨c0 * ct / (2 * Real.pi)^j, by positivity, ?_⟩
  intro f X y A D hX hy hyX hA hD b hb K hK hf hsupp hbd
  have hX0 : (0:ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le zero_lt_one hy
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  set scal : ℝ := c0 * A * Real.sqrt X * (D * Real.sqrt X / (2 * Real.pi * y))^j with hscal
  have hscalnn : 0 ≤ scal := by rw [hscal]; positivity
  have hterm : ∀ k : ℤ, K ≤ |(k:ℝ)| →
      |∫ t in Set.Ici (0:ℝ), f (t^2+b^2) * Real.cos (2*Real.pi*(k:ℝ)*t/D)|
        ≤ scal * ((|(k:ℝ)|)^j)⁻¹ := by
    intro k hk
    have hkpos : 0 < |(k:ℝ)| := lt_of_lt_of_le (by linarith) hk
    set c : ℝ := 2*Real.pi*|(k:ℝ)|/D with hcdef
    have hcpos : 0 < c := by rw [hcdef]; positivity
    have hbound := hc0 X y A hX hy hyX hA f hf hsupp hbd c b hcpos hb
    have hcos : ∀ t : ℝ, Real.cos (c*t) = Real.cos (2*Real.pi*(k:ℝ)*t/D) := by
      intro t
      rw [hcdef]
      by_cases hk0 : (0:ℝ) ≤ (k:ℝ)
      · rw [abs_of_nonneg hk0]; congr 1; ring
      · push_neg at hk0
        rw [abs_of_neg hk0,
          show (2*Real.pi*(-(k:ℝ))/D)*t = -(2*Real.pi*(k:ℝ)*t/D) by ring, Real.cos_neg]
    have hint_eq : (∫ t in Set.Ici (0:ℝ), f (t^2+b^2) * Real.cos (c*t))
        = ∫ t in Set.Ici (0:ℝ), f (t^2+b^2) * Real.cos (2*Real.pi*(k:ℝ)*t/D) := by
      apply setIntegral_congr_fun measurableSet_Ici
      intro t ht
      simp only []
      rw [hcos t]
    have h1 : √X / (c*y) = (D*√X/(2*Real.pi*y)) * (|(k:ℝ)|)⁻¹ := by
      rw [hcdef, Real.sqrt_eq_rpow]
      field_simp
    have hfac : c0 * A * Real.sqrt X * (√X/(c*y))^j = scal * ((|(k:ℝ)|)^j)⁻¹ := by
      rw [hscal, h1, mul_pow, inv_pow]; ring
    rw [← hint_eq]
    rw [hfac] at hbound
    exact hbound
  set g : ℤ → ℝ := fun k => if K ≤ |(k:ℝ)| then
      |∫ t in Set.Ici (0:ℝ), f (t^2+b^2) * Real.cos (2*Real.pi*(k:ℝ)*t/D)| else 0 with hg
  set V : ℤ → ℝ := fun k => if K ≤ |(k:ℝ)| then scal * ((|(k:ℝ)|)^j)⁻¹ else 0 with hV
  have hle : ∀ k : ℤ, g k ≤ V k := by
    intro k
    rw [hg, hV]
    by_cases hk : K ≤ |(k:ℝ)| <;> simp only [hk, ↓reduceIte]
    · exact hterm k hk
    · exact le_refl 0
  have hWsumm : Summable (fun k : ℤ => scal * ((|(k:ℝ)|)^j)⁻¹) :=
    (summable_int_abs_pow_inv j hj).mul_left scal
  have hVsumm : Summable V := by
    refine Summable.of_nonneg_of_le (f := fun k : ℤ => scal * ((|(k:ℝ)|)^j)⁻¹) ?_ ?_ hWsumm
    · intro k
      rw [hV]
      by_cases hk : K ≤ |(k:ℝ)| <;> simp only [hk, ↓reduceIte]
      · exact mul_nonneg hscalnn (inv_nonneg.mpr (pow_nonneg (abs_nonneg _) _))
      · exact le_refl 0
    · intro k
      rw [hV]
      by_cases hk : K ≤ |(k:ℝ)| <;> simp only [hk, ↓reduceIte]
      · exact le_refl _
      · exact mul_nonneg hscalnn (inv_nonneg.mpr (pow_nonneg (abs_nonneg _) _))
  have hgsumm : Summable g := by
    refine Summable.of_nonneg_of_le (f := V) ?_ hle hVsumm
    intro k
    rw [hg]
    by_cases hk : K ≤ |(k:ℝ)| <;> simp only [hk, ↓reduceIte]
    · exact abs_nonneg _
    · exact le_refl 0
  have h1 : (∑' k : ℤ, g k) ≤ ∑' k : ℤ, V k := Summable.tsum_le_tsum hle hgsumm hVsumm
  have h2 : (∑' k : ℤ, V k)
      = scal * (∑' k : ℤ, (if K ≤ |(k:ℝ)| then ((|(k:ℝ)|)^j)⁻¹ else 0)) := by
    rw [hV, ← tsum_mul_left]
    apply tsum_congr
    intro k
    by_cases hk : K ≤ |(k:ℝ)| <;> simp [hk]
  have h3 : (∑' k : ℤ, (if K ≤ |(k:ℝ)| then ((|(k:ℝ)|)^j)⁻¹ else 0))
      ≤ ct * K ^ (1 - (j:ℝ)) := hct j K hj hK
  have harith : scal * (ct * K ^ (1 - (j:ℝ)))
      = (c0 * ct / (2 * Real.pi)^j) * A * Real.sqrt X * (D * Real.sqrt X / (K * y))^j * K := by
    rw [hscal]
    have hKrp : K ^ (1 - (j:ℝ)) = (K:ℝ) * ((K:ℝ)^j)⁻¹ := by
      rw [show (1 - (j:ℝ)) = 1 + (-(j:ℝ)) by ring, Real.rpow_add hK0, Real.rpow_one,
        Real.rpow_neg hK0.le, Real.rpow_natCast]
    rw [hKrp]
    simp only [div_pow, mul_pow]
    field_simp
  calc (∑' k : ℤ, g k) ≤ ∑' k : ℤ, V k := h1
    _ = scal * (∑' k : ℤ, (if K ≤ |(k:ℝ)| then ((|(k:ℝ)|)^j)⁻¹ else 0)) := h2
    _ ≤ scal * (ct * K ^ (1 - (j:ℝ))) := mul_le_mul_of_nonneg_left h3 hscalnn
    _ = (c0 * ct / (2 * Real.pi)^j) * A * Real.sqrt X * (D * Real.sqrt X / (K * y))^j * K := harith


/-! ## The Fourier expansion of the smoothed remainder, split into `b = 0` and `b ≥ 1` -/

lemma tsum_Icos_rhoRe_even (f : ℝ → ℝ) (d b : ℕ) (hd : 0 < d) (hf : ContDiff ℝ 2 f)
    (hcs : HasCompactSupport fun t : ℝ => f (t ^ 2 + (b : ℝ) ^ 2)) :
    (∑' k : ℤ, Icos f d b k * rhoRe d b k) - Icos f d b 0 * rhoRe d b 0
      = 2 * ∑' k : ℤ, (if 0 < k then Icos f d b k * rhoRe d b k else 0) := by
  have hb : Summable fun k : ℤ => Icos f d b k * rhoRe d b k := by
    refine Summable.of_norm_bounded ((summable_Icos f d b hd hf hcs).norm.mul_left (d : ℝ))
      (fun k => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    calc |Icos f d b k| * |rhoRe d b k| ≤ |Icos f d b k| * (d : ℝ) :=
          mul_le_mul_of_nonneg_left (abs_rhoRe_le d b k) (abs_nonneg _)
      _ = (d : ℝ) * |Icos f d b k| := by ring
  have h1 : (∑' k : ℤ, Icos f d b k * rhoRe d b k) - Icos f d b 0 * rhoRe d b 0
      = ∑' k : ℤ, (if k = 0 then 0 else Icos f d b k * rhoRe d b k) := by
    rw [Summable.tsum_eq_add_tsum_ite hb 0]; ring
  rw [h1]
  exact tsum_even_eq_two_mul_pos _ (fun k => by rw [Icos_neg, rhoRe_neg]) hb

lemma ASum_sub_MdF_eq_b (f : ℝ → ℝ) (d x b : ℕ) (hd : 0 < d) (hx : 1 ≤ x)
    (hf : ContDiff ℝ 2 f) (hsupp : ∀ u, (x:ℝ) ≤ u → f u = 0) :
    ASum f d b - (2 / (d:ℝ)) * (rho b d : ℝ) * I0 f b
      = (4 / (d:ℝ)) * ∑' k : ℤ, (if 0 < k then Icos f d b k * rhoRe d b k else 0) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hcs : HasCompactSupport fun t : ℝ => f (t ^ 2 + (b : ℝ) ^ 2) :=
    hasCompactSupport_quad' f (b:ℝ) (x:ℝ) hsupp
  have hkey := tsum_dvd_quad_eq_rhoRe f d b hd hf hcs
  have hper := tsum_Icos_rhoRe_even f d b hd hf hcs
  rw [show ASum f d b = (2/(d:ℝ)) * ∑' k : ℤ, Icos f d b k * rhoRe d b k from hkey]
  rw [← Icos_zero f d b, ← rhoRe_zero d b]
  rw [show (2/(d:ℝ)) * (rhoRe d b 0) * (Icos f d b 0)
      = (2/(d:ℝ)) * (Icos f d b 0 * rhoRe d b 0) by ring]
  rw [← mul_sub, hper]
  ring

theorem AdF_sub_MdF_decomp (f : ℝ → ℝ) (d x : ℕ) (hd : 0 < d) (hx : 1 ≤ x)
    (hf : ContDiff ℝ 2 f) (hsupp : ∀ u, (x:ℝ) ≤ u → f u = 0) :
    AdF (fun n : ℕ => f n) d x - MdF f d x
      = (ASum f d 0 - (2/(d:ℝ))*(rho 0 d : ℝ)*I0 f 0)
        + (4/(d:ℝ)) * ∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
            ∑' k : ℤ, (if 0 < k then Icos f d b k * rhoRe d b k else 0) := by
  rw [AdF_sub_MdF_eq_kpos f d x hd hx hf hsupp]
  have hsplit : Finset.range (Nat.sqrt x + 1) = insert 0 (Finset.Icc 1 (Nat.sqrt x)) := by
    ext b; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), Z_zero]
  simp only [Nat.cast_one, one_mul]
  have h0 := ASum_sub_MdF_eq_b f d x 0 hd hx hf hsupp
  rw [show (∑' k : ℤ, (if 0 < k then Icos f d 0 k * rhoRe d 0 k else 0))
      = (ASum f d 0 - (2/(d:ℝ))*(rho 0 d : ℝ)*I0 f 0) * ((d:ℝ)/4) from by
    rw [h0]; field_simp]
  have hdne : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp


/-! ## The substitution `t = u √x / k` and the swap of sum and integral -/

lemma Icos_eq_subst (f : ℝ → ℝ) (d x : ℕ) (b k : ℕ) (hd : 1 ≤ d) (hx : 1 ≤ x) (hk : 1 ≤ k)
    (hfsup : ∀ u, (x:ℝ) ≤ u → f u = 0) :
    Icos f d b k = (Real.sqrt (x:ℝ) / (k:ℝ)) *
      ∫ u in (0:ℝ)..(k:ℝ), f ((x:ℝ) * u^2 / (k:ℝ)^2 + (b:ℝ)^2)
        * Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) := by
  rw [Icos]
  exact Commons.Analysis.Fourier.integral_cos_quadratic_subst f (x:ℝ) (d:ℝ) (b:ℝ)
    (by positivity) (by positivity) k hk (fun u hu => hfsup u hu.le)

/-- **Substitution + swap.** `Σ_b Z(b) Σ_k Icos f d b k ρ(k,b;d)` equals
`√x ∫_0^K cos(2π√x u/d) Y(u) du` with `Y(u) = Σ_b Z(b) Σ_k k⁻¹ f(xu²/k²+b²) ρ(k,b;d)`. -/
lemma Psi_eq_integral (f : ℝ → ℝ) (d x K : ℕ) (hd : 1 ≤ d) (hx : 1 ≤ x) (hK : 1 ≤ K)
    (hf : ContDiff ℝ 2 f) (hfsup : ∀ u, (x:ℝ) ≤ u → f u = 0) :
    (∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
        ∑ k ∈ Finset.Icc 1 K, Icos f d b k * rhoRe d b k)
      = Real.sqrt (x:ℝ) * ∫ u in (0:ℝ)..(K:ℝ),
          Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) *
            ∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
              ∑ k ∈ Finset.Icc 1 K,
                (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k := by
  have hcos : Continuous fun u : ℝ => Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) := by
    apply Real.continuous_cos.comp
    apply Continuous.div_const
    exact continuous_const.mul continuous_id
  have hargc : ∀ (k : ℕ) (b : ℕ), Continuous fun u : ℝ => (x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2 := by
    intro k b
    apply Continuous.add
    · apply Continuous.div_const
      exact continuous_const.mul (continuous_id.pow 2)
    · exact continuous_const
  -- per-`k` identity
  have hsplit : ∀ b k : ℕ, 1 ≤ k → Icos f d b k * rhoRe d b k
      = Real.sqrt (x:ℝ) * ∫ u in (0:ℝ)..(k:ℝ),
          (1/(k:ℝ)) * rhoRe d b k *
            (f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2)
              * Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ))) := by
    intro b k hk
    rw [Icos_eq_subst f d x b k hd hx hk hfsup]
    rw [intervalIntegral.integral_const_mul]
    ring
  -- vanishing of the summand above `u = k`
  have hzero : ∀ b k : ℕ, ∀ u : ℝ, (k:ℝ) ≤ u →
      (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k = 0 := by
    intro b k u hu
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast h
    rw [show f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) = 0 by
      apply hfsup
      have h1 : (1:ℝ) ≤ u^2/(k:ℝ)^2 := by
        rw [le_div_iff₀ (pow_pos hk0 2)]
        nlinarith [hu, hk0]
      have h2 : (x:ℝ) * 1 ≤ (x:ℝ) * (u^2/(k:ℝ)^2) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      simp only [mul_one] at h2
      have h3 : (x:ℝ) * u^2/(k:ℝ)^2 = (x:ℝ) * (u^2/(k:ℝ)^2) := by ring
      nlinarith [h2, h3, sq_nonneg (b:ℝ)]]
    ring
  -- the `b`-sum
  have hb : ∀ b ∈ Finset.Icc 1 (Nat.sqrt x),
      (∑ k ∈ Finset.Icc 1 K, Icos f d b k * rhoRe d b k)
        = Real.sqrt (x:ℝ) * ∫ u in (0:ℝ)..(K:ℝ),
            Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) *
              ∑ k ∈ Finset.Icc 1 K,
                (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k := by
    intro b _
    have hii : ∀ k ∈ Finset.Icc 1 K, IntervalIntegrable (fun u : ℝ =>
        (1/(k:ℝ)) * rhoRe d b k * (f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2)
          * Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)))) volume (0:ℝ) (k:ℝ) := by
      intro k hk
      exact Continuous.intervalIntegrable (μ := volume) (a := (0:ℝ)) (b := (k:ℝ))
        (continuous_const.mul (((hf.continuous.comp (hargc k b)).mul hcos)))
    have hswap : (∑ k ∈ Finset.Icc 1 K, ∫ u in (0:ℝ)..(k:ℝ),
          (1/(k:ℝ)) * rhoRe d b k *
            (f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2)
              * Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ))))
        = ∫ u in (0:ℝ)..(K:ℝ), ∑ k ∈ (Finset.Icc 1 K).filter (fun k : ℕ => u < (k:ℝ)),
            (1/(k:ℝ)) * rhoRe d b k *
              (f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2)
                * Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ))) :=
      Commons.Analysis.Integral.sum_intervalIntegral_Icc_swap _ K hii
    have hfilt : ∀ u : ℝ,
        (∑ k ∈ (Finset.Icc 1 K).filter (fun k : ℕ => u < (k:ℝ)),
            (1/(k:ℝ)) * rhoRe d b k *
              (f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2)
                * Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ))))
          = Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) *
              ∑ k ∈ Finset.Icc 1 K,
                (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k := by
      intro u
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : u < (k:ℝ)
      · rw [if_pos h]; ring
      · rw [if_neg h, hzero b k u (le_of_not_gt h)]; ring
    calc (∑ k ∈ Finset.Icc 1 K, Icos f d b k * rhoRe d b k)
        = Real.sqrt (x:ℝ) * ∑ k ∈ Finset.Icc 1 K, ∫ u in (0:ℝ)..(k:ℝ),
            (1/(k:ℝ)) * rhoRe d b k *
              (f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2)
                * Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ))) := by
          rw [Finset.sum_congr rfl (fun k hk => hsplit b k (Finset.mem_Icc.mp hk).1),
            Finset.mul_sum]
      _ = Real.sqrt (x:ℝ) * ∫ u in (0:ℝ)..(K:ℝ),
            ∑ k ∈ (Finset.Icc 1 K).filter (fun k : ℕ => u < (k:ℝ)),
              (1/(k:ℝ)) * rhoRe d b k *
                (f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2)
                  * Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ))) := by
          rw [hswap]
      _ = Real.sqrt (x:ℝ) * ∫ u in (0:ℝ)..(K:ℝ),
            Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) *
              ∑ k ∈ Finset.Icc 1 K,
                (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k := by
          congr 1
          apply intervalIntegral.integral_congr
          intro u _
          exact hfilt u
  -- assemble over `b`
  have hcont : ∀ b : ℕ, Continuous fun u : ℝ =>
      ∑ k ∈ Finset.Icc 1 K,
        (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k := by
    intro b
    apply continuous_finsetSum
    intro k hk
    exact (continuous_const.mul (hf.continuous.comp (hargc k b))).mul continuous_const
  calc (∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
        ∑ k ∈ Finset.Icc 1 K, Icos f d b k * rhoRe d b k)
      = ∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
          (Real.sqrt (x:ℝ) * ∫ u in (0:ℝ)..(K:ℝ),
            Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) *
              ∑ k ∈ Finset.Icc 1 K,
                (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k) := by
        apply Finset.sum_congr rfl
        intro b hb'
        rw [hb b hb']
    _ = Real.sqrt (x:ℝ) * ∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
          ∫ u in (0:ℝ)..(K:ℝ),
            Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) *
              ∑ k ∈ Finset.Icc 1 K,
                (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
    _ = Real.sqrt (x:ℝ) * ∑ b ∈ Finset.Icc 1 (Nat.sqrt x),
          ∫ u in (0:ℝ)..(K:ℝ),
            Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) *
              ((Z b : ℝ) * ∑ k ∈ Finset.Icc 1 K,
                (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k) := by
        congr 1
        apply Finset.sum_congr rfl
        intro b _
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro u _
        ring
    _ = Real.sqrt (x:ℝ) * ∫ u in (0:ℝ)..(K:ℝ),
          ∑ b ∈ Finset.Icc 1 (Nat.sqrt x),
            Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) *
              ((Z b : ℝ) * ∑ k ∈ Finset.Icc 1 K,
                (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k) := by
        congr 1
        rw [intervalIntegral.integral_finset_sum]
        intro b _
        exact Continuous.intervalIntegrable (μ := volume) (a := (0:ℝ)) (b := (K:ℝ))
          (hcos.mul (continuous_const.mul (hcont b)))
    _ = Real.sqrt (x:ℝ) * ∫ u in (0:ℝ)..(K:ℝ),
          Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) *
            ∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
              ∑ k ∈ Finset.Icc 1 K,
                (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k := by
        congr 1
        apply intervalIntegral.integral_congr
        intro u _
        simp only []
        rw [Finset.mul_sum]


/-! ## Identifying `Y(u)` with the real part of the large-sieve form -/

lemma ch_re (x : ℝ) :
    (Commons.Analysis.ExponentialSums.ch x).re = Real.cos (2 * Real.pi * x) := by
  rw [Commons.Analysis.ExponentialSums.ch, Complex.exp_ofReal_mul_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]

lemma sum_re_eq {α : Type*} (s : Finset α) (g : α → ℂ) :
    (∑ i ∈ s, g i).re = ∑ i ∈ s, (g i).re := map_sum Complex.reCLM g s

lemma rhoRe_eq_re_ch (d l k : ℕ) :
    rhoRe d l k = (∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => (ν^2 + l^2) % d = 0),
        Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * (k:ℝ) / d)).re := by
  have hfilt : (Finset.range d).filter (fun r : ℕ => (d:ℤ) ∣ (r:ℤ)^2+(l:ℤ)^2)
      = (Finset.range d).filter (fun ν : ℕ => (ν^2+l^2) % d = 0) := by
    apply Finset.filter_congr
    intro r _
    exact dvd_int_iff_mod_eq_zero
  rw [rhoRe, hfilt, sum_re_eq]
  apply Finset.sum_congr rfl
  intro r _
  rw [ch_re]
  congr 1
  push_cast
  ring

noncomputable def Yd (f : ℝ → ℝ) (x : ℕ) (d K : ℕ) (u : ℝ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
    ∑ k ∈ Finset.Icc 1 K,
      (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k

noncomputable def xi (f : ℝ → ℝ) (x : ℕ) (u : ℝ) : ℕ → ℕ → ℂ :=
  fun k l => (((1/(k:ℝ)) * (Z l : ℝ) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (l:ℝ)^2) : ℝ) : ℂ)

lemma Yd_eq_re (f : ℝ → ℝ) (x : ℕ) (d K : ℕ) (u : ℝ) :
    Yd f x d K u = (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
        xi f x u k l * ∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => (ν^2+l^2) % d = 0),
          Commons.Analysis.ExponentialSums.ch ((ν:ℝ)*(k:ℝ)/d)).re := by
  rw [Yd, Finset.sum_comm, sum_re_eq]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mul_sum, sum_re_eq]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (xi f x u k l * ∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => (ν^2+l^2) % d = 0),
        Commons.Analysis.ExponentialSums.ch ((ν:ℝ)*(k:ℝ)/d)).re
      = (xi f x u k l).re * (∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => (ν^2+l^2) % d = 0),
        Commons.Analysis.ExponentialSums.ch ((ν:ℝ)*(k:ℝ)/d)).re from by
    rw [Complex.mul_re]
    have : (xi f x u k l).im = 0 := by simp [xi]
    rw [this]; ring]
  rw [rhoRe_eq_re_ch d l k]
  rw [show (xi f x u k l).re = (1/(k:ℝ)) * (Z l : ℝ) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (l:ℝ)^2) from by
    simp [xi, Complex.ofReal_re]]
  ring


/-- Splitting `Σ'_{k>0} X k` at `K`. -/
lemma tsum_pos_split (X : ℤ → ℝ) (K : ℕ)
    (h1 : Summable fun k : ℤ => (if (0:ℤ) < k then X k else 0)) :
    (∑' k : ℤ, (if 0 < k then X k else 0))
      = (∑ k ∈ Finset.Icc 1 K, X (k:ℤ))
        + (∑' k : ℤ, (if (K:ℤ) < k then X k else 0)) := by
  have h2 : Summable fun k : ℤ => (if (K:ℤ) < k then X k else 0) := by
    refine Summable.of_norm_bounded h1.norm (fun k => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases h : (K:ℤ) < k
    · rw [if_pos h]
      have hk : (0:ℤ) < k := by omega
      rw [if_pos hk]
    · rw [if_neg h]; simp
  have hdiff : (∑' k : ℤ, ((if (0:ℤ) < k then X k else 0) - (if (K:ℤ) < k then X k else 0)))
      = ∑ k ∈ Finset.Icc 1 K, X (k:ℤ) := by
    have hfin : (∑' k : ℤ, ((if (0:ℤ) < k then X k else 0) - (if (K:ℤ) < k then X k else 0)))
        = ∑ k ∈ Finset.Icc (1:ℤ) (K:ℤ), X k := by
      rw [tsum_eq_sum (s := Finset.Icc (1:ℤ) (K:ℤ))]
      · apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_Icc] at hk
        rw [if_pos (by omega : (0:ℤ) < k), if_neg (by omega : ¬ ((K:ℤ) < k))]; ring
      · intro k hk
        simp only [Finset.mem_Icc, not_and_or, not_le] at hk
        rcases hk with hk | hk
        · have hk0' : ¬ ((0:ℤ) < k) := by omega
          have hkK' : ¬ ((K:ℤ) < k) := by omega
          rw [if_neg hk0', if_neg hkK']; ring
        · have hk0' : (0:ℤ) < k := by omega
          rw [if_pos hk0', if_pos hk]; ring
    rw [hfin, sum_Icc_int_cast (fun j : ℤ => X j) K]
    rw [show (∑ j ∈ Finset.range K, X ((j:ℤ) + 1)) = ∑ j ∈ Finset.range K, X (((j+1 : ℕ)):ℤ) from by
      apply Finset.sum_congr rfl
      intro j _
      simp]
    rw [← reindex_Icc_real (fun d : ℕ => X (d:ℤ)) K]
  have hsub := Summable.tsum_sub h1 h2
  linarith [hsub, hdiff]


/-- Tail bound for the truncated `k`-sum: the terms with `k > K` are small by the Fourier decay. -/
lemma tsum_tail_Icos_tail_le (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (x y : ℕ) (A : ℝ) (D K : ℕ),
      1 ≤ x → 1 ≤ y → y ≤ x → 0 < A → 1 ≤ D → 1 ≤ K →
      ContDiff ℝ j f → (∀ u, (x:ℝ) ≤ u → f u = 0) →
      (∀ i ≤ j, ∀ u ∈ Set.Icc 0 (x:ℝ), |iteratedDeriv i f u| ≤ A * (((y:ℝ)^i)⁻¹)) →
      (∑ d ∈ Finset.Icc 1 D, |∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
          ∑' k : ℤ, (if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0)|)
        ≤ C * (A + 1) * (x:ℝ)^((1:ℝ)/4) * Real.sqrt (x:ℝ)
            * ((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*y))^j * (K:ℝ) * (D:ℝ)^2 := by
  obtain ⟨Ct, hCtpos, htb⟩ := tsum_tail_Icos_le_weak j hj
  refine ⟨4 * Ct, by positivity, ?_⟩
  intro f x y A D K hx hy hyx hA hD hK hf hfsup hfd
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hy1 : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy
  have hyx1 : (y:ℝ) ≤ (x:ℝ) := by exact_mod_cast hyx
  have hK1 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by exact_mod_cast hj)
  have hZx : (∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ)) ≤ 2 * (x:ℝ)^((1:ℝ)/4) := by
    have h1 : ∀ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ)
        ≤ 2 * (if Nat.sqrt b ^ 2 = b then (1:ℝ) else 0) := by
      intro b hb
      have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      rw [show Z b = if Nat.sqrt b ^ 2 = b then 2 else 0 from by
        rw [Z, if_neg (by omega : b ≠ 0)]]
      by_cases h : Nat.sqrt b ^ 2 = b <;> simp [h]
    have h2 : (∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ))
        ≤ 2 * (Nat.sqrt (Nat.sqrt x) : ℝ) := by
      calc (∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ))
          ≤ ∑ b ∈ Finset.Icc 1 (Nat.sqrt x), 2 * (if Nat.sqrt b ^ 2 = b then (1:ℝ) else 0) :=
            Finset.sum_le_sum h1
        _ = 2 * (((Finset.Icc 1 (Nat.sqrt x)).filter (fun b => Nat.sqrt b ^ 2 = b)).card : ℝ) := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_boole]
        _ = 2 * (Nat.sqrt (Nat.sqrt x) : ℝ) := by rw [card_sq_Icc]
    have h3 : ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ≤ (x:ℝ)^((1:ℝ)/4) := by
      have h1 : ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ≤ Real.sqrt (Nat.sqrt x : ℝ) :=
        natSqrt_cast_le_sqrt (Nat.sqrt x)
      have h2 : Real.sqrt (Nat.sqrt x : ℝ) ≤ Real.sqrt (Real.sqrt (x:ℝ)) :=
        Real.sqrt_le_sqrt (natSqrt_cast_le_sqrt x)
      have h3 : Real.sqrt (Real.sqrt (x:ℝ)) = (x:ℝ) ^ ((1:ℝ)/4) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
        norm_num
      linarith [h1, h2, h3.le, h3.ge]
    linarith [h2, h3]
  have hper : ∀ d ∈ Finset.Icc 1 D,
      |∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
          ∑' k : ℤ, (if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0)|
        ≤ (2 * (x:ℝ)^((1:ℝ)/4)) * (d:ℝ) *
            (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
    have hbnd : ∀ b ∈ Finset.Icc 1 (Nat.sqrt x),
        |∑' k : ℤ, (if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0)|
          ≤ (d:ℝ) * (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)) := by
      intro b hb
      have hb2 : ((b:ℝ))^2 ≤ (x:ℝ) := by
        have h1 : b ≤ Nat.sqrt x := (Finset.mem_Icc.mp hb).2
        have h2 : b^2 ≤ x := Nat.le_sqrt'.mp h1
        exact_mod_cast h2
      have hcs : HasCompactSupport fun t : ℝ => f (t ^ 2 + (b:ℝ)^2) :=
        hasCompactSupport_quad' f (b:ℝ) (x:ℝ) hfsup
      have hIcosabs : Summable fun k : ℤ => |Icos f d b k| :=
        (summable_Icos f d b (by omega) hf2 hcs).norm
      have hsumm : Summable fun k : ℤ => Icos f d b k * rhoRe d b k := by
        refine Summable.of_norm_bounded (hIcosabs.mul_right (d:ℝ)) (fun k => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        calc |Icos f d b k| * |rhoRe d b k| ≤ |Icos f d b k| * (d:ℝ) :=
              mul_le_mul_of_nonneg_left (abs_rhoRe_le d b k) (abs_nonneg _)
          _ = |Icos f d b k| * (d:ℝ) := rfl
      have h1summ : Summable fun k : ℤ => (if (K:ℤ) < k then |Icos f d b k * rhoRe d b k| else 0) := by
        refine Summable.of_norm_bounded (hIcosabs.mul_right (d:ℝ)) (fun k => ?_)
        rw [Real.norm_eq_abs]
        by_cases h : (K:ℤ) < k
        · rw [if_pos h, abs_of_nonneg (by positivity)]
          rw [abs_mul]
          calc |Icos f d b k| * |rhoRe d b k| ≤ |Icos f d b k| * (d:ℝ) :=
                mul_le_mul_of_nonneg_left (abs_rhoRe_le d b k) (abs_nonneg _)
            _ = |Icos f d b k| * (d:ℝ) := rfl
        · rw [if_neg h, abs_zero]; positivity
      have h2summ : Summable fun k : ℤ => (if (K:ℤ) < k then (d:ℝ) * |Icos f d b k| else 0) := by
        refine Summable.of_norm_bounded (hIcosabs.mul_left (d:ℝ)) (fun k => ?_)
        rw [Real.norm_eq_abs]
        by_cases h : (K:ℤ) < k
        · rw [if_pos h, abs_of_nonneg (by positivity)]
        · rw [if_neg h, abs_zero]; positivity
      have hKsumm : Summable fun k : ℤ => (if (K:ℤ) < k then |Icos f d b k| else 0) := by
        refine Summable.of_norm_bounded hIcosabs (fun k => ?_)
        rw [Real.norm_eq_abs]
        by_cases h : (K:ℤ) < k <;> simp [h, abs_nonneg]
      have h3summ : Summable fun k : ℤ => (if (K:ℝ) ≤ |(k:ℝ)| then |Icos f d b k| else 0) := by
        refine Summable.of_norm_bounded hIcosabs (fun k => ?_)
        rw [Real.norm_eq_abs]
        by_cases h : (K:ℝ) ≤ |(k:ℝ)| <;> simp [h, abs_nonneg]
      have hm : Summable fun k : ℤ => |(if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0)| := by
        refine Summable.of_norm_bounded (hIcosabs.mul_right (d:ℝ)) (fun k => ?_)
        rw [Real.norm_eq_abs, abs_abs]
        by_cases h : (K:ℤ) < k
        · rw [if_pos h, abs_mul]
          calc |Icos f d b k| * |rhoRe d b k| ≤ |Icos f d b k| * (d:ℝ) :=
                mul_le_mul_of_nonneg_left (abs_rhoRe_le d b k) (abs_nonneg _)
            _ = |Icos f d b k| * (d:ℝ) := rfl
        · rw [if_neg h, abs_zero]; positivity
      calc |∑' k : ℤ, (if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0)|
          ≤ ∑' k : ℤ, ‖(if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0)‖ := by
            rw [← Real.norm_eq_abs]
            exact norm_tsum_le_tsum_norm (f := fun k : ℤ =>
              (if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0))
              (by simpa only [Real.norm_eq_abs] using hm)
        _ = ∑' k : ℤ, (if (K:ℤ) < k then |Icos f d b k * rhoRe d b k| else 0) := by
            apply tsum_congr; intro k
            by_cases h : (K:ℤ) < k <;> simp [h, Real.norm_eq_abs]
        _ ≤ ∑' k : ℤ, (if (K:ℤ) < k then (d:ℝ) * |Icos f d b k| else 0) := by
            refine Summable.tsum_le_tsum (fun k => ?_) h1summ h2summ
            by_cases h : (K:ℤ) < k
            · rw [if_pos h, if_pos h, abs_mul]
              calc |Icos f d b k| * |rhoRe d b k| ≤ |Icos f d b k| * (d:ℝ) :=
                    mul_le_mul_of_nonneg_left (abs_rhoRe_le d b k) (abs_nonneg _)
                _ = (d:ℝ) * |Icos f d b k| := by ring
            · rw [if_neg h, if_neg h]
        _ = (d:ℝ) * ∑' k : ℤ, (if (K:ℤ) < k then |Icos f d b k| else 0) := by
            rw [show (∑' k : ℤ, (if (K:ℤ) < k then (d:ℝ) * |Icos f d b k| else 0))
                = ∑' k : ℤ, (d:ℝ) * (if (K:ℤ) < k then |Icos f d b k| else 0) from by
              apply tsum_congr; intro k
              by_cases h : (K:ℤ) < k <;> simp [h]]
            rw [tsum_mul_left]
        _ ≤ (d:ℝ) * (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            refine le_trans (Summable.tsum_le_tsum (fun k => ?_) hKsumm h3summ) ?_
            · by_cases h : (K:ℤ) < k
              · rw [if_pos h]
                have h2 : (K:ℝ) ≤ |(k:ℝ)| := by
                  have h3 : (K:ℤ) ≤ |k| := le_trans (le_of_lt h) (le_abs_self k)
                  calc (K:ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h3
                    _ = |(k:ℝ)| := Int.cast_abs
                rw [if_pos h2]
              · rw [if_neg h]
                split <;> positivity
            · exact htb f (x:ℝ) (y:ℝ) A (d:ℝ) hx1 hy1 hyx1 hA (by positivity) (b:ℝ) hb2 (K:ℝ) hK1
                hf hfsup hfd
    calc |∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
          ∑' k : ℤ, (if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0)|
        ≤ ∑ b ∈ Finset.Icc 1 (Nat.sqrt x),
            |(Z b : ℝ) * ∑' k : ℤ, (if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
            |∑' k : ℤ, (if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0)| := by
          apply Finset.sum_congr rfl
          intro b _
          rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ ∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
            ((d:ℝ) * (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ))) := by
          apply Finset.sum_le_sum
          intro b hb
          exact mul_le_mul_of_nonneg_left (hbnd b hb) (by positivity)
      _ = (∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ)) *
            ((d:ℝ) * (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ))) := by
          rw [Finset.sum_mul]
      _ ≤ (2 * (x:ℝ)^((1:ℝ)/4)) * (d:ℝ) *
            (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)) := by
          have h := mul_le_mul_of_nonneg_right hZx
            (show (0:ℝ) ≤ (d:ℝ) * (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)) by positivity)
          calc (∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ)) *
                ((d:ℝ) * (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)))
              ≤ (2 * (x:ℝ)^((1:ℝ)/4)) *
                ((d:ℝ) * (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ))) := h
            _ = (2 * (x:ℝ)^((1:ℝ)/4)) * (d:ℝ) *
                (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)) := by ring
  calc (∑ d ∈ Finset.Icc 1 D, |∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
          ∑' k : ℤ, (if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0)|)
      ≤ ∑ d ∈ Finset.Icc 1 D, (2 * (x:ℝ)^((1:ℝ)/4)) * (d:ℝ) *
            (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)) :=
        Finset.sum_le_sum hper
    _ ≤ ∑ d ∈ Finset.Icc 1 D, (2 * (x:ℝ)^((1:ℝ)/4)) * (D:ℝ) *
            (Ct * A * Real.sqrt (x:ℝ) * (((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdD : (d:ℝ) ≤ (D:ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hd).2
        have hd1 : (1:ℝ) ≤ (d:ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hd).1
        have hbase : (0:ℝ) ≤ (d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ)) := by positivity
        have hle : (d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ)) ≤ (D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ)) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hdD (Real.sqrt_nonneg _)
        have hpow : ((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ)))^j
            ≤ ((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ)))^j :=
          pow_le_pow_left₀ hbase hle j
        have hstep : (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ))
            ≤ (Ct * A * Real.sqrt (x:ℝ) * (((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)) := by
          have h1 : Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j
              ≤ Ct * A * Real.sqrt (x:ℝ) * (((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
        calc (2 * (x:ℝ)^((1:ℝ)/4)) * (d:ℝ) * (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ))
            ≤ (2 * (x:ℝ)^((1:ℝ)/4)) * (D:ℝ) * (Ct * A * Real.sqrt (x:ℝ) * (((d:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left hdD (by positivity)
          _ ≤ (2 * (x:ℝ)^((1:ℝ)/4)) * (D:ℝ) * (Ct * A * Real.sqrt (x:ℝ) * (((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)) := by
              apply mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (2 * (x:ℝ)^((1:ℝ)/4)) * (D:ℝ) * (Ct * A * Real.sqrt (x:ℝ) * (((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)) * (D:ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        have h1 : ((D + 1 - 1 : ℕ) : ℝ) = (D:ℝ) := by norm_num
        rw [h1]; ring
    _ ≤ 4 * Ct * (A + 1) * (x:ℝ)^((1:ℝ)/4) * Real.sqrt (x:ℝ)
            * ((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*y))^j * (K:ℝ) * (D:ℝ)^2 := by
        have hx14 : (1:ℝ) ≤ (x:ℝ)^((1:ℝ)/4) := by
          have := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hx1 (by norm_num : (0:ℝ) ≤ (1:ℝ)/4)
          simpa using this
        have hmid : 2 * (x:ℝ)^((1:ℝ)/4) * (Ct * A) ≤ 4 * Ct * (A + 1) * (x:ℝ)^((1:ℝ)/4) := by
          have hxnn : (0:ℝ) ≤ (x:ℝ)^((1:ℝ)/4) := Real.rpow_nonneg (Nat.cast_nonneg x) _
          have hCA : (0:ℝ) ≤ Ct * A := mul_nonneg hCtpos.le hA.le
          have h1 : (0:ℝ) ≤ (x:ℝ)^((1:ℝ)/4) * (Ct * A) := mul_nonneg hxnn hCA
          have h2 : (0:ℝ) ≤ (x:ℝ)^((1:ℝ)/4) * Ct := mul_nonneg hxnn hCtpos.le
          nlinarith [h1, h2]
        calc 2 * (x:ℝ)^((1:ℝ)/4) * (D:ℝ) * (Ct * A * Real.sqrt (x:ℝ) * (((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ)) * (D:ℝ)
            = (2 * (x:ℝ)^((1:ℝ)/4) * (Ct * A)) * (Real.sqrt (x:ℝ) * (((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ) * (D:ℝ)^2) := by ring
          _ ≤ (4 * Ct * (A + 1) * (x:ℝ)^((1:ℝ)/4)) *
                (Real.sqrt (x:ℝ) * (((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ) * (D:ℝ)^2) :=
              mul_le_mul_of_nonneg_right hmid (by positivity)
          _ = 4 * Ct * (A + 1) * (x:ℝ)^((1:ℝ)/4) * Real.sqrt (x:ℝ)
                * (((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ))))^j * (K:ℝ) * (D:ℝ)^2 := by ring

/-- `Σ_{k ≤ K, u < k} 1/k² ≤ 4/(u+1)` for `u ≥ 0`. -/
lemma sum_Icc_inv_sq_filter_le' (u : ℝ) (hu : 0 ≤ u) (K : ℕ) :
    (∑ k ∈ (Finset.Icc 1 K).filter (fun k : ℕ => u < (k:ℝ)), (1:ℝ)/(k:ℝ)^2) ≤ 4/(u+1) := by
  rcases eq_or_lt_of_le hu with h | h
  · subst h
    have hsub : (Finset.Icc 1 K).filter (fun k : ℕ => (0:ℝ) < (k:ℝ)) = Finset.Icc 1 K := by
      apply Finset.filter_true_of_mem
      intro k hk
      simp only [Finset.mem_Icc] at hk
      exact_mod_cast (by omega : 0 < k)
    rw [hsub]
    have h3 : (∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(k:ℝ)^2) ≤ 2 := by
      have h := sum_Icc_inv_sq_le 1 (le_refl 1) K
      simpa using h
    linarith
  · exact sum_Icc_inv_sq_filter_le u h K

/-- **The `ℓ²` bound** for the weight `ξ(k,l) = k⁻¹ Z(l) f (x u²/k² + l²)` for `u ≥ 0`
(the one-sided support hypothesis suffices for the intended application). -/
lemma l2_weight_bound_nonneg (x K : ℕ) (f : ℝ → ℝ) (u : ℝ) (hx : 1 ≤ x) (hu : 0 ≤ u)
    (hfsup : ∀ v : ℝ, (x : ℝ) ≤ v → f v = 0)
    (hf0 : ∀ v : ℝ, 0 ≤ f v) (hf1 : ∀ v : ℝ, f v ≤ 1) :
    (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
      (1 / (k : ℝ) ^ 2) * (Z l : ℝ) ^ 2
        * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2)
      ≤ 16 * (x : ℝ) ^ ((1 : ℝ) / 4) / (u + 1) := by
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by positivity
  have hinner : ∀ k : ℕ, (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
      (Z l : ℝ) ^ 2 * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2)
        ≤ 4 * (x : ℝ) ^ ((1 : ℝ) / 4) := by
    intro k
    have h1 : (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
        (Z l : ℝ) ^ 2 * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2)
        ≤ ∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
            4 * (if Nat.sqrt l ^ 2 = l then (1:ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro l hl
      have hZ := Z_sq_le_four l
      have hf2 : f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2 ≤ 1 := by
        have h1 := hf0 ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2)
        have h2 := hf1 ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2)
        nlinarith
      have hind : (0:ℝ) ≤ (if Nat.sqrt l ^ 2 = l then (1:ℝ) else 0) := by
        split <;> norm_num
      have hZnn : (0:ℝ) ≤ (Z l : ℝ)^2 := by positivity
      nlinarith [hZ, hf2, hind, hZnn]
    have h2 : (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
        4 * (if Nat.sqrt l ^ 2 = l then (1:ℝ) else 0))
        = 4 * ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) := by
      rw [← Finset.mul_sum, Finset.sum_boole, card_sq_Icc]
    have h3 : ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ≤ (x : ℝ) ^ ((1:ℝ)/4) := by
      have h1 : ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ≤ Real.sqrt (Nat.sqrt x : ℝ) :=
        natSqrt_cast_le_sqrt (Nat.sqrt x)
      have h2 : Real.sqrt (Nat.sqrt x : ℝ) ≤ Real.sqrt (Real.sqrt (x:ℝ)) :=
        Real.sqrt_le_sqrt (natSqrt_cast_le_sqrt x)
      have h3 : Real.sqrt (Real.sqrt (x:ℝ)) = (x:ℝ) ^ ((1:ℝ)/4) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0]
        norm_num
      linarith [h1, h2, h3.le, h3.ge]
    rw [h2] at h1
    linarith [h1, mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 4)]
  have hstep : (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
        (1 / (k : ℝ) ^ 2) * (Z l : ℝ) ^ 2
          * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2)
      = ∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ)^2) * (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
          (Z l : ℝ) ^ 2 * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hstep]
  have hkey : ∀ k ∈ Finset.Icc 1 K,
      (1/(k:ℝ)^2) * (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
          (Z l : ℝ) ^ 2 * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2)
        ≤ (1/(k:ℝ)^2) * (if u < (k:ℝ) then 4 * (x:ℝ)^((1:ℝ)/4) else 0) := by
    intro k hk
    by_cases h : u < (k:ℝ)
    · rw [if_pos h]
      exact mul_le_mul_of_nonneg_left (hinner k) (by positivity)
    · rw [if_neg h]
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have huk : (k:ℝ) ≤ u := le_of_not_gt h
      have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
      have hzero : (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
          (Z l : ℝ) ^ 2 * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro l hl
        have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
        have harg : (x:ℝ) < (x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2 := by
          have hk2 : (0:ℝ) < (k:ℝ)^2 := by positivity
          have h1 : (x:ℝ) ≤ (x:ℝ) * u^2/(k:ℝ)^2 := by
            rw [le_div_iff₀ hk2]
            have hkk : (k:ℝ)^2 ≤ u^2 := by nlinarith [huk, hkpos]
            nlinarith [hx0, hkk]
          have h2 : (1:ℝ) ≤ (l:ℝ)^2 := by
            have : (1:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl1
            nlinarith
          linarith
        rw [show f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2 = 0 by
          rw [hfsup _ (le_of_lt harg)]; norm_num]
        ring
      rw [hzero, mul_zero]
  calc (∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ)^2) * (∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
          (Z l : ℝ) ^ 2 * f ((x : ℝ) * u ^ 2 / (k : ℝ) ^ 2 + (l : ℝ) ^ 2) ^ 2))
      ≤ ∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ)^2) * (if u < (k:ℝ) then 4 * (x:ℝ)^((1:ℝ)/4) else 0) :=
        Finset.sum_le_sum hkey
    _ = 4 * (x:ℝ)^((1:ℝ)/4) * ∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ)^2) * (if u < (k:ℝ) then 1 else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        by_cases h : u < (k:ℝ) <;> simp [h]; ring
    _ ≤ 4 * (x:ℝ)^((1:ℝ)/4) * (4/(u+1)) := by
        have h := sum_Icc_inv_sq_filter_le' u hu K
        rw [Finset.sum_filter] at h
        have hEq : (∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ)^2) * (if u < (k:ℝ) then 1 else 0))
            = ∑ k ∈ Finset.Icc 1 K, (if u < (k:ℝ) then 1/(k:ℝ)^2 else 0) := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hh : u < (k:ℝ) <;> simp [hh]
        have h4 : (0:ℝ) ≤ 4 * (x:ℝ)^((1:ℝ)/4) := by positivity
        calc 4 * (x:ℝ)^((1:ℝ)/4) * (∑ k ∈ Finset.Icc 1 K, (1/(k:ℝ)^2) * (if u < (k:ℝ) then 1 else 0))
            = 4 * (x:ℝ)^((1:ℝ)/4) * (∑ k ∈ Finset.Icc 1 K, (if u < (k:ℝ) then 1/(k:ℝ)^2 else 0)) := by
              rw [hEq]
          _ ≤ 4 * (x:ℝ)^((1:ℝ)/4) * (4/(u+1)) := mul_le_mul_of_nonneg_left h h4
    _ = 16 * (x:ℝ)^((1:ℝ)/4) / (u+1) := by ring

/-- The squared norm of the complex weight `ξ`. -/
lemma xi_normSq (f : ℝ → ℝ) (x : ℕ) (u : ℝ) (k l : ℕ) :
    ‖xi f x u k l‖^2
      = (1/(k:ℝ)^2) * (Z l : ℝ)^2 * f ((x:ℝ)*u^2/(k:ℝ)^2 + (l:ℝ)^2)^2 := by
  rw [xi, Complex.sq_norm, Complex.normSq_ofReal]
  ring

/-- `√(Σ_{k,l} ‖ξ(k,l)‖²) ≤ 4 x^{1/8}/√(u+1)`. -/
lemma xi_sqrt_le (x K : ℕ) (f : ℝ → ℝ) (u : ℝ) (hx : 1 ≤ x) (hu : 0 ≤ u)
    (hsup : ∀ v : ℝ, (x:ℝ) ≤ v → f v = 0)
    (hf0 : ∀ v : ℝ, 0 ≤ f v) (hf1 : ∀ v : ℝ, f v ≤ 1) :
    Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 (Nat.sqrt x), ‖xi f x u k l‖^2)
      ≤ 4 * (x:ℝ)^((1:ℝ)/8) / Real.sqrt (u+1) := by
  have hsum : (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 (Nat.sqrt x), ‖xi f x u k l‖^2)
      = (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
          (1/(k:ℝ)^2) * (Z l : ℝ)^2 * f ((x:ℝ)*u^2/(k:ℝ)^2 + (l:ℝ)^2)^2) := by
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    exact xi_normSq f x u k l
  rw [hsum]
  have hb := l2_weight_bound_nonneg x K f u hx hu hsup hf0 hf1
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by positivity
  have hroot : Real.sqrt ((x:ℝ)^((1:ℝ)/4)) = (x:ℝ)^((1:ℝ)/8) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0]
    norm_num
  have h16s : Real.sqrt ((16:ℝ)) = 4 := by
    rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
  have h16 : Real.sqrt (16 * (x:ℝ)^((1:ℝ)/4)) = 4 * (x:ℝ)^((1:ℝ)/8) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16), h16s, hroot]
  calc Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
        (1/(k:ℝ)^2) * (Z l : ℝ)^2 * f ((x:ℝ)*u^2/(k:ℝ)^2 + (l:ℝ)^2)^2)
      ≤ Real.sqrt (16 * (x:ℝ)^((1:ℝ)/4) / (u+1)) := Real.sqrt_le_sqrt hb
    _ = 4 * (x:ℝ)^((1:ℝ)/8) / Real.sqrt (u+1) := by
        rw [Real.sqrt_div (by positivity), h16]

/-- The large-sieve bound for `Yd` (without unused hypotheses). -/
lemma Yd_sum_le' (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x D' K : ℕ) (f : ℝ → ℝ) (u : ℝ), 1 ≤ x → 1 ≤ D' → 1 ≤ K →
      (∑ d ∈ Finset.Icc 1 D', |Yd f x d K u|)
        ≤ C * ((D':ℝ) + Real.sqrt ((D':ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ)))
            * ((D':ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ))^eps
            * (Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
                ‖xi f x u k l‖^2)) := by
  obtain ⟨C, hC, hbound⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.linear_form_rho_bound_uniform eps heps
  refine ⟨C, hC, ?_⟩
  intro x D' K f u hx hD hK
  have hL : 1 ≤ Nat.sqrt x := Nat.le_sqrt'.mpr (by simpa using hx)
  calc (∑ d ∈ Finset.Icc 1 D', |Yd f x d K u|)
      ≤ ∑ d ∈ Finset.Icc 1 D', ‖∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
          xi f x u k l * ∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => (ν^2+l^2) % d = 0),
            Commons.Analysis.ExponentialSums.ch ((ν:ℝ)*(k:ℝ)/d)‖ := by
        apply Finset.sum_le_sum
        intro d _
        rw [Yd_eq_re f x d K u]
        exact Complex.abs_re_le_norm _
    _ ≤ C * ((D':ℝ) + Real.sqrt ((D':ℝ)*(K:ℝ)*(((Nat.sqrt x : ℕ)):ℝ)))
            * ((D':ℝ)*(K:ℝ)*(((Nat.sqrt x : ℕ)):ℝ))^eps
            * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
                ‖xi f x u k l‖^2) :=
        hbound D' K (Nat.sqrt x) hD hK hL (xi f x u)

/-- **The large-sieve bound in the form used below.** -/
lemma Yd_sum_bound (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x D K : ℕ) (f : ℝ → ℝ) (u : ℝ), 1 ≤ x → 1 ≤ D → 1 ≤ K → 0 ≤ u →
      (∀ v : ℝ, (x:ℝ) ≤ v → f v = 0) →
      (∀ v : ℝ, 0 ≤ f v) → (∀ v : ℝ, f v ≤ 1) →
      (∑ d ∈ Finset.Icc 1 D, |Yd f x d K u|)
        ≤ C * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ)))
            * ((D:ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ))^eps
            * ((x:ℝ)^((1:ℝ)/8) / Real.sqrt (u+1)) := by
  obtain ⟨C1, hC1, h1⟩ := Yd_sum_le' eps heps
  refine ⟨4 * C1, by positivity, ?_⟩
  intro x D K f u hx hD hK hu hsup hf0 hf1
  have h3 := h1 x D K f u hx hD hK
  have h4 := xi_sqrt_le x K f u hx hu hsup hf0 hf1
  have hA : (0:ℝ) ≤ (D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ)) := by positivity
  have hB : (0:ℝ) ≤ ((D:ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ))^eps := by
    apply Real.rpow_nonneg; positivity
  calc (∑ d ∈ Finset.Icc 1 D, |Yd f x d K u|)
      ≤ C1 * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ)))
            * ((D:ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ))^eps
            * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 (Nat.sqrt x),
                ‖xi f x u k l‖^2) := h3
    _ ≤ C1 * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ)))
            * ((D:ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ))^eps
            * (4 * (x:ℝ)^((1:ℝ)/8) / Real.sqrt (u+1)) := by
        apply mul_le_mul_of_nonneg_left h4
        positivity
    _ = (4 * C1) * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ)))
            * ((D:ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ))^eps
            * ((x:ℝ)^((1:ℝ)/8) / Real.sqrt (u+1)) := by ring

/-- `u ↦ Yd f x d K u` is continuous for continuous `f`. -/
lemma continuous_Yd (f : ℝ → ℝ) (hf : Continuous f) (x d K : ℕ) :
    Continuous fun u : ℝ => Yd f x d K u := by
  unfold Yd
  apply continuous_finsetSum
  intro b hb
  apply Continuous.mul continuous_const
  apply continuous_finsetSum
  intro k hk
  have h1 : Continuous fun u : ℝ => (x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2 :=
    ((continuous_const.mul (continuous_id.pow 2)).div_const _).add continuous_const
  have h2 : Continuous fun u : ℝ => f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) := hf.comp h1
  have h3 : Continuous fun u : ℝ => (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k :=
    (continuous_const.mul h2).mul continuous_const
  simpa using h3

/-- `∫₀^K du/√(u+1) ≤ 2√(K+1)`. -/
lemma integral_inv_sqrt_le (K : ℝ) (hK : 0 ≤ K) :
    (∫ u in (0:ℝ)..K, (1:ℝ)/Real.sqrt (u+1)) ≤ 2 * Real.sqrt (K+1) := by
  have hcongr : (∫ u in (0:ℝ)..K, (1:ℝ)/Real.sqrt (u+1))
      = ∫ u in (0:ℝ)..K, (u+1)^(-(1/2:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only []
    rw [Set.uIcc_of_le hK] at hx
    have hx1 : (0:ℝ) < x + 1 := by linarith [hx.1]
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg (le_of_lt hx1) (1/2)]
  rw [hcongr]
  have h1 : (∫ u in (0:ℝ)..K, (u+1)^(-(1/2:ℝ)))
      = ∫ x in (0:ℝ)+1..K+1, x^(-(1/2:ℝ)) := by
    rw [intervalIntegral.integral_comp_add_right (fun x : ℝ => x^(-(1/2:ℝ))) 1]
  rw [h1]
  have h2 : (∫ x in (0:ℝ)+1..K+1, x^(-(1/2:ℝ)))
      = 2 * (Real.sqrt (K+1) - 1) := by
    rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2)))]
    norm_num [Real.sqrt_eq_rpow]
    ring
  rw [h2]
  have h3 : Real.sqrt (K+1) - 1 ≤ Real.sqrt (K+1) := by linarith [Real.sqrt_nonneg (K+1)]
  linarith

/-- The integral of the large-sieve bound for `Yd`. -/
lemma integral_Yd_sum_bound (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x D K : ℕ) (f : ℝ → ℝ), 1 ≤ x → 1 ≤ D → 1 ≤ K →
      Continuous f → (∀ v : ℝ, (x:ℝ) ≤ v → f v = 0) →
      (∀ v : ℝ, 0 ≤ f v) → (∀ v : ℝ, f v ≤ 1) →
      (∫ u in (0:ℝ)..(K:ℝ), (∑ d ∈ Finset.Icc 1 D, |Yd f x d K u|))
        ≤ C * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ)))
            * ((D:ℝ)*(K:ℝ)*((Nat.sqrt x : ℕ):ℝ))^eps
            * (x:ℝ)^((1:ℝ)/8) * Real.sqrt ((K:ℝ) + 1) := by
  obtain ⟨C1, hC1, h1⟩ := Yd_sum_bound eps heps
  refine ⟨2 * C1, by positivity, ?_⟩
  intro x D K f hx hD hK hf hsup hf0 hf1
  have hK0 : (0:ℝ) ≤ (K:ℝ) := by positivity
  set L : ℝ := ((Nat.sqrt x : ℕ) : ℝ) with hL
  set A2 : ℝ := C1 * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*L)) * ((D:ℝ)*(K:ℝ)*L)^eps with hA2
  have hA2nn : 0 ≤ A2 := by
    rw [hA2]
    have h1 : (0:ℝ) ≤ Real.sqrt ((D:ℝ)*(K:ℝ)*L) := Real.sqrt_nonneg _
    have h2 : (0:ℝ) ≤ ((D:ℝ)*(K:ℝ)*L)^eps := Real.rpow_nonneg (by positivity) _
    positivity
  have hx18nn : (0:ℝ) ≤ (x:ℝ)^((1:ℝ)/8) := Real.rpow_nonneg (by positivity) _
  have hpt : ∀ u ∈ Set.Icc (0:ℝ) (K:ℝ),
      (∑ d ∈ Finset.Icc 1 D, |Yd f x d K u|)
        ≤ A2 * ((x:ℝ)^((1:ℝ)/8) * ((1:ℝ)/Real.sqrt (u+1))) := by
    intro u hu
    have h2 := h1 x D K f u hx hD hK hu.1 hsup hf0 hf1
    have h3 : C1 * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*L)) * ((D:ℝ)*(K:ℝ)*L)^eps
        * ((x:ℝ)^((1:ℝ)/8) / Real.sqrt (u+1))
        = A2 * ((x:ℝ)^((1:ℝ)/8) * ((1:ℝ)/Real.sqrt (u+1))) := by
      rw [hA2, hL]; ring
    linarith [h2, h3.le, h3.ge]
  have hcont_sum : Continuous fun u : ℝ => ∑ d ∈ Finset.Icc 1 D, |Yd f x d K u| := by
    apply continuous_finsetSum
    intro d _
    exact (continuous_Yd f hf x d K).abs
  have hint1 : IntervalIntegrable (fun u : ℝ => ∑ d ∈ Finset.Icc 1 D, |Yd f x d K u|)
      volume 0 K := hcont_sum.intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun u : ℝ => A2 * ((x:ℝ)^((1:ℝ)/8) * ((1:ℝ)/Real.sqrt (u+1)))) volume 0 K := by
    have hcont : ContinuousOn (fun xx : ℝ => (1:ℝ)/Real.sqrt (xx+1)) (Set.uIcc 0 (K:ℝ)) := by
      rw [Set.uIcc_of_le hK0]
      apply ContinuousOn.div continuousOn_const
      · apply ContinuousOn.sqrt
        exact continuousOn_id.add continuousOn_const
      · intro xx hxx
        have : (0:ℝ) < xx + 1 := by linarith [hxx.1]
        exact ne_of_gt (Real.sqrt_pos.mpr this)
    apply IntervalIntegrable.const_mul (c := A2)
    apply IntervalIntegrable.const_mul (c := (x:ℝ)^((1:ℝ)/8))
    exact hcont.intervalIntegrable (μ := volume)
  have hswap : (∑ d ∈ Finset.Icc 1 D, ∫ u in (0:ℝ)..(K:ℝ), |Yd f x d K u|)
      = ∫ u in (0:ℝ)..(K:ℝ), ∑ d ∈ Finset.Icc 1 D, |Yd f x d K u| := by
    rw [intervalIntegral.integral_finsetSum]
    intro d _
    exact ((continuous_Yd f hf x d K).abs).intervalIntegrable _ _
  rw [← hswap]
  have hstep : (∫ u in (0:ℝ)..(K:ℝ), A2 * ((x:ℝ)^((1:ℝ)/8) * ((1:ℝ)/Real.sqrt (u+1))))
      ≤ A2 * ((x:ℝ)^((1:ℝ)/8) * (2 * Real.sqrt ((K:ℝ)+1))) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (integral_inv_sqrt_le (K:ℝ) hK0) hx18nn) hA2nn
  calc (∑ d ∈ Finset.Icc 1 D, ∫ u in (0:ℝ)..(K:ℝ), |Yd f x d K u|)
      = ∫ u in (0:ℝ)..(K:ℝ), ∑ d ∈ Finset.Icc 1 D, |Yd f x d K u| := hswap
    _ ≤ ∫ u in (0:ℝ)..(K:ℝ),
          A2 * ((x:ℝ)^((1:ℝ)/8) * ((1:ℝ)/Real.sqrt (u+1))) :=
        intervalIntegral.integral_mono_on hK0 hint1 hint2 hpt
    _ ≤ A2 * ((x:ℝ)^((1:ℝ)/8) * (2 * Real.sqrt ((K:ℝ)+1))) := hstep
    _ = 2 * C1 * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*L)) * ((D:ℝ)*(K:ℝ)*L)^eps
          * (x:ℝ)^((1:ℝ)/8) * Real.sqrt ((K:ℝ) + 1) := by
        rw [hA2, hL]; ring

/-! ### The truncation of the `k`-sum and the three-term decomposition -/

/-- Summability of the positive-frequency part of `k ↦ Icos f d b k * ρ(k,b;d)`. -/
lemma summable_pos_Icos_rhoRe (f : ℝ → ℝ) (d b : ℕ) (hd : 0 < d) (hf : ContDiff ℝ 2 f)
    (hcs : HasCompactSupport fun t : ℝ => f (t ^ 2 + (b : ℝ) ^ 2)) :
    Summable fun k : ℤ => (if 0 < k then Icos f d b k * rhoRe d b k else 0) := by
  have hIcosabs : Summable fun k : ℤ => |Icos f d b k| := (summable_Icos f d b hd hf hcs).norm
  refine Summable.of_norm_bounded (hIcosabs.mul_right (d:ℝ)) (fun k => ?_)
  rw [Real.norm_eq_abs]
  by_cases h : 0 < k
  · rw [if_pos h, abs_mul]
    calc |Icos f d b k| * |rhoRe d b k| ≤ |Icos f d b k| * (d:ℝ) :=
          mul_le_mul_of_nonneg_left (abs_rhoRe_le d b k) (abs_nonneg _)
      _ = |Icos f d b k| * (d:ℝ) := rfl
  · rw [if_neg h, abs_zero]; positivity

/-- The decomposition of the smoothed difference into the `b = 0` part, the truncated
positive-frequency part (`k ≤ K`) and the tail (`k > K`). -/
lemma AdF_sub_MdF_decomp_trunc (f : ℝ → ℝ) (d x K : ℕ) (hd : 0 < d) (hx : 1 ≤ x)
    (hf : ContDiff ℝ 2 f) (hsupp : ∀ u, (x:ℝ) ≤ u → f u = 0) :
    AdF (fun n : ℕ => f n) d x - MdF f d x
      = (ASum f d 0 - (2/(d:ℝ))*(rho 0 d : ℝ)*I0 f 0)
        + (4/(d:ℝ)) * ((∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
              ∑ k ∈ Finset.Icc 1 K, Icos f d b k * rhoRe d b k)
            + (∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
              ∑' k : ℤ, (if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0))) := by
  rw [AdF_sub_MdF_decomp f d x hd hx hf hsupp]
  congr 1
  have hsplit : ∀ b : ℕ, (∑' k : ℤ, (if 0 < k then Icos f d b k * rhoRe d b k else 0))
      = (∑ k ∈ Finset.Icc 1 K, Icos f d b k * rhoRe d b k)
        + (∑' k : ℤ, (if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0)) := by
    intro b
    exact tsum_pos_split (fun k : ℤ => Icos f d b k * rhoRe d b k) K
      (summable_pos_Icos_rhoRe f d b hd hf (hasCompactSupport_quad' f (b:ℝ) (x:ℝ) hsupp))
  simp only [hsplit, mul_add]
  rw [Finset.sum_add_distrib, mul_add]

/-- **The truncated positive-frequency sum is bounded by the integral of `|Y|`.** -/
lemma Psi_abs_le_integral (f : ℝ → ℝ) (d x K : ℕ) (hd : 1 ≤ d) (hx : 1 ≤ x) (hK : 1 ≤ K)
    (hf : ContDiff ℝ 2 f) (hfsup : ∀ u, (x:ℝ) ≤ u → f u = 0) :
    |∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
        ∑ k ∈ Finset.Icc 1 K, Icos f d b k * rhoRe d b k|
      ≤ Real.sqrt (x:ℝ) * ∫ u in (0:ℝ)..(K:ℝ), |Yd f x d K u| := by
  have hK0 : (0:ℝ) ≤ (K:ℝ) := by positivity
  have h1 := Psi_eq_integral f d x K hd hx hK hf hfsup
  have hcontY : Continuous fun u : ℝ => Yd f x d K u := continuous_Yd f hf.continuous x d K
  have hcoscont : Continuous fun u : ℝ =>
      Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) := by
    apply Real.continuous_cos.comp
    apply Continuous.div_const
    exact continuous_const.mul continuous_id
  have hIntEq : (∫ u in (0:ℝ)..(K:ℝ),
        Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) *
          ∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
            ∑ k ∈ Finset.Icc 1 K,
              (1/(k:ℝ)) * f ((x:ℝ)*u^2/(k:ℝ)^2 + (b:ℝ)^2) * rhoRe d b k)
      = ∫ u in (0:ℝ)..(K:ℝ),
        Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) * Yd f x d K u := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only []
    rfl
  rw [h1, hIntEq]
  have h2 : |∫ u in (0:ℝ)..(K:ℝ),
        Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) * Yd f x d K u|
      ≤ ∫ u in (0:ℝ)..(K:ℝ),
        |Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) * Yd f x d K u| :=
    intervalIntegral.abs_integral_le_integral_abs hK0
  have h3 : (∫ u in (0:ℝ)..(K:ℝ),
        |Real.cos (2 * Real.pi * Real.sqrt (x:ℝ) * u / (d:ℝ)) * Yd f x d K u|)
      ≤ ∫ u in (0:ℝ)..(K:ℝ), |Yd f x d K u| := by
    apply intervalIntegral.integral_mono_on hK0
    · exact (hcoscont.mul hcontY).abs.intervalIntegrable _ _
    · exact hcontY.abs.intervalIntegrable _ _
    · intro u _
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  linarith

/-! ### The weighted smoothed remainder estimate -/

/-- The number of derivatives used: `⌈2/ε⌉₊ + 2`. -/
noncomputable def Jeps (eps : ℝ) : ℕ := ⌈(2:ℝ)/eps⌉₊ + 2

lemma Jeps_ge_two (eps : ℝ) : 2 ≤ Jeps eps := by
  unfold Jeps; omega

lemma Jeps_mul_ge (eps : ℝ) (heps : 0 < eps) : 2 ≤ (Jeps eps : ℝ) * eps := by
  have h1 : (2:ℝ)/eps ≤ ((⌈(2:ℝ)/eps⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ((⌈(2:ℝ)/eps⌉₊ : ℕ) : ℝ) ≤ (Jeps eps : ℝ) := by
    unfold Jeps; push_cast; linarith
  rw [div_le_iff₀ heps] at h1
  have h3 : ((⌈(2:ℝ)/eps⌉₊ : ℕ) : ℝ) * eps ≤ (Jeps eps : ℝ) * eps :=
    mul_le_mul_of_nonneg_right h2 heps.le
  linarith

lemma sqrt_four : Real.sqrt (4:ℝ) = 2 := by
  rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

lemma sqrt_sixteen : Real.sqrt (16:ℝ) = 4 := by
  rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]

/-- **The `d`-weighted smoothed remainder estimate.** -/
theorem weighted_remainder_le (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (x y D : ℕ) (A : ℝ),
      1 ≤ x → 1 ≤ y → y ≤ x → 0 < A → 1 ≤ D →
      (D:ℝ) ≤ (x:ℝ)^((3:ℝ)/4) →
      1 ≤ (D:ℝ) * (y:ℝ)⁻¹ * (x:ℝ)^((1:ℝ)/2 + (Jeps eps : ℝ)⁻¹) →
      ContDiff ℝ (Jeps eps) f → (∀ u : ℝ, (x:ℝ) ≤ u → f u = 0) →
      (∀ u : ℝ, 0 ≤ f u) → (∀ u : ℝ, f u ≤ 1) →
      (∀ i ≤ Jeps eps, ∀ u ∈ Set.Icc 0 (x:ℝ),
        |iteratedDeriv i f u| ≤ A * (((y:ℝ)^i)⁻¹)) →
      (∑ d ∈ Finset.Icc 1 D, (d:ℝ) * |AdF (fun n : ℕ => f n) d x - MdF f d x|)
        ≤ C * (A + 1) * (D:ℝ)^((3:ℝ)/2) * ((y:ℝ)⁻¹) * (x:ℝ)^((11:ℝ)/8 + eps) := by
  obtain ⟨C1, hC1, hLS⟩ := integral_Yd_sum_bound (eps/8) (by linarith)
  obtain ⟨C3, hC3, htail⟩ := tsum_tail_Icos_tail_le (Jeps eps) (Jeps_ge_two eps)
  refine ⟨20 + 200 * C1 + 200 * C3 + 200 * C3, by positivity, ?_⟩
  intro f x y D A hx hy hyx hA hD hD34 hA0le hf hfsup hf0 hf1 hfd
  have hJ2 : 2 ≤ Jeps eps := Jeps_ge_two eps
  have hJeps_ge : 2 ≤ (Jeps eps : ℝ) * eps := Jeps_mul_ge eps heps
  have hJpos : (0:ℝ) < (Jeps eps : ℝ) := by
    have := Jeps_ge_two eps
    exact_mod_cast (by omega : 0 < Jeps eps)
  have hJne : (Jeps eps : ℝ) ≠ 0 := ne_of_gt hJpos
  have hδle : (Jeps eps : ℝ)⁻¹ ≤ eps/2 := by
    rw [inv_le_iff_one_le_mul₀ hJpos]
    nlinarith [hJeps_ge]
  have hδle_eps : (Jeps eps : ℝ)⁻¹ ≤ eps := by linarith
  have hJδ : (Jeps eps : ℝ) * (Jeps eps : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hJne
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hx0 : (0:ℝ) < (x:ℝ) := by linarith
  have hy1 : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy
  have hy0 : (0:ℝ) < (y:ℝ) := by linarith
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hyx1 : (y:ℝ) ≤ (x:ℝ) := by exact_mod_cast hyx
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by exact_mod_cast hJ2)
  have hf1c : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast (by omega : (1:ℕ) ≤ Jeps eps))
  have hfcont : Continuous f := hf.continuous
  set δ : ℝ := (Jeps eps : ℝ)⁻¹ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδle' : δ ≤ eps/2 := hδle
  set A0 : ℝ := (D:ℝ)*(y:ℝ)⁻¹*(x:ℝ)^((1:ℝ)/2+δ) with hA0def
  have hA0pos : 0 < A0 := lt_of_lt_of_le zero_lt_one hA0le
  set K : ℕ := ⌊A0⌋₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; omega
  have hKge : A0 ≤ (K:ℝ) := by
    rw [hKdef]
    push_cast
    exact le_of_lt (Nat.lt_floor_add_one A0)
  have hKle : (K:ℝ) ≤ 2*A0 := by
    rw [hKdef]
    push_cast
    have h := Nat.floor_le (le_of_lt hA0pos)
    linarith
  set L : ℝ := ((Nat.sqrt x : ℕ) : ℝ) with hLdef
  have hLle : L ≤ (x:ℝ)^((1:ℝ)/2) := by
    rw [hLdef, ← Real.sqrt_eq_rpow]
    exact natSqrt_cast_le_sqrt x
  have hLnn : 0 ≤ L := by rw [hLdef]; positivity
  set Phi : ℕ → ℝ := fun d => ∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
      ∑ k ∈ Finset.Icc 1 K, Icos f d b k * rhoRe d b k with hPhidef
  set Tail : ℕ → ℝ := fun d => ∑ b ∈ Finset.Icc 1 (Nat.sqrt x), (Z b : ℝ) *
      ∑' k : ℤ, (if (K:ℤ) < k then Icos f d b k * rhoRe d b k else 0) with hTaildef
  set R1 : ℕ → ℝ := fun d => ASum f d 0 - (2/(d:ℝ))*(rho 0 d : ℝ)*I0 f 0 with hR1def
  -- the per-modulus decomposition
  have hdecomp : ∀ d ∈ Finset.Icc 1 D,
      AdF (fun n : ℕ => f n) d x - MdF f d x = R1 d + (4/(d:ℝ))*(Phi d + Tail d) := by
    intro d hd
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    rw [hR1def, hPhidef, hTaildef]
    exact AdF_sub_MdF_decomp_trunc f d x K hd0 hx hf2 hfsup
  have hbound_d : ∀ d ∈ Finset.Icc 1 D,
      (d:ℝ) * |AdF (fun n : ℕ => f n) d x - MdF f d x|
        ≤ (d:ℝ)*|R1 d| + 4*|Phi d| + 4*|Tail d| := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
    have hdne : (d:ℝ) ≠ 0 := ne_of_gt hdR
    rw [hdecomp d hd]
    have h4 : (d:ℝ) * (4/(d:ℝ)) = 4 := by field_simp
    calc (d:ℝ) * |R1 d + 4/(d:ℝ)*(Phi d + Tail d)|
        ≤ (d:ℝ) * (|R1 d| + |4/(d:ℝ)*(Phi d + Tail d)|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (le_of_lt hdR)
      _ = (d:ℝ)*|R1 d| + (d:ℝ)*|4/(d:ℝ)*(Phi d + Tail d)| := by ring
      _ = (d:ℝ)*|R1 d| + 4*|Phi d + Tail d| := by
          have h4b : (d:ℝ)*|4/(d:ℝ)*(Phi d + Tail d)| = 4*|Phi d + Tail d| := by
            rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 4/(d:ℝ) by positivity)]
            field_simp
          rw [h4b]
      _ ≤ (d:ℝ)*|R1 d| + 4*(|Phi d| + |Tail d|) := by
          have h := abs_add_le (Phi d) (Tail d)
          linarith
      _ = (d:ℝ)*|R1 d| + 4*|Phi d| + 4*|Tail d| := by ring
  have hsum : (∑ d ∈ Finset.Icc 1 D, (d:ℝ) * |AdF (fun n : ℕ => f n) d x - MdF f d x|)
      ≤ (∑ d ∈ Finset.Icc 1 D, (d:ℝ)*|R1 d|)
        + 4*(∑ d ∈ Finset.Icc 1 D, |Phi d|) + 4*(∑ d ∈ Finset.Icc 1 D, |Tail d|) := by
    calc (∑ d ∈ Finset.Icc 1 D, (d:ℝ) * |AdF (fun n : ℕ => f n) d x - MdF f d x|)
        ≤ ∑ d ∈ Finset.Icc 1 D, ((d:ℝ)*|R1 d| + 4*|Phi d| + 4*|Tail d|) :=
          Finset.sum_le_sum hbound_d
      _ = (∑ d ∈ Finset.Icc 1 D, (d:ℝ)*|R1 d|)
            + 4*(∑ d ∈ Finset.Icc 1 D, |Phi d|) + 4*(∑ d ∈ Finset.Icc 1 D, |Tail d|) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  -- elementary bounds on powers of `D`
  have hDhalf : (D:ℝ)^((1:ℝ)/2) ≤ (x:ℝ)^((3:ℝ)/8) := by
    have h1 : (D:ℝ)^((1:ℝ)/2) ≤ ((x:ℝ)^((3:ℝ)/4))^((1:ℝ)/2) :=
      Real.rpow_le_rpow (by positivity) hD34 (by norm_num)
    have h2 : ((x:ℝ)^((3:ℝ)/4))^((1:ℝ)/2) = (x:ℝ)^((3:ℝ)/8) := by
      rw [← Real.rpow_mul (x := (x:ℝ)) (by positivity)]
      norm_num
    linarith [h1, h2.le, h2.ge]
  have hD32 : (D:ℝ)^((3:ℝ)/2) ≤ (x:ℝ)^((9:ℝ)/8) := by
    have h1 : (D:ℝ)^((3:ℝ)/2) ≤ ((x:ℝ)^((3:ℝ)/4))^((3:ℝ)/2) :=
      Real.rpow_le_rpow (by positivity) hD34 (by norm_num)
    have h2 : ((x:ℝ)^((3:ℝ)/4))^((3:ℝ)/2) = (x:ℝ)^((9:ℝ)/8) := by
      rw [← Real.rpow_mul (x := (x:ℝ)) (by positivity)]
      norm_num
    linarith [h1, h2.le, h2.ge]
  have hDsq : (D:ℝ)^2 = (D:ℝ)^((3:ℝ)/2)*(D:ℝ)^((1:ℝ)/2) := by
    rw [← Real.rpow_add (by positivity : (0:ℝ) < (D:ℝ))]
    norm_num
  have hD3 : (D:ℝ)^3 = (D:ℝ)^((3:ℝ)/2)*(D:ℝ)^((3:ℝ)/2) := by
    rw [← Real.rpow_add (by positivity : (0:ℝ) < (D:ℝ))]
    norm_num
  -- the elementary `b = 0` part
  have hR1sum : (∑ d ∈ Finset.Icc 1 D, (d:ℝ)*|R1 d|)
      ≤ 8*(A+1)*(D:ℝ)^((3:ℝ)/2)*((y:ℝ)⁻¹)*(x:ℝ)^((11:ℝ)/8+eps) := by
    have hpt : ∀ d ∈ Finset.Icc 1 D, (d:ℝ)*|R1 d| ≤ (d:ℝ)*((8*A+5)*(x:ℝ)*(y:ℝ)⁻¹) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hb : |R1 d| ≤ (8*A+5)*(x:ℝ)/y := by
        rw [hR1def]
        apply ASum_zero_sub_MdF_zero_le f d x A (y:ℝ) hd1 hx hy1 hyx1 hA hf1c
        · intro u; exact ⟨hf0 u, hf1 u⟩
        · exact hfsup
        · intro u hu
          have h := hfd 1 (by omega : 1 ≤ Jeps eps) u hu
          simpa [div_eq_mul_inv] using h
      have hb' : (8*A+5)*(x:ℝ)/y = (8*A+5)*(x:ℝ)*(y:ℝ)⁻¹ := by ring
      calc (d:ℝ)*|R1 d| ≤ (d:ℝ)*((8*A+5)*(x:ℝ)/y) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = (d:ℝ)*((8*A+5)*(x:ℝ)*(y:ℝ)⁻¹) := by rw [hb']
    have hdy : (0:ℝ) ≤ (8*A+5)*(x:ℝ)*(y:ℝ)⁻¹ := by positivity
    have hcard : (∑ d ∈ Finset.Icc 1 D, (d:ℝ)) ≤ (D:ℝ)^2 := by
      calc (∑ d ∈ Finset.Icc 1 D, (d:ℝ)) ≤ ∑ d ∈ Finset.Icc 1 D, (D:ℝ) :=
            Finset.sum_le_sum (fun d hd => by
              exact_mod_cast (Finset.mem_Icc.mp hd).2)
        _ = (D:ℝ) * (D:ℝ) := by rw [Finset.sum_const, Nat.card_Icc]; simp [nsmul_eq_mul]
        _ = (D:ℝ)^2 := by ring
    calc (∑ d ∈ Finset.Icc 1 D, (d:ℝ)*|R1 d|)
        ≤ ∑ d ∈ Finset.Icc 1 D, (d:ℝ)*((8*A+5)*(x:ℝ)*(y:ℝ)⁻¹) := Finset.sum_le_sum hpt
      _ = (∑ d ∈ Finset.Icc 1 D, (d:ℝ)) * ((8*A+5)*(x:ℝ)*(y:ℝ)⁻¹) := by rw [Finset.sum_mul]
      _ ≤ (D:ℝ)^2 * ((8*A+5)*(x:ℝ)*(y:ℝ)⁻¹) := mul_le_mul_of_nonneg_right hcard hdy
      _ ≤ 8*(A+1)*(D:ℝ)^((3:ℝ)/2)*((y:ℝ)⁻¹)*(x:ℝ)^((11:ℝ)/8+eps) := by
          have hxpow : (x:ℝ)*((D:ℝ)^((1:ℝ)/2)) ≤ (x:ℝ)^((11:ℝ)/8+eps) := by
            have h1 : (x:ℝ)*((D:ℝ)^((1:ℝ)/2)) ≤ (x:ℝ)*((x:ℝ)^((3:ℝ)/8)) :=
              mul_le_mul_of_nonneg_left hDhalf (by positivity)
            have h2 : (x:ℝ)*((x:ℝ)^((3:ℝ)/8)) = (x:ℝ)^((11:ℝ)/8) := by
              have h3 : (x:ℝ)^((11:ℝ)/8) = (x:ℝ)^((1:ℝ)+(3:ℝ)/8) := by norm_num
              rw [h3, Real.rpow_add hx0, Real.rpow_one]
            have h3 : (x:ℝ)^((11:ℝ)/8) ≤ (x:ℝ)^((11:ℝ)/8+eps) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
            linarith
          have hkey : (D:ℝ)^2 * ((8*A+5)*(x:ℝ)*(y:ℝ)⁻¹)
              = ((D:ℝ)^((3:ℝ)/2) * ((x:ℝ)*((D:ℝ)^((1:ℝ)/2)))) * ((8*A+5)*(y:ℝ)⁻¹) := by
            rw [hDsq]; ring
          rw [hkey]
          have hstep : ((D:ℝ)^((3:ℝ)/2) * ((x:ℝ)*((D:ℝ)^((1:ℝ)/2)))) * ((8*A+5)*(y:ℝ)⁻¹)
              ≤ ((D:ℝ)^((3:ℝ)/2) * (x:ℝ)^((11:ℝ)/8+eps)) * (8*(A+1)*(y:ℝ)⁻¹) := by
            have hleft : (D:ℝ)^((3:ℝ)/2) * ((x:ℝ)*((D:ℝ)^((1:ℝ)/2)))
                ≤ (D:ℝ)^((3:ℝ)/2) * (x:ℝ)^((11:ℝ)/8+eps) :=
              mul_le_mul_of_nonneg_left hxpow (by positivity)
            have hright : (8*A+5)*(y:ℝ)⁻¹ ≤ 8*(A+1)*(y:ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_right (by linarith : (8:ℝ)*A+5 ≤ 8*(A+1)) (by positivity)
            exact mul_le_mul hleft hright (by positivity) (by positivity)
          calc ((D:ℝ)^((3:ℝ)/2) * ((x:ℝ)*((D:ℝ)^((1:ℝ)/2)))) * ((8*A+5)*(y:ℝ)⁻¹)
              ≤ ((D:ℝ)^((3:ℝ)/2) * (x:ℝ)^((11:ℝ)/8+eps)) * (8*(A+1)*(y:ℝ)⁻¹) := hstep
            _ = 8*(A+1)*(D:ℝ)^((3:ℝ)/2)*((y:ℝ)⁻¹)*(x:ℝ)^((11:ℝ)/8+eps) := by ring

  -- the tail part
  have hTailsum : (∑ d ∈ Finset.Icc 1 D, |Tail d|)
      ≤ 4*C3*(A+1)*(D:ℝ)^((3:ℝ)/2)*((y:ℝ)⁻¹)*(x:ℝ)^((11:ℝ)/8+eps) := by
    have h1 := htail f x y A D K hx hy hyx hA hD hK1 hf hfsup hfd
    have hKy : (D:ℝ)*(x:ℝ)^((1:ℝ)/2+δ) ≤ (K:ℝ)*(y:ℝ) := by
      have h := mul_le_mul_of_nonneg_right hKge (le_of_lt hy0)
      have h2 : A0 * (y:ℝ) = (D:ℝ)*(x:ℝ)^((1:ℝ)/2+δ) := by
        rw [hA0def]; field_simp
      linarith [h, h2.le, h2.ge]
    have hsplitx : (x:ℝ)^((1:ℝ)/2+δ) * (x:ℝ)^(-δ) = (x:ℝ)^((1:ℝ)/2) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have hbase : (D:ℝ)*(x:ℝ)^((1:ℝ)/2)/((K:ℝ)*(y:ℝ)) ≤ (x:ℝ)^(-δ) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (K:ℝ)*(y:ℝ))]
      calc (D:ℝ)*(x:ℝ)^((1:ℝ)/2)
          = (x:ℝ)^(-δ) * ((D:ℝ)*(x:ℝ)^((1:ℝ)/2+δ)) := by rw [← hsplitx]; ring
        _ ≤ (x:ℝ)^(-δ) * ((K:ℝ)*(y:ℝ)) :=
            mul_le_mul_of_nonneg_left hKy (Real.rpow_nonneg (by positivity) _)
    have hpow : ((D:ℝ)*(x:ℝ)^((1:ℝ)/2)/((K:ℝ)*(y:ℝ)))^(Jeps eps) ≤ (x:ℝ)^(-1:ℝ) := by
      rw [← Real.rpow_natCast]
      have h2 : ((D:ℝ)*(x:ℝ)^((1:ℝ)/2)/((K:ℝ)*(y:ℝ)))^((Jeps eps : ℕ) : ℝ)
          ≤ ((x:ℝ)^(-δ))^((Jeps eps : ℕ) : ℝ) :=
        Real.rpow_le_rpow (by positivity) hbase (by positivity)
      have h3 : ((x:ℝ)^(-δ))^((Jeps eps : ℕ) : ℝ) = (x:ℝ)^(-1:ℝ) := by
        rw [← Real.rpow_mul (x := (x:ℝ)) (by positivity)]
        congr 1
        rw [hδdef]
        field_simp
      linarith [h2, h3.le, h3.ge]
    have hKleA0 : (K:ℝ) ≤ 2*A0 := hKle
    have hmain : (x:ℝ)^((1:ℝ)/4)*Real.sqrt (x:ℝ)
          *(((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ)))^(Jeps eps))*(K:ℝ)*(D:ℝ)^2
        ≤ 2*(D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps) := by
      rw [Real.sqrt_eq_rpow]
      have hcomb : (x:ℝ)^((1:ℝ)/4)*(x:ℝ)^((1:ℝ)/2)*(x:ℝ)^(-1:ℝ)
            * (x:ℝ)^((1:ℝ)/2+δ)
          = (x:ℝ)^((1:ℝ)/4+δ) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
        congr 1
        ring
      calc (x:ℝ)^((1:ℝ)/4)*(x:ℝ)^((1:ℝ)/2)
            *(((D:ℝ)*(x:ℝ)^((1:ℝ)/2)/((K:ℝ)*(y:ℝ)))^(Jeps eps))*(K:ℝ)*(D:ℝ)^2
          ≤ (x:ℝ)^((1:ℝ)/4)*(x:ℝ)^((1:ℝ)/2)*(x:ℝ)^(-1:ℝ)*(2*A0)*(D:ℝ)^2 := by
            gcongr
        _ = 2*((D:ℝ)^3*(y:ℝ)⁻¹*((x:ℝ)^((1:ℝ)/4)*(x:ℝ)^((1:ℝ)/2)*(x:ℝ)^(-1:ℝ)
              * (x:ℝ)^((1:ℝ)/2+δ))) := by
            rw [hA0def]; ring
        _ = 2*((D:ℝ)^3*(y:ℝ)⁻¹*((x:ℝ)^((1:ℝ)/4+δ))) := by rw [hcomb]
        _ ≤ 2*((D:ℝ)^((3:ℝ)/2)*(x:ℝ)^((9:ℝ)/8)*(y:ℝ)⁻¹*((x:ℝ)^((1:ℝ)/4+δ))) := by
            gcongr
            calc (D:ℝ)^3 = (D:ℝ)^((3:ℝ)/2)*(D:ℝ)^((3:ℝ)/2) := hD3
              _ ≤ (D:ℝ)^((3:ℝ)/2)*(x:ℝ)^((9:ℝ)/8) :=
                  mul_le_mul_of_nonneg_left hD32 (by positivity)
        _ ≤ 2*(D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps) := by
            have hxe : (x:ℝ)^((9:ℝ)/8) * (x:ℝ)^((1:ℝ)/4+δ) ≤ (x:ℝ)^((11:ℝ)/8+eps) := by
              rw [← Real.rpow_add hx0]
              apply Real.rpow_le_rpow_of_exponent_le hx1
              linarith
            calc 2*((D:ℝ)^((3:ℝ)/2)*(x:ℝ)^((9:ℝ)/8)*(y:ℝ)⁻¹*((x:ℝ)^((1:ℝ)/4+δ)))
                = 2*((D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*((x:ℝ)^((9:ℝ)/8) * (x:ℝ)^((1:ℝ)/4+δ))) := by ring
              _ ≤ 2*((D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps)) := by
                  gcongr
              _ = 2*(D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps) := by ring
    calc (∑ d ∈ Finset.Icc 1 D, |Tail d|)
        ≤ C3*(A+1)*(x:ℝ)^((1:ℝ)/4)*Real.sqrt (x:ℝ)
            *(((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ)))^(Jeps eps))*(K:ℝ)*(D:ℝ)^2 := h1
      _ = C3*(A+1)*((x:ℝ)^((1:ℝ)/4)*Real.sqrt (x:ℝ)
            *(((D:ℝ)*Real.sqrt (x:ℝ)/((K:ℝ)*(y:ℝ)))^(Jeps eps))*(K:ℝ)*(D:ℝ)^2) := by ring
      _ ≤ C3*(A+1)*(2*(D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps)) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = 2*C3*(A+1)*(D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps) := by ring
      _ ≤ 4*C3*(A+1)*(D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps) := by
          gcongr
          linarith [hC3.le]

  -- the truncated positive-frequency part
  have hPhisum : (∑ d ∈ Finset.Icc 1 D, |Phi d|)
      ≤ 32*C1*(D:ℝ)^((3:ℝ)/2)*((y:ℝ)⁻¹)*(x:ℝ)^((11:ℝ)/8+eps) := by
    have hper : ∀ d ∈ Finset.Icc 1 D,
        |Phi d| ≤ Real.sqrt (x:ℝ) * ∫ u in (0:ℝ)..(K:ℝ), |Yd f x d K u| := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      rw [hPhidef]
      exact Psi_abs_le_integral f d x K hd1 hx hK1 hf2 hfsup
    have hswap : (∑ d ∈ Finset.Icc 1 D, ∫ u in (0:ℝ)..(K:ℝ), |Yd f x d K u|)
        = ∫ u in (0:ℝ)..(K:ℝ), ∑ d ∈ Finset.Icc 1 D, |Yd f x d K u| := by
      rw [intervalIntegral.integral_finsetSum]
      intro d _
      exact ((continuous_Yd f hfcont x d K).abs).intervalIntegrable _ _
    have hint := hLS x D K f hx hD hK1 hfcont hfsup hf0 hf1
    -- auxiliary equalities for the exponent manipulations
    have hD1' : (D:ℝ) = (D:ℝ)^(1:ℝ) := (Real.rpow_one (D:ℝ)).symm
    have hxadd1 : (x:ℝ)^((1:ℝ)/2+δ)*((x:ℝ)^((1:ℝ)/2)) = (x:ℝ)^(1+δ) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have hDcomb : (D:ℝ)*(D:ℝ)^((1:ℝ)/2) = (D:ℝ)^((3:ℝ)/2) := by
      nth_rewrite 1 [hD1']
      rw [← Real.rpow_add (by positivity : (0:ℝ) < (D:ℝ))]
      congr 1
      norm_num
    have hycomb : (y:ℝ)^(-(1:ℝ)/2)*(y:ℝ)^(-(1:ℝ)/2) = (y:ℝ)⁻¹ := by
      rw [← Real.rpow_add (by positivity : (0:ℝ) < (y:ℝ))]
      congr 1
      rw [show (-(1:ℝ)/2)+(-(1:ℝ)/2) = (-1:ℝ) by norm_num, Real.rpow_neg_one]
    have hxgroup : (x:ℝ)^((1:ℝ)/2)*(x:ℝ)^(eps/2)*(x:ℝ)^((1:ℝ)/8)
          *(x:ℝ)^((1:ℝ)/2+δ/2)*(x:ℝ)^((1:ℝ)/4+δ/2)
        ≤ (x:ℝ)^((11:ℝ)/8+eps) := by
      have hcomb : (x:ℝ)^((1:ℝ)/2)*(x:ℝ)^(eps/2)*(x:ℝ)^((1:ℝ)/8)
            *(x:ℝ)^((1:ℝ)/2+δ/2)*(x:ℝ)^((1:ℝ)/4+δ/2)
          = (x:ℝ)^((1:ℝ)/2+eps/2+((1:ℝ)/8)+((1:ℝ)/2+δ/2)+((1:ℝ)/4+δ/2)) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
      rw [hcomb]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    -- `(D K L)^{ε/8} ≤ 2 x^{ε/2}`
    have hDKL : ((D:ℝ)*(K:ℝ)*L)^(eps/8) ≤ 2*(x:ℝ)^(eps/2) := by
      have hDKLle : (D:ℝ)*(K:ℝ)*L ≤ 2*(x:ℝ)^((5:ℝ)/2+δ) := by
        have h1 : (K:ℝ)*L ≤ (2*A0)*((x:ℝ)^((1:ℝ)/2)) :=
          mul_le_mul hKle hLle hLnn (by positivity)
        have h2 : (D:ℝ)*((K:ℝ)*L) ≤ (D:ℝ)*((2*A0)*((x:ℝ)^((1:ℝ)/2))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        have h3 : (D:ℝ)*((2*A0)*((x:ℝ)^((1:ℝ)/2)))
            = 2*((D:ℝ)^2*(y:ℝ)⁻¹*(x:ℝ)^(1+δ)) := by
          calc (D:ℝ)*((2*A0)*((x:ℝ)^((1:ℝ)/2)))
              = 2*((D:ℝ)^2*(y:ℝ)⁻¹*((x:ℝ)^((1:ℝ)/2+δ)*((x:ℝ)^((1:ℝ)/2)))) := by
                rw [hA0def]; ring
            _ = 2*((D:ℝ)^2*(y:ℝ)⁻¹*(x:ℝ)^(1+δ)) := by rw [hxadd1]
        have h5 : (D:ℝ)^2 ≤ (x:ℝ)^((3:ℝ)/2) := by
          rw [hDsq]
          calc (D:ℝ)^((3:ℝ)/2)*(D:ℝ)^((1:ℝ)/2)
              ≤ (D:ℝ)^((3:ℝ)/2)*(x:ℝ)^((3:ℝ)/8) :=
                mul_le_mul_of_nonneg_left hDhalf (by positivity)
            _ ≤ (x:ℝ)^((9:ℝ)/8)*(x:ℝ)^((3:ℝ)/8) :=
                mul_le_mul_of_nonneg_right hD32 (by positivity)
            _ = (x:ℝ)^((3:ℝ)/2) := by
                rw [← Real.rpow_add hx0]; congr 1; norm_num
        have h6 : (y:ℝ)⁻¹*(x:ℝ)^(1+δ) ≤ (x:ℝ)^(1+δ) := by
          have h6a : (y:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy1
          simpa using mul_le_mul_of_nonneg_right h6a
            (show (0:ℝ) ≤ (x:ℝ)^(1+δ) by positivity)
        have h4 : 2*((D:ℝ)^2*(y:ℝ)⁻¹*(x:ℝ)^(1+δ)) ≤ 2*(x:ℝ)^((5:ℝ)/2+δ) := by
          calc 2*((D:ℝ)^2*(y:ℝ)⁻¹*(x:ℝ)^(1+δ))
              = 2*((D:ℝ)^2*((y:ℝ)⁻¹*(x:ℝ)^(1+δ))) := by ring
            _ ≤ 2*((x:ℝ)^((3:ℝ)/2)*((x:ℝ)^(1+δ))) := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                exact mul_le_mul h5 h6 (by positivity) (by positivity)
            _ = 2*(x:ℝ)^((5:ℝ)/2+δ) := by
                rw [← Real.rpow_add hx0]; congr 1; ring
        linarith [h2, h3.le, h3.ge, h4]
      have h2e : (2:ℝ)^(eps/8) ≤ 2 := by
        calc (2:ℝ)^(eps/8) ≤ (2:ℝ)^(1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have hxe : ((5:ℝ)/2+δ)*(eps/8) ≤ eps/2 := by nlinarith [hδle', heps]
      have hxe' : (x:ℝ)^(((5:ℝ)/2+δ)*(eps/8)) ≤ (x:ℝ)^(eps/2) :=
        Real.rpow_le_rpow_of_exponent_le hx1 hxe
      calc ((D:ℝ)*(K:ℝ)*L)^(eps/8) ≤ (2*(x:ℝ)^((5:ℝ)/2+δ))^(eps/8) :=
            Real.rpow_le_rpow (by positivity) hDKLle (by positivity)
        _ = (2:ℝ)^(eps/8) * ((x:ℝ)^((5:ℝ)/2+δ))^(eps/8) :=
            Real.mul_rpow (by norm_num) (Real.rpow_nonneg (by positivity) _)
        _ = (2:ℝ)^(eps/8) * (x:ℝ)^(((5:ℝ)/2+δ)*(eps/8)) := by
            rw [Real.rpow_mul (x := (x:ℝ)) (by positivity)]
        _ ≤ 2 * (x:ℝ)^(eps/2) := by
            calc (2:ℝ)^(eps/8) * (x:ℝ)^(((5:ℝ)/2+δ)*(eps/8))
                ≤ 2 * (x:ℝ)^(((5:ℝ)/2+δ)*(eps/8)) :=
                  mul_le_mul_of_nonneg_right h2e (by positivity)
              _ ≤ 2 * (x:ℝ)^(eps/2) := mul_le_mul_of_nonneg_left hxe' (by norm_num)
    -- `√A0`
    have hsqA0 : Real.sqrt A0
        = (D:ℝ)^((1:ℝ)/2)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/4+δ/2) := by
      have hA0' : A0 = (D:ℝ)*((y:ℝ)⁻¹*((x:ℝ)^((1:ℝ)/2+δ))) := by rw [hA0def]; ring
      have hy' : ((y:ℝ)⁻¹)^((1:ℝ)/2) = (y:ℝ)^(-(1:ℝ)/2) := by
        rw [Real.inv_rpow (by positivity : (0:ℝ) ≤ (y:ℝ)),
            ← Real.rpow_neg (by positivity : (0:ℝ) ≤ (y:ℝ))]
        congr 1
        ring
      have hx' : ((x:ℝ)^((1:ℝ)/2+δ))^((1:ℝ)/2) = (x:ℝ)^((1:ℝ)/4+δ/2) := by
        rw [← Real.rpow_mul (x := (x:ℝ)) (by positivity : (0:ℝ) ≤ (x:ℝ))]
        congr 1
        ring
      calc Real.sqrt A0 = (A0)^((1:ℝ)/2) := Real.sqrt_eq_rpow A0
        _ = ((D:ℝ)*((y:ℝ)⁻¹*((x:ℝ)^((1:ℝ)/2+δ))))^((1:ℝ)/2) := by rw [hA0']
        _ = (D:ℝ)^((1:ℝ)/2) * (((y:ℝ)⁻¹*((x:ℝ)^((1:ℝ)/2+δ))))^((1:ℝ)/2) :=
            Real.mul_rpow (by positivity) (by positivity)
        _ = (D:ℝ)^((1:ℝ)/2)
              * (((y:ℝ)⁻¹)^((1:ℝ)/2) * ((x:ℝ)^((1:ℝ)/2+δ))^((1:ℝ)/2)) := by
            rw [Real.mul_rpow (by positivity) (by positivity)]
        _ = (D:ℝ)^((1:ℝ)/2)
              * ((y:ℝ)^(-(1:ℝ)/2) * ((x:ℝ)^((1:ℝ)/2+δ))^((1:ℝ)/2)) := by rw [hy']
        _ = (D:ℝ)^((1:ℝ)/2) * ((y:ℝ)^(-(1:ℝ)/2) * (x:ℝ)^((1:ℝ)/4+δ/2)) := by rw [hx']
        _ = (D:ℝ)^((1:ℝ)/2)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/4+δ/2) := by ring

    -- `√(K+1)`
    have hsqK : Real.sqrt ((K:ℝ)+1)
        ≤ 4*(D:ℝ)^((1:ℝ)/2)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/4+δ/2) := by
      have h4 : (K:ℝ)+1 ≤ 4*A0 := by linarith
      have hnn : (0:ℝ) ≤ (D:ℝ)^((1:ℝ)/2)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/4+δ/2) :=
        by positivity
      calc Real.sqrt ((K:ℝ)+1) ≤ Real.sqrt (4*A0) := Real.sqrt_le_sqrt h4
        _ = Real.sqrt (4:ℝ) * Real.sqrt A0 := Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) A0
        _ = 2*((D:ℝ)^((1:ℝ)/2)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/4+δ/2)) := by
            rw [sqrt_four, hsqA0]
        _ ≤ 4*(D:ℝ)^((1:ℝ)/2)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/4+δ/2) := by
            linarith [hnn]
    -- `√(D K L)`
    have hsqDKL : Real.sqrt ((D:ℝ)*(K:ℝ)*L)
        ≤ 2*(D:ℝ)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/2+δ/2) := by
      have h2 : (D:ℝ)*(K:ℝ)*L ≤ 2*((D:ℝ)^2*(y:ℝ)⁻¹*(x:ℝ)^(1+δ)) := by
        have h1 : (K:ℝ)*L ≤ (2*A0)*((x:ℝ)^((1:ℝ)/2)) :=
          mul_le_mul hKle hLle hLnn (by positivity)
        have h2' : (D:ℝ)*((K:ℝ)*L) ≤ (D:ℝ)*((2*A0)*((x:ℝ)^((1:ℝ)/2))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        have h3 : (D:ℝ)*((2*A0)*((x:ℝ)^((1:ℝ)/2)))
            = 2*((D:ℝ)^2*(y:ℝ)⁻¹*(x:ℝ)^(1+δ)) := by
          calc (D:ℝ)*((2*A0)*((x:ℝ)^((1:ℝ)/2)))
              = 2*((D:ℝ)^2*(y:ℝ)⁻¹*((x:ℝ)^((1:ℝ)/2+δ)*((x:ℝ)^((1:ℝ)/2)))) := by
                rw [hA0def]; ring
            _ = 2*((D:ℝ)^2*(y:ℝ)⁻¹*(x:ℝ)^(1+δ)) := by rw [hxadd1]
        linarith [h2', h3.le, h3.ge]
      have hsq2 : Real.sqrt (2:ℝ) ≤ 2 := by
        calc Real.sqrt (2:ℝ) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
          _ = 2 := sqrt_four
      have hy1' : Real.sqrt ((y:ℝ)⁻¹) = (y:ℝ)^(-(1:ℝ)/2) := by
        rw [Real.sqrt_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity : (0:ℝ) ≤ (y:ℝ))]
        congr 1
        ring
      have hx1' : Real.sqrt ((x:ℝ)^(1+δ)) = (x:ℝ)^((1:ℝ)/2+δ/2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (x := (x:ℝ)) (by positivity : (0:ℝ) ≤ (x:ℝ))]
        congr 1
        ring
      have hD1'' : Real.sqrt ((D:ℝ)^2) = (D:ℝ) := Real.sqrt_sq (by positivity : (0:ℝ) ≤ (D:ℝ))
      calc Real.sqrt ((D:ℝ)*(K:ℝ)*L)
          ≤ Real.sqrt (2*((D:ℝ)^2*(y:ℝ)⁻¹*(x:ℝ)^(1+δ))) := Real.sqrt_le_sqrt h2
        _ = Real.sqrt (2:ℝ) * Real.sqrt ((D:ℝ)^2) * Real.sqrt ((y:ℝ)⁻¹)
              * Real.sqrt ((x:ℝ)^(1+δ)) := by
            rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_mul (by positivity),
                Real.sqrt_mul (by positivity)]
            ring
        _ = Real.sqrt (2:ℝ) * (D:ℝ) * (y:ℝ)^(-(1:ℝ)/2) * (x:ℝ)^((1:ℝ)/2+δ/2) := by
            rw [hD1'', hy1', hx1']
        _ ≤ 2*(D:ℝ)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/2+δ/2) := by
            have hnn : (0:ℝ) ≤ (D:ℝ)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/2+δ/2) := by positivity
            nlinarith [hsq2, hnn, Real.sqrt_nonneg (2:ℝ)]
    -- √x ≤ x^{1/2}
    have hsqrtx : Real.sqrt (x:ℝ) = (x:ℝ)^((1:ℝ)/2) := Real.sqrt_eq_rpow (x:ℝ)
    -- the `y`-comparison
    have hyle : (y:ℝ)^((1:ℝ)/2) ≤ (x:ℝ)^((1:ℝ)/2+eps/2-δ/2) := by
      have h1 : (y:ℝ)^((1:ℝ)/2) ≤ (x:ℝ)^((1:ℝ)/2) :=
        Real.rpow_le_rpow (by positivity) hyx1 (by norm_num)
      have h2 : (x:ℝ)^((1:ℝ)/2) ≤ (x:ℝ)^((1:ℝ)/2+eps/2-δ/2) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hδle', heps])
      linarith [h1, h2]
    -- the main estimate
    have hmain : Real.sqrt (x:ℝ)
          * (C1*((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*L)) * ((D:ℝ)*(K:ℝ)*L)^(eps/8)
              * (x:ℝ)^((1:ℝ)/8) * Real.sqrt ((K:ℝ)+1))
        ≤ 32*C1*(D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps) := by
      have hyge1 : (1:ℝ) ≤ (y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/2+δ/2) := by
        have h1 : (y:ℝ)^((1:ℝ)/2) ≤ (x:ℝ)^((1:ℝ)/2+δ/2) := by
          have h1a : (y:ℝ)^((1:ℝ)/2) ≤ (x:ℝ)^((1:ℝ)/2) :=
            Real.rpow_le_rpow (by positivity) hyx1 (by norm_num)
          have h1b : (x:ℝ)^((1:ℝ)/2) ≤ (x:ℝ)^((1:ℝ)/2+δ/2) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hδpos.le])
          linarith
        have hmul := mul_le_mul_of_nonneg_right h1
          (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (y:ℝ)) (-(1:ℝ)/2))
        have h2 : (y:ℝ)^((1:ℝ)/2) * (y:ℝ)^(-(1:ℝ)/2) = 1 := by
          rw [← Real.rpow_add (by positivity : (0:ℝ) < (y:ℝ))]
          norm_num
        rw [h2] at hmul
        simpa [mul_comm] using hmul
      have hstep : (D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*L)
          ≤ 3*(D:ℝ)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/2+δ/2) := by
        have hDle : (D:ℝ) ≤ (D:ℝ)*((y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/2+δ/2)) := by
          have h := mul_le_mul_of_nonneg_left hyge1 (show (0:ℝ) ≤ (D:ℝ) by positivity)
          simpa using h
        calc (D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*L)
            ≤ (D:ℝ) + 2*((D:ℝ)*((y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/2+δ/2))) := by linarith [hsqDKL]
          _ ≤ (D:ℝ)*((y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/2+δ/2))
                + 2*((D:ℝ)*((y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/2+δ/2))) := by linarith [hDle]
          _ = 3*(D:ℝ)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/2+δ/2) := by ring
      have hstep2 : (D:ℝ) + 2*(D:ℝ)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/2+δ/2)
          ≤ 3*(D:ℝ)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/2+δ/2) := by
        nlinarith [hyge1, show (0:ℝ) ≤ (D:ℝ) by positivity]
      calc Real.sqrt (x:ℝ)
            * (C1*((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*L)) * ((D:ℝ)*(K:ℝ)*L)^(eps/8)
                * (x:ℝ)^((1:ℝ)/8) * Real.sqrt ((K:ℝ)+1))
          ≤ (x:ℝ)^((1:ℝ)/2)
            * (C1*(3*(D:ℝ)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/2+δ/2))
                * (2*(x:ℝ)^(eps/2)) * (x:ℝ)^((1:ℝ)/8)
                * (4*(D:ℝ)^((1:ℝ)/2)*(y:ℝ)^(-(1:ℝ)/2)*(x:ℝ)^((1:ℝ)/4+δ/2))) := by
              rw [hsqrtx]
              gcongr
        _ = 24*C1 * (((D:ℝ)*(D:ℝ)^((1:ℝ)/2)) * ((y:ℝ)^(-(1:ℝ)/2)*(y:ℝ)^(-(1:ℝ)/2))
              * ((x:ℝ)^((1:ℝ)/2)*(x:ℝ)^(eps/2)*(x:ℝ)^((1:ℝ)/8)
                  *(x:ℝ)^((1:ℝ)/2+δ/2)*(x:ℝ)^((1:ℝ)/4+δ/2))) := by ring
        _ = 24*C1 * ((D:ℝ)^((3:ℝ)/2) * ((y:ℝ)⁻¹)
              * ((x:ℝ)^((1:ℝ)/2)*(x:ℝ)^(eps/2)*(x:ℝ)^((1:ℝ)/8)
                  *(x:ℝ)^((1:ℝ)/2+δ/2)*(x:ℝ)^((1:ℝ)/4+δ/2))) := by
              rw [hDcomb, hycomb]
        _ ≤ 24*C1 * ((D:ℝ)^((3:ℝ)/2) * ((y:ℝ)⁻¹) * (x:ℝ)^((11:ℝ)/8+eps)) := by
              gcongr
        _ ≤ 32*C1*(D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps) := by
              have hnn : (0:ℝ) ≤ (D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps) := by positivity
              nlinarith [hC1.le, hnn]
    calc (∑ d ∈ Finset.Icc 1 D, |Phi d|)
        ≤ Real.sqrt (x:ℝ) * ∫ u in (0:ℝ)..(K:ℝ), ∑ d ∈ Finset.Icc 1 D, |Yd f x d K u| := by
          calc (∑ d ∈ Finset.Icc 1 D, |Phi d|)
              ≤ ∑ d ∈ Finset.Icc 1 D,
                  Real.sqrt (x:ℝ) * ∫ u in (0:ℝ)..(K:ℝ), |Yd f x d K u| :=
                Finset.sum_le_sum hper
            _ = Real.sqrt (x:ℝ) * ∑ d ∈ Finset.Icc 1 D,
                  ∫ u in (0:ℝ)..(K:ℝ), |Yd f x d K u| := by rw [Finset.mul_sum]
            _ = Real.sqrt (x:ℝ) * ∫ u in (0:ℝ)..(K:ℝ),
                  ∑ d ∈ Finset.Icc 1 D, |Yd f x d K u| := by rw [hswap]
      _ ≤ Real.sqrt (x:ℝ) * (C1*((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*L)) * ((D:ℝ)*(K:ℝ)*L)^(eps/8)
              * (x:ℝ)^((1:ℝ)/8) * Real.sqrt ((K:ℝ)+1)) :=
          mul_le_mul_of_nonneg_left hint (Real.sqrt_nonneg _)
      _ ≤ 32*C1*(D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps) := hmain
  -- final combination
  have hTnn : (0:ℝ) ≤ (D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps) := by positivity
  have hpoly : 8*(A+1) + 128*C1 + 16*C3*(A+1)
      ≤ (20 + 200*C1 + 400*C3)*(A+1) := by
    nlinarith [hC1.le, hC3.le, hA.le]
  calc (∑ d ∈ Finset.Icc 1 D, (d:ℝ) * |AdF (fun n : ℕ => f n) d x - MdF f d x|)
      ≤ (∑ d ∈ Finset.Icc 1 D, (d:ℝ)*|R1 d|)
        + 4*(∑ d ∈ Finset.Icc 1 D, |Phi d|) + 4*(∑ d ∈ Finset.Icc 1 D, |Tail d|) := hsum
    _ ≤ 8*(A+1)*(D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps)
        + 4*(32*C1*(D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps))
        + 4*(4*C3*(A+1)*(D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹*(x:ℝ)^((11:ℝ)/8+eps)) := by
        linarith [hR1sum, hPhisum, hTailsum]
    _ ≤ (20 + 200*C1 + 200*C3 + 200*C3)*(A+1)*(D:ℝ)^((3:ℝ)/2)*(y:ℝ)⁻¹
          *(x:ℝ)^((11:ℝ)/8+eps) := by
        have h := mul_le_mul_of_nonneg_right hpoly hTnn
        nlinarith [h]



/-! ### Elementary glue: the identification of the first factor with `Ad` -/

/-- The number of lattice pairs `(a,b) ∈ ℤ²` with `a² + b⁴ ≤ x` and `d ∣ a² + b⁴` equals
`A_d(x) = ∑_{n ≤ x, d ∣ n} a_n`. -/
theorem ncard_eq_Ad_sum (d x : ℕ) :
    (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℕ)
      = ∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n),
          ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard := by
  classical
  have hFin : ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)
      ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).Finite := by
    have hbig : ((((Finset.Icc (-(x : ℤ)) (x : ℤ) : Finset ℤ)) : Set ℤ) ×ˢ
        (((Finset.Icc (-(x : ℤ)) (x : ℤ) : Finset ℤ)) : Set ℤ)).Finite :=
      (Finset.finite_toSet _).prod (Finset.finite_toSet _)
    refine hbig.subset ?_
    intro p hp
    have hp' : p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) := hp.1
    have h2 : (0 : ℤ) ≤ p.2 ^ 4 := by positivity
    have h4 : (0 : ℤ) ≤ p.1 ^ 2 := by positivity
    have hp1 : p.1 ^ 2 ≤ (x : ℤ) := by linarith
    have hp2 : p.2 ^ 4 ≤ (x : ℤ) := by linarith
    rw [Set.mem_prod]
    constructor
    · rw [Finset.mem_coe, Finset.mem_Icc]
      have h' : ((p.1.natAbs ^ 2 : ℕ) : ℤ) ≤ (x : ℤ) := by
        rw [Nat.cast_pow, Int.natAbs_sq]; exact hp1
      have h'' : p.1.natAbs ^ 2 ≤ x := by exact_mod_cast h'
      have h : p.1.natAbs ≤ x :=
        le_trans (Nat.le_self_pow (by norm_num) p.1.natAbs) h''
      have hle : |p.1| ≤ (x : ℤ) := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast h
      exact abs_le.mp hle
    · rw [Finset.mem_coe, Finset.mem_Icc]
      have h4' : ((p.2.natAbs : ℤ)) ^ 4 = p.2 ^ 4 := by
        rw [← Nat.cast_pow, ← Int.natAbs_pow, Int.natAbs_of_nonneg (by positivity : (0:ℤ) ≤ p.2^4)]
      have h' : ((p.2.natAbs ^ 4 : ℕ) : ℤ) ≤ (x : ℤ) := by
        rw [Nat.cast_pow, h4']; exact hp2
      have h'' : p.2.natAbs ^ 4 ≤ x := by exact_mod_cast h'
      have h : p.2.natAbs ≤ x :=
        le_trans (Nat.le_self_pow (by norm_num) p.2.natAbs) h''
      have hle : |p.2| ≤ (x : ℤ) := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast h
      exact abs_le.mp hle
  let sf := hFin.toFinset
  have hmemSf : ∀ p : ℤ × ℤ, p ∈ sf ↔
      (p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)) := by
    intro p
    show p ∈ hFin.toFinset ↔ _
    rw [Set.Finite.mem_toFinset]
    rfl
  let F : ℤ × ℤ → ℕ := fun p => (p.1 ^ 2 + p.2 ^ 4).toNat
  have hmap : Set.MapsTo F (↑sf : Set (ℤ × ℤ))
      (↑((Finset.range (x + 1)).filter (fun n => d ∣ n)) : Set ℕ) := by
    intro p hp
    have hpS := (hmemSf p).mp hp
    have hnn : (0 : ℤ) ≤ p.1 ^ 2 + p.2 ^ 4 := by positivity
    have htoNat : (p.1 ^ 2 + p.2 ^ 4).toNat ≤ x := by
      have : (((p.1 ^ 2 + p.2 ^ 4).toNat : ℤ)) ≤ (x : ℤ) := by
        rw [Int.toNat_of_nonneg hnn]; exact hpS.1
      exact_mod_cast this
    have hdvd : d ∣ (p.1 ^ 2 + p.2 ^ 4).toNat := by
      have h1 : (((p.1 ^ 2 + p.2 ^ 4).toNat : ℕ) : ℤ) = p.1 ^ 2 + p.2 ^ 4 :=
        Int.toNat_of_nonneg hnn
      have h2 : (d : ℤ) ∣ (((p.1 ^ 2 + p.2 ^ 4).toNat : ℕ) : ℤ) := by
        rw [h1]; exact hpS.2
      exact_mod_cast h2
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le htoNat, hdvd⟩
  have hterm : ∀ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n),
      (sf.filter (fun p => F p = n)).card
        = ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard := by
    intro n hn
    have hnle : n ≤ x := by
      have := (Finset.mem_filter.mp hn).1
      simp only [Finset.mem_range] at this
      omega
    have hdvd : d ∣ n := (Finset.mem_filter.mp hn).2
    have hset : (↑(sf.filter (fun p => F p = n)) : Set (ℤ × ℤ))
        = {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)} := by
      ext p
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hp, hFn⟩
        have hnn : (0 : ℤ) ≤ p.1 ^ 2 + p.2 ^ 4 := by positivity
        have hFn' : (p.1 ^ 2 + p.2 ^ 4).toNat = n := hFn
        have h1 : p.1 ^ 2 + p.2 ^ 4 = (((p.1 ^ 2 + p.2 ^ 4).toNat : ℕ) : ℤ) :=
          (Int.toNat_of_nonneg hnn).symm
        rw [h1, hFn']
      · rintro h
        refine ⟨?_, ?_⟩
        · rw [hmemSf p, h]
          exact ⟨by exact_mod_cast hnle, by exact_mod_cast hdvd⟩
        · show (p.1 ^ 2 + p.2 ^ 4).toNat = n
          rw [h]
          exact Int.toNat_natCast n
    rw [← Set.ncard_coe_finset (sf.filter (fun p => F p = n)), hset]
  have hfib := Finset.card_eq_sum_card_fiberwise hmap
  have hsum : (∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n),
        ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard)
      = ∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n),
          (sf.filter (fun p => F p = n)).card :=
    Finset.sum_congr rfl (fun n hn => (hterm n hn).symm)
  have hcard : ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)
        ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard = sf.card :=
    Set.ncard_eq_toFinset_card _ hFin
  rw [hsum, ← hfib, hcard]



/-! ### Elementary glue: comparison of `M_d(x)` with the `√`-main term -/

lemma Nat_sqrt_sqrt_eq (x : ℕ) : Nat.sqrt (Nat.sqrt x) = ⌊(x:ℝ)^((1:ℝ)/4)⌋₊ := by
  have h1 : ∀ m : ℕ, m ≤ Nat.sqrt (Nat.sqrt x) ↔ m^4 ≤ x := by
    intro m
    rw [Nat.le_sqrt', Nat.le_sqrt']
    constructor
    · intro h; nlinarith [h]
    · intro h
      have : (m^2)^2 ≤ x := by nlinarith [h]
      exact this
  have h4eq : ((x:ℝ)^((1:ℝ)/4))^4 = (x:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (x:ℝ))]
    norm_num
  have h2 : ∀ m : ℕ, m ≤ ⌊(x:ℝ)^((1:ℝ)/4)⌋₊ ↔ m^4 ≤ x := by
    intro m
    rw [Nat.le_floor_iff (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (x:ℝ)) _)]
    constructor
    · intro h
      have h4 : ((m:ℝ))^4 ≤ ((x:ℝ)^((1:ℝ)/4))^4 := pow_le_pow_left₀ (by positivity) h 4
      rw [h4eq] at h4
      exact_mod_cast h4
    · intro h
      have h4 : ((m:ℝ))^4 ≤ ((x:ℝ)^((1:ℝ)/4))^4 := by
        rw [h4eq]; exact_mod_cast h
      exact (pow_le_pow_iff_left₀ (by positivity)
        (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (x:ℝ)) _)
        (by norm_num : (4:ℕ) ≠ 0)).mp h4
  refine le_antisymm ?_ ?_
  · exact (h2 _).mpr ((h1 _).mp (le_refl _))
  · exact (h1 _).mpr ((h2 _).mp (le_refl _))

/-- The number of `β ∈ [0,d)` with `d ∣ β² + c⁴` is `ρ(c²;d)`. -/
lemma card_filter_dvd_eq_rho (d : ℕ) (c : ℤ) (hd : 0 < d) :
    ((Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + (c:ℤ)^4))).card
      = rho (c.natAbs^2) d := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hc4 : ((c:ℤ))^4 = (((c.natAbs^2 : ℕ) : ℤ))^2 := by
    have h1 : c^2 = ((c.natAbs^2 : ℕ) : ℤ) := by
      rw [Nat.cast_pow, Int.natAbs_sq]
    rw [show (c:ℤ)^4 = ((c^2 : ℤ))^2 by ring, h1]
  have hset : ((Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + (c:ℤ)^4)))
      = ((Finset.range d).filter (fun β : ℕ =>
          ((d:ℤ) ∣ (β:ℤ)^2 + (((c.natAbs^2 : ℕ) : ℤ))^2))) := by
    apply Finset.filter_congr
    intro β _
    rw [hc4]
  rw [hset, card_range_filter_eq_card_zmod d (c.natAbs^2), rho]
  rw [show ({α : ZMod d | α ^ 2 + (((c.natAbs^2 : ℕ)) : ZMod d) ^ 2 = 0})
      = (↑(Finset.univ.filter (fun α : ZMod d =>
          α ^ 2 + (((c.natAbs^2 : ℕ)) : ZMod d) ^ 2 = 0)) : Set (ZMod d)) from by
    ext α; simp]
  exact (Set.ncard_coe_finset _).symm

/-- For `c ≥ 1` with `c⁴ ≤ x`: the sharp count `2⌊√(x−c⁴)⌋+1` differs from `2√(x−c⁴)` by at
most `2`. -/
lemma abs_sqrtTerm_sub_sqrt (x : ℕ) (c : ℤ) (hc : 1 ≤ c) (hcx : (c:ℝ)^4 ≤ (x:ℝ)) :
    |(2*(Nat.sqrt (x - c.toNat^4) : ℝ) + 1) - 2*Real.sqrt ((x:ℝ) - (c:ℝ)^4)| ≤ 2 := by
  have hc0 : 0 ≤ c := by omega
  have htoNat : (c.toNat : ℝ) = (c:ℝ) := by
    have h : ((c.toNat : ℤ) : ℝ) = (c : ℝ) := by
      rw [Int.toNat_of_nonneg hc0]
    exact h
  have hc4le : c.toNat^4 ≤ x := by
    have h1 : ((c.toNat^4 : ℕ) : ℝ) ≤ (x:ℝ) := by
      rw [Nat.cast_pow, htoNat]
      exact hcx
    exact_mod_cast h1
  have hcast : ((x - c.toNat^4 : ℕ) : ℝ) = (x:ℝ) - (c:ℝ)^4 := by
    rw [Nat.cast_sub hc4le]
    push_cast
    rw [htoNat]
  have h := abs_sqrt_sub_floor (x - c.toNat^4)
  rw [hcast] at h
  simpa [abs_sub_comm] using h

/-! ### Elementary glue: the crude discrepancy bound for all moduli -/

/-- **Elementary (crude) bound for the discrepancy.**  The fractional-part identity of
`X2Y4_Ad_sub_Md_eq_fract` together with `|fract t − 1/2| ≤ 1/2` gives
`Σ_{d ≤ D} |A_d(x) − main_d| ≤ C x^{1/4} D log⁶(2D+2)`. -/
theorem ncard_sub_main_term_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x D : ℕ, 1 ≤ x → 1 ≤ D →
      (∑ d ∈ Finset.Icc 1 D,
        |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
          - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ))
                (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
              ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
        ≤ C * (x : ℝ) ^ ((1 : ℝ) / 4) * (D : ℝ) * (Real.log (2 * (D : ℝ) + 2)) ^ 6 := by
  obtain ⟨Cρ, hCρpos, hρ⟩ := Commons.NumberTheory.FriedlanderIwaniec.sum_rho_sq_div_le
  refine ⟨4 * Cρ + 4, by positivity, ?_⟩
  intro x D hx hD
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hlogpos : (0:ℝ) < (Real.log (2*(D:ℝ)+2))^6 := by
    have : (0:ℝ) < Real.log (2*(D:ℝ)+2) := by
      apply Real.log_pos; linarith
    positivity
  set N : ℕ := ⌊(x:ℝ)^((1:ℝ)/4)⌋₊ with hNdef
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  -- the per-modulus bound
  have hpt : ∀ d ∈ Finset.Icc 1 D,
      |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
          - (∑ c ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
              ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|
        ≤ ∑ c ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (rho (c.natAbs^2) d : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hid := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Ad_sub_Md_eq_fract x d hd1 hx
    rw [show (∑ c ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
              ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))
          = (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ))
                (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
              ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ)) from by rw [hNdef]]
    rw [hid, abs_neg]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    apply Finset.sum_le_sum
    intro c _
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have h2 : ∀ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
        |(Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ)) - 1 / 2)
            + (Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ)) - 1 / 2)|
          ≤ 1 := by
      intro β _
      have h3 : |Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ)) - 1 / 2| ≤ 1/2 := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · linarith [Int.fract_nonneg ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ))]
        · linarith [Int.fract_lt_one ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ))]
      have h4 : |Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ)) - 1 / 2| ≤ 1/2 := by
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · linarith [Int.fract_nonneg ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ))]
        · linarith [Int.fract_lt_one ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ))]
      calc |(Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ)) - 1 / 2)
            + (Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ)) - 1 / 2)|
          ≤ |Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ)) - 1 / 2|
            + |Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ)) - 1 / 2| :=
            abs_add_le _ _
        _ ≤ 1 := by linarith
    have hcard : (∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
          (1:ℝ)) = (rho (c.natAbs^2) d : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_filter_dvd_eq_rho d c (by omega)]
    calc (∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
          |(Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ)) - 1 / 2)
              + (Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ)) - 1 / 2)|)
        ≤ ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)), (1:ℝ) :=
          Finset.sum_le_sum h2
      _ = (rho (c.natAbs^2) d : ℝ) := hcard
  -- sum over the moduli
  have hsum : (∑ d ∈ Finset.Icc 1 D,
        |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
          - (∑ c ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
              ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
      ≤ ∑ d ∈ Finset.Icc 1 D, ∑ c ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (rho (c.natAbs^2) d : ℝ) :=
    Finset.sum_le_sum hpt
  -- bound `Σ_d ρ` by `D log⁶` for each `c`
  have hbound : ∀ c ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
      (∑ d ∈ Finset.Icc 1 D, (rho (c.natAbs^2) d : ℝ))
        ≤ (D:ℝ) * (Cρ * (Real.log (2*(D:ℝ)+2))^6) := by
    intro c _
    have h := hρ D c.natAbs
    have hc4 : ∀ d : ℕ, rho (c.natAbs^2) d
        = ({α : ZMod d | α ^ 2 + (c.natAbs : ZMod d) ^ 4 = 0}).ncard := by
      intro d
      rw [rho]
      congr 1
      ext α
      simp only [Set.mem_ofPred_eq]
      rw [show (((c.natAbs^2 : ℕ)) : ZMod d) = (c.natAbs : ZMod d)^2 by push_cast; ring]
      ring
    have h1 := h
    have h2 : (∑ d ∈ Finset.Icc 1 D, (rho (c.natAbs^2) d : ℝ))
        = ∑ d ∈ Finset.Icc 1 D, (d:ℝ) * ((rho (c.natAbs^2) d : ℝ)/(d:ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd'
      have hd1 : (1:ℕ) ≤ d := (Finset.mem_Icc.mp hd').1
      have hdne : (d:ℝ) ≠ 0 := by positivity
      field_simp
    rw [h2]
    have h3 : ∀ d ∈ Finset.Icc 1 D,
        (d:ℝ) * ((rho (c.natAbs^2) d : ℝ)/(d:ℝ)) ≤ (D:ℝ) * ((rho (c.natAbs^2) d : ℝ)/(d:ℝ)) := by
      intro d hd'
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (Finset.mem_Icc.mp hd').2
    calc (∑ d ∈ Finset.Icc 1 D, (d:ℝ) * ((rho (c.natAbs^2) d : ℝ)/(d:ℝ)))
        ≤ ∑ d ∈ Finset.Icc 1 D, (D:ℝ) * ((rho (c.natAbs^2) d : ℝ)/(d:ℝ)) := Finset.sum_le_sum h3
      _ = (D:ℝ) * ∑ d ∈ Finset.Icc 1 D, (rho (c.natAbs^2) d : ℝ)/(d:ℝ) := by rw [Finset.mul_sum]
      _ = (D:ℝ) * ∑ d ∈ Finset.Icc 1 D,
            (({α : ZMod d | α ^ 2 + (c.natAbs : ZMod d) ^ 4 = 0}).ncard : ℝ)/(d:ℝ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro d _
          rw [hc4 d]
      _ ≤ (D:ℝ) * (Cρ * (Real.log (2*(D:ℝ)+2))^6) := by
          apply mul_le_mul_of_nonneg_left h (by positivity)
  calc (∑ d ∈ Finset.Icc 1 D,
        |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
          - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ))
                (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
              ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
      = (∑ d ∈ Finset.Icc 1 D,
        |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
          - (∑ c ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
              ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|) := by rw [hNdef]
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ∑ c ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (rho (c.natAbs^2) d : ℝ) := hsum
    _ = ∑ c ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), ∑ d ∈ Finset.Icc 1 D, (rho (c.natAbs^2) d : ℝ) :=
        Finset.sum_comm
    _ ≤ ∑ c ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), (D:ℝ) * (Cρ * (Real.log (2*(D:ℝ)+2))^6) :=
        Finset.sum_le_sum hbound
    _ = ((Finset.Icc (-(N:ℤ)) (N:ℤ)).card : ℝ) * ((D:ℝ) * (Cρ * (Real.log (2*(D:ℝ)+2))^6)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * Cρ + 4) * (x:ℝ)^((1:ℝ)/4) * (D:ℝ) * (Real.log (2*(D:ℝ)+2))^6 := by
        set L : ℝ := (Real.log (2*(D:ℝ)+2))^6 with hLdef
        have hxq1 : (1:ℝ) ≤ (x:ℝ)^((1:ℝ)/4) := Real.one_le_rpow hx1 (by norm_num)
        have hcard : ((Finset.Icc (-(N:ℤ)) (N:ℤ)).card : ℝ) ≤ 2 * (x:ℝ)^((1:ℝ)/4) + 1 := by
          have h1 : (Finset.Icc (-(N:ℤ)) (N:ℤ)).card = 2 * N + 1 := by
            rw [Int.card_Icc]
            simp
            omega
          rw [h1]
          have hNle : ((N:ℕ):ℝ) ≤ (x:ℝ)^((1:ℝ)/4) := by
            have h : ((⌊(x:ℝ)^((1:ℝ)/4)⌋₊ : ℕ) : ℝ) ≤ (x:ℝ)^((1:ℝ)/4) :=
              Nat.floor_le (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (x:ℝ)) _)
            rw [hNdef]; exact h
          have hcast : (((2 * N + 1 : ℕ)) : ℝ) = 2 * ((N:ℕ):ℝ) + 1 := by push_cast; ring
          rw [hcast]
          linarith
        have hstep : ((Finset.Icc (-(N:ℤ)) (N:ℤ)).card : ℝ) * ((D:ℝ) * (Cρ * L))
            ≤ (2*(x:ℝ)^((1:ℝ)/4) + 1) * ((D:ℝ) * (Cρ * L)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        have hkey : (2*(x:ℝ)^((1:ℝ)/4) + 1) * Cρ ≤ (4*Cρ + 4) * (x:ℝ)^((1:ℝ)/4) := by
          nlinarith [hCρpos.le, hxq1]
        have hstep2 : (2*(x:ℝ)^((1:ℝ)/4) + 1) * ((D:ℝ) * (Cρ * L))
            ≤ (4*Cρ + 4) * (x:ℝ)^((1:ℝ)/4) * (D:ℝ) * L := by
          calc (2*(x:ℝ)^((1:ℝ)/4) + 1) * ((D:ℝ) * (Cρ * L))
              = ((2*(x:ℝ)^((1:ℝ)/4) + 1) * Cρ) * ((D:ℝ) * L) := by ring
            _ ≤ ((4*Cρ + 4) * (x:ℝ)^((1:ℝ)/4)) * ((D:ℝ) * L) :=
                mul_le_mul_of_nonneg_right hkey (by positivity)
            _ = (4*Cρ + 4) * (x:ℝ)^((1:ℝ)/4) * (D:ℝ) * L := by ring
        linarith [hstep, hstep2]

/-! ### Elementary glue: comparison of `M_d(x)` with the `√`-main term -/

/-- **Comparison of `M_d(x)` with the `√`-main term of the target statement.** -/
theorem Md_sub_main_term_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x D : ℕ, 1 ≤ x → 1 ≤ D →
      (∑ d ∈ Finset.Icc 1 D,
        |(Md d x : ℝ)
          - (∑ c ∈ Finset.Icc (-(⌊(x:ℝ)^((1:ℝ)/4)⌋₊ : ℤ)) (⌊(x:ℝ)^((1:ℝ)/4)⌋₊),
              ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + (c:ℤ)^4)),
                2 * Real.sqrt ((x:ℝ) - (c:ℝ)^4) / (d:ℝ))|)
        ≤ C * (x:ℝ)^((1:ℝ)/4) * (Real.log (2*(D:ℝ)+2))^6 := by
  obtain ⟨Cρ, hCρpos, hρ⟩ := Commons.NumberTheory.FriedlanderIwaniec.sum_rho_sq_div_le
  refine ⟨7*Cρ + 7, by positivity, ?_⟩
  intro x D hx hD
  set N : ℕ := ⌊(x:ℝ)^((1:ℝ)/4)⌋₊ with hNdef
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by linarith
  have hNsqrt : Nat.sqrt (Nat.sqrt x) = N := by rw [hNdef]; exact Nat_sqrt_sqrt_eq x
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hlogpos : (0:ℝ) < (Real.log (2*(D:ℝ)+2))^6 := by
    have : (0:ℝ) < Real.log (2*(D:ℝ)+2) := by
      apply Real.log_pos; linarith
    positivity
  have hN4 : N^4 ≤ x := by
    have h1 : (Nat.sqrt (Nat.sqrt x))^2 ≤ Nat.sqrt x := (Nat.le_sqrt').mp (le_refl _)
    have h2 : ((Nat.sqrt (Nat.sqrt x))^2)^2 ≤ x := (Nat.le_sqrt').mp h1
    have h3 : (Nat.sqrt (Nat.sqrt x))^4 ≤ x := by nlinarith [h2]
    rwa [hNsqrt] at h3
  have hsqrtfloor : Real.sqrt (x:ℝ) < ((Nat.sqrt x : ℕ):ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity : (0:ℝ) < ((Nat.sqrt x : ℕ):ℝ) + 1)]
    have : x < (Nat.sqrt x + 1)^2 := by
      simpa [pow_two, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt x
    exact_mod_cast this
  have hsqrtfloor2 : ((Nat.sqrt x : ℕ):ℝ) ≤ Real.sqrt (x:ℝ) := natSqrt_cast_le_sqrt x
  -- the summand of the target's main term, for a natural index
  have heval : ∀ (d : ℕ) (c : ℤ), 1 ≤ d → (c:ℝ)^4 ≤ (x:ℝ) →
      (∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + (c:ℤ)^4)),
          2 * Real.sqrt ((x:ℝ) - (c:ℝ)^4) / (d:ℝ))
        = (rho (c.natAbs^2) d : ℝ) * (2*Real.sqrt ((x:ℝ) - (c:ℝ)^4) / (d:ℝ)) := by
    intro d c hd hcx
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [card_filter_dvd_eq_rho d c (by omega)]
  -- the "sharp" side, rewritten in the natural-index form
  have hMd : ∀ d : ℕ, (Md d x : ℝ)
      = (1/(d:ℝ))*(2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
            * (2*(Nat.sqrt (x - (j+1)^4) : ℝ) + 1)) + 2*((Nat.sqrt x : ℕ):ℝ)*(rho 0 d:ℝ)) := by
    intro d
    have h1 : (Md d x : ℝ) = ((MdNum d x : ℕ) : ℝ)/(d:ℝ) := by
      rw [Md]; push_cast; ring
    rw [h1]
    have h2 : ((MdNum d x : ℕ) : ℝ) = 2*(∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
          (rho (c^2) d : ℝ) * (2*(Nat.sqrt (x - c^4) : ℝ) + 1))
        + 2*((Nat.sqrt x : ℕ):ℝ)*(rho 0 d : ℝ) := by
      have h := congrArg (fun n : ℕ => (n:ℝ)) (MdNum_reindex d x)
      push_cast at h
      rw [h]
    rw [h2, hNsqrt, reindex_Icc_real]
    ring
  -- the smooth side, in the natural-index form
  have hconv : ∀ d : ℕ, 1 ≤ d →
      (∑ c ∈ Finset.Icc (1:ℤ) (N:ℤ),
          ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + (c:ℤ)^4)),
            2 * Real.sqrt ((x:ℝ) - (c:ℝ)^4) / (d:ℝ))
        = (∑ n ∈ Finset.range N, (rho ((n+1)^2) d : ℝ)
            * (2*Real.sqrt ((x:ℝ) - ((n+1:ℕ):ℝ)^4) / (d:ℝ))) := by
    intro d hd
    rw [sum_Icc_int_cast]
    apply Finset.sum_congr rfl
    intro n hn
    have hjle : n + 1 ≤ N := by
      have := Finset.mem_range.mp hn
      omega
    have h4 : (n+1)^4 ≤ x := le_trans (Nat.pow_le_pow_left hjle 4) hN4
    have hcx : (((n+1:ℕ):ℤ):ℝ)^4 ≤ (x:ℝ) := by
      have h5 : (((n+1:ℕ):ℤ):ℝ) = ((n+1:ℕ):ℝ) := by push_cast; ring
      rw [h5]
      have h6 : ((n+1:ℕ):ℝ)^4 = (((n+1)^4 : ℕ) : ℝ) := by push_cast; ring
      rw [h6]
      exact_mod_cast h4
    rw [show (((n:ℤ)+1)) = (((n+1:ℕ)):ℤ) by simp]
    rw [heval d (((n+1:ℕ)):ℤ) hd hcx]
    rw [Int.natAbs_natCast]
    push_cast
    ring
  -- the smooth side as a single modulus sum
  have hmain : ∀ d : ℕ, 1 ≤ d →
      (∑ c ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
          ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + (c:ℤ)^4)),
            2 * Real.sqrt ((x:ℝ) - (c:ℝ)^4) / (d:ℝ))
        = (1/(d:ℝ)) * (2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
              * (2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4)))
            + (rho 0 d : ℝ)*(2*Real.sqrt (x:ℝ))) := by
    intro d hd
    have hdR : (d:ℝ) ≠ 0 := by positivity
    have hsq4 : ∀ j : ℤ, (((-j):ℤ):ℝ)^4 = ((j:ℤ):ℝ)^4 := by
      intro j; push_cast; ring
    have heven : ∀ j : ℤ,
        (fun c : ℤ => ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + (c:ℤ)^4)),
            2 * Real.sqrt ((x:ℝ) - (c:ℝ)^4) / (d:ℝ)) (-j)
          = (fun c : ℤ => ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + (c:ℤ)^4)),
            2 * Real.sqrt ((x:ℝ) - (c:ℝ)^4) / (d:ℝ)) j := by
      intro j
      simp only
      have hfil : ((Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + (((-j):ℤ))^4)))
          = ((Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + ((j:ℤ))^4))) := by
        apply Finset.filter_congr
        intro β _
        rw [show (((-j):ℤ))^4 = ((j:ℤ))^4 by ring]
      rw [hfil]
      apply Finset.sum_congr rfl
      intro β _
      rw [hsq4 j]
    have hsym := sum_Icc_neg_even (fun c : ℤ =>
        ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + (c:ℤ)^4)),
          2 * Real.sqrt ((x:ℝ) - (c:ℝ)^4) / (d:ℝ)) heven N
    rw [hsym]
    have heval0 : (∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + ((0:ℤ))^4)),
            2 * Real.sqrt ((x:ℝ) - ((0:ℤ):ℝ)^4) / (d:ℝ))
          = (rho 0 d : ℝ) * (2*Real.sqrt (x:ℝ) / (d:ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 2
      · rw [card_filter_dvd_eq_rho d 0 (by omega)]
        norm_num
      · norm_num
    rw [heval0, hconv d hd]
    have hsumdiv : (∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
            * (2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4) / (d:ℝ)))
        = ((∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
            * (2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4)))) / (d:ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsumdiv]
    have hdR : (d:ℝ) ≠ 0 := ne_of_gt (by positivity : (0:ℝ) < (d:ℝ))
    rw [show (1/(d:ℝ)) * (2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
            * (2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4))) + (rho 0 d : ℝ)*(2*Real.sqrt (x:ℝ)))
          = (2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
            * (2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4))) + (rho 0 d : ℝ)*(2*Real.sqrt (x:ℝ)))/(d:ℝ)
          from by ring]
    rw [eq_div_iff hdR]
    field_simp
    ring
  have hpt : ∀ d ∈ Finset.Icc 1 D,
      |(Md d x : ℝ)
        - (∑ c ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
            ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + (c:ℤ)^4)),
              2 * Real.sqrt ((x:ℝ) - (c:ℝ)^4) / (d:ℝ))|
      ≤ (1/(d:ℝ)) * (4*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)) + 2*(rho 0 d : ℝ)) := by
    intro d hdmem
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdmem).1
    have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
    have hAX : ∀ j ∈ Finset.range N,
        |(2*(Nat.sqrt (x - (j+1)^4) : ℝ) + 1)
          - 2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4)| ≤ 2 := by
      intro j hj
      have hjle : j + 1 ≤ N := by
        have := Finset.mem_range.mp hj
        omega
      have h1 : (j+1)^4 ≤ N^4 := Nat.pow_le_pow_left hjle 4
      have h2 : (((j+1:ℕ)):ℝ)^4 ≤ (x:ℝ) := by
        have h3 : (((j+1:ℕ)):ℝ)^4 = (((j+1)^4 : ℕ) : ℝ) := by push_cast; ring
        rw [h3]
        exact_mod_cast (le_trans h1 hN4)
      have h4 : 1 ≤ ((j+1:ℕ):ℤ) := by omega
      have h5 := abs_sqrtTerm_sub_sqrt x (((j+1:ℕ)):ℤ) h4 (by
        have : ((((j+1:ℕ)):ℤ):ℝ) = ((j+1:ℕ):ℝ) := by push_cast; ring
        rw [this]; exact h2)
      have h6 : ((((j+1:ℕ)):ℤ)).toNat = j+1 := Int.toNat_natCast (j+1)
      rw [h6] at h5
      have h7 : ((((j+1:ℕ)):ℤ):ℝ) = ((j+1:ℕ):ℝ) := by push_cast; ring
      rw [h7] at h5
      exact h5
    rw [hMd d, hmain d hd1, ← mul_sub]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(d:ℝ))]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hdiff : (2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
            * (2*(Nat.sqrt (x - (j+1)^4) : ℝ) + 1)) + 2*((Nat.sqrt x : ℕ):ℝ)*(rho 0 d:ℝ))
        - (2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
            * (2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4))) + (rho 0 d : ℝ)*(2*Real.sqrt (x:ℝ)))
        = 2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
              * ((2*(Nat.sqrt (x - (j+1)^4) : ℝ) + 1)
                  - 2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4)))
          + (rho 0 d : ℝ)*(2*((Nat.sqrt x : ℕ):ℝ) - 2*Real.sqrt (x:ℝ)) := by
      rw [show (2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
              * (2*(Nat.sqrt (x - (j+1)^4) : ℝ) + 1)) + 2*((Nat.sqrt x : ℕ):ℝ)*(rho 0 d:ℝ))
            - (2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
              * (2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4))) + (rho 0 d : ℝ)*(2*Real.sqrt (x:ℝ)))
          = (2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
              * (2*(Nat.sqrt (x - (j+1)^4) : ℝ) + 1))
            - 2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
              * (2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4))))
            + (2*((Nat.sqrt x : ℕ):ℝ)*(rho 0 d:ℝ) - (rho 0 d : ℝ)*(2*Real.sqrt (x:ℝ))) by ring]
      congr 1
      · rw [← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      · ring
    rw [hdiff]
    have h2 : |2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
            * ((2*(Nat.sqrt (x - (j+1)^4) : ℝ) + 1)
                - 2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4)))|
        ≤ 4*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have h3 : |∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
            * ((2*(Nat.sqrt (x - (j+1)^4) : ℝ) + 1)
                - 2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4))|
          ≤ ∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ) * 2 := by
        calc |∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
              * ((2*(Nat.sqrt (x - (j+1)^4) : ℝ) + 1)
                  - 2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4))|
            ≤ ∑ j ∈ Finset.range N, |(rho ((j+1)^2) d : ℝ)
              * ((2*(Nat.sqrt (x - (j+1)^4) : ℝ) + 1)
                  - 2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4))| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ) * 2 := by
              apply Finset.sum_le_sum
              intro j hj
              rw [abs_mul, abs_of_nonneg (by positivity)]
              exact mul_le_mul_of_nonneg_left (hAX j hj) (by positivity)
      have h4 : (∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ) * 2)
          = 2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [h4] at h3
      linarith [h3]
    have h5 : |(rho 0 d : ℝ)*(2*((Nat.sqrt x : ℕ):ℝ) - 2*Real.sqrt (x:ℝ))| ≤ 2*(rho 0 d : ℝ) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have h6 : |2*((Nat.sqrt x : ℕ):ℝ) - 2*Real.sqrt (x:ℝ)| ≤ 2 := by
        have h7 : 2*((Nat.sqrt x : ℕ):ℝ) - 2*Real.sqrt (x:ℝ) ≤ 0 := by linarith [hsqrtfloor2]
        rw [abs_of_nonpos h7]
        linarith [hsqrtfloor]
      have h8 : (0:ℝ) ≤ (rho 0 d : ℝ) := by positivity
      calc (rho 0 d : ℝ) * |2*((Nat.sqrt x : ℕ):ℝ) - 2*Real.sqrt (x:ℝ)|
          ≤ (rho 0 d : ℝ) * 2 := mul_le_mul_of_nonneg_left h6 h8
        _ = 2*(rho 0 d : ℝ) := by ring
    calc |2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
            * ((2*(Nat.sqrt (x - (j+1)^4) : ℝ) + 1)
                - 2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4)))
          + (rho 0 d : ℝ)*(2*((Nat.sqrt x : ℕ):ℝ) - 2*Real.sqrt (x:ℝ))|
        ≤ |2*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)
            * ((2*(Nat.sqrt (x - (j+1)^4) : ℝ) + 1)
                - 2*Real.sqrt ((x:ℝ) - (((j+1:ℕ)):ℝ)^4)))|
          + |(rho 0 d : ℝ)*(2*((Nat.sqrt x : ℕ):ℝ) - 2*Real.sqrt (x:ℝ))| := abs_add_le _ _
      _ ≤ 4*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)) + 2*(rho 0 d : ℝ) := by
          linarith [h2, h5]
  -- sum over the moduli
  have hsum1 : (∑ d ∈ Finset.Icc 1 D,
      (1/(d:ℝ)) * (4*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)) + 2*(rho 0 d : ℝ)))
      = 4*(∑ j ∈ Finset.range N, ∑ d ∈ Finset.Icc 1 D, (rho ((j+1)^2) d : ℝ)/(d:ℝ))
        + 2*(∑ d ∈ Finset.Icc 1 D, (rho 0 d : ℝ)/(d:ℝ)) := by
    have h1 : ∀ dd : ℕ, (1/(dd:ℝ)) * (4*(∑ j ∈ Finset.range N, (rho ((j+1)^2) dd : ℝ))
          + 2*(rho 0 dd : ℝ))
        = 4*(∑ j ∈ Finset.range N, (rho ((j+1)^2) dd : ℝ)/(dd:ℝ))
          + 2*((rho 0 dd : ℝ)/(dd:ℝ)) := by
      intro dd
      have h2 : (∑ j ∈ Finset.range N, (rho ((j+1)^2) dd : ℝ)/(dd:ℝ))
          = ((∑ j ∈ Finset.range N, (rho ((j+1)^2) dd : ℝ))/(dd:ℝ)) := by
        rw [Finset.sum_div]
      rw [h2]; ring
    rw [Finset.sum_congr rfl (fun dd _ => h1 dd), Finset.sum_add_distrib]
    rw [show (∑ dd ∈ Finset.Icc 1 D, 4 * (∑ j ∈ Finset.range N, (rho ((j+1)^2) dd : ℝ)/(dd:ℝ)))
        = 4 * (∑ dd ∈ Finset.Icc 1 D, ∑ j ∈ Finset.range N, (rho ((j+1)^2) dd : ℝ)/(dd:ℝ)) from by
      rw [Finset.mul_sum]]
    rw [show (∑ dd ∈ Finset.Icc 1 D, 2 * ((rho 0 dd : ℝ)/(dd:ℝ)))
        = 2 * (∑ dd ∈ Finset.Icc 1 D, (rho 0 dd : ℝ)/(dd:ℝ)) from by
      rw [Finset.mul_sum]]
    rw [Finset.sum_comm]
  have hbound : ∀ j ∈ Finset.range N,
      (∑ d ∈ Finset.Icc 1 D, (rho ((j+1)^2) d : ℝ)/(d:ℝ))
        ≤ Cρ*(Real.log (2*(D:ℝ)+2))^6 := by
    intro j _
    have h := hρ D (j+1)
    have hc4 : ∀ d : ℕ, rho ((j+1)^2) d
        = ({α : ZMod d | α ^ 2 + ((j+1 : ℕ) : ZMod d) ^ 4 = 0}).ncard := by
      intro d
      rw [rho]
      congr 1
      ext α
      simp only [Set.mem_ofPred_eq]
      rw [show (((j+1)^2 : ℕ) : ZMod d) = ((j+1 : ℕ) : ZMod d)^2 by push_cast; ring]
      ring
    calc (∑ d ∈ Finset.Icc 1 D, (rho ((j+1)^2) d : ℝ)/(d:ℝ))
        = ∑ d ∈ Finset.Icc 1 D,
            (({α : ZMod d | α ^ 2 + ((j+1 : ℕ) : ZMod d) ^ 4 = 0}).ncard : ℝ)/(d:ℝ) := by
          apply Finset.sum_congr rfl
          intro d _
          rw [hc4 d]
      _ ≤ Cρ*(Real.log (2*(D:ℝ)+2))^6 := h
  have hbound0 : (∑ d ∈ Finset.Icc 1 D, (rho 0 d : ℝ)/(d:ℝ))
      ≤ Cρ*(Real.log (2*(D:ℝ)+2))^6 := by
    have h := hρ D 0
    calc (∑ d ∈ Finset.Icc 1 D, (rho 0 d : ℝ)/(d:ℝ))
        = ∑ d ∈ Finset.Icc 1 D,
            (({α : ZMod d | α ^ 2 + ((0:ℕ) : ZMod d) ^ 4 = 0}).ncard : ℝ)/(d:ℝ) := by
          apply Finset.sum_congr rfl
          intro d _
          rw [rho]; norm_num
      _ ≤ Cρ*(Real.log (2*(D:ℝ)+2))^6 := h
  have hNle : (N:ℝ) ≤ (x:ℝ)^((1:ℝ)/4) := by
    have h : ((⌊(x:ℝ)^((1:ℝ)/4)⌋₊ : ℕ) : ℝ) ≤ (x:ℝ)^((1:ℝ)/4) :=
      Nat.floor_le (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (x:ℝ)) _)
    rw [hNdef]
    exact h
  have hNnn : (0:ℝ) ≤ (N:ℝ) := by positivity
  calc (∑ d ∈ Finset.Icc 1 D,
        |(Md d x : ℝ)
          - (∑ c ∈ Finset.Icc (-(⌊(x:ℝ)^((1:ℝ)/4)⌋₊ : ℤ)) (⌊(x:ℝ)^((1:ℝ)/4)⌋₊),
              ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d:ℤ) ∣ (β:ℤ)^2 + (c:ℤ)^4)),
                2 * Real.sqrt ((x:ℝ) - (c:ℝ)^4) / (d:ℝ))|)
      ≤ ∑ d ∈ Finset.Icc 1 D,
          (1/(d:ℝ)) * (4*(∑ j ∈ Finset.range N, (rho ((j+1)^2) d : ℝ)) + 2*(rho 0 d : ℝ)) :=
        Finset.sum_le_sum hpt
    _ = 4*(∑ j ∈ Finset.range N, ∑ d ∈ Finset.Icc 1 D, (rho ((j+1)^2) d : ℝ)/(d:ℝ))
        + 2*(∑ d ∈ Finset.Icc 1 D, (rho 0 d : ℝ)/(d:ℝ)) := hsum1
    _ ≤ 4*(∑ j ∈ Finset.range N, Cρ*(Real.log (2*(D:ℝ)+2))^6)
        + 2*(Cρ*(Real.log (2*(D:ℝ)+2))^6) := by
      have h1 := Finset.sum_le_sum hbound
      have h2 := hbound0
      linarith [h1, h2]
    _ = (4*(N:ℝ) + 2) * (Cρ*(Real.log (2*(D:ℝ)+2))^6) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ ≤ (7*Cρ + 7) * (x:ℝ)^((1:ℝ)/4) * (Real.log (2*(D:ℝ)+2))^6 := by
      set L : ℝ := (Real.log (2*(D:ℝ)+2))^6 with hLdef
      have hxq1 : (1:ℝ) ≤ (x:ℝ)^((1:ℝ)/4) := Real.one_le_rpow hx1 (by norm_num)
      have hstep1 : (4*(N:ℝ) + 2) * (Cρ*L) ≤ (4*(x:ℝ)^((1:ℝ)/4) + 2) * (Cρ*L) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith [hNle]
      have hstep2 : (4*(x:ℝ)^((1:ℝ)/4) + 2) * (Cρ*L) ≤ 6*(x:ℝ)^((1:ℝ)/4) * (Cρ*L) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith [hxq1]
      have h5 : (0:ℝ) ≤ (x:ℝ)^((1:ℝ)/4) * L := by positivity
      have hstep3 : 6*(x:ℝ)^((1:ℝ)/4) * (Cρ*L)
          ≤ (7*Cρ+7) * (x:ℝ)^((1:ℝ)/4) * L := by
        calc 6*(x:ℝ)^((1:ℝ)/4) * (Cρ*L) = (6*Cρ) * ((x:ℝ)^((1:ℝ)/4)*L) := by ring
          _ ≤ (7*Cρ+7) * ((x:ℝ)^((1:ℝ)/4)*L) :=
              mul_le_mul_of_nonneg_right (by linarith [hCρpos.le]) h5
          _ = (7*Cρ+7)*(x:ℝ)^((1:ℝ)/4)*L := by ring
      linarith [hstep1, hstep2, hstep3]
/-- The main-term discrepancy for a single modulus `d`: `|ncard_d − main_d| ≤ Σ_c ρ(c²;d)`. -/
lemma ncard_sub_main_d_le (x d : ℕ) (hd : 1 ≤ d) (hx : 1 ≤ x) :
    |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
        - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
            ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
              2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|
      ≤ ∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
          (rho (c.natAbs^2) d : ℝ) := by
  have hid := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_Ad_sub_Md_eq_fract x d hd hx
  rw [hid, abs_neg]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  apply Finset.sum_le_sum
  intro c _
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have h2 : ∀ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
      |(Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ)) - 1 / 2)
          + (Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ)) - 1 / 2)| ≤ 1 := by
    intro β _
    have h3 : |Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ)) - 1 / 2| ≤ 1/2 := by
      rw [abs_le]
      exact ⟨by linarith [Int.fract_nonneg ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ))],
             by linarith [Int.fract_lt_one ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ))]⟩
    have h4 : |Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ)) - 1 / 2| ≤ 1/2 := by
      rw [abs_le]
      exact ⟨by linarith [Int.fract_nonneg ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ))],
             by linarith [Int.fract_lt_one ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ))]⟩
    calc |(Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ)) - 1 / 2)
          + (Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ)) - 1 / 2)|
        ≤ |Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ)) - 1 / 2|
          + |Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ)) - 1 / 2| :=
          abs_add_le _ _
      _ ≤ 1 := by linarith
  calc (∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
        |(Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) - (β : ℝ)) / (d : ℝ)) - 1 / 2)
            + (Int.fract ((Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) + (β : ℝ)) / (d : ℝ)) - 1 / 2)|)
      ≤ ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)), (1:ℝ) :=
        Finset.sum_le_sum h2
    _ = (((Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4))).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (rho (c.natAbs^2) d : ℝ) := by
        rw [card_filter_dvd_eq_rho d c (by omega)]

end Submission


namespace Commons.NumberTheory.FriedlanderIwaniec

/-
## Remaining assembly (target theorem below)

Let `As d x := ({p : ℤ × ℤ | p.1^2 + p.2^4 ≤ (x:ℤ) ∧ (d:ℤ) ∣ p.1^2+p.2^4}).ncard`
(the first factor of the target's summand) and `Ms d x` the target's second factor.
Take `f` from `Commons.Analysis.ContDiff.exists_smooth_cutoff_infty x y` with
`y = ⌊D^{1/4} x^{13/16}⌋₊` (so `x ≤ y²`, `y ≤ x`, `0 ≤ f ≤ 1`, `f = 1` on `[0,x-y]`,
`f = 0` off `[0,x]`, and `|f^{(j)}| ≤ A_j y^{-j}`).  Then

  `Σ_{d≤D}|As d x − Ms d x|
     ≤ Σ_{d≤D}|As d x − Ad d x|                        (identification: = 0)
     + Σ_{d≤D}|Ad d x − AdF (fun n => f n) d x|          ((3.10), `Ad_smooth_diff_le`)
     + Σ_{d≤D}|AdF (fun n => f n) d x − MdF f d x|       ((3.13), `sieve_smooth_remainder_sqrt`)
     + Σ_{d≤D}|MdF f d x − Md d x|                       ((3.12), `MdF_sub_Md_sum_le`)
     + Σ_{d≤D}|Md d x − Ms d x|`                          (√-vs-floor, `≪ x^{1/4} log x`)

with each term `≪ D^{1/4} x^{9/16+1/100}` (the last because
`|2√(x−c⁴) − sqrtTerm x c| ≤ 2` for every `c`, and `Σ_{d≤D}Σ_{c} ρ(c²;d)/d ≪ x^{1/4} log D`). -/


/-- A `C^∞` cutoff with **uniform** derivative constants: `Auniv` works for every `x, y`. -/
lemma exists_cutoff_universal (J : ℕ) :
    ∃ Auniv : ℝ, 0 < Auniv ∧ ∀ x y : ℝ, 1 ≤ x → 1 ≤ y →
      ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ u, u ≤ x - y → f u = 1) ∧
        (∀ u, x ≤ u → f u = 0) ∧ (∀ u, 0 ≤ f u) ∧ (∀ u, f u ≤ 1) ∧
        (∀ j ≤ J, ∀ u ∈ Set.Icc 0 x, |iteratedDeriv j f u| ≤ Auniv * (y ^ j)⁻¹) := by
  obtain ⟨φ, hφc, hφ1, hφ0, hφnonneg, hφle1, hφbound⟩ :=
    Commons.Analysis.ContDiff.smoothTransition_cutoff_aux
  choose A hApos hAbound using hφbound
  refine ⟨∑ j ∈ Finset.range (J + 1), A j, ?_, ?_⟩
  · exact Finset.sum_pos (fun j _ => hApos j) ⟨0, Finset.mem_range.mpr (by omega)⟩
  · intro x y hx hy
    have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
    refine ⟨fun u => φ ((u - (x - y)) / y), by fun_prop, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      exact hφ1 _ (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hu) hypos.le)
    · intro u hu
      refine hφ0 _ ?_
      rw [le_div_iff₀ hypos]; linarith
    · intro u; exact hφnonneg _
    · intro u; exact hφle1 _
    · intro j hj u hu
      have hderiv : iteratedDeriv j (fun u : ℝ => φ ((u - (x - y)) / y)) u
          = (1 / y) ^ j * iteratedDeriv j φ ((u - (x - y)) / y) := by
        have h1 : (fun u : ℝ => φ ((u - (x - y)) / y))
            = fun u => (fun z : ℝ => φ (z * (1 / y))) (u - (x - y)) := by
          funext u; simp only [div_eq_mul_inv, one_mul]
        rw [h1, iteratedDeriv_comp_sub_const j (fun z : ℝ => φ (z * (1 / y))) (x - y)]
        have h2 : (fun z : ℝ => φ (z * (1 / y))) = fun z : ℝ => φ ((1 / y) * z) := by
          funext z; rw [mul_comm]
        rw [h2, iteratedDeriv_comp_const_mul (hφc.of_le (by exact_mod_cast le_top)) (1 / y)]
        simp only [div_eq_mul_inv, one_mul]
        ring_nf
      have hcoef : |(1 / y : ℝ) ^ j| = (y ^ j)⁻¹ := by
        rw [abs_pow, abs_of_pos (one_div_pos.2 hypos), one_div, inv_pow]
      calc |iteratedDeriv j (fun u : ℝ => φ ((u - (x - y)) / y)) u|
          = (y ^ j)⁻¹ * |iteratedDeriv j φ ((u - (x - y)) / y)| := by
            rw [hderiv, abs_mul, hcoef]
        _ ≤ (y ^ j)⁻¹ * A j := mul_le_mul_of_nonneg_left (hAbound j _) (by positivity)
        _ ≤ (y ^ j)⁻¹ * (∑ i ∈ Finset.range (J + 1), A i) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Finset.single_le_sum (fun i _ => (hApos i).le)
              (Finset.mem_range.mpr (by omega))
        _ = (∑ i ∈ Finset.range (J + 1), A i) * (y ^ j)⁻¹ := by ring

/-- The logarithmic factor is bounded (up to an explicit constant) by `x^{1/100}`. -/
lemma log_six_le (D x : ℕ) (hx : 1 ≤ x) (hD : D ≤ ⌊(x:ℝ)^((3:ℝ)/4)⌋₊) :
    (Real.log (2*(D:ℝ)+2))^6 ≤ 601^6 * (x:ℝ)^((1:ℝ)/100) := by
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hD34 : (D:ℝ) ≤ (x:ℝ)^((3:ℝ)/4) :=
    le_trans (by exact_mod_cast hD) (Nat.floor_le (by positivity))
  have h2 : (2*(D:ℝ)+2) ≤ 4*(x:ℝ)^((3:ℝ)/4) := by
    have h4 : (1:ℝ) ≤ (x:ℝ)^((3:ℝ)/4) := Real.one_le_rpow hx1 (by norm_num)
    linarith
  have h2pos : (0:ℝ) < 2*(D:ℝ)+2 := by
    have : (0:ℝ) ≤ (D:ℝ) := by positivity
    linarith
  have hlog : Real.log (2*(D:ℝ)+2) ≤ Real.log (4*(x:ℝ)^((3:ℝ)/4)) :=
    Real.log_le_log h2pos h2
  have hsplit : Real.log (4*(x:ℝ)^((3:ℝ)/4)) = Real.log 4 + (3/4)*Real.log (x:ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity : ((x:ℝ)^((3:ℝ)/4)) ≠ 0),
        Real.log_rpow (by positivity : (0:ℝ) < (x:ℝ))]
  have hlogx : Real.log (x:ℝ) ≤ 600 * (x:ℝ)^((1:ℝ)/600) := by
    have h1 := Real.log_le_rpow_div (by linarith : (0:ℝ) ≤ (x:ℝ))
      (by norm_num : (0:ℝ) < 1/600)
    have h2 : (x:ℝ) ^ ((1:ℝ)/600) / (1/600) = 600 * (x:ℝ)^((1:ℝ)/600) := by ring
    linarith [h1, h2.le, h2.ge]
  have hlog4 : Real.log 4 ≤ 151 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    linarith
  have h601 : Real.log (2*(D:ℝ)+2) ≤ 601 * (x:ℝ)^((1:ℝ)/600) := by
    have hx600 : (1:ℝ) ≤ (x:ℝ)^((1:ℝ)/600) := Real.one_le_rpow hx1 (by norm_num)
    rw [hsplit] at hlog
    linarith
  have hlogpos : (0:ℝ) ≤ Real.log (2*(D:ℝ)+2) := by
    apply Real.log_nonneg
    have h1 : (0:ℝ) ≤ (D:ℝ) := by positivity
    linarith
  calc (Real.log (2*(D:ℝ)+2))^6 ≤ (601 * (x:ℝ)^((1:ℝ)/600))^6 :=
        pow_le_pow_left₀ hlogpos h601 6
    _ = 601^6 * (x:ℝ)^((1:ℝ)/100) := by
        have h3 : ((x:ℝ)^((1:ℝ)/600))^6 = (x:ℝ)^((1:ℝ)/100) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (x:ℝ))]
          norm_num
        rw [mul_pow, h3]

theorem X2Y4_sieve_remainder_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (x D : ℕ), 1 ≤ x → 1 ≤ D → D ≤ ⌊(x : ℝ) ^ ((3 : ℝ) / 4)⌋₊ →
      (∑ d ∈ Finset.Icc 1 D,
        |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
          - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
              ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
        ≤ C * (D : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((9 : ℝ) / 16) * (x : ℝ) ^ ((1 : ℝ) / 100) := by
  obtain ⟨Cw, hCw, hweighted⟩ := Submission.weighted_remainder_le (1/400) (by norm_num) (by norm_num)
  obtain ⟨C10, hC10, h310⟩ := Submission.Ad_smooth_diff_le (1/400) (by norm_num)
  obtain ⟨C12, hC12, h312⟩ := Submission.MdF_sub_Md_sum_le
  obtain ⟨Cb, hCb, hBmd⟩ := Submission.Md_sub_main_term_sum_le
  obtain ⟨Cel, hCel, hel⟩ := Submission.ncard_sub_main_term_le
  obtain ⟨Auniv, hAuniv, hcut⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.exists_cutoff_universal (Submission.Jeps (1/400))
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 2 + Cw*(Auniv+1) + C10 + C12 + Cb + Cel := ⟨_, rfl⟩
  have hA1 : (0:ℝ) ≤ Auniv + 1 := by linarith
  have hCwA0 : (0:ℝ) ≤ Cw*(Auniv+1) := mul_nonneg hCw.le hA1
  have hC10leP : C10 ≤ P := by rw [hP]; linarith [hC12.le, hCb.le, hCel.le, hCwA0]
  have hC12leP : C12 ≤ P := by rw [hP]; linarith [hC10.le, hCb.le, hCel.le, hCwA0]
  have hCbleP : Cb ≤ P := by rw [hP]; linarith [hC10.le, hC12.le, hCel.le, hCwA0]
  have hCelleP : Cel ≤ P := by rw [hP]; linarith [hC10.le, hC12.le, hCb.le, hCwA0]
  have hCwAleP : Cw*(Auniv+1) ≤ P := by rw [hP]; linarith [hC10.le, hC12.le, hCb.le, hCel.le]
  have hP2 : (2:ℝ) ≤ P := by
    rw [hP]; linarith [hC10.le, hC12.le, hCb.le, hCel.le, hCwA0]
  have hPpos : (0:ℝ) < P := by linarith
  have hP1 : (1:ℝ) ≤ P := by linarith
  have hP8nn : (0:ℝ) ≤ P^8 := pow_nonneg hPpos.le 8
  have hP8_1 : (1:ℝ) ≤ P^8 := one_le_pow₀ hP1
  have hP7 : (6:ℝ) ≤ P^7 := by
    calc (6:ℝ) ≤ (2:ℝ)^7 := by norm_num
      _ ≤ P^7 := pow_le_pow_left₀ (by norm_num) hP2 7
  have h2P7 : (2:ℝ) ≤ P^7 := le_trans (by norm_num : (2:ℝ) ≤ 6) hP7
  have h4P7 : (4:ℝ) ≤ P^7 := le_trans (by norm_num : (4:ℝ) ≤ 6) hP7
  have h601nn : (0:ℝ) ≤ (601:ℝ)^6 := by norm_num
  have h601_1 : (1:ℝ) ≤ (601:ℝ)^6 := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 601)
  obtain ⟨BIG, hBIG⟩ : ∃ B : ℝ, B = 2^1000 * P^8 * 601^6 := ⟨_, rfl⟩
  have hBIGpos : 0 < BIG := by
    rw [hBIG]
    exact mul_pos (mul_pos (pow_pos (by norm_num : (0:ℝ) < 2) 1000) (pow_pos hPpos 8))
      (pow_pos (by norm_num : (0:ℝ) < 601) 6)
  have hBIGnn : (0:ℝ) ≤ BIG := le_of_lt hBIGpos
  have hP8toBIG : P^8 ≤ BIG := by
    rw [hBIG]
    calc P^8 ≤ P^8 * 601^6 := le_mul_of_one_le_right hP8nn h601_1
      _ ≤ 2^1000 * P^8 * 601^6 :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hP8nn (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))) h601nn
  have h601toBIG : ∀ k : ℝ, 0 ≤ k → k ≤ P^8 → k * 601^6 ≤ BIG := by
    intro k hk hkP
    calc k * 601^6 ≤ P^8 * 601^6 := mul_le_mul_of_nonneg_right hkP h601nn
      _ ≤ 2^1000 * P^8 * 601^6 :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hP8nn (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))) h601nn
      _ = BIG := by rw [hBIG]
  have hrelP : ∀ c k : ℝ, 0 ≤ c → c ≤ P^7 → 0 ≤ k → k ≤ P → c * k ≤ P^8 := by
    intro c k hc hcP7 hk hkP
    calc c * k ≤ P^7 * P := mul_le_mul hcP7 hkP hk (le_of_lt (pow_pos hPpos 7))
      _ = P^8 := by ring
  have hleBIG : ∀ c k : ℝ, 0 ≤ c → c ≤ P^7 → 0 ≤ k → k ≤ P → c * k ≤ BIG :=
    fun c k hc hcP7 hk hkP => le_trans (hrelP c k hc hcP7 hk hkP) hP8toBIG
  have hleBIG601 : ∀ c k : ℝ, 0 ≤ c → c ≤ P^7 → 0 ≤ k → k ≤ P → c * k * 601^6 ≤ BIG := by
    intro c k hc hcP7 hk hkP
    exact h601toBIG (c*k) (mul_nonneg hc hk) (hrelP c k hc hcP7 hk hkP)
  have hP8_of_P : ∀ c : ℝ, 0 ≤ c → c ≤ P → c ≤ P^8 := by
    intro c hc hcP
    calc c ≤ P := hcP
      _ = P^1 := by ring
      _ ≤ P^8 := pow_le_pow_right₀ hP1 (by norm_num)
  have hCelP8 : Cel ≤ P^8 := hP8_of_P Cel hCel.le hCelleP
  have hKA : (3:ℝ)*C10 ≤ BIG := hleBIG 3 C10 (by norm_num) (le_trans (by norm_num : (3:ℝ) ≤ 6) hP7) hC10.le hC10leP
  have hKB : (6:ℝ)*(Cw*(Auniv+1)) ≤ BIG := hleBIG 6 _ (by norm_num) hP7 hCwA0 hCwAleP
  have hKC : (4:ℝ)*C12*601^6 ≤ BIG := hleBIG601 4 C12 (by norm_num) h4P7 hC12.le hC12leP
  have hKD : Cb*601^6 ≤ BIG := by
    have h := hleBIG601 1 Cb (by norm_num) (one_le_pow₀ hP1) hCb.le hCbleP
    simpa using h
  have hKE : (4:ℝ)*Cel*601^6 ≤ BIG := hleBIG601 4 Cel (by norm_num) h4P7 hCel.le hCelleP
  -- the log factor
  have hlog6le : ∀ D x : ℕ, 1 ≤ x → D ≤ ⌊(x : ℝ) ^ ((3 : ℝ) / 4)⌋₊ →
      (Real.log (2*(D:ℝ)+2))^6 ≤ 601^6 * (x:ℝ)^((1:ℝ)/100) :=
    fun D x hx hD => Commons.NumberTheory.FriedlanderIwaniec.log_six_le D x hx hD
  -- the elementary branch bound (used when `D^{3/4} ≤ x^{5/16}`)
  have habs : ∀ K : ℝ, 0 ≤ K → K ≤ P^8 → ∀ x D : ℕ, 1 ≤ x → 1 ≤ D →
      D ≤ ⌊(x : ℝ) ^ ((3 : ℝ) / 4)⌋₊ → (D:ℝ)^((3:ℝ)/4) ≤ (x:ℝ)^((5:ℝ)/16) →
      K * (x:ℝ)^((1:ℝ)/4) * (D:ℝ) * (Real.log (2*(D:ℝ)+2))^6
        ≤ BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100) := by
    intro K hK hKP x D hx hD hD34 hDq
    have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
    have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    have hxnn : (0:ℝ) ≤ (x:ℝ) := by positivity
    have hDnn : (0:ℝ) ≤ (D:ℝ) := by positivity
    have hxq : (0:ℝ) ≤ (x:ℝ)^((1:ℝ)/4) := Real.rpow_nonneg hxnn _
    have hDq0 : (0:ℝ) ≤ (D:ℝ)^((1:ℝ)/4) := Real.rpow_nonneg hDnn _
    have hx516 : (0:ℝ) ≤ (x:ℝ)^((5:ℝ)/16) := Real.rpow_nonneg hxnn _
    have hx100 : (0:ℝ) ≤ (x:ℝ)^((1:ℝ)/100) := Real.rpow_nonneg hxnn _
    have hlog := hlog6le D x hx hD34
    have hDsplit : (D:ℝ) = (D:ℝ)^((1:ℝ)/4) * (D:ℝ)^((3:ℝ)/4) := by
      rw [← Real.rpow_add (by linarith : (0:ℝ) < (D:ℝ))]; norm_num
    have hxpow : (x:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16) = (x:ℝ)^((9:ℝ)/16) := by
      rw [← Real.rpow_add (by linarith : (0:ℝ) < (x:ℝ))]; norm_num
    have hD2 : (D:ℝ) ≤ (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16) := by
      nth_rewrite 1 [hDsplit]
      exact mul_le_mul_of_nonneg_left hDq hDq0
    have s1 : K * (x:ℝ)^((1:ℝ)/4) * (D:ℝ) * (Real.log (2*(D:ℝ)+2))^6
        ≤ K * (x:ℝ)^((1:ℝ)/4) * (D:ℝ) * (601^6 * (x:ℝ)^((1:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (mul_nonneg hK hxq) hDnn)
    have s2 : K * (x:ℝ)^((1:ℝ)/4) * (D:ℝ) * (601^6 * (x:ℝ)^((1:ℝ)/100))
        ≤ K * (x:ℝ)^((1:ℝ)/4) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16))
            * (601^6 * (x:ℝ)^((1:ℝ)/100)) := by
      have h601x : (0:ℝ) ≤ 601^6 * (x:ℝ)^((1:ℝ)/100) := mul_nonneg h601nn hx100
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD2 (mul_nonneg hK hxq)) h601x
    have hK601 : K * 601^6 ≤ BIG := h601toBIG K hK hKP
    have s3 : K * (x:ℝ)^((1:ℝ)/4) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16))
            * (601^6 * (x:ℝ)^((1:ℝ)/100))
        ≤ BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100) := by
      have hWnn : (0:ℝ) ≤ (D:ℝ)^((1:ℝ)/4) * ((x:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100) :=
        mul_nonneg (mul_nonneg hDq0 (mul_nonneg hxq hx516)) hx100
      calc K * (x:ℝ)^((1:ℝ)/4) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16))
              * (601^6 * (x:ℝ)^((1:ℝ)/100))
          = (K * 601^6) * ((D:ℝ)^((1:ℝ)/4) * ((x:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16))
              * (x:ℝ)^((1:ℝ)/100)) := by ac_rfl
        _ ≤ BIG * ((D:ℝ)^((1:ℝ)/4) * ((x:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16))
              * (x:ℝ)^((1:ℝ)/100)) := mul_le_mul_of_nonneg_right hK601 hWnn
        _ = BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100) := by
            rw [hxpow]; ac_rfl
    exact le_trans (le_trans s1 s2) s3
  refine ⟨8*BIG, by positivity, ?_⟩
  intro x D hx hD hD34
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hx0 : (0:ℝ) < (x:ℝ) := by linarith
  have hxnn : (0:ℝ) ≤ (x:ℝ) := le_of_lt hx0
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDnn : (0:ℝ) ≤ (D:ℝ) := by positivity
  have hD34' : (D:ℝ) ≤ (x:ℝ)^((3:ℝ)/4) :=
    le_trans (by exact_mod_cast hD34) (Nat.floor_le (by positivity))
  have hfin : BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100)
      ≤ (8*BIG) * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100) := by
    have hW : (0:ℝ) ≤ (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100) := by positivity
    calc BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100)
        = BIG * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100)) := by ac_rfl
      _ ≤ (8*BIG) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100)) :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hBIGnn (by norm_num : (1:ℝ) ≤ 8)) hW
      _ = (8*BIG) * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100) := by ac_rfl
  by_cases hxs : (x:ℝ) ≤ 2^800
  · -- ### branch 1: `x` small, crude bound
    have hx14 : (x:ℝ)^((1:ℝ)/4) ≤ (2:ℝ)^200 := by
      calc (x:ℝ)^((1:ℝ)/4) ≤ ((2:ℝ)^800)^((1:ℝ)/4) :=
            Real.rpow_le_rpow (by positivity) hxs (by norm_num)
        _ = (2:ℝ)^200 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (2:ℝ))]
            norm_num
    have hD2600 : (D:ℝ) ≤ (2:ℝ)^600 := by
      calc (D:ℝ) ≤ (x:ℝ)^((3:ℝ)/4) := hD34'
        _ ≤ ((2:ℝ)^800)^((3:ℝ)/4) := Real.rpow_le_rpow (by positivity) hxs (by norm_num)
        _ = (2:ℝ)^600 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (2:ℝ))]
            norm_num
    have h2pow : (2:ℝ)^200 * (2:ℝ)^600 = (2:ℝ)^800 := by rw [← pow_add]
    have h2le : (2:ℝ)^800 ≤ 2^1000 :=
      pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by norm_num : 800 ≤ 1000)
    have hlog := hlog6le D x hx hD34
    have hq1 : (1:ℝ) ≤ (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) := by
      have ha : (1:ℝ) ≤ (D:ℝ)^((1:ℝ)/4) := Real.one_le_rpow hD1 (by norm_num)
      have hb : (1:ℝ) ≤ (x:ℝ)^((9:ℝ)/16) := Real.one_le_rpow hx1 (by norm_num)
      have h := mul_le_mul ha hb (by norm_num : (0:ℝ) ≤ 1)
        (le_of_lt (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < (D:ℝ)) _))
      simpa using h
    have hmid : Cel * (x:ℝ)^((1:ℝ)/4) * (D:ℝ) ≤ Cel * (2:ℝ)^200 * (2:ℝ)^600 := by
      have h2 : Cel * (x:ℝ)^((1:ℝ)/4) ≤ Cel * (2:ℝ)^200 :=
        mul_le_mul_of_nonneg_left hx14 hCel.le
      calc Cel * (x:ℝ)^((1:ℝ)/4) * (D:ℝ) ≤ Cel * (2:ℝ)^200 * (D:ℝ) :=
            mul_le_mul_of_nonneg_right h2 hDnn
        _ ≤ Cel * (2:ℝ)^200 * (2:ℝ)^600 := mul_le_mul_of_nonneg_left hD2600 (by positivity)
    have hmid2 : Cel * (2:ℝ)^200 * (2:ℝ)^600 = Cel * (2:ℝ)^800 := by
      rw [mul_assoc, h2pow]
    have hconst800 : Cel * (2:ℝ)^800 * 601^6 ≤ BIG := by
      have h1 : Cel * (2:ℝ)^800 ≤ P^8 * (2:ℝ)^800 := mul_le_mul_of_nonneg_right hCelP8 (by positivity)
      have h2 : P^8 * (2:ℝ)^800 ≤ 2^1000 * P^8 := by
        rw [mul_comm (P^8) ((2:ℝ)^800)]
        exact mul_le_mul_of_nonneg_right h2le hP8nn
      calc Cel * (2:ℝ)^800 * 601^6 ≤ P^8 * (2:ℝ)^800 * 601^6 := mul_le_mul_of_nonneg_right h1 h601nn
        _ ≤ 2^1000 * P^8 * 601^6 := mul_le_mul_of_nonneg_right h2 h601nn
        _ = BIG := by rw [hBIG]
    have s1 : Cel * (x:ℝ)^((1:ℝ)/4) * (D:ℝ) * (Real.log (2*(D:ℝ)+2))^6
        ≤ Cel * (x:ℝ)^((1:ℝ)/4) * (D:ℝ) * (601^6 * (x:ℝ)^((1:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (mul_nonneg hCel.le (Real.rpow_nonneg hxnn _)) hDnn)
    have s2 : Cel * (x:ℝ)^((1:ℝ)/4) * (D:ℝ) * (601^6 * (x:ℝ)^((1:ℝ)/100))
        ≤ Cel * (2:ℝ)^200 * (2:ℝ)^600 * (601^6 * (x:ℝ)^((1:ℝ)/100)) :=
      mul_le_mul_of_nonneg_right hmid (by positivity)
    have h1 : Cel * (2:ℝ)^200 * (2:ℝ)^600 * 601^6 ≤ BIG * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) := by
      calc Cel * (2:ℝ)^200 * (2:ℝ)^600 * 601^6 ≤ BIG := by
            rw [hmid2]; exact hconst800
        _ ≤ BIG * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) :=
            le_mul_of_one_le_right hBIGnn hq1
    have s3 : Cel * (2:ℝ)^200 * (2:ℝ)^600 * (601^6 * (x:ℝ)^((1:ℝ)/100))
        ≤ BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100) := by
      have e : Cel * (2:ℝ)^200 * (2:ℝ)^600 * (601^6 * (x:ℝ)^((1:ℝ)/100))
          = (Cel * (2:ℝ)^200 * (2:ℝ)^600 * 601^6) * (x:ℝ)^((1:ℝ)/100) := by ac_rfl
      rw [e]
      calc (Cel * (2:ℝ)^200 * (2:ℝ)^600 * 601^6) * (x:ℝ)^((1:ℝ)/100)
          ≤ (BIG * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16))) * (x:ℝ)^((1:ℝ)/100) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100) := by ac_rfl
    exact le_trans (le_trans (le_trans (hel x D hx hD) (le_trans s1 s2)) s3) hfin
  · push_neg at hxs
    by_cases hDc : (D:ℝ) ≤ (x:ℝ)^((5:ℝ)/12)
    · -- ### branch 2: `D` small, crude bound
      have hDq : (D:ℝ)^((3:ℝ)/4) ≤ (x:ℝ)^((5:ℝ)/16) := by
        calc (D:ℝ)^((3:ℝ)/4) ≤ ((x:ℝ)^((5:ℝ)/12))^((3:ℝ)/4) :=
              Real.rpow_le_rpow (by positivity) hDc (by norm_num)
          _ = (x:ℝ)^((5:ℝ)/16) := by
              rw [← Real.rpow_mul (x := (x:ℝ)) (by positivity)]
              norm_num
      exact le_trans (le_trans (hel x D hx hD) (habs Cel hCel.le hCelP8 x D hx hD hD34 hDq)) hfin
    · -- ### branch 3: smoothing
      push_neg at hDc
      have hD0r : (0:ℝ) < (D:ℝ) := by exact_mod_cast hD
      -- `x^e ≥ 2` for `e ≥ 1/800`
      have hXge2 : ∀ e : ℝ, (1:ℝ)/800 ≤ e → (2:ℝ) ≤ (x:ℝ)^e := by
        intro e he
        have h0 : ((2:ℝ)^800)^((1:ℝ)/800) = (2:ℝ) := by
          rw [← Real.rpow_natCast (2:ℝ) 800, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (2:ℝ))]
          norm_num
        have h1 : ((2:ℝ)^800)^((1:ℝ)/800) ≤ (x:ℝ)^((1:ℝ)/800) :=
          Real.rpow_le_rpow (by positivity) (le_of_lt hxs) (by norm_num)
        have h2 : (x:ℝ)^((1:ℝ)/800) ≤ (x:ℝ)^e := Real.rpow_le_rpow_of_exponent_le hx1 he
        linarith [h0, h1, h2]
      have hXq : (4:ℝ) ≤ (x:ℝ)^((1:ℝ)/400) := by
        have h1 : (2:ℝ) ≤ (x:ℝ)^((1:ℝ)/800) := hXge2 _ le_rfl
        have h2 : (2:ℝ)^2 ≤ ((x:ℝ)^((1:ℝ)/800))^2 := pow_le_pow_left₀ (by norm_num) h1 2
        have h3 : ((x:ℝ)^((1:ℝ)/800))^2 = (x:ℝ)^((1:ℝ)/400) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (x:ℝ))]
          norm_num
        linarith [h2, h3.le, h3.ge]
      have hJp : (1:ℝ) ≤ (Submission.Jeps (1/400) : ℝ) := by
        have h : 1 ≤ Submission.Jeps (1/400) := by
          have := Submission.Jeps_ge_two (1/400); omega
        exact_mod_cast h
      have hJpos : (0:ℝ) < (Submission.Jeps (1/400) : ℝ) := by linarith
      have hδle : (Submission.Jeps (1/400) : ℝ)⁻¹ ≤ 1/400 := by
        rw [inv_le_iff_one_le_mul₀ hJpos]
        have hmul : (2:ℝ) ≤ (Submission.Jeps (1/400) : ℝ) * (1/400) :=
          Submission.Jeps_mul_ge (1/400) (by norm_num)
        linarith [hmul]
      have hδnn : (0:ℝ) ≤ (Submission.Jeps (1/400) : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hJpos)
      -- the smoothing scale `z` and `y`
      set z : ℝ := (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((13:ℝ)/16 - (1:ℝ)/400) with hzdef
      set y : ℕ := ⌊z⌋₊ + 1 with hydef
      have hz_up : z ≤ (x:ℝ)^((399:ℝ)/400) := by
        have h1 : (D:ℝ)^((1:ℝ)/4) ≤ (x:ℝ)^((3:ℝ)/16) := by
          have h2 : (D:ℝ)^((1:ℝ)/4) ≤ ((x:ℝ)^((3:ℝ)/4))^((1:ℝ)/4) :=
            Real.rpow_le_rpow (by positivity) hD34' (by norm_num)
          have h3 : ((x:ℝ)^((3:ℝ)/4))^((1:ℝ)/4) = (x:ℝ)^((3:ℝ)/16) := by
            rw [← Real.rpow_mul (x := (x:ℝ)) (by positivity)]
            norm_num
          linarith [h2, h3.le, h3.ge]
        rw [hzdef]
        calc (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((13:ℝ)/16 - (1:ℝ)/400)
            ≤ (x:ℝ)^((3:ℝ)/16) * (x:ℝ)^((13:ℝ)/16 - (1:ℝ)/400) :=
              mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hxnn _)
          _ = (x:ℝ)^((399:ℝ)/400) := by
              rw [← Real.rpow_add hx0]
              norm_num
      have hz_lo : (x:ℝ)^((11:ℝ)/12 - (1:ℝ)/400) ≤ z := by
        have h1 : (x:ℝ)^((5:ℝ)/48) ≤ (D:ℝ)^((1:ℝ)/4) := by
          have h2 : ((x:ℝ)^((5:ℝ)/12))^((1:ℝ)/4) ≤ (D:ℝ)^((1:ℝ)/4) :=
            Real.rpow_le_rpow (by positivity) (le_of_lt hDc) (by norm_num)
          have h3 : ((x:ℝ)^((5:ℝ)/12))^((1:ℝ)/4) = (x:ℝ)^((5:ℝ)/48) := by
            rw [← Real.rpow_mul (x := (x:ℝ)) (by positivity)]
            norm_num
          linarith [h2, h3.le, h3.ge]
        rw [hzdef]
        calc (x:ℝ)^((11:ℝ)/12 - (1:ℝ)/400)
            = (x:ℝ)^((5:ℝ)/48) * (x:ℝ)^((13:ℝ)/16 - (1:ℝ)/400) := by
              rw [← Real.rpow_add hx0]
              norm_num
          _ ≤ (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((13:ℝ)/16 - (1:ℝ)/400) :=
              mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hxnn _)
      have hz2 : (2:ℝ) ≤ z := by
        have h1 : (2:ℝ) ≤ (x:ℝ)^((11:ℝ)/12 - (1:ℝ)/400) := hXge2 _ (by norm_num)
        linarith
      have hz0 : (0:ℝ) < z := by linarith
      have hy1 : 1 ≤ y := by rw [hydef]; omega
      have hyR1 : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy1
      have hy_ge_z : z ≤ (y:ℝ) := by
        rw [hydef]; push_cast
        exact le_of_lt (Nat.lt_floor_add_one z)
      have hy_le_2z : (y:ℝ) ≤ 2*z := by
        rw [hydef]; push_cast
        have h := Nat.floor_le (le_of_lt hz0)
        linarith
      have hz_q : z ≤ (x:ℝ)/4 := by
        have h1 : (x:ℝ)^((399:ℝ)/400) = (x:ℝ)^(1:ℝ) * (x:ℝ)^(-((1:ℝ)/400)) := by
          rw [← Real.rpow_add hx0]; norm_num
        have h2 : (x:ℝ)^(-((1:ℝ)/400)) ≤ 1/4 := by
          rw [Real.rpow_neg hxnn, show (1:ℝ)/4 = ((4:ℝ))⁻¹ by norm_num]
          rw [inv_le_inv₀ (Real.rpow_pos_of_pos hx0 _) (by norm_num : (0:ℝ) < 4)]
          exact hXq
        have h3 : (x:ℝ)^(1:ℝ) * (x:ℝ)^(-((1:ℝ)/400)) ≤ (x:ℝ) * (1/4) := by
          rw [Real.rpow_one]
          exact mul_le_mul_of_nonneg_left h2 hxnn
        calc z ≤ (x:ℝ)^((399:ℝ)/400) := hz_up
          _ = (x:ℝ)^(1:ℝ) * (x:ℝ)^(-((1:ℝ)/400)) := h1
          _ ≤ (x:ℝ) * (1/4) := h3
          _ = (x:ℝ)/4 := by ring
      have hy_le_halfx : (y:ℝ) ≤ (x:ℝ)/2 := by linarith
      have hy_le_x : y ≤ x := by
        have h1 : (y:ℝ) ≤ (x:ℝ) := by
          have ha : (y:ℝ) ≤ (x:ℝ)/2 := hy_le_halfx
          have hb : (x:ℝ)/2 ≤ (x:ℝ) := div_le_self hxnn (by norm_num)
          linarith only [ha, hb]
        exact_mod_cast h1
      have hy_div : y ≤ x / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
        have h1 : (y:ℝ)*2 ≤ (x:ℝ) := by linarith
        exact_mod_cast h1
      have hxy2 : x ≤ y ^ 2 := by
        have h1 : (x:ℝ) ≤ (y:ℝ)^2 := by
          have h2 : ((x:ℝ)^((11:ℝ)/12 - (1:ℝ)/400))^2 ≤ (y:ℝ)^2 :=
            pow_le_pow_left₀ (Real.rpow_nonneg hxnn _) (le_trans hz_lo hy_ge_z) 2
          have h3 : ((x:ℝ)^((11:ℝ)/12 - (1:ℝ)/400))^2 = (x:ℝ)^(((11:ℝ)/12 - (1:ℝ)/400)*2) := by
            rw [sq, ← Real.rpow_add hx0]
            congr 1
            ring
          have h4 : (x:ℝ)^(1:ℝ) ≤ (x:ℝ)^(((11:ℝ)/12 - (1:ℝ)/400)*2) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
          have h5 : (x:ℝ)^(1:ℝ) = (x:ℝ) := Real.rpow_one _
          calc (x:ℝ) = (x:ℝ)^(1:ℝ) := h5.symm
            _ ≤ (x:ℝ)^(((11:ℝ)/12 - (1:ℝ)/400)*2) := h4
            _ = ((x:ℝ)^((11:ℝ)/12 - (1:ℝ)/400))^2 := h3.symm
            _ ≤ (y:ℝ)^2 := h2
        exact_mod_cast h1
      -- ### the split threshold `D₁`
      set D₁ : ℕ := ⌈(y:ℝ) * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹))⌉₊ with hD₁def
      have hD₁_ge : (y:ℝ) * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹)) ≤ (D₁:ℝ) := by
        rw [hD₁def]; exact Nat.le_ceil _
      have hyXfrac : (y:ℝ) * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹))
          ≤ 2 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16)) := by
        have hz' : z * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹))
            = (D:ℝ)^((1:ℝ)/4)
              * (x:ℝ)^((5:ℝ)/16 - (1:ℝ)/400 - (Submission.Jeps (1/400) : ℝ)⁻¹) := by
          have hexp : ((13:ℝ)/16 - (1:ℝ)/400) + (-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹))
              = (5:ℝ)/16 - (1:ℝ)/400 - (Submission.Jeps (1/400) : ℝ)⁻¹ := by ring
          rw [hzdef, mul_assoc, ← Real.rpow_add hx0, hexp]
        have hle1 : z * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹))
            ≤ (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16) := by
          rw [hz']
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
            (Real.rpow_nonneg hDnn _)
        calc (y:ℝ) * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹))
            ≤ (2*z) * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹)) :=
              mul_le_mul_of_nonneg_right hy_le_2z (Real.rpow_nonneg hxnn _)
          _ = 2 * (z * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹))) := by ring
          _ ≤ 2 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16)) :=
              mul_le_mul_of_nonneg_left hle1 (by norm_num)
      have hD₁_ub : (D₁:ℝ) ≤ 4 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16)) := by
        have hceil : (D₁:ℝ) < (y:ℝ) * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹)) + 1 := by
          rw [hD₁def]
          exact Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg y) (Real.rpow_nonneg hxnn _))
        have hone : (1:ℝ) ≤ 2 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16)) := by
          have h1 : (1:ℝ) ≤ (D:ℝ)^((1:ℝ)/4) := Real.one_le_rpow hD1 (by norm_num)
          have h2 : (1:ℝ) ≤ (x:ℝ)^((5:ℝ)/16) := Real.one_le_rpow hx1 (by norm_num)
          have h3 : (1:ℝ) ≤ (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16) := by
            have h := mul_le_mul h1 h2 (by norm_num : (0:ℝ) ≤ 1)
              (le_of_lt (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < (D:ℝ)) _))
            simpa using h
          linarith
        linarith [hceil, hyXfrac, hone]
      have hD₁_le_34 : (D₁:ℝ) ≤ (x:ℝ)^((3:ℝ)/4) := by
        have h1 : (D:ℝ)^((1:ℝ)/4) ≤ (x:ℝ)^((3:ℝ)/16) := by
          have h2 : (D:ℝ)^((1:ℝ)/4) ≤ ((x:ℝ)^((3:ℝ)/4))^((1:ℝ)/4) :=
            Real.rpow_le_rpow (by positivity) hD34' (by norm_num)
          have h3 : ((x:ℝ)^((3:ℝ)/4))^((1:ℝ)/4) = (x:ℝ)^((3:ℝ)/16) := by
            rw [← Real.rpow_mul (x := (x:ℝ)) (by positivity)]
            norm_num
          linarith [h2, h3.le, h3.ge]
        have h2 : (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16) ≤ (x:ℝ)^((1:ℝ)/2) := by
          calc (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16)
              ≤ (x:ℝ)^((3:ℝ)/16) * (x:ℝ)^((5:ℝ)/16) :=
                mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hxnn _)
            _ = (x:ℝ)^((1:ℝ)/2) := by
                rw [← Real.rpow_add hx0]; norm_num
        have h3 : (4:ℝ) * (x:ℝ)^((1:ℝ)/2) ≤ (x:ℝ)^((3:ℝ)/4) := by
          have h4 : (x:ℝ)^((3:ℝ)/4) = (x:ℝ)^((1:ℝ)/4) * (x:ℝ)^((1:ℝ)/2) := by
            rw [← Real.rpow_add hx0]; norm_num
          have h5 : (4:ℝ) ≤ (x:ℝ)^((1:ℝ)/4) := by
            have h1 : (x:ℝ)^((1:ℝ)/400) ≤ (x:ℝ)^((1:ℝ)/4) :=
              Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
            linarith [hXq, h1]
          rw [h4]
          exact mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hxnn _)
        linarith [hD₁_ub, h2, h3]
      have hD₁34 : D₁ ≤ ⌊(x:ℝ)^((3:ℝ)/4)⌋₊ := Nat.le_floor hD₁_le_34
      have hxy_add : (x:ℝ)^((5:ℝ)/12 - (1:ℝ)/400 - (Submission.Jeps (1/400) : ℝ)⁻¹)
          = (x:ℝ)^((11:ℝ)/12 - (1:ℝ)/400)
            * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹)) := by
        have hexp : (11:ℝ)/12 - (1:ℝ)/400 + (-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹))
            = (5:ℝ)/12 - (1:ℝ)/400 - (Submission.Jeps (1/400) : ℝ)⁻¹ := by ring
        rw [← Real.rpow_add hx0, hexp]
      have hD₁1 : 1 ≤ D₁ := by
        have h1 : (1:ℝ) ≤ (y:ℝ) * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹)) := by
          have h2 : (x:ℝ)^((5:ℝ)/12 - (1:ℝ)/400 - (Submission.Jeps (1/400) : ℝ)⁻¹)
              ≤ (y:ℝ) * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹)) := by
            rw [hxy_add]
            exact le_trans (mul_le_mul_of_nonneg_right hz_lo (Real.rpow_nonneg hxnn _))
              (mul_le_mul_of_nonneg_right hy_ge_z (Real.rpow_nonneg hxnn _))
          have h3 : (1:ℝ) ≤ (x:ℝ)^((5:ℝ)/12 - (1:ℝ)/400 - (Submission.Jeps (1/400) : ℝ)⁻¹) :=
            Real.one_le_rpow hx1 (by linarith)
          linarith
        have h4 : (1:ℝ) ≤ (D₁:ℝ) := le_trans h1 hD₁_ge
        exact_mod_cast h4
      -- ### the cutoff function
      obtain ⟨f, hfcd, hf1, hf0', hfnn, hfle, hfderiv⟩ := hcut (x:ℝ) (y:ℝ) hx1 hyR1
      have hfcont : Continuous f := hfcd.continuous
      have hfc1 : ContDiff ℝ (Submission.Jeps (1/400)) f := hfcd.of_le (by exact_mod_cast le_top)
      have hf0nn : ∀ u : ℝ, 0 ≤ f u := hfnn
      have hfle1 : ∀ u : ℝ, f u ≤ 1 := hfle
      have hfsup : ∀ u : ℝ, (x:ℝ) ≤ u → f u = 0 := hf0'
      have hf0n : ∀ n : ℕ, n ≤ x → 0 ≤ f n := fun n _ => hfnn _
      have hf1n : ∀ n : ℕ, n ≤ x → f n ≤ 1 := fun n _ => hfle _
      have hfeqn : ∀ n : ℕ, n ≤ x - y → f n = 1 := by
        intro n hn
        apply hf1
        have h1 : (n:ℝ) ≤ ((x - y : ℕ) : ℝ) := by exact_mod_cast hn
        rw [Nat.cast_sub hy_le_x] at h1
        exact h1
      set R : ℕ → ℝ := fun d => Submission.AdF (fun n : ℕ => f n) d x - Submission.MdF f d x with hRdef
      set Rtil : ℕ → ℝ := fun d => (if D₁ < d ∧ d ≤ D then R d else 0) with hRtild
      -- ### term A: smoothing the congruence sums
      have hyX : (y:ℝ) * (x:ℝ)^(-(1/4:ℝ)) ≤ 2 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) := by
        have h2 : z * (x:ℝ)^(-(1/4:ℝ))
            = (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((13:ℝ)/16 - (1:ℝ)/400 - (1:ℝ)/4) := by
          have hexp : ((13:ℝ)/16 - (1:ℝ)/400) + (-(1/4:ℝ)) = (13:ℝ)/16 - (1:ℝ)/400 - (1:ℝ)/4 := by ring
          rw [hzdef, mul_assoc, ← Real.rpow_add hx0, hexp]
        have h3 : (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((13:ℝ)/16 - (1:ℝ)/400 - (1:ℝ)/4)
            ≤ (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hDnn _)
          apply Real.rpow_le_rpow_of_exponent_le hx1
          norm_num
        calc (y:ℝ) * (x:ℝ)^(-(1/4:ℝ)) ≤ (2*z) * (x:ℝ)^(-(1/4:ℝ)) :=
              mul_le_mul_of_nonneg_right hy_le_2z (Real.rpow_nonneg hxnn _)
          _ = 2 * (z * (x:ℝ)^(-(1/4:ℝ))) := by ring
          _ = 2 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((13:ℝ)/16 - (1:ℝ)/400 - (1:ℝ)/4)) := by rw [h2]
          _ ≤ 2 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) :=
              mul_le_mul_of_nonneg_left h3 (by norm_num)
      have hXsqrt : (x:ℝ)^((1:ℝ)/2) ≤ (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) := by
        have h1 : (1:ℝ) ≤ (D:ℝ)^((1:ℝ)/4) := Real.one_le_rpow hD1 (by norm_num)
        have h2 : (x:ℝ)^((1:ℝ)/2) ≤ (x:ℝ)^((9:ℝ)/16) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        calc (x:ℝ)^((1:ℝ)/2) ≤ 1 * (x:ℝ)^((9:ℝ)/16) := by rw [one_mul]; exact h2
          _ ≤ (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) :=
              mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hxnn _)
      have hX4 : (x:ℝ)^((1:ℝ)/4) ≤ (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) := by
        have h1 : (1:ℝ) ≤ (D:ℝ)^((1:ℝ)/4) := Real.one_le_rpow hD1 (by norm_num)
        have h2 : (x:ℝ)^((1:ℝ)/4) ≤ (x:ℝ)^((9:ℝ)/16) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
        calc (x:ℝ)^((1:ℝ)/4) ≤ 1 * (x:ℝ)^((9:ℝ)/16) := by rw [one_mul]; exact h2
          _ ≤ (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) :=
              mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hxnn _)
      have hAterm : (∑ d ∈ Finset.Icc 1 D,
            |(Submission.Ad d x : ℝ) - Submission.AdF (fun n : ℕ => f n) d x|)
          ≤ (3*C10) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100) := by
        have h310' := h310 D x y hD hx hy_div (fun n : ℕ => f n) hf0n hf1n hfeqn
        refine le_trans h310' ?_
        have hpar : (y:ℝ) * (x:ℝ)^(-(1/4:ℝ)) + Real.sqrt (x:ℝ)
            ≤ 3 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) := by
          rw [Real.sqrt_eq_rpow]
          have h3 : (x:ℝ)^((1:ℝ)/2) ≤ (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) := hXsqrt
          linarith [hyX, h3]
        calc C10 * (x:ℝ)^((1:ℝ)/400) * ((y:ℝ) * (x:ℝ)^(-(1/4:ℝ)) + Real.sqrt (x:ℝ))
            ≤ C10 * (x:ℝ)^((1:ℝ)/400) * (3 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16))) :=
              mul_le_mul_of_nonneg_left hpar (mul_nonneg hC10.le (Real.rpow_nonneg hxnn _))
          _ = C10 * (3 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16))) * (x:ℝ)^((1:ℝ)/400) := by ac_rfl
          _ ≤ C10 * (3 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16))) * (x:ℝ)^((1:ℝ)/100) := by
              apply mul_le_mul_of_nonneg_left
              · exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
              · exact mul_nonneg hC10.le (by positivity)
          _ = (3*C10) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100) := by ring
      -- ### the absorption lemma
      have habsorb : ∀ K e : ℝ, 0 ≤ K → K ≤ BIG → e ≤ 1/100 →
          K * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^e
            ≤ BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100) := by
        intro K e hK hKB he
        have hxe : (x:ℝ)^e ≤ (x:ℝ)^((1:ℝ)/100) := Real.rpow_le_rpow_of_exponent_le hx1 he
        have hW : (0:ℝ) ≤ (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) := by positivity
        calc K * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^e
            ≤ BIG * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^e :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKB hW) (Real.rpow_nonneg hxnn _)
          _ ≤ BIG * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100) := by
              apply mul_le_mul_of_nonneg_left hxe
              exact mul_nonneg hBIGnn hW
          _ = BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100) := by ac_rfl
      have hAfinal := le_trans hAterm (habsorb (3*C10) (1/100) (by positivity) hKA le_rfl)
      -- ### term B: the smoothed remainder via the large sieve + Abel
      have hTn : (0:ℝ) ≤ (y:ℝ)⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400) := by positivity
      have hwAny : ∀ E : ℕ, D₁ < E → E ≤ D →
          (∑ d ∈ Finset.Icc 1 E, (d:ℝ) * |R d|)
            ≤ (Cw*(Auniv+1)) * (E:ℝ)^((3:ℝ)/2) * ((y:ℝ)⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400)) := by
        intro E hgt hED
        have hE1 : 1 ≤ E := by omega
        have hE34 : (E:ℝ) ≤ (x:ℝ)^((3:ℝ)/4) := le_trans (by exact_mod_cast hED) hD34'
        have hhyp : 1 ≤ (E:ℝ) * (y:ℝ)⁻¹ * (x:ℝ)^((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹) := by
          have h1 : (y:ℝ) * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹)) < (E:ℝ) :=
            lt_of_le_of_lt hD₁_ge (by exact_mod_cast hgt)
          have hApos : (0:ℝ) < (y:ℝ)⁻¹ * (x:ℝ)^((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹) :=
            mul_pos (inv_pos.mpr (by exact_mod_cast hy1)) (Real.rpow_pos_of_pos hx0 _)
          have h2 := mul_lt_mul_of_pos_right h1 hApos
          have heq : (y:ℝ) * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹))
              * ((y:ℝ)⁻¹ * (x:ℝ)^((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹)) = 1 := by
            have hxa : (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹))
                * (x:ℝ)^((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹) = 1 := by
              rw [Real.rpow_neg hxnn]
              exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hx0 _))
            have hyi : (y:ℝ) * (y:ℝ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast (show y ≠ 0 by omega))
            calc (y:ℝ) * (x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹))
                  * ((y:ℝ)⁻¹ * (x:ℝ)^((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹))
                = ((y:ℝ) * (y:ℝ)⁻¹) * ((x:ℝ)^(-((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹))
                    * (x:ℝ)^((1:ℝ)/2 + (Submission.Jeps (1/400) : ℝ)⁻¹)) := by ac_rfl
              _ = 1 := by rw [hxa, hyi, mul_one]
          linarith [h2, heq.le, heq.ge]
        have h := hweighted f x y E Auniv hx hy1 hy_le_x hAuniv hE1 hE34 hhyp hfc1 hfsup hf0nn hfle1 hfderiv
        rw [hRdef]
        calc (∑ d ∈ Finset.Icc 1 E,
              (d:ℝ) * |Submission.AdF (fun n : ℕ => f n) d x - Submission.MdF f d x|)
            ≤ Cw * (Auniv + 1) * (E:ℝ)^((3:ℝ)/2) * ((y:ℝ)⁻¹) * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400) := h
          _ = (Cw*(Auniv+1)) * (E:ℝ)^((3:ℝ)/2) * ((y:ℝ)⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400)) := by ring
      have hpoint : ∀ d : ℕ, (d:ℝ) * |Rtil d| ≤ (d:ℝ) * |R d| := by
        intro d
        by_cases hc : D₁ < d ∧ d ≤ D
        · rw [hRtild]
          simp only [hc, if_true]
          exact le_refl _
        · rw [hRtild]
          simp only [hc, if_false, abs_zero, mul_zero]
          exact mul_nonneg (by positivity) (abs_nonneg _)
      have hRtilD : (∑ d ∈ Finset.Icc 1 D, (d:ℝ) * |Rtil d|)
          ≤ (Cw*(Auniv+1)) * (D:ℝ)^((3:ℝ)/2) * ((y:ℝ)⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400)) := by
        by_cases hgt : D₁ < D
        · exact le_trans (Finset.sum_le_sum (fun d _ => hpoint d)) (hwAny D hgt le_rfl)
        · push_neg at hgt
          have hzero : ∀ d ∈ Finset.Icc 1 D, (d:ℝ) * |Rtil d| = 0 := by
            intro d hd
            have h1 : ¬ (D₁ < d) := by
              have := (Finset.mem_Icc.mp hd).2; omega
            rw [hRtild]
            simp only [h1, false_and, if_false, abs_zero, mul_zero]
          rw [Finset.sum_eq_zero hzero]
          have hnn : (0:ℝ) ≤ (Cw*(Auniv+1)) * (D:ℝ)^((3:ℝ)/2)
              * ((y:ℝ)⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400)) :=
            mul_nonneg (mul_nonneg hCwA0 (Real.rpow_nonneg hDnn _)) hTn
          exact hnn
      have hRtilde : ∀ D' : ℕ,
          (∑ d ∈ Finset.Icc 1 D', (d:ℝ) * |Rtil d|)
            ≤ (Cw*(Auniv+1)) * (D':ℝ)^((3:ℝ)/2) * ((y:ℝ)⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400)) := by
        intro D'
        by_cases hle : D' ≤ D
        · by_cases hgt : D₁ < D'
          · exact le_trans (Finset.sum_le_sum (fun d _ => hpoint d)) (hwAny D' hgt hle)
          · push_neg at hgt
            have hzero : ∀ d ∈ Finset.Icc 1 D', (d:ℝ) * |Rtil d| = 0 := by
              intro d hd
              have h1 : ¬ (D₁ < d) := by
                have := (Finset.mem_Icc.mp hd).2; omega
              rw [hRtild]
              simp only [h1, false_and, if_false, abs_zero, mul_zero]
            rw [Finset.sum_eq_zero hzero]
            have hnn : (0:ℝ) ≤ (Cw*(Auniv+1)) * (D':ℝ)^((3:ℝ)/2)
                * ((y:ℝ)⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400)) :=
              mul_nonneg (mul_nonneg hCwA0 (Real.rpow_nonneg (by positivity) _)) hTn
            exact hnn
        · push_neg at hle
          have h1 : (∑ d ∈ Finset.Icc 1 D', (d:ℝ) * |Rtil d|)
              = (∑ d ∈ Finset.Icc 1 D, (d:ℝ) * |Rtil d|) := by
            calc (∑ d ∈ Finset.Icc 1 D', (d:ℝ) * |Rtil d|)
                = ∑ d ∈ Finset.Icc 1 D', (if d ≤ D then (d:ℝ) * |Rtil d| else 0) := by
                  apply Finset.sum_congr rfl
                  intro d hd
                  by_cases h : d ≤ D
                  · simp [h]
                  · rw [hRtild]
                    have hc : ¬ (D₁ < d ∧ d ≤ D) := fun hc => h hc.2
                    simp [h, hc]
              _ = ∑ d ∈ (Finset.Icc 1 D').filter (fun d => d ≤ D), (d:ℝ) * |Rtil d| := by
                  rw [Finset.sum_filter]
              _ = ∑ d ∈ Finset.Icc 1 D, (d:ℝ) * |Rtil d| := by
                  apply Finset.sum_congr _ (fun _ _ => rfl)
                  ext d; simp only [Finset.mem_filter, Finset.mem_Icc]
                  constructor
                  · intro ⟨⟨h1,_⟩, h3⟩; exact ⟨h1, h3⟩
                  · intro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 (le_of_lt hle)⟩, h2⟩
          rw [h1]
          have h2 : (D:ℝ)^((3:ℝ)/2) ≤ (D':ℝ)^((3:ℝ)/2) :=
            Real.rpow_le_rpow hDnn (by exact_mod_cast le_of_lt hle) (by norm_num)
          exact le_trans hRtilD
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hCwA0) hTn)
      have hAb := Submission.abel_sqrt_bound hCwA0 hTn hRtilde D
      have hTD : ((y:ℝ)⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400)) * (D:ℝ)^((1:ℝ)/2)
          ≤ ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/200) := by
        have hTle : (y:ℝ)⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400)
            ≤ (D:ℝ)^(-((1:ℝ)/4)) * (x:ℝ)^((9:ℝ)/16 + (1:ℝ)/200) := by
          have hyz : (y:ℝ)⁻¹ ≤ z⁻¹ := (inv_le_inv₀ (by linarith : (0:ℝ) < (y:ℝ)) hz0).mpr hy_ge_z
          have hz_inv : z⁻¹ = (D:ℝ)^(-((1:ℝ)/4)) * (x:ℝ)^(-((13:ℝ)/16 - (1:ℝ)/400)) := by
            rw [hzdef, mul_inv, ← Real.rpow_neg hDnn, ← Real.rpow_neg hxnn]
          have h1 : (y:ℝ)⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400)
              ≤ z⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400) :=
            mul_le_mul_of_nonneg_right hyz (Real.rpow_nonneg hxnn _)
          have h2 : z⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400)
              = (D:ℝ)^(-((1:ℝ)/4)) * (x:ℝ)^((9:ℝ)/16 + (1:ℝ)/200) := by
            have hexp : (-((13:ℝ)/16 - (1:ℝ)/400)) + ((11:ℝ)/8 + (1:ℝ)/400)
                = (9:ℝ)/16 + (1:ℝ)/200 := by ring
            rw [hz_inv, mul_assoc, ← Real.rpow_add hx0, hexp]
          linarith [h1, h2.le, h2.ge]
        have h2 : (D:ℝ)^(-((1:ℝ)/4)) * (x:ℝ)^((9:ℝ)/16 + (1:ℝ)/200) * (D:ℝ)^((1:ℝ)/2)
            = ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/200) := by
          calc (D:ℝ)^(-((1:ℝ)/4)) * (x:ℝ)^((9:ℝ)/16 + (1:ℝ)/200) * (D:ℝ)^((1:ℝ)/2)
              = ((D:ℝ)^(-((1:ℝ)/4)) * (D:ℝ)^((1:ℝ)/2)) * (x:ℝ)^((9:ℝ)/16 + (1:ℝ)/200) := by ac_rfl
            _ = (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16 + (1:ℝ)/200) := by
                rw [← Real.rpow_add hD0r]; norm_num
            _ = (D:ℝ)^((1:ℝ)/4) * ((x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/200)) := by
                rw [Real.rpow_add hx0]
            _ = ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/200) := by ac_rfl
        calc ((y:ℝ)⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400)) * (D:ℝ)^((1:ℝ)/2)
            ≤ ((D:ℝ)^(-((1:ℝ)/4)) * (x:ℝ)^((9:ℝ)/16 + (1:ℝ)/200)) * (D:ℝ)^((1:ℝ)/2) :=
              mul_le_mul_of_nonneg_right hTle (by positivity)
          _ = ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/200) := h2
      have hBterm : (∑ d ∈ Finset.Icc 1 D, |Rtil d|)
          ≤ (6*(Cw*(Auniv+1))) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/200) := by
        calc (∑ d ∈ Finset.Icc 1 D, |Rtil d|)
            ≤ 3 * (Cw*(Auniv+1)) * ((y:ℝ)⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400)) * (D:ℝ)^((1:ℝ)/2) := hAb
          _ = 3 * (Cw*(Auniv+1))
                * (((y:ℝ)⁻¹ * (x:ℝ)^((11:ℝ)/8 + (1:ℝ)/400)) * (D:ℝ)^((1:ℝ)/2)) := by ring
          _ ≤ 3 * (Cw*(Auniv+1)) * (((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/200)) :=
              mul_le_mul_of_nonneg_left hTD (by positivity)
          _ ≤ (6*(Cw*(Auniv+1))) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/200) := by
              have hWnn : (0:ℝ) ≤ ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/200) := by
                positivity
              calc 3 * (Cw*(Auniv+1))
                    * (((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/200))
                  ≤ 6 * (Cw*(Auniv+1))
                    * (((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/200)) := by
                    apply mul_le_mul_of_nonneg_right _ hWnn
                    linarith [hCwA0]
                _ = (6*(Cw*(Auniv+1))) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/200) := by ring
      have hBfinal := le_trans hBterm (habsorb (6*(Cw*(Auniv+1))) (1/200) (by positivity) hKB (by norm_num))
      -- ### term C: the smoothed main term
      have hCterm : (∑ d ∈ Finset.Icc 1 D, |Submission.MdF f d x - (Submission.Md d x : ℝ)|)
          ≤ (4*C12*601^6) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100) := by
        have h312' := h312 f D x y hfcont hD hx hy1 hxy2 hfnn hfle hf1 hf0'
        have hlog6 := hlog6le D x hx hD34
        refine le_trans h312' ?_
        have hpar : (y:ℝ) * (x:ℝ)^(-(1/4:ℝ)) + (x:ℝ)^((1/4:ℝ))
            ≤ 3 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) := by linarith [hyX, hX4]
        calc C12 * (Real.log (2*(D:ℝ)+2))^6
              * ((y:ℝ) * (x:ℝ)^(-(1/4:ℝ)) + (x:ℝ)^((1/4:ℝ)))
            ≤ C12 * (Real.log (2*(D:ℝ)+2))^6 * (3 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16))) :=
              mul_le_mul_of_nonneg_left hpar (mul_nonneg hC12.le (by positivity))
          _ ≤ C12 * (601^6 * (x:ℝ)^((1:ℝ)/100)) * (3 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16))) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog6 hC12.le) (by positivity)
          _ ≤ (4*C12*601^6) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100) := by
              have hWnn : (0:ℝ) ≤ ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100) := by
                positivity
              calc C12 * (601^6 * (x:ℝ)^((1:ℝ)/100)) * (3 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)))
                  = (3*C12*601^6) * (((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100)) := by ring
                _ ≤ (4*C12*601^6) * (((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100)) := by
                    apply mul_le_mul_of_nonneg_right _ hWnn
                    linarith [hC12.le, h601nn]
                _ = (4*C12*601^6) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100) := by ring
      have hCfinal := le_trans hCterm (habsorb (4*C12*601^6) (1/100) (by positivity) hKC le_rfl)
      -- ### term D: the sharp main term
      have hDterm : (∑ d ∈ Finset.Icc 1 D,
            |(Submission.Md d x : ℝ)
              - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                  ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                    2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
          ≤ (Cb*601^6) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100) := by
        have hBmd' := hBmd x D hx hD
        have hlog6 := hlog6le D x hx hD34
        calc (∑ d ∈ Finset.Icc 1 D, |(Submission.Md d x : ℝ)
              - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                  ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                    2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
            ≤ Cb * (x:ℝ)^((1:ℝ)/4) * (Real.log (2*(D:ℝ)+2))^6 := hBmd'
          _ = Cb * ((x:ℝ)^((1:ℝ)/4) * (Real.log (2*(D:ℝ)+2))^6) := by ring
          _ ≤ Cb * (((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (601^6 * (x:ℝ)^((1:ℝ)/100))) := by
              apply mul_le_mul_of_nonneg_left _ hCb.le
              exact mul_le_mul hX4 hlog6 (by positivity) (by positivity)
          _ = (Cb*601^6) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100) := by ring
      have hDfinal := le_trans hDterm (habsorb (Cb*601^6) (1/100) (by positivity) hKD le_rfl)
      -- ### the crude bound for `d ≤ D₁`
      have hcrude : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ≤ D₁),
            |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
              - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                  ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                    2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
          ≤ ((4:ℝ)*Cel*601^6) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100) := by
        have hsub : (Finset.Icc 1 D).filter (fun d => d ≤ D₁) ⊆ Finset.Icc 1 D₁ := by
          intro d hd
          rw [Finset.mem_filter] at hd
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd.1).1, hd.2⟩
        have hstep : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ≤ D₁),
              |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
                - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                    ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                      2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
            ≤ ∑ d ∈ Finset.Icc 1 D₁,
              |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
                - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                    ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                      2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))| :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => abs_nonneg _)
        have h2 := hel x D₁ hx hD₁1
        have hlog₁ : (Real.log (2*(D₁:ℝ)+2))^6 ≤ 601^6 * (x:ℝ)^((1:ℝ)/100) := hlog6le D₁ x hx hD₁34
        refine le_trans hstep (le_trans h2 ?_)
        have hxcomb : (x:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16) = (x:ℝ)^((9:ℝ)/16) := by
          rw [← Real.rpow_add hx0]; norm_num
        calc Cel * (x:ℝ)^((1:ℝ)/4) * (D₁:ℝ) * (Real.log (2*(D₁:ℝ)+2))^6
            ≤ Cel * (x:ℝ)^((1:ℝ)/4) * (4 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16)))
                * (601^6 * (x:ℝ)^((1:ℝ)/100)) := by
              have h1 : Cel * (x:ℝ)^((1:ℝ)/4) * (D₁:ℝ)
                  ≤ Cel * (x:ℝ)^((1:ℝ)/4) * (4 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16))) :=
                mul_le_mul_of_nonneg_left hD₁_ub (mul_nonneg hCel.le (Real.rpow_nonneg hxnn _))
              calc Cel * (x:ℝ)^((1:ℝ)/4) * (D₁:ℝ) * (Real.log (2*(D₁:ℝ)+2))^6
                  ≤ Cel * (x:ℝ)^((1:ℝ)/4) * (4 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16)))
                      * (Real.log (2*(D₁:ℝ)+2))^6 :=
                    mul_le_mul_of_nonneg_right h1 (by positivity)
                _ ≤ Cel * (x:ℝ)^((1:ℝ)/4) * (4 * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16)))
                      * (601^6 * (x:ℝ)^((1:ℝ)/100)) :=
                    mul_le_mul_of_nonneg_left hlog₁
                      (mul_nonneg (mul_nonneg hCel.le (Real.rpow_nonneg hxnn _)) (by positivity))
          _ = ((4:ℝ)*Cel*601^6) * ((D:ℝ)^((1:ℝ)/4) * ((x:ℝ)^((1:ℝ)/4) * (x:ℝ)^((5:ℝ)/16)))
                * (x:ℝ)^((1:ℝ)/100) := by ring
          _ = ((4:ℝ)*Cel*601^6) * ((D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16)) * (x:ℝ)^((1:ℝ)/100) := by
              rw [hxcomb]
      have hcrudefinal := le_trans hcrude (habsorb ((4:ℝ)*Cel*601^6) (1/100) (by positivity) hKE le_rfl)
      -- ### the pointwise decomposition
      have hmain : ∀ d : ℕ,
          |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
            - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                  2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|
          ≤ |(Submission.Ad d x : ℝ) - Submission.AdF (fun n : ℕ => f n) d x|
            + |Submission.AdF (fun n : ℕ => f n) d x - Submission.MdF f d x|
            + |Submission.MdF f d x - (Submission.Md d x : ℝ)|
            + |(Submission.Md d x : ℝ)
              - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                  ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                    2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))| := by
        intro d
        have hnc : (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
            = (Submission.Ad d x : ℝ) := by
          have h := Submission.ncard_eq_Ad_sum d x
          have h' : Submission.Ad d x
              = ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard := by
            rw [Submission.Ad]
            exact h.symm
          rw [← h']
        rw [hnc]
        set A := (Submission.Ad d x : ℝ) with hA'
        set C := Submission.AdF (fun n : ℕ => f n) d x with hC'
        set E := Submission.MdF f d x with hE'
        set F := (Submission.Md d x : ℝ) with hF'
        set B : ℝ := (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
              ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ)) with hB'
        have e1 : A - B = (A - C) + (C - E) + (E - F) + (F - B) := by ring
        rw [e1]
        have hh1 := abs_add_le ((A - C) + (C - E) + (E - F)) (F - B)
        have hh2 := abs_add_le ((A - C) + (C - E)) (E - F)
        have hh3 := abs_add_le (A - C) (C - E)
        linarith [hh1, hh2, hh3, abs_nonneg (F - B), abs_nonneg (E - F), abs_nonneg (C - E)]
      -- ### the split and the final assembly
      have hsum_split : (∑ d ∈ Finset.Icc 1 D,
            |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
              - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                  ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                    2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
          ≤ (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ≤ D₁),
              |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
                - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                    ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                      2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
            + (∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁),
              |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
                - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                    ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                      2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|) := by
        rw [Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 D) (fun d => d ≤ D₁)]
      have hpart2 : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁),
            |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
              - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                  ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                    2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
          ≤ (∑ d ∈ Finset.Icc 1 D, |(Submission.Ad d x : ℝ) - Submission.AdF (fun n : ℕ => f n) d x|)
            + (∑ d ∈ Finset.Icc 1 D, |Rtil d|)
            + (∑ d ∈ Finset.Icc 1 D, |Submission.MdF f d x - (Submission.Md d x : ℝ)|)
            + (∑ d ∈ Finset.Icc 1 D, |(Submission.Md d x : ℝ)
              - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                  ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                    2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|) := by
        have hstep : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁),
              |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
                - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                    ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                      2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
            ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁),
                (|(Submission.Ad d x : ℝ) - Submission.AdF (fun n : ℕ => f n) d x|
                  + |Submission.AdF (fun n : ℕ => f n) d x - Submission.MdF f d x|
                  + |Submission.MdF f d x - (Submission.Md d x : ℝ)|
                  + |(Submission.Md d x : ℝ)
                    - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                        ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                          2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|) :=
          Finset.sum_le_sum (fun d _ => hmain d)
        have hb1 : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁),
              |(Submission.Ad d x : ℝ) - Submission.AdF (fun n : ℕ => f n) d x|)
            ≤ (∑ d ∈ Finset.Icc 1 D, |(Submission.Ad d x : ℝ) - Submission.AdF (fun n : ℕ => f n) d x|) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _)
        have hb2 : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁),
              |Submission.AdF (fun n : ℕ => f n) d x - Submission.MdF f d x|)
            ≤ (∑ d ∈ Finset.Icc 1 D, |Rtil d|) := by
          refine le_trans (le_of_eq (Finset.sum_congr rfl ?_))
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _))
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_Icc] at hd
          have h1 : D₁ < d := by omega
          have h2 : d ≤ D := hd.1.2
          rw [hRtild]
          simp only [h1, h2, and_self, if_true]
          rw [hRdef]
        have hb3 : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁),
              |Submission.MdF f d x - (Submission.Md d x : ℝ)|)
            ≤ (∑ d ∈ Finset.Icc 1 D, |Submission.MdF f d x - (Submission.Md d x : ℝ)|) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _)
        have hb4 : (∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁),
              |(Submission.Md d x : ℝ)
                - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                    ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                      2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
            ≤ (∑ d ∈ Finset.Icc 1 D, |(Submission.Md d x : ℝ)
              - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                  ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                    2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _)
        calc (∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁), _)
            ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁), _ := hstep
          _ = (∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁),
                |(Submission.Ad d x : ℝ) - Submission.AdF (fun n : ℕ => f n) d x|)
              + (∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁),
                |Submission.AdF (fun n : ℕ => f n) d x - Submission.MdF f d x|)
              + (∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁),
                |Submission.MdF f d x - (Submission.Md d x : ℝ)|)
              + (∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁),
                |(Submission.Md d x : ℝ)
                  - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                      ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                        2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
          _ ≤ (∑ d ∈ Finset.Icc 1 D, |(Submission.Ad d x : ℝ) - Submission.AdF (fun n : ℕ => f n) d x|)
              + (∑ d ∈ Finset.Icc 1 D, |Rtil d|)
              + (∑ d ∈ Finset.Icc 1 D, |Submission.MdF f d x - (Submission.Md d x : ℝ)|)
              + (∑ d ∈ Finset.Icc 1 D, |(Submission.Md d x : ℝ)
                - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                    ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                      2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|) := by
              linarith [hb1, hb2, hb3, hb4]
      calc (∑ d ∈ Finset.Icc 1 D,
            |(({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ) ∧ ((d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 4)}).ncard : ℝ)
              - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                  ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                    2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)
          ≤ (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d ≤ D₁), _)
            + (∑ d ∈ (Finset.Icc 1 D).filter (fun d => ¬ d ≤ D₁), _) := hsum_split
        _ ≤ BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100)
            + ((∑ d ∈ Finset.Icc 1 D, |(Submission.Ad d x : ℝ) - Submission.AdF (fun n : ℕ => f n) d x|)
              + (∑ d ∈ Finset.Icc 1 D, |Rtil d|)
              + (∑ d ∈ Finset.Icc 1 D, |Submission.MdF f d x - (Submission.Md d x : ℝ)|)
              + (∑ d ∈ Finset.Icc 1 D, |(Submission.Md d x : ℝ)
                - (∑ c ∈ Finset.Icc (-(⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊ : ℤ)) (⌊(x : ℝ) ^ ((1 : ℝ) / 4)⌋₊),
                    ∑ β ∈ (Finset.range d).filter (fun β : ℕ => ((d : ℤ) ∣ (β : ℤ) ^ 2 + (c : ℤ) ^ 4)),
                      2 * Real.sqrt ((x : ℝ) - (c : ℝ) ^ 4) / (d : ℝ))|)) := by
            linarith [hcrudefinal, hpart2]
        _ ≤ BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100)
            + (BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100)
              + BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100)
              + BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100)
              + BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100)) := by
            linarith [hAfinal, hBfinal, hCfinal, hDfinal]
        _ ≤ 8 * (BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100)) := by
            have hBW : (0:ℝ) ≤ BIG * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100) := by
              positivity
            linarith [hBW]
        _ = (8*BIG) * (D:ℝ)^((1:ℝ)/4) * (x:ℝ)^((9:ℝ)/16) * (x:ℝ)^((1:ℝ)/100) := by ac_rfl


end Commons.NumberTheory.FriedlanderIwaniec
