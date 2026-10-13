/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.RingTheory.Ideal.Hilbert.natDegree_hilbertPoly_eq_dim_sub_one` (piece 0).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Data.Sym.NatCard
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Submission.Work.WilE2.BzPort.P46

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.natDegree_hilbertPoly_eq_dim_sub_one ====
section

namespace Commons.RingTheory.Ideal.Hilbert

open MvPolynomial Polynomial

variable {k : Type*} [Field k] {m : ℕ}

/-! ## The degree of the partial sums of a polynomial -/

lemma natDegree_bernoulli_eq (n : ℕ) : (Polynomial.bernoulli n).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.bernoulli]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    simp only [Finset.mem_range] at hi
    exact (Polynomial.natDegree_monomial_le (m := n - i) _).trans (by omega)
  · rw [Polynomial.coeff_bernoulli, if_pos (Nat.le_refl _), Nat.sub_self, _root_.bernoulli_zero,
      one_mul, Nat.choose_self]
    norm_num

lemma coeff_powSumPoly (n : ℕ) :
    (Commons.Algebra.Polynomial.EventuallyPoly.powSumPoly n).coeff (n + 1)
      = ((n + 1 : ℕ) : ℚ)⁻¹ := by
  rw [Commons.Algebra.Polynomial.EventuallyPoly.powSumPoly, Polynomial.coeff_mul_C,
    Polynomial.coeff_sub, Polynomial.coeff_C]
  have h1 : ¬ ((n + 1) = 0) := by omega
  rw [if_neg h1, sub_zero]
  rw [Polynomial.coeff_bernoulli, if_pos (Nat.le_refl _), Nat.sub_self, _root_.bernoulli_zero,
    one_mul, Nat.choose_self, Nat.cast_one]
  ring

lemma natDegree_powSumPoly (n : ℕ) :
    (Commons.Algebra.Polynomial.EventuallyPoly.powSumPoly n).natDegree = n + 1 := by
  rw [Commons.Algebra.Polynomial.EventuallyPoly.powSumPoly]
  have hb : (Polynomial.bernoulli (n + 1)).natDegree = n + 1 := natDegree_bernoulli_eq _
  have h1 : (Polynomial.bernoulli (n + 1) - Polynomial.C (_root_.bernoulli (n + 1))).natDegree
      = n + 1 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact hb
    · rw [Polynomial.natDegree_C, hb]; omega
  rw [Polynomial.natDegree_mul_C (inv_ne_zero (by positivity)), h1]

lemma natDegree_sumPoly {P : Polynomial ℚ} (hP : P ≠ 0) :
    (Commons.Algebra.Polynomial.EventuallyPoly.sumPoly P).natDegree = P.natDegree + 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Commons.Algebra.Polynomial.EventuallyPoly.sumPoly]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    rw [Polynomial.natDegree_C, natDegree_powSumPoly]
    simp only [Finset.mem_range] at hi
    omega
  · rw [Commons.Algebra.Polynomial.EventuallyPoly.sumPoly, Polynomial.finsetSum_coeff,
      Finset.sum_eq_single P.natDegree]
    · rw [Polynomial.coeff_C_mul, coeff_powSumPoly, mul_comm]
      exact mul_ne_zero (inv_ne_zero (by positivity)) (Polynomial.leadingCoeff_ne_zero.mpr hP)
    · intro i hi hne
      have hdeg : (Commons.Algebra.Polynomial.EventuallyPoly.powSumPoly i).natDegree
          < P.natDegree + 1 := by
        rw [natDegree_powSumPoly]
        simp only [Finset.mem_range] at hi
        omega
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

/-- The partial sums of a nonzero polynomial of degree `k` form a polynomial of degree `k + 1`. -/
theorem exists_partialSumPoly_natDegree {P : Polynomial ℚ} (hP : P ≠ 0) :
    ∃ Q : Polynomial ℚ, Q.natDegree = P.natDegree + 1 ∧ ∀ t : ℕ,
      (∑ u ∈ Finset.range (t + 1), P.eval (u : ℚ)) = Q.eval (t : ℚ) := by
  refine ⟨(Commons.Algebra.Polynomial.EventuallyPoly.sumPoly P).comp
    (Polynomial.X + Polynomial.C 1), ?_, ?_⟩
  · rw [Polynomial.natDegree_comp, natDegree_sumPoly hP, Polynomial.natDegree_X_add_C]
    ring
  · intro t
    rw [Polynomial.eval_comp]
    rw [show (Polynomial.eval (t:ℚ) (Polynomial.X + Polynomial.C (1:ℚ)))
        = ((t + 1 : ℕ) : ℚ) from by
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; push_cast; ring]
    rw [Commons.Algebra.Polynomial.EventuallyPoly.sumPoly_eval]

/-! ## The main theorem -/

theorem natDegree_hilbertPoly_eq_dim_sub_one {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (P : Polynomial ℚ)
    (hP : ∃ N, ∀ t ≥ N, (Module.finrank k (Submodule.map (q.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k t)) : ℚ) = P.eval (t : ℚ))
    (hP0 : P ≠ 0) :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin m) k ⧸ q) = (d : WithBot ℕ∞) ∧ d = P.natDegree + 1 := by
  classical
  haveI : Nontrivial (MvPolynomial (Fin m) k ⧸ q) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top ‹q.IsPrime›)
  have hd_ne_bot : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) ≠ ⊥ := by
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin m) k ⧸ q)
    intro h; rw [h] at h0
    exact not_le_of_gt (WithBot.bot_lt_coe (0 : ℕ∞)) h0
  have hd_ne_top : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) ≠ ⊤ := by
    have hle : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) ≤ ringKrullDim (MvPolynomial (Fin m) k) :=
      ringKrullDim_quotient_le q
    rw [ringKrullDim_mvPoly_fin_card] at hle
    intro h
    rw [h] at hle
    exact (fun hh => ENat.natCast_ne_top m (WithBot.coe_injective hh)) (le_antisymm le_top hle)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hd_ne_bot
  have ha_top : a ≠ ⊤ := by intro h; exact hd_ne_top (by rw [← ha, h]; rfl)
  obtain ⟨d, hd'⟩ := ENat.ne_top_iff_exists.mp ha_top
  have hdd : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) = (d : WithBot ℕ∞) := by
    rw [← ha, ← hd']; rfl
  obtain ⟨C, hC'⟩ := hilbert_sum_upper_bound q hq d hdd
  obtain ⟨Q, hQdeg, hQ⟩ := exists_partialSumPoly_natDegree hP0
  obtain ⟨N0, hN0'⟩ := hP
  -- The Hilbert function of the quotient, as a `ℚ`-valued function.
  let f : ℕ → ℚ := fun u => (Module.finrank k (Submodule.map (q.mkQ.restrictScalars k)
    (MvPolynomial.homogeneousSubmodule (Fin m) k u)) : ℚ)
  have hcastsum : ∀ t, (∑ u ∈ Finset.range (t+1), f u)
      = ((∑ u ∈ Finset.range (t+1), Module.finrank k (Submodule.map (q.mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k u)) : ℕ) : ℚ) := by
    intro t; simp only [f, Nat.cast_sum]
  have hfN0 : ∀ u ≥ N0, f u = P.eval (u : ℚ) := by
    intro u hu; simpa only [f] using hN0' u hu
  have hFbound : ∀ t, (∑ u ∈ Finset.range (t+1), f u) ≤ (C : ℚ) * ((t : ℚ) + 1) ^ d := by
    intro t
    rw [hcastsum t]
    have h1 : ((∑ u ∈ Finset.range (t+1), Module.finrank k (Submodule.map (q.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k u)) : ℕ) : ℚ)
        ≤ ((C * (t+1)^d : ℕ) : ℚ) := by
      exact_mod_cast hC' t
    push_cast at h1
    simpa using h1
  set K : ℚ := (∑ u ∈ Finset.range N0, f u) - ∑ u ∈ Finset.range N0, P.eval (u : ℚ) with hK
  have hQF : ∀ t ≥ N0, (∑ u ∈ Finset.range (t+1), f u) = Q.eval (t : ℚ) + K := by
    intro t ht
    have htn : N0 + (t + 1 - N0) = t + 1 := by omega
    have hsplit : (∑ u ∈ Finset.range (t+1), f u)
        = (∑ u ∈ Finset.range N0, f u) + ∑ j ∈ Finset.range (t + 1 - N0), f (N0 + j) := by
      conv_lhs => rw [← htn]
      rw [Finset.sum_range_add]
    have hsubst : ∑ j ∈ Finset.range (t + 1 - N0), f (N0 + j)
        = ∑ j ∈ Finset.range (t + 1 - N0), P.eval ((N0 + j : ℕ) : ℚ) :=
      Finset.sum_congr rfl (fun j hj => by
        simp only [Finset.mem_range] at hj
        exact hfN0 (N0 + j) (by omega))
    have hPS : (∑ u ∈ Finset.range (t+1), P.eval (u : ℚ))
        = (∑ u ∈ Finset.range N0, P.eval (u : ℚ))
          + ∑ j ∈ Finset.range (t + 1 - N0), P.eval ((N0 + j : ℕ) : ℚ) := by
      conv_lhs => rw [← htn]
      rw [Finset.sum_range_add]
    have hQ' : Q.eval (t : ℚ) = (∑ u ∈ Finset.range N0, P.eval (u : ℚ))
          + ∑ j ∈ Finset.range (t + 1 - N0), P.eval ((N0 + j : ℕ) : ℚ) := by
      rw [← hQ t, hPS]
    rw [hsplit, hsubst, hQ', hK]
    ring
  -- `natDegree Q ≤ d`
  have hQle : Q.natDegree ≤ d := by
    refine Commons.Algebra.Polynomial.natDegree_le_of_eventually_abs_eval_le
      (C := (C : ℚ) * 2 ^ d + |K|) (N := max N0 1) ?_
    intro t ht
    have htN0 : N0 ≤ t := le_trans (le_max_left _ _) ht
    have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
    have ht1' : (1 : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht1
    have hQeq : Q.eval (t : ℚ) = (∑ u ∈ Finset.range (t+1), f u) - K := by
      rw [hQF t htN0]; ring
    have hnonneg : (0 : ℚ) ≤ ∑ u ∈ Finset.range (t+1), f u :=
      Finset.sum_nonneg (fun u _ => by simp only [f]; exact Nat.cast_nonneg _)
    have ht0 : (0 : ℚ) ≤ (t : ℚ) := Nat.cast_nonneg t
    have hpow : ((t : ℚ) + 1) ^ d ≤ 2 ^ d * (t : ℚ) ^ d := by
      calc ((t : ℚ) + 1) ^ d ≤ (2 * (t : ℚ)) ^ d :=
            pow_le_pow_left₀ (by linarith [ht0]) (by linarith [ht1']) d
        _ = 2 ^ d * (t : ℚ) ^ d := by rw [mul_pow]
    have hKle : |K| ≤ |K| * (t : ℚ) ^ d := by
      have h1 : (1 : ℚ) ≤ (t : ℚ) ^ d := one_le_pow₀ ht1'
      nlinarith [abs_nonneg K]
    rw [hQeq]
    calc |(∑ u ∈ Finset.range (t+1), f u) - K|
          ≤ |∑ u ∈ Finset.range (t+1), f u| + |K| := by
            simpa [sub_eq_add_neg] using abs_add_le (∑ u ∈ Finset.range (t+1), f u) (-K)
      _ = (∑ u ∈ Finset.range (t+1), f u) + |K| := by rw [abs_of_nonneg hnonneg]
      _ ≤ (C : ℚ) * 2 ^ d * (t : ℚ) ^ d + |K| * (t : ℚ) ^ d := by
            have h2 : (0 : ℚ) ≤ (C : ℚ) := Nat.cast_nonneg C
            have h3 := mul_le_mul_of_nonneg_left hpow h2
            nlinarith [hFbound t, h3, hKle]
      _ = ((C : ℚ) * 2 ^ d + |K|) * (t : ℚ) ^ d := by ring
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · rw [h0] at hQle; omega
    · exact hpos
  obtain ⟨c, hcpos, Nc, hc'⟩ := hilbert_sum_lower_bound q hq d hdd
  have hc : ∀ t ≥ Nc, c * ((t : ℚ) + 1) ^ d ≤ (∑ u ∈ Finset.range (t+1), f u) := by
    intro t ht
    rw [hcastsum t, Nat.cast_sum]
    exact hc' t ht
  -- `d ≤ natDegree Q`
  have hQge : d ≤ Q.natDegree := by
    refine Commons.Algebra.Polynomial.le_natDegree_of_eventually_le_eval
      (C := c / 2) (N := max (max Nc N0) (Nat.ceil (2 * |K| / c) + 1))
      (div_pos hcpos (by norm_num)) ?_
    intro t ht
    have htNc : Nc ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
    have htN0 : N0 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
    have ht1 : 1 ≤ t := by
      have h3 : Nat.ceil (2 * |K| / c) + 1 ≤ t := le_trans (le_max_right _ _) ht
      omega
    have ht1' : (1 : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht1
    have htK : 2 * |K| / c ≤ (t : ℚ) := by
      have h1 : ((Nat.ceil (2 * |K| / c) : ℕ) : ℚ) ≤ (t : ℚ) := by
        have h2 : Nat.ceil (2 * |K| / c) ≤ t := by
          have h3 : Nat.ceil (2 * |K| / c) + 1 ≤ t := le_trans (le_max_right _ _) ht
          omega
        exact_mod_cast h2
      have h3 : 2 * |K| / c ≤ (Nat.ceil (2 * |K| / c) : ℚ) := Nat.le_ceil _
      linarith
    have h1 := hc t htNc
    have h2 := hQF t htN0
    rw [h2] at h1
    have h3 : c * (t : ℚ) ^ d ≤ c * ((t : ℚ) + 1) ^ d := by
      have hb : (t : ℚ) ≤ (t : ℚ) + 1 := by linarith
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg t) hb d) hcpos.le
    have h5 : |K| ≤ c / 2 * (t : ℚ) := by
      rw [div_le_iff₀ hcpos] at htK
      nlinarith [htK]
    have h6 : (t : ℚ) ≤ (t : ℚ) ^ d := by
      have h7 : (t : ℚ) ^ 1 ≤ (t : ℚ) ^ d := pow_le_pow_right₀ ht1' hd1
      simpa using h7
    have h7c : |K| ≤ c / 2 * (t : ℚ) ^ d := by
      have h8 : (0 : ℚ) ≤ c / 2 := le_of_lt (div_pos hcpos (by norm_num))
      have h9 : c / 2 * (t : ℚ) ≤ c / 2 * (t : ℚ) ^ d := mul_le_mul_of_nonneg_left h6 h8
      linarith [h5, h9]
    have h11 : K ≤ |K| := le_abs_self K
    nlinarith [h1, h3, h7c, h11]
  have hdeg : Q.natDegree = d := le_antisymm hQle hQge
  exact ⟨d, hdd, by omega⟩

end Commons.RingTheory.Ideal.Hilbert

end


