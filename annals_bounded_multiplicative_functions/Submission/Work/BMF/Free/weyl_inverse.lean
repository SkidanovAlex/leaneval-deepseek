import Mathlib
import Submission.Work.BMF.Defs
import Submission.Commons.Analysis.ExponentialSums.iterated_differencing_step
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test
import Submission.Work.BMF.SD.sum_range_eq_sum_mod
import Submission.Work.BMF.SD.abel_geom_bound
import Submission.Work.BMF.SD.fiber_card_ge
import Submission.Work.BMF.SD.beta_pinning
import Submission.Work.BMF.SD.descent_coeff
import Submission.Work.BMF.Free.a_one_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Inverse Weyl inequality (deterministic)

If a polynomial exponential sum `∑_{n<L} e(P(n))` has modulus at least `δ L`, then all
coefficients of `P` are close to rationals with a common bounded denominator: there exists
`q` (depending only on `deg P` and `δ`) with `‖q a_j‖ ≤ C / L^j`.

Proof (induction on the degree):
* `diff_shift_exists` (van der Corput differencing) produces a large set `D` of shifts `d`
  for which the differenced polynomial `P(·+d) - P` has a large exponential sum;
* the induction hypothesis applied to `P(·+d) - P` gives, after pigeonholing over the
  bounded denominators (`fiber_card_ge`), a common `q` and conditions on the coefficients
  `∑_j C(j,i) d^{j-i} P.coeff j`;
* `descent_coeff` converts these, using `beta_pinning` (a Vinogradov-type lemma turning
  "many `d` with `‖β d‖` small" into a bounded denominator), into bounds for `P.coeff j`,
  `j ≥ 2`;
* `a_one_bound` pins the linear coefficient `P.coeff 1` by a residue-class/Abel argument;
* `taylor_sub_coeff_aux` supplies the coefficient identity for `P(·+d) - P`.
-/

namespace Work.BMF.SD.FreeW
open Finset Real Polynomial
open scoped BigOperators
set_option maxHeartbeats 0
noncomputable section

/-! ### Local facts about the additive character `eC t = exp(2πit)` -/

lemma norm_eC' (t : ℝ) : ‖eC t‖ = 1 := by
  rw [eC, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h, Real.exp_zero]

lemma eC_add' (a b : ℝ) : eC (a + b) = eC a * eC b := by
  rw [eC, eC, eC, ← Complex.exp_add]; congr 1; push_cast; ring

lemma eC_neg' (a : ℝ) : eC (-a) = star (eC a) := by
  rw [eC, eC]
  have h : star (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)))
      = Complex.exp (star (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ))) := by
    rw [Complex.star_def, ← Complex.exp_conj]
  rw [h]; congr 1; simp [Complex.conj_ofReal]

lemma eC_sub' (a b : ℝ) : eC (a - b) = eC a * star (eC b) := by
  rw [sub_eq_add_neg, eC_add', eC_neg']

@[simp] lemma eC_zero' : eC 0 = 1 := by rw [eC]; simp

/-- Taylor coefficients of a polynomial in the form used by the descent. -/
lemma taylor_coeff_aux (P : Polynomial ℝ) (d : ℝ) (K : ℕ) (hP : P.natDegree ≤ K) (i : ℕ) :
    (Polynomial.taylor d P).coeff i
      = ∑ j ∈ Finset.Icc i K, P.coeff j * d ^ (j - i) * ((j.choose i : ℕ) : ℝ) := by
  have key : (Polynomial.taylor d P).coeff i
      = ∑ j ∈ P.support, P.coeff j * d ^ (j - i) * (j.choose i : ℝ) := by
    rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_apply, Polynomial.sum_def,
        Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Polynomial.eval_monomial]
    ring
  rw [key]
  have hsub : P.support ⊆ Finset.range (K + 1) := by
    intro j hj
    rw [Finset.mem_range]
    have := Polynomial.le_natDegree_of_mem_supp j hj
    omega
  have hzero : ∀ x ∈ Finset.range (K + 1), x ∉ P.support →
      P.coeff x * d ^ (x - i) * (x.choose i : ℝ) = 0 := by
    intro x _ hx
    have hc : P.coeff x = 0 := by
      by_contra h
      exact hx (Polynomial.mem_support_iff.mpr h)
    simp [hc]
  rw [Finset.sum_subset hsub hzero]
  symm
  apply Finset.sum_subset
  · intro x hx; rw [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
  · intro x hx hxnot
    rw [Finset.mem_range] at hx
    have hxi : x < i := by
      by_contra h; push Not at h
      exact hxnot (by rw [Finset.mem_Icc]; omega)
    simp [Nat.choose_eq_zero_of_lt hxi]

/-- Coefficients of `taylor d P - P`; the diagonal term of the Taylor expansion cancels. -/
lemma taylor_sub_coeff_aux (k : ℕ) (d : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ k + 1) :
    (Polynomial.taylor (d:ℝ) P - P).natDegree ≤ k ∧
    ∀ i : ℕ, (Polynomial.taylor (d:ℝ) P - P).coeff i
      = ∑ j ∈ Finset.Icc (i+1) (k+1), P.coeff j * (d:ℝ)^(j-i) * ((j.choose i : ℕ) : ℝ) := by
  have hcoeff : ∀ i : ℕ, (Polynomial.taylor (d:ℝ) P - P).coeff i
      = ∑ j ∈ Finset.Icc (i+1) (k+1), P.coeff j * (d:ℝ)^(j-i) * ((j.choose i : ℕ) : ℝ) := by
    intro i
    rw [Polynomial.coeff_sub, taylor_coeff_aux P (d:ℝ) (k+1) hP i]
    by_cases hi : i ≤ k + 1
    · rw [show Finset.Icc i (k+1) = insert i (Finset.Icc (i+1) (k+1)) from by
        ext j; simp only [Finset.mem_insert, Finset.mem_Icc]; omega,
        Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
      simp
    · push Not at hi
      have h1 : (∑ j ∈ Finset.Icc i (k+1), P.coeff j * (d:ℝ)^(j-i) * ((j.choose i : ℕ):ℝ)) = 0 :=
        Finset.sum_eq_zero (fun j hj => by
          rw [Finset.mem_Icc] at hj; exact absurd hj.1 (by omega))
      have h2 : (∑ j ∈ Finset.Icc (i+1) (k+1), P.coeff j * (d:ℝ)^(j-i) * ((j.choose i : ℕ):ℝ)) = 0 :=
        Finset.sum_eq_zero (fun j hj => by
          rw [Finset.mem_Icc] at hj; exact absurd hj.1 (by omega))
      have h3 : P.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [h1, h2, h3]; ring
  refine ⟨?_, hcoeff⟩
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [hcoeff N]
  exact Finset.sum_eq_zero (fun j hj => by
    rw [Finset.mem_Icc] at hj; exact absurd hj.2 (by omega))






lemma norm_sum_eC_le (M : ℕ) (g : ℕ → ℝ) :
    ‖∑ x ∈ Finset.range M, eC (g x)‖ ≤ (M : ℝ) := by
  calc ‖∑ x ∈ Finset.range M, eC (g x)‖ ≤ ∑ x ∈ Finset.range M, ‖eC (g x)‖ := norm_sum_le _ _
    _ = ∑ _x ∈ Finset.range M, (1 : ℝ) := by
        apply Finset.sum_congr rfl; intro x _; rw [norm_eC']
    _ = (M : ℝ) := by simp

lemma diff_shift_exists (δ : ℝ) (hδ : 0 < δ) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 / 2 ∧ ∀ (L : ℕ) (f : ℕ → ℝ),
      (16 : ℝ) / δ ^ 2 ≤ (L : ℝ) →
      δ * (L : ℝ) ≤ ‖∑ n ∈ Finset.range L, eC (f n)‖ →
      ∃ D : Finset ℕ, D ⊆ Finset.Icc 1 (L - 1) ∧ δ₁ * (L : ℝ) ≤ (D.card : ℝ) ∧
        ∀ d ∈ D, δ₁ * (L : ℝ) ≤ ((L - d : ℕ) : ℝ) ∧
          δ₁ * ((L - d : ℕ) : ℝ) ≤
            ‖∑ x ∈ Finset.range (L - d), eC (f (x + d) - f x)‖ := by
  refine ⟨min (δ ^ 2 / 8) (1 / 2), lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  intro L f hL hbig
  classical
  have hδ₁le : min (δ ^ 2 / 8) (1 / 2) ≤ δ ^ 2 / 8 := min_le_left _ _
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    have : (0 : ℝ) < 16 / δ ^ 2 := by positivity
    linarith
  have hL1 : 1 ≤ L := by
    by_contra h; push Not at h; interval_cases L; simp at hLpos
  set G : ℕ → ℂ := fun h => ∑ x ∈ Finset.range (L - h), eC (f (x + h) - f x) with hG
  set τ : ℝ := δ ^ 2 / 8 * (L : ℝ) with hτ
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have key : δ ^ 2 * (L : ℝ) ^ 2 ≤ 2 * ∑ h ∈ Finset.range L, ‖G h‖ := by
    have h1 := Commons.Analysis.ExponentialSums.iterated_differencing_step L (fun n => eC (f n))
    have h2 : ∀ h : ℕ, ‖∑ x ∈ Finset.range (L - h), eC (f (x + h)) * star (eC (f x))‖ = ‖G h‖ := by
      intro h; congr 1
      apply Finset.sum_congr rfl; intro x _; rw [eC_sub']
    have h4 : (δ * (L : ℝ)) ^ 2 ≤ ‖∑ n ∈ Finset.range L, eC (f n)‖ ^ 2 := by
      apply sq_le_sq'
      · nlinarith [norm_nonneg (∑ n ∈ Finset.range L, eC (f n))]
      · exact hbig
    calc δ ^ 2 * (L : ℝ) ^ 2 = (δ * (L : ℝ)) ^ 2 := by ring
      _ ≤ ‖∑ n ∈ Finset.range L, eC (f n)‖ ^ 2 := h4
      _ ≤ 2 * ∑ h ∈ Finset.range L,
            ‖∑ x ∈ Finset.range (L - h), eC (f (x + h)) * star (eC (f x))‖ := h1
      _ = 2 * ∑ h ∈ Finset.range L, ‖G h‖ := by
          congr 1; exact Finset.sum_congr rfl (fun h _ => h2 h)
  have hnorm_le : ∀ h : ℕ, ‖G h‖ ≤ ((L - h : ℕ) : ℝ) := fun h =>
    norm_sum_eC_le (L - h) (fun x => f (x + h) - f x)
  have hG0 : ‖G 0‖ = (L : ℝ) := by
    have : G 0 = (L : ℂ) := by
      simp only [hG, Nat.sub_zero, Nat.add_zero]
      rw [show (∑ x ∈ Finset.range L, eC (f x - f x)) = ∑ _x ∈ Finset.range L, (1:ℂ) from
        Finset.sum_congr rfl (fun x _ => by rw [sub_self]; simp)]
      simp
    rw [this]; simp
  have hsplit : ∑ h ∈ Finset.range L, ‖G h‖
      = ‖G 0‖ + ∑ h ∈ (Finset.range L).filter (fun h => 1 ≤ h), ‖G h‖ := by
    have hnot : (Finset.range L).filter (fun h => ¬ (1 ≤ h)) = {0} := by
      ext h; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
    have hs := Finset.sum_filter_add_sum_filter_not (Finset.range L) (fun h => 1 ≤ h) (fun h => ‖G h‖)
    rw [hnot] at hs
    simp only [Finset.sum_singleton] at hs
    linarith
  have htail : δ ^ 2 * (L : ℝ) ^ 2 / 4 ≤ ∑ h ∈ (Finset.range L).filter (fun h => 1 ≤ h), ‖G h‖ := by
    have hLge : (L : ℝ) ≤ δ ^ 2 * (L : ℝ) ^ 2 / 4 := by
      have h16 : (16 : ℝ) ≤ δ ^ 2 * (L : ℝ) := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < δ^2)] at hL; linarith
      nlinarith [hLpos, h16]
    have := key; rw [hsplit, hG0] at this; linarith
  refine ⟨((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => τ ≤ ‖G h‖), ?_, ?_, ?_⟩
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hh ⊢; omega
  · by_contra hlt
    push Not at hlt
    have hbound : ∑ h ∈ (Finset.range L).filter (fun h => 1 ≤ h), ‖G h‖
        ≤ ((((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => τ ≤ ‖G h‖)).card : ℝ)
            * (L : ℝ) + (L : ℝ) * τ := by
      rw [← Finset.sum_filter_add_sum_filter_not ((Finset.range L).filter (fun h => 1 ≤ h))
              (fun h => τ ≤ ‖G h‖) (fun h => ‖G h‖)]
      apply add_le_add
      · calc _ ≤ ∑ _h ∈ ((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => τ ≤ ‖G h‖),
                (L : ℝ) := Finset.sum_le_sum (fun h hh =>
                  le_trans (hnorm_le h) (by exact_mod_cast Nat.sub_le L h))
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      · calc _ ≤ ∑ _h ∈ ((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => ¬ τ ≤ ‖G h‖), τ :=
              Finset.sum_le_sum (fun h hh => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hh).2))
          _ = ((((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => ¬ τ ≤ ‖G h‖)).card : ℝ) * τ := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (((Finset.range L).filter (fun h => 1 ≤ h)).card : ℝ) * τ := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hτpos)
              exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
          _ ≤ (L : ℝ) * τ := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hτpos)
              have h2 := Finset.card_le_card (Finset.filter_subset (fun h => 1 ≤ h) (Finset.range L))
              simp only [Finset.card_range] at h2
              exact_mod_cast h2
    have h1 : δ ^ 2 * (L : ℝ) ^ 2 / 4 ≤
        ((((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => τ ≤ ‖G h‖)).card : ℝ)
          * (L : ℝ) + (L : ℝ) * τ := le_trans htail hbound
    have h2 : ((((Finset.range L).filter (fun h => 1 ≤ h)).filter (fun h => τ ≤ ‖G h‖)).card : ℝ)
          * (L : ℝ) + (L : ℝ) * τ < δ ^ 2 * (L : ℝ) ^ 2 / 4 := by
      rw [hτ] at hlt ⊢; nlinarith [hlt, hLpos]
    linarith
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_range] at hd
    obtain ⟨⟨hdL, hd1⟩, hdτ⟩ := hd
    have hnorm : ‖G d‖ ≤ ((L - d : ℕ) : ℝ) := hnorm_le d
    have hτd : τ ≤ ((L - d : ℕ) : ℝ) := le_trans hdτ hnorm
    refine ⟨?_, ?_⟩
    · have h1 : min (δ ^ 2 / 8) (1 / 2) * (L : ℝ) ≤ δ ^ 2 / 8 * (L : ℝ) :=
        mul_le_mul_of_nonneg_right hδ₁le (le_of_lt hLpos)
      rw [hτ] at hτd; linarith
    · calc min (δ ^ 2 / 8) (1 / 2) * ((L - d : ℕ) : ℝ)
          ≤ δ ^ 2 / 8 * ((L - d : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hδ₁le (by positivity)
        _ ≤ δ ^ 2 / 8 * (L : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le L d) (by positivity)
        _ = τ := by rw [hτ]
        _ ≤ ‖G d‖ := hdτ
        _ = ‖∑ x ∈ Finset.range (L - d), eC (f (x + d) - f x)‖ := rfl

/-! ## Elementary helper lemmas -/

lemma eC_mul_nat (a : ℝ) : ∀ n : ℕ, eC (a * (n : ℝ)) = (eC a) ^ n := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, mul_zero, eC_zero', pow_zero]
  | succ n ih =>
      rw [show a * (((n+1 : ℕ)) : ℝ) = a * (n:ℝ) + a by push_cast; ring, eC_add', ih, pow_succ]

lemma linPhase_eq_eC (a : ℝ) (n : ℕ) : Submission.VanDerCorput.linPhase a n = eC (a * (n:ℝ)) := by
  rw [Submission.VanDerCorput.linPhase, eC]
  congr 1
  push_cast
  ring

lemma exists_int_le_intDist (x : ℝ) :
    ∃ m : ℤ, |x - (m:ℝ)| ≤ Submission.VanDerCorput.intDist x := by
  by_cases h : Int.fract x ≤ 1 / 2
  · refine ⟨⌊x⌋, ?_⟩
    rw [Submission.IntDistRegion.abs_sub_floor_eq_fract]
    simp only [Submission.VanDerCorput.intDist]
    rw [min_eq_left (by linarith [h] : Int.fract x ≤ 1 - Int.fract x)]
  · refine ⟨⌊x⌋ + 1, ?_⟩
    rw [Submission.IntDistRegion.abs_sub_floor_add_one]
    simp only [Submission.VanDerCorput.intDist]
    rw [min_eq_right (by linarith [lt_of_not_ge h] : 1 - Int.fract x ≤ Int.fract x)]

lemma eval_eq_sum_range_of_natDegree_le (P : Polynomial ℝ) (K : ℕ) (hP : P.natDegree ≤ K) (x : ℝ) :
    P.eval x = ∑ j ∈ Finset.range (K+1), P.coeff j * x ^ j :=
  Polynomial.eval_eq_sum_range' (by omega) x

lemma taylor_sub_eval (P : Polynomial ℝ) (d n : ℕ) :
    (Polynomial.taylor (d:ℝ) P - P).eval (n:ℝ) = P.eval ((n+d:ℕ):ℝ) - P.eval (n:ℝ) := by
  rw [Polynomial.eval_sub, Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
  congr 2
  push_cast; ring

/-! ## The Weyl inverse statement (polynomial form) -/

def WeylInvP (k : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ), 1 ≤ L → ∀ (P : Polynomial ℝ),
    P.natDegree ≤ k →
    δ * (L : ℝ) ≤ ‖∑ n ∈ Finset.range L, eC (P.eval (n : ℝ))‖ →
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C ∧
      ∀ j ∈ Finset.Icc 1 k, ∃ m : ℤ, |(q : ℝ) * P.coeff j - m| ≤ C / (L : ℝ) ^ j

theorem weylInvP_zero : WeylInvP 0 := by
  intro δ hδ
  refine ⟨1, one_pos, ?_⟩
  intro L hL P hP hbig
  refine ⟨1, le_refl 1, by norm_num, ?_⟩
  intro j hj
  rw [Finset.mem_Icc] at hj
  exact absurd hj.2 (by omega)

theorem weylInvP_one : WeylInvP 1 := by
  intro δ hδ
  refine ⟨max 1 (1/(2*δ)) + 1, by positivity, ?_⟩
  intro L hL P hP hbig
  have hPeval : ∀ x : ℝ, P.eval x = P.coeff 0 + P.coeff 1 * x := by
    intro x
    rw [eval_eq_sum_range_of_natDegree_le P 1 hP x, Finset.sum_range_succ, Finset.sum_range_one]
    ring
  have hsum_eq : (∑ n ∈ Finset.range L, eC (P.eval (n:ℝ)))
      = eC (P.coeff 0) * ∑ n ∈ Finset.range L, (eC (P.coeff 1))^n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [hPeval, eC_add', eC_mul_nat]
  have hbc : δ * (L:ℝ) ≤ ‖∑ n ∈ Finset.range L, (eC (P.coeff 1))^n‖ := by
    have h := hbig
    rw [hsum_eq, norm_mul, norm_eC', one_mul] at h
    exact h
  -- bound intDist(P.coeff 1)
  have hkey : Submission.VanDerCorput.intDist (P.coeff 1) ≤ 1/(2*δ*(L:ℝ)) := by
    by_cases hcc : Submission.VanDerCorput.intDist (P.coeff 1) = 0
    · rw [hcc]; positivity
    · have hpos : 0 < Submission.VanDerCorput.intDist (P.coeff 1) := lt_of_le_of_ne
        (Submission.VanDerCorput.intDist_nonneg _) (Ne.symm hcc)
      have h1 : ‖∑ n ∈ Finset.range L, Submission.VanDerCorput.linPhase (P.coeff 1) n‖
          ≤ (1/2) / Submission.VanDerCorput.intDist (P.coeff 1) :=
        Submission.UnitCircle.geom_sum_bound_of_intDist_pos hpos
      have h2 : (∑ n ∈ Finset.range L, Submission.VanDerCorput.linPhase (P.coeff 1) n)
          = ∑ n ∈ Finset.range L, (eC (P.coeff 1))^n := by
        apply Finset.sum_congr rfl; intro n _
        rw [linPhase_eq_eC, eC_mul_nat]
      rw [h2] at h1
      have h3 : δ * (L:ℝ) ≤ (1/2) / Submission.VanDerCorput.intDist (P.coeff 1) := le_trans hbc h1
      have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast hL
      have hδL : 0 < δ * (L:ℝ) := mul_pos hδ hLpos
      rw [le_div_iff₀ hpos] at h3
      -- h3 : δ*L * intDist ≤ 1/2
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*δ*(L:ℝ))]
      nlinarith [h3, hδL]
  obtain ⟨m, hm⟩ := exists_int_le_intDist (P.coeff 1)
  refine ⟨1, le_refl 1, ?_, ?_⟩
  · have h2 : (1:ℝ) ≤ max 1 (1/(2*δ)) := le_max_left _ _
    linarith
  intro j hj
  have hj1 : j = 1 := by rw [Finset.mem_Icc] at hj; omega
  subst hj1
  refine ⟨m, ?_⟩
  simp only [Nat.cast_one, one_mul]
  calc |P.coeff 1 - (m:ℝ)|
      ≤ Submission.VanDerCorput.intDist (P.coeff 1) := hm
      _ ≤ 1/(2*δ*(L:ℝ)) := hkey
      _ ≤ (max 1 (1/(2*δ)) + 1) / (L:ℝ)^1 := by
          rw [pow_one, div_le_div_iff₀ (by positivity) (by exact_mod_cast hL)]
          have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast hL
          have h6 : (1/(2*δ)) * (2*δ) = 1 := by field_simp
          have h8 : (1/(2*δ) + 1) * (2*δ) = 1 + 2*δ := by
            rw [add_mul, one_mul, h6]
          have h9 : (1/(2*δ) + 1) ≤ max 1 (1/(2*δ)) + 1 := by
            have h4 : (1/(2*δ)) ≤ max 1 (1/(2*δ)) := le_max_right _ _
            linarith
          have h10 : (1:ℝ) ≤ (max 1 (1/(2*δ)) + 1) * (2*δ) := by
            have h11 := mul_le_mul_of_nonneg_right h9 (by positivity : (0:ℝ) ≤ 2*δ)
            rw [h8] at h11
            nlinarith [h11, hδ]
          nlinarith [h10, hLpos]

theorem weylInvP_succ (k : ℕ) (hk : 1 ≤ k) (H : WeylInvP k) : WeylInvP (k + 1) := by
  intro δ hδ
  obtain ⟨δ₁, hδ₁pos, hδ₁half, hshift⟩ := diff_shift_exists δ hδ
  obtain ⟨Ck, hCkpos, hCk⟩ := H δ₁ hδ₁pos
  set B : ℕ := ⌈Ck⌉₊ + 1 with hBdef
  have hB1 : 1 ≤ B := by rw [hBdef]; omega
  have hBCk : (Ck : ℝ) ≤ (B : ℝ) := by
    have h1 : (Ck : ℝ) ≤ (⌈Ck⌉₊ : ℝ) := Nat.le_ceil Ck
    have h2 : ((⌈Ck⌉₊ : ℕ) : ℝ) ≤ (B : ℝ) := by rw [hBdef]; push_cast; linarith
    linarith
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB1
  set δ₄ : ℝ := δ₁ / (2 * (B:ℝ)) with hδ₄def
  have hδ₄pos : 0 < δ₄ := by rw [hδ₄def]; positivity
  have hδ₄half : δ₄ ≤ 1/2 := by
    have hB1' : (1:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB1
    rw [hδ₄def, div_le_iff₀ (by positivity : (0:ℝ) < 2*(B:ℝ))]
    nlinarith [hδ₁half, hB1']
  obtain ⟨C₁, hC₁pos, hdesc⟩ := descent_coeff k Ck (B:ℝ) δ₁ δ₄ hCkpos
    (by exact_mod_cast hB1) hδ₁pos hδ₄pos hδ₄half
  obtain ⟨C₂, hC₂pos, ha1⟩ := Work.BMF.SD.FreeA.a_one_bound (k+1) (by omega) δ hδ (max C₁ 1) (le_max_right _ _)
  set L₀ : ℝ := max (16 / δ^2) (max (1/δ₁) (max (100 * Ck / (δ₄^2 * δ₁)) (max 2 (max C₁ 1)))) with hL₀def
  have hL₀2 : (2:ℝ) ≤ L₀ := by
    rw [hL₀def]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hL₀1 : (1:ℝ) ≤ L₀ := le_trans (by norm_num) hL₀2
  have hL₀16 : (16:ℝ)/δ^2 ≤ L₀ := by rw [hL₀def]; exact le_max_left _ _
  have hL₀1δ : (1:ℝ)/δ₁ ≤ L₀ := by
    rw [hL₀def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hL₀100 : 100 * Ck / (δ₄^2 * δ₁) ≤ L₀ := by
    rw [hL₀def]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hL₀C₁ : C₁ ≤ L₀ := by
    rw [hL₀def]
    exact le_trans (le_max_left C₁ 1) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hL₀max : max C₁ 1 ≤ L₀ := by
    rw [hL₀def]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  set C : ℝ := max (max C₁ (C₂ * (C₁ + 1) + 1) + 1) (L₀^(k+1)/2 + 1) with hCdef
  have hCC₁ : C₁ ≤ C := by
    rw [hCdef]
    have h1 : C₁ ≤ max C₁ (C₂ * (C₁ + 1) + 1) := le_max_left _ _
    have h2 : max C₁ (C₂ * (C₁ + 1) + 1) ≤ max C₁ (C₂ * (C₁ + 1) + 1) + 1 := by linarith
    have h3 : max C₁ (C₂ * (C₁ + 1) + 1) + 1 ≤
        max (max C₁ (C₂ * (C₁ + 1) + 1) + 1) (L₀^(k+1)/2 + 1) := le_max_left _ _
    linarith
  have hCC₂ : C₂ * (C₁ + 1) ≤ C := by
    rw [hCdef]
    have h1 : C₂ * (C₁ + 1) ≤ max C₁ (C₂ * (C₁ + 1) + 1) := by
      have h := le_max_right C₁ (C₂ * (C₁ + 1) + 1); linarith
    have h2 : max C₁ (C₂ * (C₁ + 1) + 1) ≤ max C₁ (C₂ * (C₁ + 1) + 1) + 1 := by linarith
    have h3 : max C₁ (C₂ * (C₁ + 1) + 1) + 1 ≤
        max (max C₁ (C₂ * (C₁ + 1) + 1) + 1) (L₀^(k+1)/2 + 1) := le_max_left _ _
    linarith
  have hC1 : (1:ℝ) ≤ C := by
    rw [hCdef]
    refine le_trans ?_ (le_max_left _ _)
    have h2 : (0:ℝ) ≤ max C₁ (C₂ * (C₁ + 1) + 1) :=
      le_trans (le_of_lt hC₁pos) (le_max_left _ _)
    linarith
  have hCL₀ : L₀^(k+1)/2 + 1 ≤ C := by rw [hCdef]; exact le_max_right _ _
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC1, ?_⟩
  intro L hL1 P hPnat hbig
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast hL1
  by_cases hcase : L₀ < (L:ℝ)
  · have hL16 : (16:ℝ)/δ^2 ≤ (L:ℝ) := le_trans hL₀16 (le_of_lt hcase)
    have hL2 : 2 ≤ L := by
      have h : (2:ℝ) ≤ (L:ℝ) := le_trans hL₀2 (le_of_lt hcase)
      exact_mod_cast h
    have hLδ₁ : 1 ≤ δ₁ * (L:ℝ) := by
      have h1 : 1/δ₁ ≤ (L:ℝ) := le_trans hL₀1δ (le_of_lt hcase)
      have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hδ₁pos)
      rw [mul_one_div, div_self (ne_of_gt hδ₁pos)] at h2
      exact h2
    have hCkL : Ck ≤ δ₄^2 * (δ₁ * (L:ℝ)) / 100 := by
      have h1 : 100 * Ck / (δ₄^2 * δ₁) ≤ (L:ℝ) := le_trans hL₀100 (le_of_lt hcase)
      have h2 : 0 < δ₄^2 * δ₁ := by positivity
      rw [div_le_iff₀ h2] at h1
      have h3 : Ck * 100 ≤ δ₄^2 * δ₁ * (L:ℝ) := by linarith
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 100)]
      linarith
    have hC₁L : C₁ ≤ (L:ℝ) := le_trans hL₀C₁ (le_of_lt hcase)
    obtain ⟨D, hDsub, hDcard, hDprop⟩ := hshift L (fun n => P.eval (n:ℝ)) hL16 hbig
    have hex : ∀ d : ℕ, d ∈ D → ∃ qd : ℕ, 1 ≤ qd ∧ (qd:ℝ) ≤ Ck ∧ (∀ i ∈ Finset.Icc 1 k,
        ∃ m : ℤ, |(qd:ℝ) * (∑ j ∈ Finset.Icc (i+1) (k+1), P.coeff j * (d:ℝ)^(j-i) * ((j.choose i:ℕ):ℝ)) - m|
          ≤ Ck / (((L-d:ℕ)):ℝ)^i) := by
      intro d hd
      obtain ⟨hdd1, hdLd⟩ := hDprop d hd
      have hdd : d < L := by
        have h := hDsub hd; rw [Finset.mem_Icc] at h; omega
      have hLd1 : 1 ≤ L - d := by omega
      have hdeg : (Polynomial.taylor (d:ℝ) P - P).natDegree ≤ k := (taylor_sub_coeff_aux k d P hPnat).1
      have hNN : δ₁ * ((L - d : ℕ):ℝ) ≤
          ‖∑ x ∈ Finset.range (L-d), eC (P.eval ((x+d:ℕ):ℝ) - P.eval (x:ℝ))‖ := hdLd
      have hsum : δ₁ * ((L - d : ℕ):ℝ) ≤
          ‖∑ n ∈ Finset.range (L - d), eC ((Polynomial.taylor (d:ℝ) P - P).eval (n:ℝ))‖ := by
        rw [show (∑ n ∈ Finset.range (L-d), eC ((Polynomial.taylor (d:ℝ) P - P).eval (n:ℝ)))
            = ∑ n ∈ Finset.range (L-d), eC (P.eval ((n+d:ℕ):ℝ) - P.eval (n:ℝ)) from
          Finset.sum_congr rfl (fun n _ => by rw [taylor_sub_eval])]
        exact hNN
      obtain ⟨qd, hqd1, hqd2, hqd3⟩ := hCk (L-d) hLd1 (Polynomial.taylor (d:ℝ) P - P) hdeg hsum
      refine ⟨qd, hqd1, hqd2, ?_⟩
      intro i hi
      obtain ⟨m, hm⟩ := hqd3 i hi
      exact ⟨m, by rwa [(taylor_sub_coeff_aux k d P hPnat).2 i] at hm⟩
    classical
    let qd : ℕ → ℕ := fun d => if h : d ∈ D then Classical.choose (hex d h) else 1
    have hqd_spec : ∀ d (hd : d ∈ D), 1 ≤ qd d ∧ (qd d:ℝ) ≤ Ck ∧ (∀ i ∈ Finset.Icc 1 k,
        ∃ m : ℤ, |(qd d:ℝ) * (∑ j ∈ Finset.Icc (i+1) (k+1), P.coeff j * (d:ℝ)^(j-i) * ((j.choose i:ℕ):ℝ)) - m|
          ≤ Ck / (((L-d:ℕ)):ℝ)^i) := by
      intro d hd
      have hh := Classical.choose_spec (hex d hd)
      simpa only [qd, dif_pos hd] using hh
    have hqd_lo : ∀ d ∈ D, 1 ≤ qd d := fun d hd => (hqd_spec d hd).1
    have hqd_hi : ∀ d ∈ D, qd d ≤ B := by
      intro d hd
      have h := (hqd_spec d hd).2.1
      exact_mod_cast (le_trans h hBCk)
    obtain ⟨q, hq1, hqB, hqcard⟩ := fiber_card_ge D B qd hB1 hqd_lo hqd_hi
    set D' : Finset ℕ := D.filter (fun d => qd d = q) with hD'def
    have hD'card : δ₄ * (L:ℝ) ≤ (D'.card : ℝ) := by
      have hb : δ₄ * (L:ℝ) ≤ (D.card:ℝ)/(B:ℝ) := by
        rw [hδ₄def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hBpos]
        nlinarith [hBpos, hδ₁pos, hDcard]
      linarith [hb, hqcard]
    have hD'sub : ∀ d ∈ D', 1 ≤ d ∧ δ₁ * (L:ℝ) ≤ ((L-d:ℕ):ℝ) := by
      intro d hd
      have hdD : d ∈ D := (Finset.mem_filter.mp hd).1
      obtain ⟨h1, h2⟩ := hDprop d hdD
      exact ⟨(Finset.mem_Icc.mp (hDsub hdD)).1, h1⟩
    have hD'cond : ∀ d ∈ D', ∀ i ∈ Finset.Icc 1 k, ∃ m : ℤ,
        |(q:ℝ) * (∑ j ∈ Finset.Icc (i+1) (k+1), P.coeff j * (d:ℝ)^(j-i) * ((j.choose i:ℕ):ℝ)) - m|
          ≤ Ck / (((L-d:ℕ)):ℝ)^i := by
      intro d hd i hi
      have hdD : d ∈ D := (Finset.mem_filter.mp hd).1
      have heq : qd d = q := (Finset.mem_filter.mp hd).2
      have := (hqd_spec d hdD).2.2 i hi
      rwa [heq] at this
    obtain ⟨Q, hQ1, hQle, hQcond⟩ := hdesc L q D' (fun j => P.coeff j) hL2 hq1
      (by exact_mod_cast hqB) hLδ₁ hCkL hD'card hD'sub hD'cond
    have hQle2 : (Q:ℝ) ≤ max C₁ 1 := le_trans hQle (le_max_left _ _)
    have hsumP : (∑ n ∈ Finset.range L, eC (∑ j ∈ Finset.range ((k+1)+1), P.coeff j * (n:ℝ)^j))
        = ∑ n ∈ Finset.range L, eC (P.eval (n:ℝ)) := by
      apply Finset.sum_congr rfl
      intro n _
      congr 1
      exact (eval_eq_sum_range_of_natDegree_le P (k+1) hPnat (n:ℝ)).symm
    have hmaxL : max C₁ 1 ≤ (L:ℝ) := le_trans hL₀max (le_of_lt hcase)
    obtain ⟨m₁, hm₁⟩ := ha1 L Q (fun j => P.coeff j) C₁ hL2 hmaxL hQ1 hQle2 (le_of_lt hC₁pos)
      hQcond (by rw [hsumP]; exact hbig)
    refine ⟨Q, hQ1, le_trans hQle hCC₁, ?_⟩
    intro j hj
    have hjle : j ≤ k+1 := (Finset.mem_Icc.mp hj).2
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    by_cases hje : j = 1
    · subst hje
      refine ⟨m₁, ?_⟩
      calc |(Q:ℝ) * P.coeff 1 - (m₁:ℝ)| ≤ C₂ * (C₁+1) / (L:ℝ) := hm₁
        _ ≤ C / (L:ℝ)^1 := by
            rw [pow_one, div_le_div_iff₀ hLpos hLpos]
            nlinarith [hCC₂, hLpos]
    · have hj2 : 2 ≤ j := by omega
      obtain ⟨m, hm⟩ := hQcond j (by rw [Finset.mem_Icc]; exact ⟨hj2, hjle⟩)
      refine ⟨m, ?_⟩
      calc |(Q:ℝ)*P.coeff j - (m:ℝ)| ≤ C₁/(L:ℝ)^j := hm
        _ ≤ C/(L:ℝ)^j := by
            rw [div_le_div_iff₀ (pow_pos hLpos j) (pow_pos hLpos j)]
            nlinarith [hCC₁, pow_pos hLpos j]
  · -- small L
    have hLle : (L:ℝ) ≤ L₀ := not_lt.mp hcase
    refine ⟨1, le_refl 1, by simpa using hC1, ?_⟩
    intro j hj
    refine ⟨round (P.coeff j), ?_⟩
    rw [Nat.cast_one, one_mul]
    have hjle : j ≤ k+1 := (Finset.mem_Icc.mp hj).2
    have hLj : (L:ℝ)^j ≤ L₀^(k+1) := by
      calc (L:ℝ)^j ≤ L₀^j := pow_le_pow_left₀ (le_of_lt hLpos) hLle j
        _ ≤ L₀^(k+1) := pow_le_pow_right₀ hL₀1 hjle
    have hCL : (L:ℝ)^j ≤ 2*C := by
      have h2 : L₀^(k+1)/2 + 1 ≤ C := hCL₀
      nlinarith [hLj, h2, pow_pos (lt_of_lt_of_le zero_lt_one hL₀1) (k+1)]
    calc |P.coeff j - (round (P.coeff j) : ℝ)| ≤ 1/2 := abs_sub_round _
      _ ≤ C/(L:ℝ)^j := by
          rw [div_le_div_iff₀ (by norm_num) (pow_pos hLpos j)]
          nlinarith [hCL]

theorem weylInvP_all : ∀ k : ℕ, WeylInvP k
  | 0 => weylInvP_zero
  | 1 => weylInvP_one
  | (k+2) => weylInvP_succ (k+1) (by omega) (weylInvP_all (k+1))

theorem weyl_inverse (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ → ℝ),
      δ * L ≤ ‖∑ n ∈ Finset.range L,
          Work.BMF.eC (∑ j ∈ Finset.range (k + 1), a j * (n : ℝ) ^ j)‖ →
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C ∧
        ∀ j ∈ Finset.Icc 1 k, ∃ m : ℤ, |(q : ℝ) * a j - m| ≤ C / (L : ℝ) ^ j := by
  obtain ⟨C, hCpos, hC⟩ := weylInvP_all k δ hδ
  refine ⟨C, hCpos, ?_⟩
  intro L hL a hbig
  set P : Polynomial ℝ := ∑ j ∈ Finset.range (k+1), Polynomial.monomial j (a j) with hPdef
  have hPcoeff : ∀ i ≤ k, P.coeff i = a i := by
    intro i hi
    rw [hPdef, Polynomial.finset_sum_coeff, Finset.sum_eq_single i]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro b hb hbne
      rw [Polynomial.coeff_monomial, if_neg (by omega : ¬ (b = i))]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  have hPeval : ∀ x : ℝ, P.eval x = ∑ j ∈ Finset.range (k+1), a j * x ^ j := by
    intro x
    rw [hPdef, Polynomial.eval_finset_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [Polynomial.eval_monomial])
  have hPdeg : P.natDegree ≤ k := by
    rw [hPdef]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    refine le_trans (Polynomial.natDegree_monomial_le (a j)) ?_
    rw [Finset.mem_range] at hj; omega
  have hbridge : (∑ n ∈ Finset.range L, eC (P.eval (n:ℝ)))
      = ∑ n ∈ Finset.range L, eC (∑ j ∈ Finset.range (k+1), a j * (n:ℝ)^j) :=
    Finset.sum_congr rfl (fun n _ => by rw [hPeval])
  obtain ⟨q, hq1, hqle, hq⟩ := hC L hL P hPdeg (by rw [hbridge]; exact hbig)
  refine ⟨q, hq1, hqle, ?_⟩
  intro j hj
  obtain ⟨m, hm⟩ := hq j hj
  exact ⟨m, by rwa [hPcoeff j (Finset.mem_Icc.mp hj).2] at hm⟩

end
end Work.BMF.SD.FreeW
