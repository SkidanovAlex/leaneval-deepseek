import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors
import Submission.Commons.Data.Nat.squarefree_prod_primes

namespace Commons.NumberTheory.EulerProduct

open scoped BigOperators

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Auxiliary lemmas -/

private lemma coprime_factorization_eq_zero_or {n k : ℕ} (h : Nat.Coprime n k) (p : ℕ) :
    n.factorization p = 0 ∨ k.factorization p = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · right
    rw [Nat.coprime_zero_left] at h
    rw [h, Nat.factorization_one]; rfl
  rcases eq_or_ne k 0 with rfl | hk
  · left
    rw [Nat.coprime_zero_right] at h
    rw [h, Nat.factorization_one]; rfl
  have hg : Nat.gcd n k = 1 := h
  have hfac := Nat.factorization_gcd hn hk
  rw [hg] at hfac
  have := congrFun (congrArg DFunLike.coe hfac) p
  simp only [Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, Finsupp.inf_apply] at this
  have hmin : min (n.factorization p) (k.factorization p) = 0 := this.symm
  omega

private lemma lcm_mul_coprime_right {m n k : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hk : k ≠ 0)
    (h : Nat.Coprime n k) : Nat.lcm (m * n) k = n * Nat.lcm m k := by
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  have hlcmk : Nat.lcm m k ≠ 0 := Nat.lcm_ne_zero hm hk
  refine Nat.eq_of_factorization_eq (Nat.lcm_ne_zero hmn hk) (Nat.mul_ne_zero hn hlcmk) ?_
  intro p
  rw [Nat.factorization_lcm hmn hk, Nat.factorization_mul hn hlcmk,
      Nat.factorization_mul hm hn, Nat.factorization_lcm hm hk]
  simp only [Finsupp.sup_apply, Finsupp.add_apply]
  rcases coprime_factorization_eq_zero_or h p with hz | hz
  · rw [hz]; omega
  · rw [hz]; omega

private lemma g_prod_of_pairwise {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (h1 : g 1 = 1) :
    ∀ (s : Finset ℕ) (f : ℕ → ℕ),
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Nat.Coprime (f p) (f q)) →
      g (∏ p ∈ s, f p) = ∏ p ∈ s, g (f p) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro f _; simp [h1]
  | insert a t ha ih =>
    intro f hpair
    have hpair_t : ∀ p ∈ t, ∀ q ∈ t, p ≠ q → Nat.Coprime (f p) (f q) :=
      fun p hp q hq hpq => hpair p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq) hpq
    have hcop : Nat.Coprime (f a) (∏ p ∈ t, f p) := by
      rw [Nat.coprime_prod_right_iff]
      intro p hp
      exact hpair a (Finset.mem_insert_self a t) p (Finset.mem_insert_of_mem hp) (fun h => ha (h ▸ hp))
    have h1' : g (∏ p ∈ insert a t, f p) = g (f a) * g (∏ p ∈ t, f p) := by
      rw [Finset.prod_insert ha, hmul (f a) _ hcop]
    have h2 : ∏ p ∈ insert a t, g (f p) = g (f a) * ∏ p ∈ t, g (f p) := by
      rw [Finset.prod_insert ha]
    rw [h1', h2, ih f hpair_t]

private lemma lcm_sq_eq_mul_of_dvd_squarefree {a d : ℕ} (had : a ∣ d) (hd : Squarefree d) :
    Nat.lcm (a ^ 2) d = a * d := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have ha0 : a ≠ 0 := by rintro rfl; exact hd0 (Nat.eq_zero_of_zero_dvd had)
  refine Nat.eq_of_factorization_eq (Nat.lcm_ne_zero (pow_ne_zero 2 ha0) hd0)
    (Nat.mul_ne_zero ha0 hd0) ?_
  intro p
  have hv_d_le : d.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hd0).mp hd p
  have hv_a_le_d : a.factorization p ≤ d.factorization p :=
    ((Nat.factorization_le_iff_dvd ha0 hd0).mpr had) p
  rw [Nat.factorization_lcm (pow_ne_zero 2 ha0) hd0, Nat.factorization_mul ha0 hd0,
      Nat.factorization_pow]
  simp only [Finsupp.sup_apply, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
  omega

private lemma moebius_eq_prod_neg_one_real {n : ℕ} (hn : Squarefree n) :
    (ArithmeticFunction.moebius n : ℝ) = ∏ _p ∈ n.primeFactors, (-1 : ℝ) := by
  have hcard : ArithmeticFunction.cardFactors n = n.primeFactors.card := by
    rw [ArithmeticFunction.cardFactors_apply,
      ← List.toFinset_card_of_nodup hn.nodup_primeFactorsList]
    simp
  rw [ArithmeticFunction.moebius_apply_of_squarefree hn, hcard, Finset.prod_const]
  push_cast
  rfl

private lemma moebius_apply_zero : ArithmeticFunction.moebius 0 = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree not_squarefree_zero

/-- Linear-bound Euler product. -/
private def hf0 (f : ℕ → ℝ) (n : ℕ) : ℝ := if n.Prime then -f n else 0
private def hfS (f : ℕ → ℝ) (S : Finset ℕ) : ℝ := ∏ n ∈ S, hf0 f n
private lemma hf0_ne_zero {f : ℕ → ℝ} {n : ℕ} : hf0 f n ≠ 0 ↔ n.Prime ∧ f n ≠ 0 := by
  by_cases hp : n.Prime <;> simp [hf0, hp]
private lemma prime_of_hfS_ne_zero {f : ℕ → ℝ} {S : Finset ℕ} (hS : hfS f S ≠ 0) :
    ∀ n ∈ S, n.Prime := by
  intro n hn
  rw [hfS, Finset.prod_ne_zero_iff] at hS
  exact (hf0_ne_zero.mp (hS n hn)).1
private lemma hfS_eq_prod_neg {f : ℕ → ℝ} {S : Finset ℕ} (hS : ∀ n ∈ S, n.Prime) :
    hfS f S = ∏ n ∈ S, (-f n) :=
  Finset.prod_congr rfl fun n hn => by simp [hf0, hS n hn]
private lemma moebius_term_eq {f : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (h1 : f 1 = 1)
    {S : Finset ℕ} (hS : ∀ n ∈ S, n.Prime) :
    ((ArithmeticFunction.moebius (∏ n ∈ S, n) : ℤ) : ℝ) * f (∏ n ∈ S, n) = hfS f S := by
  have hpr : (∏ n ∈ S, n).primeFactors = S := Nat.primeFactors_prod hS
  have hsq : Squarefree (∏ n ∈ S, n) := Commons.Data.Nat.squarefree_prod_primes hS
  have hfprod : f (∏ n ∈ S, n) = ∏ n ∈ S, f n := by
    rw [Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors f hmul h1 hsq, hpr]
  have hmu : ((ArithmeticFunction.moebius (∏ n ∈ S, n) : ℤ) : ℝ) = ∏ n ∈ S, (-1 : ℝ) := by
    rw [moebius_eq_prod_neg_one_real hsq, hpr]
  calc ((ArithmeticFunction.moebius (∏ n ∈ S, n) : ℤ) : ℝ) * f (∏ n ∈ S, n)
      = (∏ n ∈ S, (-1 : ℝ)) * (∏ n ∈ S, f n) := by rw [hmu, hfprod]
    _ = ∏ n ∈ S, ((-1 : ℝ) * f n) := Finset.prod_mul_distrib.symm
    _ = ∏ n ∈ S, (-f n) := Finset.prod_congr rfl fun n _ => by rw [neg_one_mul]
    _ = hfS f S := (hfS_eq_prod_neg hS).symm

private theorem tsum_moebius_mul_eq_tprod_of_le {f : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (h1 : f 1 = 1)
    {C : ℝ} (hC : 0 ≤ C) (hbd : ∀ p : ℕ, p.Prime → |f p| ≤ C / (p : ℝ) ^ 2) :
    (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) * f n)
      = ∏' p : {p : ℕ // p.Prime}, (1 - f p) := by
  classical
  have hbd_lin : ∀ n : ℕ, ‖hf0 f n‖ ≤ C / (n : ℝ) ^ 2 := by
    intro n
    by_cases hp : n.Prime
    · rw [hf0, if_pos hp, norm_neg, Real.norm_eq_abs]
      exact hbd n hp
    · rw [hf0, if_neg hp, norm_zero]
      exact div_nonneg hC (sq_nonneg _)
  have hbase : Summable (fun n : ℕ => C / (n : ℝ) ^ 2) := by
    have h := ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : (1:ℕ) < 2)).mul_left C
    simpa [div_eq_mul_inv] using h
  have hsum_F0 : Summable (fun n : ℕ => ‖hf0 f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hbd_lin n) hbase
  have hsum_g : Summable (hfS f) := summable_finsetProd_of_summable_norm hsum_F0
  have htprod : ∏' n : ℕ, (1 + hf0 f n) = ∑' S : Finset ℕ, hfS f S := tprod_one_add hsum_g
  have hprod_sub : ∏' n : ℕ, (1 + hf0 f n)
      = ∏' p : {p : ℕ // p.Prime}, (1 - f p) := by
    have hsub : (∏' p : {p : ℕ // p.Prime}, (1 - f p))
        = ∏' n : ℕ, (Set.mulIndicator {n : ℕ | n.Prime} (fun n => 1 - f n)) n :=
      tprod_subtype {n : ℕ | n.Prime} (fun n => 1 - f n)
    rw [hsub]
    refine tprod_congr fun n => ?_
    by_cases hp : n.Prime
    · simp only [hf0, Set.mulIndicator_apply, Set.mem_ofPred_eq, hp, if_true]
      ring
    · simp only [hf0, Set.mulIndicator_apply, Set.mem_ofPred_eq, hp, if_false]
      ring
  have hHasSum_g : HasSum (hfS f) (∏' p : {p : ℕ // p.Prime}, (1 - f p)) := by
    have hh := hsum_g.hasSum
    rw [← htprod] at hh
    rw [hprod_sub] at hh
    exact hh
  have hmain : ∀ S : Finset ℕ, (∀ n ∈ S, n.Prime) →
      ((ArithmeticFunction.moebius (∏ n ∈ S, n) : ℤ) : ℝ) * f (∏ n ∈ S, n) = hfS f S :=
    fun S hS => moebius_term_eq hmul h1 hS
  have key : HasSum (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * f n)
        (∏' p : {p : ℕ // p.Prime}, (1 - f p))
      ↔ HasSum (hfS f) (∏' p : {p : ℕ // p.Prime}, (1 - f p)) :=
    hasSum_iff_hasSum_of_ne_zero_bij
      (a := ∏' p : {p : ℕ // p.Prime}, (1 - f p))
      (f := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * f n)
      (g := hfS f)
      (i := fun x : ↑(Function.support (hfS f)) => ∏ n ∈ (x : Finset ℕ), n)
      (by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
        have hxp : ∀ n ∈ x, n.Prime := prime_of_hfS_ne_zero hx
        have hyp : ∀ n ∈ y, n.Prime := prime_of_hfS_ne_zero hy
        have hxy'' : (∏ p ∈ (x : Finset ℕ), p) = (∏ p ∈ (y : Finset ℕ), p) := hxy
        have hxy' : (x : Finset ℕ) = y := by
          rw [← Nat.primeFactors_prod hxp, hxy'', Nat.primeFactors_prod hyp]
        exact Subtype.ext hxy')
      (by
        intro n hn
        rw [Function.mem_support] at hn
        have hmu_ne : ArithmeticFunction.moebius n ≠ 0 := by
          intro hzero
          rw [hzero] at hn
          simp at hn
        have hsq : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu_ne
        refine ⟨⟨n.primeFactors, ?_⟩, ?_⟩
        · rw [Function.mem_support,
            ← hmain n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp),
            Nat.prod_primeFactors_of_squarefree hsq]
          exact hn
        · exact Nat.prod_primeFactors_of_squarefree hsq)
      (by
        rintro ⟨S, hS⟩
        exact hmain S (prime_of_hfS_ne_zero hS))
  exact (key.mpr hHasSum_g).tsum_eq

private noncomputable def hcoprime (g : ℕ → ℝ) (d n : ℕ) : ℝ :=
  if Nat.Coprime n d then g (n ^ 2) else 0

private lemma hcoprime_mul (d : ℕ) {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) :
    ∀ m n : ℕ, Nat.Coprime m n → hcoprime g d (m * n) = hcoprime g d m * hcoprime g d n := by
  intro m n hmn
  have hcop : Nat.Coprime (m * n) d ↔ Nat.Coprime m d ∧ Nat.Coprime n d :=
    Nat.coprime_mul_iff_left
  by_cases hmd : Nat.Coprime m d <;> by_cases hnd : Nat.Coprime n d
  · have hmn_d : Nat.Coprime (m * n) d := hcop.mpr ⟨hmd, hnd⟩
    rw [hcoprime, if_pos hmn_d, hcoprime, if_pos hmd, hcoprime, if_pos hnd]
    rw [show (m*n)^2 = m^2 * n^2 by ring]
    rw [hmul (m^2) (n^2) (hmn.pow 2 2)]
  · have hmn_d : ¬ Nat.Coprime (m * n) d := fun h => hnd ((hcop.mp h).2)
    rw [hcoprime, if_neg hmn_d, hcoprime, if_pos hmd, hcoprime, if_neg hnd]
    ring
  · have hmn_d : ¬ Nat.Coprime (m * n) d := fun h => hmd ((hcop.mp h).1)
    rw [hcoprime, if_neg hmn_d, hcoprime, if_neg hmd, hcoprime, if_pos hnd]
    ring
  · have hmn_d : ¬ Nat.Coprime (m * n) d := fun h => hmd ((hcop.mp h).1)
    rw [hcoprime, if_neg hmn_d, hcoprime, if_neg hmd, hcoprime, if_neg hnd]
    ring

private lemma hcoprime_one (d : ℕ) {g : ℕ → ℝ} (h1 : g 1 = 1) : hcoprime g d 1 = 1 := by
  rw [hcoprime, if_pos (Nat.coprime_one_left d), one_pow, h1]

/-- Restricted Euler product, as a `HasSum` (so summability is available too). -/
private theorem hasSum_moebius_mul_coprime_sq {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (h1 : g 1 = 1)
    {C : ℝ} (hC : 0 ≤ C) (hg0 : ∀ p : ℕ, p.Prime → 0 ≤ g (p ^ 2))
    (hbd : ∀ p : ℕ, p.Prime → g (p ^ 2) ≤ C / (p : ℝ) ^ 2)
    (d : ℕ) (hd : Squarefree d) :
    HasSum (fun b : ℕ => (ArithmeticFunction.moebius b : ℝ) *
        (if Nat.Coprime b d then g (b ^ 2) else 0))
      (∏' p : {p : ℕ // p.Prime ∧ p ∉ d.primeFactors}, (1 - g (p ^ 2))) := by
  have hd0 : d ≠ 0 := hd.ne_zero
  have hbd' : ∀ p : ℕ, p.Prime → |hcoprime g d p| ≤ C / (p : ℝ) ^ 2 := by
    intro p hp
    rw [hcoprime]
    by_cases hpd : p ∣ d
    · rw [if_neg (fun h => (hp.coprime_iff_not_dvd.mp h) hpd)]
      rw [abs_zero]
      exact div_nonneg hC (sq_nonneg _)
    · rw [if_pos (hp.coprime_iff_not_dvd.mpr hpd)]
      rw [abs_of_nonneg (hg0 p hp)]
      exact hbd p hp
  -- linear Euler product gives the HasSum for hcoprime
  have hbd_lin : ∀ n : ℕ, ‖hf0 (hcoprime g d) n‖ ≤ C / (n : ℝ) ^ 2 := by
    intro n
    by_cases hp : n.Prime
    · rw [hf0, if_pos hp, norm_neg, Real.norm_eq_abs]; exact hbd' n hp
    · rw [hf0, if_neg hp, norm_zero]; exact div_nonneg hC (sq_nonneg _)
  have hbase : Summable (fun n : ℕ => C / (n : ℝ) ^ 2) := by
    have h := ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : (1:ℕ) < 2)).mul_left C
    simpa [div_eq_mul_inv] using h
  have hsum_F0 : Summable (fun n : ℕ => ‖hf0 (hcoprime g d) n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hbd_lin n) hbase
  have hsum_g : Summable (hfS (hcoprime g d)) := summable_finsetProd_of_summable_norm hsum_F0
  have htprod : ∏' n : ℕ, (1 + hf0 (hcoprime g d) n) = ∑' S : Finset ℕ, hfS (hcoprime g d) S :=
    tprod_one_add hsum_g
  have hprod_sub : ∏' n : ℕ, (1 + hf0 (hcoprime g d) n)
      = ∏' p : {p : ℕ // p.Prime}, (1 - hcoprime g d p) := by
    have hsub : (∏' p : {p : ℕ // p.Prime}, (1 - hcoprime g d p))
        = ∏' n : ℕ, (Set.mulIndicator {n : ℕ | n.Prime} (fun n => 1 - hcoprime g d n)) n :=
      tprod_subtype {n : ℕ | n.Prime} (fun n => 1 - hcoprime g d n)
    rw [hsub]
    refine tprod_congr fun n => ?_
    by_cases hp : n.Prime
    · simp only [hf0, Set.mulIndicator_apply, Set.mem_ofPred_eq, hp, if_true]; ring
    · simp only [hf0, Set.mulIndicator_apply, Set.mem_ofPred_eq, hp, if_false]; ring
  have hHasSum_g : HasSum (hfS (hcoprime g d)) (∏' p : {p : ℕ // p.Prime}, (1 - hcoprime g d p)) := by
    have hh := hsum_g.hasSum
    rw [← htprod] at hh
    rw [hprod_sub] at hh
    exact hh
  have hmain : ∀ S : Finset ℕ, (∀ n ∈ S, n.Prime) →
      ((ArithmeticFunction.moebius (∏ n ∈ S, n) : ℤ) : ℝ) * hcoprime g d (∏ n ∈ S, n)
        = hfS (hcoprime g d) S :=
    fun S hS => moebius_term_eq (hcoprime_mul d hmul) (hcoprime_one d h1) hS
  have key : HasSum (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * hcoprime g d n)
        (∏' p : {p : ℕ // p.Prime}, (1 - hcoprime g d p))
      ↔ HasSum (hfS (hcoprime g d)) (∏' p : {p : ℕ // p.Prime}, (1 - hcoprime g d p)) :=
    hasSum_iff_hasSum_of_ne_zero_bij
      (a := ∏' p : {p : ℕ // p.Prime}, (1 - hcoprime g d p))
      (f := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * hcoprime g d n)
      (g := hfS (hcoprime g d))
      (i := fun x : ↑(Function.support (hfS (hcoprime g d))) => ∏ n ∈ (x : Finset ℕ), n)
      (by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
        have hxp : ∀ n ∈ x, n.Prime := prime_of_hfS_ne_zero hx
        have hyp : ∀ n ∈ y, n.Prime := prime_of_hfS_ne_zero hy
        have hxy'' : (∏ p ∈ (x : Finset ℕ), p) = (∏ p ∈ (y : Finset ℕ), p) := hxy
        have hxy' : (x : Finset ℕ) = y := by
          rw [← Nat.primeFactors_prod hxp, hxy'', Nat.primeFactors_prod hyp]
        exact Subtype.ext hxy')
      (by
        intro n hn
        rw [Function.mem_support] at hn
        have hmu_ne : ArithmeticFunction.moebius n ≠ 0 := by
          intro hzero; rw [hzero] at hn; simp at hn
        have hsq : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu_ne
        refine ⟨⟨n.primeFactors, ?_⟩, ?_⟩
        · rw [Function.mem_support,
            ← hmain n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp),
            Nat.prod_primeFactors_of_squarefree hsq]
          exact hn
        · exact Nat.prod_primeFactors_of_squarefree hsq)
      (by rintro ⟨S, hS⟩; exact hmain S (prime_of_hfS_ne_zero hS))
  have hHasSum_h : HasSum (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * hcoprime g d n)
      (∏' p : {p : ℕ // p.Prime}, (1 - hcoprime g d p)) := (key.mpr hHasSum_g)
  -- transfer to the target product
  have hpt : (∏' p : {p : ℕ // p.Prime}, (1 - hcoprime g d p))
      = ∏' p : {p : ℕ // p.Prime ∧ p ∉ d.primeFactors}, (1 - g (p ^ 2)) := by
    have hsub1 : (∏' p : {p : ℕ // p.Prime}, (1 - hcoprime g d p))
        = ∏' n : ℕ, (Set.mulIndicator {n : ℕ | n.Prime} (fun n => 1 - hcoprime g d n)) n :=
      tprod_subtype {n : ℕ | n.Prime} (fun n => 1 - hcoprime g d n)
    have hsub2 : (∏' p : {p : ℕ // p.Prime ∧ p ∉ d.primeFactors}, (1 - g (p ^ 2)))
        = ∏' n : ℕ, (Set.mulIndicator {n : ℕ | n.Prime ∧ n ∉ d.primeFactors}
            (fun n => 1 - g (n ^ 2))) n :=
      tprod_subtype {n : ℕ | n.Prime ∧ n ∉ d.primeFactors} (fun n => 1 - g (n ^ 2))
    rw [hsub1, hsub2]
    have hpt2 : Set.mulIndicator {n : ℕ | n.Prime} (fun n => 1 - hcoprime g d n)
        = Set.mulIndicator {n : ℕ | n.Prime ∧ n ∉ d.primeFactors} (fun n => 1 - g (n ^ 2)) := by
      funext n
      rw [Set.mulIndicator_apply, Set.mulIndicator_apply]
      simp only [Set.mem_ofPred_eq]
      by_cases hnp : n.Prime
      · by_cases hnd : n ∈ d.primeFactors
        · have hndvd : n ∣ d := (Nat.mem_primeFactors.mp hnd).2.1
          have hncop : ¬ Nat.Coprime n d := fun h => (hnp.coprime_iff_not_dvd.mp h) hndvd
          rw [if_pos hnp, if_neg (by simp [hnp, hnd])]
          rw [hcoprime, if_neg hncop]; ring
        · have hndvd : ¬ n ∣ d := fun h => hnd (Nat.mem_primeFactors.mpr ⟨hnp, h, hd0⟩)
          have hncop : Nat.Coprime n d := hnp.coprime_iff_not_dvd.mpr hndvd
          rw [if_pos hnp, if_pos (by simp [hnp, hnd])]
          rw [hcoprime, if_pos hncop]
      · rw [if_neg hnp, if_neg (by simp [hnp])]
    rw [hpt2]
  have hLHS : (fun b : ℕ => (ArithmeticFunction.moebius b : ℝ) *
        (if Nat.Coprime b d then g (b ^ 2) else 0))
      = fun b : ℕ => (ArithmeticFunction.moebius b : ℝ) * hcoprime g d b := by
    funext b; rw [hcoprime]
  rw [hpt] at hHasSum_h
  rw [hLHS]
  exact hHasSum_h

/-- The finite local factor. -/
private theorem sum_divisors_moebius_mul_lcm_sq_eq {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (h1 : g 1 = 1)
    (d : ℕ) (hd : Squarefree d) :
    (∑ a ∈ d.divisors, (ArithmeticFunction.moebius a : ℝ) * g (Nat.lcm (a ^ 2) d))
      = ∏ p ∈ d.primeFactors, (g p - g (p ^ 2)) := by
  classical
  have hd0 : d ≠ 0 := hd.ne_zero
  set P := d.primeFactors with hP
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hbij : (∑ a ∈ d.divisors, (ArithmeticFunction.moebius a : ℝ) * g (Nat.lcm (a ^ 2) d))
      = ∑ s ∈ P.powerset,
          (∏ p ∈ s, (-g (p ^ 2))) * ∏ p ∈ P \ s, g p := by
    refine Finset.sum_bij (fun a _ => a.primeFactors) ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_powerset]
      intro p hp
      have hpa : p ∣ a := (Nat.mem_primeFactors.mp hp).2.1
      have had : a ∣ d := (Nat.mem_divisors.mp ha).1
      have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
      exact Nat.mem_primeFactors.mpr ⟨hpp, dvd_trans hpa had, hd0⟩
    · intro a1 ha1 a2 ha2 heq
      have had1 : a1 ∣ d := (Nat.mem_divisors.mp ha1).1
      have had2 : a2 ∣ d := (Nat.mem_divisors.mp ha2).1
      have hs1 : Squarefree a1 := hd.squarefree_of_dvd had1
      have hs2 : Squarefree a2 := hd.squarefree_of_dvd had2
      rw [← Nat.prod_primeFactors_of_squarefree hs1,
        ← Nat.prod_primeFactors_of_squarefree hs2, heq]
    · intro s hs
      rw [Finset.mem_powerset] at hs
      refine ⟨∏ p ∈ s, p, ?_, ?_⟩
      · rw [Nat.mem_divisors]
        refine ⟨?_, hd0⟩
        rw [← Nat.prod_primeFactors_of_squarefree hd]
        exact Finset.prod_dvd_prod_of_subset s P (fun p => p) hs
      · rw [Nat.primeFactors_prod (fun p hp => hPprime p (hs hp))]
    · intro a ha
      have had : a ∣ d := (Nat.mem_divisors.mp ha).1
      have hsa : Squarefree a := hd.squarefree_of_dvd had
      set s := a.primeFactors with hs
      have hatP : s ⊆ P := by
        intro p hp
        rw [hs] at hp
        have hpa : p ∣ a := (Nat.mem_primeFactors.mp hp).2.1
        have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
        exact Nat.mem_primeFactors.mpr ⟨hpp, dvd_trans hpa had, hd0⟩
      have haeq : a = ∏ p ∈ s, p := by
        rw [hs]; exact (Nat.prod_primeFactors_of_squarefree hsa).symm
      have hdeq : d = ∏ p ∈ P, p := (Nat.prod_primeFactors_of_squarefree hd).symm
      have hR : (∏ p ∈ s, p ^ 2) * ∏ p ∈ P \ s, p = a * d := by
        have h2 : (∏ p ∈ s, p) * ∏ p ∈ P \ s, p = ∏ p ∈ P, p := by
          rw [mul_comm, Finset.prod_sdiff hatP]
        rw [Finset.prod_pow, haeq, hdeq, ← h2]; ring
      have hlcm : Nat.lcm (a ^ 2) d = (∏ p ∈ s, p ^ 2) * ∏ p ∈ P \ s, p := by
        rw [lcm_sq_eq_mul_of_dvd_squarefree had hd]; exact hR.symm
      have hpsi_coprime : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
          Nat.Coprime (if p ∈ s then p ^ 2 else p) (if q ∈ s then q ^ 2 else q) := by
        intro p hp q hq hpq
        have hpp : p.Prime := hPprime p hp
        have hqp : q.Prime := hPprime q hq
        have hcop : Nat.Coprime p q := (hpp.coprime_iff_not_dvd).mpr
          (fun hdvd => hpq ((hqp.dvd_iff_eq hpp.ne_one).mp hdvd).symm)
        by_cases hps : p ∈ s <;> by_cases hqs : q ∈ s <;>
          simp only [hps, hqs, if_true, if_false]
        · exact hcop.pow 2 2
        · exact hcop.pow_left 2
        · exact hcop.pow_right 2
        · exact hcop
      have hsplit : (∏ p ∈ P, (if p ∈ s then p ^ 2 else p))
          = (∏ p ∈ s, p ^ 2) * ∏ p ∈ P \ s, p := by
        rw [← Finset.prod_sdiff hatP]
        have e1 : ∏ p ∈ P \ s, (if p ∈ s then p ^ 2 else p) = ∏ p ∈ P \ s, p :=
          Finset.prod_congr rfl (fun p hp => by rw [if_neg (Finset.mem_sdiff.mp hp).2])
        have e2 : ∏ p ∈ s, (if p ∈ s then p ^ 2 else p) = ∏ p ∈ s, p ^ 2 :=
          Finset.prod_congr rfl (fun p hp => by rw [if_pos hp])
        rw [e1, e2]; ring
      have hglcm : g (Nat.lcm (a ^ 2) d) = (∏ p ∈ s, g (p ^ 2)) * ∏ p ∈ P \ s, g p := by
        rw [hlcm, ← hsplit]
        rw [g_prod_of_pairwise hmul h1 P (fun p => if p ∈ s then p ^ 2 else p) hpsi_coprime]
        have e1 : ∏ p ∈ P \ s, g (if p ∈ s then p ^ 2 else p) = ∏ p ∈ P \ s, g p :=
          Finset.prod_congr rfl (fun p hp => by rw [if_neg (Finset.mem_sdiff.mp hp).2])
        have e2 : ∏ p ∈ s, g (if p ∈ s then p ^ 2 else p) = ∏ p ∈ s, g (p ^ 2) :=
          Finset.prod_congr rfl (fun p hp => by rw [if_pos hp])
        rw [← Finset.prod_sdiff hatP, e1, e2]; ring
      have e : (∏ p ∈ s, (-1 : ℝ)) * (∏ p ∈ s, g (p ^ 2)) = ∏ p ∈ s, (-g (p ^ 2)) := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun p hp => by ring)
      rw [hglcm, moebius_eq_prod_neg_one_real hsa, ← hs, ← mul_assoc, e]
  rw [hbij]
  rw [← Finset.prod_add (fun p => -g (p ^ 2)) (fun p => g p) P]
  exact Finset.prod_congr rfl (fun p hp => by ring)

/-! ## Main theorem -/

theorem tsum_moebius_lcm_eq_not_dvd {g : ℕ → ℝ}
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (h1 : g 1 = 1)
    {C : ℝ} (hC : 0 ≤ C) (hg0 : ∀ p : ℕ, p.Prime → 0 ≤ g (p ^ 2))
    (hbd : ∀ p : ℕ, p.Prime → g (p ^ 2) ≤ C / (p : ℝ) ^ 2)
    (d : ℕ) (hd : Squarefree d) :
    (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ) * g (Nat.lcm (ν ^ 2) d))
      = (∏ p ∈ d.primeFactors, (g p - g (p ^ 2)))
        * ∏' p : {p : ℕ // p.Prime ∧ p ∉ d.primeFactors}, (1 - g (p ^ 2)) := by
  classical
  have hd0 : d ≠ 0 := hd.ne_zero
  let f : ℕ → ℝ := fun ν => (ArithmeticFunction.moebius ν : ℝ) * g (Nat.lcm (ν ^ 2) d)
  let aF : ℕ → ℝ := fun a => (ArithmeticFunction.moebius a : ℝ) * g (Nat.lcm (a ^ 2) d)
  let bF : ℕ → ℝ := fun b => (if Nat.Coprime b d then (ArithmeticFunction.moebius b : ℝ) * g (b ^ 2) else 0)
  let gF : d.divisors × ℕ → ℝ := fun p => aF (↑p.1) * bF p.2
  change (∑' ν : ℕ, f ν) = (∏ p ∈ d.primeFactors, (g p - g (p ^ 2)))
        * ∏' p : {p : ℕ // p.Prime ∧ p ∉ d.primeFactors}, (1 - g (p ^ 2))
  have hcop_of : ∀ b : ℕ, bF b ≠ 0 → Nat.Coprime b d := by
    intro b hb
    by_contra h
    exact hb (by simp only [bF, if_neg h])
  -- key multiplicative computation
  have hkey : ∀ (a b : ℕ), a ∣ d → Nat.Coprime b d → f (a * b) = aF a * bF b := by
    intro a b had hbd
    have ha0 : a ≠ 0 := by rintro rfl; exact hd0 (Nat.eq_zero_of_zero_dvd had)
    have hab : Nat.Coprime a b := Nat.Coprime.coprime_dvd_left had hbd.symm
    rcases eq_or_ne b 0 with rfl | hb0
    · simp [f, aF, bF]
    · have hb2d : Nat.Coprime (b ^ 2) d := hbd.pow_left 2
      have hmu : (ArithmeticFunction.moebius (a * b) : ℝ)
          = (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) := by
        have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab.gcd_eq_one
        rw [h]; push_cast; ring
      have hlcm : Nat.lcm ((a * b) ^ 2) d = b ^ 2 * Nat.lcm (a ^ 2) d := by
        have h2 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
        rw [h2]
        exact lcm_mul_coprime_right (pow_ne_zero 2 ha0) (pow_ne_zero 2 hb0) hd0 hb2d
      have hb2lcm : Nat.Coprime (b ^ 2) (Nat.lcm (a ^ 2) d) := by
        have hcad : Nat.Coprime (b ^ 2) (a ^ 2 * d) := (hab.pow 2 2).symm.mul_right hb2d
        refine Nat.Coprime.of_dvd dvd_rfl ?_ hcad
        exact Nat.lcm_dvd ⟨d, by ring⟩ ⟨a ^ 2, by ring⟩
      have hgl : g (Nat.lcm ((a * b) ^ 2) d) = g (b ^ 2) * g (Nat.lcm (a ^ 2) d) := by
        rw [hlcm, hmul (b ^ 2) (Nat.lcm (a ^ 2) d) hb2lcm]
      simp only [f, aF, bF]
      rw [hmu, hgl, if_pos hbd]; ring
  -- Step 1: reindex the sum over ν as a sum over pairs (a, b)
  have hstep1 : (∑' ν : ℕ, f ν) = ∑' p : d.divisors × ℕ, gF p := by
    refine tsum_eq_tsum_of_ne_zero_bij
      (i := fun x : ↑(Function.support gF) => (x.val.1 : ℕ) * x.val.2) ?_ ?_ ?_
    · rintro ⟨⟨a1, b1⟩, hx1⟩ ⟨⟨a2, b2⟩, hx2⟩ hxy
      have hxy' : (a1 : ℕ) * b1 = (a2 : ℕ) * b2 := hxy
      have h1d : (a1 : ℕ) ∣ d := (Nat.mem_divisors.mp a1.2).1
      have h2d : (a2 : ℕ) ∣ d := (Nat.mem_divisors.mp a2.2).1
      have hb1 : bF b1 ≠ 0 := by intro hb; exact hx1 (by simp only [gF, hb, mul_zero])
      have hb2 : bF b2 ≠ 0 := by intro hb; exact hx2 (by simp only [gF, hb, mul_zero])
      have hc1 : Nat.Coprime b1 d := hcop_of b1 hb1
      have hc2 : Nat.Coprime b2 d := hcop_of b2 hb2
      have hdvd1 : (a1 : ℕ) ∣ (a2 : ℕ) := by
        have hcop : Nat.Coprime (a1 : ℕ) b2 := Nat.Coprime.coprime_dvd_left h1d hc2.symm
        have hd2 : (a1 : ℕ) ∣ b2 * (a2 : ℕ) := by
          rw [mul_comm b2 (a2 : ℕ), ← hxy']; exact dvd_mul_right _ _
        exact hcop.dvd_of_dvd_mul_left hd2
      have hdvd2 : (a2 : ℕ) ∣ (a1 : ℕ) := by
        have hcop : Nat.Coprime (a2 : ℕ) b1 := Nat.Coprime.coprime_dvd_left h2d hc1.symm
        have hd1 : (a2 : ℕ) ∣ b1 * (a1 : ℕ) := by
          rw [mul_comm b1 (a1 : ℕ), hxy']; exact dvd_mul_right _ _
        exact hcop.dvd_of_dvd_mul_left hd1
      have haeq : a1 = a2 := Subtype.ext (Nat.dvd_antisymm hdvd1 hdvd2)
      have hb_eq : b1 = b2 := by
        have h2z : (a2 : ℕ) ≠ 0 := by
          rintro h
          rw [h] at h2d
          exact hd0 (Nat.eq_zero_of_zero_dvd h2d)
        rw [haeq] at hxy'
        exact Nat.mul_left_cancel (Nat.pos_of_ne_zero h2z) hxy'
      exact Subtype.ext (Prod.ext haeq hb_eq)
    · intro ν hν
      have hmuν : ArithmeticFunction.moebius ν ≠ 0 := by
        intro h0; exact hν (by simp only [f, h0, Int.cast_zero, zero_mul])
      have hsν : Squarefree ν := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuν
      let a0 : ℕ := ∏ p ∈ ν.primeFactors ∩ d.primeFactors, p
      let b0 : ℕ := ∏ p ∈ ν.primeFactors \ d.primeFactors, p
      have ha0d : a0 ∣ d := by
        have h1 : a0 ∣ ∏ p ∈ d.primeFactors, p := by
          show (∏ p ∈ ν.primeFactors ∩ d.primeFactors, p) ∣ ∏ p ∈ d.primeFactors, p
          exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.inter_subset_right
        rwa [Nat.prod_primeFactors_of_squarefree hd] at h1
      have hmem : a0 ∈ d.divisors := Nat.mem_divisors.mpr ⟨ha0d, hd0⟩
      have hb0cop : Nat.Coprime b0 d := by
        refine Nat.Coprime.prod_left (fun p hp => ?_)
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
        have hpd : ¬ p ∣ d := fun hdvd =>
          (Finset.mem_sdiff.mp hp).2 (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hd0⟩)
        exact hpp.coprime_iff_not_dvd.mpr hpd
      have ha0b0 : a0 * b0 = ν := by
        have hsd : ν.primeFactors \ (ν.primeFactors ∩ d.primeFactors) = ν.primeFactors \ d.primeFactors := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
        have hsplit : (∏ p ∈ ν.primeFactors \ d.primeFactors, p) *
            (∏ p ∈ ν.primeFactors ∩ d.primeFactors, p) = ∏ p ∈ ν.primeFactors, p := by
          rw [← hsd]
          exact Finset.prod_sdiff Finset.inter_subset_left
        show (∏ p ∈ ν.primeFactors ∩ d.primeFactors, p) *
            (∏ p ∈ ν.primeFactors \ d.primeFactors, p) = ν
        rw [mul_comm, hsplit, Nat.prod_primeFactors_of_squarefree hsν]
      have hval : gF (⟨a0, hmem⟩, b0) ≠ 0 := by
        simp only [gF]
        rw [← hkey a0 b0 ha0d hb0cop, ha0b0]
        exact hν
      exact ⟨⟨(⟨a0, hmem⟩, b0), hval⟩, ha0b0⟩
    · rintro ⟨⟨a, b⟩, hx⟩
      have ha : (a : ℕ) ∣ d := (Nat.mem_divisors.mp a.2).1
      have hb : bF b ≠ 0 := by intro hb0; exact hx (by simp only [gF, hb0, mul_zero])
      exact hkey a b ha (hcop_of b hb)
  -- Step 2: factor the pair sum into the product of the two sums
  have hB_sum_eq : (fun b : ℕ => (ArithmeticFunction.moebius b : ℝ) *
      (if Nat.Coprime b d then g (b ^ 2) else 0)) = bF := by
    funext b; by_cases h : Nat.Coprime b d <;> simp [bF, h]
  have hBsumm : Summable bF :=
    (hasSum_moebius_mul_coprime_sq hmul h1 hC hg0 hbd d hd).summable.congr
      (fun b => congrFun hB_sum_eq b)
  have hAsumm : Summable (fun a : d.divisors => aF (↑a)) := Summable.of_finite
  have hABsumm : Summable (fun p : d.divisors × ℕ => aF (↑p.1) * bF p.2) := by
    have hgsumm : Summable (fun p : d.divisors × ℕ => (∑ a : d.divisors, ‖aF (↑a)‖) * ‖bF p.2‖) := by
      have h1' : Summable (fun p : (Σ _ : d.divisors, ℕ) =>
          (∑ a : d.divisors, ‖aF (↑a)‖) * ‖bF p.2‖) := by
        rw [summable_sigma_of_nonneg
          (f := fun p : (Σ _ : d.divisors, ℕ) =>
            (∑ a : d.divisors, ‖aF (↑a)‖) * ‖bF p.2‖)
          (fun p => mul_nonneg (Finset.sum_nonneg (fun a _ => norm_nonneg _)) (norm_nonneg _))]
        have hfiber : Summable (fun b : ℕ => (∑ a : d.divisors, ‖aF (↑a)‖) * ‖bF b‖) :=
          ((hBsumm.norm : Summable (fun b : ℕ => ‖bF b‖)).mul_left
            (∑ a : d.divisors, ‖aF (↑a)‖))
        exact ⟨fun a => hfiber, Summable.of_finite⟩
      exact (Equiv.summable_iff (Equiv.sigmaEquivProd d.divisors ℕ)
        (f := fun p : d.divisors × ℕ =>
          (∑ a : d.divisors, ‖aF (↑a)‖) * ‖bF p.2‖)).mp h1'
    refine Summable.of_norm_bounded
      (f := fun p : d.divisors × ℕ => aF (↑p.1) * bF p.2)
      (g := fun p : d.divisors × ℕ => (∑ a : d.divisors, ‖aF (↑a)‖) * ‖bF p.2‖) hgsumm ?_
    intro p
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [← Real.norm_eq_abs]
    exact Finset.single_le_sum (s := Finset.univ) (f := fun a : d.divisors => ‖aF (↑a)‖)
      (fun a _ => norm_nonneg (aF (↑a))) (Finset.mem_univ (p.1))
  have hstep2 : (∑' p : d.divisors × ℕ, gF p)
      = (∑' a : d.divisors, aF (↑a)) * (∑' b : ℕ, bF b) := by
    have h := Summable.tsum_mul_tsum hAsumm hBsumm hABsumm
    exact h.symm
  -- Step 3: the finite divisor sum
  have hstep3 : (∑' a : d.divisors, aF (↑a)) = ∏ p ∈ d.primeFactors, (g p - g (p ^ 2)) := by
    rw [tsum_fintype]
    have hattach : (∑ a : d.divisors, aF (↑a)) = ∑ a ∈ d.divisors, aF a := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach d.divisors aF
    rw [hattach]
    exact sum_divisors_moebius_mul_lcm_sq_eq hmul h1 d hd
  -- Step 4: the restricted Euler product
  have hstep4 : (∑' b : ℕ, bF b)
      = ∏' p : {p : ℕ // p.Prime ∧ p ∉ d.primeFactors}, (1 - g (p ^ 2)) := by
    have h := hasSum_moebius_mul_coprime_sq hmul h1 hC hg0 hbd d hd
    rw [hB_sum_eq] at h
    exact h.tsum_eq
  calc (∑' ν : ℕ, f ν) = ∑' p : d.divisors × ℕ, gF p := hstep1
    _ = (∑' a : d.divisors, aF (↑a)) * (∑' b : ℕ, bF b) := hstep2
    _ = (∏ p ∈ d.primeFactors, (g p - g (p ^ 2)))
          * ∏' p : {p : ℕ // p.Prime ∧ p ∉ d.primeFactors}, (1 - g (p ^ 2)) := by
        rw [hstep3, hstep4]

end Commons.NumberTheory.EulerProduct