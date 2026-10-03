import Mathlib
import Submission.Commons.NumberTheory.Nat.prod_pm1_pm2_eq_divisor_sum
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_divisors_prod_primes
import Submission.Commons.NumberTheory.Sieve.rankin_trick
import Submission.Commons.NumberTheory.Mertens.mertens_range_gap_bound
import Submission.Commons.NumberTheory.Sieve.sifted_sum_comparison
import Submission.Commons.NumberTheory.Sieve.exists_good_Z_sieve
import Submission.Commons.NumberTheory.Sieve.moebius_rough_recip_large_z

set_option maxHeartbeats 8000000

namespace Commons.NumberTheory.Sieve

open Finset
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

/-! ## The smooth/rough partition of an integer

For a threshold `Z : ℕ`, every squarefree `d` factors uniquely as
`d = smoothPart Z d * roughPart Z d` where the first factor collects the prime
factors `< Z` and the second the prime factors `≥ Z`. -/

/-- Product of the prime factors of `d` that are `< Z`. -/
def smoothPart (Z d : ℕ) : ℕ := ∏ p ∈ d.primeFactors.filter (fun p => p < Z), p

/-- Product of the prime factors of `d` that are `≥ Z`. -/
def roughPart (Z d : ℕ) : ℕ := ∏ p ∈ d.primeFactors.filter (fun p => Z ≤ p), p

/-- The primorial of the primes below `Z`. -/
def primeZProd (Z : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow Z, p

lemma smoothPart_pos (Z d : ℕ) : 0 < smoothPart Z d := by
  unfold smoothPart
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

lemma roughPart_pos (Z d : ℕ) : 0 < roughPart Z d := by
  unfold roughPart
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos)

lemma squarefree_smoothPart (Z d : ℕ) : Squarefree (smoothPart Z d) := by
  unfold smoothPart
  exact Commons.NumberTheory.Nat.squarefree_prod_of_prime
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)

lemma squarefree_roughPart (Z d : ℕ) : Squarefree (roughPart Z d) := by
  unfold roughPart
  exact Commons.NumberTheory.Nat.squarefree_prod_of_prime
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)

lemma primeZProd_pos (Z : ℕ) : 0 < primeZProd Z := by
  unfold primeZProd
  exact Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primesBelow hp).pos)

lemma primeZProd_ne_zero (Z : ℕ) : primeZProd Z ≠ 0 := ne_of_gt (primeZProd_pos Z)

lemma squarefree_primeZProd (Z : ℕ) : Squarefree (primeZProd Z) := by
  unfold primeZProd
  exact Commons.NumberTheory.Nat.squarefree_prod_of_prime (fun p hp => Nat.prime_of_mem_primesBelow hp)

lemma roughPart_eq_filter_not {Z d : ℕ} :
    roughPart Z d = ∏ p ∈ d.primeFactors.filter (fun p => ¬ p < Z), p := by
  unfold roughPart
  congr 1
  ext p
  simp only [Finset.mem_filter, not_lt]

lemma smoothPart_mul_roughPart {Z d : ℕ} (hsq : Squarefree d) :
    smoothPart Z d * roughPart Z d = d := by
  unfold smoothPart
  rw [roughPart_eq_filter_not,
    Finset.prod_filter_mul_prod_filter_not d.primeFactors (fun p => p < Z) (fun p => p)]
  exact Nat.prod_primeFactors_of_squarefree hsq

lemma smoothPart_dvd {Z d : ℕ} (hsq : Squarefree d) : smoothPart Z d ∣ d :=
  ⟨roughPart Z d, (smoothPart_mul_roughPart hsq).symm⟩

lemma roughPart_dvd {Z d : ℕ} (hsq : Squarefree d) : roughPart Z d ∣ d :=
  ⟨smoothPart Z d, by rw [mul_comm]; exact (smoothPart_mul_roughPart hsq).symm⟩

lemma primeFactors_smoothPart {Z d : ℕ} :
    (smoothPart Z d).primeFactors = d.primeFactors.filter (fun p => p < Z) := by
  unfold smoothPart
  rw [Nat.primeFactors_prod]
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma primeFactors_roughPart {Z d : ℕ} :
    (roughPart Z d).primeFactors = d.primeFactors.filter (fun p => Z ≤ p) := by
  unfold roughPart
  rw [Nat.primeFactors_prod]
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma smoothPart_dvd_primorial (Z d : ℕ) : smoothPart Z d ∣ primeZProd Z := by
  unfold smoothPart primeZProd
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [Finset.mem_filter] at hp
  exact Nat.mem_primesBelow.mpr ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩

lemma primeFactors_primeZProd (Z : ℕ) : (primeZProd Z).primeFactors = Nat.primesBelow Z := by
  unfold primeZProd
  rw [Nat.primeFactors_prod]
  intro p hp
  exact Nat.prime_of_mem_primesBelow hp

lemma primeFactors_subset_primesBelow_of_dvd {Z m : ℕ} (hm : m ∣ primeZProd Z) :
    m.primeFactors ⊆ Nat.primesBelow Z := by
  rw [← primeFactors_primeZProd Z]
  exact Nat.primeFactors_mono hm (primeZProd_ne_zero Z)

lemma le_of_mem_primeFactors_of_coprime_primorial {Z n : ℕ}
    (hn : n.Coprime (primeZProd Z)) {p : ℕ} (hp : p ∈ n.primeFactors) : Z ≤ p := by
  by_contra h
  rw [not_le] at h
  have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hpPS : p ∣ primeZProd Z := by
    apply Nat.dvd_of_mem_primeFactors
    rw [primeFactors_primeZProd]
    exact Nat.mem_primesBelow.mpr ⟨h, hpp⟩
  have hg : p ∣ Nat.gcd n (primeZProd Z) := Nat.dvd_gcd hpn hpPS
  rw [hn] at hg
  exact hpp.not_dvd_one hg

lemma coprime_roughPart_primeZProd (Z d : ℕ) :
    (roughPart Z d).Coprime (primeZProd Z) := by
  unfold primeZProd
  rw [Nat.coprime_prod_right_iff]
  intro q hq
  unfold roughPart
  rw [Nat.coprime_prod_left_iff]
  intro r hr
  rw [Finset.mem_filter] at hr
  have hrp : Nat.Prime r := Nat.prime_of_mem_primeFactors hr.1
  have hqp : Nat.Prime q := Nat.prime_of_mem_primesBelow hq
  have hqz : q < Z := (Nat.mem_primesBelow.mp hq).1
  have hne : r ≠ q := by omega
  exact (Nat.coprime_primes hrp hqp).mpr hne

lemma coprime_smoothPart_roughPart (Z d : ℕ) :
    (smoothPart Z d).Coprime (roughPart Z d) := by
  exact (coprime_roughPart_primeZProd Z d).coprime_dvd_right (smoothPart_dvd_primorial Z d) |>.symm

lemma smoothPart_mul_of_dvd {Z m n : ℕ} (hm : Squarefree m) (hmPS : m ∣ primeZProd Z)
    (hn : 1 ≤ n) (hnPS : n.Coprime (primeZProd Z)) : smoothPart Z (m * n) = m := by
  have hm0 : m ≠ 0 := fun h => primeZProd_ne_zero Z (zero_dvd_iff.mp (h ▸ hmPS))
  have hn0 : n ≠ 0 := by omega
  have hpf : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors := Nat.primeFactors_mul hm0 hn0
  have hfilt : (m * n).primeFactors.filter (fun p => p < Z) = m.primeFactors := by
    rw [hpf, Finset.filter_union]
    have h1 : m.primeFactors.filter (fun p => p < Z) = m.primeFactors :=
      Finset.filter_true_of_mem (fun p hp => (Nat.mem_primesBelow.mp (primeFactors_subset_primesBelow_of_dvd hmPS hp)).1)
    have h2 : n.primeFactors.filter (fun p => p < Z) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      rw [Finset.mem_filter] at hp
      have := le_of_mem_primeFactors_of_coprime_primorial hnPS hp.1
      omega
    rw [h1, h2, Finset.union_empty]
  unfold smoothPart
  rw [hfilt]
  exact Nat.prod_primeFactors_of_squarefree hm

lemma roughPart_mul_of_dvd {Z m n : ℕ} (hn : Squarefree n) (hmPS : m ∣ primeZProd Z)
    (hn' : 1 ≤ n) (hnPS : n.Coprime (primeZProd Z)) : roughPart Z (m * n) = n := by
  have hm0 : m ≠ 0 := fun h => primeZProd_ne_zero Z (zero_dvd_iff.mp (h ▸ hmPS))
  have hn0 : n ≠ 0 := by omega
  have hpf : (m * n).primeFactors = m.primeFactors ∪ n.primeFactors := Nat.primeFactors_mul hm0 hn0
  have hfilt : (m * n).primeFactors.filter (fun p => Z ≤ p) = n.primeFactors := by
    rw [hpf, Finset.filter_union]
    have h1 : m.primeFactors.filter (fun p => Z ≤ p) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      rw [Finset.mem_filter] at hp
      have hpZ := (Nat.mem_primesBelow.mp (primeFactors_subset_primesBelow_of_dvd hmPS hp.1)).1
      omega
    have h2 : n.primeFactors.filter (fun p => Z ≤ p) = n.primeFactors :=
      Finset.filter_true_of_mem (fun p hp => le_of_mem_primeFactors_of_coprime_primorial hnPS hp)
    rw [h1, h2, Finset.empty_union]
  unfold roughPart
  rw [hfilt]
  exact Nat.prod_primeFactors_of_squarefree hn

/-- The Dirichlet hyperbola / smooth-rough decomposition of the Möbius sum. -/
lemma moebius_sum_hyperbola (Z ϱ y : ℕ) (g : ℕ → ℝ)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) :
    (∑ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ Nat.Coprime d ϱ),
        (ArithmeticFunction.moebius d : ℝ) * g d)
    = ∑ m ∈ (Nat.divisors (primeZProd Z)).filter (fun m => Nat.Coprime m ϱ),
        (ArithmeticFunction.moebius m : ℝ) * g m *
        (∑ n ∈ (Finset.Icc 1 (y / m)).filter
            (fun n => Squarefree n ∧ Nat.Coprime n (primeZProd Z * ϱ)),
          (ArithmeticFunction.moebius n : ℝ) * g n) := by
  classical
  let Sh : Finset ℕ := (Nat.divisors (primeZProd Z)).filter (fun m => Nat.Coprime m ϱ)
  let Th : ℕ → Finset ℕ :=
    fun m => (Finset.Icc 1 (y / m)).filter
      (fun n => Squarefree n ∧ Nat.Coprime n (primeZProd Z * ϱ))
  let gg : (Σ _ : ℕ, ℕ) → ℝ :=
    fun x => ((ArithmeticFunction.moebius x.1 : ℝ) * g x.1) *
          ((ArithmeticFunction.moebius x.2 : ℝ) * g x.2)
  have step1 : (∑ x ∈ Sh.sigma Th, gg x) = ∑ m ∈ Sh, ∑ n ∈ Th m, gg ⟨m, n⟩ :=
    (Finset.sum_sigma' Sh Th (fun m n => gg ⟨m, n⟩)).symm
  have key := Finset.sum_nbij'
    (s := (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ Nat.Coprime d ϱ))
    (t := Sh.sigma Th)
    (f := fun d => (ArithmeticFunction.moebius d : ℝ) * g d)
    (g := gg)
    (i := fun d => (⟨smoothPart Z d, roughPart Z d⟩ : Σ _ : ℕ, ℕ))
    (j := fun x => x.1 * x.2)
    (by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, hdy⟩, hdsq, hdcop⟩ := hd
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · dsimp only [Sh]
        rw [Finset.mem_filter, Nat.mem_divisors]
        exact ⟨⟨smoothPart_dvd_primorial Z d, primeZProd_ne_zero Z⟩,
          hdcop.of_dvd_left (smoothPart_dvd hdsq)⟩
      · dsimp only [Th]
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨roughPart_pos Z d, ?_⟩, squarefree_roughPart Z d, ?_⟩
        · rw [Nat.le_div_iff_mul_le (smoothPart_pos Z d), mul_comm, smoothPart_mul_roughPart hdsq]
          exact hdy
        · rw [Nat.coprime_mul_iff_right]
          exact ⟨coprime_roughPart_primeZProd Z d, hdcop.of_dvd_left (roughPart_dvd hdsq)⟩)
    (by
      rintro ⟨m, n⟩ hx
      have hxm : m ∈ Sh := (Finset.mem_sigma.mp hx).1
      have hxn : n ∈ Th m := (Finset.mem_sigma.mp hx).2
      dsimp only [Sh] at hxm
      rw [Finset.mem_filter, Nat.mem_divisors] at hxm
      obtain ⟨⟨hmdvd, _⟩, hmcop⟩ := hxm
      dsimp only [Th] at hxn
      rw [Finset.mem_filter, Finset.mem_Icc] at hxn
      obtain ⟨⟨hn1, hny⟩, hnsq, hncop⟩ := hxn
      have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hmdvd (primeZProd_pos Z)
      have hncopPS : n.Coprime (primeZProd Z) := (Nat.coprime_mul_iff_right.mp hncop).1
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_, ?_⟩
      · exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.mul_pos hmpos (lt_of_lt_of_le Nat.zero_lt_one hn1)))
      · have := (Nat.le_div_iff_mul_le hmpos).mp hny
        rwa [mul_comm] at this
      · have hmncop : m.Coprime n := hncopPS.symm.of_dvd_left hmdvd
        exact (Nat.squarefree_mul hmncop).mpr
          ⟨Squarefree.squarefree_of_dvd hmdvd (squarefree_primeZProd Z), hnsq⟩
      · exact hmcop.mul_left ((Nat.coprime_mul_iff_right.mp hncop).2))
    (by
      intro d hd
      rw [Finset.mem_filter] at hd
      exact smoothPart_mul_roughPart hd.2.1)
    (by
      rintro ⟨m, n⟩ hx
      have hxm : m ∈ Sh := (Finset.mem_sigma.mp hx).1
      have hxn : n ∈ Th m := (Finset.mem_sigma.mp hx).2
      dsimp only [Sh] at hxm
      rw [Finset.mem_filter, Nat.mem_divisors] at hxm
      obtain ⟨⟨hmdvd, _⟩, hmcop⟩ := hxm
      dsimp only [Th] at hxn
      rw [Finset.mem_filter, Finset.mem_Icc] at hxn
      obtain ⟨⟨hn1, hny⟩, hnsq, hncop⟩ := hxn
      have hncopPS : n.Coprime (primeZProd Z) := (Nat.coprime_mul_iff_right.mp hncop).1
      rw [smoothPart_mul_of_dvd (Squarefree.squarefree_of_dvd hmdvd (squarefree_primeZProd Z)) hmdvd hn1 hncopPS,
        roughPart_mul_of_dvd hnsq hmdvd hn1 hncopPS])
    (by
      intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨_, hdsq, _⟩ := hd
      have hcop := coprime_smoothPart_roughPart Z d
      have hmu : ArithmeticFunction.moebius (smoothPart Z d * roughPart Z d)
          = ArithmeticFunction.moebius (smoothPart Z d) * ArithmeticFunction.moebius (roughPart Z d) :=
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
      have hg : g (smoothPart Z d * roughPart Z d) = g (smoothPart Z d) * g (roughPart Z d) :=
        hgmul _ _ hcop
      have hd_eq : d = smoothPart Z d * roughPart Z d := (smoothPart_mul_roughPart hdsq).symm
      dsimp only [gg]
      conv_lhs => rw [hd_eq]
      rw [hmu, hg]
      push_cast
      ring)
  have step2 : ∑ m ∈ Sh, ∑ n ∈ Th m, gg ⟨m, n⟩
      = ∑ m ∈ (Nat.divisors (primeZProd Z)).filter (fun m => Nat.Coprime m ϱ),
        (ArithmeticFunction.moebius m : ℝ) * g m *
        (∑ n ∈ (Finset.Icc 1 (y / m)).filter
            (fun n => Squarefree n ∧ Nat.Coprime n (primeZProd Z * ϱ)),
          (ArithmeticFunction.moebius n : ℝ) * g n) := by
    simp only [Sh, Th, gg, Finset.mul_sum]
  exact key.trans (step1.trans step2)


/-! ## Euler-product bounds for the smooth parts -/

/-- `∑_{m | Z-primorial, (m,ϱ)=1} g m ≤ ∏_{p < Z} (1 + g p)`. -/
lemma smooth_g_sum_le (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1) (Z ϱ : ℕ) :
    (∑ m ∈ (Nat.divisors (primeZProd Z)).filter (fun m => Nat.Coprime m ϱ), g m)
      ≤ ∏ p ∈ Nat.primesBelow Z, (1 + g p) := by
  rw [← Commons.NumberTheory.ArithmeticFunction.sum_divisors_prod_primes g hgmul hg1 Z]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun x _ _ => hg0 x)

/-- `∏_{p < Z} (1 + g p) ≤ C (1 + log Z)`, using the prime-sum hypothesis. -/
lemma prod_one_add_g_le (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (c Cs : ℝ)
    (hg_sum : ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (⌊y⌋₊).primesLE, g p) - (Real.log (Real.log y) + c)| ≤ Cs * (Real.log y) ^ (-10 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℕ, 2 ≤ Z →
      ∏ p ∈ Nat.primesBelow Z, (1 + g p) ≤ C * (1 + Real.log Z) := by
  have hBpos : 0 < (Real.log 2) ^ (-10 : ℝ) := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
  have hCsnn : 0 ≤ Cs := by
    have h := hg_sum 2 (by norm_num)
    have h2 : (0 : ℝ) ≤ Cs * (Real.log 2) ^ (-10 : ℝ) := le_trans (abs_nonneg _) h
    exact (mul_nonneg_iff_of_pos_right hBpos).mp h2
  refine ⟨max (Real.exp (c + Cs * (Real.log 2) ^ (-10 : ℝ))) 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro Z hZ
  have hZ2 : (2 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ
  have hZ1 : (1 : ℝ) < Z := by linarith
  have hlogZpos : 0 < Real.log (Z : ℝ) := Real.log_pos hZ1
  have hsum_le : (∑ p ∈ Nat.primesBelow Z, g p)
      ≤ Real.log (Real.log (Z : ℝ)) + c + Cs * (Real.log (Z : ℝ)) ^ (-10 : ℝ) := by
    have h := hg_sum (Z : ℝ) hZ2
    have h2 := le_trans (le_abs_self _) h
    have hfloor : (⌊(Z : ℝ)⌋₊) = Z := Nat.floor_natCast Z
    rw [hfloor] at h2
    have hle : (∑ p ∈ Nat.primesBelow Z, g p) ≤ ∑ p ∈ Z.primesLE, g p :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by intro p hp
            exact Nat.mem_primesLE.mpr
              ⟨le_of_lt (Nat.mem_primesBelow.mp hp).1, Nat.prime_of_mem_primesBelow hp⟩)
        (fun x _ _ => hg0 x)
    linarith
  have hpow : (Real.log (Z : ℝ)) ^ (-10 : ℝ) ≤ (Real.log 2) ^ (-10 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hZ2) (by norm_num)
  have hCs : Cs * (Real.log (Z : ℝ)) ^ (-10 : ℝ) ≤ Cs * (Real.log 2) ^ (-10 : ℝ) :=
    mul_le_mul_of_nonneg_left hpow hCsnn
  calc ∏ p ∈ Nat.primesBelow Z, (1 + g p)
      ≤ ∏ p ∈ Nat.primesBelow Z, Real.exp (g p) := by
        apply Finset.prod_le_prod₀
        · intro p _; linarith [hg0 p]
        · intro p _; linarith [Real.add_one_le_exp (g p)]
    _ = Real.exp (∑ p ∈ Nat.primesBelow Z, g p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (Real.log (Real.log (Z : ℝ)) + c + Cs * (Real.log (Z : ℝ)) ^ (-10 : ℝ)) :=
        Real.exp_le_exp.mpr hsum_le
    _ = Real.log (Z : ℝ) * Real.exp (c + Cs * (Real.log (Z : ℝ)) ^ (-10 : ℝ)) := by
        rw [show Real.log (Real.log (Z : ℝ)) + c + Cs * (Real.log (Z : ℝ)) ^ (-10 : ℝ)
              = Real.log (Real.log (Z : ℝ)) + (c + Cs * (Real.log (Z : ℝ)) ^ (-10 : ℝ)) by ring,
            Real.exp_add, Real.exp_log hlogZpos]
    _ ≤ Real.log (Z : ℝ) * Real.exp (c + Cs * (Real.log 2) ^ (-10 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hlogZpos.le
        apply Real.exp_le_exp.mpr
        linarith [hCs]
    _ ≤ Real.log (Z : ℝ) * max (Real.exp (c + Cs * (Real.log 2) ^ (-10 : ℝ))) 1 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hlogZpos.le
    _ ≤ (1 + Real.log (Z : ℝ)) * max (Real.exp (c + Cs * (Real.log 2) ^ (-10 : ℝ))) 1 := by
        apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one (le_max_right _ _))
        linarith
    _ = max (Real.exp (c + Cs * (Real.log 2) ^ (-10 : ℝ))) 1 * (1 + Real.log Z) := by ring


/-- `g m = ∏_{p | m} g p` for squarefree `m` (from weak multiplicativity). -/
lemma g_eq_prod_primeFactors (g : ℕ → ℝ)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1) :
    ∀ n, Squarefree n → g n = ∏ p ∈ n.primeFactors, g p := by
  have key : ∀ s : Finset ℕ, (∀ p ∈ s, Nat.Prime p) → g (∏ p ∈ s, p) = ∏ p ∈ s, g p := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _; simp [hg1]
    · intro a t hat ih hprime
      rw [Finset.prod_insert hat, Finset.prod_insert hat]
      have ha : Nat.Prime a := hprime a (Finset.mem_insert_self a t)
      have ht : ∀ p ∈ t, Nat.Prime p := fun p hp => hprime p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ t, p) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        have hqprime : Nat.Prime q := ht q hq
        have hne : a ≠ q := fun h => hat (h ▸ hq)
        exact (Nat.coprime_primes ha hqprime).mpr hne
      rw [hgmul a (∏ p ∈ t, p) hcop, ih ht]
  intro n hsq
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  conv_lhs => rw [← hprod]
  exact key n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)


/-- Rankin's trick bound for the "large smooth part" `H`. -/
lemma rankin_H_bound (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1)
    (c Cs : ℝ)
    (hg_sum : ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (⌊y⌋₊).primesLE, g p) - (Real.log (Real.log y) + c)| ≤ Cs * (Real.log y) ^ (-10 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z y : ℕ, 3 ≤ Z → 16 ≤ y →
      (∑ m ∈ (Nat.divisors (primeZProd Z)).filter (fun m => Nat.sqrt y < m ∧ m ≤ y), g m)
        ≤ C * Real.exp (-(Real.log y / (4 * Real.log Z))) * (Real.log Z) ^ 8 := by
  have hBpos : 0 < (Real.log 2) ^ (-10 : ℝ) := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
  have hCsnn : 0 ≤ Cs := by
    have h := hg_sum 2 (by norm_num)
    have h2 : (0 : ℝ) ≤ Cs * (Real.log 2) ^ (-10 : ℝ) := le_trans (abs_nonneg _) h
    exact (mul_nonneg_iff_of_pos_right hBpos).mp h2
  refine ⟨max 1 (Real.exp (3 * (c + Cs))), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro Z y hZ hy16
  have hZ3 : (3 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ
  have hy16' : (16 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy16
  have hZ2 : (2 : ℝ) ≤ (Z : ℝ) := by linarith
  have hlogZpos : 0 < Real.log (Z : ℝ) := Real.log_pos (by linarith)
  have hlogZ1 : 1 ≤ Real.log (Z : ℝ) := by
    have h3 : (1 : ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num)).mpr (le_of_lt Real.exp_one_lt_three)
    calc (1 : ℝ) ≤ Real.log 3 := h3
      _ ≤ Real.log Z := Real.log_le_log (by norm_num) hZ3
  -- the Rankin set contains the divisor filter
  have hsub : (Nat.divisors (primeZProd Z)).filter (fun m => Nat.sqrt y < m ∧ m ≤ y)
      ⊆ (Finset.range (y + 1)).filter
          (fun n => n ∈ Nat.smoothNumbers Z ∧ Squarefree n ∧ Nat.sqrt y < n) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    obtain ⟨hmdvd, hlt, hle⟩ := hm
    obtain ⟨hmPS, _⟩ := Nat.mem_divisors.mp hmdvd
    refine ⟨Finset.mem_range.mpr (by omega), ?_, ?_, hlt⟩
    · exact Nat.mem_smoothNumbers'.mpr (fun p hp hpm => by
        have hpPS : p ∣ primeZProd Z := dvd_trans hpm hmPS
        have hpPF : p ∈ (primeZProd Z).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp, hpPS, primeZProd_ne_zero Z⟩
        rw [primeFactors_primeZProd] at hpPF
        exact (Nat.mem_primesBelow.mp hpPF).1)
    · exact Squarefree.squarefree_of_dvd hmPS (squarefree_primeZProd Z)
  have hle_sum : (∑ m ∈ (Nat.divisors (primeZProd Z)).filter (fun m => Nat.sqrt y < m ∧ m ≤ y), g m)
      ≤ ∑ n ∈ (Finset.range (y + 1)).filter
          (fun n => n ∈ Nat.smoothNumbers Z ∧ Squarefree n ∧ Nat.sqrt y < n), g n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hg0 x)
  have hrank := Commons.NumberTheory.Sieve.rankin_trick (f := g) hg0
    (g_eq_prod_primeFactors g hgmul hg1) (z := Z) (y := Nat.sqrt y) (N := y)
    (by rw [Nat.le_sqrt']; omega) (show (0:ℝ) < 1 / Real.log (Z:ℝ) by positivity)
  refine le_trans hle_sum (le_trans hrank ?_)
  -- first factor: (Nat.sqrt y)^{-1/log Z} ≤ exp(-log y/(4 log Z))
  have hsqrt_lt : Real.sqrt (y : ℝ) - 1 ≤ (Nat.sqrt y : ℝ) := by
    have h : Real.sqrt (y:ℝ) < (Nat.sqrt y : ℝ) + 1 := by
      rw [Real.sqrt_lt' (by positivity : (0:ℝ) < (Nat.sqrt y : ℝ) + 1)]
      have hnat : y < (Nat.sqrt y).succ * (Nat.sqrt y).succ := Nat.lt_succ_sqrt y
      have hcast : (((Nat.sqrt y).succ * (Nat.sqrt y).succ : ℕ) : ℝ) = ((Nat.sqrt y : ℝ) + 1)^2 := by
        push_cast [Nat.succ_eq_add_one]; ring
      rw [← hcast]
      exact_mod_cast hnat
    linarith
  have hlogSqrt : (1:ℝ)/4 * Real.log y ≤ Real.log (Nat.sqrt y : ℝ) := by
    have hpos : 0 < Real.sqrt (y:ℝ) - 1 := by
      have : (4:ℝ) ≤ Real.sqrt y := by rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
      linarith
    have hhalf : Real.sqrt (y:ℝ)/2 ≤ Real.sqrt (y:ℝ) - 1 := by
      have : (2:ℝ) ≤ Real.sqrt y := by rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
      linarith
    have h1 : Real.log (Real.sqrt (y:ℝ)/2) ≤ Real.log (Nat.sqrt y : ℝ) := by
      apply Real.log_le_log (by positivity)
      linarith [hsqrt_lt, hhalf]
    have h2 : Real.log (Real.sqrt (y:ℝ)/2) = (1:ℝ)/2 * Real.log y - Real.log 2 := by
      rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by positivity)]
      ring
    have h3 : Real.log 2 ≤ (1:ℝ)/4 * Real.log y := by
      have := Real.log_le_log (by norm_num : (0:ℝ) < 16) hy16'
      rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow] at this
      push_cast at this; linarith
    rw [h2] at h1; linarith
  have hexp1 : (Nat.sqrt y : ℝ) ^ (-(1 / Real.log (Z:ℝ)))
      ≤ Real.exp (-(Real.log y / (4 * Real.log Z))) := by
    have hkey : Real.log y / (4 * Real.log Z) ≤ Real.log (Nat.sqrt y : ℝ) / Real.log Z := by
      have h4 : Real.log y / 4 ≤ Real.log (Nat.sqrt y : ℝ) := by linarith [hlogSqrt]
      have heq : Real.log y / (4 * Real.log Z) = (Real.log y / 4) / Real.log Z :=
        (div_div _ _ _).symm
      rw [heq]
      exact div_le_div_of_nonneg_right h4 hlogZpos.le
    rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < Nat.sqrt y)]
    apply Real.exp_le_exp.mpr
    rw [show Real.log (Nat.sqrt y : ℝ) * (-(1 / Real.log Z)) = -(Real.log (Nat.sqrt y : ℝ) / Real.log Z) by ring,
      neg_le_neg_iff]
    exact hkey
  -- second factor
  have hprod1 : ∏ p ∈ Nat.primesBelow Z, (1 + (p : ℝ) ^ (1 / Real.log (Z:ℝ)) * g p)
      ≤ max 1 (Real.exp (3 * (c + Cs))) * (Real.log Z) ^ 8 := by
    have hterm : ∀ p ∈ Nat.primesBelow Z,
        (1 + (p : ℝ) ^ (1 / Real.log (Z:ℝ)) * g p) ≤ Real.exp (3 * g p) := by
      intro p hp
      have hpZ : (p:ℝ) < Z := by exact_mod_cast (Nat.mem_primesBelow.mp hp).1
      have hppos : 0 < (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).pos
      have hpr : (p:ℝ) ^ (1 / Real.log (Z:ℝ)) ≤ 3 := by
        rw [Real.rpow_def_of_pos hppos]
        have hle : Real.log (p:ℝ) * (1 / Real.log Z) ≤ 1 := by
          rw [mul_one_div, div_le_iff₀ hlogZpos]; linarith [Real.log_lt_log hppos hpZ]
        calc Real.exp (Real.log (p:ℝ) * (1 / Real.log Z)) ≤ Real.exp 1 := Real.exp_le_exp.mpr hle
          _ ≤ 3 := le_of_lt Real.exp_one_lt_three
      have hstep : (p:ℝ) ^ (1 / Real.log (Z:ℝ)) * g p ≤ 3 * g p :=
        mul_le_mul_of_nonneg_right hpr (hg0 p)
      calc 1 + (p:ℝ) ^ (1 / Real.log (Z:ℝ)) * g p ≤ 1 + 3 * g p := by linarith
        _ ≤ Real.exp (3 * g p) := by linarith [Real.add_one_le_exp (3 * g p)]
    have hsum := hg_sum (Z:ℝ) hZ2
    have h2 := le_trans (le_abs_self _) hsum
    have hfloor : (⌊(Z:ℝ)⌋₊) = Z := Nat.floor_natCast Z
    rw [hfloor] at h2
    have hle : (∑ p ∈ Nat.primesBelow Z, g p) ≤ ∑ p ∈ Z.primesLE, g p :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by intro p hp; exact Nat.mem_primesLE.mpr ⟨le_of_lt (Nat.mem_primesBelow.mp hp).1, Nat.prime_of_mem_primesBelow hp⟩)
        (fun x _ _ => hg0 x)
    have hpow1 : (Real.log (Z:ℝ)) ^ (-10 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hlogZ1 (by norm_num)
    have hsum_le : (∑ p ∈ Nat.primesBelow Z, g p) ≤ Real.log (Real.log Z) + c + Cs := by nlinarith [h2, hle, hCsnn, hpow1]
    calc ∏ p ∈ Nat.primesBelow Z, (1 + (p : ℝ) ^ (1 / Real.log (Z:ℝ)) * g p)
        ≤ ∏ p ∈ Nat.primesBelow Z, Real.exp (3 * g p) :=
          Finset.prod_le_prod₀
            (fun p hp => add_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (hg0 p)))
            hterm
      _ = Real.exp (∑ p ∈ Nat.primesBelow Z, 3 * g p) := (Real.exp_sum _ _).symm
      _ = Real.exp (3 * ∑ p ∈ Nat.primesBelow Z, g p) := by congr 1; rw [Finset.mul_sum]
      _ ≤ Real.exp (3 * (Real.log (Real.log Z) + c + Cs)) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = Real.exp (3 * (c + Cs)) * (Real.log Z) ^ 3 := by
          have h2 : Real.exp (3 * Real.log (Real.log (Z:ℝ))) = (Real.log (Z:ℝ)) ^ 3 := by
            rw [show (3:ℝ) * Real.log (Real.log (Z:ℝ)) = Real.log ((Real.log (Z:ℝ))^3) by
              rw [Real.log_pow]; ring,
              Real.exp_log (pow_pos (by linarith [hlogZ1] : (0:ℝ) < Real.log Z) 3)]
          rw [show 3 * (Real.log (Real.log (Z:ℝ)) + c + Cs)
                = 3 * Real.log (Real.log (Z:ℝ)) + 3 * (c + Cs) by ring, Real.exp_add, h2, mul_comm]
      _ ≤ max 1 (Real.exp (3 * (c + Cs))) * (Real.log Z) ^ 8 := by
          have hpow38 : (Real.log (Z:ℝ)) ^ 3 ≤ (Real.log Z) ^ 8 :=
            pow_le_pow_right₀ hlogZ1 (by norm_num : (3:ℕ) ≤ 8)
          have hmax : Real.exp (3 * (c + Cs)) ≤ max 1 (Real.exp (3 * (c + Cs))) := le_max_right _ _
          exact mul_le_mul hmax hpow38 (pow_nonneg hlogZpos.le 3)
            (le_trans (Real.exp_pos _).le (le_max_right _ _))
  calc (Nat.sqrt y : ℝ) ^ (-(1 / Real.log (Z:ℝ))) *
        ∏ p ∈ Nat.primesBelow Z, (1 + (p : ℝ) ^ (1 / Real.log (Z:ℝ)) * g p)
      ≤ Real.exp (-(Real.log y / (4 * Real.log Z))) *
        (max 1 (Real.exp (3 * (c + Cs))) * (Real.log Z) ^ 8) := by
        have hb : 0 ≤ ∏ p ∈ Nat.primesBelow Z, (1 + (p : ℝ) ^ (1 / Real.log (Z:ℝ)) * g p) :=
          Finset.prod_nonneg (fun p _ => add_nonneg zero_le_one
            (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (hg0 p)))
        have hc : 0 ≤ Real.exp (-(Real.log y / (4 * Real.log Z))) := Real.exp_nonneg _
        exact mul_le_mul hexp1 hprod1 hb hc
    _ = max 1 (Real.exp (3 * (c + Cs))) *
        Real.exp (-(Real.log y / (4 * Real.log Z))) * (Real.log Z) ^ 8 := by ring


/-- Any sub-collection of the `(ϱ-)coprime` divisors of the primorial has `g`-mass at
most the Euler product. -/
lemma smooth_sum_le (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1)
    (Z ϱ : ℕ) (S : Finset ℕ)
    (hS : S ⊆ (Nat.divisors (primeZProd Z)).filter (fun m => Nat.Coprime m ϱ)) :
    (∑ m ∈ S, g m) ≤ ∏ p ∈ Nat.primesBelow Z, (1 + g p) :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg hS (fun x _ _ => hg0 x))
    (smooth_g_sum_le g hg0 hgmul hg1 Z ϱ)

/-- The `g`-mass of the squarefree numbers up to `N` is at most the Euler product. -/
lemma squarefree_sum_g_le (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n) (hg1 : g 1 = 1) (N : ℕ) :
    (∑ n ∈ (Finset.Icc 1 N).filter Squarefree, g n) ≤ ∏ p ∈ Nat.primesBelow (N + 1), (1 + g p) := by
  have hsub : (Finset.Icc 1 N).filter Squarefree
      ⊆ (Nat.divisors (∏ p ∈ Nat.primesBelow (N + 1), p)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hnsq⟩ := hn
    rw [Nat.mem_divisors]
    refine ⟨?_, ?_⟩
    · rw [← Nat.prod_primeFactors_of_squarefree hnsq]
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hle : p ≤ n := Nat.le_of_dvd (by omega) hpn
      exact Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩
    · exact Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primesBelow hp).ne_zero)
  calc (∑ n ∈ (Finset.Icc 1 N).filter Squarefree, g n)
      ≤ ∑ n ∈ Nat.divisors (∏ p ∈ Nat.primesBelow (N + 1), p), g n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hg0 x)
    _ = ∏ p ∈ Nat.primesBelow (N + 1), (1 + g p) :=
        Commons.NumberTheory.ArithmeticFunction.sum_divisors_prod_primes g hgmul hg1 (N + 1)


/-! ## Ordered telescoping of products (used for the `g` vs `1/n` comparison) -/

lemma prod_sub_prod_finset {ι : Type*} [LinearOrder ι] (s : Finset ι) (a b : ι → ℝ) :
    ∏ p ∈ s, a p - ∏ p ∈ s, b p
      = ∑ q ∈ s, (∏ p ∈ s.filter (fun p => q < p), a p) * (a q - b q)
                * (∏ p ∈ s.filter (fun p => p < q), b p) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert M s hlt ih =>
    have hMs : M ∉ s := fun h => absurd (hlt M h) (lt_irrefl M)
    rw [Finset.prod_insert hMs, Finset.prod_insert hMs, Finset.sum_insert hMs]
    have hMgt : s.filter (fun p => M < p) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp; rw [Finset.mem_filter] at hp
      exact absurd hp.2 (not_lt.mpr (le_of_lt (hlt p hp.1)))
    have hMlt : s.filter (fun p => p < M) = s := Finset.filter_true_of_mem (fun p hp => hlt p hp)
    have hMgti : (insert M s).filter (fun p => M < p) = ∅ := by
      rw [Finset.filter_insert, if_neg (lt_irrefl M)]; exact hMgt
    have hMlti : (insert M s).filter (fun p => p < M) = s := by
      rw [Finset.filter_insert, if_neg (lt_irrefl M)]; exact hMlt
    rw [hMgti, hMlti, Finset.prod_empty, one_mul]
    have hcongr : ∀ q ∈ s, (∏ p ∈ (insert M s).filter (fun p => q < p), a p) * (a q - b q)
        * (∏ p ∈ (insert M s).filter (fun p => p < q), b p)
        = a M * ((∏ p ∈ s.filter (fun p => q < p), a p) * (a q - b q)
                * (∏ p ∈ s.filter (fun p => p < q), b p)) := by
      intro q hq
      have hqM : q < M := hlt q hq
      have hMq : ¬ M < q := not_lt.mpr (le_of_lt hqM)
      have hMnotin : M ∉ s.filter (fun p => q < p) := fun h => hMs (Finset.mem_filter.mp h).1
      rw [Finset.filter_insert, if_pos hqM, Finset.filter_insert, if_neg hMq,
          Finset.prod_insert hMnotin]
      ring
    rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum, ← ih]
    ring


/-! ## Auxiliary constructions for the assembly

The target sum carries the factor `μ`, which vanishes on non-squarefree integers.  It is
therefore harmless to replace `g` by its restriction `sqfreeMul g` to squarefree integers;
the advantage is that `sqfreeMul g` has controlled total mass
`∑_{n ≤ N} sqfreeMul g n ≤ ∏_{p ≤ N} (1 + g p) ≪ log N`. -/

/-- `g` restricted to squarefree integers, and `0` elsewhere. -/
def sqfreeMul (g : ℕ → ℝ) : ℕ → ℝ := fun n => if Squarefree n then g n else 0

lemma sqfreeMul_nonneg {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ sqfreeMul g n := by
  unfold sqfreeMul; split <;> simp [hg0]

lemma sqfreeMul_one {g : ℕ → ℝ} (hg1 : g 1 = 1) : sqfreeMul g 1 = 1 := by
  unfold sqfreeMul; rw [if_pos (squarefree_one (R := ℕ)), hg1]

lemma sqfreeMul_of_squarefree {g : ℕ → ℝ} {n : ℕ} (hn : Squarefree n) : sqfreeMul g n = g n := by
  unfold sqfreeMul; rw [if_pos hn]

lemma sqfreeMul_of_not_squarefree {g : ℕ → ℝ} {n : ℕ} (hn : ¬ Squarefree n) :
    sqfreeMul g n = 0 := by
  unfold sqfreeMul; rw [if_neg hn]

lemma sqfreeMul_mul {g : ℕ → ℝ}
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    {m n : ℕ} (h : Nat.Coprime m n) : sqfreeMul g (m * n) = sqfreeMul g m * sqfreeMul g n := by
  by_cases hm : Squarefree m
  · by_cases hn : Squarefree n
    · rw [sqfreeMul_of_squarefree (Nat.squarefree_mul h |>.mpr ⟨hm, hn⟩),
        sqfreeMul_of_squarefree hm, sqfreeMul_of_squarefree hn, hgmul m n h]
    · rw [sqfreeMul_of_not_squarefree hn, mul_zero]
      by_cases hmn : Squarefree (m * n)
      · exact absurd (Squarefree.squarefree_of_dvd (Nat.dvd_mul_left n m) hmn) hn
      · exact sqfreeMul_of_not_squarefree hmn
  · rw [sqfreeMul_of_not_squarefree hm, zero_mul]
    by_cases hmn : Squarefree (m * n)
    · exact absurd (Squarefree.squarefree_of_dvd (Nat.dvd_mul_right m n) hmn) hm
    · exact sqfreeMul_of_not_squarefree hmn

/-- `(n, primeZProd Z) = 1` iff every prime factor of `n` is `≥ Z`. -/
lemma coprime_primeZProd_iff {Z n : ℕ} (hn : n ≠ 0) :
    Nat.Coprime n (primeZProd Z) ↔ ∀ p : ℕ, p ∈ n.primeFactors → Z ≤ p := by
  constructor
  · exact fun h p hp => le_of_mem_primeFactors_of_coprime_primorial h hp
  · intro h
    rw [Nat.Coprime]
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpn : p ∣ n := hpd.trans (Nat.gcd_dvd_left n (primeZProd Z))
    have hpPS : p ∣ primeZProd Z := hpd.trans (Nat.gcd_dvd_right n (primeZProd Z))
    have hpPF : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩
    have hle := h p hpPF
    have hpPF' : p ∈ (primeZProd Z).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpPS, primeZProd_ne_zero Z⟩
    rw [primeFactors_primeZProd] at hpPF'
    have := (Nat.mem_primesBelow.mp hpPF').1
    omega

/-- Real-valued version of `coprime_primeZProd_iff`. -/
lemma coprime_primeZProd_iff_real {Z n : ℕ} (hn : n ≠ 0) :
    Nat.Coprime n (primeZProd Z) ↔ ∀ p : ℕ, p ∈ n.primeFactors → (Z : ℝ) ≤ (p : ℝ) := by
  rw [coprime_primeZProd_iff hn]
  constructor
  · intro h p hp; exact_mod_cast h p hp
  · intro h p hp; exact_mod_cast h p hp

/-- A Möbius-weighted sum does not see an explicit `Squarefree` filter. -/
lemma sum_filter_squarefree_moebius {P : ℕ → Prop} [DecidablePred P]
    (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ s.filter (fun n => Squarefree n ∧ P n), (ArithmeticFunction.moebius n : ℝ) * f n)
      = ∑ n ∈ s.filter P, (ArithmeticFunction.moebius n : ℝ) * f n := by
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hP : P n
  · rw [if_pos hP]
    by_cases hs : Squarefree n
    · rw [if_pos (show Squarefree n ∧ P n from ⟨hs, hP⟩)]
    · rw [if_neg (fun h => hs h.1), ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
      ring
  · rw [if_neg hP, if_neg (fun h => hP h.2)]

/-- The Friedlander–Iwaniec factor `σ_ν = ∏_{p | ν} (1 + 1/√p)` is at least `1`. -/
lemma one_le_sigma (ν : ℕ) :
    1 ≤ ∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) := by
  refine Finset.one_le_prod₀ fun p _ => ?_
  have : (0 : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := by positivity
  linarith

/-- The harmonic sum bound `∑_{m ≤ N} 1/m ≤ 1 + log N`. -/
lemma sum_Icc_one_div_le : ∀ N : ℕ,
    (∑ m ∈ Finset.Icc 1 N, 1 / (m : ℝ)) ≤ 1 + Real.log N := by
  intro N
  induction N with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num
    have hstep : (∑ m ∈ Finset.Icc 1 (k + 1), 1 / (m : ℝ))
        = (∑ m ∈ Finset.Icc 1 k, 1 / (m : ℝ)) + 1 / ((k + 1 : ℕ) : ℝ) :=
      Finset.sum_Icc_succ_top (by omega) _
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      have : (1 : ℕ) ≤ k := hk
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)
    have hkp1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    have hlog : 1 / ((k + 1 : ℕ) : ℝ) ≤ Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) := by
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hlt : (0 : ℝ) < (k : ℝ) / ((k : ℝ) + 1) := by positivity
      have h1 : Real.log ((k : ℝ) / ((k : ℝ) + 1)) ≤ (k : ℝ) / ((k : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos hlt
      have h2 : (k : ℝ) / ((k : ℝ) + 1) - 1 = -(1 / ((k : ℝ) + 1)) := by
        field_simp; ring
      rw [h2] at h1
      have h3 : Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)
          = -Real.log ((k : ℝ) / ((k : ℝ) + 1)) := by
        rw [Real.log_div hkpos.ne' hkp1.ne']; ring
      rw [h3]
      linarith
    rw [hstep]
    have hcast2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast2] at hlog ⊢
    linarith [ih, hlog]


/-! ## Helpers for the main assembly -/

/-- `∑ x ≤ ∏ (1 + x)` for nonnegative `x`. -/
lemma sum_le_prod_one_add {ι : Type*} [DecidableEq ι] :
    ∀ (s : Finset ι) (f : ι → ℝ), (∀ i ∈ s, 0 ≤ f i) → ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro f _; simp
  | insert a s ha ih =>
    intro f hf
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := ih f (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h2 : 1 ≤ ∏ i ∈ s, (1 + f i) :=
      Finset.one_le_prod₀ (fun i hi => by linarith [hf i (Finset.mem_insert_of_mem hi)])
    have h0 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have h3 : f a * 1 ≤ f a * ∏ i ∈ s, (1 + f i) := mul_le_mul_of_nonneg_left h2 h0
    linarith [h1, h3]

/-- The range-sum comparison for the Mertens-type hypothesis: on a range of primes above
`Z`, the difference `1/p - g(p)` (with the primes dividing `ϱ` removed from `g`) is at most
`Cgap (log Z)^{-10} + Cg σ_ϱ / √Z`. -/
lemma range_gap_le {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n) {Cg Cgap : ℝ} (hCg : 0 ≤ Cg)
    (hgap : ∀ z : ℕ, 2 ≤ z → ∀ u v : ℕ, z ≤ u →
      |∑ p ∈ (Finset.Icc u v).filter Nat.Prime, (g p - 1 / (p : ℝ))| ≤
        Cgap * (Real.log z) ^ (-10 : ℝ))
    (hgple : ∀ p : ℕ, p.Prime → g p ≤ Cg / (p : ℝ))
    {ϱ Z : ℕ} (hϱ : 1 ≤ ϱ) (hZ : 2 ≤ Z) :
    ∀ u v : ℕ, Z ≤ u →
      |∑ p ∈ (Finset.Icc u v).filter Nat.Prime,
          (1 / (p : ℝ) - if p ∣ ϱ then 0 else g p)|
        ≤ Cgap * (Real.log Z) ^ (-10 : ℝ)
          + Cg * (∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) / Real.sqrt (Z : ℝ) := by
  intro u v huv
  set S : Finset ℕ := (Finset.Icc u v).filter Nat.Prime with hS
  have hZpos : (0 : ℝ) < Z := by positivity
  have hsqrtZ : (0 : ℝ) < Real.sqrt Z := Real.sqrt_pos.mpr hZpos
  have hσnn : 0 ≤ ∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  -- split the summand
  have hdecomp : (∑ p ∈ S, (1 / (p : ℝ) - if p ∣ ϱ then 0 else g p))
      = (∑ p ∈ S, (1 / (p : ℝ) - g p)) + ∑ p ∈ S, (if p ∣ ϱ then g p else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p ∣ ϱ <;> simp [h]
  have h1 : |∑ p ∈ S, (1 / (p : ℝ) - g p)| ≤ Cgap * (Real.log Z) ^ (-10 : ℝ) := by
    have h := hgap Z hZ u v huv
    have heq : (∑ p ∈ S, (1 / (p : ℝ) - g p)) = -(∑ p ∈ S, (g p - 1 / (p : ℝ))) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [heq, abs_neg]
    exact_mod_cast h
  have h2 : ∑ p ∈ S, (if p ∣ ϱ then g p else 0)
      ≤ Cg * (∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) / Real.sqrt (Z : ℝ) := by
    have hsum : (∑ p ∈ S, (if p ∣ ϱ then g p else 0))
        = ∑ p ∈ S.filter (fun p => p ∣ ϱ), g p :=
      (Finset.sum_filter (s := S) (p := fun p => p ∣ ϱ) (f := g)).symm
    rw [hsum]
    have hsub : S.filter (fun p => p ∣ ϱ) ⊆ ϱ.primeFactors.filter (fun p => Z ≤ p) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      obtain ⟨hpS, hpdvd⟩ := hp
      rw [hS, Finset.mem_filter, Finset.mem_Icc] at hpS
      obtain ⟨⟨hup, _⟩, hpp⟩ := hpS
      refine ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, by omega⟩, le_trans huv hup⟩
    have hstep1 : (∑ p ∈ S.filter (fun p => p ∣ ϱ), g p)
        ≤ ∑ p ∈ ϱ.primeFactors.filter (fun p => Z ≤ p), g p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hg0 x)
    have hstep2 : (∑ p ∈ ϱ.primeFactors.filter (fun p => Z ≤ p), g p)
        ≤ ∑ p ∈ ϱ.primeFactors.filter (fun p => Z ≤ p),
            (Cg / Real.sqrt Z) * (1 / Real.sqrt (p : ℝ)) := by
      refine Finset.sum_le_sum fun p hp => ?_
      rw [Finset.mem_filter] at hp
      have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp.1
      have hppos : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hZp : Z ≤ p := hp.2
      have hZle : (Z : ℝ) ≤ (p : ℝ) := by exact_mod_cast hZp
      have hsqrt : Real.sqrt Z ≤ Real.sqrt p := Real.sqrt_le_sqrt hZle
      have h1p : 1 / (p : ℝ) ≤ (1 / Real.sqrt Z) * (1 / Real.sqrt (p : ℝ)) := by
        have hle : Real.sqrt ((Z : ℝ) * (p : ℝ)) ≤ (p : ℝ) := by
          rw [Real.sqrt_le_iff]
          exact ⟨by positivity, by nlinarith [hZle, hppos]⟩
        have h1 : 1 / (p : ℝ) ≤ 1 / Real.sqrt ((Z : ℝ) * (p : ℝ)) :=
          one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) hle
        have h2 : Real.sqrt ((Z : ℝ) * (p : ℝ)) = Real.sqrt Z * Real.sqrt (p : ℝ) :=
          Real.sqrt_mul (by positivity) _
        have h3 : 1 / (Real.sqrt Z * Real.sqrt (p : ℝ))
            = (1 / Real.sqrt Z) * (1 / Real.sqrt (p : ℝ)) := by
          rw [one_div, one_div, one_div, mul_inv]
        rw [h2, h3] at h1
        exact h1
      have := hgple p hpp
      have hCgdiv : g p ≤ Cg / (p : ℝ) := this
      calc g p ≤ Cg / (p : ℝ) := hCgdiv
        _ = Cg * (1 / (p : ℝ)) := by ring
        _ ≤ Cg * ((1 / Real.sqrt Z) * (1 / Real.sqrt (p : ℝ))) :=
            mul_le_mul_of_nonneg_left h1p hCg
        _ = (Cg / Real.sqrt Z) * (1 / Real.sqrt (p : ℝ)) := by ring
    have hstep3 : (∑ p ∈ ϱ.primeFactors.filter (fun p => Z ≤ p),
            (Cg / Real.sqrt Z) * (1 / Real.sqrt (p : ℝ)))
        = (Cg / Real.sqrt Z) * ∑ p ∈ ϱ.primeFactors.filter (fun p => Z ≤ p),
            (1 / Real.sqrt (p : ℝ)) := by
      rw [Finset.mul_sum]
    have hstep4 : (∑ p ∈ ϱ.primeFactors.filter (fun p => Z ≤ p), (1 / Real.sqrt (p : ℝ)))
        ≤ ∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) := by
      have hsub2 : ϱ.primeFactors.filter (fun p => Z ≤ p) ⊆ ϱ.primeFactors :=
        Finset.filter_subset _ _
      have hle1 : (∑ p ∈ ϱ.primeFactors.filter (fun p => Z ≤ p), (1 / Real.sqrt (p : ℝ)))
          ≤ ∑ p ∈ ϱ.primeFactors, (1 / Real.sqrt (p : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun x _ _ => by positivity)
      have hle2 := sum_le_prod_one_add ϱ.primeFactors
        (fun p => 1 / Real.sqrt (p : ℝ)) (fun p _ => by positivity)
      linarith
    calc (∑ p ∈ S.filter (fun p => p ∣ ϱ), g p)
        ≤ ∑ p ∈ ϱ.primeFactors.filter (fun p => Z ≤ p), g p := hstep1
      _ ≤ (Cg / Real.sqrt Z) * ∑ p ∈ ϱ.primeFactors.filter (fun p => Z ≤ p),
            (1 / Real.sqrt (p : ℝ)) := by rw [← hstep3]; exact hstep2
      _ ≤ (Cg / Real.sqrt Z) * ∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep4 (by positivity)
      _ = Cg * (∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) / Real.sqrt (Z : ℝ) := by ring
  have h2nn : 0 ≤ ∑ p ∈ S, (if p ∣ ϱ then g p else 0) :=
    Finset.sum_nonneg fun p _ => by split <;> [exact hg0 p; exact le_refl 0]
  rw [hdecomp]
  calc |(∑ p ∈ S, (1 / (p : ℝ) - g p)) + ∑ p ∈ S, (if p ∣ ϱ then g p else 0)|
      ≤ |∑ p ∈ S, (1 / (p : ℝ) - g p)| + |∑ p ∈ S, (if p ∣ ϱ then g p else 0)| := abs_add_le _ _
    _ ≤ |∑ p ∈ S, (1 / (p : ℝ) - g p)|
          + Cg * (∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) / Real.sqrt (Z : ℝ) := by
        rw [abs_of_nonneg h2nn]; linarith [h2]
    _ ≤ Cgap * (Real.log Z) ^ (-10 : ℝ)
          + Cg * (∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) / Real.sqrt (Z : ℝ) := by
        linarith [h1]


/-- Rewriting the inner sum of the hyperbola into the form used by `sifted_sum_comparison`,
replacing `g` by `sqfreeMul g`. -/
lemma afun_eq (s : Finset ℕ) (g : ℕ → ℝ) (Z ϱ : ℕ) (hs : ∀ n ∈ s, 1 ≤ n) :
    (∑ n ∈ s.filter (fun n => Squarefree n ∧ Nat.Coprime n (primeZProd Z * ϱ)),
        (ArithmeticFunction.moebius n : ℝ) * g n)
      = ∑ n ∈ s.filter (fun n =>
            (∀ p : ℕ, p ∈ n.primeFactors → (Z : ℝ) ≤ (p : ℝ)) ∧ Nat.Coprime n ϱ),
          (ArithmeticFunction.moebius n : ℝ) * sqfreeMul g n := by
  rw [sum_filter_squarefree_moebius (P := fun n => Nat.Coprime n (primeZProd Z * ϱ)) s g]
  have hfil : s.filter (fun n => Nat.Coprime n (primeZProd Z * ϱ))
      = s.filter (fun n => (∀ p : ℕ, p ∈ n.primeFactors → (Z : ℝ) ≤ (p : ℝ)) ∧ Nat.Coprime n ϱ) := by
    refine Finset.filter_congr fun n hn => ?_
    have hn0 : n ≠ 0 := by have := hs n hn; omega
    rw [Nat.coprime_mul_iff_right, coprime_primeZProd_iff_real hn0]
  rw [hfil]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_filter] at hn
  by_cases hs' : Squarefree n
  · rw [sqfreeMul_of_squarefree hs']
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs']; ring

/-- The mass of `sqfreeMul g` equals the mass of `g` on squarefree integers. -/
lemma sum_sqfreeMul (g : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, sqfreeMul g n)
      = ∑ n ∈ (Finset.Icc 1 N).filter Squarefree, g n := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold sqfreeMul
  by_cases h : Squarefree n <;> simp [h]

/-! ## The target theorem

The remaining ingredients are the analytic Möbius reciprocal bound (`moebius_recip_sifted_powLog`,
being proved in parallel) and the ordered-factorisation comparison `moebius_recip_comparison`
(the telescoping identity `prod_sub_prod_finset` above is the key input to its proof). -/


/-! ## The target theorem (Friedlander–Iwaniec, "Asymptotic sieve for primes", (2.4))

The proof (see the plan below) proceeds via:
* `moebius_sum_hyperbola`   — the smooth/rough (Buchstab) hyperbola decomposition;
* `rankin_H_bound`          — Rankin's trick for the large smooth part;
* `smooth_sum_le` / `prod_one_add_g_le` — bounds for the small smooth part;
* the ordered-factorisation comparison `moebius_recip_comparison`
  (built from `prod_sub_prod_finset`) and the sharp Mertens gap
  `Commons.NumberTheory.Mertens.mertens_range_gap_bound`;
* the analytic sifted Möbius reciprocal bound `moebius_recip_sifted_powLog`. -/

/-- . -/
lemma rpow_neg_six (x : ℝ) (hx : 0 < x) : x ^ (-6 : ℝ) = 1 / x ^ 6 := by
  rw [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt hx),
    Real.rpow_natCast, one_div]

/-- . -/
lemma rpow_neg_ten (x : ℝ) (hx : 0 < x) : x ^ (-10 : ℝ) = 1 / x ^ 10 := by
  rw [show (-10 : ℝ) = -((10 : ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt hx),
    Real.rpow_natCast, one_div]

/-- If `6 log B + log A ≤ c` then `exp (-c) ≤ B^{-6}/A`. -/
lemma exp_neg_le_rpow_neg_six_div {c A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : 6 * Real.log B + Real.log A ≤ c) : Real.exp (-c) ≤ B ^ (-6 : ℝ) / A := by
  rw [rpow_neg_six B hB]
  have hkey : Real.exp (-c) ≤ 1 / (A * B ^ 6) := by
    have h1 : -c ≤ Real.log (1 / (A * B ^ 6)) := by
      rw [Real.log_div (by norm_num) (by positivity), Real.log_mul hA.ne' (pow_ne_zero 6 hB.ne'),
        Real.log_pow, Real.log_one]
      push_cast
      linarith
    calc Real.exp (-c) ≤ Real.exp (Real.log (1 / (A * B ^ 6))) := Real.exp_le_exp.mpr h1
      _ = 1 / (A * B ^ 6) := Real.exp_log (by positivity)
  calc Real.exp (-c) ≤ 1 / (A * B ^ 6) := hkey
    _ = (1 / B ^ 6) / A := by ring

theorem sieve_mu_sum_coprime_powLog
    (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg1 : g 1 = 1)
    (hgmul : ∀ m n : ℕ, Nat.Coprime m n → g (m * n) = g m * g n)
    (hgp_lt : ∀ p : ℕ, p.Prime → g p < 1)
    (hgp_le : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ))
    (hg_sum : ∃ c C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (⌊y⌋₊).primesLE, g p) - (Real.log (Real.log y) + c)| ≤
        C * (Real.log y) ^ (-10 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϱ y : ℕ, 1 ≤ ϱ → 2 ≤ y →
      |∑ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ Nat.Coprime d ϱ),
          (ArithmeticFunction.moebius d : ℝ) * g d|
        ≤ C * (∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) *
              (Real.log y) ^ (-6 : ℝ) := by
  classical
  obtain ⟨cg, Cs, hCs, hgsum⟩ := hg_sum
  obtain ⟨Cg, hCg, hgple⟩ := hgp_le
  obtain ⟨Cgap, hCgap, hgap⟩ :=
    Commons.NumberTheory.Mertens.mertens_range_gap_bound g cg Cs hgsum
  obtain ⟨cA, CA, hcA, hCA, hAb⟩ :=
    Commons.NumberTheory.Sieve.moebius_rough_recip_large_z
  obtain ⟨C1, hC1, hprod1⟩ := prod_one_add_g_le g hg0 cg Cs hgsum
  obtain ⟨CH, hCH, hrankin⟩ := rankin_H_bound g hg0 hgmul hg1 cg Cs hgsum
  have hC1nn : 0 ≤ C1 := le_of_lt hC1
  have hCAnn : 0 ≤ CA := le_of_lt hCA
  have hCHnn : 0 ≤ CH := le_of_lt hCH
  have hCgnn : 0 ≤ Cg := le_of_lt hCg
  have hCgapnn : 0 ≤ Cgap := le_of_lt hCgap
  -- a first elementary mass bound for squarefree integers
  have hmass_lin : ∀ N : ℕ, (∑ n ∈ (Finset.Icc 1 N).filter Squarefree, g n)
      ≤ C1 * (1 + Real.log ((N : ℝ) + 1)) := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp only [Finset.Icc_eq_empty (by norm_num : ¬ (1:ℕ) ≤ 0), Finset.filter_empty,
        Finset.sum_empty, Nat.cast_zero, zero_add, Real.log_one, add_zero, mul_one]
      exact hC1nn
    · have h := squarefree_sum_g_le g hg0 hgmul hg1 N
      have h2 := hprod1 (N + 1) (by omega)
      have hcast : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast] at h2
      exact le_trans h h2
  -- constants for the choice of `Z`
  set E : ℝ := 2 * C1 with hEdef
  have hEpos : 0 < E := by rw [hEdef]; linarith
  set α : ℝ := 64 * C1 * E * (Cgap + Cg + 1) + 16 * C1 * CA + 1 with hαdef
  have hαpos : 0 < α := by rw [hαdef]; positivity
  have hα1 : 16 * C1 * CA ≤ 3 * α := by
    rw [hαdef]
    have h1 : 0 ≤ 64 * C1 * E * (Cgap + Cg + 1) := by positivity
    have h2 : 0 ≤ 16 * C1 * CA := by positivity
    linarith
  have hα2 : 64 * C1 * E * (Cgap + Cg + 1) ≤ 3 * α := by
    rw [hαdef]
    have h1 : 0 ≤ 64 * C1 * E * (Cgap + Cg + 1) := by positivity
    have h2 : 0 ≤ 16 * C1 * CA := by positivity
    linarith
  set γ : ℝ := max (Real.log (16 * C1 * CA + 1)) (Real.log (8 * C1 * CH + 1)) + 4 with hγdef
  have hγ1 : Real.log (16 * C1 * CA) ≤ γ := by
    have h2 : Real.log (16 * C1 * CA) ≤ Real.log (16 * C1 * CA + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have h3 : Real.log (16 * C1 * CA + 1) ≤ γ := by
      rw [hγdef]
      linarith [le_max_left (Real.log (16 * C1 * CA + 1)) (Real.log (8 * C1 * CH + 1))]
    linarith
  have hγ2 : Real.log (8 * C1 * CH) ≤ γ := by
    have h2 : Real.log (8 * C1 * CH) ≤ Real.log (8 * C1 * CH + 1) :=
      Real.log_le_log (by positivity) (by nlinarith [hC1, hCH])
    have h3 : Real.log (8 * C1 * CH + 1) ≤ γ := by
      rw [hγdef]
      linarith [le_max_right (Real.log (16 * C1 * CA + 1)) (Real.log (8 * C1 * CH + 1))]
    linarith
  have hγ3 : Real.log (32 * C1 * CH) ≤ γ := by
    have h2 : Real.log (32 * C1 * CH) ≤ Real.log (4 * (8 * C1 * CH + 1)) := by
      apply Real.log_le_log (by positivity)
      nlinarith [hC1, hCH]
    have h3 : Real.log (4 * (8 * C1 * CH + 1)) = Real.log 4 + Real.log (8 * C1 * CH + 1) :=
      Real.log_mul (by norm_num) (by positivity)
    have h4 : Real.log 4 ≤ 2 := by
      have h6 : Real.log (4:ℝ) = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      rw [h6]; linarith [Real.log_two_lt_d9]
    have h5 : Real.log (8 * C1 * CH + 1) ≤ γ - 4 := by
      rw [hγdef]
      linarith [le_max_right (Real.log (16 * C1 * CA + 1)) (Real.log (8 * C1 * CH + 1))]
    rw [h3] at h2; linarith
  obtain ⟨L0, hL0pos, hZlem⟩ := Commons.NumberTheory.Sieve.exists_good_Z_sieve α hαpos cA hcA γ
  set Y0 : ℕ := max 16 (⌈Real.exp L0⌉₊ + 2) with hY0def
  have hY016 : 16 ≤ Y0 := le_max_left _ _
  have hexpL0 : Real.exp L0 ≤ (Y0 : ℝ) := by
    have h1 : Real.exp L0 ≤ (⌈Real.exp L0⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp L0⌉₊ + 2 : ℕ) : ℝ) ≤ (Y0 : ℝ) := by
      rw [hY0def]; exact_mod_cast le_max_right 16 (⌈Real.exp L0⌉₊ + 2)
    push_cast at h2
    linarith
  have hlogY0pos : 0 < Real.log (Y0 : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y0 by omega))
  set Csmall : ℝ := C1 * (1 + Real.log ((Y0 : ℝ) + 1)) * (Real.log (Y0 : ℝ)) ^ 6 with hCsmalldef
  have hsmall_nonneg : 0 ≤ Csmall := by
    rw [hCsmalldef]
    have h : 0 ≤ Real.log ((Y0 : ℝ) + 1) := Real.log_nonneg (by linarith)
    positivity
  refine ⟨max Csmall 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro ϱ y hϱ hy
  have hy1R : (1 : ℝ) < (y : ℝ) := by exact_mod_cast (show 1 < y by omega)
  by_cases hyy : y < Y0
  · -- small `y`
    have hypos : 0 < Real.log (y : ℝ) := Real.log_pos hy1R
    have hlogyle : Real.log (y : ℝ) ≤ Real.log (Y0 : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast le_of_lt hyy)
    have hlogy1 : Real.log ((y : ℝ) + 1) ≤ Real.log ((Y0 : ℝ) + 1) := by
      refine Real.log_le_log (by positivity) ?_
      have : (y : ℝ) ≤ (Y0 : ℝ) := by exact_mod_cast le_of_lt hyy
      linarith
    have hb : |∑ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ Nat.Coprime d ϱ),
        (ArithmeticFunction.moebius d : ℝ) * g d| ≤ C1 * (1 + Real.log ((y : ℝ) + 1)) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hpt : ∀ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ Nat.Coprime d ϱ),
          |(ArithmeticFunction.moebius d : ℝ) * g d| ≤ g d := by
        intro d _
        have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
          rw [← Int.cast_abs]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
        rw [abs_mul, abs_of_nonneg (hg0 d)]
        calc |(ArithmeticFunction.moebius d : ℝ)| * g d ≤ 1 * g d :=
              mul_le_mul_of_nonneg_right hmu (hg0 d)
          _ = g d := by ring
      calc ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ Nat.Coprime d ϱ),
              |(ArithmeticFunction.moebius d : ℝ) * g d|
          ≤ ∑ d ∈ (Finset.Icc 1 y).filter Squarefree, g d := by
            refine le_trans (Finset.sum_le_sum hpt) ?_
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => hg0 d)
            intro d hd
            rw [Finset.mem_filter] at hd ⊢
            exact ⟨hd.1, hd.2.1⟩
        _ ≤ C1 * (1 + Real.log ((y : ℝ) + 1)) := hmass_lin y
    have hkey : C1 * (1 + Real.log ((y : ℝ) + 1)) ≤ Csmall * (Real.log (y : ℝ)) ^ (-6 : ℝ) := by
      rw [hCsmalldef, rpow_neg_six _ hypos, mul_one_div, le_div_iff₀ (pow_pos hypos 6)]
      have h2 : (Real.log (y : ℝ)) ^ 6 ≤ (Real.log (Y0 : ℝ)) ^ 6 :=
        pow_le_pow_left₀ hypos.le hlogyle 6
      have h4 : (1 + Real.log ((y : ℝ) + 1)) * (Real.log (y : ℝ)) ^ 6
          ≤ (1 + Real.log ((Y0 : ℝ) + 1)) * (Real.log (Y0 : ℝ)) ^ 6 := by
        have hnn : (0 : ℝ) ≤ (Real.log (y : ℝ)) ^ 6 := pow_nonneg hypos.le 6
        have hnn2 : (0 : ℝ) ≤ 1 + Real.log ((Y0 : ℝ) + 1) := by
          have := Real.log_nonneg (show (1:ℝ) ≤ (Y0:ℝ) + 1 by linarith [hlogY0pos])
          linarith
        exact mul_le_mul (by linarith) h2 hnn hnn2
      nlinarith [h4, hC1]
    calc |∑ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ Nat.Coprime d ϱ),
            (ArithmeticFunction.moebius d : ℝ) * g d|
        ≤ C1 * (1 + Real.log ((y : ℝ) + 1)) := hb
      _ ≤ Csmall * (Real.log (y : ℝ)) ^ (-6 : ℝ) := hkey
      _ ≤ max Csmall 1 * (∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) *
            (Real.log (y : ℝ)) ^ (-6 : ℝ) := by
          have hσ := one_le_sigma ϱ
          have hnn : 0 ≤ (Real.log (y : ℝ)) ^ (-6 : ℝ) := Real.rpow_nonneg hypos.le _
          have h1 : Csmall ≤ max Csmall 1 * (∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) := by
            have h2 : (1 : ℝ) ≤ max Csmall 1 := le_max_right _ _
            nlinarith [le_max_left Csmall 1, hσ, hsmall_nonneg]
          exact mul_le_mul_of_nonneg_right h1 hnn
  · -- large `y`
    have hyY0 : Y0 ≤ y := not_lt.mp hyy
    have hy16 : 16 ≤ y := le_trans hY016 hyY0
    set L : ℝ := Real.log (y : ℝ) with hLdef
    have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos hy1R
    have hL1 : 1 ≤ L := by
      rw [hLdef]
      have h1 : Real.exp 1 < (y : ℝ) := by
        have h2 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
        have h3 : (3 : ℝ) ≤ (y : ℝ) := by
          exact_mod_cast (le_trans (by norm_num : 3 ≤ 16) hy16)
        linarith
      have h4 := Real.log_lt_log (Real.exp_pos 1) h1
      rw [Real.log_exp] at h4
      exact le_of_lt h4
    have hL0le : L0 ≤ L := by
      rw [hLdef]
      have h1 : Real.exp L0 ≤ (y : ℝ) := le_trans hexpL0 (by exact_mod_cast hyY0)
      calc L0 = Real.log (Real.exp L0) := (Real.log_exp L0).symm
        _ ≤ Real.log (y : ℝ) := Real.log_le_log (Real.exp_pos L0) h1
    obtain ⟨Z, hZ3, hZ200, hZpow, hZ4, hZα, hZc, hZγ⟩ := hZlem L hL0le
    set lz : ℝ := Real.log (Z : ℝ) with hlzdef
    have hlz1 : 1 ≤ lz := by linarith
    have hlzpos : 0 < lz := by linarith
    have hTnn : 0 ≤ Real.log L := Real.log_nonneg hL1
    have hWnn : 0 ≤ Real.log lz := Real.log_nonneg hlz1
    have hZposR : (0 : ℝ) < (Z : ℝ) := by
      have : (0 : ℕ) < Z := by omega
      exact_mod_cast this
    have hZ3R : (3 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ3
    set σ : ℝ := ∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) with hσdef
    have hσ1 : 1 ≤ σ := one_le_sigma ϱ
    have hσpos : 0 < σ := lt_of_lt_of_le zero_lt_one hσ1
    set hc : ℝ := (Cgap + Cg + 1) * σ * lz ^ (-10 : ℝ) with hhcdef
    have hcnonneg : 0 ≤ hc := by rw [hhcdef]; positivity
    have hrangesum : ∀ u v : ℕ, ⌈(Z : ℝ)⌉₊ ≤ u →
        |∑ p ∈ (Finset.Icc u v).filter Nat.Prime,
            (1 / (p : ℝ) - if p ∣ ϱ then 0 else sqfreeMul g p)| ≤ hc := by
      intro u v huv
      have huvZ : Z ≤ u := by
        have h := huv; rwa [Nat.ceil_natCast] at h
      have h1 := range_gap_le hg0 hCg.le hgap hgple hϱ
        (le_trans (by norm_num : 2 ≤ 3) hZ3) u v huvZ
      have h2 : Cgap * (Real.log (Z : ℝ)) ^ (-10 : ℝ)
          + Cg * (∏ p ∈ ϱ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) / Real.sqrt (Z : ℝ) ≤ hc := by
        rw [hhcdef, ← hσdef]
        have hlz10pos : 0 < lz ^ 10 := by positivity
        have hsqrtpos : 0 < Real.sqrt (Z : ℝ) := Real.sqrt_pos.mpr hZposR
        have hle : (Real.sqrt (Z : ℝ))⁻¹ ≤ lz ^ (-10 : ℝ) := by
          rw [show lz ^ (-10 : ℝ) = (lz ^ 10)⁻¹ by
            rw [show (-10 : ℝ) = -((10:ℕ) : ℝ) by norm_num, Real.rpow_neg (le_of_lt hlzpos),
              Real.rpow_natCast]]
          exact (inv_le_inv₀ hsqrtpos hlz10pos).mpr hZpow
        have hstep : Cg * σ / Real.sqrt (Z : ℝ) ≤ Cg * σ * lz ^ (-10 : ℝ) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left hle (by positivity)
        have hstep2 : Cgap * lz ^ (-10 : ℝ) ≤ (Cgap + Cg + 1) * σ * lz ^ (-10 : ℝ) := by
          have hσle : Cgap ≤ (Cgap + Cg + 1) * σ := by nlinarith [hCgapnn, hCgnn, hσ1]
          exact mul_le_mul_of_nonneg_right hσle (Real.rpow_nonneg (le_of_lt hlzpos) _)
        have hstep3 : Cgap * σ * lz ^ (-10 : ℝ) + Cg * σ * lz ^ (-10 : ℝ)
            ≤ (Cgap + Cg + 1) * σ * lz ^ (-10 : ℝ) := by
          have hle2 : Cgap + Cg ≤ Cgap + Cg + 1 := by linarith
          have h3 : 0 ≤ σ * lz ^ (-10 : ℝ) := by positivity
          nlinarith [hle2, h3]
        have hs1 : Cgap * lz ^ (-10 : ℝ) ≤ Cgap * σ * lz ^ (-10 : ℝ) := by
          have hσle : Cgap ≤ Cgap * σ := by nlinarith [hCgapnn, hσ1]
          exact mul_le_mul_of_nonneg_right hσle (Real.rpow_nonneg hlzpos.le _)
        linarith [hs1, hstep3]
      have heq : (∑ p ∈ (Finset.Icc u v).filter Nat.Prime,
            (1 / (p : ℝ) - if p ∣ ϱ then 0 else sqfreeMul g p))
          = ∑ p ∈ (Finset.Icc u v).filter Nat.Prime,
            (1 / (p : ℝ) - if p ∣ ϱ then 0 else g p) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mem_filter] at hp
        rw [sqfreeMul_of_squarefree hp.2.squarefree]
      rw [heq]
      exact le_trans h1 h2
    -- the hyperbola decomposition
    have hhyp := moebius_sum_hyperbola Z ϱ y g hgmul
    set M : Finset ℕ := (Nat.divisors (primeZProd Z)).filter (fun m => Nat.Coprime m ϱ) with hMdef
    set Afun : ℕ → ℝ := fun t =>
      ∑ n ∈ (Finset.Icc 1 (y / t)).filter
        (fun n => Squarefree n ∧ Nat.Coprime n (primeZProd Z * ϱ)),
        (ArithmeticFunction.moebius n : ℝ) * g n with hAfundef
    have hG : (∑ d ∈ (Finset.Icc 1 y).filter (fun d => Squarefree d ∧ Nat.Coprime d ϱ),
          (ArithmeticFunction.moebius d : ℝ) * g d)
        = ∑ m ∈ M, (ArithmeticFunction.moebius m : ℝ) * g m * Afun m := hhyp
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := M)
      (p := fun m => m ≤ Nat.sqrt y)
      (f := fun m => (ArithmeticFunction.moebius m : ℝ) * g m * Afun m)
    -- per-term bound on the small smooth part
    have hpt1 : ∀ m ∈ M.filter (fun m => m ≤ Nat.sqrt y),
        |(ArithmeticFunction.moebius m : ℝ) * g m * Afun m|
          ≤ g m * (CA * ((Z : ℝ) ^ (-cA)
              + Real.exp (-(L / (4 * lz))) * lz ^ 6) + 2 * C1 * hc * (1 + L) ^ 2) := by
      intro m hm
      rw [Finset.mem_filter] at hm
      obtain ⟨hmM, hmsq⟩ := hm
      rw [Finset.mem_filter] at hmM
      obtain ⟨hmdvd, hmcop⟩ := hmM
      have hmpos : 0 < m :=
        Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hmdvd) (primeZProd_pos Z)
      have hmu : |(ArithmeticFunction.moebius m : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
      have hAbound : |Afun m| ≤ CA * ((Z : ℝ) ^ (-cA)
          + Real.exp (-(L / (4 * lz))) * lz ^ 6) + 2 * C1 * hc * (1 + L) ^ 2 := by
        have hmoved : Nat.sqrt y ≤ y / m := by
          rw [Nat.le_div_iff_mul_le hmpos]
          calc Nat.sqrt y * m ≤ Nat.sqrt y * Nat.sqrt y := Nat.mul_le_mul_left _ hmsq
            _ ≤ y := Nat.sqrt_le y
        set Bfun : ℝ := ∑ n ∈ (Finset.Icc 1 (y / m)).filter
            (fun n => (∀ p : ℕ, p ∈ n.primeFactors → (Z : ℝ) ≤ (p : ℝ)) ∧ Nat.Coprime n ϱ),
            (ArithmeticFunction.moebius n : ℝ) * sqfreeMul g n with hBfundef
        set Frec : ℝ := ∑ n ∈ (Finset.Icc 1 (y / m)).filter
            (fun n => ∀ p : ℕ, p ∈ n.primeFactors → (Z : ℝ) ≤ (p : ℝ)),
            (ArithmeticFunction.moebius n : ℝ) * (1 / (n : ℝ)) with hFrecdef
        have hAfunB : Afun m = Bfun := by
          rw [hAfundef, hBfundef]
          exact afun_eq (Finset.Icc 1 (y / m)) g Z ϱ (fun n hn => (Finset.mem_Icc.mp hn).1)
        have hw4 : 4 ≤ y / m := by
          refine le_trans ?_ hmoved
          rw [Nat.le_sqrt]
          omega
        have hw2 : 2 ≤ ((y / m : ℕ) : ℝ) := by
          have : (2 : ℕ) ≤ y / m := by omega
          exact_mod_cast this
        have hcmp := Commons.NumberTheory.Sieve.sifted_sum_comparison (sqfreeMul g)
          (sqfreeMul_nonneg hg0) (fun a b h => sqfreeMul_mul hgmul h) (sqfreeMul_one hg1)
          ϱ (z := (Z : ℝ)) (w := ((y / m : ℕ) : ℝ)) (by linarith) hw2 hcnonneg hrangesum
        rw [Nat.floor_natCast] at hcmp
        have hZ4le : (Z : ℝ) ^ 4 ≤ (y : ℝ) := by
          have h1 : Real.log ((Z : ℝ) ^ 4) ≤ Real.log (y : ℝ) := by
            rw [Real.log_pow, ← hlzdef, ← hLdef]
            push_cast
            linarith
          have h2 := Real.exp_le_exp.mpr h1
          rwa [Real.exp_log (by positivity), Real.exp_log (by positivity)] at h2
        have hZ2le : (Z : ℝ) ^ 2 ≤ ((y / m : ℕ) : ℝ) := by
          have hnat : Z * Z ≤ Nat.sqrt y := by
            rw [Nat.le_sqrt]
            have hcast : (((Z * Z) * (Z * Z) : ℕ) : ℝ) = (Z : ℝ) ^ 4 := by push_cast; ring
            have : (((Z * Z) * (Z * Z) : ℕ) : ℝ) ≤ (y : ℝ) := by rw [hcast]; exact hZ4le
            exact_mod_cast this
          calc (Z : ℝ) ^ 2 = ((Z * Z : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((Nat.sqrt y : ℕ) : ℝ) := by exact_mod_cast hnat
            _ ≤ ((y / m : ℕ) : ℝ) := by exact_mod_cast hmoved
        have hlogdiv : L / 4 ≤ Real.log ((y / m : ℕ) : ℝ) := by
          have h1 : ((Nat.sqrt y : ℕ) : ℝ) ≤ ((y / m : ℕ) : ℝ) := by exact_mod_cast hmoved
          refine le_trans ?_ (Real.log_le_log (by positivity) h1)
          have hspos : (0 : ℝ) < Real.sqrt (y : ℝ) := Real.sqrt_pos.mpr (by positivity)
          have h3 : Real.sqrt (y : ℝ) - 1 ≤ ((Nat.sqrt y : ℕ) : ℝ) := by
            have h : Real.sqrt (y : ℝ) < ((Nat.sqrt y : ℕ) : ℝ) + 1 := by
              rw [Real.sqrt_lt' (by positivity : (0 : ℝ) < ((Nat.sqrt y : ℕ) : ℝ) + 1)]
              have hnat : y < (Nat.sqrt y).succ * (Nat.sqrt y).succ := Nat.lt_succ_sqrt y
              have hcast : (((Nat.sqrt y).succ * (Nat.sqrt y).succ : ℕ) : ℝ)
                  = (((Nat.sqrt y : ℕ) : ℝ) + 1) ^ 2 := by
                push_cast [Nat.succ_eq_add_one]; ring
              rw [← hcast]; exact_mod_cast hnat
            linarith
          have h4 : Real.sqrt (y : ℝ) / 2 ≤ Real.sqrt (y : ℝ) - 1 := by
            have h5 : (2 : ℝ) ≤ Real.sqrt (y : ℝ) := by
              rw [Real.le_sqrt (by norm_num) (by positivity)]
              have : (4 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (by omega : 4 ≤ y)
              linarith
            linarith
          have h5 : Real.log (Real.sqrt (y : ℝ) / 2) ≤ Real.log ((Nat.sqrt y : ℕ) : ℝ) :=
            Real.log_le_log (by positivity) (by linarith)
          have h6 : Real.log (Real.sqrt (y : ℝ) / 2) = L / 2 - Real.log 2 := by
            rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by positivity), ← hLdef]
          have h7 : Real.log 2 ≤ L / 4 := by
            have h8 : Real.log (16 : ℝ) ≤ L := by
              rw [hLdef]
              exact Real.log_le_log (by norm_num) (by exact_mod_cast hy16)
            have h9 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
              rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
            rw [h9] at h8; linarith
          rw [h6] at h5; linarith
        have hFrec_bound : |Frec| ≤ CA * ((Z : ℝ) ^ (-cA)
            + Real.exp (-(L / (4 * lz))) * lz ^ 6) := by
          rw [hFrecdef]
          have hF := hAb (Z : ℝ) ((y / m : ℕ) : ℝ) hZ3R hw2 hZ2le
          rw [Nat.floor_natCast, ← hlzdef] at hF
          rw [show (∑ n ∈ (Finset.Icc 1 (y / m)).filter
                (fun n => ∀ p : ℕ, p ∈ n.primeFactors → (Z : ℝ) ≤ (p : ℝ)),
                (ArithmeticFunction.moebius n : ℝ) / (n : ℝ))
              = ∑ n ∈ (Finset.Icc 1 (y / m)).filter
                (fun n => ∀ p : ℕ, p ∈ n.primeFactors → (Z : ℝ) ≤ (p : ℝ)),
                (ArithmeticFunction.moebius n : ℝ) * (1 / (n : ℝ)) from by
            apply Finset.sum_congr rfl; intro n _; ring] at hF
          refine le_trans hF ?_
          have hexpmono : Real.exp (-(Real.log ((y / m : ℕ) : ℝ) / lz))
              ≤ Real.exp (-(L / (4 * lz))) := by
            apply Real.exp_le_exp.mpr
            have hdiv : (L / 4) / lz ≤ Real.log ((y / m : ℕ) : ℝ) / lz :=
              div_le_div_of_nonneg_right hlogdiv hlzpos.le
            have heq : L / (4 * lz) = (L / 4) / lz := by ring
            rw [heq]; linarith
          refine mul_le_mul_of_nonneg_left ?_ hCAnn
          have h2 : Real.exp (-(Real.log ((y / m : ℕ) : ℝ) / lz)) * lz ^ 6
              ≤ Real.exp (-(L / (4 * lz))) * lz ^ 6 :=
            mul_le_mul_of_nonneg_right hexpmono (by positivity)
          linarith
        have hRHS : hc * (∑ a ∈ Finset.Icc 1 (y / m), 1 / (a : ℝ))
              * (∑ n ∈ Finset.Icc 1 (y / m), sqfreeMul g n) ≤ 2 * C1 * hc * (1 + L) ^ 2 := by
          have h1 : (∑ a ∈ Finset.Icc 1 (y / m), 1 / (a : ℝ))
              ≤ 1 + Real.log ((y / m : ℕ) : ℝ) := sum_Icc_one_div_le _
          have h2 : Real.log ((y / m : ℕ) : ℝ) ≤ L := by
            rw [hLdef]
            exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.div_le_self y m)
          have h3 : (∑ n ∈ Finset.Icc 1 (y / m), sqfreeMul g n)
              = ∑ n ∈ (Finset.Icc 1 (y / m)).filter Squarefree, g n := sum_sqfreeMul g (y / m)
          rw [h3]
          have h4 : (∑ n ∈ (Finset.Icc 1 (y / m)).filter Squarefree, g n) ≤ 2 * C1 * (1 + L) := by
            refine le_trans (hmass_lin (y / m)) ?_
            have h5 : Real.log (((y / m : ℕ) : ℝ) + 1) ≤ 1 + L := by
              have h11 : ((y / m : ℕ) : ℝ) + 1 ≤ 2 * (y : ℝ) := by
                have h12 : ((y / m : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast Nat.div_le_self y m
                linarith
              have h14 : Real.log (((y / m : ℕ) : ℝ) + 1) ≤ Real.log (2 * (y : ℝ)) :=
                Real.log_le_log (by positivity) h11
              rw [Real.log_mul (by norm_num) (by positivity), ← hLdef] at h14
              linarith [Real.log_two_lt_d9]
            have h15 : (1 : ℝ) ≤ 1 + L := by linarith
            nlinarith [h5, h15, hC1nn, hLpos]
          have h6 : 1 + Real.log ((y / m : ℕ) : ℝ) ≤ 1 + L := by linarith
          have h7 : (0 : ℝ) ≤ hc := hcnonneg
          have h8 : (0 : ℝ) ≤ ∑ n ∈ (Finset.Icc 1 (y / m)).filter Squarefree, g n :=
            Finset.sum_nonneg fun n _ => hg0 n
          have h9 : (0 : ℝ) ≤ ∑ a ∈ Finset.Icc 1 (y / m), 1 / (a : ℝ) :=
            Finset.sum_nonneg fun a _ => by positivity
          calc hc * (∑ a ∈ Finset.Icc 1 (y / m), 1 / (a : ℝ))
                * (∑ n ∈ (Finset.Icc 1 (y / m)).filter Squarefree, g n)
              ≤ hc * (1 + L) * (2 * C1 * (1 + L)) := by
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_left (le_trans h1 h6) h7
                · exact h4
                · exact h8
                · positivity
            _ = 2 * C1 * hc * (1 + L) ^ 2 := by ring
        calc |Afun m| = |Bfun| := by rw [hAfunB]
          _ = |(Bfun - Frec) + Frec| := by ring_nf
          _ ≤ |Bfun - Frec| + |Frec| := abs_add_le _ _
          _ ≤ hc * (∑ a ∈ Finset.Icc 1 (y / m), 1 / (a : ℝ))
                * (∑ n ∈ Finset.Icc 1 (y / m), sqfreeMul g n)
              + CA * ((Z : ℝ) ^ (-cA) + Real.exp (-(L / (4 * lz))) * lz ^ 6) := by
              refine add_le_add ?_ hFrec_bound
              rw [abs_sub_comm]
              exact hcmp
          _ ≤ 2 * C1 * hc * (1 + L) ^ 2
              + CA * ((Z : ℝ) ^ (-cA) + Real.exp (-(L / (4 * lz))) * lz ^ 6) := by
              linarith [hRHS]
          _ = CA * ((Z : ℝ) ^ (-cA) + Real.exp (-(L / (4 * lz))) * lz ^ 6)
              + 2 * C1 * hc * (1 + L) ^ 2 := by ring
      rw [abs_mul, abs_mul, abs_of_nonneg (hg0 m)]
      calc |(ArithmeticFunction.moebius m : ℝ)| * g m * |Afun m|
          ≤ 1 * g m * (CA * ((Z : ℝ) ^ (-cA) + Real.exp (-(L / (4 * lz))) * lz ^ 6)
              + 2 * C1 * hc * (1 + L) ^ 2) := by
            have hnn : 0 ≤ CA * ((Z : ℝ) ^ (-cA) + Real.exp (-(L / (4 * lz))) * lz ^ 6)
                + 2 * C1 * hc * (1 + L) ^ 2 := by
              have h1 : 0 ≤ (Z : ℝ) ^ (-cA) := Real.rpow_nonneg hZposR.le _
              have h2 : 0 ≤ Real.exp (-(L / (4 * lz))) * lz ^ 6 := by positivity
              have h3 : 0 ≤ 2 * C1 * hc * (1 + L) ^ 2 := by
                rw [hhcdef]
                have h5 : 0 ≤ lz ^ (-10 : ℝ) := Real.rpow_nonneg hlzpos.le _
                have h6 : 0 ≤ σ := le_of_lt hσpos
                have h7 : 0 ≤ Cgap + Cg + 1 := by linarith [hCgapnn, hCgnn]
                have h8 : 0 ≤ (1 + L) ^ 2 := by positivity
                have h9 : 0 ≤ (Cgap + Cg + 1) * σ * lz ^ (-10 : ℝ) :=
                  mul_nonneg (mul_nonneg h7 h6) h5
                have h10 : 0 ≤ 2 * C1 * ((Cgap + Cg + 1) * σ * lz ^ (-10 : ℝ)) :=
                  mul_nonneg (by positivity) h9
                nlinarith [h8, h10]
              have h4 : 0 ≤ CA * ((Z : ℝ) ^ (-cA) + Real.exp (-(L / (4 * lz))) * lz ^ 6) :=
                mul_nonneg hCAnn (by linarith)
              linarith
            refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmu (hg0 m))
              (abs_nonneg _)) ?_
            exact mul_le_mul_of_nonneg_left hAbound (mul_nonneg zero_le_one (hg0 m))
        _ = g m * (CA * ((Z : ℝ) ^ (-cA) + Real.exp (-(L / (4 * lz))) * lz ^ 6)
              + 2 * C1 * hc * (1 + L) ^ 2) := by ring
    have hM1mass : (∑ m ∈ M.filter (fun m => m ≤ Nat.sqrt y), g m) ≤ 2 * C1 * lz := by
      have hsub : M.filter (fun m => m ≤ Nat.sqrt y) ⊆
          (Nat.divisors (primeZProd Z)).filter (fun m => Nat.Coprime m ϱ) := by
        rw [hMdef]; exact Finset.filter_subset _ _
      calc (∑ m ∈ M.filter (fun m => m ≤ Nat.sqrt y), g m)
          ≤ ∑ m ∈ (Nat.divisors (primeZProd Z)).filter (fun m => Nat.Coprime m ϱ), g m :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => hg0 _)
        _ ≤ ∏ p ∈ Nat.primesBelow Z, (1 + g p) := smooth_g_sum_le g hg0 hgmul hg1 Z ϱ
        _ ≤ C1 * (1 + lz) := by
            have := hprod1 Z (by omega)
            rwa [← hlzdef] at this
        _ ≤ 2 * C1 * lz := by nlinarith [hC1nn, hlz1]
    have hM1b : |∑ m ∈ M.filter (fun m => m ≤ Nat.sqrt y),
        (ArithmeticFunction.moebius m : ℝ) * g m * Afun m|
        ≤ (2 * C1 * lz) * (CA * ((Z : ℝ) ^ (-cA)
            + Real.exp (-(L / (4 * lz))) * lz ^ 6) + 2 * C1 * hc * (1 + L) ^ 2) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc (∑ m ∈ M.filter (fun m => m ≤ Nat.sqrt y),
              |(ArithmeticFunction.moebius m : ℝ) * g m * Afun m|)
          ≤ ∑ m ∈ M.filter (fun m => m ≤ Nat.sqrt y),
              g m * (CA * ((Z : ℝ) ^ (-cA)
                + Real.exp (-(L / (4 * lz))) * lz ^ 6) + 2 * C1 * hc * (1 + L) ^ 2) :=
            Finset.sum_le_sum hpt1
        _ = (∑ m ∈ M.filter (fun m => m ≤ Nat.sqrt y), g m)
              * (CA * ((Z : ℝ) ^ (-cA)
                + Real.exp (-(L / (4 * lz))) * lz ^ 6) + 2 * C1 * hc * (1 + L) ^ 2) := by
            rw [Finset.sum_mul]
        _ ≤ (2 * C1 * lz) * (CA * ((Z : ℝ) ^ (-cA)
                + Real.exp (-(L / (4 * lz))) * lz ^ 6) + 2 * C1 * hc * (1 + L) ^ 2) := by
            apply mul_le_mul_of_nonneg_right hM1mass
            positivity
    -- the large smooth part
    have hM2b : |∑ m ∈ M.filter (fun m => ¬ m ≤ Nat.sqrt y),
        (ArithmeticFunction.moebius m : ℝ) * g m * Afun m|
        ≤ (2 * C1 * (1 + L)) * (CH * Real.exp (-(L / (4 * lz))) * lz ^ 8) := by
      have hpt2 : ∀ m ∈ M.filter (fun m => ¬ m ≤ Nat.sqrt y),
          |(ArithmeticFunction.moebius m : ℝ) * g m * Afun m| ≤ g m * (2 * C1 * (1 + L)) := by
        intro m _
        have hmu : |(ArithmeticFunction.moebius m : ℝ)| ≤ 1 := by
          rw [← Int.cast_abs]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
        have hbound : |Afun m| ≤ 2 * C1 * (1 + L) := by
          have heq : (∑ n ∈ (Finset.Icc 1 (y / m)).filter
                (fun n => Squarefree n ∧ Nat.Coprime n (primeZProd Z * ϱ)),
                (ArithmeticFunction.moebius n : ℝ) * g n)
              = Afun m := by rw [hAfundef]
          rw [← heq]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          have hnt : ∀ n ∈ (Finset.Icc 1 (y / m)).filter
                (fun n => Squarefree n ∧ Nat.Coprime n (primeZProd Z * ϱ)),
              |(ArithmeticFunction.moebius n : ℝ) * g n| ≤ g n := by
            intro n _
            have hmm : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
              rw [← Int.cast_abs]
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
            rw [abs_mul, abs_of_nonneg (hg0 n)]
            calc |(ArithmeticFunction.moebius n : ℝ)| * g n ≤ 1 * g n :=
                  mul_le_mul_of_nonneg_right hmm (hg0 n)
              _ = g n := by ring
          calc (∑ n ∈ (Finset.Icc 1 (y / m)).filter
                  (fun n => Squarefree n ∧ Nat.Coprime n (primeZProd Z * ϱ)),
                  |(ArithmeticFunction.moebius n : ℝ) * g n|)
              ≤ ∑ n ∈ (Finset.Icc 1 (y / m)).filter Squarefree, g n := by
                refine le_trans (Finset.sum_le_sum hnt) ?_
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hg0 n)
                intro n hn
                rw [Finset.mem_filter] at hn ⊢
                exact ⟨hn.1, hn.2.1⟩
            _ ≤ 2 * C1 * (1 + L) := by
                refine le_trans (hmass_lin (y / m)) ?_
                have h5 : Real.log (((y / m : ℕ) : ℝ) + 1) ≤ 1 + L := by
                  have h11 : ((y / m : ℕ) : ℝ) + 1 ≤ 2 * (y : ℝ) := by
                    have h12 : ((y / m : ℕ) : ℝ) ≤ (y : ℝ) := by
                      exact_mod_cast Nat.div_le_self y m
                    linarith
                  have h14 : Real.log (((y / m : ℕ) : ℝ) + 1) ≤ Real.log (2 * (y : ℝ)) :=
                    Real.log_le_log (by positivity) h11
                  rw [Real.log_mul (by norm_num) (by positivity), ← hLdef] at h14
                  linarith [Real.log_two_lt_d9]
                have h15 : (1 : ℝ) ≤ 1 + L := by linarith
                nlinarith [h5, h15, hC1nn, hLpos]
        rw [abs_mul, abs_mul, abs_of_nonneg (hg0 m)]
        calc |(ArithmeticFunction.moebius m : ℝ)| * g m * |Afun m|
            ≤ 1 * g m * (2 * C1 * (1 + L)) := by
              refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmu (hg0 m))
                (abs_nonneg _)) ?_
              exact mul_le_mul_of_nonneg_left hbound (mul_nonneg zero_le_one (hg0 m))
          _ = g m * (2 * C1 * (1 + L)) := by ring
      have hzeroterm : ∀ m ∈ M.filter (fun m => ¬ m ≤ Nat.sqrt y), y < m →
          |(ArithmeticFunction.moebius m : ℝ) * g m * Afun m| = 0 := by
        intro m _ hym
        have h0 : y / m = 0 := Nat.div_eq_of_lt hym
        have hA0 : Afun m = 0 := by
          rw [hAfundef]
          show (∑ n ∈ (Finset.Icc 1 (y / m)).filter
              (fun n => Squarefree n ∧ Nat.Coprime n (primeZProd Z * ϱ)),
              (ArithmeticFunction.moebius n : ℝ) * g n) = 0
          rw [h0]
          have : (Finset.Icc 1 (0:ℕ)) = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by norm_num)
          rw [this]; simp
        rw [hA0, mul_zero, abs_zero]
      have hsubset : (M.filter (fun m => ¬ m ≤ Nat.sqrt y)).filter (fun m => m ≤ y) ⊆
          (Nat.divisors (primeZProd Z)).filter (fun m => Nat.sqrt y < m ∧ m ≤ y) := by
        intro m hm
        rw [Finset.mem_filter, Finset.mem_filter] at hm
        obtain ⟨⟨hmM, hnotle⟩, hmley⟩ := hm
        rw [hMdef, Finset.mem_filter] at hmM
        exact Finset.mem_filter.mpr ⟨hmM.1, by omega, hmley⟩
      have hrestrict : (∑ m ∈ M.filter (fun m => ¬ m ≤ Nat.sqrt y),
            |(ArithmeticFunction.moebius m : ℝ) * g m * Afun m|)
          = ∑ m ∈ (M.filter (fun m => ¬ m ≤ Nat.sqrt y)).filter (fun m => m ≤ y),
            |(ArithmeticFunction.moebius m : ℝ) * g m * Afun m| := by
        refine (Finset.sum_subset
          (Finset.filter_subset (fun m => m ≤ y) (M.filter (fun m => ¬ m ≤ Nat.sqrt y))) ?_).symm
        intro m hm hnot
        have hym : y < m := by
          by_contra hc
          exact hnot (Finset.mem_filter.mpr ⟨hm, not_lt.mp hc⟩)
        exact hzeroterm m hm hym
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      calc (∑ m ∈ M.filter (fun m => ¬ m ≤ Nat.sqrt y),
              |(ArithmeticFunction.moebius m : ℝ) * g m * Afun m|)
          = ∑ m ∈ (M.filter (fun m => ¬ m ≤ Nat.sqrt y)).filter (fun m => m ≤ y),
              |(ArithmeticFunction.moebius m : ℝ) * g m * Afun m| := hrestrict
        _ ≤ ∑ m ∈ (M.filter (fun m => ¬ m ≤ Nat.sqrt y)).filter (fun m => m ≤ y),
              g m * (2 * C1 * (1 + L)) :=
            Finset.sum_le_sum fun m hm => hpt2 m (Finset.mem_filter.mp hm).1
        _ = (∑ m ∈ (M.filter (fun m => ¬ m ≤ Nat.sqrt y)).filter (fun m => m ≤ y), g m)
              * (2 * C1 * (1 + L)) := by rw [Finset.sum_mul]
        _ ≤ (CH * Real.exp (-(L / (4 * lz))) * lz ^ 8) * (2 * C1 * (1 + L)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => hg0 _)) ?_
            have hr := hrankin Z y hZ3 hy16
            have heq : CH * Real.exp (-(Real.log (y : ℝ) / (4 * Real.log (Z : ℝ))))
                  * (Real.log (Z : ℝ)) ^ 8 = CH * Real.exp (-(L / (4 * lz))) * lz ^ 8 := by
              rw [← hLdef, ← hlzdef]
            rw [heq] at hr
            exact hr
        _ = (2 * C1 * (1 + L)) * (CH * Real.exp (-(L / (4 * lz))) * lz ^ 8) := by ring
    -- the two halves are small
    have hM1fin : (2 * C1 * lz) * (CA * ((Z : ℝ) ^ (-cA)
          + Real.exp (-(L / (4 * lz))) * lz ^ 6) + 2 * C1 * hc * (1 + L) ^ 2)
        ≤ σ * L ^ (-6 : ℝ) / 2 := by
      have hE1 : 2 * C1 * lz * (CA * (Z : ℝ) ^ (-cA)) ≤ σ * L ^ (-6 : ℝ) / 6 := by
        have hzeq : (Z : ℝ) ^ (-cA) = Real.exp (-(cA * lz)) := by
          rw [Real.rpow_def_of_pos hZposR, ← hlzdef]
          congr 1
          ring
        rw [hzeq]
        have hlog8 : 6 * Real.log L + Real.log (12 * C1 * CA * lz) ≤ cA * lz := by
          have h1 : Real.log (3 * α * lz) ≤ cA * lz - 8 * Real.log L - 8 * Real.log lz := by
            linarith [hZc]
          have h2 : Real.log (12 * C1 * CA * lz) ≤ Real.log (3 * α * lz) := by
            apply Real.log_le_log (by positivity)
            nlinarith [hα1, hlzpos]
          have h6 : Real.log (3 * α * lz) = Real.log (3 * α) + Real.log lz :=
            Real.log_mul (by positivity) (by linarith)
          have h5 : Real.log (12 * C1 * CA * lz) = Real.log (12 * C1 * CA) + Real.log lz :=
            Real.log_mul (by positivity) (by linarith)
          linarith [hTnn, hWnn, h1, h2]
        have hexp : Real.exp (-(cA * lz)) ≤ L ^ (-6 : ℝ) / (12 * C1 * CA * lz) :=
          exp_neg_le_rpow_neg_six_div (by positivity) hLpos hlog8
        have hEq : 2 * C1 * lz * (CA * (L ^ (-6 : ℝ) / (12 * C1 * CA * lz)))
            = L ^ (-6 : ℝ) / 6 := by
          rw [div_eq_mul_inv]
          field_simp
          ring
        have hmono : 2 * C1 * lz * (CA * Real.exp (-(cA * lz)))
            ≤ 2 * C1 * lz * (CA * (L ^ (-6 : ℝ) / (12 * C1 * CA * lz))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hCAnn) (by positivity)
        rw [hEq] at hmono
        have h3 : 0 ≤ L ^ (-6 : ℝ) := Real.rpow_nonneg hLpos.le _
        nlinarith [hmono, hσ1, h3]
      have hE2 : 2 * C1 * lz * (CA * (Real.exp (-(L / (4 * lz))) * lz ^ 6))
          ≤ σ * L ^ (-6 : ℝ) / 6 := by
        have hlogA : 6 * Real.log L + Real.log (12 * C1 * CA * lz ^ 7) ≤ L / (4 * lz) := by
          have h7 : Real.log (12 * C1 * CA * lz ^ 7) ≤ Real.log (12 * C1 * CA) + 7 * Real.log lz := by
            rw [show (12 * C1 * CA * lz ^ 7) = (12 * C1 * CA) * lz ^ 7 by ring,
              Real.log_mul (by positivity) (by positivity), Real.log_pow]
            push_cast; linarith
          have h8 : Real.log (12 * C1 * CA) ≤ γ := by
            have h9 : Real.log (12 * C1 * CA) ≤ Real.log (16 * C1 * CA + 1) :=
              Real.log_le_log (by positivity) (by nlinarith [hC1, hCA])
            have h10 : Real.log (16 * C1 * CA + 1) ≤ γ := by
              rw [hγdef]
              linarith [le_max_left (Real.log (16 * C1 * CA + 1)) (Real.log (8 * C1 * CH + 1))]
            linarith [h10, h9]
          linarith [hZγ, h7, h8, hTnn, hWnn]
        have hexp : Real.exp (-(L / (4 * lz))) ≤ L ^ (-6 : ℝ) / (12 * C1 * CA * lz ^ 7) :=
          exp_neg_le_rpow_neg_six_div (by positivity) hLpos hlogA
        have hEq : 2 * C1 * lz * (CA * ((L ^ (-6 : ℝ) / (12 * C1 * CA * lz ^ 7)) * lz ^ 6))
            = L ^ (-6 : ℝ) / 6 := by
          rw [div_eq_mul_inv]
          field_simp
          ring
        have hmono : 2 * C1 * lz * (CA * (Real.exp (-(L / (4 * lz))) * lz ^ 6))
            ≤ 2 * C1 * lz * (CA * ((L ^ (-6 : ℝ) / (12 * C1 * CA * lz ^ 7)) * lz ^ 6)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hexp (by positivity)) hCAnn) (by positivity)
        rw [hEq] at hmono
        have h3 : 0 ≤ L ^ (-6 : ℝ) := Real.rpow_nonneg hLpos.le _
        nlinarith [hmono, hσ1, h3]
      have hE3 : 2 * C1 * lz * (2 * C1 * hc * (1 + L) ^ 2) ≤ σ * L ^ (-6 : ℝ) / 6 := by
        rw [hhcdef, rpow_neg_ten lz hlzpos]
        have hCab1 : 0 ≤ Cgap + Cg + 1 := by linarith [hCgapnn, hCgnn]
        have h9 : 24 * C1 ^ 2 * (Cgap + Cg + 1) * (1 + L) ^ 2 * L ^ 6 ≤ lz ^ 9 := by
          have h1 : (1 + L) ^ 2 ≤ 4 * L ^ 2 := by nlinarith [hL1]
          have h2 : 24 * C1 ^ 2 * (Cgap + Cg + 1) * (1 + L) ^ 2 * L ^ 6
              ≤ 24 * C1 ^ 2 * (Cgap + Cg + 1) * (4 * L ^ 2) * L ^ 6 := by
            have h0 : 0 ≤ 24 * C1 ^ 2 * (Cgap + Cg + 1) * L ^ 6 := by positivity
            have h2a := mul_le_mul_of_nonneg_left h1 h0
            nlinarith [h2a]
          have h3 : 24 * C1 ^ 2 * (Cgap + Cg + 1) * (4 * L ^ 2) * L ^ 6
              = 96 * C1 ^ 2 * (Cgap + Cg + 1) * L ^ 8 := by ring
          have h4 : 96 * C1 ^ 2 * (Cgap + Cg + 1) ≤ 64 * C1 * E * (Cgap + Cg + 1) := by
            rw [hEdef]
            have h0 : 0 ≤ Cgap + Cg + 1 := hCab1
            nlinarith [hC1nn, h0]
          have h5 : 96 * C1 ^ 2 * (Cgap + Cg + 1) * L ^ 8 ≤ 3 * α * L ^ 8 := by
            have h6 := hα2
            have hL8 : 0 ≤ L ^ 8 := by positivity
            nlinarith [h6, h4, hL8]
          linarith [h2, h3, h5, hZα]
        have h10 : (lz ^ 9)⁻¹
            ≤ (24 * C1 ^ 2 * (Cgap + Cg + 1) * (1 + L) ^ 2 * L ^ 6)⁻¹ :=
          (inv_le_inv₀ (by positivity) (by positivity)).mpr h9
        have h12 : 2 * C1 * lz * (2 * C1 * ((Cgap + Cg + 1) * σ * (1 / lz ^ 10)) * (1 + L) ^ 2)
            = (4 * C1 ^ 2 * (Cgap + Cg + 1) * (1 + L) ^ 2 * (lz ^ 9)⁻¹) * σ := by
          have hlz9 : lz * (1 / lz ^ 10) = (lz ^ 9)⁻¹ := by
            rw [one_div, show (lz ^ 10) = lz * lz ^ 9 by ring, mul_inv, ← mul_assoc,
              mul_inv_cancel₀ (by positivity : lz ≠ 0), one_mul]
          rw [← hlz9]
          ring
        rw [h12]
        have h13 : 4 * C1 ^ 2 * (Cgap + Cg + 1) * (1 + L) ^ 2 * (lz ^ 9)⁻¹
            ≤ 1 / (6 * L ^ 6) := by
          have h14 : 4 * C1 ^ 2 * (Cgap + Cg + 1) * (1 + L) ^ 2 * (lz ^ 9)⁻¹
              ≤ 4 * C1 ^ 2 * (Cgap + Cg + 1) * (1 + L) ^ 2
                * (24 * C1 ^ 2 * (Cgap + Cg + 1) * (1 + L) ^ 2 * L ^ 6)⁻¹ :=
            mul_le_mul_of_nonneg_left h10 (by positivity)
          have h15 : 4 * C1 ^ 2 * (Cgap + Cg + 1) * (1 + L) ^ 2
                * (24 * C1 ^ 2 * (Cgap + Cg + 1) * (1 + L) ^ 2 * L ^ 6)⁻¹
              = 1 / (6 * L ^ 6) := by
            rw [mul_inv, div_eq_mul_inv]
            field_simp
            ring
          rw [h15] at h14
          exact h14
        calc (4 * C1 ^ 2 * (Cgap + Cg + 1) * (1 + L) ^ 2 * (lz ^ 9)⁻¹) * σ
            ≤ (1 / (6 * L ^ 6)) * σ := mul_le_mul_of_nonneg_right h13 hσpos.le
          _ = σ * L ^ (-6 : ℝ) / 6 := by
              rw [show L ^ (-6 : ℝ) = 1 / L ^ 6 from rpow_neg_six L hLpos]
              ring
      calc (2 * C1 * lz) * (CA * ((Z : ℝ) ^ (-cA)
              + Real.exp (-(L / (4 * lz))) * lz ^ 6) + 2 * C1 * hc * (1 + L) ^ 2)
          = 2 * C1 * lz * (CA * (Z : ℝ) ^ (-cA))
            + 2 * C1 * lz * (CA * (Real.exp (-(L / (4 * lz))) * lz ^ 6))
            + 2 * C1 * lz * (2 * C1 * hc * (1 + L) ^ 2) := by ring
        _ ≤ σ * L ^ (-6 : ℝ) / 6 + σ * L ^ (-6 : ℝ) / 6 + σ * L ^ (-6 : ℝ) / 6 :=
            add_le_add (add_le_add hE1 hE2) hE3
        _ ≤ σ * L ^ (-6 : ℝ) / 2 := by
            have h3 : 0 ≤ σ * L ^ (-6 : ℝ) := by positivity
            linarith
    have hM2fin : (2 * C1 * (1 + L)) * (CH * Real.exp (-(L / (4 * lz))) * lz ^ 8)
        ≤ σ * L ^ (-6 : ℝ) / 2 := by
      have hE4 : (2 * C1 * (1 + L)) * (CH * Real.exp (-(L / (4 * lz))) * lz ^ 8)
          ≤ σ * L ^ (-6 : ℝ) / 6 := by
        have hmono : 2 * C1 * (1 + L) ≤ 4 * C1 * L := by nlinarith [hC1nn, hL1]
        have hlogA : 6 * Real.log L + Real.log (24 * C1 * CH * L * lz ^ 8) ≤ L / (4 * lz) := by
          have h7 : Real.log (24 * C1 * CH * L * lz ^ 8)
              = Real.log (24 * C1 * CH) + Real.log L + 8 * Real.log lz := by
            rw [show (24 * C1 * CH * L * lz ^ 8) = (24 * C1 * CH) * L * lz ^ 8 by ring,
              Real.log_mul (by positivity) (by positivity),
              Real.log_mul (by positivity) (by positivity), Real.log_pow]
            push_cast; ring
          have h8 : Real.log (24 * C1 * CH) ≤ γ := by
            have h9 : Real.log (24 * C1 * CH) ≤ Real.log (32 * C1 * CH) :=
              Real.log_le_log (by positivity) (by nlinarith [hC1, hCH])
            linarith [hγ3, h9]
          linarith [hZγ, h7, h8, hTnn, hWnn]
        have hexp : Real.exp (-(L / (4 * lz))) ≤ L ^ (-6 : ℝ) / (24 * C1 * CH * L * lz ^ 8) :=
          exp_neg_le_rpow_neg_six_div (by positivity) hLpos hlogA
        have hstep : (2 * C1 * (1 + L)) * (CH * Real.exp (-(L / (4 * lz))) * lz ^ 8)
            ≤ (2 * C1 * (1 + L))
              * (CH * ((L ^ (-6 : ℝ) / (24 * C1 * CH * L * lz ^ 8)) * lz ^ 8)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hA : 0 < 24 * C1 * CH * L * lz ^ 8 := by positivity
          have hB : 0 < L ^ 6 := by positivity
          have h1 : Real.exp (-(L / (4 * lz))) ≤ L ^ (-6 : ℝ) / (24 * C1 * CH * L * lz ^ 8) := hexp
          have h2 : Real.exp (-(L / (4 * lz))) * lz ^ 8
              ≤ (L ^ (-6 : ℝ) / (24 * C1 * CH * L * lz ^ 8)) * lz ^ 8 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
          have h3 : CH * (Real.exp (-(L / (4 * lz))) * lz ^ 8)
              ≤ CH * ((L ^ (-6 : ℝ) / (24 * C1 * CH * L * lz ^ 8)) * lz ^ 8) :=
            mul_le_mul_of_nonneg_left h2 (le_of_lt hCH)
          calc CH * Real.exp (-(L / (4 * lz))) * lz ^ 8
              = CH * (Real.exp (-(L / (4 * lz))) * lz ^ 8) := by ring
            _ ≤ CH * ((L ^ (-6 : ℝ) / (24 * C1 * CH * L * lz ^ 8)) * lz ^ 8) := h3
        refine le_trans hstep ?_
        have hmm : (2 * C1 * (1 + L))
              * (CH * ((L ^ (-6 : ℝ) / (24 * C1 * CH * L * lz ^ 8)) * lz ^ 8))
            ≤ (4 * C1 * L)
              * (CH * ((L ^ (-6 : ℝ) / (24 * C1 * CH * L * lz ^ 8)) * lz ^ 8)) :=
          mul_le_mul_of_nonneg_right hmono (by positivity)
        refine le_trans hmm ?_
        have hEq2 : (4 * C1 * L)
              * (CH * ((L ^ (-6 : ℝ) / (24 * C1 * CH * L * lz ^ 8)) * lz ^ 8))
            = L ^ (-6 : ℝ) / 6 := by
          rw [div_eq_mul_inv]
          field_simp
          ring
        rw [hEq2]
        have h3 : 0 ≤ L ^ (-6 : ℝ) := Real.rpow_nonneg hLpos.le _
        nlinarith [hσ1, h3]
      have h3 : 0 ≤ σ * L ^ (-6 : ℝ) := by positivity
      linarith
    rw [hG]
    have htri : abs (∑ m ∈ M, (ArithmeticFunction.moebius m : ℝ) * g m * Afun m)
        ≤ abs (∑ m ∈ M.filter (fun m => m ≤ Nat.sqrt y),
              (ArithmeticFunction.moebius m : ℝ) * g m * Afun m)
          + abs (∑ m ∈ M.filter (fun m => ¬ m ≤ Nat.sqrt y),
              (ArithmeticFunction.moebius m : ℝ) * g m * Afun m) := by
      have h2 := abs_add_le
        (∑ m ∈ M.filter (fun m => m ≤ Nat.sqrt y),
          (ArithmeticFunction.moebius m : ℝ) * g m * Afun m)
        (∑ m ∈ M.filter (fun m => ¬ m ≤ Nat.sqrt y),
          (ArithmeticFunction.moebius m : ℝ) * g m * Afun m)
      rwa [hsplit] at h2
    refine le_trans htri ?_
    refine le_trans (add_le_add (le_trans hM1b hM1fin) (le_trans hM2b hM2fin)) ?_
    have hfin : σ * L ^ (-6 : ℝ) / 2 + σ * L ^ (-6 : ℝ) / 2 = σ * L ^ (-6 : ℝ) := by ring
    rw [hfin]
    rw [show L ^ (-6 : ℝ) = (Real.log (y : ℝ)) ^ (-6 : ℝ) by rw [← hLdef]]
    have hfin2 : σ * (Real.log (y : ℝ)) ^ (-6 : ℝ)
        ≤ max Csmall 1 * σ * (Real.log (y : ℝ)) ^ (-6 : ℝ) := by
      have h1 : (1 : ℝ) ≤ max Csmall 1 := le_max_right _ _
      have h2 : 0 ≤ (Real.log (y : ℝ)) ^ (-6 : ℝ) := Real.rpow_nonneg hLpos.le _
      have h3 : 0 ≤ max Csmall 1 - 1 := by linarith
      nlinarith [mul_nonneg h3 hσpos.le, h2]
    exact hfin2

end

end Commons.NumberTheory.Sieve
