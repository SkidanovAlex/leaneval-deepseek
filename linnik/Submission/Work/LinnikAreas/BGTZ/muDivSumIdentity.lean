/-
# The Möbius divisor-sum identity of the BGTZ reindexing

`muDivSumIdentity` is the arithmetic identity consumed by `Work.LinnikAreas.BGTZ.moebius_reindex`
(the Selberg-sieve reindexing of the BGTZ detector): for squarefree `k`, `Q0` with `k` coprime to
`Q0` and `1 ≤ k`,

`∑_{d | n, k | d, (d,Q0) = 1, d ⊥ n/d, Squarefree (n/d)} μ(d) = [k | n ∧ (n/k) | Q0] · μ(k)`.

It was the only `sorry` of the BGTZ chapter (via `SieveWeights` it made the whole detector
assembly depend on `sorryAx`); see `NOTES_workspace_blockers.md` §4.

Proof.  If `n` is not squarefree every summand has `μ(d) = 0` (a squarefree `d` with coprime
squarefree complement `n/d` would make `n` squarefree), and then `n/k ∤ Q0` as well: `n = k·(n/k)`
with `k ⊥ Q0` and `(n/k) | Q0` would force `k ⊥ n/k` and `n` squarefree.  If `n` is squarefree,
the conditions `d ⊥ n/d` and `Squarefree (n/d)` are automatic for `d | n`
(`coprime_div_of_squarefree`), so the filter collapses to `k | d ∧ (d,Q0) = 1`; for `k | n` the
substitution `d = k·e` (`e | n/k`) gives `∑_{e | n/k} μ(k·e)[(k·e,Q0) = 1]`, and `k ⊥ e`,
`μ(k·e) = μ(k)μ(e)` turn this into `μ(k)·∑_{e | n/k, (e,Q0)=1} μ(e) = μ(k)·[n/k | Q0]`
(`sum_muR_divisors_coprime_of_squarefree`). -/
import Mathlib
import Submission.Work.LinnikAreas.BGTZ.MuRBasic

open Finset
namespace Work.LinnikAreas.BGTZ

private lemma coprime_div_of_squarefree {d n : ℕ} (hsq : Squarefree n) (hd : d ∣ n) :
    Nat.Coprime d (n / d) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd h
  have hpd : p ∣ d := dvd_trans hpg (Nat.gcd_dvd_left d (n / d))
  have hpn : p ∣ n / d := dvd_trans hpg (Nat.gcd_dvd_right d (n / d))
  have hpp : p * p ∣ n := by
    have h1 : p * p ∣ d * (n / d) := mul_dvd_mul hpd hpn
    rwa [Nat.mul_div_cancel' hd] at h1
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) hpp

private lemma coprime_of_squarefree_mul {a b : ℕ} (h : Squarefree (a * b)) : Nat.Coprime a b := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpa : p ∣ a := dvd_trans hpg (Nat.gcd_dvd_left a b)
  have hpb : p ∣ b := dvd_trans hpg (Nat.gcd_dvd_right a b)
  exact (Nat.squarefree_iff_prime_squarefree.mp h p hp) (mul_dvd_mul hpa hpb)

private lemma sum_muR_divisors_eq_ite (n : ℕ) :
    (∑ d ∈ n.divisors, muR d) = if n = 1 then 1 else 0 := by
  have hZ : (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = if n = 1 then (1 : ℤ) else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply (f := ArithmeticFunction.moebius) (x := n),
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  have h := congrArg (fun z : ℤ => (z : ℝ)) hZ
  push_cast at h
  simpa only [muR] using h

private lemma sum_muR_divisors_coprime_of_squarefree (m Q0 : ℕ) (hm : Squarefree m) :
    (∑ e ∈ m.divisors.filter (fun e => Nat.Coprime e Q0), muR e)
      = if m ∣ Q0 then 1 else 0 := by
  have hm0 : m ≠ 0 := hm.ne_zero
  rcases eq_or_ne Q0 0 with hQ0 | hQ0
  · subst hQ0
    have hset : m.divisors.filter (fun e => Nat.Coprime e 0) = {1} := by
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton, Nat.Coprime,
        Nat.gcd_zero_right]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro rfl; exact ⟨⟨one_dvd m, hm0⟩, rfl⟩
    rw [hset, Finset.sum_singleton, muR_one, if_pos (dvd_zero m)]
  · set S : Finset ℕ := m.primeFactors.filter (fun p => ¬ p ∣ Q0) with hS
    set m' : ℕ := ∏ p ∈ S, p with hm'
    have hSprime : ∀ p ∈ S, Nat.Prime p := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    have hm'pf : m'.primeFactors = S := by rw [hm']; exact Nat.primeFactors_prod hSprime
    have hm'pos : 0 < m' := by
      rw [hm']; exact Finset.prod_pos (fun p hp => (hSprime p hp).pos)
    have hm'ne : m' ≠ 0 := hm'pos.ne'
    have hm'dvd : m' ∣ m := by
      rw [hm']
      exact dvd_trans (Finset.prod_dvd_prod_of_subset S m.primeFactors (fun p => p)
        (Finset.filter_subset _ _)) (Nat.prod_primeFactors_dvd m)
    have hm'cop : Nat.Coprime m' Q0 := by
      rw [hm']
      exact Nat.Coprime.prod_left (fun p hp =>
        (Nat.Prime.coprime_iff_not_dvd (hSprime p hp)).mpr (Finset.mem_filter.mp hp).2)
    have hfilter : m.divisors.filter (fun e => Nat.Coprime e Q0) = m'.divisors := by
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hem, _⟩, hcop⟩
        refine ⟨?_, hm'ne⟩
        have hesq : Squarefree e := Squarefree.squarefree_of_dvd hem hm
        have hsub : e.primeFactors ⊆ S := by
          intro p hp
          rw [Finset.mem_filter]
          have hpprime : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
          have hpe : p ∣ e := (Nat.mem_primeFactors.mp hp).2.1
          refine ⟨Nat.mem_primeFactors.mpr ⟨hpprime, dvd_trans hpe hem, hm0⟩, ?_⟩
          intro hpQ
          have hpg : p ∣ e.gcd Q0 := Nat.dvd_gcd hpe hpQ
          rw [hcop] at hpg
          exact hpprime.ne_one (Nat.dvd_one.mp hpg)
        calc e = ∏ p ∈ e.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hesq).symm
          _ ∣ ∏ p ∈ S, p := Finset.prod_dvd_prod_of_subset e.primeFactors S (fun p => p) hsub
          _ = m' := hm'.symm
      · rintro ⟨hem', _⟩
        exact ⟨⟨dvd_trans hem' hm'dvd, hm0⟩, Nat.Coprime.coprime_dvd_left hem' hm'cop⟩
    rw [hfilter, sum_muR_divisors_eq_ite]
    have hiff : m' = 1 ↔ m ∣ Q0 := by
      constructor
      · intro h1
        have hSempty : S = ∅ := by
          rw [← hm'pf, h1]; simp
        have hall : ∀ p ∈ m.primeFactors, p ∣ Q0 := by
          intro p hp
          by_contra hpQ
          exact Finset.notMem_empty p (hSempty ▸ (Finset.mem_filter.mpr ⟨hp, hpQ⟩))
        refine (Nat.factorization_le_iff_dvd hm0 hQ0).mp ?_
        rw [Finsupp.le_def]
        intro p
        by_cases hpprime : Nat.Prime p
        · by_cases hfac : m.factorization p = 0
          · rw [hfac]; exact Nat.zero_le _
          · have hpm : p ∣ m := Nat.dvd_of_factorization_pos hfac
            have hpQ : p ∣ Q0 := hall p (Nat.mem_primeFactors.mpr ⟨hpprime, hpm, hm0⟩)
            have h1 : 1 ≤ Q0.factorization p :=
              (Nat.Prime.dvd_iff_one_le_factorization hpprime hQ0).mp hpQ
            have h2 : m.factorization p ≤ 1 :=
              (Nat.squarefree_iff_factorization_le_one hm0).mp hm p
            omega
        · rw [Nat.factorization_eq_zero_of_not_prime m hpprime]; exact Nat.zero_le _
      · intro hdvd
        have hall : ∀ p ∈ m.primeFactors, p ∣ Q0 := fun p hp =>
          (Nat.mem_primeFactors.mp (Nat.primeFactors_mono hdvd hQ0 hp)).2.1
        have hSempty : S = ∅ := by
          rw [← Finset.not_nonempty_iff_eq_empty]
          rintro ⟨p, hp⟩
          exact (Finset.mem_filter.mp hp).2 (hall p (Finset.mem_filter.mp hp).1)
        rw [hm', hSempty, Finset.prod_empty]
    by_cases h : m ∣ Q0
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]


theorem muDivSumIdentity (k Q0 n : ℕ) (hk : Squarefree k) (hk1 : 1 ≤ k)
    (hkQ0 : Nat.Coprime k Q0) (hQ0 : Squarefree Q0) :
    (∑ d ∈ n.divisors.filter (fun d => k ∣ d ∧ Nat.Coprime d Q0 ∧
        Nat.Coprime d (n / d) ∧ Squarefree (n / d)), muR d)
      = if (k ∣ n ∧ n / k ∣ Q0) then muR k else 0 := by
  have hk0 : k ≠ 0 := by omega
  rcases eq_or_ne n 0 with hn0 | hn0
  · subst hn0
    rw [Nat.divisors_zero, Finset.filter_empty, Finset.sum_empty]
    refine (if_neg ?_).symm
    rintro ⟨-, hQ⟩
    rw [Nat.zero_div] at hQ
    exact hQ0.ne_zero (Nat.eq_zero_of_zero_dvd hQ)
  by_cases hsfn : Squarefree n
  · by_cases hkn : k ∣ n
    · have hnm : n / k ≠ 0 := by
        rw [Nat.div_ne_zero_iff]
        exact ⟨hk0, Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hkn⟩
      have hmsq : Squarefree (n / k) :=
        Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hkn) hsfn
      have hkm : Nat.Coprime k (n / k) := by
        refine coprime_of_squarefree_mul ?_
        rw [Nat.mul_div_cancel' hkn]
        exact hsfn
      have hfilt : n.divisors.filter (fun d => k ∣ d ∧ Nat.Coprime d Q0 ∧
            Nat.Coprime d (n / d) ∧ Squarefree (n / d))
          = n.divisors.filter (fun d => k ∣ d ∧ Nat.Coprime d Q0) := by
        refine Finset.filter_congr (fun d hd => ?_)
        rw [Nat.mem_divisors] at hd
        constructor
        · rintro ⟨h1, h2, -, -⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2, coprime_div_of_squarefree hsfn hd.1,
            Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hd.1) hsfn⟩
      rw [hfilt]
      have himg : n.divisors.filter (fun d => k ∣ d) = (n / k).divisors.image (fun e => k * e) := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hdn, -⟩, hkd⟩
          refine ⟨d / k, ⟨⟨?_, hnm⟩, Nat.mul_div_cancel' hkd⟩⟩
          rw [Nat.dvd_div_iff_mul_dvd hkn, Nat.mul_div_cancel' hkd]
          exact hdn
        · rintro ⟨e, ⟨⟨hed, -⟩, rfl⟩⟩
          exact ⟨⟨by rwa [← Nat.dvd_div_iff_mul_dvd hkn], hn0⟩, dvd_mul_right k e⟩
      rw [show n.divisors.filter (fun d => k ∣ d ∧ Nat.Coprime d Q0)
            = (n.divisors.filter (fun d => k ∣ d)).filter (fun d => Nat.Coprime d Q0) from
          (Finset.filter_filter (p := fun d => k ∣ d) (q := fun d => Nat.Coprime d Q0) n.divisors).symm]
      rw [Finset.sum_filter]
      rw [himg, Finset.sum_image (by
        intro a _ b _ hab
        exact Nat.mul_left_cancel (by omega : 0 < k) hab)]
      have hstep : (∑ e ∈ (n / k).divisors,
            (if Nat.Coprime (k * e) Q0 then muR (k * e) else 0))
          = muR k * (∑ e ∈ (n / k).divisors.filter (fun e => Nat.Coprime e Q0), muR e) := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun e he => ?_)
        rw [Nat.mem_divisors] at he
        have hek : Nat.Coprime k e := Nat.Coprime.coprime_dvd_right he.1 hkm
        by_cases hce : Nat.Coprime e Q0
        · have hcke : Nat.Coprime (k * e) Q0 := Nat.Coprime.mul_left hkQ0 hce
          rw [if_pos hcke, if_pos hce, muR_mul hek]
        · have hcke : ¬ Nat.Coprime (k * e) Q0 := fun h => hce (Nat.coprime_mul_iff_left.mp h).2
          rw [if_neg hcke, if_neg hce, mul_zero]
      rw [hstep, sum_muR_divisors_coprime_of_squarefree (n / k) Q0 hmsq]
      by_cases hQ : n / k ∣ Q0
      · rw [if_pos hQ, mul_one, if_pos ⟨hkn, hQ⟩]
      · rw [if_neg hQ, mul_zero, if_neg (fun h => hQ h.2)]
    · rw [if_neg (fun h => hkn h.1)]
      refine Finset.sum_eq_zero (fun d hd => ?_)
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      exact absurd (dvd_trans hd.2.1 hd.1.1) hkn
  · rw [if_neg ?_]
    · refine Finset.sum_eq_zero (fun d hd => ?_)
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdn, -⟩, hkd, hcopQ, hcopd, hsfe⟩ := hd
      refine muR_eq_zero_of_not_squarefree (fun hsfd => hsfn ?_)
      rw [← Nat.mul_div_cancel' hdn]
      exact (Nat.squarefree_mul hcopd).2 ⟨hsfd, hsfe⟩
    · rintro ⟨hkn', hmQ⟩
      have hkm' : Nat.Coprime k (n / k) := Nat.Coprime.coprime_dvd_right hmQ hkQ0
      have hsq' : Squarefree (n / k) := Squarefree.squarefree_of_dvd hmQ hQ0
      refine hsfn ?_
      have h := (Nat.squarefree_mul hkm').2 ⟨hk, hsq'⟩
      rwa [Nat.mul_div_cancel' hkn'] at h

end Work.LinnikAreas.BGTZ
