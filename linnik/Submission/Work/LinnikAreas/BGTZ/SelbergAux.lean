import Mathlib
import Submission.Work.LinnikAreas.Sieve.Defs
import Submission.Work.Sieve.aFun_basics
import Submission.Work.Sieve.gFun_theory
import Submission.Work.Sieve.hFun_squarefree
import Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors

open scoped BigOperators
open DirichletCharacter

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
lemma hFun_eq_finsupp (χ₁ : DirichletCharacter ℂ q) (n : ℕ) :
    Work.LinnikAreas.Sieve.hFun χ₁ n
      = n.factorization.prod (fun p e => Work.LinnikAreas.Sieve.hPrime χ₁ p ^ e) := by
  simp only [Work.LinnikAreas.Sieve.hFun, Finsupp.prod, Nat.support_factorization]

lemma hFun_mul (χ₁ : DirichletCharacter ℂ q) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    Work.LinnikAreas.Sieve.hFun χ₁ (m * n)
      = Work.LinnikAreas.Sieve.hFun χ₁ m * Work.LinnikAreas.Sieve.hFun χ₁ n := by
  rw [hFun_eq_finsupp, hFun_eq_finsupp, hFun_eq_finsupp, Nat.factorization_mul hm hn]
  rw [Finsupp.prod_add_index (f := m.factorization) (g := n.factorization)
        (h := fun p e => Work.LinnikAreas.Sieve.hPrime χ₁ p ^ e)
        (by intro a ha; rw [pow_zero])
        (by intro a ha b1 b2; rw [pow_add])]

lemma hFun_pos (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) (n : ℕ) :
    0 < Work.LinnikAreas.Sieve.hFun χ₁ n := by
  rw [Work.LinnikAreas.Sieve.hFun]
  refine Finset.prod_pos (fun p hp => ?_)
  have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hg : 0 < Work.LinnikAreas.Sieve.gPrime χ₁ p := (Work.Sieve.gFun_theory χ₁ hreal).2.1 p hp'
  exact pow_pos (by rw [Work.LinnikAreas.Sieve.hPrime]; linarith) _

lemma hPrime_gt_one (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) (p : ℕ) (hp : p.Prime) :
    1 < Work.LinnikAreas.Sieve.hPrime χ₁ p := by
  have hg : 0 < Work.LinnikAreas.Sieve.gPrime χ₁ p := (Work.Sieve.gFun_theory χ₁ hreal).2.1 p hp
  rw [Work.LinnikAreas.Sieve.hPrime]; linarith

lemma gFun_pos (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) (n : ℕ) (hn : n ≠ 0) :
    0 < Work.LinnikAreas.Sieve.gFun χ₁ n := by
  rw [Work.LinnikAreas.Sieve.gFun]
  refine mul_pos (hFun_pos χ₁ hreal n) (Finset.prod_pos (fun p hp => ?_))
  have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have h := hPrime_gt_one χ₁ hreal p hp'
  have hpos : 0 < Work.LinnikAreas.Sieve.hPrime χ₁ p := lt_trans zero_lt_one h
  rw [sub_pos, inv_lt_one₀ hpos]
  exact h

lemma gFun_mul (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) (hcop : Nat.Coprime m n) :
    Work.LinnikAreas.Sieve.gFun χ₁ (m * n)
      = Work.LinnikAreas.Sieve.gFun χ₁ m * Work.LinnikAreas.Sieve.gFun χ₁ n := by
  rw [Work.LinnikAreas.Sieve.gFun, Work.LinnikAreas.Sieve.gFun, Work.LinnikAreas.Sieve.gFun,
      hFun_mul χ₁ hm hn, Nat.Coprime.primeFactors_mul hcop,
      Finset.prod_union hcop.disjoint_primeFactors]
  ring

lemma hFun_lcm_mul_gcd (χ₁ : DirichletCharacter ℂ q) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    Work.LinnikAreas.Sieve.hFun χ₁ (Nat.lcm d e) * Work.LinnikAreas.Sieve.hFun χ₁ (Nat.gcd d e)
      = Work.LinnikAreas.Sieve.hFun χ₁ d * Work.LinnikAreas.Sieve.hFun χ₁ e := by
  have hg : Nat.gcd d e ≠ 0 := fun h => he (Nat.gcd_eq_zero_iff.mp h).2
  have hl : Nat.lcm d e ≠ 0 := fun h => by
    rcases Nat.lcm_eq_zero_iff.mp h with h1 | h1
    · exact hd h1
    · exact he h1
  calc Work.LinnikAreas.Sieve.hFun χ₁ (Nat.lcm d e) * Work.LinnikAreas.Sieve.hFun χ₁ (Nat.gcd d e)
      = Work.LinnikAreas.Sieve.hFun χ₁ (Nat.lcm d e * Nat.gcd d e) :=
        (hFun_mul χ₁ hl hg).symm
    _ = Work.LinnikAreas.Sieve.hFun χ₁ (d * e) := by
        rw [mul_comm (Nat.lcm d e) (Nat.gcd d e), Nat.gcd_mul_lcm]
    _ = Work.LinnikAreas.Sieve.hFun χ₁ d * Work.LinnikAreas.Sieve.hFun χ₁ e :=
        hFun_mul χ₁ hd he

omit [NeZero q] in
lemma thetaFun_eq_zero_of_not_squarefree (χ₁ : DirichletCharacter ℂ q) (R d : ℕ)
    (hd : ¬ Squarefree d) : Work.LinnikAreas.Sieve.thetaFun χ₁ R d = 0 := by
  rw [Work.LinnikAreas.Sieve.thetaFun, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
  norm_num

omit [NeZero q] in
lemma thetaFun_eq_zero_of_gt (χ₁ : DirichletCharacter ℂ q) {R d : ℕ} (hd : R < d) :
    Work.LinnikAreas.Sieve.thetaFun χ₁ R d = 0 := by
  have h0 : R / d = 0 := Nat.div_eq_of_lt hd
  rw [Work.LinnikAreas.Sieve.thetaFun, h0]
  simp

lemma thetaFun_one (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) {R : ℕ} (hR : 1 ≤ R) :
    Work.LinnikAreas.Sieve.thetaFun χ₁ R 1 = 1 := by
  have hV : Work.LinnikAreas.Sieve.VFun χ₁ R ≠ 0 :=
    ne_of_gt ((Work.Sieve.gFun_theory χ₁ hreal).2.2.2.2.2.2 R hR)
  have hsum : (∑ r ∈ (Finset.Icc 1 (R / 1)).filter (fun r => Nat.Coprime r 1),
      (if Squarefree r then (1 : ℝ) else 0) / Work.LinnikAreas.Sieve.gFun χ₁ r)
      = Work.LinnikAreas.Sieve.VFun χ₁ R := by
    rw [Work.LinnikAreas.Sieve.VFun, Nat.div_one]
    refine Finset.sum_congr ?_ (fun r _ => rfl)
    ext r; simp
  rw [Work.LinnikAreas.Sieve.thetaFun, hsum]
  have h2 : Work.LinnikAreas.Sieve.hFun χ₁ 1 = 1 := by
    rw [Work.LinnikAreas.Sieve.hFun, Nat.primeFactors_one, Finset.prod_empty]
  have h3 : Work.LinnikAreas.Sieve.gFun χ₁ 1 = 1 := by
    rw [Work.LinnikAreas.Sieve.gFun, h2, Nat.primeFactors_one, Finset.prod_empty, mul_one]
  rw [ArithmeticFunction.moebius_apply_one, h2, h3]
  push_cast
  rw [one_mul, mul_one, one_div, inv_mul_cancel₀ hV]

lemma hFun_eq_sum_gFun_of_squarefree (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    {n : ℕ} (hn : Squarefree n) :
    Work.LinnikAreas.Sieve.hFun χ₁ n
      = ∑ d ∈ n.divisors, Work.LinnikAreas.Sieve.gFun χ₁ d := by
  obtain ⟨-, -, hhsf, hgsf, -, hgmul, -⟩ := Work.Sieve.gFun_theory χ₁ hreal
  set f : ℕ → ℝ := fun d => if Squarefree d then Work.LinnikAreas.Sieve.gFun χ₁ d else 0 with hf
  have hf1 : f 1 = 1 := by
    simp [hf, Work.LinnikAreas.Sieve.gFun, Work.LinnikAreas.Sieve.hFun]
  have hfm : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b := by
    intro a b hab
    by_cases ha : Squarefree a
    · by_cases hb : Squarefree b
      · have hab' : Squarefree (a * b) := (Nat.squarefree_mul hab).mpr ⟨ha, hb⟩
        simp only [hf, hab', ha, hb, if_true]
        exact hgmul a b ha hb hab
      · have hab' : ¬ Squarefree (a * b) := fun h => hb ((Nat.squarefree_mul hab).mp h).2
        simp [hf, ha, hb, hab']
    · have hab' : ¬ Squarefree (a * b) := fun h => ha ((Nat.squarefree_mul hab).mp h).1
      simp [hf, ha, hab']
  have hfs : ∀ p k : ℕ, p.Prime → 2 ≤ k → f (p ^ k) = 0 := by
    intro p k hp hk
    have hns : ¬ Squarefree (p ^ k) := by
      rw [Nat.squarefree_iff_prime_squarefree]
      push Not
      exact ⟨p, hp, by rw [← pow_two]; exact pow_dvd_pow p hk⟩
    simp [hf, hns]
  have hkey := Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
    f n hn.ne_zero hf1 hfm hfs
  have hdiv : ∀ d ∈ n.divisors, f d = Work.LinnikAreas.Sieve.gFun χ₁ d := by
    intro d hd
    have hsd : Squarefree d := hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    simp [hf, hsd]
  have hL : (∏ p ∈ n.primeFactors, Work.LinnikAreas.Sieve.hPrime χ₁ p)
      = ∏ p ∈ n.primeFactors, (1 + f p) := by
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hfp : f p = Work.LinnikAreas.Sieve.gPrime χ₁ p := by
      simp only [hf, hpp.squarefree, if_true]
      rw [hgsf p hpp.squarefree, hpp.primeFactors]; simp
    rw [hfp, Work.LinnikAreas.Sieve.hPrime]; ring
  have hR : (∑ d ∈ n.divisors, Work.LinnikAreas.Sieve.gFun χ₁ d)
      = ∑ d ∈ n.divisors, f d := Finset.sum_congr rfl (fun d hd => (hdiv d hd).symm)
  rw [hhsf n hn, hL, hR]
  exact hkey


/-- `a(1) = 1`. -/
lemma aFun_one' (χ₁ : DirichletCharacter ℂ q) : Work.LinnikAreas.Sieve.aFun χ₁ 1 = 1 := by
  simp [Work.LinnikAreas.Sieve.aFun]

/-- `a` is multiplicative on coprime arguments. -/
lemma aFun_mul' (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) {m n : ℕ}
    (h : Nat.Coprime m n) :
    Work.LinnikAreas.Sieve.aFun χ₁ (m * n)
      = Work.LinnikAreas.Sieve.aFun χ₁ m * Work.LinnikAreas.Sieve.aFun χ₁ n :=
  (Work.Sieve.aFun_basics χ₁ hreal).1 m n h

/-- `a` is multiplicative over a finite pairwise-coprime family. -/
lemma aFun_prod_of_pairwise (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    (s : Finset ℕ) (g : ℕ → ℕ)
    (hcop : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (g a).Coprime (g b)) :
    Work.LinnikAreas.Sieve.aFun χ₁ (∏ i ∈ s, g i)
      = ∏ i ∈ s, Work.LinnikAreas.Sieve.aFun χ₁ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [aFun_one' χ₁]
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has]
    have hca : (g a).Coprime (∏ i ∈ s, g i) :=
      Nat.Coprime.prod_right (fun i hi =>
        hcop a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (by rintro rfl; exact has hi))
    rw [aFun_mul' χ₁ hreal hca]
    rw [ih (fun x hx y hy hxy =>
      hcop x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)]

/-- **`a(n) = ∏_{p | n} a(p ^ v_p(n))`.** -/
lemma aFun_prod_primeFactors (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    (n : ℕ) (hn : n ≠ 0) :
    Work.LinnikAreas.Sieve.aFun χ₁ n
      = ∏ p ∈ n.primeFactors, Work.LinnikAreas.Sieve.aFun χ₁ (p ^ n.factorization p) := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  exact aFun_prod_of_pairwise χ₁ hreal n.primeFactors (fun p => p ^ n.factorization p)
    (fun a ha b hb hab =>
      Nat.Coprime.pow (n.factorization a) (n.factorization b)
        ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
          (Nat.prime_of_mem_primeFactors hb)).mpr hab))


end Work.LinnikAreas.BGTZ
