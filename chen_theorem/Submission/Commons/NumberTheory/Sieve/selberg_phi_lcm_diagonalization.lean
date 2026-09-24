import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Squarefree
import Submission.Commons.NumberTheory.Sieve.selberg_double_sum_diagonalization

namespace Commons.NumberTheory.Sieve

open Finset

/-! ## The `1/φ(lcm)` Selberg diagonalisation

The Selberg `Λ²` quadratic form built from the density `1/φ` has kernel `1/φ(lcm d e)`.
Writing `φ(lcm)·φ(gcd) = φ d · φ e`, this kernel factors through `φ(gcd)`, and the
squarefree divisor sum `∑_{l ∣ n} ∏_{p ∣ l} (p-2) = φ(n)` diagonalises it with
weight `∏_{p ∣ l} (p-2)`.
-/

/-- **The lcm–gcd identity for Euler's totient**: `φ(lcm d e) · φ(gcd d e) = φ d · φ e`. -/
theorem phi_lcm_mul_phi_gcd (d e : ℕ) :
    Nat.totient (Nat.lcm d e) * Nat.totient (Nat.gcd d e) = Nat.totient d * Nat.totient e := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  rcases eq_or_ne e 0 with rfl | he
  · simp
  refine Nat.cast_injective (R := ℚ) ?_
  have hpf_lcm : (Nat.lcm d e).primeFactors = d.primeFactors ∪ e.primeFactors := by
    ext p
    rw [Nat.mem_primeFactors, Finset.mem_union, Nat.mem_primeFactors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hdvd, _⟩
      by_cases hpd : p ∣ d
      · exact Or.inl ⟨hp, hpd, hd⟩
      · refine Or.inr ⟨hp, ?_, he⟩
        by_contra hpe
        have hcop : Nat.Coprime p (d * e) :=
          (hp.coprime_iff_not_dvd.mpr hpd).mul_right (hp.coprime_iff_not_dvd.mpr hpe)
        have h1 : p ∣ d * e := dvd_trans hdvd (Nat.lcm_dvd (dvd_mul_right d e) (dvd_mul_left e d))
        have hg : p.gcd (d * e) = 1 := hcop
        exact hp.not_dvd_one (hg ▸ Nat.dvd_gcd dvd_rfl h1)
    · rintro (⟨hp, hpd, _⟩ | ⟨hp, hpe, _⟩)
      · exact ⟨hp, dvd_trans hpd (Nat.dvd_lcm_left d e), fun h => Or.elim (Nat.lcm_eq_zero_iff.mp h) hd he⟩
      · exact ⟨hp, dvd_trans hpe (Nat.dvd_lcm_right d e), fun h => Or.elim (Nat.lcm_eq_zero_iff.mp h) hd he⟩
  have hpf_gcd : (Nat.gcd d e).primeFactors = d.primeFactors ∩ e.primeFactors :=
    Nat.primeFactors_gcd hd he
  rw [Nat.cast_mul, Nat.cast_mul, Nat.totient_eq_mul_prod_factors, Nat.totient_eq_mul_prod_factors,
    Nat.totient_eq_mul_prod_factors, Nat.totient_eq_mul_prod_factors]
  have key : (∏ p ∈ (Nat.lcm d e).primeFactors, (1 - (p : ℚ)⁻¹))
        * (∏ p ∈ (Nat.gcd d e).primeFactors, (1 - (p : ℚ)⁻¹))
      = (∏ p ∈ d.primeFactors, (1 - (p : ℚ)⁻¹)) * ∏ p ∈ e.primeFactors, (1 - (p : ℚ)⁻¹) := by
    rw [hpf_lcm, hpf_gcd, Finset.prod_union_inter]
  have hcast : ((Nat.lcm d e : ℕ) : ℚ) * ((Nat.gcd d e : ℕ) : ℚ) = (d : ℚ) * (e : ℚ) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.lcm_mul_gcd]
  rw [show (((Nat.lcm d e : ℕ) : ℚ)
        * (∏ p ∈ (Nat.lcm d e).primeFactors, (1 - (p : ℚ)⁻¹)))
      * (((Nat.gcd d e : ℕ) : ℚ)
        * (∏ p ∈ (Nat.gcd d e).primeFactors, (1 - (p : ℚ)⁻¹)))
      = (((Nat.lcm d e : ℕ) : ℚ) * ((Nat.gcd d e : ℕ) : ℚ))
        * ((∏ p ∈ (Nat.lcm d e).primeFactors, (1 - (p : ℚ)⁻¹))
          * (∏ p ∈ (Nat.gcd d e).primeFactors, (1 - (p : ℚ)⁻¹))) by ring,
    key, hcast]
  ring

/-- Pointwise form of the kernel diagonalisation: the `1/φ(lcm)` kernel equals
`(1/φ d)(1/φ e)·φ(gcd d e)` (for positive `d`, `e`). -/
lemma div_phi_lcm_eq (lam : ℕ → ℝ) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    lam d * lam e / (Nat.totient (Nat.lcm d e) : ℝ)
      = lam d / (Nat.totient d : ℝ) * (lam e / (Nat.totient e : ℝ))
          * (Nat.totient (Nat.gcd d e) : ℝ) := by
  have hcast : (Nat.totient (Nat.lcm d e) : ℝ) * (Nat.totient (Nat.gcd d e) : ℝ)
      = (Nat.totient d : ℝ) * (Nat.totient e : ℝ) := by
    exact_mod_cast phi_lcm_mul_phi_gcd d e
  have hl : (Nat.totient (Nat.lcm d e) : ℝ) ≠ 0 := by
    have hz : Nat.lcm d e ≠ 0 := fun hz => Or.elim (Nat.lcm_eq_zero_iff.mp hz) hd he
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hz)).ne'
  have hdd : (Nat.totient d : ℝ) ≠ 0 :=
    (by exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd)).ne' : (Nat.totient d : ℝ) ≠ 0)
  have hee : (Nat.totient e : ℝ) ≠ 0 :=
    (by exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero he)).ne' : (Nat.totient e : ℝ) ≠ 0)
  have h1 : (1 : ℝ) / (Nat.totient (Nat.lcm d e) : ℝ)
      = (Nat.totient (Nat.gcd d e) : ℝ) / ((Nat.totient d : ℝ) * (Nat.totient e : ℝ)) := by
    rw [div_eq_div_iff hl (by positivity), one_mul]
    linarith [hcast]
  rw [show lam d * lam e / (Nat.totient (Nat.lcm d e) : ℝ)
        = lam d * lam e * ((1 : ℝ) / (Nat.totient (Nat.lcm d e) : ℝ)) by ring, h1]
  field_simp

/-- The prime factors of a product of a set of primes are exactly that set. -/
lemma primeFactors_prod_of_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p).primeFactors = s := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Nat.primeFactors_mul (hs a (Finset.mem_insert_self a s)).ne_zero
      (Finset.prod_ne_zero_iff.mpr fun p hp => (hs p (Finset.mem_insert_of_mem hp)).ne_zero),
      Nat.Prime.primeFactors (hs a (Finset.mem_insert_self a s)),
      ih (fun p hp => hs p (Finset.mem_insert_of_mem hp)), Finset.insert_eq]

/-- **Divisor/powerset bijection for squarefree numbers.**  For squarefree `g`, the divisors of
`g` are exactly the products of subsets of the prime factors of `g`. -/
lemma divisors_eq_powerset_image_prod {g : ℕ} (hg : Squarefree g) :
    g.divisors = (g.primeFactors.powerset).image (fun t => ∏ p ∈ t, p) := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact (Nat.squarefree_iff_prime_squarefree.mp hg 2 Nat.prime_two) (by norm_num)
  ext l
  simp only [Finset.mem_image, Finset.mem_powerset]
  constructor
  · intro hl
    have hlg : l ∣ g := (Nat.mem_divisors.mp hl).1
    have hlsq : Squarefree l := hg.squarefree_of_dvd hlg
    refine ⟨l.primeFactors, fun p hp => ?_, Nat.prod_primeFactors_of_squarefree hlsq⟩
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      dvd_trans (Nat.dvd_of_mem_primeFactors hp) hlg, hg0⟩
  · rintro ⟨t, ht, rfl⟩
    refine Nat.mem_divisors.mpr ⟨?_, hg0⟩
    rw [← Nat.prod_primeFactors_of_squarefree hg]
    exact Finset.prod_dvd_prod_of_subset t g.primeFactors (fun p : ℕ => p) ht

/-- **The squarefree totient expansion**: `φ(g) = ∑_{l ∣ g} ∏_{p ∣ l} (p - 2)` for squarefree `g`. -/
theorem totient_eq_sum_prod_sub_two {g : ℕ} (hg : Squarefree g) (hg0 : g ≠ 0) :
    (Nat.totient g : ℝ) = ∑ l ∈ g.divisors, ∏ p ∈ l.primeFactors, ((p : ℝ) - 2) := by
  have hgf : (∏ p ∈ g.primeFactors, p).primeFactors = g.primeFactors :=
    primeFactors_prod_of_primes fun p hp => Nat.prime_of_mem_primeFactors hp
  have hswitch : (∑ l ∈ g.divisors, ∏ p ∈ l.primeFactors, ((p : ℝ) - 2))
      = ∑ t ∈ g.primeFactors.powerset, ∏ p ∈ t, ((p : ℝ) - 2) := by
    rw [divisors_eq_powerset_image_prod hg, Finset.sum_image]
    · refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.mem_powerset] at ht
      rw [primeFactors_prod_of_primes fun p hp => Nat.prime_of_mem_primeFactors (ht hp)]
    · intro a ha b hb hab
      have ha' : a ⊆ g.primeFactors := Finset.mem_powerset.mp (Finset.mem_coe.mp ha)
      have hb' : b ⊆ g.primeFactors := Finset.mem_powerset.mp (Finset.mem_coe.mp hb)
      have hab' : (∏ p ∈ a, p) = (∏ p ∈ b, p) := hab
      rw [← primeFactors_prod_of_primes (fun p hp => Nat.prime_of_mem_primeFactors (ha' hp)),
        hab',
        primeFactors_prod_of_primes (fun p hp => Nat.prime_of_mem_primeFactors (hb' hp))]
  have hprod_eq : (∏ p ∈ g.primeFactors, (((p : ℝ) - 2) + 1))
      = ∏ p ∈ g.primeFactors, (((p - 1 : ℕ)) : ℝ) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have h1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
    rw [Nat.cast_sub h1]; ring
  have hleft : (Nat.totient g : ℝ) = ∏ p ∈ g.primeFactors, (((p : ℝ) - 2) + 1) := by
    have h := Nat.totient_mul_prod_primeFactors g
    have hpf : ∏ p ∈ g.primeFactors, p = g := Nat.prod_primeFactors_of_squarefree hg
    have hR : (Nat.totient g : ℝ) * ((∏ p ∈ g.primeFactors, p : ℕ) : ℝ)
        = (g : ℝ) * ((∏ p ∈ g.primeFactors, (p - 1) : ℕ) : ℝ) := by exact_mod_cast h
    rw [hpf, Nat.cast_prod] at hR
    have hR2 : (Nat.totient g : ℝ) * (g : ℝ)
        = (g : ℝ) * ∏ p ∈ g.primeFactors, (((p : ℝ) - 2) + 1) := by
      rw [hprod_eq]; exact hR
    rw [mul_comm (g : ℝ) (∏ p ∈ g.primeFactors, (((p : ℝ) - 2) + 1))] at hR2
    exact mul_right_cancel₀ (by exact_mod_cast hg0 : (g : ℝ) ≠ 0) hR2
  have hprod : ∏ p ∈ g.primeFactors, (((p : ℝ) - 2) + 1)
      = ∑ t ∈ g.primeFactors.powerset, ∏ p ∈ t, ((p : ℝ) - 2) := by
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t ht => ?_
    simp
  rw [hleft, hprod, ← hswitch]

/-- **General gcd diagonalisation.**  If `F (gcd d e) = ∑_{l ∣ d, l ∣ e} f l` on a
divisor-closed finite set `T` of positive integers, then
`∑_{d,e} a_d a_e F(gcd d e) = ∑_l f_l (∑_{l ∣ d} a_d)²`. -/
lemma sum_gcd_eq_sum_weight_sq {T : Finset ℕ} (F f : ℕ → ℝ)
    (hdiv : ∀ {d e : ℕ}, d ∈ T → e ∈ T →
      (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then f l else 0) = F (Nat.gcd d e))
    (a : ℕ → ℝ) :
    (∑ d ∈ T, ∑ e ∈ T, a d * a e * F (Nat.gcd d e))
      = ∑ l ∈ T, f l * (∑ d ∈ T.filter (fun d => l ∣ d), a d) ^ 2 := by
  have step1 : (∑ d ∈ T, ∑ e ∈ T, a d * a e * F (Nat.gcd d e))
      = ∑ d ∈ T, ∑ e ∈ T, a d * a e *
          (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then f l else 0) := by
    apply Finset.sum_congr rfl; intro d hd
    apply Finset.sum_congr rfl; intro e he
    rw [hdiv hd he]
  rw [step1]
  calc (∑ d ∈ T, ∑ e ∈ T, a d * a e *
          (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then f l else 0))
      = ∑ d ∈ T, ∑ e ∈ T, ∑ l ∈ T, a d * a e *
          (if (l ∣ d ∧ l ∣ e) then f l else 0) := by
        apply Finset.sum_congr rfl; intro d _
        apply Finset.sum_congr rfl; intro e _
        rw [Finset.mul_sum]
    _ = ∑ l ∈ T, ∑ d ∈ T, ∑ e ∈ T, a d * a e *
          (if (l ∣ d ∧ l ∣ e) then f l else 0) := by
        rw [triple_sum_swap]
    _ = ∑ l ∈ T, ∑ d ∈ T, ∑ e ∈ T,
          (if (l ∣ d ∧ l ∣ e) then a d * a e * f l else 0) := by
        apply Finset.sum_congr rfl; intro l _
        apply Finset.sum_congr rfl; intro d _
        apply Finset.sum_congr rfl; intro e _
        rw [mul_ite, mul_zero]
    _ = ∑ l ∈ T, f l * (∑ d ∈ T.filter (fun d => l ∣ d), a d) ^ 2 := by
        apply Finset.sum_congr rfl; intro l _
        rw [sum_sum_ite, sq]
        ring

/-- **The `1/φ(lcm)` Selberg double-sum diagonalisation.**  For squarefree `M`, the quadratic
form `∑_{d,e ≤ D} λ_d λ_e / φ(lcm d e)` over the divisors of `M` equals
`∑_{l ≤ D} (∏_{p ∣ l} (p-2)) (∑_{l ∣ d} λ_d / φ(d))²`. -/
theorem selberg_phi_lcm_diagonalization (M D : ℕ) (hM : 1 ≤ M) (hMsq : Squarefree M)
    (lam : ℕ → ℝ) :
    (∑ d ∈ M.divisors.filter (fun d : ℕ => d ≤ D),
       ∑ e ∈ M.divisors.filter (fun e : ℕ => e ≤ D),
         lam d * lam e / ((Nat.totient (Nat.lcm d e) : ℕ) : ℝ))
    = ∑ l ∈ M.divisors.filter (fun l : ℕ => l ≤ D),
        (∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) *
          (∑ d ∈ (M.divisors.filter (fun d : ℕ => d ≤ D)).filter (fun d : ℕ => l ∣ d),
             lam d / (Nat.totient d : ℝ)) ^ 2 := by
  classical
  set T : Finset ℕ := M.divisors.filter (fun d : ℕ => d ≤ D) with hTdef
  have hMpos : 0 < M := hM
  have hTpos : ∀ d ∈ T, 0 < d := by
    intro d hd
    rw [hTdef] at hd
    exact Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1) hMpos
  have hTclosed : ∀ {l d : ℕ}, l ∣ d → d ∈ T → l ∈ T := by
    intro l d hld hd
    rw [hTdef] at hd ⊢
    have hdM : d ∣ M := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hdD : d ≤ D := (Finset.mem_filter.mp hd).2
    rw [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨hld.trans hdM, hMpos.ne'⟩,
      le_trans (Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hdM hMpos) hld) hdD⟩
  have key : (∑ d ∈ T, ∑ e ∈ T, lam d * lam e / (Nat.totient (Nat.lcm d e) : ℝ))
      = ∑ d ∈ T, ∑ e ∈ T,
          lam d / (Nat.totient d : ℝ) * (lam e / (Nat.totient e : ℝ))
            * (Nat.totient (Nat.gcd d e) : ℝ) := by
    apply Finset.sum_congr rfl; intro d hd
    apply Finset.sum_congr rfl; intro e he
    exact div_phi_lcm_eq lam (hTpos d hd).ne' (hTpos e he).ne'
  have hdiv : ∀ {d e : ℕ}, d ∈ T → e ∈ T →
      (∑ l ∈ T, if (l ∣ d ∧ l ∣ e) then (∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) else 0)
        = (Nat.totient (Nat.gcd d e) : ℝ) := by
    intro d e hd he
    have hdM : d ∣ M := by
      rw [hTdef] at hd
      exact Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hg0 : Nat.gcd d e ≠ 0 :=
      (Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left d e) (hTpos d hd)).ne'
    have hgsq : Squarefree (Nat.gcd d e) :=
      hMsq.squarefree_of_dvd ((Nat.gcd_dvd_left d e).trans hdM)
    have hset : T.filter (fun l => l ∣ d ∧ l ∣ e) = (Nat.gcd d e).divisors := by
      ext l
      rw [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨hlT, hld, hle⟩
        exact ⟨⟨hld, hle⟩, hg0⟩
      · rintro ⟨⟨hld, hle⟩, _⟩
        exact ⟨hTclosed hld hd, hld, hle⟩
    rw [← Finset.sum_filter, hset]
    exact (totient_eq_sum_prod_sub_two hgsq hg0).symm
  rw [key]
  exact sum_gcd_eq_sum_weight_sq
    (fun n => (Nat.totient n : ℝ))
    (fun l => ∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) hdiv
    (fun d => lam d / (Nat.totient d : ℝ))

end Commons.NumberTheory.Sieve