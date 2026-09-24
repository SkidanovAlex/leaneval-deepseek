import Mathlib
import Submission.Work.ChenPlan.LinearSieve.basic
import Submission.Work.LinearSieve.Selberg.weights
import Submission.Work.LinearSieve.Selberg.mu_sum_multiples

namespace Work.LinearSieve.Selberg

open Finset
open scoped BigOperators Pointwise

set_option autoImplicit false

/-- `h(1) = 1` for Selberg's terms. -/
lemma selbergTerms_one (s : BoundingSieve) : (s.selbergTerms) 1 = 1 := by
  rw [BoundingSieve.selbergTerms_apply, s.nu_mult.map_one]; simp

/-- Positivity of the `G`-sum. -/
lemma gSum_pos (s : BoundingSieve) {ξ : ℝ} (hξ : 1 < ξ) :
    0 < Work.ChenPlan.LinearSieve.gSum s ξ := by
  rw [Work.ChenPlan.LinearSieve.gSum]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun d hd => ?_) (show 1 ∈ _ from ?_))
  · rw [selbergTerms_one]; norm_num
  · exact le_of_lt (BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1))
  · exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd _, BoundingSieve.prodPrimes_ne_zero⟩,
      by simpa using hξ⟩

lemma tailG_nonneg (s : BoundingSieve) (ξ : ℝ) (d : ℕ) : 0 ≤ tailG s ξ d := by
  rw [tailG]
  exact Finset.sum_nonneg fun l hl =>
    le_of_lt (BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1))

/-- `T_d = 0` when `d ∤ P`. -/
lemma tailG_eq_zero_of_not_dvd (s : BoundingSieve) (ξ : ℝ) {d : ℕ} (hd : ¬ d ∣ s.prodPrimes) :
    tailG s ξ d = 0 := by
  rw [tailG]
  apply Finset.sum_eq_zero
  intro l hl
  obtain ⟨hlD, hdl, -⟩ := Finset.mem_filter.mp hl
  exact absurd (hdl.trans (Nat.dvd_of_mem_divisors hlD)) hd

/-- `T_d = 0` when `ξ ≤ d`. -/
lemma tailG_eq_zero_of_le (s : BoundingSieve) (ξ : ℝ) {d : ℕ} (hd : ξ ≤ (d : ℝ)) :
    tailG s ξ d = 0 := by
  rw [tailG]
  apply Finset.sum_eq_zero
  intro l hl
  obtain ⟨hlD, hdl, hlξ⟩ := Finset.mem_filter.mp hl
  have hlne : l ≠ 0 :=
    ne_zero_of_dvd_ne_zero (Nat.mem_divisors.mp hlD).2 (Nat.mem_divisors.mp hlD).1
  have : (d : ℝ) < ξ :=
    lt_of_le_of_lt (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hlne) hdl) hlξ
  exact absurd this (not_lt.mpr hd)

/-- `ν(d) w(d) = μ(d) T_d / G(ξ)`. -/
lemma nu_mul_selbergWeight (s : BoundingSieve) {ξ : ℝ} (hξ : 1 < ξ) (d : ℕ) :
    s.nu d * selbergWeight s ξ d
      = ((ArithmeticFunction.moebius d : ℤ) : ℝ) * tailG s ξ d
          / Work.ChenPlan.LinearSieve.gSum s ξ := by
  by_cases h : d ∣ s.prodPrimes ∧ (d : ℝ) < ξ
  · have hG : Work.ChenPlan.LinearSieve.gSum s ξ ≠ 0 := ne_of_gt (gSum_pos s hξ)
    have hν : s.nu d ≠ 0 := BoundingSieve.nu_ne_zero h.1
    rw [selbergWeight, if_pos h]
    field_simp
  · have hT : tailG s ξ d = 0 := by
      by_cases hdP : d ∣ s.prodPrimes
      · exact tailG_eq_zero_of_le s ξ (not_lt.mp fun hc => h ⟨hdP, hc⟩)
      · exact tailG_eq_zero_of_not_dvd s ξ hdP
    rw [selbergWeight, if_neg h, mul_zero, hT, mul_zero, zero_div]

/-- `w(1) = 1`. -/
lemma selbergWeight_one (s : BoundingSieve) {ξ : ℝ} (hξ : 1 < ξ) : selbergWeight s ξ 1 = 1 := by
  rw [selbergWeight]
  have hcond : (1 : ℕ) ∣ s.prodPrimes ∧ ((1 : ℕ) : ℝ) < ξ :=
    ⟨one_dvd _, by simpa using hξ⟩
  rw [if_pos hcond]
  have hT : tailG s ξ 1 = Work.ChenPlan.LinearSieve.gSum s ξ := by
    rw [tailG, Work.ChenPlan.LinearSieve.gSum]; congr 1; ext l; simp
  have hμ1 : ((ArithmeticFunction.moebius 1 : ℤ) : ℝ) = 1 := by
    rw [ArithmeticFunction.moebius_apply_one]; norm_num
  have hν1 : s.nu 1 = 1 := s.nu_mult.map_one
  have hG : Work.ChenPlan.LinearSieve.gSum s ξ ≠ 0 := ne_of_gt (gSum_pos s hξ)
  rw [hT, hμ1, hν1]
  field_simp

/-- Support: `w d = 0` for `d ∤ P`. -/
lemma selbergWeight_eq_zero_of_not_dvd (s : BoundingSieve) (ξ : ℝ) {d : ℕ}
    (hd : ¬ d ∣ s.prodPrimes) : selbergWeight s ξ d = 0 := by
  rw [selbergWeight, if_neg (fun h => hd h.1)]

/-- Support: `w d = 0` for `ξ ≤ d`. -/
lemma selbergWeight_eq_zero_of_le (s : BoundingSieve) (ξ : ℝ) {d : ℕ}
    (hd : ξ ≤ (d : ℝ)) : selbergWeight s ξ d = 0 := by
  rw [selbergWeight, if_neg (fun h => not_lt.mpr hd h.2)]

/-- The Möbius sum over divisors of `l'` in `P.divisors` that are multiples of `l`. -/
lemma sum_mu_between (s : BoundingSieve) {l l' : ℕ} (hl : l ∈ s.prodPrimes.divisors)
    (hl' : l' ∈ s.prodPrimes.divisors) :
    ∑ d ∈ s.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ∣ l'),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)
      = if l = l' then ((ArithmeticFunction.moebius l : ℤ) : ℝ) else 0 := by
  have hP := BoundingSieve.prodPrimes_ne_zero (s := s)
  have hl'0 : l' ≠ 0 := ne_zero_of_dvd_ne_zero hP (Nat.dvd_of_mem_divisors hl')
  have hfil : s.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ∣ l')
      = l'.divisors.filter (fun d => l ∣ d) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdP, -⟩, hld, hdl'⟩
      exact ⟨⟨hdl', hl'0⟩, hld⟩
    · rintro ⟨⟨hdl', -⟩, hld⟩
      exact ⟨⟨hdl'.trans (Nat.dvd_of_mem_divisors hl'), hP⟩, hld, hdl'⟩
  rw [hfil]
  by_cases hll' : l ∣ l'
  · exact mu_sum_multiples l l' hll' hl'0 (BoundingSieve.squarefree_of_mem_divisors_prodPrimes hl')
  · have hempty : l'.divisors.filter (fun d => l ∣ d) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro d hd hld
      exact hll' (hld.trans (Nat.dvd_of_mem_divisors hd))
    rw [hempty, Finset.sum_empty, if_neg (by rintro rfl; exact hll' dvd_rfl)]

/-- `T_d` as a sum over all divisors of `P`. -/
lemma tailG_sum_form (s : BoundingSieve) (ξ : ℝ) (d : ℕ) :
    tailG s ξ d = ∑ l ∈ s.prodPrimes.divisors,
        (if d ∣ l ∧ (l : ℝ) < ξ then (s.selbergTerms) l else 0) := by
  rw [tailG, Finset.sum_filter]

/-- The numerator of the Selberg "Fourier coefficient": the Möbius transform of `T`. -/
lemma V_num (s : BoundingSieve) {ξ : ℝ} {l : ℕ} (hl : l ∈ s.prodPrimes.divisors) :
    ∑ d ∈ s.prodPrimes.divisors,
        (if l ∣ d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) * tailG s ξ d else 0)
      = if (l : ℝ) < ξ then ((ArithmeticFunction.moebius l : ℤ) : ℝ) * (s.selbergTerms) l else 0 := by
  rw [← Finset.sum_filter]
  have step1 : ∀ d : ℕ, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * tailG s ξ d
      = ∑ l' ∈ s.prodPrimes.divisors,
          (if d ∣ l' ∧ (l' : ℝ) < ξ then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (s.selbergTerms) l' else 0) := by
    intro d
    rw [tailG_sum_form, Finset.mul_sum]
    simp only [mul_ite, mul_zero]
  simp_rw [step1]
  rw [Finset.sum_comm]
  have step2 : ∀ l' ∈ s.prodPrimes.divisors,
      ∑ d ∈ s.prodPrimes.divisors.filter (fun d => l ∣ d),
          (if d ∣ l' ∧ (l' : ℝ) < ξ then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (s.selbergTerms) l' else 0)
      = (if (l' : ℝ) < ξ then
          (s.selbergTerms) l' * (if l = l' then ((ArithmeticFunction.moebius l : ℤ) : ℝ) else 0)
          else 0) := by
    intro l' hl'
    by_cases hξ' : (l' : ℝ) < ξ
    · rw [if_pos hξ']
      have hterm : ∀ d : ℕ,
          (if d ∣ l' ∧ (l' : ℝ) < ξ then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (s.selbergTerms) l' else 0)
          = (s.selbergTerms) l' * (if d ∣ l' then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) := by
        intro d
        by_cases hd : d ∣ l'
        · rw [if_pos ⟨hd, hξ'⟩, if_pos hd, mul_comm]
        · rw [if_neg (fun h => hd h.1), if_neg hd, mul_zero]
      simp_rw [hterm, ← Finset.mul_sum]
      rw [← Finset.sum_filter, Finset.filter_filter, sum_mu_between s hl hl']
    · rw [if_neg hξ']
      refine Finset.sum_eq_zero fun d hd => ?_
      simp [not_lt.mp hξ']
  rw [Finset.sum_congr rfl step2]
  have step3 : ∀ l' : ℕ,
      (if (l' : ℝ) < ξ then
        (s.selbergTerms) l' * (if l = l' then ((ArithmeticFunction.moebius l : ℤ) : ℝ) else 0)
        else 0)
      = (if l' = l then
          (if (l' : ℝ) < ξ then ((ArithmeticFunction.moebius l' : ℤ) : ℝ) * (s.selbergTerms) l' else 0)
          else 0) := by
    intro l'
    by_cases h : l = l'
    · subst h; simp [mul_comm]
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  rw [Finset.sum_congr rfl (fun l' _ => step3 l')]
  rw [Finset.sum_ite_eq' s.prodPrimes.divisors l
        (fun l' => if (l' : ℝ) < ξ then ((ArithmeticFunction.moebius l' : ℤ) : ℝ) * (s.selbergTerms) l' else 0),
      if_pos hl]

/-- The Selberg "Fourier coefficient" `Σ_{d : l ∣ d} ν(d) w(d) = μ(l) h(l) / G(ξ)` (and `0` when
`ξ ≤ l`). -/
lemma V_eq (s : BoundingSieve) {ξ : ℝ} (hξ : 1 < ξ) {l : ℕ} (hl : l ∈ s.prodPrimes.divisors) :
    ∑ d ∈ s.prodPrimes.divisors, (if l ∣ d then s.nu d * selbergWeight s ξ d else 0)
      = if (l : ℝ) < ξ then ((ArithmeticFunction.moebius l : ℤ) : ℝ) * (s.selbergTerms) l
          / Work.ChenPlan.LinearSieve.gSum s ξ else 0 := by
  have hstep : ∀ d : ℕ, (if l ∣ d then s.nu d * selbergWeight s ξ d else 0)
      = (if l ∣ d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) * tailG s ξ d else 0)
          / Work.ChenPlan.LinearSieve.gSum s ξ := by
    intro d
    rw [nu_mul_selbergWeight s hξ d]
    by_cases h : l ∣ d
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_div]
  rw [Finset.sum_congr rfl (fun d _ => hstep d), ← Finset.sum_div, V_num s hl]
  by_cases h : (l : ℝ) < ξ <;> simp [h]


/-! ### The bound `T_d ≤ ν(d) G(ξ)`

We need the standard decomposition of the divisors of a product of coprime numbers, applied to
`P = d · (P/d)`. -/

/-- The map `(a, b) ↦ a * b` is injective on `divisors m × divisors n` when `m ⊥ n`. -/
lemma injOn_mul_divisors {m n : ℕ} (hmn : m.Coprime n) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ↑(m.divisors ×ˢ n.divisors) := by
  rintro ⟨a1, b1⟩ hp1 ⟨a2, b2⟩ hp2 heq
  rw [Finset.mem_coe, Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hp1 hp2
  obtain ⟨⟨ha1, hm0⟩, hb1, -⟩ := hp1
  obtain ⟨⟨ha2, -⟩, hb2, -⟩ := hp2
  simp only [Prod.fst, Prod.snd] at heq
  have hb1m : b1.Coprime m := (hmn.coprime_dvd_right hb1).symm
  have hb2m : b2.Coprime m := (hmn.coprime_dvd_right hb2).symm
  have hg1 : (a1 * b1).gcd m = a1 := by
    refine Nat.dvd_antisymm ?_ (Nat.dvd_gcd (dvd_mul_right a1 b1) ha1)
    exact (hb1m.coprime_dvd_right (Nat.gcd_dvd_right (a1 * b1) m)).symm.dvd_of_dvd_mul_right
      (Nat.gcd_dvd_left (a1 * b1) m)
  have hg2 : (a2 * b2).gcd m = a2 := by
    refine Nat.dvd_antisymm ?_ (Nat.dvd_gcd (dvd_mul_right a2 b2) ha2)
    exact (hb2m.coprime_dvd_right (Nat.gcd_dvd_right (a2 * b2) m)).symm.dvd_of_dvd_mul_right
      (Nat.gcd_dvd_left (a2 * b2) m)
  have haeq : a1 = a2 := by rw [← hg1, ← hg2, heq]
  have ha1pos : 0 < a1 := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hm0 ha1)
  refine Prod.ext haeq ?_
  rw [← haeq] at heq
  exact Nat.eq_of_mul_eq_mul_left ha1pos heq

/-- Divisibility decomposition: sums over divisors of a product of coprimes split. -/
lemma sum_divisors_mul_coprime {m n : ℕ} (hmn : m.Coprime n) (F : ℕ → ℝ) :
    ∑ l ∈ (m * n).divisors, F l
      = ∑ a ∈ m.divisors, ∑ b ∈ n.divisors, F (a * b) := by
  have himg : m.divisors * n.divisors
      = (m.divisors ×ˢ n.divisors).image (fun p : ℕ × ℕ => p.1 * p.2) := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_mul] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
    · intro hx
      obtain ⟨⟨a, b⟩, hp, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_product] at hp
      exact Finset.mem_mul.mpr ⟨a, hp.1, b, hp.2, rfl⟩
  rw [Nat.divisors_mul, himg,
    Finset.sum_image (f := F) (g := fun p : ℕ × ℕ => p.1 * p.2) (injOn_mul_divisors hmn)]
  exact Finset.sum_product m.divisors n.divisors (fun p : ℕ × ℕ => F (p.1 * p.2))

/-- Reindexing: the divisors of `P` that are multiples of `d` are `d` times the divisors of
`P / d`. -/
lemma sum_multiples_divisors (s : BoundingSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) (F : ℕ → ℝ) :
    ∑ l ∈ s.prodPrimes.divisors.filter (fun l => d ∣ l), F l
      = ∑ e ∈ (s.prodPrimes / d).divisors, F (d * e) := by
  have hP0 : s.prodPrimes ≠ 0 := BoundingSieve.prodPrimes_ne_zero
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hP0 hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hfil : s.prodPrimes.divisors.filter (fun l => d ∣ l)
      = ((s.prodPrimes / d).divisors).image (fun e => d * e) := by
    ext l
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨hlP, -⟩, hdl⟩
      refine ⟨l / d, ⟨?_, ?_⟩, Nat.mul_div_cancel' hdl⟩
      · rw [← Nat.mul_div_cancel' hdl, ← Nat.mul_div_cancel' hd] at hlP
        exact (Nat.mul_dvd_mul_iff_left hdpos).mp hlP
      · exact fun h => hP0 (by rw [← Nat.mul_div_cancel' hd, h, mul_zero])
    · rintro ⟨e, ⟨he, -⟩, rfl⟩
      refine ⟨⟨?_, hP0⟩, dvd_mul_right d e⟩
      rw [← Nat.mul_div_cancel' hd]
      exact Nat.mul_dvd_mul_left d he
  rw [hfil, Finset.sum_image (f := F) (g := fun e => d * e)
    (fun e1 _ e2 _ h => Nat.eq_of_mul_eq_mul_left hdpos h)]

/-- `ν(d) · Σ_{a ∣ d} h(a) = h(d)`. -/
lemma nu_mul_sum_selbergTerms (s : BoundingSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    s.nu d * (∑ d' ∈ d.divisors, (s.selbergTerms) d') = (s.selbergTerms) d := by
  have hsq : Squarefree d := BoundingSieve.squarefree_of_dvd_prodPrimes hd
  have h1 : (∑ d' ∈ d.divisors, (s.selbergTerms) d')
      = ∏ p ∈ d.primeFactors, (1 + (s.selbergTerms) p) :=
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
      s.selbergTerms_isMultiplicative hsq).symm
  have h2 : ∀ p ∈ d.primeFactors, (1 + (s.selbergTerms) p) = (1 - s.nu p)⁻¹ := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpP : p ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hd
    have hne : 1 - s.nu p ≠ 0 := by
      have hlt := BoundingSieve.nu_lt_one_of_prime s p hpprime hpP; linarith
    rw [BoundingSieve.selbergTerms_apply, hpprime.primeFactors]
    simp only [Finset.prod_singleton]
    field_simp
    ring
  rw [h1, Finset.prod_congr rfl h2, BoundingSieve.selbergTerms_apply]

/-- The bound `T_d ≤ ν(d) G(ξ)`. -/
lemma tailG_le_self (s : BoundingSieve) (ξ : ℝ) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    tailG s ξ d ≤ s.nu d * Work.ChenPlan.LinearSieve.gSum s ξ := by
  have hP0 : s.prodPrimes ≠ 0 := BoundingSieve.prodPrimes_ne_zero
  have hdpos : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP0 hd)
  have hcop : d.Coprime (s.prodPrimes / d) :=
    (Nat.squarefree_mul_iff.mp (by rw [Nat.mul_div_cancel' hd]; exact s.prodPrimes_squarefree)).1
  have hmul : ∀ a b : ℕ, a.Coprime b →
      (s.selbergTerms) (a * b) = (s.selbergTerms) a * (s.selbergTerms) b :=
    fun a b hab => s.selbergTerms_isMultiplicative.map_mul_of_coprime hab
  have hT0 : tailG s ξ d = ∑ l ∈ s.prodPrimes.divisors.filter (fun l => d ∣ l),
      (if (l : ℝ) < ξ then (s.selbergTerms) l else 0) := by
    rw [tailG, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : d ∣ l <;> simp [h]
  have hT : tailG s ξ d = (s.selbergTerms) d *
      ∑ e ∈ (s.prodPrimes / d).divisors,
        (if ((d * e : ℕ) : ℝ) < ξ then (s.selbergTerms) e else 0) := by
    rw [hT0, sum_multiples_divisors s hd
      (fun l => if (l : ℝ) < ξ then (s.selbergTerms) l else 0), Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hde : (s.selbergTerms) (d * e) = (s.selbergTerms) d * (s.selbergTerms) e :=
      hmul d e (hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors he))
    by_cases h : ((d * e : ℕ) : ℝ) < ξ
    · rw [if_pos h, if_pos h, hde]
    · rw [if_neg h, if_neg h, mul_zero]
  have hG : Work.ChenPlan.LinearSieve.gSum s ξ =
      ∑ a ∈ d.divisors, ∑ b ∈ (s.prodPrimes / d).divisors,
        (if ((a * b : ℕ) : ℝ) < ξ then (s.selbergTerms) a * (s.selbergTerms) b else 0) := by
    conv_lhs => rw [Work.ChenPlan.LinearSieve.gSum, Finset.sum_filter, ← Nat.mul_div_cancel' hd]
    rw [sum_divisors_mul_coprime hcop
      (fun l => if (l : ℝ) < ξ then (s.selbergTerms) l else 0)]
    refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
    have hab : (s.selbergTerms) (a * b) = (s.selbergTerms) a * (s.selbergTerms) b :=
      hmul a b ((hcop.coprime_dvd_left (Nat.dvd_of_mem_divisors ha)).coprime_dvd_right
        (Nat.dvd_of_mem_divisors hb))
    by_cases h : ((a * b : ℕ) : ℝ) < ξ
    · rw [if_pos h, if_pos h, hab]
    · rw [if_neg h, if_neg h]
  have hkey : (∑ a ∈ d.divisors, (s.selbergTerms) a) *
      (∑ b ∈ (s.prodPrimes / d).divisors,
        (if ((d * b : ℕ) : ℝ) < ξ then (s.selbergTerms) b else 0))
      ≤ ∑ a ∈ d.divisors, ∑ b ∈ (s.prodPrimes / d).divisors,
        (if ((a * b : ℕ) : ℝ) < ξ then (s.selbergTerms) a * (s.selbergTerms) b else 0) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    have ha_le : a ≤ d := Nat.le_of_dvd hdpos (Nat.dvd_of_mem_divisors ha)
    have hga : 0 ≤ (s.selbergTerms) a :=
      le_of_lt (BoundingSieve.selbergTerms_pos ((Nat.dvd_of_mem_divisors ha).trans hd))
    have hgb : 0 ≤ (s.selbergTerms) b :=
      le_of_lt (BoundingSieve.selbergTerms_pos
        ((Nat.dvd_of_mem_divisors hb).trans (Nat.div_dvd_of_dvd hd)))
    by_cases h : ((d * b : ℕ) : ℝ) < ξ
    · have hab_lt : ((a * b : ℕ) : ℝ) < ξ :=
        lt_of_le_of_lt (by exact_mod_cast Nat.mul_le_mul_right b ha_le) h
      rw [if_pos hab_lt, if_pos h]
    · rw [if_neg h, mul_zero]
      by_cases hab : ((a * b : ℕ) : ℝ) < ξ
      · rw [if_pos hab]; exact mul_nonneg hga hgb
      · rw [if_neg hab]
  rw [hT, hG]
  rw [show (s.selbergTerms) d = s.nu d * (∑ a ∈ d.divisors, (s.selbergTerms) a) from
    (nu_mul_sum_selbergTerms s hd).symm]
  conv_lhs => rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hkey (le_of_lt (BoundingSieve.nu_pos_of_dvd_prodPrimes hd))

/-- `|w(d)| ≤ 1` for the Selberg weights. -/
lemma selbergWeight_abs_le_one (s : BoundingSieve) {ξ : ℝ} (hξ : 1 < ξ) (d : ℕ) :
    |selbergWeight s ξ d| ≤ 1 := by
  by_cases h : d ∣ s.prodPrimes ∧ (d : ℝ) < ξ
  · obtain ⟨hdP, hdξ⟩ := h
    have hG : 0 < Work.ChenPlan.LinearSieve.gSum s ξ := gSum_pos s hξ
    have hν : 0 < s.nu d := BoundingSieve.nu_pos_of_dvd_prodPrimes hdP
    have hμ : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        (BoundingSieve.squarefree_of_dvd_prodPrimes hdP)]
      norm_num
    rw [selbergWeight, if_pos ⟨hdP, hdξ⟩, abs_div, abs_mul, hμ, one_mul,
      abs_of_nonneg (tailG_nonneg s ξ d), abs_of_nonneg (le_of_lt (mul_pos hG hν))]
    rw [div_le_iff₀ (mul_pos hG hν), one_mul, mul_comm]
    exact tailG_le_self s ξ hdP
  · rw [selbergWeight, if_neg h, abs_zero]; norm_num

theorem optimal_weights (s : BoundingSieve) {ξ : ℝ} (hξ : 1 < ξ) :
    ∃ w : ℕ → ℝ, w 1 = 1 ∧ (∀ d : ℕ, |w d| ≤ 1)
      ∧ (∀ d : ℕ, ¬ d ∣ s.prodPrimes → w d = 0)
      ∧ (∀ d : ℕ, ξ ≤ (d : ℝ) → w d = 0)
      ∧ s.mainSum (BoundingSieve.lambdaSquared w) * Work.ChenPlan.LinearSieve.gSum s ξ ≤ 1 := by
  refine ⟨selbergWeight s ξ, selbergWeight_one s hξ, selbergWeight_abs_le_one s hξ,
    fun d hd => selbergWeight_eq_zero_of_not_dvd s ξ hd,
    fun d hd => selbergWeight_eq_zero_of_le s ξ hd, ?_⟩
  have hG : Work.ChenPlan.LinearSieve.gSum s ξ ≠ 0 := ne_of_gt (gSum_pos s hξ)
  have hsum : (∑ l ∈ s.prodPrimes.divisors, ((s.selbergTerms) l)⁻¹ *
      (∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then s.nu d * selbergWeight s ξ d else 0) ^ 2)
      = 1 / Work.ChenPlan.LinearSieve.gSum s ξ := by
    have hterm : ∀ l ∈ s.prodPrimes.divisors,
        ((s.selbergTerms) l)⁻¹ *
          (if (l : ℝ) < ξ then ((ArithmeticFunction.moebius l : ℤ) : ℝ) * (s.selbergTerms) l
            / Work.ChenPlan.LinearSieve.gSum s ξ else 0) ^ 2
        = (if (l : ℝ) < ξ then
            (s.selbergTerms) l / (Work.ChenPlan.LinearSieve.gSum s ξ) ^ 2 else 0) := by
      intro l hl
      have hg : (s.selbergTerms) l ≠ 0 :=
        ne_of_gt (BoundingSieve.selbergTerms_pos (Nat.dvd_of_mem_divisors hl))
      have hμ2 : (((ArithmeticFunction.moebius l : ℤ) : ℝ)) ^ 2 = 1 := by
        rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (BoundingSieve.squarefree_of_mem_divisors_prodPrimes hl)]
        norm_num
      by_cases h : (l : ℝ) < ξ
      · rw [if_pos h, if_pos h, div_pow, mul_pow, hμ2, one_mul]
        field_simp
      · rw [if_neg h, if_neg h, zero_pow (by norm_num)]
        simp
    rw [Finset.sum_congr rfl (fun l hl => by rw [V_eq s hξ hl]), Finset.sum_congr rfl hterm]
    rw [← Finset.sum_filter, ← Finset.sum_div, ← Work.ChenPlan.LinearSieve.gSum]
    field_simp
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq, hsum, one_div, inv_mul_cancel₀ hG]

end Work.LinearSieve.Selberg
