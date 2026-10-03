import Mathlib
import Submission.Work.FIArea2.R6.count_sqroot_prime_pow_self
import Submission.Work.FIArea2.R6.card_range_filter_dvd_mul_sq
import Submission.Work.FIArea2.R6.count_sqroot_mul_coprime
import Submission.Work.FIArea2.card_sq_roots_nat
import Submission.Work.FIArea2.Tsum_odd_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2.R6

open Finset

attribute [local instance] Classical.propDecidable

/-! ### The general square-root count, rebuilt on `count_sqroot_prime_pow_self` -/

/-- The number of `z : ZMod n` with `z ^ 2 = a`. -/
private def sqCnt (n : ℕ) [NeZero n] (a : ℤ) : ℕ :=
  ((Finset.univ : Finset (ZMod n)).filter (fun z => z ^ 2 = (a : ZMod n))).card

/-- Multiplicativity wrapper: allows rewriting the modulus along an equality. -/
private lemma sqCnt_mul_of_eq {q p e n : ℕ} [NeZero q] [NeZero (p ^ e)] [NeZero n]
    (h : q = p ^ e * n) (hc : (p ^ e).Coprime n) (a : ℤ) :
    sqCnt q a = sqCnt (p ^ e) a * sqCnt n a := by
  subst h
  exact count_sqroot_mul_coprime (p ^ e) n hc a

/-- `√x · √y ≤ √(xy)`. -/
private lemma sqrt_mul_sqrt_le (x y : ℕ) : Nat.sqrt x * Nat.sqrt y ≤ Nat.sqrt (x * y) := by
  rw [Nat.le_sqrt', mul_pow]
  exact Nat.mul_le_mul (Nat.sqrt_le' x) (Nat.sqrt_le' y)

/-- For `m ≥ 1` and `a : ℤ`, the number of `z : ZMod m` with `z ^ 2 = a` is at most
`4 ^ m.primeFactors.card * Nat.sqrt (Nat.gcd a.natAbs m)`. This is
`Work.FIArea2.R6.count_sqroot_general` rebuilt on the prime-power bound
`Work.FIArea2.R6.count_sqroot_prime_pow_self`, so that the present development does not rest on the
unproved `Work.FIArea2.R6.count_sqroot_prime_pow`. -/
private theorem sqroot_count_general_aux (m : ℕ) [NeZero m] (a : ℤ) :
    ((Finset.univ : Finset (ZMod m)).filter (fun z => z ^ 2 = (a : ZMod m))).card
      ≤ 4 ^ m.primeFactors.card * Nat.sqrt (Nat.gcd a.natAbs m) := by
  have h : ∀ m : ℕ, [NeZero m] → ∀ a : ℤ,
      sqCnt m a ≤ 4 ^ m.primeFactors.card * Nat.sqrt (Nat.gcd a.natAbs m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro _ a
      have hmne : m ≠ 0 := NeZero.ne m
      rcases Nat.lt_or_ge m 2 with hm | hm
      · -- base case `m = 1`
        have hm1 : m = 1 := by omega
        subst hm1
        have h1 : sqCnt 1 a = 1 := by
          rw [sqCnt, Finset.filter_true_of_mem (fun z _ => Subsingleton.elim _ _),
            Finset.card_univ, ZMod.card]
        rw [h1]
        simp
      · -- split off the full `p`-part of `m`
        obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
        set e := m.factorization p with he
        set m' := m / p ^ e with hm'
        have he1 : 1 ≤ e := by
          rw [he]
          exact (hp.dvd_iff_one_le_factorization hmne).mp hpq
        have hpe_dvd : p ^ e ∣ m := by
          rw [he]
          exact (hp.pow_dvd_iff_le_factorization hmne).mpr le_rfl
        have hmul : m = p ^ e * m' := by
          rw [hm']
          exact (Nat.mul_div_cancel' hpe_dvd).symm
        have hmen : m' ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hmul
          exact hmne hmul
        haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
        haveI : NeZero m' := ⟨hmen⟩
        have hmp : ¬ p ∣ m' := by
          intro hdiv
          have hdvd : p ^ (e + 1) ∣ m := by
            rw [hmul, pow_succ]
            exact Nat.mul_dvd_mul_left (p ^ e) hdiv
          have hle : e + 1 ≤ e := by
            rw [he]
            exact (hp.pow_dvd_iff_le_factorization hmne).mp hdvd
          omega
        have hcop : (p ^ e).Coprime m' := by
          rw [Nat.coprime_pow_left_iff (by omega : 0 < e), hp.coprime_iff_not_dvd]
          exact hmp
        have hm_lt : m' < m := by
          have h2 : 1 < p ^ e := by
            calc 1 < p := hp.one_lt
              _ = p ^ 1 := (pow_one p).symm
              _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he1
          have h := Nat.mul_lt_mul_of_pos_left h2 (Nat.pos_of_ne_zero hmen)
          rw [mul_one, mul_comm m' (p ^ e), ← hmul] at h
          exact h
        have hpp := count_sqroot_prime_pow_self p e hp he1 a
        have hmm := ih m' hm_lt a
        have hpf_pe : (p ^ e).primeFactors = {p} :=
          Nat.primeFactors_prime_pow (by omega : e ≠ 0) hp
        have hpf_m : m.primeFactors = (p ^ e).primeFactors ∪ m'.primeFactors := by
          rw [hmul]
          exact hcop.primeFactors_mul
        have hdisj : Disjoint ({p} : Finset ℕ) m'.primeFactors := by
          rw [Finset.disjoint_left]
          intro x hx hx'
          rw [Finset.mem_singleton] at hx
          subst hx
          exact hmp (Nat.mem_primeFactors.mp hx').2.1
        have homega : m.primeFactors.card = 1 + m'.primeFactors.card := by
          rw [hpf_m, hpf_pe, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
        have hgcd : Nat.gcd a.natAbs m
            = Nat.gcd a.natAbs (p ^ e) * Nat.gcd a.natAbs m' := by
          rw [hmul]
          exact hcop.gcd_mul a.natAbs
        rw [sqCnt_mul_of_eq hmul hcop a]
        calc sqCnt (p ^ e) a * sqCnt m' a
            ≤ (4 * Nat.sqrt (Nat.gcd a.natAbs (p ^ e)))
                * (4 ^ m'.primeFactors.card * Nat.sqrt (Nat.gcd a.natAbs m')) :=
              Nat.mul_le_mul hpp hmm
          _ = 4 ^ m.primeFactors.card
                * (Nat.sqrt (Nat.gcd a.natAbs (p ^ e)) * Nat.sqrt (Nat.gcd a.natAbs m')) := by
              rw [homega, pow_add, pow_one]
              ring
          _ ≤ 4 ^ m.primeFactors.card
                * Nat.sqrt (Nat.gcd a.natAbs (p ^ e) * Nat.gcd a.natAbs m') :=
              Nat.mul_le_mul_left _ (sqrt_mul_sqrt_le _ _)
          _ = 4 ^ m.primeFactors.card * Nat.sqrt (Nat.gcd a.natAbs m) := by
              rw [← hgcd]
  exact h m a

/-! ### Auxiliary counting lemmas for the local congruence count -/

/-- **Fiber reduction.** If `e > 0`, `m = e * m'`, `A = e * a` and `B = e * b`, then the solutions
of `m ∣ A z ^ 2 - B` in `[0, m)` number at most `e` times the solutions of `m' ∣ a z ^ 2 - b` in
`[0, m')`: the reduction `z ↦ (z % m', z / m')` is injective and the fibre of a solution of the
reduced congruence over `m'` has exactly `e` elements. -/
private lemma card_filter_dvd_le_mul (m e m' : ℕ) (he : 0 < e) (hmm : m = e * m')
    (A B a b : ℤ) (hA : (e : ℤ) * a = A) (hB : (e : ℤ) * b = B) :
    ((Finset.range m).filter (fun z : ℕ => (m : ℤ) ∣ A * (z : ℤ) ^ 2 - B)).card
      ≤ e * ((Finset.range m').filter (fun z : ℕ => (m' : ℤ) ∣ a * (z : ℤ) ^ 2 - b)).card := by
  rcases Nat.eq_zero_or_pos m' with hm' | hm'
  · subst hm'
    rw [mul_zero] at hmm
    rw [hmm]
    simp
  · set S := (Finset.range m).filter (fun z : ℕ => (m : ℤ) ∣ A * (z : ℤ) ^ 2 - B) with hS
    set T := (Finset.range m').filter (fun z : ℕ => (m' : ℤ) ∣ a * (z : ℤ) ^ 2 - b) with hT
    have heZ : (e : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt he
    have key : ∀ z : ℕ, (m : ℤ) ∣ A * (z : ℤ) ^ 2 - B → (m' : ℤ) ∣ a * (z : ℤ) ^ 2 - b := by
      intro z hz
      have h1 : ((e : ℤ) * (m' : ℤ)) ∣ (e : ℤ) * (a * (z : ℤ) ^ 2 - b) := by
        have h := hz
        rw [hmm] at h
        push_cast at h
        rw [← hA, ← hB] at h
        convert h using 1 <;> ring
      exact (mul_dvd_mul_iff_left heZ).mp h1
    have hmod : ∀ z : ℕ, (m' : ℤ) ∣ (z : ℤ) - ((z % m' : ℕ) : ℤ) := by
      intro z
      have hz : (z : ℤ) = (m' : ℤ) * ((z / m' : ℕ) : ℤ) + ((z % m' : ℕ) : ℤ) := by
        exact_mod_cast (Nat.div_add_mod z m').symm
      exact ⟨((z / m' : ℕ) : ℤ), by rw [hz]; ring⟩
    have hsub : ∀ z ∈ S, (z % m', z / m') ∈ T ×ˢ Finset.range e := by
      intro z hz
      rw [hS] at hz
      simp only [Finset.mem_filter, Finset.mem_range] at hz
      obtain ⟨hzm, hzdvd⟩ := hz
      have h1 : (m' : ℤ) ∣ a * ((z % m' : ℕ) : ℤ) ^ 2 - b := by
        have h1' : (m' : ℤ) ∣ a * (z : ℤ) ^ 2 - b := key z hzdvd
        have h2 : (m' : ℤ) ∣ (z : ℤ) ^ 2 - ((z % m' : ℕ) : ℤ) ^ 2 := by
          obtain ⟨k, hk⟩ := hmod z
          refine ⟨k * ((z : ℤ) + ((z % m' : ℕ) : ℤ)), ?_⟩
          calc (z : ℤ) ^ 2 - ((z % m' : ℕ) : ℤ) ^ 2
              = ((z : ℤ) - ((z % m' : ℕ) : ℤ)) * ((z : ℤ) + ((z % m' : ℕ) : ℤ)) := by ring
            _ = ((m' : ℤ) * k) * ((z : ℤ) + ((z % m' : ℕ) : ℤ)) := by rw [hk]
            _ = (m' : ℤ) * (k * ((z : ℤ) + ((z % m' : ℕ) : ℤ))) := by ring
        have h3 := dvd_sub h1' (dvd_mul_of_dvd_right h2 a)
        have heq : (a * (z : ℤ) ^ 2 - b) - a * ((z : ℤ) ^ 2 - ((z % m' : ℕ) : ℤ) ^ 2)
            = a * ((z % m' : ℕ) : ℤ) ^ 2 - b := by ring
        rwa [heq] at h3
      have h2 : z / m' < e := by
        rw [Nat.div_lt_iff_lt_mul hm']
        rw [hmm] at hzm
        exact hzm
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hm'), h1⟩,
          Finset.mem_range.mpr h2⟩
    have hinj : Set.InjOn (fun z : ℕ => (z % m', z / m')) ↑S := by
      intro x _ y _ hxy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      have hx1 : x = m' * (x / m') + x % m' := (Nat.div_add_mod x m').symm
      have hy1 : y = m' * (y / m') + y % m' := (Nat.div_add_mod y m').symm
      rw [hx1, hy1, h1, h2]
    have hcard : S.card ≤ (T ×ˢ Finset.range e).card :=
      Finset.card_le_card_of_injOn (fun z : ℕ => (z % m', z / m')) hsub hinj
    rw [Finset.card_product, Finset.card_range] at hcard
    calc S.card ≤ T.card * e := hcard
      _ = e * T.card := by ring

/-- The sign of an integer does not affect being a unit after a ring cast. -/
private lemma isUnit_intCast_natAbs {R : Type*} [Ring R] (x : ℤ)
    (h : IsUnit ((x.natAbs : ℕ) : R)) : IsUnit ((x : ℤ) : R) := by
  rcases (Int.natAbs_eq_iff (a := x) (n := x.natAbs)).mp rfl with hx | hx
  · rw [hx]; simpa using h
  · rw [hx]; simpa using h.neg

/-- **The one-variable local congruence count, in divisibility form.** For `m ≥ 1`, `A ≠ 0` and
any `B : ℤ`, the number of `z ∈ {0, …, m-1}` with `m ∣ A * z ^ 2 - B` is at most
`Nat.gcd A.natAbs m * 4 ^ m.primeFactors.card * Nat.sqrt (Nat.gcd B.natAbs m)`.
(Verified numerically for `m ≤ 100`, `1 ≤ A ≤ 40`, all `B`.) This is the divisibility form of the
`ZMod`-count `#{z : ZMod m // (A : ZMod m) * z ^ 2 = (B : ZMod m)}` (via the bijection `z ↦ z.val`,
cf. `Work.FIArea2.card_range_filter_sq_mod` in `Submission/Work/FIArea2/card_sq_roots_nat.lean`,
and `Work.FIArea2.zmod_sq_eq_dvd` in `Submission/Work/FIArea2/zmod_sq_eq_dvd.lean`).
Proof route: put `e = Nat.gcd A.natAbs m`, `m' = m / e` (so `m = e * m'`).
* If `¬ e ∣ B` there are no solutions: reducing `m ∣ A z² - B` modulo `e` gives `e ∣ B`.
* Otherwise map `z ↦ z % m'`: if `m ∣ A z² - B` then, since `e ∣ A`, `e ∣ B` and `e ∣ m`,
  `m' ∣ (A / e) * (z % m') ^ 2 - (B / e)`. The preimage of a fixed `z'` has at most `e` elements
  (`z = z' + m' * k`, `0 ≤ k < e`), so the count modulo `m` is at most `e` times the corresponding
  count modulo `m'`.
* `Nat.gcd (A / e) (m / e) = 1` (`Nat.coprime_div_gcd_div_gcd`), so `(A / e : ZMod m')` is a unit;
  multiplying the equation by its inverse turns `(A/e) * z' ^ 2 = B / e` into `z' ^ 2 = b` for some
  `b` with `Nat.gcd b.natAbs m' = Nat.gcd (B / e).natAbs m'`; apply `count_sqroot_general` to `m'`.
* Finish with `e ≤ Nat.gcd A.natAbs m`, `ω(m') ≤ ω(m)`, `Nat.gcd (B / e).natAbs m' ≤ Nat.gcd B.natAbs m`. -/
theorem count_mul_sq_range_clean (m : ℕ) (hm : 1 ≤ m) (A : ℤ) (hA : A ≠ 0) (B : ℤ) :
    ((Finset.range m).filter (fun z : ℕ => (m : ℤ) ∣ A * (z : ℤ) ^ 2 - B)).card
      ≤ Nat.gcd A.natAbs m * 4 ^ m.primeFactors.card * Nat.sqrt (Nat.gcd B.natAbs m) := by
  haveI : NeZero m := ⟨by omega⟩
  set e := Nat.gcd A.natAbs m with he
  have he_pos : 0 < e := by rw [he]; exact Nat.gcd_pos_of_pos_right _ (by omega)
  have he_dvd_m : e ∣ m := by rw [he]; exact Nat.gcd_dvd_right _ _
  have he_dvd_Aabs : e ∣ A.natAbs := by rw [he]; exact Nat.gcd_dvd_left _ _
  have hm_eq : m = e * (m / e) := (Nat.mul_div_cancel' he_dvd_m).symm
  have heZ_dvd_A : (e : ℤ) ∣ A := by
    have h1 : (e : ℤ) ∣ ((A.natAbs : ℕ) : ℤ) := by exact_mod_cast he_dvd_Aabs
    exact dvd_trans h1 (Int.natAbs_dvd.mpr dvd_rfl)
  by_cases hBdvd : (e : ℤ) ∣ B
  · obtain ⟨b, hb⟩ := hBdvd
    obtain ⟨a, ha⟩ := heZ_dvd_A
    have hm'pos : 0 < m / e := by
      rcases Nat.eq_zero_or_pos (m / e) with h | h
      · rw [h, mul_zero] at hm_eq; omega
      · exact h
    haveI : NeZero (m / e) := ⟨hm'pos.ne'⟩
    -- Step 1: reduce modulo `m / e`, counting fibres of size `e`.
    have hstep1 : ((Finset.range m).filter (fun z : ℕ => (m : ℤ) ∣ A * (z : ℤ) ^ 2 - B)).card
        ≤ e * ((Finset.univ : Finset (ZMod (m / e))).filter
            (fun z => (a : ZMod (m / e)) * z ^ 2 = (b : ZMod (m / e)))).card := by
      have h0 := card_filter_dvd_le_mul m e (m / e) he_pos hm_eq A B a b ha.symm hb.symm
      rwa [card_range_filter_dvd_mul_sq (m / e) a b] at h0
    -- Step 2: `(a : ZMod (m/e))` is a unit, so the equation can be inverted.
    have hcop : a.natAbs.Coprime (m / e) := by
      have h := Nat.coprime_div_gcd_div_gcd (m := A.natAbs) (n := m) (by rw [← he]; exact he_pos)
      rw [← he] at h
      have hAe : A.natAbs / e = a.natAbs := by
        have h1 : A.natAbs = e * a.natAbs := by
          rw [ha, Int.natAbs_mul, Int.natAbs_natCast]
        rw [h1, Nat.mul_div_cancel_left _ he_pos]
      rwa [hAe] at h
    have hunit : IsUnit (a : ZMod (m / e)) :=
      isUnit_intCast_natAbs a ((ZMod.isUnit_iff_coprime a.natAbs (m / e)).mpr hcop)
    obtain ⟨w, hw⟩ := hunit
    set uv : ℕ := (↑w⁻¹ : ZMod (m / e)).val with huv
    set c : ℤ := (uv : ℤ) * b with hcdef
    have hc : (↑w⁻¹ : ZMod (m / e)) * (b : ZMod (m / e)) = (c : ZMod (m / e)) := by
      rw [hcdef, huv]
      push_cast
      rw [ZMod.natCast_zmod_val (↑w⁻¹ : ZMod (m / e))]
    have hseteq : ((Finset.univ : Finset (ZMod (m / e))).filter
          (fun z => (a : ZMod (m / e)) * z ^ 2 = (b : ZMod (m / e))))
        = ((Finset.univ : Finset (ZMod (m / e))).filter
          (fun z => z ^ 2 = (c : ZMod (m / e)))) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hw]
      constructor
      · intro h
        calc z ^ 2 = (↑w⁻¹ * ↑w) * z ^ 2 := by rw [Units.inv_mul, one_mul]
          _ = ↑w⁻¹ * (↑w * z ^ 2) := by ring
          _ = ↑w⁻¹ * (b : ZMod (m / e)) := by rw [h]
          _ = (c : ZMod (m / e)) := hc
      · intro h
        calc ↑w * z ^ 2 = ↑w * (c : ZMod (m / e)) := by rw [h]
          _ = ↑w * (↑w⁻¹ * (b : ZMod (m / e))) := by rw [← hc]
          _ = (↑w * ↑w⁻¹) * (b : ZMod (m / e)) := by ring
          _ = (b : ZMod (m / e)) := by rw [Units.mul_inv, one_mul]
    have hU : ((Finset.univ : Finset (ZMod (m / e))).filter
          (fun z => (a : ZMod (m / e)) * z ^ 2 = (b : ZMod (m / e)))).card
        ≤ 4 ^ (m / e).primeFactors.card * Nat.sqrt (Nat.gcd c.natAbs (m / e)) := by
      rw [hseteq]
      exact sqroot_count_general_aux (m / e) c
    -- Step 3: arithmetic.
    have hm'dvd : m / e ∣ m :=
      ⟨e, by rw [Nat.mul_comm]; exact (Nat.mul_div_cancel' he_dvd_m).symm⟩
    have homega : (m / e).primeFactors.card ≤ m.primeFactors.card :=
      Finset.card_le_card (Nat.primeFactors_mono hm'dvd (by omega))
    have h4 : 4 ^ (m / e).primeFactors.card ≤ 4 ^ m.primeFactors.card :=
      Nat.pow_le_pow_right (by norm_num) homega
    have hgc : Nat.gcd c.natAbs (m / e) ≤ Nat.gcd B.natAbs m := by
      set d := Nat.gcd c.natAbs (m / e) with hd
      have hdm : d ∣ m / e := Nat.gcd_dvd_right _ _
      have hdc : d ∣ c.natAbs := Nat.gcd_dvd_left _ _
      have hcval : c.natAbs = uv * b.natAbs := by
        rw [hcdef, huv, Int.natAbs_mul, Int.natAbs_natCast]
      have hunitval : uv.Coprime (m / e) := huv ▸ ZMod.val_coe_unit_coprime w⁻¹
      have hcop_d : d.Coprime uv := by
        rw [Nat.coprime_iff_gcd_eq_one]
        have h1 : Nat.gcd d uv ∣ Nat.gcd (m / e) uv :=
          Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left _ _) hdm) (Nat.gcd_dvd_right _ _)
        have h2 : Nat.gcd (m / e) uv = 1 := by
          rw [Nat.gcd_comm]; exact hunitval
        rw [h2] at h1
        exact Nat.dvd_one.mp h1
      have hdb : d ∣ b.natAbs := hcop_d.dvd_of_dvd_mul_left (hcval ▸ hdc)
      have hbB : b.natAbs ∣ B.natAbs := by
        rw [hb, Int.natAbs_mul, Int.natAbs_natCast]
        exact dvd_mul_left _ _
      refine Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega))
        (Nat.dvd_gcd (dvd_trans hdb hbB) (dvd_trans hdm hm'dvd))
    calc ((Finset.range m).filter (fun z : ℕ => (m : ℤ) ∣ A * (z : ℤ) ^ 2 - B)).card
        ≤ e * ((Finset.univ : Finset (ZMod (m / e))).filter
            (fun z => (a : ZMod (m / e)) * z ^ 2 = (b : ZMod (m / e)))).card := hstep1
      _ ≤ e * (4 ^ (m / e).primeFactors.card * Nat.sqrt (Nat.gcd c.natAbs (m / e))) :=
          Nat.mul_le_mul_left e hU
      _ = e * 4 ^ (m / e).primeFactors.card * Nat.sqrt (Nat.gcd c.natAbs (m / e)) := by ring
      _ ≤ e * 4 ^ m.primeFactors.card * Nat.sqrt (Nat.gcd B.natAbs m) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left e h4) (Nat.sqrt_le_sqrt hgc)
      _ = Nat.gcd A.natAbs m * 4 ^ m.primeFactors.card * Nat.sqrt (Nat.gcd B.natAbs m) := by
          rw [he]
  · have hempty : ((Finset.range m).filter
        (fun z : ℕ => (m : ℤ) ∣ A * (z : ℤ) ^ 2 - B)) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun z _ hz => hBdvd ?_
      have h1 : (e : ℤ) ∣ (m : ℤ) := by exact_mod_cast he_dvd_m
      have h2 : (e : ℤ) ∣ A * (z : ℤ) ^ 2 := dvd_mul_of_dvd_left heZ_dvd_A _
      have h3 := dvd_sub (dvd_trans h1 hz) h2
      rw [show A * (z : ℤ) ^ 2 - B - A * (z : ℤ) ^ 2 = -B by ring] at h3
      exact dvd_neg.mp h3
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

end Work.FIArea2.R6
