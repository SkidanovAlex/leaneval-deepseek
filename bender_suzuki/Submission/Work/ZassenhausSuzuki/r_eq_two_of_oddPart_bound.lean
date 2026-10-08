import Mathlib
import Submission.Work.ZassenhausSuzuki.pow_two_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The exponent `r` is `2` when `2 * oddPart (p ^ r - 1) ≤ p - 1`

For an odd prime `p` and an exponent `r ≥ 2`, the arithmetic hypothesis
`2 * oddPart (p ^ r - 1) ≤ p - 1` forces `r = 2`.

The proof splits according to the parity of `r`:

* `r` odd (`r ≥ 3`): writing `p ^ r - 1 = (p - 1) * S` with
  `S = ∑_{i < r} p ^ i`, the factor `S` is odd, hence `S ∣ oddPart (p ^ r - 1)`
  and therefore `oddPart (p ^ r - 1) ≥ S ≥ p + 1`, so `2 * oddPart (p ^ r - 1) > p - 1`.

* `r` even (`r ≥ 4`): the `2`-adic valuation of `p ^ r - 1` is controlled by LTE,
  `v₂(p ^ r - 1) = v₂(p - 1) + v₂(p + 1) + v₂(r) - 1`. This bounds
  `oddPart S` below by `2 ^ (v₂(p - 1) - 1)`, again giving `2 * oddPart (p ^ r - 1) > p - 1`.

All the bookkeeping is done with `Nat.factorization 2`, which is exactly the
exponent occurring in the definition of `oddPart`.
-/

namespace Work.ZassenhausSuzuki

/-- **Lifting the exponent lemma**, specialised to the prime `2`, expressed in terms
of `Nat.factorization`. For an odd prime `p` and a nonzero even exponent `r`,
`v₂ (p ^ r - 1) + 1 = v₂ (p + 1) + v₂ (p - 1) + v₂ r`. -/
lemma lte_two_pow_sub_one {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hre : Even r)
    (hr0 : r ≠ 0) :
    (p ^ r - 1).factorization 2 + 1
      = (p + 1).factorization 2 + (p - 1).factorization 2 + r.factorization 2 := by
  have hnod : ¬ 2 ∣ p := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    rintro ⟨m, hm⟩
    omega
  have key := padicValNat.pow_two_sub_one hp.one_lt hnod hr0 hre
  rw [Nat.factorization_def (p ^ r - 1) Nat.prime_two,
      Nat.factorization_def (p + 1) Nat.prime_two,
      Nat.factorization_def (p - 1) Nat.prime_two,
      Nat.factorization_def r Nat.prime_two]
  exact key

/-- Elementary growth bound used in the even case: for `p ≥ 3` and `r ≥ 4`,
`r ≤ 4 * p ^ (r - 3)`. -/
lemma r_le_four_mul_pow {p r : ℕ} (hp : 3 ≤ p) (hr : 4 ≤ r) : r ≤ 4 * p ^ (r - 3) := by
  have h3 : r ≤ 4 * 3 ^ (r - 3) := by
    induction r, hr using Nat.le_induction with
    | base => norm_num
    | succ r hr ih =>
      have h1 : (r + 1) - 3 = r - 2 := by omega
      rw [h1]
      have hpow : 3 ^ (r - 2) = 3 * 3 ^ (r - 3) := by
        rw [show r - 2 = (r - 3) + 1 by omega, pow_succ']
      rw [hpow]
      have hX : 1 ≤ 3 ^ (r - 3) := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)
      nlinarith [ih, hX]
  exact le_trans h3 (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hp (r - 3)))

/-- `(∑ i ∈ range r, p ^ i) % 2 = r % 2` for odd `p`; the geometric sum has the
parity of the number of its terms. -/
lemma geom_sum_mod_two {p : ℕ} (hp : Odd p) :
    ∀ r, (∑ i ∈ Finset.range r, p ^ i) % 2 = r % 2 := by
  intro r
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih]
    have hpn : p ^ n % 2 = 1 := Nat.odd_iff.mp (hp.pow)
    rw [hpn, Nat.add_mod]
    simp

/-- Odd exponent case: for an odd prime `p` and an odd exponent `r ≥ 3`,
`2 * oddPart (p ^ r - 1) > p - 1`. -/
lemma two_mul_oddPart_gt_of_odd_exp {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 3 ≤ r) (hro : Odd r) : p - 1 < 2 * oddPart (p ^ r - 1) := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have h1p : 1 ≤ p := le_of_lt hp.one_lt
  have hpos : 1 ≤ oddPart (p - 1) := oddPart_pos (Nat.sub_pos_of_lt hp.one_lt).ne'
  have hSmod : (∑ i ∈ Finset.range r, p ^ i) % 2 = 1 := by
    rw [geom_sum_mod_two hpodd r, Nat.odd_iff.mp hro]
  have hSodd : Odd (∑ i ∈ Finset.range r, p ^ i) := Nat.odd_iff.mpr hSmod
  have hmul : (∑ i ∈ Finset.range r, p ^ i) * (p - 1) = p ^ r - 1 :=
    geom_sum_mul_of_one_le h1p r
  have hge : p + 1 ≤ ∑ i ∈ Finset.range r, p ^ i := by
    have hsub : Finset.range 2 ⊆ Finset.range r := by
      intro i hi; simp only [Finset.mem_range] at *; omega
    have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => p ^ i) hsub
      (fun i _ _ => Nat.zero_le _)
    have h2 : (∑ i ∈ Finset.range 2, p ^ i) = p + 1 := by
      simp [Finset.sum_range_succ, Nat.add_comm]
    omega
  have hoddS : oddPart (∑ i ∈ Finset.range r, p ^ i) = ∑ i ∈ Finset.range r, p ^ i :=
    oddPart_eq_self_of_odd hSodd
  have hstep : p - 1 < 2 * (∑ i ∈ Finset.range r, p ^ i) := by
    have h1 : p - 1 < 2 * (p + 1) := by omega
    exact lt_of_lt_of_le h1 (Nat.mul_le_mul_left 2 hge)
  calc p - 1 < 2 * (∑ i ∈ Finset.range r, p ^ i) := hstep
    _ = 2 * ((∑ i ∈ Finset.range r, p ^ i) * 1) := by ring
    _ ≤ 2 * (oddPart (∑ i ∈ Finset.range r, p ^ i) * oddPart (p - 1)) := by
          rw [hoddS]; gcongr
    _ = 2 * oddPart ((∑ i ∈ Finset.range r, p ^ i) * (p - 1)) := by rw [oddPart_mul]
    _ = 2 * oddPart (p ^ r - 1) := by rw [hmul]

/-- Even exponent case: for an odd prime `p` and an even exponent `r ≥ 4`,
`2 * oddPart (p ^ r - 1) > p - 1`. -/
lemma two_mul_oddPart_gt_of_even_exp {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 4 ≤ r) (hre : Even r) : p - 1 < 2 * oddPart (p ^ r - 1) := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have h1p : 1 ≤ p := le_of_lt hp.one_lt
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp1pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hp1ne : p - 1 ≠ 0 := hp1pos.ne'
  have hrne : r ≠ 0 := by omega
  have h2p1 : 2 ∣ p - 1 := by
    obtain ⟨k, hk⟩ := hpodd
    exact ⟨k, by omega⟩
  have h2r : 2 ∣ r := even_iff_two_dvd.mp hre
  set S := ∑ i ∈ Finset.range r, p ^ i with hSdef
  set a := (p - 1).factorization 2 with hadef
  set b := (p + 1).factorization 2 with hbdef
  set c := r.factorization 2 with hcdef
  set t := (p ^ r - 1).factorization 2 with htdef
  have hSpos : S ≠ 0 := by
    rw [hSdef]
    exact ne_of_gt (Finset.sum_pos (fun i _ => pow_pos hp.pos i)
      ⟨0, Finset.mem_range.mpr (by omega)⟩)
  have hS : S * (p - 1) = p ^ r - 1 := by
    rw [hSdef]; exact geom_sum_mul_of_one_le h1p r
  have ha1 : 1 ≤ a := by
    rw [hadef]
    exact Nat.succ_le_of_lt (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hp1ne h2p1)
  have hc1 : 1 ≤ c := by
    rw [hcdef]
    exact Nat.succ_le_of_lt (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hrne h2r)
  have hlte : t + 1 = b + a + c := by
    rw [htdef, hbdef, hadef, hcdef]; exact lte_two_pow_sub_one hp hp2 hre hrne
  have hfm : t = S.factorization 2 + a := by
    have h := congrArg (fun f : ℕ →₀ ℕ => f 2) (Nat.factorization_mul hSpos hp1ne)
    rw [hS] at h
    rw [htdef, hadef]; exact h
  have hSfac : S.factorization 2 = b + c - 1 := by omega
  have hp2m1pos : 0 < p ^ 2 - 1 := Nat.sub_pos_of_lt (by nlinarith [hp.two_le])
  have hsq : (p ^ 2 - 1).factorization 2 = a + b := by
    have h1 : p ^ 2 - 1 = (p + 1) * (p - 1) := by simpa using Nat.sq_sub_sq p 1
    have h2 : ((p + 1) * (p - 1)).factorization 2
        = (p + 1).factorization 2 + (p - 1).factorization 2 := by
      have := congrArg (fun f : ℕ →₀ ℕ => f 2)
        (Nat.factorization_mul (by positivity : p + 1 ≠ 0) hp1ne)
      simpa only [Finsupp.add_apply] using this
    rw [h1, h2, hadef, hbdef]
    ring
  have hdiv1 : 2 ^ (a + b) ∣ p ^ 2 - 1 := by
    rw [hsq.symm]
    exact ⟨(p ^ 2 - 1) / 2 ^ ((p ^ 2 - 1).factorization 2),
      (Nat.ordProj_mul_ordCompl_eq_self (p ^ 2 - 1) 2).symm⟩
  have hle1 : 2 ^ (a + b) ≤ p ^ 2 - 1 := Nat.le_of_dvd hp2m1pos hdiv1
  have hdiv2 : 2 ^ c ∣ r := by
    rw [hcdef]
    exact ⟨r / 2 ^ (r.factorization 2), (Nat.ordProj_mul_ordCompl_eq_self r 2).symm⟩
  have hle2 : 2 ^ c ≤ r := Nat.le_of_dvd (by omega) hdiv2
  have hpow4 : 4 * 2 ^ (a + b + c - 2) = 2 ^ (a + b) * 2 ^ c := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add,
        show 2 + (a + b + c - 2) = (a + b) + c by omega, pow_add]
  have hbig : 4 * 2 ^ (a + b + c - 2) < p ^ 2 * r := by
    rw [hpow4]
    calc 2 ^ (a + b) * 2 ^ c ≤ (p ^ 2 - 1) * r := Nat.mul_le_mul hle1 hle2
      _ < p ^ 2 * r := by
            rw [Nat.mul_lt_mul_right (by omega : 0 < r)]; omega
  have hSge : p ^ (r - 1) ≤ S := by
    rw [hSdef]
    exact Finset.single_le_sum (f := fun i => p ^ i) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
  have hkey : 2 ^ (a + b + c - 2) < S := by
    by_contra hle
    rw [not_lt] at hle
    have h4S : 4 * S ≤ 4 * 2 ^ (a + b + c - 2) := Nat.mul_le_mul_left 4 hle
    have hlt : 4 * p ^ (r - 1) < p ^ 2 * r :=
      lt_of_le_of_lt (Nat.mul_le_mul_left 4 hSge) (lt_of_le_of_lt h4S hbig)
    have hlt2 : 4 * p ^ (r - 3) < r := by
      have h1 : p ^ (r - 1) = p ^ 2 * p ^ (r - 3) := by rw [← pow_add]; congr 1; omega
      rw [h1] at hlt
      have h2 : 4 * (p ^ 2 * p ^ (r - 3)) = p ^ 2 * (4 * p ^ (r - 3)) := by ring
      rw [h2] at hlt
      exact Nat.lt_of_mul_lt_mul_left hlt
    have hL5 : r ≤ 4 * p ^ (r - 3) := r_le_four_mul_pow hp3 hr
    omega
  have hSeq : 2 ^ (b + c - 1) * oddPart S = S := by
    have h := Nat.ordProj_mul_ordCompl_eq_self S 2
    rw [hSfac] at h
    simpa [oddPart, hSfac] using h
  have hpowkey : 2 ^ (a + b + c - 2) = 2 ^ (a - 1) * 2 ^ (b + c - 1) := by
    rw [← pow_add]; congr 1; omega
  have hoddS_gt : 2 ^ (a - 1) < oddPart S := by
    have h := hkey
    rw [hpowkey, ← hSeq] at h
    rw [mul_comm (2 ^ (a - 1)) (2 ^ (b + c - 1))] at h
    exact Nat.lt_of_mul_lt_mul_left h
  have hp1fac : 2 ^ a * oddPart (p - 1) = p - 1 := by
    rw [hadef]
    unfold oddPart
    exact Nat.ordProj_mul_ordCompl_eq_self (p - 1) 2
  have h2apow : 2 ^ a = 2 * 2 ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega]
    rw [pow_succ']
  calc p - 1 = 2 ^ a * oddPart (p - 1) := hp1fac.symm
    _ = 2 * 2 ^ (a - 1) * oddPart (p - 1) := by rw [h2apow]
    _ = 2 * (2 ^ (a - 1) * oddPart (p - 1)) := by ring
    _ < 2 * (oddPart S * oddPart (p - 1)) := by
          apply Nat.mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℕ) < 2)
          exact Nat.mul_lt_mul_of_pos_right hoddS_gt (oddPart_pos hp1ne)
    _ = 2 * oddPart (S * (p - 1)) := by rw [oddPart_mul]
    _ = 2 * oddPart (p ^ r - 1) := by rw [hS]

theorem r_eq_two_of_oddPart_bound {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hr : 2 ≤ r) (h : 2 * oddPart (p ^ r - 1) ≤ p - 1) : r = 2 := by
  by_contra hne
  have hr3 : 3 ≤ r := by omega
  rcases Nat.even_or_odd r with hre | hro
  · have hr4 : 4 ≤ r := by obtain ⟨k, hk⟩ := hre; omega
    have := two_mul_oddPart_gt_of_even_exp hp hp2 hr4 hre
    omega
  · have := two_mul_oddPart_gt_of_odd_exp hp hp2 hr3 hro
    omega

end Work.ZassenhausSuzuki
