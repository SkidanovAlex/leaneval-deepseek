import Mathlib
import Submission.Work.FIArea1.L51Count

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local bounds for the refined quadratic-congruence count (`FI` §9)

The two prime-power bounds which, multiplied over the prime factors of `d`, give the refined local
count of `Submission/Work/FIArea1/card_sq_congr_l51.lean`.  `Nc` (see
`Submission/Work/FIArea1/L51Count.lean`) is the total version of the quadratic congruence count of
*FI* §9:

* `Nc_pow_le_of_not_dvd`: the case `p ∤ ab`, `Nc (p^e) a b ≤ (e+1)·p^e`;
* `Nc_pow_le_of_dvd`: the case `p ∣ ab`, `Nc (p^e) a b ≤ (e+1)·p^e·p^(e/2)` (the sharp `p`-part).

The low-level input is the prime-power recursion of `Submission/Work/FIArea1/L51Rec.lean`.
-/

namespace Work.FIArea1

open Finset

attribute [local instance] Classical.propDecidable

/-- In the field `ZMod p` (`p` prime) the equation `b y² = c` has at most two solutions. -/
lemma card_sq_eq_le_two_zmod {p : ℕ} [NeZero p] (hp : p.Prime) (b c : ZMod p) (hb : b ≠ 0) :
    ((Finset.univ : Finset (ZMod p)).filter (fun y => b * y ^ 2 = c)).card ≤ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Finset.eq_empty_or_nonempty
    ((Finset.univ : Finset (ZMod p)).filter (fun y => b * y ^ 2 = c)) with h | ⟨y₀, hy₀⟩
  · rw [h]; simp
  · have hsub : ((Finset.univ : Finset (ZMod p)).filter (fun y => b * y ^ 2 = c))
        ⊆ ({y₀, -y₀} : Finset (ZMod p)) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy hy₀
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have h0 : b * (y ^ 2 - y₀ ^ 2) = 0 := by rw [mul_sub, hy, hy₀, sub_self]
      have h1 : b * ((y - y₀) * (y + y₀)) = 0 := by rw [← h0]; ring
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hb
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · left; linear_combination h3
        · right; linear_combination h3
    calc ((Finset.univ : Finset (ZMod p)).filter (fun y => b * y ^ 2 = c)).card
        ≤ ({y₀, -y₀} : Finset (ZMod p)).card := Finset.card_le_card hsub
      _ ≤ 2 := by
          refine le_trans (Finset.card_insert_le y₀ ({-y₀} : Finset (ZMod p))) ?_
          simp

/-- **The modulus `p` case of `Nc_pow_le_of_not_dvd`**: for `p ∤ b`, the congruence
`aγ₁² ≡ bγ₂² (mod p)` has at most `2p` solutions, because every fibre over `γ₁` has at most two
points (`b` is a unit and `ZMod p` is a field). -/
lemma Nc_prime_le_of_not_dvd (p a b : ℕ) (hp : p.Prime) (hb : ¬ p ∣ b) : Nc p a b ≤ 2 * p := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [Nc_eq_Ncount_of_ne p hp.ne_zero a b]
  rw [Work.FIArea2.Ncount]
  set S : Finset (ZMod p × ZMod p) := (Finset.univ.filter
      (fun z => (a : ZMod p) * z.1 ^ 2 = (b : ZMod p) * z.2 ^ 2)) with hS
  have hbb : (b : ZMod p) ≠ 0 := fun h => hb ((CharP.cast_eq_zero_iff (ZMod p) p b).mp h)
  have hsum : S.card = ∑ x ∈ (Finset.univ : Finset (ZMod p)),
      (S.filter (fun z => z.1 = x)).card := by
    refine Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
      (t := (Finset.univ : Finset (ZMod p))) (fun z _ => Finset.mem_univ _)
  have hfiber : ∀ x : ZMod p, (S.filter (fun z => z.1 = x)).card ≤
      ((Finset.univ : Finset (ZMod p)).filter
        (fun y => (b : ZMod p) * y ^ 2 = (a : ZMod p) * x ^ 2)).card := by
    intro x
    refine Finset.card_le_card_of_injOn (fun z => z.2) ?_ ?_
    · intro z hz
      simp only [Finset.mem_coe, hS, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hz.2]
      exact hz.1.symm
    · intro z hz w hw h
      simp only [Finset.mem_coe, hS, Finset.mem_filter, Finset.mem_univ, true_and] at hz hw
      exact Prod.ext (by rw [hz.2, hw.2]) h
  calc S.card
      = ∑ x ∈ (Finset.univ : Finset (ZMod p)), (S.filter (fun z => z.1 = x)).card := hsum
    _ ≤ ∑ x ∈ (Finset.univ : Finset (ZMod p)), 2 := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        exact le_trans (hfiber x) (card_sq_eq_le_two_zmod hp (b : ZMod p) ((a : ZMod p) * x ^ 2) hbb)
    _ = 2 * p := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
        ring

/-- The arithmetic core of the induction in `Nc_pow_le_of_not_dvd`. -/
lemma arith_not_dvd {p e c : ℕ} (he : 2 ≤ e) (hc : c * (p - 1) ≤ 2 * p) :
    p ^ 2 * ((e - 1) * p ^ (e - 2)) + c * (p ^ e - p ^ (e - 1)) ≤ (e + 1) * p ^ e := by
  have h2 : p ^ 2 * p ^ (e - 2) = p ^ e := by
    rw [← pow_add]; congr 1; omega
  have hA : p ^ 2 * ((e - 1) * p ^ (e - 2)) = (e - 1) * p ^ e := by
    calc p ^ 2 * ((e - 1) * p ^ (e - 2)) = (p ^ 2 * p ^ (e - 2)) * (e - 1) := by ring
      _ = p ^ e * (e - 1) := by rw [h2]
      _ = (e - 1) * p ^ e := by ring
  have hsplit : p ^ e = p ^ (e - 1) * p := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos (by omega : 0 < e)]
    rw [pow_succ]
    simp [Nat.pred_eq_sub_one]
  have hsub : p ^ e - p ^ (e - 1) = p ^ (e - 1) * (p - 1) := by
    rw [hsplit, Nat.mul_sub_left_distrib, Nat.mul_one]
  have hB : c * (p ^ e - p ^ (e - 1)) ≤ 2 * p ^ e := by
    rw [hsub]
    calc c * (p ^ (e - 1) * (p - 1)) = (c * (p - 1)) * p ^ (e - 1) := by ring
      _ ≤ (2 * p) * p ^ (e - 1) := Nat.mul_le_mul_right _ hc
      _ = 2 * p ^ e := by rw [hsplit]; ring
  calc p ^ 2 * ((e - 1) * p ^ (e - 2)) + c * (p ^ e - p ^ (e - 1))
      = (e - 1) * p ^ e + c * (p ^ e - p ^ (e - 1)) := by rw [hA]
    _ ≤ (e - 1) * p ^ e + 2 * p ^ e := add_le_add le_rfl hB
    _ = (e + 1) * p ^ e := by
        rw [← add_mul, show e - 1 + 2 = e + 1 by omega]

lemma ite_mul_pred_le (p : ℕ) : (if p = 2 then 4 else 2) * (p - 1) ≤ 2 * p := by
  by_cases h : p = 2
  · subst h; norm_num
  · rw [if_neg h]; omega

/-- **Local bound, case `p ∤ ab`** (*FI* Lemma 9.1, sharp form): for `p ∤ ab` and every `e`,
`Nc (p^e) a b ≤ (e+1)·p^e`.  Proof by strong induction on `e` from the recursion
`N(p^e) ≤ p²N(p^{e-2}) + c(p^e - p^{e-1})` of `L51Rec`: the induced bound is exactly
`(e+1)p^e` since `c(p-1) ≤ 2p` for `c = 4` (`p = 2`) and `c = 2` (`p` odd). -/
lemma Nc_pow_le_of_not_dvd (p : ℕ) (hp : p.Prime) :
    ∀ e a b : ℕ, ¬ p ∣ a → ¬ p ∣ b → Nc (p ^ e) a b ≤ (e + 1) * p ^ e := by
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro a b ha hb
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      rw [pow_zero, Nc_eq_Ncount_of_ne 1 one_ne_zero a b, Ncount_one]
      norm_num
    · rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr he.ne') with h1 | h2
      · subst h1
        rw [pow_one]
        refine le_trans (Nc_prime_le_of_not_dvd p a b hp hb) ?_
        norm_num
      · have he2 : 2 ≤ e := h2
        have hpe : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
        have hpe2 : p ^ (e - 2) ≠ 0 := pow_ne_zero _ hp.ne_zero
        haveI : NeZero (p ^ e) := ⟨hpe⟩
        haveI : NeZero (p ^ (e - 2)) := ⟨hpe2⟩
        rw [Nc_eq_Ncount_of_ne (p ^ e) hpe a b]
        have hrec := Ncount_pow_not_dvd_not_dvd (p := p) (e := e) hp he2 ha hb
        have hih := ih (e - 2) (by omega) a b ha hb
        rw [Nc_eq_Ncount_of_ne (p ^ (e - 2)) hpe2 a b] at hih
        have hih' : Work.FIArea2.Ncount (p ^ (e - 2)) a b ≤ (e - 1) * p ^ (e - 2) := by
          have hh : e - 2 + 1 = e - 1 := by omega
          rwa [hh] at hih
        refine le_trans hrec ?_
        refine le_trans (add_le_add (Nat.mul_le_mul_left _ hih') le_rfl) ?_
        exact arith_not_dvd he2 (ite_mul_pred_le p)



/-- If `p^e ∣ a` then `p^(e-k) ∣ a / p^k` (for `p > 0`, `k ≤ e`). -/
lemma pow_sub_dvd_div {p e k a : ℕ} (hp : 0 < p) (hk : k ≤ e) (ha : p ^ e ∣ a) :
    p ^ (e - k) ∣ a / p ^ k := by
  obtain ⟨c, rfl⟩ := ha
  refine ⟨c, ?_⟩
  rw [mul_comm (p ^ e) c, Nat.mul_div_assoc c (pow_dvd_pow p hk), Nat.pow_div hk hp]
  ring

/-- Arithmetic step: `p·(p²·((e-1)·p^(e-2)·p^((e-2)/2))) ≤ (e+1)·p^e·p^(e/2)` (`e ≥ 3`). -/
lemma arith_pow1 {p e : ℕ} (hp : 1 ≤ p) (he : 3 ≤ e) :
    p * (p ^ 2 * ((e - 2 + 1) * p ^ (e - 2) * p ^ ((e - 2) / 2)))
      ≤ (e + 1) * p ^ e * p ^ (e / 2) := by
  have hcoe : e - 2 + 1 = e - 1 := by omega
  have hpow : p * (p ^ 2 * (p ^ (e - 2) * p ^ ((e - 2) / 2))) = p ^ e * p ^ (e / 2) := by
    have h1 : p ^ 2 * p ^ (e - 2) = p ^ e := by rw [← pow_add]; congr 1; omega
    have h2 : p * p ^ ((e - 2) / 2) = p ^ (e / 2) := by
      rw [mul_comm, ← pow_succ]; congr 1; omega
    calc p * (p ^ 2 * (p ^ (e - 2) * p ^ ((e - 2) / 2)))
        = p ^ 2 * (p ^ (e - 2) * (p * p ^ ((e - 2) / 2))) := by ring
      _ = p ^ 2 * (p ^ (e - 2) * p ^ (e / 2)) := by rw [h2]
      _ = (p ^ 2 * p ^ (e - 2)) * p ^ (e / 2) := by ring
      _ = p ^ e * p ^ (e / 2) := by rw [h1]
  rw [hcoe]
  calc p * (p ^ 2 * ((e - 1) * p ^ (e - 2) * p ^ ((e - 2) / 2)))
      = (e - 1) * (p * (p ^ 2 * (p ^ (e - 2) * p ^ ((e - 2) / 2)))) := by ring
    _ ≤ (e + 1) * (p * (p ^ 2 * (p ^ (e - 2) * p ^ ((e - 2) / 2)))) :=
        Nat.mul_le_mul_right _ (by omega)
    _ = (e + 1) * (p ^ e * p ^ (e / 2)) := by rw [hpow]
    _ = (e + 1) * p ^ e * p ^ (e / 2) := by ring

/-- Arithmetic step: `p·(p²·((e-1)·p^(e-2))) ≤ (e+1)·p^e·p^(e/2)` (`e ≥ 3`). -/
lemma arith_pow2 {p e : ℕ} (hp : 1 ≤ p) (he : 3 ≤ e) :
    p * (p ^ 2 * ((e - 2 + 1) * p ^ (e - 2))) ≤ (e + 1) * p ^ e * p ^ (e / 2) := by
  have hcoe : e - 2 + 1 = e - 1 := by omega
  have hpow : p * (p ^ 2 * p ^ (e - 2)) = p ^ e * p := by
    have h1 : p ^ 2 * p ^ (e - 2) = p ^ e := by rw [← pow_add]; congr 1; omega
    calc p * (p ^ 2 * p ^ (e - 2)) = p * p ^ e := by rw [h1]
      _ = p ^ e * p := by ring
  have hle : p ≤ p ^ (e / 2) := by
    simpa using (Nat.pow_le_pow_right hp (show 1 ≤ e / 2 by omega) : p ^ 1 ≤ p ^ (e / 2))
  rw [hcoe]
  calc p * (p ^ 2 * ((e - 1) * p ^ (e - 2)))
      = (e - 1) * (p * (p ^ 2 * p ^ (e - 2))) := by ring
    _ ≤ (e + 1) * (p * (p ^ 2 * p ^ (e - 2))) := Nat.mul_le_mul_right _ (by omega)
    _ = (e + 1) * (p ^ e * p) := by rw [hpow]
    _ = (e + 1) * p ^ e * p := by ring
    _ ≤ (e + 1) * p ^ e * p ^ (e / 2) := Nat.mul_le_mul_left _ hle

/-- Arithmetic step: `p·((e-1+1)·p^(e-1)·p^((e-1)/2)) ≤ (e+1)·p^e·p^(e/2)` (`e ≥ 2`). -/
lemma arith_div_unit {p e : ℕ} (hp : 1 ≤ p) (he : 2 ≤ e) :
    p * ((e - 1 + 1) * p ^ (e - 1) * p ^ ((e - 1) / 2)) ≤ (e + 1) * p ^ e * p ^ (e / 2) := by
  have hcoe : e - 1 + 1 = e := by omega
  rw [hcoe]
  have hpow : p * (e * p ^ (e - 1)) = e * p ^ e := by
    have h2 : p * p ^ (e - 1) = p ^ e := by
      rw [mul_comm, ← pow_succ, show e - 1 + 1 = e by omega]
    calc p * (e * p ^ (e - 1)) = e * (p * p ^ (e - 1)) := by ring
      _ = e * p ^ e := by rw [h2]
  calc p * (e * p ^ (e - 1) * p ^ ((e - 1) / 2))
      = (p * (e * p ^ (e - 1))) * p ^ ((e - 1) / 2) := by ring
    _ = (e * p ^ e) * p ^ ((e - 1) / 2) := by rw [hpow]
    _ = e * (p ^ e * p ^ ((e - 1) / 2)) := by ring
    _ ≤ e * (p ^ e * p ^ (e / 2)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hp (Nat.div_le_div_right (by omega))))
    _ ≤ (e + 1) * (p ^ e * p ^ (e / 2)) := Nat.mul_le_mul_right _ (by omega)
    _ = (e + 1) * p ^ e * p ^ (e / 2) := by ring

/-- Arithmetic step: the `e = 2` case, `p·(p^(e-1)·p^(e-1)) ≤ (e+1)·p^e·p^(e/2)`. -/
lemma arith_pow2_small {p e : ℕ} (he : e = 2) :
    p * (p ^ (e - 1) * p ^ (e - 1)) ≤ (e + 1) * p ^ e * p ^ (e / 2) := by
  subst he
  norm_num
  calc p * (p * p) ≤ 3 * (p * (p * p)) := by nlinarith
    _ = 3 * p ^ 2 * p := by ring

/-- **The `e = 1` count for `p ∣ a`, `p ∤ b`**: the congruence reads `bγ₂² ≡ 0 (mod p)`, so
`γ₂ ≡ 0` and the count is exactly `p`. -/
lemma Nc_prime_dvd_left (p a b : ℕ) (hp : p.Prime) (ha : p ∣ a) (hb : ¬ p ∣ b) :
    Nc p a b = p := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nc_eq_Ncount_of_ne p hp.ne_zero a b, Work.FIArea2.Ncount]
  have ha0 : (a : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p a).mpr ha
  have hb0 : (b : ZMod p) ≠ 0 := fun h => hb ((CharP.cast_eq_zero_iff (ZMod p) p b).mp h)
  have hset : (Finset.univ.filter (fun z : ZMod p × ZMod p =>
      (a : ZMod p) * z.1 ^ 2 = (b : ZMod p) * z.2 ^ 2))
      = (Finset.univ : Finset (ZMod p)) ×ˢ ({0} : Finset (ZMod p)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    constructor
    · intro h
      have h2 : (b : ZMod p) * z.2 ^ 2 = 0 := by rw [← h, ha0, zero_mul]
      have h3 : z.2 ^ 2 = 0 := (mul_eq_zero.mp h2).resolve_left hb0
      exact sq_eq_zero_iff.mp h3
    · intro h
      rw [h, ha0]; ring
  rw [hset, Finset.card_product, Finset.card_univ, Finset.card_singleton, ZMod.card, mul_one]

/-- **The case `p^e ∣ a` of the local bound**: if `p^e` divides `a` and `p ∤ b`, then
`Nc (p^e) a b ≤ (e+1)·p^e·p^(e/2)` (the congruence is `bγ₂² ≡ 0 (mod p^e)`, whose exact count is
`p^e·p^(e/2)`).  Proved by strong induction on `e`: the reduction (ii) of `L51Rec` gives
`N(p^e) = p·N(p^{e-1}, a/p, pb)`, and for `e ≥ 3` the reduction (i) applied at modulus `p^(e-1)`
gives `N(p^{e-1}, a/p, pb) = p²·N(p^{e-2}, a/p², b)`, where `p^{e-2} ∣ a/p²`, so the induction
hypothesis applies (uniformly in the divisibility pattern, since its hypothesis is only
`p^{e-2} ∣ a/p²`). -/
lemma Nc_pow_le_of_pow_dvd_left (p : ℕ) (hp : p.Prime) :
    ∀ e a b : ℕ, p ^ e ∣ a → ¬ p ∣ b → Nc (p ^ e) a b ≤ (e + 1) * p ^ e * p ^ (e / 2) := by
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro a b ha hb
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      rw [pow_zero, Nc_eq_Ncount_of_ne 1 one_ne_zero a b, Ncount_one]
      norm_num
    · rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr he.ne') with h1 | h2
      · subst h1
        rw [pow_one, Nc_prime_dvd_left p a b hp (by simpa using ha) hb]
        rw [show (1 : ℕ) / 2 = 0 by norm_num, pow_zero, mul_one]
        omega
      · have he2 : 2 ≤ e := h2
        have hpa : p ∣ a := by
          have h : p ^ 1 ∣ a := dvd_trans (pow_dvd_pow p (by omega : 1 ≤ e)) ha
          rwa [pow_one] at h
        have hpe : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
        have hpe1 : p ^ (e - 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
        haveI : NeZero (p ^ e) := ⟨hpe⟩
        haveI : NeZero (p ^ (e - 1)) := ⟨hpe1⟩
        rw [Nc_eq_Ncount_of_ne (p ^ e) hpe a b]
        have hrec := Ncount_pow_dvd_not_dvd (p := p) (e := e) hp he2 hpa hb
        rw [hrec]
        rcases Nat.eq_or_lt_of_le he2 with h2' | h3
        · have hle : Work.FIArea2.Ncount (p ^ (e - 1)) (a / p) (p * b)
              ≤ p ^ (e - 1) * p ^ (e - 1) := by
            have h := Nc_le (p ^ (e - 1)) (a / p) (p * b)
            rw [Nc_eq_Ncount_of_ne (p ^ (e - 1)) hpe1] at h
            exact h
          exact le_trans (Nat.mul_le_mul_left _ hle) (arith_pow2_small h2'.symm)
        · have he3 : 3 ≤ e := h3
          have hpp : p ∣ a / p := by
            have h : p ^ (e - 1) ∣ a / p ^ 1 := pow_sub_dvd_div hp.pos (by omega : 1 ≤ e) ha
            rw [pow_one] at h
            exact dvd_trans (by simpa using (pow_dvd_pow p (by omega : 1 ≤ e - 1) : p ^ 1 ∣ p ^ (e - 1))) h
          haveI : NeZero (p ^ (e - 1 - 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
          have hrec2 := Ncount_pow_dvd_dvd (p := p) (e := e - 1) hp (by omega : 2 ≤ e - 1)
            hpp (dvd_mul_right p b)
          rw [hrec2, Nat.mul_div_right b hp.pos]
          have hne2 : p ^ (e - 2) ≠ 0 := pow_ne_zero _ hp.ne_zero
          have hp2dvd : p ^ (e - 2) ∣ (a / p) / p := by
            rw [Nat.div_div_eq_div_mul, show p * p = p ^ 2 by ring]
            exact pow_sub_dvd_div hp.pos (by omega : 2 ≤ e) ha
          haveI : NeZero (p ^ (e - 2)) := ⟨hne2⟩
          have hih : Work.FIArea2.Ncount (p ^ (e - 1 - 1)) ((a / p) / p) b ≤
              (e - 2 + 1) * p ^ (e - 2) * p ^ ((e - 2) / 2) := by
            have h := ih (e - 2) (by omega) ((a / p) / p) b hp2dvd hb
            rw [Nc_eq_Ncount_of_ne (p ^ (e - 2)) hne2] at h
            exact h
          refine le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hih)) ?_
          exact arith_pow1 hp.one_le he3

/-- **Local bound, case `p ∣ a`, `p ∤ b`**: `Nc (p^e) a b ≤ (e+1)·p^e·p^(e/2)`.  Strong induction
on `e`: the reduction (ii) gives `N(p^e) = p·N(p^{e-1}, a/p, pb)`; if `p ∤ a/p` the induction
hypothesis applies to the swapped pair `(pb, a/p)`, while if `p ∣ a/p` the reduction (i) gives
`N(p^{e-1}, a/p, pb) = p²N(p^{e-2}, a/p², b)` and one uses the induction hypothesis (if
`p ∣ a/p²`) or the case `p ∤ ab` (if not). -/
lemma Nc_pow_le_of_dvd_left (p : ℕ) (hp : p.Prime) :
    ∀ e a b : ℕ, p ∣ a → ¬ p ∣ b → Nc (p ^ e) a b ≤ (e + 1) * p ^ e * p ^ (e / 2) := by
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro a b ha hb
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      rw [pow_zero, Nc_eq_Ncount_of_ne 1 one_ne_zero a b, Ncount_one]
      norm_num
    · rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr he.ne') with h1 | h2
      · subst h1
        rw [pow_one, Nc_prime_dvd_left p a b hp ha hb,
          show (1 : ℕ) / 2 = 0 by norm_num, pow_zero, mul_one]
        omega
      · have he2 : 2 ≤ e := h2
        have hpe : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
        have hpe1 : p ^ (e - 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
        haveI : NeZero (p ^ e) := ⟨hpe⟩
        haveI : NeZero (p ^ (e - 1)) := ⟨hpe1⟩
        rw [Nc_eq_Ncount_of_ne (p ^ e) hpe a b]
        have hrec := Ncount_pow_dvd_not_dvd (p := p) (e := e) hp he2 ha hb
        rw [hrec]
        by_cases hpp : p ∣ a / p
        · rcases Nat.eq_or_lt_of_le he2 with h2' | h3
          · have hle : Work.FIArea2.Ncount (p ^ (e - 1)) (a / p) (p * b)
                ≤ p ^ (e - 1) * p ^ (e - 1) := by
              have h := Nc_le (p ^ (e - 1)) (a / p) (p * b)
              rw [Nc_eq_Ncount_of_ne (p ^ (e - 1)) hpe1] at h
              exact h
            exact le_trans (Nat.mul_le_mul_left _ hle) (arith_pow2_small h2'.symm)
          · have he3 : 3 ≤ e := h3
            haveI : NeZero (p ^ (e - 1 - 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
            have hrec2 := Ncount_pow_dvd_dvd (p := p) (e := e - 1) hp (by omega : 2 ≤ e - 1)
              hpp (dvd_mul_right p b)
            rw [hrec2, Nat.mul_div_right b hp.pos]
            by_cases hpp2 : p ∣ (a / p) / p
            · have hne2 : p ^ (e - 2) ≠ 0 := pow_ne_zero _ hp.ne_zero
              haveI : NeZero (p ^ (e - 2)) := ⟨hne2⟩
              have hih : Work.FIArea2.Ncount (p ^ (e - 1 - 1)) ((a / p) / p) b ≤
                  (e - 2 + 1) * p ^ (e - 2) * p ^ ((e - 2) / 2) := by
                have h := ih (e - 2) (by omega) ((a / p) / p) b hpp2 hb
                rw [Nc_eq_Ncount_of_ne (p ^ (e - 2)) hne2] at h
                exact h
              refine le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hih)) ?_
              exact arith_pow1 hp.one_le he3
            · have hL1 : Work.FIArea2.Ncount (p ^ (e - 1 - 1)) ((a / p) / p) b
                  ≤ (e - 2 + 1) * p ^ (e - 2) := by
                have h := Nc_pow_le_of_not_dvd p hp (e - 2) ((a / p) / p) b hpp2 hb
                rw [Nc_eq_Ncount_of_ne (p ^ (e - 2)) (pow_ne_zero _ hp.ne_zero)] at h
                exact h
              refine le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hL1)) ?_
              exact arith_pow2 hp.one_le he3
        · have hswap : Work.FIArea2.Ncount (p ^ (e - 1)) (a / p) (p * b)
              = Work.FIArea2.Ncount (p ^ (e - 1)) (p * b) (a / p) :=
            Ncount_swap (p ^ (e - 1)) (a / p) (p * b)
          rw [hswap]
          have hih := ih (e - 1) (by omega) (p * b) (a / p) (dvd_mul_right p b) hpp
          rw [Nc_eq_Ncount_of_ne (p ^ (e - 1)) hpe1] at hih
          refine le_trans (Nat.mul_le_mul_left _ hih) ?_
          exact arith_div_unit hp.one_le he2

/-- **Local bound, case `p ∣ ab`** (exactly one of `a`, `b` divisible by `p`), by symmetry in the
two coefficients. -/
lemma Nc_pow_le_of_dvd (p : ℕ) (hp : p.Prime) :
    ∀ e a b : ℕ, ((p ∣ a ∧ ¬ p ∣ b) ∨ (¬ p ∣ a ∧ p ∣ b)) →
      Nc (p ^ e) a b ≤ (e + 1) * p ^ e * p ^ (e / 2) := by
  intro e a b h
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Nc_pow_le_of_dvd_left p hp e a b ha hb
  · rw [Nc_swap]
    exact Nc_pow_le_of_dvd_left p hp e b a hb ha

end Work.FIArea1
