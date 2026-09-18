import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.ModEq

open scoped Nat

namespace Commons.NumberTheory.DuffinSchaeffer

set_option linter.unusedVariables false

/-- local: `(x+e)%r = ((x*q)%r + e)%r` -/
private lemma add_mul_mod_eq (b q e r : ℕ) : (b * q + e) % r = ((b * q) % r + e) % r := by
  have h1 : (b * q + e) % r = ((b * q) % r + e % r) % r := by rw [Nat.add_mod]
  have h2 : ((b * q) % r + e) % r = ((b * q) % r + e % r) % r := by
    rw [Nat.add_mod]
    rw [Nat.mod_mod]
  rw [h2]
  exact h1

private lemma cong_iff (q r e a b : ℕ) (hqr : q.Coprime r) :
    (a * r) % (q * r) = (b * q + e) % (q * r) ↔
      (a * r) % q = e % q ∧ (b * q + e) % r = 0 := by
  have hbq : (b * q + e) % q = e % q := by
    rw [add_comm, mul_comm]
    exact Nat.add_mul_mod_self_left e q b
  have har : (a * r) % r = 0 := by
    exact Nat.mul_mod_left a r
  constructor
  · intro h
    have hmod : a * r ≡ b * q + e [MOD q] ∧ a * r ≡ b * q + e [MOD r] := by
      apply (Nat.modEq_and_modEq_iff_modEq_mul hqr).mpr
      exact h
    have hq' : (a * r) % q = (b * q + e) % q := hmod.1
    have hr' : (a * r) % r = (b * q + e) % r := hmod.2
    exact ⟨hq'.trans hbq, hr'.symm.trans har⟩
  · intro h
    have hq' : (a * r) % q = (b * q + e) % q := h.1.trans hbq.symm
    have hr' : (a * r) % r = (b * q + e) % r := har.trans h.2.symm
    apply (Nat.modEq_and_modEq_iff_modEq_mul hqr).mp
    exact ⟨hq', hr'⟩

private lemma card_coprime_eq_single (n c : ℕ) (hn : 0 < n) (hc : c < n) :
    ((Finset.range n).filter (fun x => x.gcd n = 1 ∧ x = c)).card =
      if c.gcd n = 1 then 1 else 0 := by
  classical
  by_cases hg : c.gcd n = 1
  · have hset : (Finset.range n).filter (fun x => x.gcd n = 1 ∧ x = c) = {c} := by
      ext x
      constructor
      · intro hx
        have hxm := (Finset.mem_filter.mp hx)
        exact Finset.mem_singleton.mpr hxm.2.2
      · intro hx
        rw [Finset.mem_singleton] at hx
        subst x
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, hg, rfl⟩
    rw [hset, if_pos hg]
    simp
  · have hset : (Finset.range n).filter (fun x => x.gcd n = 1 ∧ x = c) = ∅ := by
      ext x
      constructor
      · intro hx
        rcases (Finset.mem_filter.mp hx) with ⟨hxr, hxg, hxeq⟩
        exfalso
        exact hg (by rwa [hxeq] at hxg)
      · intro hx
        simp at hx
    rw [hset, if_neg hg]
    simp

/-- for `x < p`, the congruence `x + e ≡ 0 (mod p)` singles out `x = (p - e%p) % p` -/
private lemma mod_add_eq_zero_iff (p e x : ℕ) (hp : 0 < p) (hx : x < p) :
    (x + e) % p = 0 ↔ x = (p - e % p) % p := by
  have hxmod : x % p = x := Nat.mod_eq_of_lt hx
  have h1 : (x + e) % p = (x % p + e % p) % p := Nat.add_mod x e p
  have h2 : (x % p + e % p) % p = (x + e % p) % p := by rw [hxmod]
  have hred : (x + e) % p = (x + e % p) % p := h1.trans h2
  rw [hred]
  have hep : e % p < p := Nat.mod_lt e hp
  constructor
  · intro h
    by_cases hep0 : e % p = 0
    · have hx0 : x = 0 := by
        simpa [hep0, hxmod] using h
      simp [hep0, hx0]
    · have hge : p ≤ x + e % p := by
        by_contra hnot
        have hlt : x + e % p < p := lt_of_not_ge hnot
        have : (x + e % p) % p = x + e % p := Nat.mod_eq_of_lt hlt
        rw [this] at h
        omega
      have hlt2 : x + e % p - p < p := by omega
      have hm : (x + e % p) % p = (x + e % p - p) % p := Nat.mod_eq_sub_mod hge
      rw [hm] at h
      have hxrp : x + e % p - p = 0 := by
        rw [Nat.mod_eq_of_lt hlt2] at h
        exact h
      have hxeq : x = p - e % p := by omega
      rw [hxeq]
      have hsub : p - e % p < p := by omega
      rw [Nat.mod_eq_of_lt hsub]
  · intro h
    by_cases hep0 : e % p = 0
    · have hx0 : x = 0 := by
        simpa [hep0] using h
      simp [hep0, hx0]
    · have hsub : p - e % p < p := by omega
      have hxeq : x = p - e % p := by
        rwa [Nat.mod_eq_of_lt hsub] at h
      have hsum : x + e % p = p := by omega
      rw [hsum]
      exact Nat.mod_self p

private lemma card_coprime_add_zero (n e : ℕ) (hn : 0 < n) :
    ((Finset.range n).filter (fun x => x.gcd n = 1 ∧ (x + e) % n = 0)).card =
      if e.gcd n = 1 then 1 else 0 := by
  classical
  let c : ℕ := (n - e % n) % n
  have hc : c < n := by
    dsimp [c]
    exact Nat.mod_lt (n - e % n) hn
  have hset : (Finset.range n).filter (fun x => x.gcd n = 1 ∧ (x + e) % n = 0) =
      (Finset.range n).filter (fun x => x.gcd n = 1 ∧ x = c) := by
    apply Finset.filter_congr
    intro x hx
    have hxlt : x < n := Finset.mem_range.mp hx
    constructor
    · intro hx2
      exact ⟨hx2.1, (mod_add_eq_zero_iff n e x hn hxlt).mp hx2.2⟩
    · intro hx2
      exact ⟨hx2.1, (mod_add_eq_zero_iff n e x hn hxlt).mpr hx2.2⟩
  rw [hset]
  rw [card_coprime_eq_single n c hn hc]
  have hgcd : c.gcd n = e.gcd n := by
    let r := e % n
    have hrlt : r < n := Nat.mod_lt e hn
    calc
      c.gcd n = ((n - r) % n).gcd n := by dsimp [c, r]
      _ = (n - r).gcd n := by
        calc
          ((n - r) % n).gcd n = n.gcd (n - r) := (Nat.gcd_rec n (n - r)).symm
          _ = (n - r).gcd n := Nat.gcd_comm n (n - r)
      _ = r.gcd n := Nat.gcd_self_sub_left (le_of_lt hrlt)
      _ = e.gcd n := by
        calc
          r.gcd n = n.gcd e := by
            dsimp [r]
            exact (Nat.gcd_rec n e).symm
          _ = e.gcd n := Nat.gcd_comm n e
  by_cases he : e.gcd n = 1
  · have hc1 : c.gcd n = 1 := by rwa [hgcd]
    simp [he, hc1]
  · have hc0 : ¬ c.gcd n = 1 := by
      intro h
      apply he
      rwa [← hgcd]
    simp [he, hc0]

private lemma card_filter_preimage_eq (n a : ℕ) (hn : 0 < n) (hac : a.Coprime n)
    (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range n).filter (fun x => x.gcd n = 1 ∧ P ((x * a) % n))).card =
      ((Finset.range n).filter (fun x => x.gcd n = 1 ∧ P x)).card := by
  classical
  let i : ℕ → ℕ := fun x => (x * a) % n
  let U : Finset ℕ := (Finset.range n).filter (fun x => x.gcd n = 1)
  have hi_mem : ∀ x ∈ U, i x ∈ U := by
    intro x hx
    have hxg : x.gcd n = 1 := (Finset.mem_filter.mp hx).2
    change (x * a) % n ∈ (Finset.range n).filter (fun x => x.gcd n = 1)
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_range.mpr (Nat.mod_lt (x * a) hn)
    · show ((x * a) % n).gcd n = 1
      have hgcd : ((x * a) % n).gcd n = (x * a).gcd n := by
        calc
          ((x * a) % n).gcd n = n.gcd (x * a) := (Nat.gcd_rec n (x * a)).symm
          _ = (x * a).gcd n := Nat.gcd_comm n (x * a)
      rw [hgcd]
      exact Nat.Coprime.mul_left hxg hac
  have hinj_range : ∀ x, x < n → ∀ y, y < n → (x * a) % n = (y * a) % n → x = y := by
    intro x hx y hy h
    have hxy_mod : x * a ≡ y * a [MOD n] := h
    rcases le_total x y with hle | hle
    · have hdv1 : n ∣ y * a - x * a := (Nat.modEq_iff_dvd' (Nat.mul_le_mul_right a hle)).mp hxy_mod
      have hsub : (y - x) * a = y * a - x * a := by
        rw [Nat.mul_sub_right_distrib]
      have hdv : n ∣ (y - x) * a := by
        rwa [← hsub] at hdv1
      have hcop : n.Coprime a := hac.symm
      have hdiv : n ∣ y - x := Nat.Coprime.dvd_of_dvd_mul_right hcop hdv
      have hlt : y - x < n := lt_of_le_of_lt (Nat.sub_le y x) hy
      have hzx : y - x = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
      omega
    · have hdv1 : n ∣ x * a - y * a := (Nat.modEq_iff_dvd' (Nat.mul_le_mul_right a hle)).mp hxy_mod.symm
      have hsub : (x - y) * a = x * a - y * a := by
        rw [Nat.mul_sub_right_distrib]
      have hdv : n ∣ (x - y) * a := by
        rwa [← hsub] at hdv1
      have hcop : n.Coprime a := hac.symm
      have hdiv : n ∣ x - y := Nat.Coprime.dvd_of_dvd_mul_right hcop hdv
      have hlt : x - y < n := lt_of_le_of_lt (Nat.sub_le x y) hx
      have hzx : x - y = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
      omega
  have hinjU : Set.InjOn i (↑U : Set ℕ) := by
    intro x hxS y hyS hxy
    have hxlt : x < n := Finset.mem_range.mp ((Finset.mem_filter.mp hxS).1)
    have hylt : y < n := Finset.mem_range.mp ((Finset.mem_filter.mp hyS).1)
    exact hinj_range x hxlt y hylt (by simpa [i] using hxy)
  have himg : U.image i = U := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
      exact hi_mem x hx
    · rw [Finset.card_image_of_injOn hinjU]
  calc
    ((Finset.range n).filter (fun x => x.gcd n = 1 ∧ P ((x * a) % n))).card
        = (U.filter (fun x => P (i x))).card := by
          congr 1
          ext x
          simp [U, i]
          tauto
    _ = (U.filter P).card := by
      refine Finset.card_bij (s := U.filter (fun x => P (i x))) (t := U.filter P)
        (fun x _ => i x) ?hi ?hinj ?hsurj
      · intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hi_mem x hx.1, hx.2⟩
      · intro x hx y hy hxy
        simp only [Finset.mem_filter] at hx hy
        apply hinjU
        · simpa using hx.1
        · simpa using hy.1
        · simpa [i] using hxy
      · intro t ht
        simp only [Finset.mem_filter] at ht
        have htU : t ∈ U.image i := by
          rw [himg]
          exact ht.1
        rcases Finset.mem_image.mp htU with ⟨x, hx, hxit⟩
        exact ⟨x, Finset.mem_filter.mpr ⟨hx, by rw [hxit]; exact ht.2⟩, hxit⟩
    _ = ((Finset.range n).filter (fun x => x.gcd n = 1 ∧ P x)).card := by
          congr 1
          ext x
          simp [U]
          tauto

private lemma card_coprime_mul_mod (n a c : ℕ) (hn : 0 < n) (hac : a.Coprime n) (hc : c < n) :
    ((Finset.range n).filter (fun x => x.gcd n = 1 ∧ (x * a) % n = c)).card =
      if c.gcd n = 1 then 1 else 0 := by
  classical
  rw [card_filter_preimage_eq n a hn hac (fun t => t = c)]
  exact card_coprime_eq_single n c hn hc

private lemma card_factor_a (q r e : ℕ) (hq : 0 < q) (hrq : r.Coprime q) :
    ((Finset.range q).filter (fun a => a.gcd q = 1 ∧ (a * r) % q = e % q)).card =
      if e.gcd q = 1 then 1 else 0 := by
  classical
  have hlt : e % q < q := Nat.mod_lt e hq
  rw [card_coprime_mul_mod q r (e % q) hq hrq hlt]
  have hgcd : (e % q).gcd q = e.gcd q := by
    calc
      (e % q).gcd q = q.gcd e := (Nat.gcd_rec q e).symm
      _ = e.gcd q := Nat.gcd_comm q e
  by_cases he : e.gcd q = 1
  · have h1 : (e % q).gcd q = 1 := by rwa [hgcd]
    simp [he, h1]
  · have h0 : ¬ (e % q).gcd q = 1 := by
      intro h
      apply he
      rwa [← hgcd]
    simp [he, h0]

private lemma card_factor_b (q r e : ℕ) (hr : 0 < r) (hqr : q.Coprime r) :
    ((Finset.range r).filter (fun b => b.gcd r = 1 ∧ (b * q + e) % r = 0)).card =
      if e.gcd r = 1 then 1 else 0 := by
  classical
  have hrewrite : (Finset.range r).filter (fun b => b.gcd r = 1 ∧ (b * q + e) % r = 0) =
      (Finset.range r).filter (fun b => b.gcd r = 1 ∧ ((b * q) % r + e) % r = 0) := by
    apply Finset.filter_congr
    intro b hb
    rw [add_mul_mod_eq]
  rw [hrewrite]
  rw [card_filter_preimage_eq r q hr hqr (fun t => (t + e) % r = 0)]
  exact card_coprime_add_zero r e hr

theorem reduced_pair_coprime_fiber (q r e : ℕ) (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r) :
    (((Finset.product (Finset.range q) (Finset.range r)).filter
      (fun mn : ℕ × ℕ => mn.1.gcd q = 1 ∧ mn.2.gcd r = 1 ∧
         ((mn.1 * r) % (q * r) = ((mn.2 * q + e) % (q * r))))).card) =
      if e.gcd (q * r) = 1 then 1 else 0 := by
  classical
  let A0 := (Finset.range q).filter (fun a => a.gcd q = 1 ∧ (a * r) % q = e % q)
  let B0 := (Finset.range r).filter (fun b => b.gcd r = 1 ∧ (b * q + e) % r = 0)
  have hsplit :
      ((Finset.product (Finset.range q) (Finset.range r)).filter
        (fun mn : ℕ × ℕ => mn.1.gcd q = 1 ∧ mn.2.gcd r = 1 ∧
           ((mn.1 * r) % (q * r) = ((mn.2 * q + e) % (q * r))))) = A0.product B0 := by
    ext p
    rcases p with ⟨a, b⟩
    simp [A0, B0, Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    rw [cong_iff q r e a b hqr]
    tauto
  have hcardA : A0.card = if e.gcd q = 1 then 1 else 0 := by
    simpa [A0] using card_factor_a q r e hq hqr.symm
  have hcardB : B0.card = if e.gcd r = 1 then 1 else 0 := by
    simpa [B0] using card_factor_b q r e hr hqr
  have hS : (((Finset.product (Finset.range q) (Finset.range r)).filter
        (fun mn : ℕ × ℕ => mn.1.gcd q = 1 ∧ mn.2.gcd r = 1 ∧
           ((mn.1 * r) % (q * r) = ((mn.2 * q + e) % (q * r))))).card) =
      A0.card * B0.card := by
    rw [hsplit]
    exact Finset.card_product A0 B0
  rw [hS, hcardA, hcardB]
  have hprod : (if e.gcd q = 1 then 1 else 0) * (if e.gcd r = 1 then 1 else 0) =
      if (e.gcd q = 1 ∧ e.gcd r = 1) then 1 else 0 := by
    by_cases hq1 : e.gcd q = 1 <;> by_cases hr1 : e.gcd r = 1 <;> simp [hq1, hr1]
  rw [hprod]
  have hiff : (e.gcd q = 1 ∧ e.gcd r = 1) ↔ e.gcd (q * r) = 1 := by
    rw [← Nat.coprime_iff_gcd_eq_one (m := e) (n := q * r),
        ← Nat.coprime_iff_gcd_eq_one (m := e) (n := q),
        ← Nat.coprime_iff_gcd_eq_one (m := e) (n := r)]
    exact (Nat.coprime_mul_iff_right (k := e) (m := q) (n := r)).symm
  by_cases h1 : e.gcd (q * r) = 1
  · have hc : e.gcd q = 1 ∧ e.gcd r = 1 := hiff.mpr h1
    simp [h1, hc]
  · have hc : ¬ (e.gcd q = 1 ∧ e.gcd r = 1) := fun h => h1 (hiff.mp h)
    simp [h1, hc]

end Commons.NumberTheory.DuffinSchaeffer