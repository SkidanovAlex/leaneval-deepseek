import Mathlib
import Submission.Work.ThmF.ChV3.Chain15
import Submission.Work.ThmF.Prove.geomSumPadic
import Submission.Work.ThmF.Prove.powMulZpow
import Submission.Work.ThmF.Prove.conjFixesPowOne

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step9Omega1` — `Ω₁(S) = (T ⊓ C_G(y)) · ⟨y⟩`, and it is abelian

Peterfalvi II Ch. V §3, step (9): the local `Ω₁`-statement for the pair `(S, T)`.

Let `p` be an odd prime, `T ≤ S ≤ G` with `T` a **cyclic** `p`-group normalized by `S`,
`y ∈ S \ T` of order `p`, `S = T ⊔ ⟨y⟩` and `|T ⊓ C_G(y)| ≤ p`.  Then

* `x ^ p = 1` for `x ∈ S` **iff** `x ∈ (T ⊓ C_G(y)) ⊔ ⟨y⟩`, and
* the subgroup `(T ⊓ C_G(y)) ⊔ ⟨y⟩` is abelian.

## The mathematics

Write `Z = T ⊓ C_G(y)`.  Every `x ∈ S` is `t · w` with `t ∈ T`, `w ∈ ⟨y⟩`, because `y`
normalizes `T`.

* `Z` is a subgroup of the `p`-group `T` of order `≤ p`, hence every `z ∈ Z` has `z ^ p = 1`;
  since `Z ≤ C_G(y)`, every element of `Z ⊔ ⟨y⟩` is killed by `p` (the `⊆` direction of the
  first claim, and the second claim: `Z` is abelian as a subgroup of the cyclic `T`, and `y`
  centralizes it).
* Conversely let `x = t w` with `x ^ p = 1`.
  - If `w = 1` then `t ^ p = 1`, and `conjFixesPowOne` shows `y t y⁻¹ = t`, i.e. `t ∈ Z`.
  - If `w ≠ 1`, the heart of the argument is `conjFixOfPowMul`: pick a generator `g` of `T`,
    write `t = g ^ k` and `w g w⁻¹ = g ^ l`.  The bookkeeping identity `powMulZpow` gives
    `(g ^ k w) ^ p = g ^ (k · ∑_{i<p} l ^ i) · w ^ p`, and `w ^ p = 1` because `w ∈ ⟨y⟩` and
    `orderOf y = p`.  Hence `orderOf g = p ^ m` divides `k · ∑ l ^ i`, while `w ^ p = 1`
    (`σ ^ p = 1` for the conjugation automorphism) gives `p ^ m ∣ l ^ p - 1`.  The `p`-adic
    input `geomSumPadic` (here `v_p (∑_{i<p} l ^ i) = 1`, plus Fermat for `p ∣ l - 1`) then
    yields `p ^ m ∣ k (l - 1)`, i.e. `w t w⁻¹ = g ^ (l k) = g ^ k = t`.  Since `⟨w⟩ = ⟨y⟩`
    (both have order the prime `p`), `t` centralizes `y` as well, so `t ∈ Z`.

Together: `x ∈ Z ⊔ ⟨y⟩`.  (The hypothesis `y ∉ T` is not needed by the argument, and the
hypothesis `|Z| ≤ p` is used exactly once, for `z ^ p = 1` on `Z`.)
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ThmF.Prove

/-- Conjugation by `w` raising `g` to the power `l` makes its `n`-th iterate raise `g`
to the power `l ^ n`. -/
lemma conjPowApply {G : Type*} [Group G] (w g : G) {l : ℤ}
    (hl : w * g * w⁻¹ = g ^ l) (n : ℕ) : ((MulAut.conj w) ^ n) g = g ^ (l ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, MulAut.conj_apply, hl, map_zpow, ih]
    rw [pow_succ, zpow_mul]

/-- If `w * g * w⁻¹ = g ^ l`, then `w * g ^ m * w⁻¹ = g ^ (l * m)` for every `m : ℤ`. -/
lemma conjZpow {G : Type*} [Group G] (w g : G) {l : ℤ}
    (hl : w * g * w⁻¹ = g ^ l) (m : ℤ) : w * g ^ m * w⁻¹ = g ^ (l * m) := by
  rw [← MulAut.conj_apply w (g ^ m), map_zpow, MulAut.conj_apply, hl, ← zpow_mul]

/-- **The `Ω₁`-crux.**  Let `p` be an odd prime, `g` of order `p ^ m` (`m ≥ 1`), `w ^ p = 1`,
`w * g * w⁻¹ = g ^ l`.  If `(g ^ k * w) ^ p = 1` then `w` fixes `g ^ k`.

(This says that the norm `∑_{i<p} σ ^ i` of the order-`p` conjugation automorphism `σ` of the
cyclic `p`-group `⟨g⟩` has kernel contained in the fixed points of `σ`.) -/
theorem conjFixOfPowMul {G : Type*} [Group G] {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : 1 ≤ m) {g w : G} {l k : ℤ} (hg : orderOf g = p ^ m) (hw : w ^ p = 1)
    (hl : w * g * w⁻¹ = g ^ l) (h : (g ^ k * w) ^ p = 1) :
    w * g ^ k * w⁻¹ = g ^ k := by
  have hcast : (orderOf g : ℤ) = (p : ℤ) ^ m := by rw [hg]; push_cast; rfl
  -- `σ ^ p = 1` gives `g ^ (l ^ p) = g`
  have hlp_eq : g ^ (l ^ p) = g := by
    have hconj : ((MulAut.conj w) ^ p) g = g ^ (l ^ p) := conjPowApply w g hl p
    have hwp : (MulAut.conj w) ^ p = (1 : MulAut G) := by
      rw [← map_pow (MulAut.conj) w p, hw, map_one]
    rw [← hconj, hwp, MulAut.one_apply]
  have hlp : (p : ℤ) ^ m ∣ l ^ p - 1 := by
    have h1 : g ^ (l ^ p - 1) = 1 := by
      rw [zpow_sub_one, hlp_eq]; simp
    rw [← hcast]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h1
  -- the product formula turns `(g ^ k * w) ^ p = 1` into `g ^ (k * ∑ l ^ i) = 1`
  have hk : (p : ℤ) ^ m ∣ k * ∑ i ∈ Finset.range p, l ^ i := by
    have h1 : g ^ (k * ∑ i ∈ Finset.range p, l ^ i) = 1 := by
      have h2 : (g ^ k * w) ^ p = g ^ (k * ∑ i ∈ Finset.range p, l ^ i) * w ^ p :=
        powMulZpow hl k p
      rw [h2, hw, mul_one] at h
      exact h
    rw [← hcast]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h1
  have hmain : (p : ℤ) ^ m ∣ k * (l - 1) := geomSumPadic hp hp2 hm hlp hk
  have hker : g ^ (k * (l - 1)) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hcast]
    exact hmain
  rw [conjZpow w g hl k]
  rw [show l * k = k + k * (l - 1) from by ring, zpow_add, hker, mul_one]

theorem step9Omega1 {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S T : Subgroup G} {y : G}
    (hy : y ∈ S) (hyT : y ∉ T) (hordy : orderOf y = p)
    (hTc : IsCyclic ↥T) (hTp : IsPGroup p T) (hTn : ∀ g ∈ S, ∀ x ∈ T, g * x * g⁻¹ ∈ T)
    (hS : S = T ⊔ Subgroup.zpowers y)
    (hC : Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set G)) ≤ p) :
    (∀ x ∈ S, x ^ p = 1 ↔ x ∈ (T ⊓ Subgroup.centralizer ({y} : Set G)) ⊔ Subgroup.zpowers y) ∧
    (∀ a ∈ (T ⊓ Subgroup.centralizer ({y} : Set G)) ⊔ Subgroup.zpowers y,
      ∀ b ∈ (T ⊓ Subgroup.centralizer ({y} : Set G)) ⊔ Subgroup.zpowers y, a * b = b * a) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Z : Subgroup G := T ⊓ Subgroup.centralizer ({y} : Set G) with hZdef
  have hSle : Subgroup.zpowers y ≤ S := Subgroup.zpowers_le.mpr hy
  have hTyp : y ^ p = 1 := by rw [← hordy]; exact pow_orderOf_eq_one y
  haveI hTcI : IsCyclic ↥T := hTc
  -- `y` normalizes `T`, so every element of `S` is `t * w` with `t ∈ T`, `w ∈ ⟨y⟩`
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.le_normalizer_iff.mpr (fun h hh k hk => hTn h (hSle hh) k hk)
  have hSdec : ∀ x, x ∈ S ↔ ∃ t ∈ T, ∃ w ∈ Subgroup.zpowers y, t * w = x := by
    intro x
    rw [hS, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_right_le_normalizer_left T (Subgroup.zpowers y) hyN]
    exact Set.mem_mul
  -- elements of `Z` commute with `⟨y⟩`
  have hzy : ∀ z ∈ Z, ∀ w ∈ Subgroup.zpowers y, z * w = w * z := by
    intro z hz w hw
    have hzc : z * y = y * z := by
      have h := Subgroup.mem_centralizer_iff.mp hz.2
      exact (h y (Set.mem_singleton y)).symm
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_right (show Commute z y from hzc) j).eq
  have hZnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (Z : Set G) :=
    Subgroup.le_normalizer_iff.mpr (fun h hh k hk => by
      rw [← hzy k hk h hh, mul_assoc, mul_inv_cancel, mul_one]
      exact hk)
  have hZdec : ∀ x, x ∈ Z ⊔ Subgroup.zpowers y ↔
      ∃ z ∈ Z, ∃ w ∈ Subgroup.zpowers y, z * w = x := by
    intro x
    rw [← SetLike.mem_coe,
      Subgroup.coe_mul_of_right_le_normalizer_left Z (Subgroup.zpowers y) hZnorm]
    exact Set.mem_mul
  -- `Z` is a subgroup of the `p`-group `T` of order at most `p`, hence has exponent `p`
  have hZpow : ∀ z ∈ Z, z ^ p = 1 := by
    intro z hz
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hTp (⟨z, hz.1⟩ : ↥T)
    have hkz : orderOf z = p ^ k := by
      have h2 : orderOf z = orderOf (⟨z, hz.1⟩ : ↥T) :=
        Subgroup.orderOf_coe (⟨z, hz.1⟩ : ↥T)
      rw [h2, hk]
    have hle : orderOf z ≤ p :=
      (Nat.le_of_dvd (Nat.card_pos (α := ↥Z)) (Subgroup.orderOf_dvd_natCard Z hz)).trans hC
    have hle2 : p ^ k ≤ p := hkz ▸ hle
    have hk1 : k ≤ 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (by rw [pow_one]; exact hle2)
    rw [← orderOf_dvd_iff_pow_eq_one, hkz]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with h | h <;> subst h <;> simp
  have hwp_of : ∀ w ∈ Subgroup.zpowers y, w ^ p = 1 := fun w hw =>
    orderOf_dvd_iff_pow_eq_one.mp (by rw [← hordy]; exact orderOf_dvd_of_mem_zpowers hw)
  -- ## the forward direction
  have hfwd : ∀ x ∈ S, x ^ p = 1 → x ∈ Z ⊔ Subgroup.zpowers y := by
    intro x hxS hxp
    obtain ⟨t, ht, w, hw, hxw⟩ := (hSdec x).mp hxS
    rw [← hxw] at hxp ⊢
    by_cases hw1 : w = 1
    · -- `x = t ∈ T`, `t ^ p = 1`: `conjFixesPowOne` puts `t` in `Z`
      rw [hw1, mul_one] at hxp ⊢
      have htZ : t ∈ Z := by
        rw [hZdef, Subgroup.mem_inf]
        refine ⟨ht, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := conjFixesPowOne hp hTc (fun a ha => hTn y hy a ha) hTyp ht hxp
        exact (mul_inv_eq_iff_eq_mul.mp h).symm
      exact Subgroup.mem_sup_left htZ
    · by_cases hTbot : T = ⊥
      · -- `T` trivial: `t = 1` and `x = w ∈ ⟨y⟩`
        have ht1 : t = 1 := by rw [hTbot] at ht; exact Subgroup.mem_bot.mp ht
        rw [ht1, one_mul]
        exact Subgroup.mem_sup_right hw
      · -- the substantive case: `t * w` of order dividing `p` with `w ≠ 1`
        obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥T)
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hTp
        have hgord : orderOf g = Nat.card ↥T := orderOf_eq_card_of_forall_mem_zpowers hg
        have hn1 : 1 ≤ n := by
          rcases Nat.eq_zero_or_pos n with h0 | hpos
          · exfalso
            rw [h0, pow_zero] at hn
            exact hTbot (Subgroup.card_eq_one.mp hn)
          · exact hpos
        obtain ⟨kk, hkk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨t, ht⟩)
        have hkk' : (g : G) ^ kk = t := by
          have := congrArg Subtype.val hkk
          simpa using this
        have hwgT : w * (g : G) * w⁻¹ ∈ T := hTn w (hSle hw) (g : G) g.2
        obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨w * (g : G) * w⁻¹, hwgT⟩)
        have hl' : w * (g : G) * w⁻¹ = (g : G) ^ l := by
          have := congrArg Subtype.val hl
          simpa using this.symm
        have hwp : w ^ p = 1 := hwp_of w hw
        have hgord' : orderOf (g : G) = p ^ n := by
          rw [Subgroup.orderOf_coe, hgord, hn]
        have hcrux := conjFixOfPowMul hp hp2 hn1 hgord' hwp hl' (by rw [hkk']; exact hxp)
        rw [hkk'] at hcrux
        have htw : w * t = t * w := mul_inv_eq_iff_eq_mul.mp hcrux
        -- `⟨w⟩ = ⟨y⟩` because both have order the prime `p`
        have hyw : y ∈ Subgroup.zpowers w := by
          have hle : Subgroup.zpowers w ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hw
          have hcard : Nat.card ↥(Subgroup.zpowers w) = Nat.card ↥(Subgroup.zpowers y) := by
            rw [Nat.card_zpowers, Nat.card_zpowers, hordy]
            have hdvd : orderOf w ∣ p := by
              rw [← hordy]; exact orderOf_dvd_of_mem_zpowers hw
            have hne : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
            rcases (Nat.dvd_prime hp).mp hdvd with h | h
            · exact absurd h hne
            · exact h
          have heq : Subgroup.zpowers w = Subgroup.zpowers y :=
            Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
          rw [heq]
          exact Subgroup.mem_zpowers y
        have hty : t * y = y * t := by
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hyw
          rw [← hj]
          exact (Commute.zpow_right (show Commute t w from htw.symm) j).eq
        have htZ : t ∈ Z := by
          rw [hZdef, Subgroup.mem_inf]
          refine ⟨ht, ?_⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hty
        exact Subgroup.mul_mem_sup htZ hw
  -- ## the backward direction
  have hbwd : ∀ x ∈ Z ⊔ Subgroup.zpowers y, x ^ p = 1 := by
    intro x hx
    obtain ⟨z, hz, w, hw, hxw⟩ := (hZdec x).mp hx
    rw [← hxw, Commute.mul_pow (show Commute z w from hzy z hz w hw), hZpow z hz,
      hwp_of w hw]
    simp
  -- ## the subgroup `Z ⊔ ⟨y⟩` is abelian
  have hcommZ : ∀ a ∈ Z ⊔ Subgroup.zpowers y, ∀ b ∈ Z ⊔ Subgroup.zpowers y,
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨z1, hz1, w1, hw1, hx1⟩ := (hZdec a).mp ha
    obtain ⟨z2, hz2, w2, hw2, hx2⟩ := (hZdec b).mp hb
    rw [← hx1, ← hx2]
    have h12 : z1 * z2 = z2 * z1 := setLike_mul_comm (s := T) hz1.1 hz2.1
    have hw12 : w1 * w2 = w2 * w1 := setLike_mul_comm (s := Subgroup.zpowers y) hw1 hw2
    calc z1 * w1 * (z2 * w2)
        = z1 * (w1 * z2) * w2 := by group
      _ = z1 * (z2 * w1) * w2 := by rw [← hzy z2 hz2 w1 hw1]
      _ = (z1 * z2) * (w1 * w2) := by group
      _ = (z2 * z1) * (w2 * w1) := by rw [h12, hw12]
      _ = z2 * (z1 * w2) * w1 := by group
      _ = z2 * (w2 * z1) * w1 := by rw [← hzy z1 hz1 w2 hw2]
      _ = (z2 * w2) * (z1 * w1) := by group
  exact ⟨fun x hxS => ⟨fun h => hfwd x hxS h, fun h => hbwd x h⟩, hcommZ⟩

end Work.ThmF.Prove
