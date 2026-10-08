import Mathlib
import Submission.Work.ThmF.ChV3.step4
import Submission.Work.ThmF.Prove.step1
-- (`Submission.Work.ThmF.Prove.step3` is *not* imported: its target `step3` is the hypothesis
--  `h3` of `step4` here, and the sibling file is currently not building.)
import Submission.Work.ThmF.ChV12.prop1a
import Submission.Work.ThmF.ChV12.prop1b
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.ThmF.ChV12.prop3_frobenius_power
import Submission.Work.ThmF.ChV12.fixedField_card_pow
import Submission.Work.ThmF.ChV12.L6basic
import Submission.Work.ThmF.ChV12.natCard_ringEquiv_finiteField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step4` — Peterfalvi II, Ch. V §3, step (4): `|Q| = |C_Q(P)|^{|P|}`

The source's step (4) (p. 248) reads

> **(4)** `|Q| = |C_Q(P)|^p = |F^*|^p`.
> *Proof.* `KP` is a Frobenius group with kernel `K`, so in `ℤ[KP]`
> `Σ_{x∈K} P^x + K = KP + |K|·1`.  Applying **Wielandt's fixed-point formula** ([HB] XI (12-4))
> to `KP` acting on `Q` gives `|C_Q(P)|^p = |Q|`.

To instantiate the black box `WielandtFixedPoint` (`Tools/External.lean`) we must supply, for the
*conjugation action* `φ : H →* MulAut ↥Q` (`H` normalises `Q`):

* `K̄ = φ(Ksub H t)` and `P̄ = φ(P)` — both have odd order (`|K̄| = 2^|P| - 1`, `|P̄| = |P|`);
* coprimality `(|K̄|·|P̄|, |Q|) = 1` — `h3` (step (3)) says every odd prime `ℓ` dividing `|Q|`
  satisfies `ℓ ≡ 2^i (mod 2^|P| - 1)`, whence `ℓ ∤ 2^|P| - 1`;
* `K̄#` acts fixed-point-freely on `Q` (Ch. V §1 Prop. 1 a, `ChV12.prop1a`) and `C_Q(K̄) = 1`;
* `|P̄| = |P|` — this is the faithfulness hypothesis `hPfaith`;
* `P̄ ⊓ P̄^{k̄} = ⊥` for `k̄ ∈ K̄#` ("`K̄P̄` is a Frobenius group"): `P̄` normalises `K̄`
  (`ChV12.conj_mem_Ksub`, since `P ≤ C_D(t)`) and `C_{K̄}(P̄) = 1`.  The latter is the rigidity of
  the joint action of `Ksub` and `P` on `Q₀ = ⟨Inv H⟩ ≅ 𝔽_{2^|P|}`, which §1 Prop. 3 turns into:
  `conj k` acts on `Q₀` by multiplication by `κ k`, `conj p` by the field automorphism `ρ p ≠ 1`,
  and `C_{K̄}(P̄) = 1` follows since the fixed field of a nontrivial automorphism of `𝔽_{2^p}`
  (`p` prime) is the prime field `𝔽₂`.

## The pieces of this file

* `odd_two_pow_sub_one`, `two_not_dvd_two_pow_sub_one` — number theory;
* `step4_field` — a nontrivial automorphism of a finite field of cardinality `2^p` (`p` prime)
  fixes no unit other than `1`;
* `step4_coprime` — `(|K̄|·|P̄|, |Q|) = 1` from step (3);
* `step4_frob` — the abstract Frobenius clause `P ⊓ k⁻¹Pk = ⊥`;
* `step4_Kcard` — `|Ksub H t| = 2^|P| - 1`;
* `step4_act` — the rigidity of the action on `Q₀` (two clauses: `k = 1` if `conj k = conj p` on
  `Q₀`, and `k = 1` if `conj k` commutes with `conj p` on `Q₀`, `p ≠ 1`);
* `step4` — the target: `|Q| = |C_Q(P)|^{|P|}`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.Prove

open Classical Submission.Blueprint

/-! ## Number theory -/

/-- `2 ^ n - 1` is odd for `n ≥ 1`. -/
theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨2 ^ m - 1, ?_⟩
  have h : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [pow_succ']
  omega

/-- `2` does not divide `2 ^ n - 1` for `n ≥ 1`. -/
theorem two_not_dvd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : ¬ (2 : ℕ) ∣ 2 ^ n - 1 := by
  intro h
  obtain ⟨k, hk⟩ := h
  obtain ⟨m, hm⟩ := odd_two_pow_sub_one hn
  omega

/-! ## The fixed field of a nontrivial automorphism of `𝔽_{2^p}` -/

/-- **Field-theoretic input of step (4).**  If `F` is a finite field with `|F| = 2 ^ p`, `p` prime,
and `σ ≠ 1` is a ring automorphism of `F`, then the only unit of `F` fixed by `σ` is `1`: `σ`
generates the Galois group of `F` over `𝔽₂`, whose fixed field is `𝔽₂`. -/
theorem step4_field {F : Type} [Field F] [Fintype F] {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = 2 ^ p) {σ : F ≃+* F} (hσ : σ ≠ 1) {a : Fˣ}
    (ha : (σ a : F) = (a : F)) : a = 1 := by
  -- `F` has characteristic `2`: its cardinality is `q ^ k` with `q` prime, and `q ^ k = 2 ^ p`
  obtain ⟨q, hcharq⟩ := CharP.exists F
  obtain ⟨k, hqprime, hkcard⟩ := FiniteField.card F q
  have hq2 : q = 2 := by
    have hqk : q ^ (k : ℕ) = 2 ^ p := by
      rw [← hkcard, Fintype.card_eq_nat_card, hF]
    have hdvd : q ∣ 2 ^ p := by rw [← hqk]; exact dvd_pow_self q k.ne_zero
    have hdvd2 : q ∣ 2 := hqprime.dvd_of_dvd_pow hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact absurd h hqprime.ne_one
    · exact h
  haveI : CharP F 2 := hq2 ▸ hcharq
  -- `σ` is an iterate of the Frobenius `x ↦ x ^ 2`
  obtain ⟨i, hi⟩ := Work.ThmF.ChV12.ringAut_charTwo_eq_frobenius_pow (F := F) σ
  -- `x ^ (2 ^ p) = x`
  have hpowp : ∀ x : F, x ^ 2 ^ p = x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · have hcard : Fintype.card Fˣ = 2 ^ p - 1 := by
        rw [Fintype.card_units, Fintype.card_eq_nat_card, hF]
      have hunit : (Units.mk0 x hx) ^ (2 ^ p - 1) = 1 := by
        rw [← hcard]; exact pow_card_eq_one
      have hval : x ^ (2 ^ p - 1) = 1 := by
        have h := congrArg (fun u : Fˣ => (u : F)) hunit
        simpa using h
      calc x ^ 2 ^ p = x ^ (2 ^ p - 1 + 1) := by rw [Nat.sub_add_cancel (Nat.one_le_two_pow)]
        _ = x ^ (2 ^ p - 1) * x ^ 1 := by rw [pow_add]
        _ = x := by rw [hval, one_mul, pow_one]
  have hpowpm : ∀ m : ℕ, ∀ x : F, x ^ 2 ^ (p * m) = x := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ n ih => intro x; rw [Nat.mul_succ, pow_add, pow_mul, ih x, hpowp]
  -- `p ∤ i`, since otherwise `σ = (x ↦ x ^ 2) ^ i = (x ↦ x ^ 2) ^ (p * m) = 1`
  have hpndvd : ¬ p ∣ i := by
    intro hdiv
    obtain ⟨m, rfl⟩ := hdiv
    apply hσ
    ext x
    rw [hi x]
    exact hpowpm m x
  have hipos : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exfalso
      apply hσ
      ext x
      rw [hi x, h]
      simp
    · exact h
  have hcop : Nat.Coprime i p := (hp.coprime_iff_not_dvd.mpr hpndvd).symm
  -- `a ^ (2 ^ i) = a`
  have hapow : (a : Fˣ) ^ (2 ^ i) = a := by
    apply Units.ext
    show (((a : Fˣ) ^ (2 ^ i) : Fˣ) : F) = (a : F)
    rw [Units.val_pow_eq_pow_val, ← hi (a : F)]
    exact ha
  -- hence `orderOf a ∣ 2 ^ i - 1` and `orderOf a ∣ 2 ^ p - 1`, so `orderOf a ∣ 1`
  have hdiv1 : orderOf a ∣ 2 ^ i - 1 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have hmul : (a : Fˣ) ^ (2 ^ i - 1) * a = a := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow), hapow]
    exact mul_right_cancel (show (a : Fˣ) ^ (2 ^ i - 1) * a = (1 : Fˣ) * a by rw [hmul, one_mul])
  have hdiv2 : orderOf a ∣ 2 ^ p - 1 := by
    have hcard : Fintype.card Fˣ = 2 ^ p - 1 := by
      rw [Fintype.card_units, Fintype.card_eq_nat_card, hF]
    rw [← hcard]
    exact orderOf_dvd_card
  have hdiv3 : orderOf a ∣ 2 ^ Nat.gcd i p - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one 2 i p]
    exact Nat.dvd_gcd hdiv1 hdiv2
  rw [show Nat.gcd i p = 1 from hcop, pow_one] at hdiv3
  have hone : orderOf a = 1 := Nat.dvd_one.mp (by simpa using hdiv3)
  exact orderOf_eq_one_iff.mp hone

/-! ## Coprimality of `|K̄| · |P̄|` and `|Q|` (step (3)) -/

/-- **Step (4), coprimality input.**  Given step (3)'s arithmetic statement on the prime divisors
of `|oddPart Q|`, and given that `|K̄|` divides `2 ^ |P| - 1` while `|P̄| = |P|` is odd, the order of
the acting group `K̄ P̄` is coprime to `|Q|`. -/
theorem step4_coprime {G : Type} [Group G] [Finite G] {Q P : Subgroup G}
    (hPprime : (Nat.card P).Prime) (hPodd : Odd (Nat.card P))
    (h3 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card ↥(Work.ThmF.oddPart Q) →
      (∃ i < Nat.card P, ℓ ≡ 2 ^ i [MOD 2 ^ Nat.card P - 1]) ∧ ℓ ≠ Nat.card P)
    {Kbar Pbar : Subgroup (MulAut ↥Q)}
    (hKcard : Nat.card Kbar ∣ 2 ^ Nat.card P - 1) (hPcard : Nat.card Pbar = Nat.card P) :
    Nat.Coprime (Nat.card Kbar * Nat.card Pbar) (Nat.card Q) := by
  classical
  haveI : Fintype ↥Q := Fintype.ofFinite _
  haveI : Fintype ↥(Work.ThmF.oddPart Q) := Fintype.ofFinite _
  by_contra hcon
  obtain ⟨ℓ, hℓp, hℓdvd, hℓQ⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
  have h1le : 1 ≤ Nat.card P := hPprime.one_le
  -- `ℓ ≠ 2`
  have hℓne2 : ℓ ≠ 2 := by
    intro h2
    subst h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hℓdvd with h | h
    · exact two_not_dvd_two_pow_sub_one h1le (h.trans hKcard)
    · rw [hPcard] at h
      exact Nat.not_even_iff_odd.mpr hPodd (even_iff_two_dvd.mpr h)
  have hℓodd : Odd ℓ := by
    rcases Nat.Prime.eq_two_or_odd hℓp with h | h
    · exact absurd h hℓne2
    · exact Nat.odd_iff.mpr h
  -- `ℓ` divides `|oddPart Q|`, since an element of order `ℓ` is an odd order element of `Q`
  have hdvdOdd : ℓ ∣ Nat.card ↥(Work.ThmF.oddPart Q) := by
    haveI : Fact ℓ.Prime := ⟨hℓp⟩
    rw [Nat.card_eq_fintype_card] at hℓQ
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card ℓ hℓQ
    have hgmem : (g : G) ∈ Work.ThmF.oddPart Q :=
      Work.ThmF.mem_oddPart_of_odd Q g.2 (by rw [Subgroup.orderOf_coe, hg]; exact hℓodd)
    have ho : orderOf (⟨(g : G), hgmem⟩ : ↥(Work.ThmF.oddPart Q)) = ℓ := by
      calc orderOf (⟨(g : G), hgmem⟩ : ↥(Work.ThmF.oddPart Q))
          = orderOf ((⟨(g : G), hgmem⟩ : ↥(Work.ThmF.oddPart Q)) : G) :=
            (Subgroup.orderOf_coe _).symm
        _ = orderOf (g : G) := rfl
        _ = orderOf g := Subgroup.orderOf_coe g
        _ = ℓ := hg
    rw [← ho, Nat.card_eq_fintype_card]
    exact orderOf_dvd_card
  obtain ⟨⟨i, hi, hres⟩, hne⟩ := h3 ℓ hℓp hdvdOdd
  -- `ℓ` divides `2 ^ |P| - 1`
  have hℓm : ℓ ∣ 2 ^ Nat.card P - 1 := by
    rcases (Nat.Prime.dvd_mul hℓp).mp hℓdvd with h | h
    · exact h.trans hKcard
    · exfalso
      rw [hPcard] at h
      rcases (Nat.dvd_prime hPprime).mp h with h1 | h1
      · exact hℓp.ne_one h1
      · exact hne h1
  -- then `ℓ ∣ 2 ^ i`, which is impossible for an odd prime
  have hmpos : 0 < 2 ^ Nat.card P - 1 := by
    have h2 : 2 ^ 2 ≤ 2 ^ Nat.card P := Nat.pow_le_pow_right (by norm_num) hPprime.two_le
    omega
  have hle : ℓ ≤ 2 ^ Nat.card P - 1 := Nat.le_of_dvd hmpos hℓm
  have hdiv2i : ℓ ∣ 2 ^ i := by
    rcases lt_or_eq_of_le hle with hlt | heq
    · have h2i : 2 ^ i < 2 ^ Nat.card P - 1 := by
        have h1 : 2 ^ i ≤ 2 ^ (Nat.card P - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h5 : 1 ≤ Nat.card P - 1 := Nat.le_sub_one_of_lt hPprime.one_lt
        have h7 : 2 ≤ 2 ^ (Nat.card P - 1) := by
          calc (2 : ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (Nat.card P - 1) := Nat.pow_le_pow_right (by norm_num) h5
        have h8 : 2 ^ Nat.card P = 2 * 2 ^ (Nat.card P - 1) := by
          rw [← pow_succ', Nat.sub_one_add_one hPprime.ne_zero]
        have h9 : 1 ≤ 2 ^ (Nat.card P - 1) - 1 := by
          calc (1 : ℕ) = 2 - 1 := by norm_num
            _ ≤ 2 ^ (Nat.card P - 1) - 1 := Nat.sub_le_sub_right h7 1
        have h10 : 2 ^ Nat.card P - 1
            = 2 ^ (Nat.card P - 1) + (2 ^ (Nat.card P - 1) - 1) := by
          rw [h8, two_mul, Nat.add_sub_assoc Nat.one_le_two_pow]
        have h6 : 2 ^ (Nat.card P - 1) < 2 ^ Nat.card P - 1 := by
          rw [h10]
          exact Nat.lt_add_of_pos_right (by omega)
        exact lt_of_le_of_lt h1 h6
      have hmod : ℓ = 2 ^ i := by
        have h : ℓ % (2 ^ Nat.card P - 1) = 2 ^ i % (2 ^ Nat.card P - 1) := hres
        rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt h2i] at h
        exact h
      rw [hmod]
    · subst heq
      have hzero : 2 ^ i % (2 ^ Nat.card P - 1) = 0 := by
        have h : (2 ^ Nat.card P - 1) % (2 ^ Nat.card P - 1)
            = 2 ^ i % (2 ^ Nat.card P - 1) := hres
        rw [Nat.mod_self] at h
        exact h.symm
      exact Nat.dvd_of_mod_eq_zero hzero
  have hℓ2 : ℓ = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (hℓp.dvd_of_dvd_pow hdiv2i) with h1 | h1
    · exact absurd h1 hℓp.ne_one
    · exact h1
  rw [hℓ2] at hℓodd
  exact Nat.not_even_iff_odd.mpr hℓodd (even_iff_two_dvd.mpr dvd_rfl)

/-! ## The abstract Frobenius clause -/

/-- **Step (4), "`KP` is a Frobenius group with kernel `K`".**  If `K ⊓ P = ⊥`, `P` normalises `K`
and `C_K(p) = 1` for `p ∈ P^#`, then the conjugates `P, P^k` (`k ∈ K^#`) meet trivially.

Indeed, if `x ∈ P ⊓ k⁻¹Pk` then the commutator `[k,x] = (kxk⁻¹)x⁻¹` lies both in `P` (as a product
of two elements of `P`) and in `K` (as `k · (xk⁻¹x⁻¹)`), hence is `1`; so `k` commutes with
`x ∈ P^#`, forcing `k = 1`. -/
theorem step4_frob {A : Type} [Group A] (K P : Subgroup A) (hKP : K ⊓ P = ⊥)
    (hnorm : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hcent : ∀ p ∈ P, p ≠ 1 → ∀ k ∈ K, p * k = k * p → k = 1) :
    ∀ k ∈ K, k ≠ 1 → P ⊓ P.map (MulAut.conj k⁻¹).toMonoidHom = ⊥ := by
  intro k hk hk1
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨hxP, hxK⟩ := Subgroup.mem_inf.mp hx
  -- `x = k⁻¹ p k`, so `k x k⁻¹ ∈ P`
  obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp hxK
  have hkx : k * x * k⁻¹ = p := by
    have h : (MulAut.conj k⁻¹) p = x := hpx
    rw [MulAut.conj_apply] at h
    rw [← h]
    group
  -- the commutator is in `K` (from `P` normalising `K`) and in `P`
  have hmemK : k * x * k⁻¹ * x⁻¹ ∈ K := by
    have hmem : x * k⁻¹ * x⁻¹ ∈ K := by
      have h := hnorm x hxP k hk
      rw [show x * k⁻¹ * x⁻¹ = (x * k * x⁻¹)⁻¹ by group]
      exact K.inv_mem h
    rw [show k * x * k⁻¹ * x⁻¹ = k * (x * k⁻¹ * x⁻¹) by group]
    exact K.mul_mem hk hmem
  have hmemP : k * x * k⁻¹ * x⁻¹ ∈ P := by
    rw [show k * x * k⁻¹ * x⁻¹ = p * x⁻¹ by rw [hkx]]
    exact P.mul_mem hp (P.inv_mem hxP)
  have hcommK : k * x * k⁻¹ * x⁻¹ = 1 := by
    have h := Subgroup.mem_inf.mpr ⟨hmemK, hmemP⟩
    rwa [hKP, Subgroup.mem_bot] at h
  have hcomm : x * k = k * x := by
    have h2 : k * x * k⁻¹ = x := by
      have h := congrArg (fun z => z * x) hcommK
      simpa [mul_assoc] using h
    have h3 : k * x = x * k := by
      have h4 : k * x * k⁻¹ * k = x * k := by rw [h2]
      simpa [mul_assoc] using h4
    exact h3.symm
  exact hk1 (hcent x hxP hx1 k hk hcomm)

/-! ## `|Ksub H t| = 2 ^ |P| - 1` -/

/-- In the standing context the order of `K = J(D,t) = Kset H t = Ksub H t` is `2 ^ |P| - 1`:
Ch. V §1 Prop. 3 identifies `K` with the multiplicative group of `Q₀ ≅ 𝔽_{2^{|P|}}`. -/
theorem step4_Kcard {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    Nat.card ↥(Work.ThmF.Ksub H t) = 2 ^ Nat.card P - 1 := by
  classical
  have hS : Submission.Blueprint.Situation G := c.sit
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := c.split
  have hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
    (Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 hS hsplit).2.1
  have hQ0 : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ Nat.card P :=
    Work.ThmF.Prove.Q0sub_card_eq_two_pow hFT hC4 c
  have hcomm := Work.ThmF.L5.involutions_commute hS hC4 hsplit
  have hQ0elem := Work.ThmF.ChV12.Q0sub_elementary H hcomm
  -- `Q₀sub H = Inv H ∪ {1}`
  have hset : ((Work.ThmF.Q0sub H : Subgroup G) : Set G)
      = Submission.Blueprint.involutions (H : Set G) ∪ {1} := by
    ext x
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · exact Or.inr hx1
      · exact Or.inl (hQ0elem.2.2.2 x hx hx1)
    · intro hx
      rcases hx with h | h
      · exact Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H h)
      · rw [h]; exact (Work.ThmF.Q0sub H).one_mem
  have hdisj : Disjoint (Submission.Blueprint.involutions (H : Set G)) ({1} : Set G) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_singleton_iff] at hx2
    subst hx2
    exact absurd hx1.2 (by norm_num)
  have hInv1 : Nat.card ↥(Work.ThmF.Q0sub H)
      = (Submission.Blueprint.involutions (H : Set G)).ncard + 1 := by
    calc Nat.card ↥(Work.ThmF.Q0sub H)
        = ((Work.ThmF.Q0sub H : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
      _ = (Submission.Blueprint.involutions (H : Set G) ∪ {1} : Set G).ncard := by rw [hset]
      _ = (Submission.Blueprint.involutions (H : Set G)).ncard + 1 := by
            rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton]
  have hKset : (Work.ThmF.Kset H t).ncard
      = (Submission.Blueprint.involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv hsplit.stronglyEmbedded hsplit.invol hsplit.not_mem
  have hKcard : Nat.card ↥(Work.ThmF.Ksub H t) = (Work.ThmF.Kset H t).ncard := by
    calc Nat.card ↥(Work.ThmF.Ksub H t)
        = ((Work.ThmF.Ksub H t : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
      _ = (Work.ThmF.Kset H t).ncard := by rw [hKsub]
  calc Nat.card ↥(Work.ThmF.Ksub H t) = (Work.ThmF.Kset H t).ncard := hKcard
    _ = (Submission.Blueprint.involutions (H : Set G)).ncard := hKset
    _ = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by rw [hInv1]; omega
    _ = 2 ^ Nat.card P - 1 := by rw [hQ0]

/-! ## The rigidity of the joint action of `Ksub` and `P` on `Q₀` -/

/-- The image of `k ∈ Ksub H t` under the isomorphism `κ : Ksub H t ≃* Fˣ` of §1 Prop. 3 is
determined by its action on `Q₀ ≅ F`: if `conj k` is multiplication by `κ k` and `conj p`
(`p ∈ C_D(t)`) is a field automorphism, then `κ k = 1` whenever `conj k` and `conj p` agree on
`Q₀` — evaluate both at the element of `Q₀` corresponding to `1 ∈ F`. -/
theorem step4_kappa_eq_one {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {F : Type}
    [Field F] (e : ↥(Work.ThmF.Q0sub H) ≃* Multiplicative F)
    (κ : ↥(Work.ThmF.Ksub H t) ≃* Fˣ)
    (ρ : ↥(Submission.Blueprint.centD H t) →* (F ≃+* F))
    (hactK : ∀ (k : ↥(Work.ThmF.Ksub H t)) (x : ↥(Work.ThmF.Q0sub H))
      (hx : (k : G) * x * (k : G)⁻¹ ∈ Work.ThmF.Q0sub H),
      Multiplicative.toAdd (e ⟨(k : G) * x * (k : G)⁻¹, hx⟩) = (κ k : F) * Multiplicative.toAdd (e x))
    (hactV : ∀ (v : ↥(Submission.Blueprint.centD H t)) (x : ↥(Work.ThmF.Q0sub H))
      (hx : (v : G) * x * (v : G)⁻¹ ∈ Work.ThmF.Q0sub H),
      Multiplicative.toAdd (e ⟨(v : G) * x * (v : G)⁻¹, hx⟩) = (ρ v) (Multiplicative.toAdd (e x)))
    {k : ↥(Work.ThmF.Ksub H t)} {p : G} (hpcd : p ∈ Submission.Blueprint.centD H t)
    (hmemK : ∀ x ∈ Work.ThmF.Q0sub H, (k : G) * x * (k : G)⁻¹ ∈ Work.ThmF.Q0sub H)
    (hcom : ∀ x ∈ Work.ThmF.Q0sub H, (k : G) * x * (k : G)⁻¹ = p * x * p⁻¹) :
    κ k = 1 := by
  -- the element `x₀` with `e x₀ = 1`
  let x₀ : ↥(Work.ThmF.Q0sub H) := e.symm (Multiplicative.ofAdd (1 : F))
  have hx₀ : Multiplicative.toAdd (e x₀) = 1 := by
    simp [x₀]
  have hm1 : (k : G) * (x₀ : G) * (k : G)⁻¹ ∈ Work.ThmF.Q0sub H := hmemK (x₀ : G) x₀.2
  have hm2 : p * (x₀ : G) * p⁻¹ ∈ Work.ThmF.Q0sub H := (hcom (x₀ : G) x₀.2) ▸ hm1
  have heq : e ⟨(k : G) * (x₀ : G) * (k : G)⁻¹, hm1⟩ = e ⟨p * (x₀ : G) * p⁻¹, hm2⟩ := by
    congr 1
    exact Subtype.ext (hcom (x₀ : G) x₀.2)
  have h1 := hactK k x₀ hm1
  have h2 : Multiplicative.toAdd (e ⟨p * (x₀ : G) * p⁻¹, hm2⟩) = 1 := by
    rw [hactV ⟨p, hpcd⟩ x₀ hm2, hx₀, map_one]
  have h3 : (κ k : F) = 1 :=
    calc (κ k : F) = (κ k : F) * Multiplicative.toAdd (e x₀) := by rw [hx₀, mul_one]
      _ = Multiplicative.toAdd (e ⟨(k : G) * (x₀ : G) * (k : G)⁻¹, hm1⟩) := h1.symm
      _ = Multiplicative.toAdd (e ⟨p * (x₀ : G) * p⁻¹, hm2⟩) := by rw [heq]
      _ = 1 := h2
  exact Units.ext h3

/-- **Step (4), rigidity of the action on `Q₀` (step (1) + §1 Prop. 3).**  Two clauses:

1. if `conj k = conj p` on `Q₀` (with `k ∈ Ksub H t`, `p ∈ P`) then `k = 1`;
2. if the conjugation actions of `k ∈ Ksub H t` and of `p ∈ P^#` commute on `Q₀`, then `k = 1`.

Via `prop3`, `conj k` acts on `Q₀ ≅ F` by multiplication by `a = κ k` and `conj p` by the field
automorphism `σ = ρ p ≠ 1` (because `P ⊓ W = ⊥` and `ρ.ker = W`).  Clause 1 is `a · 1 = σ 1 = 1`;
clause 2 is `a · σ(1) = σ(a · 1)`, i.e. `σ a = a`, and `a` lies in the fixed field of `σ`, which is
the prime field `𝔽₂` since `|F| = 2^{|P|}` with `|P|` prime (`step4_field`). -/
theorem step4_act {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hfield : ∀ {F : Type} [Field F] [Fintype F] {q : ℕ}, q.Prime → Nat.card F = 2 ^ q →
      ∀ {σ : F ≃+* F}, σ ≠ 1 → ∀ {a : Fˣ}, (σ a : F) = (a : F) → a = 1)
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    (∀ k ∈ Work.ThmF.Ksub H t, ∀ p ∈ P,
      (∀ x ∈ Work.ThmF.Q0sub H, k * x * k⁻¹ = p * x * p⁻¹) → k = 1) ∧
    (∀ k ∈ Work.ThmF.Ksub H t, ∀ p ∈ P, p ≠ 1 →
      (∀ x ∈ Work.ThmF.Q0sub H, k * (p * x * p⁻¹) * k⁻¹ = p * (k * x * k⁻¹) * p⁻¹) → k = 1) := by
  classical
  have hS : Submission.Blueprint.Situation G := c.sit
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := c.split
  obtain ⟨hKcyc, hKsub, hKn⟩ := Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 hS hsplit
  have hcomm := Work.ThmF.L5.involutions_commute hS hC4 hsplit
  have hreg := Work.ThmF.L5.Kset_regular hsplit
  obtain ⟨u, hu, huV⟩ := (hC4 G hS H hsplit.stronglyEmbedded t hsplit.invol hsplit.not_mem).2.1
  obtain ⟨F, hFld, hFint, e, κ, ρ, hcardF, hactK, hactV, hker⟩ :=
    Work.ThmF.ChV12.prop3 H Q t hsplit hcomm hKsub hKcyc hKn hreg u hu huV
  letI : Field F := hFld
  letI : Fintype F := hFint
  have hFcard : Nat.card F = 2 ^ Nat.card P := by
    rw [hcardF, Work.ThmF.Prove.Q0sub_card_eq_two_pow hFT hC4 c]
  -- `P ⊓ W = ⊥`, so `ρ p ≠ 1` for `p ∈ P^#`
  have hPW : P ⊓ Work.ThmF.W H t = ⊥ := by
    rw [inf_comm]
    exact Work.ThmF.ChV3.W_inf_eq_bot_of_prime hS hC4 hsplit c.P_prime c.F1
  have hρne : ∀ p : ↥P, (p : G) ≠ 1 → ρ ⟨(p : G), c.P_le p.2⟩ ≠ 1 := by
    intro p hp1 hρ1
    have hmem : (⟨(p : G), c.P_le p.2⟩ : ↥(Submission.Blueprint.centD H t)) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, hρ1]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    have hbot : (p : G) ∈ P ⊓ Work.ThmF.W H t := ⟨p.2, hmem⟩
    rw [hPW, Subgroup.mem_bot] at hbot
    exact hp1 hbot
  constructor
  · -- clause 1
    intro k hk p hp hcom
    have hmemK : ∀ x ∈ Work.ThmF.Q0sub H, (⟨k, hk⟩ : ↥(Work.ThmF.Ksub H t)) * x
        * (⟨k, hk⟩ : ↥(Work.ThmF.Ksub H t))⁻¹ ∈ Work.ThmF.Q0sub H :=
      fun x hx => Work.ThmF.ChV12.conj_mem_Q0sub ((Work.ThmF.ChV12.Ksub_le_H H t) hk) hx
    have hκ : κ ⟨k, hk⟩ = 1 :=
      step4_kappa_eq_one e κ ρ hactK hactV (c.P_le hp) hmemK hcom
    have h1 : (⟨k, hk⟩ : ↥(Work.ThmF.Ksub H t)) = 1 := by
      apply κ.injective
      rw [hκ, map_one]
    exact congrArg Subtype.val h1
  · -- clause 2
    intro k hk p hp hp1 hcom
    have hσne : ρ ⟨p, c.P_le hp⟩ ≠ 1 := hρne ⟨p, hp⟩ hp1
    -- the fixed-point equation on `F`
    have hmain : ∀ y : F, (κ ⟨k, hk⟩ : F) * (ρ ⟨p, c.P_le hp⟩) y
        = (ρ ⟨p, c.P_le hp⟩) ((κ ⟨k, hk⟩ : F) * y) := by
      intro y
      set x : ↥(Work.ThmF.Q0sub H) := e.symm (Multiplicative.ofAdd y) with hx
      have hxy : Multiplicative.toAdd (e x) = y := by simp [x]
      have hm1 : k * (x : G) * k⁻¹ ∈ Work.ThmF.Q0sub H :=
        Work.ThmF.ChV12.conj_mem_Q0sub ((Work.ThmF.ChV12.Ksub_le_H H t) hk) x.2
      have hm2 : p * (x : G) * p⁻¹ ∈ Work.ThmF.Q0sub H :=
        Work.ThmF.ChV12.conj_mem_Q0sub ((Work.ThmF.ChV12.centD_le_H H t) (c.P_le hp)) x.2
      have hm3 : k * (p * (x : G) * p⁻¹) * k⁻¹ ∈ Work.ThmF.Q0sub H :=
        Work.ThmF.ChV12.conj_mem_Q0sub ((Work.ThmF.ChV12.Ksub_le_H H t) hk) hm2
      have hm4 : p * (k * (x : G) * k⁻¹) * p⁻¹ ∈ Work.ThmF.Q0sub H :=
        Work.ThmF.ChV12.conj_mem_Q0sub ((Work.ThmF.ChV12.centD_le_H H t) (c.P_le hp)) hm1
      have hA := hactK ⟨k, hk⟩ ⟨p * (x : G) * p⁻¹, hm2⟩ hm3
      have hB := hactV ⟨p, c.P_le hp⟩ ⟨k * (x : G) * k⁻¹, hm1⟩ hm4
      have hC := hactK ⟨k, hk⟩ x hm1
      have hD := hactV ⟨p, c.P_le hp⟩ x hm2
      have hE : k * (p * (x : G) * p⁻¹) * k⁻¹ = p * (k * (x : G) * k⁻¹) * p⁻¹ :=
        hcom (x : G) x.2
      have key : Multiplicative.toAdd (e ⟨k * (p * (x : G) * p⁻¹) * k⁻¹, hm3⟩)
          = Multiplicative.toAdd (e ⟨p * (k * (x : G) * k⁻¹) * p⁻¹, hm4⟩) := by
        have hsub : (⟨k * (p * (x : G) * p⁻¹) * k⁻¹, hm3⟩ : ↥(Work.ThmF.Q0sub H))
            = ⟨p * (k * (x : G) * k⁻¹) * p⁻¹, hm4⟩ := Subtype.ext hE
        rw [hsub]
      calc (κ ⟨k, hk⟩ : F) * (ρ ⟨p, c.P_le hp⟩) y
          = (κ ⟨k, hk⟩ : F) * Multiplicative.toAdd (e ⟨p * (x : G) * p⁻¹, hm2⟩) := by
            rw [hD, hxy]
        _ = Multiplicative.toAdd (e ⟨k * (p * (x : G) * p⁻¹) * k⁻¹, hm3⟩) := hA.symm
        _ = Multiplicative.toAdd (e ⟨p * (k * (x : G) * k⁻¹) * p⁻¹, hm4⟩) := key
        _ = (ρ ⟨p, c.P_le hp⟩) (Multiplicative.toAdd (e ⟨k * (x : G) * k⁻¹, hm1⟩)) := hB
        _ = (ρ ⟨p, c.P_le hp⟩) ((κ ⟨k, hk⟩ : F) * y) := by rw [hC, hxy]
    -- evaluate at `y = 1`
    have hfix : (κ ⟨k, hk⟩ : F) = (ρ ⟨p, c.P_le hp⟩) ((κ ⟨k, hk⟩ : F)) := by
      simpa only [map_one, mul_one] using hmain 1
    have hone : κ ⟨k, hk⟩ = 1 :=
      hfield c.P_prime hFcard (σ := ρ ⟨p, c.P_le hp⟩) hσne (a := κ ⟨k, hk⟩) hfix.symm
    have h1 : (⟨k, hk⟩ : ↥(Work.ThmF.Ksub H t)) = 1 := by
      apply κ.injective
      rw [hone, map_one]
    exact congrArg Subtype.val h1

theorem step4 (hW : Work.ThmF.WielandtFixedPoint) {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G} (hFT : Submission.Blueprint.FeitThompsonProp) (hTh : Submission.Blueprint.ThompsonFrobeniusProp) (hC4 : Submission.Blueprint.ChIIFourProp) (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h3 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card ↥(Work.ThmF.oddPart Q) → (∃ i < Nat.card P, ℓ ≡ 2 ^ i [MOD 2 ^ Nat.card P - 1]) ∧ ℓ ≠ Nat.card P) (hPfaith : ∀ p ∈ P, (∀ q ∈ Q, p * q * p⁻¹ = q) → p = 1) : Nat.card Q = Nat.card ↥(Work.ThmF.ChV3.CQ Q P) ^ Nat.card P := by
  classical
  have hS : Submission.Blueprint.Situation G := c.sit
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := c.split
  -- `Q ≠ ⊥`: otherwise `P` acts trivially on `Q`, so `P = ⊥` by faithfulness, contradicting
  -- `|P|` prime
  have hQne : Q ≠ ⊥ := by
    intro hQbot
    have hPle : P ≤ (⊥ : Subgroup G) := by
      intro p hp
      rw [Subgroup.mem_bot]
      refine hPfaith p hp (fun q hq => ?_)
      have hq1 : q = 1 := by
        have : q ∈ (⊥ : Subgroup G) := by rw [← hQbot]; exact hq
        simpa using this
      rw [hq1]; simp
    have hPbot : P = ⊥ := le_bot_iff.mp hPle
    have h1 : Nat.card P = 1 := by rw [hPbot, Subgroup.card_bot]
    exact c.P_prime.ne_one h1
  -- the conjugation action of `H` (hence of `Ksub H t` and of `P`) on `Q`
  have hKnorm : Work.ThmF.Ksub H t ≤ Subgroup.normalizer (Q : Set G) :=
    (Work.ThmF.ChV12.Ksub_le_H H t).trans hsplit.normal
  have hPnorm : P ≤ Subgroup.normalizer (Q : Set G) :=
    (c.P_le.trans (Work.ThmF.ChV12.centD_le_H H t)).trans hsplit.normal
  have hKsub_eq : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
    (Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 hS hsplit).2.1
  let φK : ↥(Work.ThmF.Ksub H t) →* MulAut ↥Q :=
    Work.ThmF.ChV12.conjAutOfLe Q (Work.ThmF.Ksub H t) hKnorm
  let φP : ↥P →* MulAut ↥Q := Work.ThmF.ChV12.conjAutOfLe Q P hPnorm
  let Kbar : Subgroup (MulAut ↥Q) := φK.range
  let Pbar : Subgroup (MulAut ↥Q) := φP.range
  have hφKval : ∀ (k : ↥(Work.ThmF.Ksub H t)) (y : ↥Q),
      ((φK k) y : G) = (k : G) * (y : G) * (k : G)⁻¹ :=
    fun k y => Work.ThmF.ChV12.conjAutOfLe_apply Q (Work.ThmF.Ksub H t) hKnorm k y
  have hφPval : ∀ (p : ↥P) (y : ↥Q),
      ((φP p) y : G) = (p : G) * (y : G) * (p : G)⁻¹ :=
    fun p y => Work.ThmF.ChV12.conjAutOfLe_apply Q P hPnorm p y
  have hφPvalinv : ∀ (p : ↥P) (y : ↥Q),
      (((φP p)⁻¹) y : G) = (p : G)⁻¹ * (y : G) * (p : G) := by
    intro p y
    have h := hφPval p ((φP p)⁻¹ y)
    have h2 : (φP p) ((φP p)⁻¹ y) = y := by
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    rw [h2] at h
    rw [h]; group
  -- `(2)` `φP` is injective, i.e. `|P̄| = |P|` (this is `hPfaith`)
  have hφPinj : Function.Injective φP := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine hPfaith (a : G) a.2 (fun q hq => ?_)
    have h2 : ((φP a) ⟨q, hq⟩ : ↥Q) = ⟨q, hq⟩ := by
      rw [ha, MulAut.one_apply]
    have h3 : ((φP a) ⟨q, hq⟩ : G) = (q : G) := congrArg Subtype.val h2
    rw [hφPval a ⟨q, hq⟩] at h3
    exact h3
  have hPbarCard : Nat.card Pbar = Nat.card P := by
    rw [show Pbar = Subgroup.map φP ⊤ from MonoidHom.range_eq_map φP,
      Subgroup.card_map_of_injective hφPinj (K := ⊤), Subgroup.card_top]
  -- `(3)` `φK` is injective (`C_{Q}(k) = 1` for `k ∈ Kset H t^#`, Ch. V §1 Prop. 1 a)
  have hφKinj : Function.Injective φK := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    by_contra ha1
    have hakset : (a : G) ∈ Work.ThmF.Kset H t := by rw [← hKsub_eq]; exact a.2
    have hQbot : Q = ⊥ := by
      rw [eq_bot_iff]
      intro q hq
      rw [Subgroup.mem_bot]
      refine Work.ThmF.ChV12.prop1a hS hC4 H Q t hsplit (a : G) hakset ha1 q hq ?_
      have h2 : ((φK a) ⟨q, hq⟩ : ↥Q) = ⟨q, hq⟩ := by
        rw [ha, MulAut.one_apply]
      have h3 : ((φK a) ⟨q, hq⟩ : G) = (q : G) := congrArg Subtype.val h2
      rw [hφKval a ⟨q, hq⟩] at h3
      calc (q : G) * (a : G) = ((a : G) * (q : G) * (a : G)⁻¹) * (a : G) := by rw [h3]
        _ = (a : G) * (q : G) := by group
    exact hQne hQbot
  have hKbarCard : Nat.card Kbar = 2 ^ Nat.card P - 1 := by
    rw [show Kbar = Subgroup.map φK ⊤ from MonoidHom.range_eq_map φK,
      Subgroup.card_map_of_injective hφKinj (K := ⊤), Subgroup.card_top]
    exact step4_Kcard hFT hC4 c
  -- `(4)` `K̄#` acts fixed-point-freely on `Q`
  have hfpf : ∀ k ∈ Kbar, k ≠ 1 → ∀ q : ↥Q, k q = q → q = 1 := by
    intro k hk hk1 q hq
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hk
    have ha1 : (a : G) ≠ 1 := by
      intro h
      exact hk1 (by rw [← ha, show a = 1 from Subtype.ext h, map_one])
    have hakset : (a : G) ∈ Work.ThmF.Kset H t := by rw [← hKsub_eq]; exact a.2
    have hqa : (a : G) * (q : G) * (a : G)⁻¹ = (q : G) := by
      have h2 : ((φK a) q : ↥Q) = q := by rw [ha]; exact hq
      have h3 : ((φK a) q : G) = (q : G) := congrArg Subtype.val h2
      rwa [hφKval a q] at h3
    have hcomm : (q : G) * (a : G) = (a : G) * (q : G) := by
      calc (q : G) * (a : G) = ((a : G) * (q : G) * (a : G)⁻¹) * (a : G) := by rw [hqa]
        _ = (a : G) * (q : G) := by group
    have hq1 : (q : G) = 1 :=
      Work.ThmF.ChV12.prop1a hS hC4 H Q t hsplit (a : G) hakset ha1 q q.2 hcomm
    exact Subtype.ext hq1
  -- `(5)` `C_Q(K̄) = 1` (`K̄ ≠ 1` since `K̄ ≅ Kset H t ≠ 1`)
  have hCQK : ∀ q : ↥Q, (∀ k ∈ Kbar, k q = q) → q = 1 := by
    intro q hq
    have hne : ∃ a ∈ Work.ThmF.Kset H t, a ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have h1 : 2 ≤ (Work.ThmF.Kset H t).ncard := by
        rw [Work.ThmF.Bender.cardKsetEqInv hsplit.stronglyEmbedded hsplit.invol hsplit.not_mem]
        exact Work.ThmF.Bender.cardInvGeTwo hsplit.stronglyEmbedded hS.1.1
      have hle : (Work.ThmF.Kset H t).ncard ≤ 1 := by
        have hsub : Work.ThmF.Kset H t ⊆ ({1} : Set G) := fun x hx => by
          simp only [Set.mem_singleton_iff]; exact hcon x hx
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        simpa using this
      omega
    obtain ⟨a, hak, ha1⟩ := hne
    have haksub : a ∈ Work.ThmF.Ksub H t := Work.ThmF.Kset_le_Ksub H t hak
    have hk1 : φK ⟨a, haksub⟩ ≠ 1 := by
      intro h
      have h2 := hφKinj (h.trans (map_one φK).symm)
      exact ha1 (congrArg Subtype.val h2)
    have hmem : φK ⟨a, haksub⟩ ∈ Kbar := MonoidHom.mem_range.mpr ⟨⟨a, haksub⟩, rfl⟩
    exact hfpf _ hmem hk1 q (hq _ hmem)
  -- `(6)` `P̄` normalises `K̄`
  have hnormK : ∀ g ∈ Pbar, ∀ k ∈ Kbar, g * k * g⁻¹ ∈ Kbar := by
    intro g hg k hk
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hg
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hk
    have hmem : (p : G) * (a : G) * (p : G)⁻¹ ∈ Work.ThmF.Ksub H t :=
      Work.ThmF.ChV12.conj_mem_Ksub H t (c.P_le p.2) (a : G) a.2
    refine MonoidHom.mem_range.mpr ⟨⟨(p : G) * (a : G) * (p : G)⁻¹, hmem⟩, ?_⟩
    rw [← hp, ← ha]
    ext y
    show ((φK ⟨(p : G) * (a : G) * (p : G)⁻¹, hmem⟩) y : G)
        = ((φP p * φK a * (φP p)⁻¹) y : G)
    rw [hφKval, MulAut.mul_apply, MulAut.mul_apply, hφPval, hφKval, hφPvalinv]
    simp only [Subtype.coe_mk]
    group
  -- `(7)` `K̄ ⊓ P̄ = ⊥` and `C_{K̄}(P̄) = 1` (rigidity of the action on `Q₀`)
  have hact : (∀ k ∈ Work.ThmF.Ksub H t, ∀ p ∈ P,
      (∀ x ∈ Work.ThmF.Q0sub H, k * x * k⁻¹ = p * x * p⁻¹) → k = 1) ∧
      (∀ k ∈ Work.ThmF.Ksub H t, ∀ p ∈ P, p ≠ 1 →
      (∀ x ∈ Work.ThmF.Q0sub H, k * (p * x * p⁻¹) * k⁻¹ = p * (k * x * k⁻¹) * p⁻¹) → k = 1) :=
    step4_act (hfield := step4_field) hFT hC4 c
  have hKbarPbar : Kbar ⊓ Pbar = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxK, hxP⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hxK
    obtain ⟨p, hp'⟩ := MonoidHom.mem_range.mp hxP
    have hcom : ∀ x' ∈ Work.ThmF.Q0sub H, (a : G) * x' * (a : G)⁻¹ = p * x' * p⁻¹ := by
      intro x' hx'
      have hx'Q : x' ∈ Q := Work.ThmF.ChV12.Q0sub_le_Q hsplit hx'
      have h2 : (φK a) ⟨x', hx'Q⟩ = (φP p) ⟨x', hx'Q⟩ := by
        rw [show φK a = x from ha, show φP p = x from hp']
      have h3 : ((φK a) ⟨x', hx'Q⟩ : G) = ((φP p) ⟨x', hx'Q⟩ : G) :=
        congrArg Subtype.val h2
      rw [hφKval a ⟨x', hx'Q⟩, hφPval p ⟨x', hx'Q⟩] at h3
      exact h3
    have h1 : a = 1 := Subtype.ext (hact.1 (a : G) a.2 (p : G) p.2 hcom)
    rw [show x = φK a from ha.symm, h1, map_one]
  have hcent : ∀ u ∈ Pbar, u ≠ 1 → ∀ v ∈ Kbar, u * v = v * u → v = 1 := by
    intro u hu hu1 v hv huv
    obtain ⟨p, hp'⟩ := MonoidHom.mem_range.mp hu
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hv
    have hp1 : (p : G) ≠ 1 := by
      intro h
      exact hu1 (by rw [← hp', show p = 1 from Subtype.ext h, map_one])
    have hcom : ∀ x' ∈ Work.ThmF.Q0sub H,
        (a : G) * (p * x' * p⁻¹) * (a : G)⁻¹ = p * ((a : G) * x' * (a : G)⁻¹) * p⁻¹ := by
      intro x' hx'
      have hx'Q : x' ∈ Q := Work.ThmF.ChV12.Q0sub_le_Q hsplit hx'
      have h2 : (u * v) ⟨x', hx'Q⟩ = (v * u) ⟨x', hx'Q⟩ := by rw [huv]
      have h3 : (u (v ⟨x', hx'Q⟩) : G) = (v (u ⟨x', hx'Q⟩) : G) := by
        have h := congrArg Subtype.val h2
        simpa only [MulAut.mul_apply] using h
      have hL : (u (v ⟨x', hx'Q⟩) : G)
          = (p : G) * ((a : G) * (x' : G) * (a : G)⁻¹) * (p : G)⁻¹ := by
        rw [show u = φP p from hp'.symm, show v = φK a from ha.symm, hφPval, hφKval]
      have hR : (v (u ⟨x', hx'Q⟩) : G)
          = (a : G) * ((p : G) * (x' : G) * (p : G)⁻¹) * (a : G)⁻¹ := by
        rw [show v = φK a from ha.symm, show u = φP p from hp'.symm, hφKval, hφPval]
      rw [hL, hR] at h3
      exact h3.symm
    have h1 : a = 1 := Subtype.ext (hact.2 (a : G) a.2 (p : G) p.2 hp1 hcom)
    rw [show v = φK a from ha.symm, h1, map_one]
  have hfrob : ∀ k ∈ Kbar, k ≠ 1 →
      Pbar ⊓ Submission.Blueprint.conj k⁻¹ Pbar = ⊥ :=
    step4_frob Kbar Pbar hKbarPbar hnormK hcent
  -- `(8)` coprimality (step (3))
  have hPodd : Odd (Nat.card P) := by
    rcases Nat.Prime.eq_two_or_odd c.P_prime with h | h
    · exfalso
      have hDodd := Work.ThmF.split_odd_card_twoPoint hsplit
      have hdvd : Nat.card P ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) :=
        (Subgroup.card_dvd_of_le c.P_le).trans
          (Subgroup.card_dvd_of_le (inf_le_left : Submission.Blueprint.centD H t ≤
            Submission.Blueprint.twoPoint H t))
      exact Nat.not_even_iff_odd.mpr hDodd (even_iff_two_dvd.mpr (h ▸ hdvd))
    · exact Nat.odd_iff.mpr h
  have hcop : Nat.Coprime (Nat.card Kbar * Nat.card Pbar) (Nat.card Q) :=
    step4_coprime c.P_prime hPodd h3 (by rw [hKbarCard]) (by rw [hPbarCard])
  -- `(9)` Wielandt's fixed-point formula
  have hWapp := hW ↥Q (Nat.card P) c.P_prime Kbar Pbar hcop hfpf hCQK hPbarCard hnormK hfrob
  -- `(10)` the fixed points of `P̄` on `Q` are `C_Q(P)`
  have hfixset : {q : ↥Q | ∀ g ∈ Pbar, g q = q}
      = {q : ↥Q | (q : G) ∈ Subgroup.centralizer (P : Set G)} := by
    ext q
    constructor
    · intro hq
      show (q : G) ∈ Subgroup.centralizer (P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have h := hq (φP ⟨p, hp⟩) (MonoidHom.mem_range.mpr ⟨⟨p, hp⟩, rfl⟩)
      have h2 : ((φP ⟨p, hp⟩) q : G) = (p : G) * (q : G) * (p : G)⁻¹ := hφPval ⟨p, hp⟩ q
      have h3 : ((φP ⟨p, hp⟩) q : G) = (q : G) := congrArg Subtype.val h
      rw [h2] at h3
      calc (p : G) * (q : G) = ((p : G) * (q : G) * (p : G)⁻¹) * (p : G) := by group
        _ = (q : G) * (p : G) := by rw [h3]
    · intro hq g hg
      obtain ⟨p, hp'⟩ := MonoidHom.mem_range.mp hg
      apply Subtype.ext
      rw [show g = φP p from hp'.symm, hφPval]
      rw [Subgroup.mem_centralizer_iff.mp hq p p.2]
      group
  have hfixcard : Set.ncard {q : ↥Q | (q : G) ∈ Subgroup.centralizer (P : Set G)}
      = Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr
      ⟨fun q => ⟨(q.1 : G), q.1.2, q.2⟩,
       fun x => ⟨⟨(x : G), x.2.1⟩, x.2.2⟩, fun q => rfl, fun x => rfl⟩
  rw [hWapp, hfixset, hfixcard]

end Work.ThmF.Prove
