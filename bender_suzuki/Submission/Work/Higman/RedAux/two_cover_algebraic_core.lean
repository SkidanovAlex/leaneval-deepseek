import Mathlib
import Submission.Work.Higman.c4_field_core
import Submission.Work.Higman.bivariate_monomial_indep
import Submission.Work.Higman.bilinear_frob
import Submission.Work.Higman.double_sum_diag
import Submission.Work.Higman.frob_diag_zero
import Submission.Work.Higman.Q3.two_pow_add_eq_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Higman.RedAux

/-! ## Auxiliary lemmas for `two_cover_algebraic_core`. -/

/-- In a finite field of cardinality `2 ^ n`, a group element of order `2 ^ n - 1` is a generator
of the multiplicative group: every non-zero element is one of its powers. -/
private lemma lam_pow_exists {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    {lam : F} (hlam : orderOf lam = 2 ^ n - 1) :
    ∀ y : F, y ≠ 0 → ∃ m : ℕ, lam ^ m = y := by
  have hN : (2 : ℕ) ^ n - 1 ≠ 0 := by
    have h2 : 2 ≤ 2 ^ n := by
      calc (2:ℕ) = 2^1 := by norm_num
        _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hlam0 : lam ≠ 0 := by
    intro h
    have h1 : lam ^ (2 ^ n - 1) = 1 := by rw [← hlam]; exact pow_orderOf_eq_one lam
    rw [h, zero_pow hN] at h1
    exact zero_ne_one h1
  intro y hy
  set u : Fˣ := Units.mk0 lam hlam0 with hu
  have huval : (u : F) = lam := by rw [hu]; exact Units.val_mk0 hlam0
  have hord : orderOf u = 2 ^ n - 1 := by
    rw [← orderOf_units (y := u), huval, hlam]
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord]
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hcard]
  have hmem : Units.mk0 y hy ∈ Subgroup.zpowers u := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff.mp hmem)
  have hNint : (((2:ℕ) ^ n - 1 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hN
  have hNu : u ^ ((((2:ℕ) ^ n - 1 : ℕ) : ℤ)) = 1 := by
    rw [zpow_natCast, ← hord]; exact pow_orderOf_eq_one u
  have step1 : u ^ k = u ^ (k % ((((2:ℕ) ^ n - 1 : ℕ) : ℤ))) := zpow_eq_zpow_emod k hNu
  have hck : k % ((((2:ℕ) ^ n - 1 : ℕ) : ℤ)) = ((k % ((((2:ℕ) ^ n - 1 : ℕ) : ℤ))).toNat : ℤ) :=
    (Int.toNat_of_nonneg (Int.emod_nonneg k hNint)).symm
  refine ⟨(k % ((((2:ℕ) ^ n - 1 : ℕ) : ℤ))).toNat, ?_⟩
  have key : u ^ (k % ((((2:ℕ) ^ n - 1 : ℕ) : ℤ))).toNat = Units.mk0 y hy := by
    rw [← zpow_natCast (a:=u) ((k % ((((2:ℕ) ^ n - 1 : ℕ) : ℤ))).toNat), ← hck, ← step1, hk]
  have h2 := congrArg (fun z : Fˣ => (z:F)) key
  rw [Units.val_pow_eq_pow_val, huval, Units.val_mk0] at h2
  exact h2

/-- `a ≡ b (mod orderOf ν)` implies `ν ^ a = ν ^ b` for `ν ≠ 0`. -/
private lemma pow_eq_pow_of_modEq {F : Type} [Field F] {nu : F} (hnu : nu ≠ 0) {a b : ℕ}
    (h : a ≡ b [MOD orderOf nu]) : nu ^ a = nu ^ b := by
  have hu : (Units.mk0 nu hnu) ^ a = (Units.mk0 nu hnu) ^ b := by
    rw [pow_eq_pow_iff_modEq]
    rwa [← orderOf_units (y := Units.mk0 nu hnu), Units.val_mk0]
  have h2 := congrArg (fun z : Fˣ => (z:F)) hu
  rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0] at h2

/-- `ν ^ a = ν ^ b` with `orderOf ν = 2 ^ n - 1` and `ν ≠ 0` gives the congruence. -/
private lemma pow_eq_pow_modEq {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} {nu : F} (hnu : nu ≠ 0) (hnuord : orderOf nu = 2 ^ n - 1) {a b : ℕ}
    (h : nu ^ a = nu ^ b) : a ≡ b [MOD 2 ^ n - 1] := by
  have hu : (Units.mk0 nu hnu) ^ a = (Units.mk0 nu hnu) ^ b := by
    apply Units.ext; push_cast; exact h
  have h2 := (pow_eq_pow_iff_modEq).mp hu
  rw [← orderOf_units (y := Units.mk0 nu hnu), Units.val_mk0, hnuord] at h2
  exact h2

/-- A congruence `2 ^ A + 2 ^ B ≡ 2 ^ C (mod 2 ^ n - 1)` packaged as a `ℤ`-divisibility. -/
private lemma int_dvd_of_modeq {n A B C : ℕ} (h : 2 ^ A + 2 ^ B ≡ 2 ^ C [MOD 2 ^ n - 1]) :
    (2 ^ n - 1 : ℤ) ∣ (2 ^ A : ℤ) + 2 ^ B - 2 ^ C := by
  have h1 := Nat.ModEq.dvd h
  rw [Nat.cast_sub (Nat.one_le_two_pow)] at h1
  push_cast at h1
  have h2 : (2 ^ n - 1 : ℤ) ∣ -(((2 ^ A : ℤ) + 2 ^ B) - 2 ^ C) := by
    convert h1 using 1; ring
  simpa using dvd_neg.mp h2

/-- The left radical of an equivariant biadditive map `Φ` (with `Φ (λ a) (σ b) = λ * Φ a b`,
`λ` a generator of `Fˣ`, `σ ≠ 0`, `Φ ≠ 0`) is trivial. -/
private lemma left_radical_eq_bot {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (hn : 1 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    {lam sig : F} (hlam : orderOf lam = 2 ^ n - 1) (hsig : sig ≠ 0)
    {Φ : F → F → F}
    (hΦ1 : ∀ a b c : F, Φ (a + b) c = Φ a c + Φ b c)
    (hΦeq : ∀ a b : F, Φ (lam * a) (sig * b) = lam * Φ a b)
    (hΦne : ∃ a b : F, Φ a b ≠ 0) :
    ∀ z, (∀ y, Φ z y = 0) → z = 0 := by
  have hzero : ∀ c : F, Φ 0 c = 0 := by
    intro c
    have h := hΦ1 0 0 c
    rw [add_zero] at h
    rw [CharTwo.add_self_eq_zero] at h
    exact h
  intro z hz
  by_contra hz0
  have hstep : ∀ a, (∀ y, Φ a y = 0) → (∀ y, Φ (lam * a) y = 0) := by
    intro a ha y
    have hy : y = sig * (sig⁻¹ * y) := by rw [← mul_assoc, mul_inv_cancel₀ hsig, one_mul]
    rw [hy, hΦeq, ha, mul_zero]
  have hpow : ∀ m : ℕ, ∀ y, Φ (lam ^ m * z) y = 0 := by
    intro m
    induction m with
    | zero => simpa using hz
    | succ m ih =>
        have := hstep (lam ^ m * z) ih
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using this
  have hxall : ∀ x y : F, Φ x y = 0 := by
    intro x y
    rcases eq_or_ne x 0 with hx0 | hx0
    · subst hx0; exact hzero y
    · obtain ⟨m, hm⟩ := lam_pow_exists hn hcard hlam (x / z) (div_ne_zero hx0 hz0)
      have hxz : x = lam ^ m * z := by
        rw [hm]; exact (div_mul_cancel₀ x hz0).symm
      rw [hxz]; exact hpow m y
  obtain ⟨a, b, hab⟩ := hΦne
  exact hab (hxall a b)

/-- For a symmetric biadditive `B`, the Frobenius expansion coefficients are symmetric. -/
private lemma frob_coeff_symm {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    {B : F → F → F} {d : ℕ → ℕ → F}
    (hexp : ∀ x y, B x y = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
      d k l * x ^ (2 ^ k) * y ^ (2 ^ l))
    (hsym : ∀ x y, B x y = B y x) :
    ∀ k ∈ Finset.range n, ∀ l ∈ Finset.range n, d k l = d l k := by
  have hc := Work.Higman.bivariate_monomial_indep hcard (fun k l => d k l - d l k) (by
    intro x y
    have h1 := hexp x y
    have h2 := hexp y x
    have hs := hsym x y
    rw [h1, h2] at hs
    have hN : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, d k l * y ^ (2 ^ k) * x ^ (2 ^ l))
        = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, d l k * x ^ (2 ^ k) * y ^ (2 ^ l) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      ring
    have hgoal : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, d k l * x ^ (2 ^ k) * y ^ (2 ^ l))
        = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, d l k * x ^ (2 ^ k) * y ^ (2 ^ l) :=
      hs.trans hN
    have hsplit : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          (d k l - d l k) * x ^ (2 ^ k) * y ^ (2 ^ l))
        = (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, d k l * x ^ (2 ^ k) * y ^ (2 ^ l))
          - (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, d l k * x ^ (2 ^ k) * y ^ (2 ^ l)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    rw [hsplit, hgoal, sub_self])
  intro k hk l hl
  exact sub_eq_zero.mp (hc k hk l hl)

theorem two_cover_algebraic_core
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    {lam : F} (hlam : orderOf lam = 2 ^ n - 1)
    {sig mu : F} (hsig : sig ≠ 1) (hmu : mu ≠ 1)
    (hsigord : ∀ k : ℕ, 1 ≤ k → k < n → sig ^ (2 ^ k) ≠ sig)
    (hmuord : ∀ k : ℕ, 1 ≤ k → k < n → mu ^ (2 ^ k) ≠ mu)
    {β : F → F → F}
    (hβ1 : ∀ a b c : F, β (a + b) c = β a c + β b c)
    (hβ2 : ∀ a b c : F, β a (b + c) = β a b + β a c)
    (hβeq : ∀ a b : F, β (sig * a) (mu * b) = lam * β a b)
    (hβsym : ∀ a b : F, β a b = β b a)
    (hβne : ∃ a b : F, β a b ≠ 0)
    {Φ : F → F → F}
    (hΦ1 : ∀ a b c : F, Φ (a + b) c = Φ a c + Φ b c)
    (hΦ2 : ∀ a b c : F, Φ a (b + c) = Φ a b + Φ a c)
    (hΦeq : ∀ a b : F, Φ (lam * a) (sig * b) = lam * Φ a b)
    (hΦne : ∃ a b : F, Φ a b ≠ 0)
    (hjac : ∀ s t s' : F, Φ (β s t) s' = Φ (β s' t) s)
    (hdiag : ∀ s t : F, Φ (β s t) s = β s t) : False := by
  classical
  have hn1 : 1 ≤ n := by omega
  have htwo : 2 ≤ 2 ^ n := by
    calc (2:ℕ) = 2^1 := by norm_num
      _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn1
  have hNnz : 2 ^ n - 1 ≠ 0 := by omega
  -- ## basic nonvanishing
  have hlam0 : lam ≠ 0 := by
    intro h
    have h1 : lam ^ (2 ^ n - 1) = 1 := by rw [← hlam]; exact pow_orderOf_eq_one lam
    rw [h, zero_pow hNnz] at h1
    exact zero_ne_one h1
  have hβ0l : ∀ c, β 0 c = 0 := by
    intro c; have h := hβ1 0 0 c; rw [add_zero] at h
    rw [CharTwo.add_self_eq_zero] at h; exact h
  have hβ0r : ∀ a, β a 0 = 0 := by
    intro a; have h := hβ2 a 0 0; rw [add_zero] at h
    rw [CharTwo.add_self_eq_zero] at h; exact h
  have hΦ0l : ∀ c, Φ 0 c = 0 := by
    intro c; have h := hΦ1 0 0 c; rw [add_zero] at h
    rw [CharTwo.add_self_eq_zero] at h; exact h
  have hsig0 : sig ≠ 0 := by
    intro h
    obtain ⟨a,b,hab⟩ := hβne
    have hh := hβeq a b
    rw [h, zero_mul, hβ0l, zero_eq_mul] at hh
    rcases hh with h' | h'
    · exact hlam0 h'
    · exact hab h'
  have hmu0 : mu ≠ 0 := by
    intro h
    obtain ⟨a,b,hab⟩ := hβne
    have hh := hβeq a b
    rw [h, zero_mul, hβ0r, zero_eq_mul] at hh
    rcases hh with h' | h'
    · exact hlam0 h'
    · exact hab h'
  -- ## Frobenius expansion of β
  obtain ⟨d, hdexp⟩ := Work.Higman.bilinear_frob_general hcard β
      (fun y x x' => hβ1 x x' y) (fun x y y' => hβ2 x y y')
  have hdsym := frob_coeff_symm hcard hdexp hβsym
  have hresβ := Work.Higman.bilinear_frob_general_constraint hcard β d hdexp sig mu lam hβeq
  -- ## the key relation `Φ (β t t) s = β s t`
  have hF : ∀ s t : F, Φ (β t t) s = β s t := by
    have hE : ∀ s t : F, Φ (β s t) (s + t) = 0 := by
      intro s t
      have ht : Φ (β s t) t = β s t := by
        have h := hdiag t s
        rwa [hβsym t s] at h
      calc Φ (β s t) (s + t) = Φ (β s t) s + Φ (β s t) t := hΦ2 (β s t) s t
        _ = β s t + β s t := by rw [hdiag s t, ht]
        _ = 0 := CharTwo.add_self_eq_zero _
    intro s t
    have hbt : β (s + t) t = β s t + β t t := hβ1 s t t
    have h := hE (s + t) t
    rw [show (s + t) + t = s from by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]] at h
    rw [hbt, hΦ1, hdiag s t] at h
    have h1 : Φ (β t t) s = β s t := by
      have h2 : β s t = -(Φ (β t t) s) := add_eq_zero_iff_eq_neg.mp h
      rw [CharTwo.neg_eq] at h2
      exact h2.symm
    exact h1
  -- ## `(4)`: `β (μ t) (μ t) = λ * β t t`
  have h4 : ∀ t : F, β (mu * t) (mu * t) = lam * β t t := by
    intro t
    have hkey : ∀ a : F, Φ (lam⁻¹ * β (mu * t) (mu * t) - β t t) a = 0 := by
      intro a
      have e1 : Φ (β (mu * t) (mu * t)) (sig * a)
          = lam * Φ (lam⁻¹ * β (mu * t) (mu * t)) a := by
        have := hΦeq (lam⁻¹ * β (mu * t) (mu * t)) a
        rwa [← mul_assoc, mul_inv_cancel₀ hlam0, one_mul] at this
      have e2 : Φ (β (mu * t) (mu * t)) (sig * a) = lam * Φ (β t t) a := by
        rw [hF (sig * a) (mu * t), hβeq a t, ← hF a t]
      have heq : Φ (lam⁻¹ * β (mu * t) (mu * t)) a = Φ (β t t) a := by
        apply mul_left_cancel₀ hlam0
        rw [← e1, e2]
      rw [sub_eq_add_neg, CharTwo.neg_eq, hΦ1, heq, CharTwo.add_self_eq_zero]
    have hz := left_radical_eq_bot hn1 hcard hlam hsig0 hΦ1 hΦeq hΦne
        (lam⁻¹ * β (mu * t) (mu * t) - β t t) hkey
    rw [sub_eq_iff_eq_add, zero_add] at hz
    rw [← hz, ← mul_assoc, mul_inv_cancel₀ hlam0, one_mul]
  -- ## diagonal Frobenius form of `β`
  have hQdiag : ∀ t, β t t = ∑ k ∈ Finset.range n, d k k * t ^ (2 ^ (k+1)) := by
    intro t
    rw [hdexp t t]
    rw [Work.Higman.double_sum_diag (Finset.range n) (fun k l => d k l * t ^ (2^k) * t ^ (2^l))
      (by intro k hk l hl; rw [hdsym k hk l hl]; ring)]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [mul_assoc, ← pow_add, show 2 ^ k + 2 ^ k = 2 ^ (k+1) from by rw [pow_succ]; ring]
  -- ## a single diagonal index survives; extract it
  have hczero : ∀ k ∈ Finset.range n, d k k * (mu ^ (2 ^ (k+1)) - lam) = 0 := by
    apply Work.Higman.frob_diag_zero hcard (fun k => d k k * (mu ^ (2^(k+1)) - lam))
    intro t
    have h := h4 t
    rw [hQdiag (mu*t), hQdiag t, Finset.mul_sum] at h
    simp only [mul_pow] at h
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    ring
  have hqne : ∃ k, k ∈ Finset.range n ∧ d k k ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ k, k ∈ Finset.range n → d k k = 0 := by
      intro k hk; by_contra hk'; exact hcon ⟨k, hk, hk'⟩
    have hQ0 : ∀ t, β t t = 0 := by
      intro t; rw [hQdiag t]; apply Finset.sum_eq_zero
      intro k hk; rw [hcon' k hk, zero_mul]
    obtain ⟨a,b,hab⟩ := hβne
    have h1 : β a b = 0 := by rw [← hF a b, hQ0 b, hΦ0l a]
    exact hab h1
  obtain ⟨k0, hk0mem, hdk0⟩ := hqne
  have hk0n : k0 < n := Finset.mem_range.mp hk0mem
  have hmuM : mu ^ (2^(k0+1)) = lam := by
    have := hczero k0 hk0mem
    rcases mul_eq_zero.mp this with h|h
    · exact absurd h hdk0
    · rwa [sub_eq_zero] at h
  have hsigmu : sig ^ (2^k0) * mu ^ (2^k0) = lam := by
    have := hresβ k0 hk0mem k0 hk0mem
    rcases mul_eq_zero.mp this with h|h
    · exact absurd h hdk0
    · rwa [sub_eq_zero] at h
  have hsig_eq : sig ^ (2^k0) = mu ^ (2^k0) := by
    have h2 : mu ^ (2^k0) * mu ^ (2^k0) = lam := by
      rw [← pow_add, show 2^k0 + 2^k0 = 2^(k0+1) from by rw [pow_succ]; ring, hmuM]
    have h3 : sig ^ (2^k0) * mu ^ (2^k0) = mu ^ (2^k0) * mu ^ (2^k0) := by rw [hsigmu, h2]
    exact mul_right_cancel₀ (pow_ne_zero _ hmu0) h3
  have hsigmueq : sig = mu := by
    have h2 : (sig ^ (2^k0)) ^ (2^(n-k0)) = (mu ^ (2^k0)) ^ (2^(n-k0)) := by rw [hsig_eq]
    rw [← pow_mul, ← pow_mul, show 2^k0 * 2^(n-k0) = 2^n from by rw [← pow_add]; congr 1; omega] at h2
    rwa [Work.Higman.pow_two_pow_card hcard sig, Work.Higman.pow_two_pow_card hcard mu] at h2
  -- ## order of μ (= σ) is `2 ^ n - 1`
  have hmu_order : orderOf mu = 2 ^ n - 1 := by
    apply Nat.dvd_antisymm
    · rw [orderOf_dvd_iff_pow_eq_one]
      have h1 : mu ^ (2 ^ n - 1) * mu = mu := by
        rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
        exact Work.Higman.pow_two_pow_card hcard mu
      exact mul_right_cancel₀ hmu0 (by rw [one_mul]; exact h1)
    · have h1 : orderOf (mu ^ (2^(k0+1))) = 2 ^ n - 1 := by rw [hmuM]; exact hlam
      calc 2 ^ n - 1 = orderOf (mu ^ (2^(k0+1))) := h1.symm
        _ ∣ orderOf mu := orderOf_pow_dvd (x := mu) (2^(k0+1))
  -- ## reduction of `2 ^ (k0+1)` modulo `2 ^ n - 1`
  have hM0lt : (k0+1) % n < n := Nat.mod_lt _ (by omega)
  have hred : 2 ^ (k0+1) ≡ 2 ^ ((k0+1) % n) [MOD 2 ^ n - 1] := by
    have h2n : 2 ^ n ≡ 1 [MOD 2 ^ n - 1] := by
      have h : (2 ^ n - 1) + 1 = 2 ^ n := Nat.sub_add_cancel Nat.one_le_two_pow
      rw [← h]
      simpa using (Nat.modEq_zero_iff_dvd.mpr (dvd_refl (2 ^ n - 1))).add (Nat.ModEq.refl 1)
    have hkey := (Nat.ModEq.refl (2 ^ ((k0+1) % n))).mul (h2n.pow ((k0+1)/n))
    rwa [one_pow, mul_one, ← pow_mul, ← pow_add, Nat.mod_add_div] at hkey
  have hlamM0 : mu ^ (2 ^ ((k0+1) % n)) = lam := by
    rw [← hmuM]
    exact (pow_eq_pow_of_modEq hmu0 (by rw [hmu_order]; exact hred)).symm
  -- ## resonance: for a non-zero coefficient, `i = j` and `i + 1 ≡ (k0+1) % n (mod n)`
  have hkey : ∀ i j : ℕ, i < n → j < n → d i j ≠ 0 →
      i = j ∧ (i + 1 = (k0+1) % n ∨ (i + 1 = n ∧ (k0+1) % n = 0)) := by
    intro i j hi hj hdij
    have hres := hresβ i (Finset.mem_range.mpr hi) j (Finset.mem_range.mpr hj)
    have hval : sig ^ (2^i) * mu ^ (2^j) = lam := by
      rcases mul_eq_zero.mp hres with h|h
      · exact absurd h hdij
      · rwa [sub_eq_zero] at h
    rw [hsigmueq] at hval
    have hh : mu ^ (2^i + 2^j) = mu ^ (2 ^ ((k0+1) % n)) := by
      rw [pow_add, hval, hlamM0]
    have hcong : 2^i + 2^j ≡ 2 ^ ((k0+1) % n) [MOD 2 ^ n - 1] :=
      pow_eq_pow_modEq hmu0 hmu_order hh
    exact Work.Higman.Q3.two_pow_add_eq_pow hn1 hi hj hM0lt (int_dvd_of_modeq hcong)
  -- ## witness for the unique non-zero coefficient
  obtain ⟨i0, hi0mem, j0, hj0mem, hdi0j0⟩ : ∃ i ∈ Finset.range n, ∃ j ∈ Finset.range n,
      d i j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨a0,b0,ha0b0⟩ := hβne
    apply ha0b0
    rw [hdexp a0 b0]
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [hcon i hi j hj, zero_mul, zero_mul]
  have hi0n : i0 < n := Finset.mem_range.mp hi0mem
  have hj0n : j0 < n := Finset.mem_range.mp hj0mem
  have hsupp : ∀ i j : ℕ, i < n → j < n → d i j ≠ 0 → i = i0 ∧ j = i0 := by
    intro i j hi hj hdij
    have h1 := hkey i j hi hj hdij
    have h2 := hkey i0 j0 hi0n hj0n hdi0j0
    have hi1 : i + 1 ≡ (k0+1) % n [MOD n] := by
      rcases h1.2 with h|⟨h,hz⟩
      · rw [h]
      · rw [h, hz]; exact Nat.modEq_zero_iff_dvd.mpr (dvd_refl n)
    have hi01 : i0 + 1 ≡ (k0+1) % n [MOD n] := by
      rcases h2.2 with h|⟨h,hz⟩
      · rw [h]
      · rw [h, hz]; exact Nat.modEq_zero_iff_dvd.mpr (dvd_refl n)
    have hii : i = i0 :=
      Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' 1 (hi1.trans hi01.symm)) hi hi0n
    refine ⟨hii, ?_⟩
    rw [← h1.1, hii]
  -- ## β is a single Frobenius monomial
  have hβmono : ∀ s t : F, β s t = d i0 i0 * s ^ (2^i0) * t ^ (2^i0) := by
    intro s t
    rw [hdexp s t]
    rw [Finset.sum_eq_single i0]
    · rw [Finset.sum_eq_single i0]
      · intro l hl hlne
        have hl' : l < n := Finset.mem_range.mp hl
        have hz : d i0 l = 0 := by
          by_contra hc; exact hlne (hsupp i0 l hi0n hl' hc).2
        rw [hz, zero_mul, zero_mul]
      · intro hm; exact absurd (Finset.mem_range.mpr hi0n) hm
    · intro k hk hkne
      apply Finset.sum_eq_zero
      intro l hl
      have hk' : k < n := Finset.mem_range.mp hk
      have hl' : l < n := Finset.mem_range.mp hl
      have hz : d k l = 0 := by
        by_contra hc; exact hkne (hsupp k l hk' hl' hc).1
      rw [hz, zero_mul, zero_mul]
    · intro hm; exact absurd (Finset.mem_range.mpr hi0n) hm
  -- ## hence `Φ x s = x` for every `s ≠ 0`
  have hPhi_id : ∀ x s : F, s ≠ 0 → Φ x s = x := by
    intro x s hs
    have hj0i0 : j0 = i0 := (hsupp i0 j0 hi0n hj0n hdi0j0).2
    have hd0 : d i0 i0 ≠ 0 := by have := hdi0j0; rwa [hj0i0] at this
    have hvs : d i0 i0 * s ^ (2^i0) ≠ 0 := mul_ne_zero hd0 (pow_ne_zero _ hs)
    set w := x * (d i0 i0 * s ^ (2^i0))⁻¹ with hw
    have hβw : β s (w ^ (2^(n-i0))) = x := by
      rw [hβmono s (w ^ (2^(n-i0)))]
      have h1 : (w ^ (2^(n-i0))) ^ (2^i0) = w := by
        rw [← pow_mul, show 2^(n-i0) * 2^i0 = 2^n from by rw [← pow_add]; congr 1; omega]
        exact Work.Higman.pow_two_pow_card hcard w
      rw [h1, hw]
      field_simp
    rw [← hβw, hdiag]
  -- ## final contradiction
  have hlam1 : lam ≠ 1 := by
    intro h
    have h1 : (2:ℕ)^n - 1 = 1 := by rw [← hlam, h, orderOf_one]
    have hlt : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hpow2 : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have h1lam : (1:F) + lam ≠ 0 := by
    intro h
    have h2 : (-1:F) = lam := (neg_eq_iff_add_eq_zero (a:=1) (b:=lam)).mpr h
    rw [CharTwo.neg_eq] at h2
    exact hlam1 h2.symm
  have e1 : Φ 1 1 = 1 := hPhi_id 1 1 one_ne_zero
  have e2 : Φ 1 lam = 1 := hPhi_id 1 lam hlam0
  have e3 : Φ 1 (1 + lam) = 1 := hPhi_id 1 (1 + lam) h1lam
  have e4 : Φ 1 (1 + lam) = 1 + 1 := by rw [hΦ2, e1, e2]
  rw [e3] at e4
  rw [CharTwo.add_self_eq_zero] at e4
  exact one_ne_zero e4

end Work.Higman.RedAux
