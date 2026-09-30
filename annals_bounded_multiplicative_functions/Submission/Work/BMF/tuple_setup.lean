import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N4 setup: admissible primes, tuples, their products, and the Fejér majorant kernel

Elementary definitions and lemmas for the node `Work.BMF.prime_tuple_count`
(MRT `Counting nearby products of primes`, Lemma 2.6 / MRTTZ Lemma 3.12).
No `sorry`.
-/

namespace Work.BMF

open Polynomial Finset Real
open scoped BigOperators

/-! ## The admissible primes, the tuples, and their products -/

lemma mem_primesIn_iff {a b : ℝ} {p : ℕ} (hb : 0 ≤ b) :
    p ∈ primesIn a b ↔ p.Prime ∧ a ≤ (p:ℝ) ∧ (p:ℝ) ≤ b := by
  unfold primesIn natIcc
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, le_trans (Nat.le_ceil a) (by exact_mod_cast h1),
      le_trans (by exact_mod_cast h2) (Nat.floor_le hb)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨Nat.ceil_le.mpr (by exact_mod_cast h2), Nat.le_floor (by exact_mod_cast h3)⟩, h1⟩

/-- The primes in `[P, 2P]` that do not divide `q`. -/
noncomputable def admP (P : ℝ) (q : ℕ) : Finset ℕ := (primesIn P (2 * P)).filter (fun p ↦ ¬ p ∣ q)

/-- The `ℓ`-tuples of admissible primes. -/
noncomputable def tup (P : ℝ) (q ℓ : ℕ) : Finset (Fin ℓ → ℕ) :=
  Fintype.piFinset (fun _ : Fin ℓ ↦ admP P q)

/-- The product of an `ℓ`-tuple. -/
def tprod {ℓ : ℕ} (v : Fin ℓ → ℕ) : ℕ := ∏ i, v i

lemma mem_admP {P : ℝ} {q p : ℕ} (hP : 0 ≤ P) :
    p ∈ admP P q ↔ p.Prime ∧ P ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*P ∧ ¬ p ∣ q := by
  unfold admP
  rw [Finset.mem_filter, mem_primesIn_iff (by linarith)]
  tauto

lemma admP_prime {P : ℝ} {q p : ℕ} (hP : 0 ≤ P) (hp : p ∈ admP P q) : p.Prime :=
  ((mem_admP hP).mp hp).1

lemma admP_ge {P : ℝ} {q p : ℕ} (hP : 0 ≤ P) (hp : p ∈ admP P q) : P ≤ (p:ℝ) :=
  ((mem_admP hP).mp hp).2.1

lemma admP_le {P : ℝ} {q p : ℕ} (hP : 0 ≤ P) (hp : p ∈ admP P q) : (p:ℝ) ≤ 2*P :=
  ((mem_admP hP).mp hp).2.2.1

lemma admP_notdvd {P : ℝ} {q p : ℕ} (hP : 0 ≤ P) (hp : p ∈ admP P q) : ¬ p ∣ q :=
  ((mem_admP hP).mp hp).2.2.2

lemma mem_tup {P : ℝ} {q ℓ : ℕ} {v : Fin ℓ → ℕ} :
    v ∈ tup P q ℓ ↔ ∀ i, v i ∈ admP P q := by
  unfold tup
  rw [Fintype.mem_piFinset]

lemma tup_prime {P : ℝ} {q ℓ : ℕ} {v : Fin ℓ → ℕ} (hP : 0 ≤ P) (hv : v ∈ tup P q ℓ) (i : Fin ℓ) :
    (v i).Prime := admP_prime hP ((mem_tup.mp hv) i)

lemma tup_ge {P : ℝ} {q ℓ : ℕ} {v : Fin ℓ → ℕ} (hP : 0 ≤ P) (hv : v ∈ tup P q ℓ) (i : Fin ℓ) :
    P ≤ ((v i : ℕ) : ℝ) := admP_ge hP ((mem_tup.mp hv) i)

lemma tup_le {P : ℝ} {q ℓ : ℕ} {v : Fin ℓ → ℕ} (hP : 0 ≤ P) (hv : v ∈ tup P q ℓ) (i : Fin ℓ) :
    ((v i : ℕ) : ℝ) ≤ 2*P := admP_le hP ((mem_tup.mp hv) i)

lemma tup_pos {P : ℝ} {q ℓ : ℕ} {v : Fin ℓ → ℕ} (hP : 0 ≤ P) (hv : v ∈ tup P q ℓ) (i : Fin ℓ) :
    0 < v i := (tup_prime hP hv i).pos

/-- The number of tuples is at most `(#(primesIn P (2P)))^ℓ`. -/
lemma card_tup_le {P : ℝ} {q ℓ : ℕ} :
    (tup P q ℓ).card ≤ ((primesIn P (2 * P)).card)^ℓ := by
  have hsub : tup P q ℓ ⊆ Fintype.piFinset (fun _ : Fin ℓ => primesIn P (2 * P)) := by
    intro v hv
    exact Fintype.mem_piFinset.mpr (fun i => (Finset.mem_filter.mp ((mem_tup.mp hv) i)).1)
  calc (tup P q ℓ).card ≤ (Fintype.piFinset (fun _ : Fin ℓ => primesIn P (2*P))).card :=
        Finset.card_le_card hsub
    _ = ((primesIn P (2*P)).card)^ℓ := by rw [Fintype.card_piFinset]; simp

/-- `tprod v ≤ (2P)^ℓ`. -/
lemma tprod_le {P : ℝ} {q ℓ : ℕ} {v : Fin ℓ → ℕ} (hP : 0 ≤ P) (hv : v ∈ tup P q ℓ) :
    (tprod v : ℝ) ≤ (2*P)^ℓ := by
  have hle : ∀ i, v i ≤ ⌊2*P⌋₊ := fun i => Nat.le_floor (by exact_mod_cast tup_le hP hv i)
  have h : tprod v ≤ (⌊2*P⌋₊)^ℓ := by
    have hp : tprod v ≤ ∏ _i : Fin ℓ, ⌊2*P⌋₊ := by
      rw [tprod]
      exact Finset.prod_le_prod (fun i _ => hle i)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
    exact hp
  calc (tprod v : ℝ) ≤ ((⌊2*P⌋₊ : ℕ) : ℝ)^ℓ := by exact_mod_cast h
    _ ≤ (2*P)^ℓ := by
        apply pow_le_pow_left₀ (by positivity)
        exact Nat.floor_le (by linarith)

/-- Every factor of `tprod v` is at least `P`. -/
lemma tprod_ge {P : ℝ} {q ℓ : ℕ} {v : Fin ℓ → ℕ} (hP : 0 ≤ P) (hv : v ∈ tup P q ℓ) :
    P^ℓ ≤ (tprod v : ℝ) := by
  have hconst : ∀ i ∈ (Finset.univ : Finset (Fin ℓ)), P ≤ ((v i : ℕ) : ℝ) :=
    fun i _ => tup_ge hP hv i
  have h1 : (∏ _i : Fin ℓ, P) ≤ ∏ i : Fin ℓ, ((v i : ℕ) : ℝ) :=
    Finset.prod_le_prod₀ (fun i _ => hP) hconst
  have h2 : (∏ _i : Fin ℓ, P) = P^ℓ := by simp [Finset.prod_const, Fintype.card_fin]
  rw [h2] at h1
  calc P^ℓ ≤ ∏ i : Fin ℓ, ((v i : ℕ) : ℝ) := h1
    _ = (tprod v : ℝ) := by rw [tprod]; push_cast; ring

/-- Euclid's lemma: a prime dividing a product of admissible primes is one of them. -/
lemma prime_dvd_tprod {P : ℝ} {q ℓ : ℕ} {v : Fin ℓ → ℕ} (hP : 0 ≤ P)
    (hv : ∀ i, v i ∈ admP P q) {p : ℕ} (hp : p.Prime) (hpd : p ∣ tprod v) :
    ∃ i, p = v i := by
  rw [tprod] at hpd
  obtain ⟨i, _, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun i => v i)).mp hpd
  exact ⟨i, (Nat.prime_dvd_prime_iff_eq hp (admP_prime hP (hv i))).mp hi⟩

/-- Any prime divisor of `tprod v` is at least `P`. -/
lemma prime_dvd_tprod_ge {P : ℝ} {q ℓ : ℕ} {v : Fin ℓ → ℕ} (hP : 0 ≤ P)
    (hv : ∀ i, v i ∈ admP P q) {p : ℕ} (hp : p.Prime) (hpd : p ∣ tprod v) :
    P ≤ (p : ℝ) := by
  obtain ⟨i, rfl⟩ := prime_dvd_tprod hP hv hp hpd
  exact admP_ge hP (hv i)

/-- The number of distinct prime divisors of `tprod v` is at most `ℓ + 1`. -/
lemma card_primeFactors_tprod_le {P : ℝ} {q ℓ : ℕ} {v : Fin ℓ → ℕ} (hℓ : 1 ≤ ℓ) (hP : 1 ≤ P)
    (h2l : (2:ℝ)^ℓ ≤ P) (hv : ∀ i, v i ∈ admP P q) :
    (tprod v).primeFactors.card ≤ ℓ + 1 := by
  have hP0 : (0:ℝ) < P := by linarith
  have hP2 : 2 ≤ P := by
    have : (2:ℝ) ≤ (2:ℝ)^ℓ := by
      calc (2:ℝ) = 2^1 := by ring
        _ ≤ 2^ℓ := by apply pow_le_pow_right₀ (by norm_num) hℓ
    linarith
  have hpos : 0 < tprod v := by
    rw [tprod]
    exact Finset.prod_pos (fun i _ => tup_pos (le_of_lt hP0) (mem_tup.mpr hv) i)
  have hge : ∀ p ∈ (tprod v).primeFactors, ⌈P⌉₊ ≤ p := fun p hp =>
    Nat.ceil_le.mpr (by exact_mod_cast (prime_dvd_tprod_ge (le_of_lt hP0) hv
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)))
  have h1 : (⌈P⌉₊)^((tprod v).primeFactors.card) ≤ tprod v := by
    calc (⌈P⌉₊)^((tprod v).primeFactors.card)
        ≤ ∏ p ∈ (tprod v).primeFactors, p := Finset.pow_card_le_prod _ _ _ hge
      _ ≤ tprod v := Nat.le_of_dvd hpos (Nat.prod_primeFactors_dvd _)
  have h2 : (tprod v : ℝ) ≤ ((⌈P⌉₊ : ℕ) : ℝ)^(ℓ+1) := by
    have h3 : (tprod v : ℝ) ≤ (2*P)^ℓ := tprod_le (le_of_lt hP0) (mem_tup.mpr hv)
    have h4 : (2*P)^ℓ ≤ (2:ℝ)^ℓ * P^ℓ := by rw [mul_pow]
    have h5 : (2:ℝ)^ℓ * P^ℓ ≤ P * P^ℓ := by
      nlinarith [h2l, show (0:ℝ) ≤ P^ℓ by positivity]
    have h6 : P * P^ℓ ≤ ((⌈P⌉₊ : ℕ) : ℝ)^(ℓ+1) := by
      have h7 : P ≤ ((⌈P⌉₊ : ℕ) : ℝ) := Nat.le_ceil P
      have h8 : (0:ℝ) ≤ P := le_of_lt hP0
      calc P * P^ℓ = P^(ℓ+1) := by ring
        _ ≤ ((⌈P⌉₊ : ℕ) : ℝ)^(ℓ+1) := pow_le_pow_left₀ h8 h7 _
    linarith
  have h9 : (⌈P⌉₊)^((tprod v).primeFactors.card) ≤ (⌈P⌉₊)^(ℓ+1) :=
    le_trans h1 (by exact_mod_cast h2)
  have h10 : 1 < ⌈P⌉₊ := by
    have h11 : (2:ℝ) ≤ (⌈P⌉₊ : ℝ) := le_trans hP2 (Nat.le_ceil P)
    exact_mod_cast (show (1:ℝ) < (⌈P⌉₊ : ℝ) by linarith)
  exact (Nat.pow_le_pow_iff_right h10).mp h9

/-- The number of `ℓ`-tuples of admissible primes with the same product as `v` is at most
`(ℓ+1)^ℓ`. -/
lemma fiber_card_le {P : ℝ} {q ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hP : 1 ≤ P) (h2l : (2:ℝ)^ℓ ≤ P)
    (v : Fin ℓ → ℕ) (hv : v ∈ tup P q ℓ) :
    ((tup P q ℓ).filter (fun w => tprod w = tprod v)).card ≤ (ℓ+1)^ℓ := by
  have hP0 : (0:ℝ) < P := by linarith
  have hsub : (tup P q ℓ).filter (fun w => tprod w = tprod v) ⊆
      Fintype.piFinset (fun _ : Fin ℓ => (tprod v).primeFactors) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    have hw' : ∀ i, w i ∈ admP P q := mem_tup.mp hw.1
    refine Fintype.mem_piFinset.mpr (fun i => ?_)
    have hdvd : w i ∣ tprod w := by
      rw [tprod]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    rw [hw.2] at hdvd
    have hpos : 0 < tprod v :=
      Finset.prod_pos (fun i _ => (admP_prime (le_of_lt hP0) (mem_tup.mp hv i)).pos)
    exact Nat.mem_primeFactors.mpr ⟨admP_prime (le_of_lt hP0) (hw' i), hdvd, hpos.ne'⟩
  have hcard : ((Fintype.piFinset (fun _ : Fin ℓ => (tprod v).primeFactors)).card) =
      (tprod v).primeFactors.card ^ ℓ := by
    rw [Fintype.card_piFinset]
    simp [Fintype.card_fin]
  calc ((tup P q ℓ).filter (fun w => tprod w = tprod v)).card
      ≤ (Fintype.piFinset (fun _ : Fin ℓ => (tprod v).primeFactors)).card :=
        Finset.card_le_card hsub
    _ = (tprod v).primeFactors.card ^ ℓ := hcard
    _ ≤ (ℓ+1)^ℓ := Nat.pow_le_pow_left
        (card_primeFactors_tprod_le hℓ hP h2l (mem_tup.mp hv)) ℓ

/-- Fibre bound with the product named: if `w ∈ tup` has product `n` then at most `(ℓ+1)^ℓ`
tuples of `tup` have product `n`. -/
lemma fiber_card_le_of_mem {P : ℝ} {q ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hP : 1 ≤ P) (h2l : (2:ℝ)^ℓ ≤ P)
    {w : Fin ℓ → ℕ} (hw : w ∈ tup P q ℓ) :
    ((tup P q ℓ).filter (fun w' => tprod w' = tprod w)).card ≤ (ℓ+1)^ℓ :=
  fiber_card_le hℓ hP h2l w hw

/-- **Case `q > (2P)^{ℓm}`** (the `m`-th power congruence forces equal products): the number
of filtered pairs is at most `#tup * (ℓ+1)^ℓ`. -/
lemma case_diagonal {ℓ m : ℕ} (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m) {P N C₀ : ℝ} {q : ℕ}
    (hP : 1 ≤ P) (h2l : (2:ℝ)^ℓ ≤ P) (hq : (2*P)^(ℓ*m) < (q:ℝ)) :
    (((tup P q ℓ) ×ˢ (tup P q ℓ)).filter (fun v ↦
        |((tprod v.2 : ℕ) : ℝ) - ((tprod v.1 : ℕ) : ℝ)| ≤ C₀ * P^ℓ / N ∧
        (tprod v.2)^m ≡ (tprod v.1)^m [MOD q])).card ≤
      (tup P q ℓ).card * (ℓ+1)^ℓ := by
  classical
  have hP0 : (0:ℝ) < P := by linarith
  have hpow : ∀ v : Fin ℓ → ℕ, v ∈ tup P q ℓ → (tprod v)^m < q := by
    intro v hv
    have hb : ((tprod v : ℕ) : ℝ) ≤ (2*P)^ℓ := tprod_le (le_of_lt hP0) hv
    have hb2 : (((tprod v)^m : ℕ) : ℝ) ≤ (2*P)^(ℓ*m) := by
      have h1 : ((tprod v : ℕ) : ℝ)^m ≤ ((2*P)^ℓ)^m :=
        pow_le_pow_left₀ (by positivity) hb m
      calc (((tprod v)^m : ℕ) : ℝ) = ((tprod v : ℕ) : ℝ)^m := by push_cast; ring
        _ ≤ ((2*P)^ℓ)^m := h1
        _ = (2*P)^(ℓ*m) := by rw [← pow_mul]
    have := lt_of_le_of_lt hb2 hq
    exact_mod_cast this
  have hkey : ∀ v ∈ ((tup P q ℓ) ×ˢ (tup P q ℓ)).filter (fun v ↦
      |((tprod v.2 : ℕ) : ℝ) - ((tprod v.1 : ℕ) : ℝ)| ≤ C₀ * P^ℓ / N ∧
      (tprod v.2)^m ≡ (tprod v.1)^m [MOD q]), tprod v.2 = tprod v.1 := by
    intro v hv
    rw [Finset.mem_filter, Finset.mem_product] at hv
    obtain ⟨⟨hv1, hv2⟩, -, hcong⟩ := hv
    have h1 := hpow v.1 hv1
    have h2 := hpow v.2 hv2
    have heq : (tprod v.2)^m = (tprod v.1)^m := by
      rw [Nat.ModEq] at hcong
      rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h1] at hcong
      exact hcong
    exact Nat.pow_left_injective (by omega : m ≠ 0) heq
  have hsub : (((tup P q ℓ) ×ˢ (tup P q ℓ)).filter
      (fun v ↦ tprod v.2 = tprod v.1)) ⊆
      (tup P q ℓ).biUnion (fun v₁ ↦
        (((tup P q ℓ).filter (fun v₂ ↦ tprod v₂ = tprod v₁)).image (fun v₂ ↦ (v₁, v₂)))) := by
    intro v hv
    rw [Finset.mem_filter, Finset.mem_product] at hv
    obtain ⟨⟨hv1, hv2⟩, heq⟩ := hv
    exact Finset.mem_biUnion.mpr ⟨v.1, hv1, Finset.mem_image.mpr
      ⟨v.2, by rw [Finset.mem_filter]; exact ⟨hv2, heq⟩, rfl⟩⟩
  calc (((tup P q ℓ) ×ˢ (tup P q ℓ)).filter (fun v ↦
        |((tprod v.2 : ℕ) : ℝ) - ((tprod v.1 : ℕ) : ℝ)| ≤ C₀ * P^ℓ / N ∧
        (tprod v.2)^m ≡ (tprod v.1)^m [MOD q])).card
      ≤ (((tup P q ℓ) ×ˢ (tup P q ℓ)).filter (fun v ↦ tprod v.2 = tprod v.1)).card := by
        apply Finset.card_le_card
        intro v hv
        rw [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, hkey v (Finset.mem_filter.mpr ⟨hv.1, hv.2⟩)⟩
    _ ≤ ((tup P q ℓ).biUnion (fun v₁ ↦
        (((tup P q ℓ).filter (fun v₂ ↦ tprod v₂ = tprod v₁)).image (fun v₂ ↦ (v₁, v₂))))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v₁ ∈ tup P q ℓ,
        ((((tup P q ℓ).filter (fun v₂ ↦ tprod v₂ = tprod v₁)).image (fun v₂ ↦ (v₁, v₂)))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _v₁ ∈ tup P q ℓ, (ℓ+1)^ℓ := by
        refine Finset.sum_le_sum (fun v₁ hv₁ => ?_)
        calc ((((tup P q ℓ).filter (fun v₂ ↦ tprod v₂ = tprod v₁)).image (fun v₂ ↦ (v₁, v₂)))).card
            ≤ ((tup P q ℓ).filter (fun v₂ ↦ tprod v₂ = tprod v₁)).card := Finset.card_image_le
          _ ≤ (ℓ+1)^ℓ := fiber_card_le hℓ hP h2l v₁ hv₁
    _ = (tup P q ℓ).card * (ℓ+1)^ℓ := by rw [Finset.sum_const, smul_eq_mul]

/-! ## The Fejér majorant kernel

For `C₀ > 0` put
`n4w C₀ u = 3 * (sin (π u / (4 C₀)) / (π u / (4 C₀)))²` (with the value `3` at `u = 0`), a
rescaled Fejér kernel: nonnegative, at least `1` on `[-2C₀, 2C₀]`, of total mass `3`, with
Fourier transform `n4W C₀ ξ = 12 C₀ (1 − 4 C₀ |ξ|)₊`. -/

/-- Rescaled Fejér kernel. -/
noncomputable def n4w (C₀ u : ℝ) : ℝ :=
  if u = 0 then 3 else 3 * (Real.sin (Real.pi * u / (4 * C₀)) / (Real.pi * u / (4 * C₀)))^2

/-- The (triangular) Fourier transform of `n4w C₀`, as a real function. -/
noncomputable def n4Wr (C₀ ξ : ℝ) : ℝ := 12 * C₀ * max (1 - 4 * C₀ * |ξ|) 0

/-- The (triangular) Fourier transform of `n4w C₀`. -/
noncomputable def n4W (C₀ ξ : ℝ) : ℂ := ((12 * C₀ * max (1 - 4 * C₀ * |ξ|) 0 : ℝ) : ℂ)

@[simp] lemma n4W_apply (C₀ ξ : ℝ) : n4W C₀ ξ = ((n4Wr C₀ ξ : ℝ) : ℂ) := rfl

end Work.BMF
