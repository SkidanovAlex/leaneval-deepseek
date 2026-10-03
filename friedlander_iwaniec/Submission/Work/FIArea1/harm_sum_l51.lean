import Mathlib

namespace Work.FIArea1

open Finset
open scoped BigOperators

/-! ### Auxiliary facts for `harm_sum_l51`

The target is the coprime-harmonic off-diagonal estimate of *FI* Lemma 5.1:
`Σ_{S₁,S₂ ∈ [-K,K]∖{0}} 1/(S₁/(S₁,S₂)) ≪ K (log K)²`.
The proof reduces the ℤ-double-sum to a ℕ-double-sum (the term only depends on
`|S₁|, |S₂|`, each of `(n,m)` occurring four times), then bounds
`Σ_{n,m ≤ K} (n,m)/n ≤ K Σ_{n ≤ K} τ(n)/n` via the identity `(n,m) = Σ_{d|n, d|m} φ(d)`,
and finally uses `Σ_{n ≤ K} τ(n)/n ≤ (1+log K)²`. -/

private lemma Ioc_zero_eq_Icc_one (n : ℕ) : Finset.Ioc 0 n = Finset.Icc 1 n := by
  ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega

private lemma harmonic_eq_sum_Ioc (n : ℕ) :
    (∑ j ∈ Finset.Ioc 0 n, ((j:ℝ))⁻¹) = (harmonic n : ℝ) := by
  rw [Ioc_zero_eq_Icc_one, harmonic_eq_sum_Icc, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_natCast]

private lemma image_mul_Ioc (K d : ℕ) (hd : 0 < d) :
    (Finset.Ioc 0 (K / d)).image (fun j => d * j) = (Finset.Ioc 0 K).filter (fun n => d ∣ n) := by
  ext n
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
    exact ⟨⟨Nat.mul_pos hd hj1, (Nat.mul_le_mul_left d hj2).trans (Nat.mul_div_le K d)⟩,
      dvd_mul_right d j⟩
  · rintro ⟨⟨hn1, hn2⟩, ⟨j, rfl⟩⟩
    refine ⟨j, ⟨?_, ?_⟩, rfl⟩
    · have : 0 < j := Nat.pos_of_mul_pos_left (by omega)
      omega
    · rw [Nat.le_div_iff_mul_le hd]
      simpa [mul_comm] using hn2

/-- `Σ_{n ≤ K, d ∣ n} 1/n = (1/d)·H_{⌊K/d⌋}` (for `0 < d`). -/
private lemma sum_filter_dvd_inv (K d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Ioc 0 K).filter (fun n => d ∣ n), ((n:ℝ))⁻¹)
      = (d:ℝ)⁻¹ * (harmonic (K / d) : ℝ) := by
  rw [← image_mul_Ioc K d hd, Finset.sum_image]
  · simp_rw [Nat.cast_mul, mul_inv_rev]
    rw [← Finset.sum_mul, harmonic_eq_sum_Ioc]
    ring
  · intro a ha b hb hab
    exact Nat.mul_left_cancel hd hab

/-- For `1 ≤ n ≤ K`, the divisors of `n` are exactly the `d ∈ (0,K]` dividing `n`. -/
private lemma divisors_eq_filter (K n : ℕ) (hn : n ∈ Finset.Ioc 0 K) :
    n.divisors = (Finset.Ioc 0 K).filter (fun d => d ∣ n) := by
  ext d
  rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
  rw [Finset.mem_Ioc] at hn
  constructor
  · rintro ⟨hdvd, hn0⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), (Nat.le_of_dvd (by omega) hdvd).trans hn.2⟩, hdvd⟩
  · rintro ⟨⟨hd1, hdK⟩, hdvd⟩
    exact ⟨hdvd, by omega⟩

/-- `Σ_{n ≤ K} τ(n)/n ≤ (1 + log K)²`. -/
private lemma sum_tau_div_le (K : ℕ) :
    (∑ n ∈ Finset.Ioc 0 K, (n.divisors.card : ℝ) / (n : ℝ))
      ≤ (1 + Real.log K) ^ 2 := by
  set D := Finset.Ioc 0 K with hD
  have hposK : (0:ℝ) ≤ 1 + Real.log (K:ℝ) := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp
    · have := Real.log_nonneg (x := (K:ℝ)) (by exact_mod_cast h); linarith
  have step1 : (∑ n ∈ D, (n.divisors.card : ℝ) / (n : ℝ))
      = ∑ n ∈ D, (∑ d ∈ D, (if d ∣ n then ((n:ℝ))⁻¹ else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [show n.divisors = D.filter (fun d => d ∣ n) by
          rw [hD]; exact divisors_eq_filter K n (hD ▸ hn),
        div_eq_mul_inv, ← Finset.sum_boole (fun d => d ∣ n) D, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : d ∣ n <;> simp [h]
  have step2 : (∑ n ∈ D, (∑ d ∈ D, (if d ∣ n then ((n:ℝ))⁻¹ else 0)))
      = ∑ d ∈ D, (d:ℝ)⁻¹ * (harmonic (K / d) : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 1 ≤ d := by rw [hD] at hd; exact (Finset.mem_Ioc.mp hd).1
    rw [← Finset.sum_filter]
    exact sum_filter_dvd_inv K d hd1
  have step3 : (∑ d ∈ D, (d:ℝ)⁻¹ * (harmonic (K / d) : ℝ)) ≤ (1 + Real.log K) ^ 2 := by
    have key : ∀ d ∈ D, (d:ℝ)⁻¹ * (harmonic (K / d) : ℝ) ≤ (d:ℝ)⁻¹ * (1 + Real.log K) := by
      intro d hd
      have hdI := hd; rw [hD, Finset.mem_Ioc] at hdI
      have hle : K / d ≤ K := Nat.div_le_self K d
      have hlog : Real.log ((K / d : ℕ) : ℝ) ≤ Real.log (K:ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast Nat.div_pos hdI.2 hdI.1
        · exact_mod_cast hle
      calc (d:ℝ)⁻¹ * (harmonic (K / d) : ℝ)
          ≤ (d:ℝ)⁻¹ * (1 + Real.log ((K/d:ℕ):ℝ)) := by
              apply mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (K/d)) (by positivity)
        _ ≤ (d:ℝ)⁻¹ * (1 + Real.log (K:ℝ)) := by
              apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc ∑ d ∈ D, (d:ℝ)⁻¹ * (harmonic (K/d):ℝ)
        ≤ ∑ d ∈ D, (d:ℝ)⁻¹ * (1 + Real.log K) := Finset.sum_le_sum key
      _ = (∑ d ∈ D, (d:ℝ)⁻¹) * (1 + Real.log K) := by rw [Finset.sum_mul]
      _ = (harmonic K : ℝ) * (1 + Real.log K) := by
            rw [show (∑ d ∈ D, (d:ℝ)⁻¹) = (harmonic K : ℝ) by
                  rw [hD]; exact harmonic_eq_sum_Ioc K]
      _ ≤ (1 + Real.log K) * (1 + Real.log K) := by
            apply mul_le_mul_of_nonneg_right (harmonic_le_one_add_log K) hposK
      _ = (1 + Real.log K)^2 := by ring
  rw [step1, step2]
  exact step3

/-- `Σ_{m ≤ K} (n,m) ≤ K·τ(n)`, via `(n,m) = Σ_{d ∣ n, d ∣ m} φ(d)`. -/
private lemma gcd_sum_le (K n : ℕ) (hn1 : 1 ≤ n) (hnK : n ≤ K) :
    (∑ m ∈ Finset.Ioc 0 K, (Nat.gcd n m : ℝ)) ≤ (K : ℝ) * (n.divisors.card : ℝ) := by
  set D := Finset.Ioc 0 K with hD
  have hnD : n ∈ D := by rw [hD]; exact Finset.mem_Ioc.mpr ⟨hn1, hnK⟩
  have hgcd : ∀ m : ℕ, (Nat.gcd n m : ℝ)
      = ∑ d ∈ D.filter (fun d => d ∣ n), (if d ∣ m then (Nat.totient d : ℝ) else 0) := by
    intro m
    have hdiv : (Nat.gcd n m).divisors
        = (D.filter (fun d => d ∣ n)).filter (fun d => d ∣ m) := by
      ext d
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_filter, hD, Finset.mem_Ioc]
      constructor
      · rintro ⟨hdvd, _⟩
        obtain ⟨hdn, hdm⟩ := Nat.dvd_gcd_iff.mp hdvd
        exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hdn (by omega),
          (Nat.le_of_dvd (by omega) hdn).trans hnK⟩, hdn⟩, hdm⟩
      · rintro ⟨⟨⟨hd1, hdK⟩, hdn⟩, hdm⟩
        exact ⟨Nat.dvd_gcd hdn hdm, Nat.gcd_ne_zero_left (by omega)⟩
    calc (Nat.gcd n m : ℝ) = (((Nat.gcd n m).divisors.sum Nat.totient : ℕ) : ℝ) := by
            rw [Nat.sum_totient]
      _ = ∑ d ∈ (Nat.gcd n m).divisors, (Nat.totient d : ℝ) := by push_cast; rfl
      _ = ∑ d ∈ (D.filter (fun d => d ∣ n)).filter (fun d => d ∣ m), (Nat.totient d : ℝ) := by
            rw [hdiv]
      _ = ∑ d ∈ D.filter (fun d => d ∣ n), (if d ∣ m then (Nat.totient d : ℝ) else 0) := by
            rw [Finset.sum_filter]
  have hinner : ∀ d : ℕ, (∑ m ∈ D, (if d ∣ m then (Nat.totient d : ℝ) else 0))
      = (Nat.totient d : ℝ) * ((D.filter (fun m => d ∣ m)).card : ℝ) := by
    intro d
    calc (∑ m ∈ D, (if d ∣ m then (Nat.totient d : ℝ) else 0))
        = ∑ m ∈ D, (Nat.totient d : ℝ) * (if d ∣ m then (1:ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro m _; by_cases h : d ∣ m <;> simp [h]
      _ = (Nat.totient d : ℝ) * ∑ m ∈ D, (if d ∣ m then (1:ℝ) else 0) := by rw [Finset.mul_sum]
      _ = (Nat.totient d : ℝ) * ((D.filter (fun m => d ∣ m)).card : ℝ) := by rw [Finset.sum_boole]
  calc (∑ m ∈ D, (Nat.gcd n m : ℝ))
      = ∑ m ∈ D, ∑ d ∈ D.filter (fun d => d ∣ n), (if d ∣ m then (Nat.totient d : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro m _; exact hgcd m
    _ = ∑ d ∈ D.filter (fun d => d ∣ n),
          ∑ m ∈ D, (if d ∣ m then (Nat.totient d : ℝ) else 0) :=
          Finset.sum_comm
    _ = ∑ d ∈ D.filter (fun d => d ∣ n),
          (Nat.totient d : ℝ) * ((D.filter (fun m => d ∣ m)).card : ℝ) := by
          apply Finset.sum_congr rfl; intro d _; exact hinner d
    _ ≤ ∑ d ∈ D.filter (fun d => d ∣ n), (K:ℝ) := by
          apply Finset.sum_le_sum; intro d hd
          rw [Finset.mem_filter] at hd
          have hd1 : 0 < d := by rw [hD, Finset.mem_Ioc] at hd; exact hd.1.1
          have hcard : ((D.filter (fun m => d ∣ m)).card : ℝ) = ((K/d : ℕ) : ℝ) := by
            rw [hD, Nat.Ioc_filter_dvd_card_eq_div]
          rw [hcard]
          have hb : Nat.totient d * (K/d) ≤ K :=
            (Nat.mul_le_mul_right _ (Nat.totient_le d)).trans (Nat.mul_div_le K d)
          rw [← Nat.cast_mul]
          exact_mod_cast hb
    _ = (K:ℝ) * ((D.filter (fun d => d ∣ n)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ = (K:ℝ) * (n.divisors.card : ℝ) := by rw [← divisors_eq_filter K n hnD]

/-- Splitting the symmetric box `[-K,K]∖{0}` into its positive and negative halves:
`Σ_{S ∈ B} G(|S|) = 2 Σ_{n=1}^{K} G(n)`. -/
private lemma sum_erase_Icc_natAbs (K : ℕ) (G : ℕ → ℝ) :
    (∑ S ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0, G S.natAbs)
      = 2 * ∑ n ∈ Finset.Ioc 0 K, G n := by
  have hB : (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0
      = (Finset.Ico (-(K : ℤ)) 0) ∪ (Finset.Ioc 0 (K : ℤ)) := by
    ext S
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico, Finset.mem_Ioc]
    constructor
    · rintro ⟨hS0, h1, h2⟩
      rcases lt_trichotomy S 0 with h | h | h
      · exact Or.inl ⟨h1, h⟩
      · exact absurd h hS0
      · exact Or.inr ⟨h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨by omega, h1, by omega⟩
      · exact ⟨by omega, by omega, h2⟩
  have hdisj : Disjoint (Finset.Ico (-(K : ℤ)) 0) (Finset.Ioc 0 (K : ℤ)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_Ico] at ha; rw [Finset.mem_Ioc] at hb
    omega
  rw [hB, Finset.sum_union hdisj]
  have hneg : (∑ S ∈ Finset.Ico (-(K : ℤ)) 0, G S.natAbs) = ∑ n ∈ Finset.Ioc 0 K, G n := by
    have himg : (Finset.Ioc 0 K).image (fun n : ℕ => (-(n:ℤ))) = Finset.Ico (-(K:ℤ)) 0 := by
      ext S
      simp only [Finset.mem_image, Finset.mem_Ioc, Finset.mem_Ico]
      constructor
      · rintro ⟨n, ⟨hn1, hn2⟩, rfl⟩
        constructor <;> omega
      · intro hS
        refine ⟨S.natAbs, ⟨?_, ?_⟩, ?_⟩
        · omega
        · omega
        · have hS' : (↑S.natAbs : ℤ) = -S := by
            have := Int.natAbs_of_nonneg (a := -S) (by omega)
            rwa [Int.natAbs_neg] at this
          omega
    rw [← himg, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [Int.natAbs_neg]
    · intro a ha b hb hab
      exact Int.ofNat.inj (Int.neg_inj.mp hab)
  have hpos : (∑ S ∈ Finset.Ioc 0 (K:ℤ), G S.natAbs) = ∑ n ∈ Finset.Ioc 0 K, G n := by
    have himg : (Finset.Ioc 0 K).image (fun n : ℕ => ((n:ℤ))) = Finset.Ioc 0 (K:ℤ) := by
      ext S
      simp only [Finset.mem_image, Finset.mem_Ioc]
      constructor
      · rintro ⟨n, ⟨hn1, hn2⟩, rfl⟩
        exact ⟨by exact_mod_cast hn1, by exact_mod_cast hn2⟩
      · rintro ⟨hS1, hS2⟩
        refine ⟨S.natAbs, ⟨?_, ?_⟩, ?_⟩
        · omega
        · omega
        · exact Int.natAbs_of_nonneg (by omega)
    rw [← himg, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      simp
    · intro a ha b hb hab
      exact Int.ofNat.inj hab
  rw [hneg, hpos]; ring

/-- `1/(S₁/(S₁,S₂)) = (S₁,S₂)/|S₁|` for `S₁ ≠ 0`. -/
private lemma abs_div_gcd_inv (a b : ℤ) (ha : a ≠ 0) :
    (((a.natAbs / Nat.gcd a.natAbs b.natAbs : ℕ) : ℝ))⁻¹
      = (Nat.gcd a.natAbs b.natAbs : ℝ) / (a.natAbs : ℝ) := by
  have hg : 0 < Nat.gcd a.natAbs b.natAbs := Nat.gcd_pos_of_pos_left b.natAbs (Int.natAbs_pos.mpr ha)
  have hgR : (Nat.gcd a.natAbs b.natAbs : ℝ) ≠ 0 := by positivity
  have hdvd : Nat.gcd a.natAbs b.natAbs ∣ a.natAbs := Nat.gcd_dvd_left _ _
  have hnat : a.natAbs = Nat.gcd a.natAbs b.natAbs * (a.natAbs / Nat.gcd a.natAbs b.natAbs) :=
    (Nat.mul_div_cancel' hdvd).symm
  have hdecomp : (a.natAbs : ℝ)
      = (Nat.gcd a.natAbs b.natAbs : ℝ) * ((a.natAbs / Nat.gcd a.natAbs b.natAbs : ℕ) : ℝ) := by
    conv_lhs => rw [hnat]
    push_cast; ring
  have hmem : (a.natAbs : ℝ) / (Nat.gcd a.natAbs b.natAbs : ℝ)
      = ((a.natAbs / Nat.gcd a.natAbs b.natAbs : ℕ) : ℝ) := by
    rw [div_eq_iff hgR, mul_comm]
    exact hdecomp
  rw [← hmem, inv_div]

/-- Reduction of the ℤ-double-sum to the ℕ-double-sum (each `(n,m)` has four preimages). -/
private lemma reduce_nat (K : ℕ) (Ψ : ℕ → ℕ → ℝ) :
    (∑ S₁ ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).erase 0,
      ∑ S₂ ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).erase 0, Ψ S₁.natAbs S₂.natAbs)
      = 4 * ∑ n ∈ Finset.Ioc 0 K, ∑ m ∈ Finset.Ioc 0 K, Ψ n m := by
  have h1 : ∀ S₁ : ℤ,
      (∑ S₂ ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).erase 0, Ψ S₁.natAbs S₂.natAbs)
      = 2 * ∑ m ∈ Finset.Ioc 0 K, Ψ S₁.natAbs m :=
    fun S₁ => sum_erase_Icc_natAbs K (fun m => Ψ S₁.natAbs m)
  calc (∑ S₁ ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).erase 0,
          ∑ S₂ ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).erase 0, Ψ S₁.natAbs S₂.natAbs)
      = ∑ S₁ ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).erase 0,
          2 * ∑ m ∈ Finset.Ioc 0 K, Ψ S₁.natAbs m := by
          apply Finset.sum_congr rfl; intro S₁ _; exact h1 S₁
    _ = 2 * (∑ S₁ ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).erase 0,
          ∑ m ∈ Finset.Ioc 0 K, Ψ S₁.natAbs m) := by
          rw [Finset.mul_sum]
    _ = 2 * (2 * ∑ n ∈ Finset.Ioc 0 K, ∑ m ∈ Finset.Ioc 0 K, Ψ n m) := by
          congr 1
          exact sum_erase_Icc_natAbs K (fun n => ∑ m ∈ Finset.Ioc 0 K, Ψ n m)
    _ = 4 * ∑ n ∈ Finset.Ioc 0 K, ∑ m ∈ Finset.Ioc 0 K, Ψ n m := by ring

/-- **Coprime harmonic sum for the off-diagonal of FI Lemma 5.1.** The sum of `1/(S₁/(S₁,S₂))` over
pairs `S₁, S₂ ∈ [-K,K] ∖ {0}` is at most `C·(K+1)·(log(K+2))²`.

*Route:* group by `δ = (S₁,S₂)` and write `Sᵢ = δ S*ᵢ` with `(S*₁,S*₂) = 1`; then
`1/|S*₁| = δ/|S₁|`, and `Σ_{δ≤K} Σ_{coprime, |S*ᵢ| ≤ K/δ} 1/|S*₁| ≤ Σ_δ (2K/δ)·(2 log(K/δ))`. -/
theorem harm_sum_l51 : ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ,
    (∑ S₁ ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0,
      ∑ S₂ ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0,
        (((S₁.natAbs / Nat.gcd S₁.natAbs S₂.natAbs : ℕ) : ℝ))⁻¹)
      ≤ C * ((K : ℝ) + 1) * (Real.log ((K : ℝ) + 2)) ^ 2 := by
  refine ⟨16, by norm_num, fun K => ?_⟩
  set B := (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0 with hB
  have stepA : (∑ S₁ ∈ B, ∑ S₂ ∈ B, (((S₁.natAbs / Nat.gcd S₁.natAbs S₂.natAbs : ℕ) : ℝ))⁻¹)
      = ∑ S₁ ∈ B, ∑ S₂ ∈ B, (Nat.gcd S₁.natAbs S₂.natAbs : ℝ) / (S₁.natAbs : ℝ) := by
    apply Finset.sum_congr rfl; intro S₁ hS₁
    apply Finset.sum_congr rfl; intro S₂ hS₂
    have hne : S₁ ≠ 0 := by rw [hB, Finset.mem_erase] at hS₁; exact hS₁.1
    exact abs_div_gcd_inv S₁ S₂ hne
  have hred : (∑ S₁ ∈ B, ∑ S₂ ∈ B, (Nat.gcd S₁.natAbs S₂.natAbs : ℝ) / (S₁.natAbs : ℝ))
      = 4 * ∑ n ∈ Finset.Ioc 0 K, ∑ m ∈ Finset.Ioc 0 K, (Nat.gcd n m : ℝ) / (n : ℝ) := by
    rw [hB]
    exact reduce_nat K (fun n m => (Nat.gcd n m : ℝ) / (n : ℝ))
  have hbound : (∑ n ∈ Finset.Ioc 0 K, ∑ m ∈ Finset.Ioc 0 K, (Nat.gcd n m : ℝ) / (n : ℝ))
      ≤ (K:ℝ) * (1 + Real.log K) ^ 2 := by
    calc (∑ n ∈ Finset.Ioc 0 K, ∑ m ∈ Finset.Ioc 0 K, (Nat.gcd n m : ℝ) / (n : ℝ))
        = ∑ n ∈ Finset.Ioc 0 K, (n:ℝ)⁻¹ * (∑ m ∈ Finset.Ioc 0 K, (Nat.gcd n m : ℝ)) := by
            apply Finset.sum_congr rfl; intro n hn
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro m hm
            rw [div_eq_mul_inv, mul_comm]
      _ ≤ ∑ n ∈ Finset.Ioc 0 K, (n:ℝ)⁻¹ * ((K:ℝ) * (n.divisors.card : ℝ)) := by
            apply Finset.sum_le_sum; intro n hn
            have hnI := hn; rw [Finset.mem_Ioc] at hnI
            apply mul_le_mul_of_nonneg_left (gcd_sum_le K n hnI.1 hnI.2)
            positivity
      _ = (K:ℝ) * ∑ n ∈ Finset.Ioc 0 K, (n.divisors.card : ℝ) / (n : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro n hn
            rw [div_eq_mul_inv]; ring
      _ ≤ (K:ℝ) * (1 + Real.log K) ^ 2 := by
            apply mul_le_mul_of_nonneg_left (sum_tau_div_le K)
            positivity
  have hfinal : 4 * ((K:ℝ) * (1 + Real.log (K:ℝ)) ^ 2)
      ≤ 16 * ((K : ℝ) + 1) * (Real.log ((K : ℝ) + 2)) ^ 2 := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp; positivity
    · have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
      have hlog3 : (1:ℝ) ≤ Real.log 3 := by
        have := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
        rw [Real.log_exp] at this; linarith
      have hmul : (3:ℝ) * (K:ℝ) ≤ ((K:ℝ)+2)^2 := by nlinarith [hKpos]
      have ha : 1 + Real.log (K:ℝ) ≤ 2 * Real.log ((K:ℝ)+2) := by
        have h1 : Real.log 3 + Real.log (K:ℝ) = Real.log ((3:ℝ) * (K:ℝ)) :=
          (Real.log_mul (by norm_num) (ne_of_gt hKpos)).symm
        have h2 : Real.log (((K:ℝ)+2)^2) = 2 * Real.log ((K:ℝ)+2) := by
          rw [Real.log_pow]; ring
        have h3 : Real.log ((3:ℝ)*(K:ℝ)) ≤ Real.log (((K:ℝ)+2)^2) :=
          Real.log_le_log (by positivity) hmul
        linarith
      have ha0 : 0 ≤ 1 + Real.log (K:ℝ) := by
        have := Real.log_nonneg (x := (K:ℝ)) (by exact_mod_cast hK); linarith
      have hsq : (1 + Real.log (K:ℝ))^2 ≤ 4 * (Real.log ((K:ℝ)+2))^2 := by
        have := pow_le_pow_left₀ ha0 ha 2
        calc (1 + Real.log (K:ℝ))^2 ≤ (2 * Real.log ((K:ℝ)+2))^2 := this
          _ = 4 * (Real.log ((K:ℝ)+2))^2 := by ring
      calc 4 * ((K:ℝ) * (1 + Real.log (K:ℝ))^2)
          = 4 * (K:ℝ) * (1 + Real.log (K:ℝ))^2 := by ring
        _ ≤ 4 * (K:ℝ) * (4 * (Real.log ((K:ℝ)+2))^2) := by
              apply mul_le_mul_of_nonneg_left hsq; positivity
        _ = 16 * (K:ℝ) * (Real.log ((K:ℝ)+2))^2 := by ring
        _ ≤ 16 * ((K:ℝ)+1) * (Real.log ((K:ℝ)+2))^2 := by
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              nlinarith
  rw [stepA, hred]
  calc 4 * (∑ n ∈ Finset.Ioc 0 K, ∑ m ∈ Finset.Ioc 0 K, (Nat.gcd n m : ℝ) / (n : ℝ))
      ≤ 4 * ((K:ℝ) * (1 + Real.log K)^2) := by
        apply mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ ≤ 16 * ((K : ℝ) + 1) * (Real.log ((K : ℝ) + 2)) ^ 2 := hfinal

end Work.FIArea1
