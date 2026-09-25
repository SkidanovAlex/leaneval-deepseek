import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs
import Submission.Work.BourgainPlan.IonescuWainger.iwPN_le_exp

/-!
# **(Σ3, denominators)** Tao's Ionescu–Wainger moduli are `≤ exp(N^ρ)`

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066,
Lemma `iwac`(iv); Mirek–Stein–Trojan, arXiv:1512.07518, §2.

For `S_N = taoSetS ρ N = {smallPrimePowerProd ρ N} ∪ {p^{⌊log N/log p⌋} : N^{ρ/2} < p ≤ N}`
and `k = ⌊2/ρ⌋ + 1`, every modulus `Q_A = ∏_{q ∈ A} q`, `A ⊆ S_N`, `|A| ≤ k`, satisfies
`Q_A ≤ ⌈exp(N^ρ)⌉₊` for all large `N`.

The arithmetic content is split in two:

* every element of `S_N` *other than* the single "small" element `smallPrimePowerProd ρ N` is a
  prime power `p^{⌊log N/log p⌋} ≤ N` (`sigmaNDenom_pow_floor_log_le`), so a product of at most `k`
  of them is at most `N^k`;
* the small element is a product of the prime powers attached to the primes `p ≤ N^{ρ/2}`, each of
  which is `≤ N`, so `smallPrimePowerProd ρ N ≤ N^{⌊N^{ρ/2}⌋} ≤ exp(N^{ρ/2} log N)`, and the
  classical comparison `N^{ρ/2} log N ≤ N^ρ/2` finishes (`sigmaNDenom_smallPrimePowerProd_le_exp`).

Since also `N^k ≤ exp(N^ρ/2)` for large `N` (`sigmaNDenom_natPow_le_exp_half`), the two bounds
multiply to `exp(N^ρ)`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

/-- **The exponent attached to a prime below `N`.**  For a prime `p` and `1 ≤ N` one has
`p ^ ⌊log N / log p⌋ ≤ N`: raising to the real exponent `log N / log p` recovers `N`, and the
floor only makes the left side smaller. -/
lemma sigmaNDenom_pow_floor_log_le {N p : ℕ} (hp : Nat.Prime p) (hN : 1 ≤ N) :
    p ^ ⌊Real.log N / Real.log p⌋₊ ≤ N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hr : 0 ≤ Real.log (N : ℝ) / Real.log (p : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hN)) (le_of_lt hlogp)
  have hmain : ((p : ℝ) ^ (⌊Real.log N / Real.log p⌋₊ : ℕ)) ≤ (N : ℝ) := by
    calc ((p : ℝ) ^ (⌊Real.log N / Real.log p⌋₊ : ℕ))
        = (p : ℝ) ^ ((⌊Real.log N / Real.log p⌋₊ : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (p : ℝ) ^ (Real.log (N : ℝ) / Real.log (p : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (Nat.floor_le hr)
      _ = (N : ℝ) := by
          rw [Real.rpow_def_of_pos hppos]
          have hsimp : Real.log (p : ℝ) * (Real.log (N : ℝ) / Real.log (p : ℝ))
              = Real.log (N : ℝ) := by
            rw [mul_comm (Real.log (p : ℝ)) (Real.log (N : ℝ) / Real.log (p : ℝ)),
              div_mul_cancel₀ _ (ne_of_gt hlogp)]
          rw [hsimp, Real.exp_log hNpos]
  exact_mod_cast hmain

/-- Membership characterisation of Tao's set of large prime powers: the elements of
`largePrimePowers ρ N` are exactly the numbers `p ^ ⌊log N / log p⌋`, `p` prime with
`⌊N^{ρ/2}⌋ + 1 ≤ p ≤ N`. -/
lemma sigmaNDenom_mem_largePrimePowers {ρ : ℝ} {N x : ℕ} :
    x ∈ largePrimePowers ρ N ↔
      ∃ p : ℕ, Nat.Prime p ∧ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 ≤ p ∧ p ≤ N ∧
        p ^ ⌊Real.log N / Real.log p⌋₊ = x := by
  rw [largePrimePowers, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hpx⟩
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    exact ⟨p, hp.2, hp.1.1, hp.1.2, hpx⟩
  · rintro ⟨p, hprim, h1, h2, hpx⟩
    exact ⟨p, by rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨h1, h2⟩, hprim⟩, hpx⟩

/-- The "small" element of `taoSetS ρ N` is a product of prime powers, hence positive. -/
lemma sigmaNDenom_smallPrimePowerProd_pos (ρ : ℝ) (N : ℕ) :
    0 < smallPrimePowerProd ρ N := by
  rw [smallPrimePowerProd]
  exact Finset.prod_pos (fun p hp => pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2) _)

/-- **Products over the large prime powers.**  If `A ⊆ largePrimePowers ρ N` then
`Q_A = ∏_{q ∈ A} q ≤ N^{|A|}`: every element of `largePrimePowers ρ N` is at most `N`. -/
lemma sigmaNDenom_QA_le_pow_card {ρ : ℝ} {N : ℕ} (hN : 1 ≤ N) {A : Finset ℕ}
    (hA : A ⊆ largePrimePowers ρ N) : QA A ≤ N ^ A.card := by
  rw [QA]
  have hle : ∀ q ∈ A, q ≤ N := by
    intro q hq
    obtain ⟨p, hpp, -, -, rfl⟩ := sigmaNDenom_mem_largePrimePowers.mp (hA hq)
    exact sigmaNDenom_pow_floor_log_le hpp hN
  calc ∏ q ∈ A, q ≤ ∏ _q ∈ A, N :=
        Finset.prod_le_prod₀ (fun q _ => Nat.zero_le _) (fun q hq => hle q hq)
    _ = N ^ A.card := Finset.prod_const N

/-- **The small element is `≤ exp(N^ρ/2)`.**  `smallPrimePowerProd ρ N` is the product of the
prime powers `p^{⌊log N/log p⌋} ≤ N` over the primes `p ≤ N^{ρ/2}`, so it is at most
`N^{⌊N^{ρ/2}⌋} = exp(⌊N^{ρ/2}⌋ log N)`, and `N^{ρ/2} log N ≤ N^ρ/2` for large `N`. -/
lemma sigmaNDenom_smallPrimePowerProd_le_exp (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N : ℕ, N₁ ≤ N →
      (smallPrimePowerProd ρ N : ℝ) ≤ Real.exp ((N : ℝ) ^ ρ / 2) := by
  obtain ⟨C, -, hC⟩ := exists_log_le_rpow 2 (ρ / 2) (by norm_num) (by linarith)
  refine ⟨max ⌈C⌉₊ 2, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN1 : 1 ≤ N := by omega
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNposR
  have hNC : C ≤ (N : ℝ) := by
    have h : (⌈C⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hN
    exact le_trans (Nat.le_ceil C) h
  have hlog_le : Real.log (N : ℝ) ≤ (N : ℝ) ^ (ρ / 2) / 2 := by
    have := hC N hNC
    linarith
  have hlogNnn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hfloor_le : ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (ρ / 2) :=
    Nat.floor_le (Real.rpow_nonneg hNnn _)
  have hkey : ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) * Real.log (N : ℝ) ≤ (N : ℝ) ^ ρ / 2 := by
    have h1 : ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) * Real.log (N : ℝ)
        ≤ (N : ℝ) ^ (ρ / 2) * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right hfloor_le hlogNnn
    have h2 : (N : ℝ) ^ (ρ / 2) * Real.log (N : ℝ)
        ≤ (N : ℝ) ^ (ρ / 2) * ((N : ℝ) ^ (ρ / 2) / 2) :=
      mul_le_mul_of_nonneg_left hlog_le (Real.rpow_nonneg hNnn _)
    have h3 : (N : ℝ) ^ (ρ / 2) * ((N : ℝ) ^ (ρ / 2) / 2) = (N : ℝ) ^ ρ / 2 := by
      rw [← mul_div_assoc, ← Real.rpow_add hNposR, show ρ / 2 + ρ / 2 = ρ by ring]
    linarith [h1, h2, h3.le]
  have hcard : ((Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime).card
      ≤ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ := by
    have hsub : Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊ ⊆ Finset.Icc 1 ⌊(N : ℝ) ^ (ρ / 2)⌋₊ := by
      intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    calc ((Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime).card
        ≤ (Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).card := Finset.card_filter_le _ _
      _ ≤ (Finset.Icc 1 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).card := Finset.card_le_card hsub
      _ = ⌊(N : ℝ) ^ (ρ / 2)⌋₊ := by rw [Nat.card_Icc]; omega
  have hcNat : smallPrimePowerProd ρ N ≤ N ^ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ := by
    rw [smallPrimePowerProd]
    calc ∏ p ∈ (Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime,
            p ^ ⌊Real.log N / Real.log p⌋₊
        ≤ ∏ _p ∈ (Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime, N :=
          Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _)
            (fun p hp => sigmaNDenom_pow_floor_log_le (Finset.mem_filter.mp hp).2 hN1)
      _ = N ^ ((Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime).card :=
          Finset.prod_const N
      _ ≤ N ^ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ := Nat.pow_le_pow_right (by omega : 0 < N) hcard
  have hcast : (smallPrimePowerProd ρ N : ℝ) ≤ (N : ℝ) ^ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ := by
    have h : (smallPrimePowerProd ρ N : ℝ) ≤ ((N ^ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) :=
      Nat.cast_le.mpr hcNat
    rwa [Nat.cast_pow] at h
  have hlogpow : Real.log ((N : ℝ) ^ ⌊(N : ℝ) ^ (ρ / 2)⌋₊) ≤ (N : ℝ) ^ ρ / 2 := by
    rw [Real.log_pow]
    exact hkey
  calc (smallPrimePowerProd ρ N : ℝ) ≤ (N : ℝ) ^ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ := hcast
    _ ≤ Real.exp ((N : ℝ) ^ ρ / 2) :=
        (Real.log_le_iff_le_exp (pow_pos hNposR _)).mp hlogpow

/-- **Plain powers are `≤ exp(N^ρ/2)`.**  For `1 ≤ k` and large `N`,
`N^k = exp(k log N) ≤ exp(N^ρ/2)`, since `k log N ≤ N^ρ/2` for large `N`. -/
lemma sigmaNDenom_natPow_le_exp_half (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (hk : 1 ≤ k) :
    ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N : ℕ, N₁ ≤ N →
      ((N ^ k : ℕ) : ℝ) ≤ Real.exp ((N : ℝ) ^ ρ / 2) := by
  obtain ⟨C, -, hC⟩ := exists_log_le_rpow (2 * (k : ℝ)) ρ (by positivity) hρ
  refine ⟨max ⌈C⌉₊ 2, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN1n : 1 ≤ N := by omega
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNC : C ≤ (N : ℝ) := by
    have h : (⌈C⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hN
    exact le_trans (Nat.le_ceil C) h
  have hlog : Real.log ((N : ℝ) ^ k) ≤ (N : ℝ) ^ ρ / 2 := by
    rw [Real.log_pow]
    have h := hC N hNC
    have he : (2 * (k : ℝ)) * Real.log (N : ℝ) = 2 * ((k : ℝ) * Real.log (N : ℝ)) := by ring
    linarith [h, he.le]
  calc ((N ^ k : ℕ) : ℝ) = (N : ℝ) ^ k := by rw [Nat.cast_pow]
    _ ≤ Real.exp ((N : ℝ) ^ ρ / 2) :=
        (Real.log_le_iff_le_exp (pow_pos hNposR k)).mp hlog

/-- **(Σ3, denominators)** Every denominator occurring in Tao's Ionescu–Wainger superset `Σ_N = Σ_{≤k}(taoSetS ρ N)` with `k = ⌊2/ρ⌋ + 1` is at most `exp(N^ρ)` for `N` large.  Route (Tao, Lemma `iwac`(iv)): every element of `taoSetS ρ N` other than the small product `smallPrimePowerProd ρ N` is a prime power `p^{⌊log N/log p⌋} ≤ N`, so for `A ⊆ taoSetS ρ N` with `|A| ≤ k` one has `log Q_A ≤ log (smallPrimePowerProd ρ N) + k log N ≤ N^{ρ/2} log N + k log N = o(N^ρ)`.  (Note `smallPrimePowerProd ρ N` itself is *not* bounded by `N^k`; it is the only element that needs the `N^{ρ/2} log N` bound.) -/
theorem sigmaN_denom_le (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ A : Finset ℕ,
      A ⊆ Work.BourgainPlan.IonescuWainger.taoSetS ρ N →
      A.card ≤ ⌊2 / ρ⌋₊ + 1 →
      Work.BourgainPlan.IonescuWainger.QA A ≤ ⌈Real.exp ((N : ℝ) ^ ρ)⌉₊ := by
  obtain ⟨N₁, hN₁1, hsmall⟩ := sigmaNDenom_smallPrimePowerProd_le_exp ρ hρ
  obtain ⟨N₂, hN₂1, hpow⟩ := sigmaNDenom_natPow_le_exp_half ρ hρ (⌊2 / ρ⌋₊ + 1) (by omega)
  refine ⟨max N₁ N₂, fun N hN A hA hAcard => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) hN
  have hNnat : 1 ≤ N := le_trans hN₁1 hN1
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNposR
  set k : ℕ := ⌊2 / ρ⌋₊ + 1 with hk
  have hAcardk : A.card ≤ k := by rw [hk]; exact hAcard
  have hk1 : 1 ≤ k := by rw [hk]; omega
  have hsmall' : (smallPrimePowerProd ρ N : ℝ) ≤ Real.exp ((N : ℝ) ^ ρ / 2) := hsmall N hN1
  have hk_exp : ((N : ℝ) ^ k) ≤ Real.exp ((N : ℝ) ^ ρ / 2) := by
    have h := hpow N hN2
    rwa [hk, Nat.cast_pow] at h
  have hexp_le : Real.exp ((N : ℝ) ^ ρ / 2) ≤ Real.exp ((N : ℝ) ^ ρ) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.rpow_nonneg hNnn ρ])
  suffices h : (QA A : ℝ) ≤ Real.exp ((N : ℝ) ^ ρ) by
    exact Nat.cast_le.mp (le_trans h (Nat.le_ceil _))
  have hA' : A ⊆ insert (smallPrimePowerProd ρ N) (largePrimePowers ρ N) := by
    simpa [taoSetS] using hA
  by_cases hc : smallPrimePowerProd ρ N ∈ A
  · -- the small element occurs: `Q_A = c · Q_{A∖{c}}` with `|A∖{c}| ≤ k`
    have hsub' : A.erase (smallPrimePowerProd ρ N) ⊆ largePrimePowers ρ N := by
      intro q hq
      rw [Finset.mem_erase] at hq
      obtain ⟨hqc, hqA⟩ := hq
      rcases Finset.mem_insert.mp (hA' hqA) with h | h
      · exact absurd h hqc
      · exact h
    have hcard' : (A.erase (smallPrimePowerProd ρ N)).card ≤ k :=
      le_trans Finset.card_erase_le hAcardk
    have hQA' : QA (A.erase (smallPrimePowerProd ρ N)) ≤ N ^ k :=
      le_trans (sigmaNDenom_QA_le_pow_card hNnat hsub')
        (Nat.pow_le_pow_right (by omega : 0 < N) hcard')
    have hQA'_real : (QA (A.erase (smallPrimePowerProd ρ N)) : ℝ) ≤ (N : ℝ) ^ k := by
      have h : (QA (A.erase (smallPrimePowerProd ρ N)) : ℝ)
          ≤ ((N ^ k : ℕ) : ℝ) := Nat.cast_le.mpr hQA'
      rwa [Nat.cast_pow] at h
    have hsplit : QA A = smallPrimePowerProd ρ N * QA (A.erase (smallPrimePowerProd ρ N)) := by
      rw [QA, QA]
      exact (Finset.mul_prod_erase A (fun q => q) hc).symm
    calc (QA A : ℝ)
        = (smallPrimePowerProd ρ N : ℝ) * (QA (A.erase (smallPrimePowerProd ρ N)) : ℝ) := by
          rw [hsplit]; push_cast; ring
      _ ≤ Real.exp ((N : ℝ) ^ ρ / 2) * Real.exp ((N : ℝ) ^ ρ / 2) :=
          mul_le_mul hsmall' (le_trans hQA'_real hk_exp) (by positivity) (by positivity)
      _ = Real.exp ((N : ℝ) ^ ρ) := by
          rw [← Real.exp_add]
          congr 1
          ring
  · -- the small element does not occur: `A ⊆ largePrimePowers ρ N`
    have hAsub : A ⊆ largePrimePowers ρ N := by
      intro q hq
      rcases Finset.mem_insert.mp (hA' hq) with h | h
      · exact absurd (h ▸ hq) hc
      · exact h
    have hQA : QA A ≤ N ^ k :=
      le_trans (sigmaNDenom_QA_le_pow_card hNnat hAsub)
        (Nat.pow_le_pow_right (by omega : 0 < N) hAcardk)
    have hQA_real : (QA A : ℝ) ≤ (N : ℝ) ^ k := by
      have h : (QA A : ℝ) ≤ ((N ^ k : ℕ) : ℝ) := Nat.cast_le.mpr hQA
      rwa [Nat.cast_pow] at h
    exact le_trans hQA_real (le_trans hk_exp hexp_le)

end Work.BourgainPlan.Maximal
