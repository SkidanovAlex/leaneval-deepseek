import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

/-- If `N` is large enough that `N ≥ ⌈2^(2/ρ)⌉`, then `⌊N^(ρ/2)⌋ ≥ 2` (for `ρ > 0`). -/
private lemma two_le_floor_rpow_half {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ}
    (hN : ⌈(2 : ℝ) ^ (2 / ρ)⌉₊ ≤ N) : 2 ≤ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ := by
  have h2le : (2 : ℝ) ^ (2 / ρ) ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have hbase : (0 : ℝ) ≤ (2 : ℝ) ^ (2 / ρ) := Real.rpow_nonneg (by norm_num) _
  have hexp : (0 : ℝ) ≤ ρ / 2 := by linarith
  have h := Real.rpow_le_rpow hbase h2le hexp
  have hpow : ((2 : ℝ) ^ (2 / ρ)) ^ (ρ / 2) = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hmul : 2 / ρ * (ρ / 2) = 1 := by
      field_simp
    rw [hmul, Real.rpow_one]
  rw [hpow] at h
  exact Nat.le_floor h

/-- If `2 ≤ N` and `p` is a prime with `p ≤ N`, then `⌊log N / log p⌋ ≥ 1`. -/
private lemma one_le_floor_log_div {N p : ℕ} (hp : Nat.Prime p) (hpN : p ≤ N) :
    1 ≤ ⌊Real.log N / Real.log p⌋₊ := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hle : Real.log (p : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hppos (by exact_mod_cast hpN)
  have h1 : 1 ≤ Real.log (N : ℝ) / Real.log (p : ℝ) := (one_le_div hlogp).mpr hle
  have hpos : 0 < ⌊Real.log (N : ℝ) / Real.log (p : ℝ)⌋₊ := Nat.floor_pos.mpr h1
  omega

/-- Membership characterisation of Tao's set of large prime powers: the elements of
`largePrimePowers ρ N` are exactly the numbers `p ^ ⌊log N / log p⌋`, `p` prime with
`⌊N^{ρ/2}⌋ + 1 ≤ p ≤ N`. -/
private lemma mem_largePrimePowers {ρ : ℝ} {N x : ℕ} :
    x ∈ Work.BourgainPlan.IonescuWainger.largePrimePowers ρ N ↔
      ∃ p : ℕ, Nat.Prime p ∧ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 ≤ p ∧ p ≤ N ∧
        p ^ ⌊Real.log N / Real.log p⌋₊ = x := by
  simp only [Work.BourgainPlan.IonescuWainger.largePrimePowers, Finset.mem_image,
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨p, ⟨⟨h1, h2⟩, hpp⟩, hpx⟩
    exact ⟨p, hpp, h1, h2, hpx⟩
  · rintro ⟨p, hpp, h1, h2, hpx⟩
    exact ⟨p, ⟨⟨h1, h2⟩, hpp⟩, hpx⟩

/-- For every `ρ > 0` and all large `N`, every element of Tao's set
`taoSetS ρ N = {smallPrimePowerProd ρ N} ∪ {p^{⌊log N/log p⌋} : N^{ρ/2} < p ≤ N}` is `≥ 2`.
Route: the "large" elements are `p ^ ⌊log N / log p⌋` with `p` prime and `p ≤ N`, so the exponent
`⌊log N / log p⌋` is `≥ 1` (as `log N ≥ log p > 0` for `N ≥ 2`) and the element is `≥ p ≥ 2`; the
"small" element is a product whose index set contains `2` once `⌊N^{ρ/2}⌋₊ ≥ 2`, so it is at least
`2 ^ ⌊log N / log 2⌋ ≥ 2`, all other factors being `≥ 1`. -/
lemma taoSetS_two_le (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ q ∈ Work.BourgainPlan.IonescuWainger.taoSetS ρ N, 2 ≤ q := by
  refine ⟨max ⌈(2 : ℝ) ^ (2 / ρ)⌉₊ 2, ?_⟩
  intro N hN q hq
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hM : 2 ≤ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ :=
    two_le_floor_rpow_half hρ (le_trans (le_max_left _ _) hN)
  rw [Work.BourgainPlan.IonescuWainger.taoSetS, Finset.mem_insert] at hq
  rcases hq with rfl | hq
  · -- the "small" element: the product over the primes `p ≤ ⌊N^{ρ/2}⌋` contains the factor at `2`
    rw [Work.BourgainPlan.IonescuWainger.smallPrimePowerProd]
    set s := (Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime with hs
    have h2mem : 2 ∈ s := by
      rw [hs, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_rfl, hM⟩, Nat.prime_two⟩
    have hfac : ∀ p ∈ s, 1 ≤ p ^ ⌊Real.log N / Real.log p⌋₊ := by
      intro p hp
      rw [hs, Finset.mem_filter] at hp
      exact Nat.one_le_pow _ _ (Nat.Prime.pos hp.2)
    refine le_trans ?_ (Finset.single_le_prod' hfac h2mem)
    have h1 : 1 ≤ ⌊Real.log N / Real.log 2⌋₊ :=
      one_le_floor_log_div Nat.prime_two hN2
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ ⌊Real.log N / Real.log 2⌋₊ := Nat.pow_le_pow_right (by norm_num) h1
  · -- the "large" elements: `p ^ e` with `e ≥ 1`, `p ≥ 2`
    obtain ⟨p, hpp, -, hpN, rfl⟩ := mem_largePrimePowers.mp hq
    have he : 1 ≤ ⌊Real.log N / Real.log p⌋₊ := one_le_floor_log_div hpp hpN
    calc (2 : ℕ) ≤ p := hpp.two_le
      _ ≤ p ^ ⌊Real.log N / Real.log p⌋₊ := Nat.le_self_pow (by omega) p

end Work.BourgainPlan.Maximal
