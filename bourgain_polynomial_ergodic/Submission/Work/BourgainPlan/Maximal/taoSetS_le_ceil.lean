import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs
import Submission.Work.BourgainPlan.Maximal.sigmaN_denom_le
import Submission.Work.BourgainPlan.Maximal.sigmaN_card_le

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

open Work.BourgainPlan.IonescuWainger

/-- **The "small" element of `taoSetS ρ N` is a product of at most `⌊N^{ρ/2}⌋ + 1` numbers `≤ N`**:
`smallPrimePowerProd ρ N ≤ N ^ (⌊N^{ρ/2}⌋ + 1)`.  Each prime power in the product is `≤ N`
(`sigmaNDenom_pow_floor_log_le`) and there are at most `⌊N^{ρ/2}⌋ + 1` of them. -/
private lemma smallPrimePowerProd_le_pow (ρ : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    smallPrimePowerProd ρ N ≤ N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1) := by
  rw [smallPrimePowerProd]
  have hstep : ∏ p ∈ (Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime,
        p ^ ⌊Real.log N / Real.log p⌋₊
      ≤ ∏ _p ∈ (Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime, N :=
    Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _)
      (fun p hp => sigmaNDenom_pow_floor_log_le (Finset.mem_filter.mp hp).2 hN)
  have hcard : ((Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime).card
      ≤ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 := by
    have h := Finset.card_le_card
      (Finset.filter_subset (Nat.Prime) (Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊))
    rw [Nat.card_Icc] at h
    omega
  calc ∏ p ∈ (Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime,
          p ^ ⌊Real.log N / Real.log p⌋₊
      ≤ ∏ _p ∈ (Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime, N := hstep
    _ = N ^ ((Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime).card := Finset.prod_const N
    _ ≤ N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1) := Nat.pow_le_pow_right (by omega) hcard

/-- **Every element of Tao's set `taoSetS ρ N` is at most `N ^ (⌊N^{ρ/2}⌋ + 1)`** (for `1 ≤ N`):
the large elements are the prime powers `p^{⌊log N/log p⌋} ≤ N`, the small one is
`smallPrimePowerProd ρ N ≤ N^{⌊N^{ρ/2}⌋+1}`. -/
private lemma le_of_mem_taoSetS (ρ : ℝ) {N a : ℕ} (hN : 1 ≤ N) (ha : a ∈ taoSetS ρ N) :
    a ≤ N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1) := by
  rw [taoSetS, Finset.mem_insert] at ha
  rcases ha with rfl | ha
  · exact smallPrimePowerProd_le_pow ρ hN
  · rw [largePrimePowers, Finset.mem_image] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    calc p ^ ⌊Real.log N / Real.log p⌋₊ ≤ N := sigmaNDenom_pow_floor_log_le hp.2 hN
      _ = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- Every element of Tao's set `taoSetS ρ N` is at most `⌈N ^ (⌊N^{ρ/2}⌋ + 1)⌉` when `1 ≤ N`.
Route, in the `ℕ`-power form `q ≤ N ^ (⌊N^{ρ/2}⌋₊ + 1)`:
`smallPrimePowerProd ρ N = ∏_{p ≤ N^{ρ/2}} p^{⌊log N/log p⌋}` is a product with at most
`⌊N^{ρ/2}⌋₊ + 1` factors, each `≤ N` (the public lemma `sigmaNDenom_pow_floor_log_le`), hence at
most `N ^ (⌊N^{ρ/2}⌋₊ + 1)`; every other element of `taoSetS ρ N` is a prime power
`p^{⌊log N/log p⌋} ≤ N`. The `ℕ`-power form is already proved, as the private lemma
`le_of_mem_taoSetS`, in `Submission/Work/BourgainPlan/Maximal/sigmaN_card_le.lean` (copy it).
To pass to the `⌈·⌉₊`-form: `(N:ℝ) ^ ((m:ℕ):ℝ) = (N:ℝ) ^ m` (`Real.rpow_natCast`), so
`(q:ℝ) ≤ (N:ℝ) ^ ((m:ℕ):ℝ) ≤ ((↑⌈(N:ℝ) ^ ((m:ℕ):ℝ)⌉₊ : ℕ) : ℝ)` by `Nat.le_ceil`, and `exact_mod_cast`. -/
lemma taoSetS_le_ceil (ρ : ℝ) :
    ∀ N : ℕ, 1 ≤ N → ∀ q ∈ Work.BourgainPlan.IonescuWainger.taoSetS ρ N,
      q ≤ ⌈(N : ℝ) ^ ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 : ℕ) : ℝ)⌉₊ := by
  intro N hN q hq
  have hnat : q ≤ N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1) := le_of_mem_taoSetS ρ hN hq
  have hreal : (q : ℝ) ≤ (N : ℝ) ^ ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 : ℕ) : ℝ) := by
    have h1 : (q : ℝ) ≤ ((N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    rw [Nat.cast_pow] at h1
    rw [Real.rpow_natCast]
    exact h1
  have h2 : (q : ℝ)
      ≤ ((⌈(N : ℝ) ^ ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) :=
    hreal.trans (Nat.le_ceil _)
  exact_mod_cast h2

end Work.BourgainPlan.Maximal
