import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs
import Submission.Work.BourgainPlan.IonescuWainger.ArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.ArcSep
import Submission.Work.BourgainPlan.Maximal.sigmaN_denom_le
import Submission.Work.BourgainPlan.Maximal.sigmaN_farey_helpers
import Submission.Work.BourgainPlan.Maximal.sigmaN_log_bound

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

local notation "𝕋" => Work.BourgainPlan.IonescuWainger.Circle

/-!
# (Σ4) Tao's Ionescu–Wainger superset `Σ_N` is `2 exp(−N^ρ)`-separated

This file proves the elementary arithmetic fact that two *distinct* points of

`Σ_N = Σ_{≤ k}(S_N) = ⋃_{A ⊆ S_N, |A| ≤ k} 𝕋[Q_A]`,  `S_N = taoSetS ρ N`,  `k = ⌊2/ρ⌋₊ + 1`,

are separated by at least `2 exp(−N^ρ)` once `N` is large, so that the bumps `η((·−β)/ε)` of width
`ε ≤ exp(−N^ρ)` have disjoint supports.

## The argument

Every point of `Σ_N` is `β = a/Q_A` with `A ⊆ S_N`, `|A| ≤ k`.  Two such points differ by

`a/Q_A − a'/Q_{A'} = (a Q_{A'} − a' Q_A)/(Q_A Q_{A'})`,

a rational whose denominator (in the circle `𝕋 = ℝ/ℤ`) divides `Q_A Q_{A'}`; if the two points are
distinct this fraction is not an integer, so the circle norm of the difference is at least
`1/(Q_A Q_{A'})` (`one_div_mul_le_norm_arcPt_sub`).  It therefore remains to bound `Q_A Q_{A'}`.

The corpus bound `sigmaN_denom_le` only gives `Q_A ≤ exp(N^ρ)`, which yields the too weak
`exp(−2N^ρ)`.  Here we record the sharper bound actually available from the proof: every element of
`S_N` is `≤ exp(N^{ρ/2} log N)` (the "small" product) or a prime power `≤ N` (`sigmaNDenom_*`), so

`log Q_A ≤ N^{ρ/2} log N + k log N ≤ N^ρ/4`

for large `N` (`sigmaN_QA_le_exp_quarter`), and hence `Q_A Q_{A'} ≤ exp(N^ρ/2)`.  Finally
`2 exp(−N^ρ) ≤ exp(−N^ρ/2)` for large `N` since `N^ρ ≥ 2 log 2`, which closes the chain

`2 exp(−N^ρ) ≤ exp(−N^ρ/2) ≤ 1/(Q_A Q_{A'}) ≤ ‖β − β'‖`.
-/

/-- **A product of prime powers is `≤ exp(c N^ρ)`.**  `smallPrimePowerProd ρ N` is the product of
`p^{⌊log N/log p⌋} ≤ N` over the primes `p ≤ N^{ρ/2}`, hence at most `N^{⌊N^{ρ/2}⌋₊}` with logarithm
`⌊N^{ρ/2}⌋₊ log N ≤ N^{ρ/2} log N ≤ c N^ρ` for large `N`. -/
lemma smallPrimePowerProd_le_exp_scaled (ρ : ℝ) (hρ : 0 < ρ) {c : ℝ} (hc : 0 < c) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      (smallPrimePowerProd ρ N : ℝ) ≤ Real.exp (c * (N : ℝ) ^ ρ) := by
  obtain ⟨C, -, hC⟩ := exists_log_le_rpow (1 / c) (ρ / 2) (by positivity) (by linarith)
  refine ⟨max ⌈C⌉₊ 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN1n : 1 ≤ N := by omega
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := hNposR.le
  have hNC : C ≤ (N : ℝ) := by
    have h : (⌈C⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hN
    exact le_trans (Nat.le_ceil C) h
  have hlog_le : Real.log (N : ℝ) ≤ c * (N : ℝ) ^ (ρ / 2) := by
    have h := hC N hNC
    have hrewrite : c * ((1 / c) * Real.log (N : ℝ)) = Real.log (N : ℝ) := by
      field_simp
    calc Real.log (N : ℝ) = c * ((1 / c) * Real.log (N : ℝ)) := hrewrite.symm
      _ ≤ c * (N : ℝ) ^ (ρ / 2) := mul_le_mul_of_nonneg_left h hc.le
  have hfloor_le : ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (ρ / 2) :=
    Nat.floor_le (Real.rpow_nonneg hNnn _)
  have hlogNnn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1n)
  have hkey : ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) * Real.log (N : ℝ)
      ≤ c * (N : ℝ) ^ ρ := by
    have h1 : ((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) * Real.log (N : ℝ)
        ≤ (N : ℝ) ^ (ρ / 2) * Real.log (N : ℝ) :=
      mul_le_mul_of_nonneg_right hfloor_le hlogNnn
    have h2 : (N : ℝ) ^ (ρ / 2) * Real.log (N : ℝ)
        ≤ (N : ℝ) ^ (ρ / 2) * (c * (N : ℝ) ^ (ρ / 2)) :=
      mul_le_mul_of_nonneg_left hlog_le (Real.rpow_nonneg hNnn _)
    have h3 : (N : ℝ) ^ (ρ / 2) * (c * (N : ℝ) ^ (ρ / 2)) = c * (N : ℝ) ^ ρ := by
      have h := Real.rpow_add hNposR (ρ / 2) (ρ / 2)
      rw [show ρ / 2 + ρ / 2 = ρ by ring] at h
      rw [h]; ring
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
            (fun p hp => sigmaNDenom_pow_floor_log_le (Finset.mem_filter.mp hp).2 hN1n)
      _ = N ^ ((Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime).card :=
          Finset.prod_const N
      _ ≤ N ^ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ := Nat.pow_le_pow_right (by omega : 0 < N) hcard
  have hcast : (smallPrimePowerProd ρ N : ℝ) ≤ (N : ℝ) ^ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ := by
    have h : (smallPrimePowerProd ρ N : ℝ) ≤ ((N ^ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) :=
      Nat.cast_le.mpr hcNat
    rwa [Nat.cast_pow] at h
  have hlogpow : Real.log ((N : ℝ) ^ ⌊(N : ℝ) ^ (ρ / 2)⌋₊) ≤ c * (N : ℝ) ^ ρ := by
    rw [Real.log_pow]
    exact hkey
  calc (smallPrimePowerProd ρ N : ℝ) ≤ (N : ℝ) ^ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ := hcast
    _ ≤ Real.exp (c * (N : ℝ) ^ ρ) :=
        (Real.log_le_iff_le_exp (pow_pos hNposR _)).mp hlogpow

/-- **A plain power is `≤ exp(c N^ρ)`.**  `N^k = exp(k log N)` and `k log N ≤ c N^ρ` for large `N`. -/
lemma natPow_le_exp_scaled (ρ : ℝ) (hρ : 0 < ρ) {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 1 ≤ k) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ((N ^ k : ℕ) : ℝ) ≤ Real.exp (c * (N : ℝ) ^ ρ) := by
  obtain ⟨C, -, hC⟩ := exists_log_le_rpow ((k : ℝ) / c) ρ (by positivity) hρ
  refine ⟨max ⌈C⌉₊ 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN1n : 1 ≤ N := by omega
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNC : C ≤ (N : ℝ) := by
    have h : (⌈C⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hN
    exact le_trans (Nat.le_ceil C) h
  have hlog : Real.log ((N : ℝ) ^ k) ≤ c * (N : ℝ) ^ ρ := by
    rw [Real.log_pow]
    have h := hC N hNC
    have hrewrite : c * ((k : ℝ) / c * Real.log (N : ℝ)) = (k : ℝ) * Real.log (N : ℝ) := by
      field_simp
    calc (k : ℝ) * Real.log (N : ℝ) = c * ((k : ℝ) / c * Real.log (N : ℝ)) := hrewrite.symm
      _ ≤ c * (N : ℝ) ^ ρ := mul_le_mul_of_nonneg_left h hc.le
  calc ((N ^ k : ℕ) : ℝ) = (N : ℝ) ^ k := by rw [Nat.cast_pow]
    _ ≤ Real.exp (c * (N : ℝ) ^ ρ) :=
        (Real.log_le_iff_le_exp (pow_pos hNposR k)).mp hlog

/-- **(Σ4), quantitative denominator bound.**  Every modulus `Q_A = ∏_{q ∈ A} q` with
`A ⊆ taoSetS ρ N`, `|A| ≤ ⌊2/ρ⌋₊ + 1`, is at most `exp(N^ρ/4)` for `N` large.  This refines
`sigmaN_denom_le` (which gives `exp(N^ρ)`) and is what the separation estimate needs. -/
lemma sigmaN_QA_le_exp_quarter (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ A : Finset ℕ,
      A ⊆ Work.BourgainPlan.IonescuWainger.taoSetS ρ N →
      A.card ≤ ⌊2 / ρ⌋₊ + 1 →
      (QA A : ℝ) ≤ Real.exp ((N : ℝ) ^ ρ / 4) := by
  obtain ⟨N₁, hsmall⟩ := smallPrimePowerProd_le_exp_scaled ρ hρ (c := 1 / 8) (by norm_num)
  obtain ⟨N₂, hpow⟩ := natPow_le_exp_scaled ρ hρ (c := 1 / 8) (by norm_num) (k := ⌊2 / ρ⌋₊ + 1)
    (by omega)
  refine ⟨max (max N₁ N₂) 2, fun N hN A hA hAcard => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2' : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNnat : 1 ≤ N := by omega
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set k : ℕ := ⌊2 / ρ⌋₊ + 1 with hk
  have hAcardk : A.card ≤ k := by rw [hk]; exact hAcard
  have hsmallpos : (0 : ℝ) < (smallPrimePowerProd ρ N : ℝ) := by
    exact_mod_cast sigmaNDenom_smallPrimePowerProd_pos ρ N
  have hsmall' : (smallPrimePowerProd ρ N : ℝ) ≤ Real.exp ((1 / 8) * (N : ℝ) ^ ρ) :=
    hsmall N hN1
  have hpow' : ((N : ℝ) ^ k) ≤ Real.exp ((1 / 8) * (N : ℝ) ^ ρ) := by
    simpa [Nat.cast_pow] using hpow N hN2
  have hbound : (QA A : ℝ) ≤ (smallPrimePowerProd ρ N : ℝ) * (N : ℝ) ^ k := by
    have hA' : A ⊆ insert (smallPrimePowerProd ρ N) (largePrimePowers ρ N) := by
      simpa [taoSetS] using hA
    by_cases hc : smallPrimePowerProd ρ N ∈ A
    · have hsub' : A.erase (smallPrimePowerProd ρ N) ⊆ largePrimePowers ρ N := by
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
        have h : (QA (A.erase (smallPrimePowerProd ρ N)) : ℝ) ≤ ((N ^ k : ℕ) : ℝ) :=
          Nat.cast_le.mpr hQA'
        rwa [Nat.cast_pow] at h
      have hsplit : QA A = smallPrimePowerProd ρ N * QA (A.erase (smallPrimePowerProd ρ N)) := by
        rw [QA, QA]
        exact (Finset.mul_prod_erase A (fun q => q) hc).symm
      calc (QA A : ℝ)
          = (smallPrimePowerProd ρ N : ℝ) * (QA (A.erase (smallPrimePowerProd ρ N)) : ℝ) := by
            rw [hsplit]; push_cast; ring
        _ ≤ (smallPrimePowerProd ρ N : ℝ) * (N : ℝ) ^ k :=
            mul_le_mul_of_nonneg_left hQA'_real hsmallpos.le
    · have hAsub : A ⊆ largePrimePowers ρ N := by
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
      have h1s : (1 : ℝ) ≤ (smallPrimePowerProd ρ N : ℝ) := by
        have : 1 ≤ smallPrimePowerProd ρ N :=
          Nat.one_le_iff_ne_zero.mpr (ne_of_gt (sigmaNDenom_smallPrimePowerProd_pos ρ N))
        exact_mod_cast this
      calc (QA A : ℝ) ≤ (N : ℝ) ^ k := hQA_real
        _ = 1 * (N : ℝ) ^ k := by ring
        _ ≤ (smallPrimePowerProd ρ N : ℝ) * (N : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right h1s (by positivity)
  calc (QA A : ℝ) ≤ (smallPrimePowerProd ρ N : ℝ) * (N : ℝ) ^ k := hbound
    _ ≤ Real.exp ((1 / 8) * (N : ℝ) ^ ρ) * Real.exp ((1 / 8) * (N : ℝ) ^ ρ) :=
        mul_le_mul hsmall' hpow' (by positivity) (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) ^ ρ / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- **Arithmetic separation of two torsion points.**  If `a/Q` and `a'/Q'` are distinct points of
`𝕋 = ℝ/ℤ` (with `Q, Q' ≠ 0`), then their circle distance is at least `1/(Q Q')`: their difference
is a rational of denominator dividing `Q Q'` which is not an integer. -/
lemma one_div_mul_le_norm_arcPt_sub {Q Q' : ℕ} (hQ : Q ≠ 0) (hQ' : Q' ≠ 0) {a a' : ℤ}
    (h : arcPt Q a ≠ arcPt Q' a') :
    1 / ((Q : ℝ) * (Q' : ℝ)) ≤ ‖arcPt Q a - arcPt Q' a'‖ := by
  have hQr : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hQ
  have hQ'r : (0 : ℝ) < (Q' : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hQ'
  have hNpos : (0 : ℝ) < (Q : ℝ) * (Q' : ℝ) := mul_pos hQr hQ'r
  have hx : arcPt Q a - arcPt Q' a'
      = ((((a : ℝ) / (Q : ℝ) - (a' : ℝ) / (Q' : ℝ) : ℝ)) : 𝕋) := by
    simp only [arcPt]
    rw [← AddCircle.coe_sub]
  rw [hx, AddCircle.norm_eq]
  simp only [inv_one, one_mul, mul_one]
  set m : ℤ := a * (Q' : ℤ) - a' * (Q : ℤ) with hm
  have hxM : (a : ℝ) / (Q : ℝ) - (a' : ℝ) / (Q' : ℝ) = (m : ℝ) / ((Q : ℝ) * (Q' : ℝ)) := by
    simp only [hm]
    push_cast
    field_simp
  rw [hxM]
  set r : ℤ := round ((m : ℝ) / ((Q : ℝ) * (Q' : ℝ))) with hr
  set z : ℤ := m - r * ((Q : ℤ) * (Q' : ℤ)) with hz
  have hzsplit : (m : ℝ) / ((Q : ℝ) * (Q' : ℝ)) - (r : ℝ)
      = (z : ℝ) / ((Q : ℝ) * (Q' : ℝ)) := by
    simp only [hz]
    push_cast
    field_simp
  rw [hzsplit, abs_div, abs_of_pos hNpos]
  have hz0 : z ≠ 0 := by
    intro hzz
    have heq : (m : ℝ) / ((Q : ℝ) * (Q' : ℝ)) = (r : ℝ) := by
      have h1 := hzsplit
      rw [hzz] at h1
      simp only [Int.cast_zero, zero_div, sub_eq_zero] at h1
      exact h1
    have hzero : (((m : ℝ) / ((Q : ℝ) * (Q' : ℝ))) : 𝕋) = 0 := by
      rw [heq]
      exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨r, by simp⟩
    refine h ?_
    rw [← hxM, ← hx] at hzero
    exact sub_eq_zero.mp hzero
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hz0
  rw [div_le_div_iff_of_pos_right hNpos]
  exact hz1

/-- MST route, property (Σ4): distinct points of Tao's superset `Σ_N = Σ_{≤⌊2/ρ⌋+1}(S_N)` are `2·exp(−N^ρ)`-separated, so that the bumps `η((·−β)/ε)` of width `ε ≤ exp(−N^ρ)` have disjoint supports. -/
theorem sigmaN_separated {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      ∀ β ∈ Work.BourgainPlan.IonescuWainger.sigmaLeFinset
          (Work.BourgainPlan.IonescuWainger.taoSetS ρ N) (⌊2 / ρ⌋₊ + 1),
      ∀ β' ∈ Work.BourgainPlan.IonescuWainger.sigmaLeFinset
          (Work.BourgainPlan.IonescuWainger.taoSetS ρ N) (⌊2 / ρ⌋₊ + 1),
        β ≠ β' → 2 * Real.exp (-(N : ℝ) ^ ρ) ≤ ‖β - β'‖ := by
  obtain ⟨Nden, hden⟩ := sigmaN_QA_le_exp_quarter ρ hρ
  obtain ⟨Ntriv, htriv⟩ := exists_rpow_ge (s := ρ) (B := 2 * Real.log 2) hρ (by positivity)
  refine ⟨max (max Nden Ntriv) 1, fun N hN β hβ β' hβ' hne => ?_⟩
  have hNd : Nden ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNt : Ntriv ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  -- extract representations of `β` and `β'`
  rw [sigmaLeFinset, Finset.mem_biUnion] at hβ
  obtain ⟨A, hA, hβA⟩ := hβ
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  obtain ⟨hAS, hAcard⟩ := hA
  rw [sigmaSubAFinset, Finset.mem_image] at hβA
  obtain ⟨a, -, hβeq⟩ := hβA
  rw [sigmaLeFinset, Finset.mem_biUnion] at hβ'
  obtain ⟨A', hA', hβA'⟩ := hβ'
  rw [Finset.mem_filter, Finset.mem_powerset] at hA'
  obtain ⟨hA'S, hA'card⟩ := hA'
  rw [sigmaSubAFinset, Finset.mem_image] at hβA'
  obtain ⟨a', -, hβ'eq⟩ := hβA'
  -- the two torsion points are distinct
  have hne' : arcPt (QA A) (a : ℤ) ≠ arcPt (QA A') (a' : ℤ) := by
    rw [hβeq, hβ'eq]
    exact hne
  -- denominators are nonzero
  have hQAnz : QA A ≠ 0 := QA_ne_zero_of_subset_taoSetS hAS
  have hQA'nz : QA A' ≠ 0 := QA_ne_zero_of_subset_taoSetS hA'S
  have hQApos : (0 : ℝ) < (QA A : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hQAnz
  have hQA'pos : (0 : ℝ) < (QA A' : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hQA'nz
  -- the sharp denominator bounds
  have hdenA : (QA A : ℝ) ≤ Real.exp ((N : ℝ) ^ ρ / 4) := hden N hNd A hAS hAcard
  have hdenA' : (QA A' : ℝ) ≤ Real.exp ((N : ℝ) ^ ρ / 4) := hden N hNd A' hA'S hA'card
  have hprod : (QA A : ℝ) * (QA A' : ℝ) ≤ Real.exp ((N : ℝ) ^ ρ / 2) := by
    calc (QA A : ℝ) * (QA A' : ℝ)
        ≤ Real.exp ((N : ℝ) ^ ρ / 4) * Real.exp ((N : ℝ) ^ ρ / 4) :=
          mul_le_mul hdenA hdenA' hQA'pos.le (Real.exp_pos _).le
      _ = Real.exp ((N : ℝ) ^ ρ / 4 + (N : ℝ) ^ ρ / 4) := (Real.exp_add _ _).symm
      _ = Real.exp ((N : ℝ) ^ ρ / 2) := by ring_nf
  have hposprod : (0 : ℝ) < (QA A : ℝ) * (QA A' : ℝ) := mul_pos hQApos hQA'pos
  -- `exp(N^ρ/2) ≥ 2`
  have hexp2 : (2 : ℝ) ≤ Real.exp ((N : ℝ) ^ ρ / 2) := by
    have hrp : 2 * Real.log 2 ≤ (N : ℝ) ^ ρ := by
      have h := htriv N (by exact_mod_cast hNt : (Ntriv : ℝ) ≤ (N : ℝ))
      exact h
    have hlog2 : Real.log 2 ≤ (N : ℝ) ^ ρ / 2 := by linarith
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp ((N : ℝ) ^ ρ / 2) := Real.exp_le_exp.mpr hlog2
  have hkey : 2 * Real.exp (-(N : ℝ) ^ ρ) ≤ 1 / ((QA A : ℝ) * (QA A' : ℝ)) := by
    rw [le_div_iff₀ hposprod]
    calc 2 * Real.exp (-(N : ℝ) ^ ρ) * ((QA A : ℝ) * (QA A' : ℝ))
        ≤ 2 * Real.exp (-(N : ℝ) ^ ρ) * Real.exp ((N : ℝ) ^ ρ / 2) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 2 * Real.exp (-(N : ℝ) ^ ρ + (N : ℝ) ^ ρ / 2) := by
          rw [mul_assoc, ← Real.exp_add]
      _ = 2 * Real.exp (-((N : ℝ) ^ ρ / 2)) := by ring_nf
      _ ≤ 1 := by
          rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
          simpa using hexp2
  have hsep := one_div_mul_le_norm_arcPt_sub hQAnz hQA'nz hne'
  calc 2 * Real.exp (-(N : ℝ) ^ ρ)
      ≤ 1 / ((QA A : ℝ) * (QA A' : ℝ)) := hkey
    _ ≤ ‖arcPt (QA A) (a : ℤ) - arcPt (QA A') (a' : ℤ)‖ := hsep
    _ = ‖β - β'‖ := by rw [hβeq, hβ'eq]

end Work.BourgainPlan.Maximal
