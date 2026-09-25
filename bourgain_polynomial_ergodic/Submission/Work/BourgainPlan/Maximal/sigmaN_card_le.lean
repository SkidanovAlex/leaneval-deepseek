import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs
import Submission.Work.BourgainPlan.IonescuWainger.card_sigmaSubAFinset
import Submission.Work.BourgainPlan.Maximal.card_powerset_filter_le
import Submission.Work.BourgainPlan.Maximal.sigmaN_log_bound

/-!
# (Σ3, cardinality): Tao's Ionescu–Wainger superset has `≤ exp(N^ρ)` points

`Σ_N = Σ_{≤k}(taoSetS ρ N)`, `k = ⌊2/ρ⌋ + 1`, is the union of the torsion subgroups `𝕋[Q_A]`,
`Q_A = ∏_{a ∈ A} a`, over the `A ⊆ taoSetS ρ N` with `|A| ≤ k` (`sigmaLeFinset`).  Hence

`|Σ_N| ≤ Σ_A Q_A ≤ #{A} · (max_A Q_A) ≤ (k+1)(N+1)^k · Y^k`,

where `Y = N^{⌊N^{ρ/2}⌋+1}` bounds every element of `taoSetT ρ N` (every `p^{⌊log N/log p⌋}` is `≤ N`,
and the "small" element `smallPrimePowerProd ρ N` is a product of at most `⌊N^{ρ/2}⌋+1` factors `≤ N`).
Taking logarithms, the exponent is `log(k+1) + k log(N+1) + k log Y ≤ N^ρ` for `N` large, which gives
the claim (Tao, Lemma `iwac`(iv)).

The two arithmetic inputs are delegated: `card_powerset_filter_le` (the subset count) and
`sigmaN_log_bound` (the elementary asymptotic `k N^{ρ/2} log N + k log N ≤ N^ρ`).
-/

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

open Work.BourgainPlan.IonescuWainger

/-- **The exponent of a prime in Tao's set is at most `N`**: for a prime `p` and `1 ≤ N`,
`p ^ ⌊log N / log p⌋ ≤ N`. -/
private lemma prime_pow_floor_log_div_log_le {N p : ℕ} (hp : Nat.Prime p) (hN : 1 ≤ N) :
    p ^ ⌊Real.log N / Real.log p⌋₊ ≤ N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hr : 0 ≤ Real.log (N : ℝ) / Real.log (p : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hN)) hlogp.le
  have hmain : ((p : ℝ) ^ (⌊Real.log (N : ℝ) / Real.log (p : ℝ)⌋₊ : ℕ)) ≤ (N : ℝ) := by
    calc ((p : ℝ) ^ (⌊Real.log (N : ℝ) / Real.log (p : ℝ)⌋₊ : ℕ))
        = (p : ℝ) ^ ((⌊Real.log (N : ℝ) / Real.log (p : ℝ)⌋₊ : ℕ) : ℝ) :=
          (Real.rpow_natCast _ _).symm
      _ ≤ (p : ℝ) ^ (Real.log (N : ℝ) / Real.log (p : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (Nat.floor_le hr)
      _ = (N : ℝ) := by
          rw [Real.rpow_def_of_pos hppos]
          have hcancel : Real.log (p : ℝ) * (Real.log (N : ℝ) / Real.log (p : ℝ))
              = Real.log (N : ℝ) := by
            field_simp
          rw [hcancel, Real.exp_log hNpos]
  exact_mod_cast hmain

/-- **The "small" element of `taoSetS ρ N` is a product of at most `⌊N^{ρ/2}⌋ + 1` numbers `≤ N`**:
`smallPrimePowerProd ρ N ≤ N ^ (⌊N^{ρ/2}⌋ + 1)`. -/
private lemma smallPrimePowerProd_le_pow (ρ : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    smallPrimePowerProd ρ N ≤ N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1) := by
  rw [smallPrimePowerProd]
  have hstep : ∏ p ∈ (Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime,
        p ^ ⌊Real.log N / Real.log p⌋₊
      ≤ ∏ _p ∈ (Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime, N := by
    apply Finset.prod_le_prod₀
    · intro p _
      exact Nat.zero_le _
    · intro p hp
      exact prime_pow_floor_log_div_log_le (Finset.mem_filter.mp hp).2 hN
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
    calc p ^ ⌊Real.log N / Real.log p⌋₊ ≤ N := prime_pow_floor_log_div_log_le hp.2 hN
      _ = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- **`taoSetS ρ N` has at most `N + 1` elements**: it consists of the prime powers
`p^{⌊log N/log p⌋}` for the at most `N` primes `p ≤ N`, plus the single small product. -/
private lemma taoSetS_card_le (ρ : ℝ) (hρ : 0 < ρ) {N : ℕ} (hN : 1 ≤ N) :
    (taoSetS ρ N).card ≤ N := by
  rw [taoSetS]
  refine (Finset.card_insert_le _ _).trans ?_
  have hlarge : (largePrimePowers ρ N).card ≤ N - 1 := by
    rw [largePrimePowers]
    refine (Finset.card_image_le).trans ?_
    refine (Finset.card_le_card
      (Finset.filter_subset (Nat.Prime) (Finset.Icc (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1) N))).trans ?_
    rw [Nat.card_Icc]
    have hm : 1 ≤ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ := by
      have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      exact Nat.floor_pos.mpr (Real.one_le_rpow hN1R (by positivity))
    omega
  omega

/-- **(Σ3, cardinality)** Tao's Ionescu–Wainger superset `Σ_N = Σ_{≤k}(taoSetS ρ N)`, `k = ⌊2/ρ⌋ + 1`, has at most `exp(N^ρ)` points for `N` large (Tao, Lemma `iwac`(iv)).  Route: `sigmaLeFinset S k` is the union of the torsion subgroups `𝕋[Q_A]` over the `A ⊆ S` with `|A| ≤ k`, so its cardinality is at most `#{A} · max_A Q_A`; `|taoSetS ρ N| ≤ N + 1` gives `#{A} ≤ (N+1)^k`, and the denominator bound `Q_A ≤ exp(N^ρ)` (for `N ≥ N₁`) gives the claim.  (The small element `smallPrimePowerProd ρ N` is larger than `N`, so the estimate must go through `N^{ρ/2} log N + k log N`, not through `N^k`.) -/
theorem sigmaN_card_le (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      (Work.BourgainPlan.IonescuWainger.sigmaLeFinset
        (Work.BourgainPlan.IonescuWainger.taoSetS ρ N) (⌊2 / ρ⌋₊ + 1)).card
      ≤ ⌈Real.exp ((N : ℝ) ^ ρ)⌉₊ := by
  set k : ℕ := ⌊2 / ρ⌋₊ + 1 with hk
  obtain ⟨C, hC⟩ := sigmaN_log_bound ρ hρ k
  refine ⟨max C 2, fun N hN => ?_⟩
  have hNC : C ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN1 : 1 ≤ N := by omega
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hY : ∀ a ∈ taoSetS ρ N, a ≤ N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1) :=
    fun a ha => le_of_mem_taoSetS ρ hN1 ha
  -- ### Step 1: the union bound over the subsets `A`
  have h1 : (sigmaLeFinset (taoSetS ρ N) k).card
      ≤ ∑ A ∈ (taoSetS ρ N).powerset.filter (fun A => A.card ≤ k), QA A := by
    rw [sigmaLeFinset]
    exact (Finset.card_biUnion_le).trans
      (Finset.sum_le_sum (fun A _ => le_of_eq (card_sigmaSubAFinset A)))
  -- ### Step 2: each `Q_A` is at most `Y^k`
  have h2 : ∑ A ∈ (taoSetS ρ N).powerset.filter (fun A => A.card ≤ k), QA A
      ≤ ((taoSetS ρ N).powerset.filter (fun A => A.card ≤ k)).card
        * (N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ k := by
    have hb : ∀ A ∈ (taoSetS ρ N).powerset.filter (fun A => A.card ≤ k),
        QA A ≤ (N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ k := by
      intro A hA
      rw [Finset.mem_filter, Finset.mem_powerset] at hA
      have hQA : QA A ≤ (N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ A.card := by
        rw [QA]
        exact Finset.prod_le_pow_card A (fun a => a) _ (fun a ha => hY a (hA.1 ha))
      exact hQA.trans (Nat.pow_le_pow_right (by positivity) hA.2)
    simpa [smul_eq_mul] using
      Finset.sum_le_card_nsmul ((taoSetS ρ N).powerset.filter (fun A => A.card ≤ k))
        (fun A => QA A) ((N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ k) hb
  -- ### Step 3: the number of subsets `A`
  have h3 : ((taoSetS ρ N).powerset.filter (fun A => A.card ≤ k)).card
        * (N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ k
      ≤ ((k + 1) * (N + 1) ^ k) * (N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ k := by
    apply Nat.mul_le_mul_right
    refine (card_powerset_filter_le (taoSetS ρ N) k).trans ?_
    have hSc : (taoSetS ρ N).card + 1 ≤ N + 1 := by
      have := taoSetS_card_le ρ hρ hN1
      omega
    exact Nat.mul_le_mul_left (k + 1) (Nat.pow_le_pow_left hSc k)
  have hcard : (sigmaLeFinset (taoSetS ρ N) k).card
      ≤ (k + 1) * (N + 1) ^ k * (N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ k :=
    h1.trans (h2.trans h3)
  -- ### Step 4: cast to `ℝ` and take logarithms
  have hcast : (((sigmaLeFinset (taoSetS ρ N) k).card : ℕ) : ℝ)
      ≤ ((k : ℝ) + 1) * ((N : ℝ) + 1) ^ k
        * ((N : ℝ) ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ k := by
    have h0 : (((sigmaLeFinset (taoSetS ρ N) k).card : ℕ) : ℝ)
        ≤ (((k + 1) * (N + 1) ^ k * (N ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ k : ℕ) : ℝ) := by
      exact_mod_cast hcard
    push_cast at h0
    exact h0
  have hprodpos : (0 : ℝ) < ((k : ℝ) + 1) * ((N : ℝ) + 1) ^ k
      * ((N : ℝ) ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ k := by positivity
  have hlog : Real.log (((k : ℝ) + 1) * ((N : ℝ) + 1) ^ k
      * ((N : ℝ) ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ k) ≤ (N : ℝ) ^ ρ := by
    have hlogid : Real.log (((k : ℝ) + 1) * ((N : ℝ) + 1) ^ k
        * ((N : ℝ) ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ k)
        = Real.log ((k : ℝ) + 1) + (k : ℝ) * Real.log ((N : ℝ) + 1)
          + (k : ℝ) * (((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) + 1) * Real.log (N : ℝ) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      ring
    rw [hlogid]
    have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1R
    have hmle : (((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) + 1) ≤ (N : ℝ) ^ (ρ / 2) + 2 := by
      have hfl := Nat.floor_le (show (0 : ℝ) ≤ (N : ℝ) ^ (ρ / 2) by positivity)
      linarith
    have hstep : (k : ℝ) * (((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) + 1) * Real.log (N : ℝ)
        ≤ (k : ℝ) * ((N : ℝ) ^ (ρ / 2) + 2) * Real.log (N : ℝ) := by
      have h4 : (((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) + 1) * Real.log (N : ℝ)
          ≤ ((N : ℝ) ^ (ρ / 2) + 2) * Real.log (N : ℝ) :=
        mul_le_mul_of_nonneg_right hmle hlogN
      calc (k : ℝ) * (((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) + 1) * Real.log (N : ℝ)
          = (k : ℝ) * ((((⌊(N : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) + 1) * Real.log (N : ℝ)) := by ring
        _ ≤ (k : ℝ) * (((N : ℝ) ^ (ρ / 2) + 2) * Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg k)
        _ = (k : ℝ) * ((N : ℝ) ^ (ρ / 2) + 2) * Real.log (N : ℝ) := by ring
    linarith [hstep, hC N hNC]
  -- ### Step 5: exponentiate
  have hfinal : (((sigmaLeFinset (taoSetS ρ N) k).card : ℕ) : ℝ) ≤ Real.exp ((N : ℝ) ^ ρ) := by
    calc (((sigmaLeFinset (taoSetS ρ N) k).card : ℕ) : ℝ)
        ≤ ((k : ℝ) + 1) * ((N : ℝ) + 1) ^ k
          * ((N : ℝ) ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ k := hcast
      _ = Real.exp (Real.log (((k : ℝ) + 1) * ((N : ℝ) + 1) ^ k
          * ((N : ℝ) ^ (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1)) ^ k)) := (Real.exp_log hprodpos).symm
      _ ≤ Real.exp ((N : ℝ) ^ ρ) := Real.exp_le_exp.mpr hlog
  exact_mod_cast le_trans hfinal (Nat.le_ceil (Real.exp ((N : ℝ) ^ ρ)))

end Work.BourgainPlan.Maximal
