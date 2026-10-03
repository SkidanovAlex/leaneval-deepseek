/-
# `Submission.Work.FIChain.RhoWin2TailInlined`

The `n₁ > Δπ` tail of the integrated `ρ`-window (`RhoWin2Tail`), re-proved against the
**sorry-free** fibre-counting lemma `RhoTailReindex2`.

`Submission.Work.FIChain.RhoWin2Tail` is complete but its proof invokes
`Submission.Work.FIChain.RhoTailReindex`, a module that still ends in `sorry`; a consumer
that imports it therefore inherits `sorryAx`.  This module contains the same argument with
`RhoTailReindex` replaced by `RhoTailReindex2`, so that it is axiom-clean
(`propext`, `Quot.sound`, `Classical.choice` only) and can be consumed by
`Submission.Work.FIChain.RhoWindowIntegrated2`.
-/
import Mathlib
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FIChain.RhoTailReindex2
import Submission.Work.FIChain.RhoTailWeightLe
import Submission.Work.FIChain.RhoTailRankin
import Submission.Work.FIChain.RhoTailDoubleIntegralBound
import Submission.Work.FITop.AseqTauEightBound
import Submission.Work.FITop.RCPrelude
import Submission.Work.FITop.SingleDvdTauSqLe

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.FIChain


open Finset Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The tail integrand, its mass bound, and the reindexed weight -/

/-- The `n₁ > Δπ` index set of the tail: the divisors of `Π(Pz)` above `Δπ`. -/
def TailT (x : ℕ) : Finset ℕ :=
  (ProdP (Pzc x)).divisors.filter (fun n₁ : ℕ => DpiC x < n₁)

/-- The `n₁ > Δπ` tail integrand of the `ρ`-window `Π`-removal. -/
def TailInt (x : ℕ) (s t : ℝ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 2 *
    (∑ n₁ ∈ (ProdP (Pzc x)).divisors.filter (fun n₁ : ℕ => (DpiC x : ℝ) < n₁),
      ∑ d₁ ∈ n₁.divisors, |Xpg x (Pzc x) (c * n₁) (s / d₁) (t / n₁)|)

/-- The mass dominating `TailInt`: the window and coprimality conditions are dropped and
the absolute values are replaced by `τ`. -/
def TailMass (x : ℕ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 2 *
    (∑ n₁ ∈ TailT x, ((n₁.divisors.card : ℝ)) *
      ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n₁ * n ≤ x),
        ((n.divisors.card : ℝ)) * atilc (c * n₁ * n))

/-- The reindexed weight `τ(M)³·ã(M)`. -/
private def Ftau (M : ℕ) : ℝ := ((M.divisors.card : ℝ)) ^ 3 * atilc M

private lemma one_le_DpiC (x : ℕ) : 1 ≤ DpiC x := by
  rw [DpiC, Dpi]
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

private lemma TailT_mem {x n₁ : ℕ} (h : n₁ ∈ TailT x) :
    n₁ ∣ ProdP (Pzc x) ∧ DpiC x < n₁ := by
  rw [TailT, Finset.mem_filter, Nat.mem_divisors] at h
  exact ⟨h.1.1, h.2⟩

private lemma TailT_one_le {x n₁ : ℕ} (h : n₁ ∈ TailT x) : 1 ≤ n₁ := by
  have h2 := (TailT_mem h).2
  have := one_le_DpiC x
  omega

private lemma filter_real_eq_TailT (x : ℕ) :
    (ProdP (Pzc x)).divisors.filter (fun n₁ : ℕ => (DpiC x : ℝ) < n₁) = TailT x := by
  rw [TailT]
  exact Finset.filter_congr (fun n₁ _ => Nat.cast_lt)

private lemma TailInt_nonneg (x : ℕ) (s t : ℝ) : 0 ≤ TailInt x s t := by
  rw [TailInt]
  refine Finset.sum_nonneg (fun c _ => mul_nonneg (by positivity) ?_)
  exact Finset.sum_nonneg (fun n₁ _ => Finset.sum_nonneg (fun d₁ _ => abs_nonneg _))

private lemma TailMass_nonneg (x : ℕ) : 0 ≤ TailMass x := by
  rw [TailMass]
  refine Finset.sum_nonneg (fun c _ => mul_nonneg (by positivity) ?_)
  refine Finset.sum_nonneg (fun n₁ _ => mul_nonneg (Nat.cast_nonneg _) ?_)
  exact Finset.sum_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg _)
    (Work.FITop.atilFIa_nonneg _))

/-- `|Xpg|` is dominated by the unsigned mass of the same modulus. -/
private lemma Xpg_mass (x Pz c : ℕ) (σ u : ℝ) :
    |Xpg x Pz c σ u| ≤ ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n ≤ x),
      ((n.divisors.card : ℝ)) * atilc (c * n) := by
  refine (abs_Xpg_le_mass x Pz c σ u).trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  · intro n _ _
    exact mul_nonneg (Nat.cast_nonneg _) (Work.FITop.atilFIa_nonneg _)

/-- The pointwise domination of the tail integrand by its mass. -/
private lemma TailInt_le_TailMass (x : ℕ) (s t : ℝ) : TailInt x s t ≤ TailMass x := by
  rw [TailInt, TailMass, filter_real_eq_TailT x]
  refine Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine Finset.sum_le_sum (fun n₁ _ => ?_)
  calc ∑ d₁ ∈ n₁.divisors, |Xpg x (Pzc x) (c * n₁) (s / d₁) (t / n₁)|
      ≤ ∑ _d₁ ∈ n₁.divisors, (∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n₁ * n ≤ x),
          ((n.divisors.card : ℝ)) * atilc (c * n₁ * n)) :=
        Finset.sum_le_sum (fun d₁ _ => Xpg_mass x (Pzc x) (c * n₁) (s / d₁) (t / n₁))
    _ = ((n₁.divisors.card : ℝ)) * ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n₁ * n ≤ x),
          ((n.divisors.card : ℝ)) * atilc (c * n₁ * n) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## 2. The arithmetic bound for the mass -/

private lemma TailMass_le (C8 : ℕ) (x : ℕ)
    (hL1 : 1 ≤ Real.log (x : ℝ))
    (hPz : 2 ≤ Pzc x) (hD1 : 1 ≤ DpiC x)
    (hRan : ((DpiC x : ℝ)) ^ (-(Real.log 2 / Real.log ((Pzc x : ℕ) : ℝ)))
        ≤ (Real.log (x : ℝ)) ^ (-(262150 : ℤ)))
    (hMom : (∑ M ∈ Finset.Icc 1 x, atilc M * (((M.divisors.card : ℝ)) ^ 8))
        ≤ (C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ)) :
    TailMass x ≤ (C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(6 : ℤ)) := by
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hL1
  have hDnn : (0 : ℝ) ≤ (DpiC x : ℝ) := Nat.cast_nonneg _
  have hFnn : ∀ M, 0 ≤ Ftau M := fun M => by
    rw [Ftau]
    exact mul_nonneg (by positivity) (Work.FITop.atilFIa_nonneg M)
  -- flatten `TailMass` into a triple sum
  have hTM : TailMass x = ∑ c ∈ Finset.Icc 1 x, ∑ n₁ ∈ TailT x,
      ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n₁ * n ≤ x),
        ((c.divisors.card : ℝ)) ^ 2 * ((n₁.divisors.card : ℝ))
          * ((n.divisors.card : ℝ)) * atilc (c * n₁ * n) := by
    rw [TailMass]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n₁ _ => ?_)
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    ring
  -- (A) the pointwise Rankin step, summed
  have hA : TailMass x ≤ ((DpiC x : ℝ)) ^ (-(Real.log 2 / Real.log ((Pzc x : ℕ) : ℝ)))
      * (∑ c ∈ Finset.Icc 1 x, ∑ n₁ ∈ TailT x,
          ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n₁ * n ≤ x), Ftau (c * n₁ * n)) := by
    rw [hTM, Finset.mul_sum]
    refine Finset.sum_le_sum (fun c hc => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun n₁ hn₁ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun n hn => ?_)
    have h1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
    have h2 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have h := RhoTailWeightLe (Pzc x) (DpiC x) c n₁ n hPz hD1 (TailT_mem hn₁).1
      (TailT_mem hn₁).2 h1 h2
    simpa only [Ftau, mul_assoc] using h
  refine hA.trans ?_
  -- (B) the reindexing
  have hRe := RhoTailReindex2 x (TailT x) (fun n₁ hn₁ => TailT_one_le hn₁) Ftau hFnn
  have hB : (∑ c ∈ Finset.Icc 1 x, ∑ n₁ ∈ TailT x,
        ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n₁ * n ≤ x), Ftau (c * n₁ * n))
      ≤ ∑ M ∈ Finset.Icc 1 x, atilc M * (((M.divisors.card : ℝ)) ^ 8) := by
    refine hRe.trans (Finset.sum_le_sum (fun M hM => ?_))
    have hM1 : (1 : ℝ) ≤ ((M.divisors.card : ℝ)) := by
      have h : (1 : ℕ) ≤ M.divisors.card := by
        refine Finset.card_pos.mpr ⟨1, ?_⟩
        rw [Nat.mem_divisors]
        exact ⟨one_dvd M, by have := (Finset.mem_Icc.mp hM).1; omega⟩
      exact_mod_cast h
    have hp : (((M.divisors.card : ℝ))) ^ (5 : ℕ) ≤ (((M.divisors.card : ℝ))) ^ (8 : ℕ) :=
      pow_le_pow_right₀ hM1 (by norm_num)
    calc Ftau M * ((M.divisors.card : ℝ)) ^ 2
        = atilc M * (((M.divisors.card : ℝ)) ^ (3 : ℕ) * ((M.divisors.card : ℝ)) ^ (2 : ℕ)) := by
          rw [Ftau]; ring
      _ = atilc M * (((M.divisors.card : ℝ)) ^ (5 : ℕ)) := by
          rw [← pow_add]
      _ ≤ atilc M * (((M.divisors.card : ℝ)) ^ (8 : ℕ)) :=
          mul_le_mul_of_nonneg_left hp (Work.FITop.atilFIa_nonneg M)
  -- (C) exponent bookkeeping
  have hExp : (Real.log (x : ℝ)) ^ (-(262150 : ℤ)) * ((C8 : ℝ) * AcountAtilC x
        * (Real.log (x : ℝ)) ^ (262144 : ℕ))
      = (C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(6 : ℤ)) := by
    have e2 : (Real.log (x : ℝ)) ^ (262144 : ℕ) = (Real.log (x : ℝ)) ^ ((262144 : ℤ)) :=
      (zpow_natCast _ _).symm
    rw [e2]
    have h1 : (Real.log (x : ℝ)) ^ (-(262150 : ℤ))
          * ((C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ ((262144 : ℤ)))
        = (C8 : ℝ) * AcountAtilC x
          * ((Real.log (x : ℝ)) ^ (-(262150 : ℤ))
            * (Real.log (x : ℝ)) ^ ((262144 : ℤ))) := by ring
    rw [h1]
    have hc : (-(262150 : ℤ)) + (262144 : ℤ) = (-(6 : ℤ)) := by norm_num
    have hcomb : (Real.log (x : ℝ)) ^ (-(262150 : ℤ))
        * (Real.log (x : ℝ)) ^ ((262144 : ℤ)) = (Real.log (x : ℝ)) ^ (-(6 : ℤ)) := by
      rw [← zpow_add₀ hLpos.ne', hc]
    rw [hcomb]

  have hMnn : (0 : ℝ) ≤ (C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Work.FITop.AcountAtil_nonneg' x)) (pow_nonneg hLpos.le _)
  calc ((DpiC x : ℝ)) ^ (-(Real.log 2 / Real.log ((Pzc x : ℕ) : ℝ)))
        * (∑ c ∈ Finset.Icc 1 x, ∑ n₁ ∈ TailT x,
            ∑ n ∈ (Finset.Icc 1 x).filter (fun n => c * n₁ * n ≤ x), Ftau (c * n₁ * n))
      ≤ ((DpiC x : ℝ)) ^ (-(Real.log 2 / Real.log ((Pzc x : ℕ) : ℝ)))
        * (∑ M ∈ Finset.Icc 1 x, atilc M * (((M.divisors.card : ℝ)) ^ 8)) :=
        mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hDnn _)
    _ ≤ ((DpiC x : ℝ)) ^ (-(Real.log 2 / Real.log ((Pzc x : ℕ) : ℝ)))
        * ((C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ)) :=
        mul_le_mul_of_nonneg_left hMom (Real.rpow_nonneg hDnn _)
    _ ≤ (Real.log (x : ℝ)) ^ (-(262150 : ℤ))
        * ((C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ)) :=
        mul_le_mul hRan (le_refl _) hMnn (by positivity)
    _ = (C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(6 : ℤ)) := hExp

/-! ## 3. The target -/

theorem RhoWin2TailInlined : ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in Filter.atTop, ∀ lo hi C : ℝ,
    0 < lo → lo ≤ hi → 1 ≤ C →
    Real.log (hi / lo) ≤ 2 * Real.log (x : ℝ) →
    Real.log C ≤ 2 * Real.log (x : ℝ) →
    (∫ t in lo..hi, (∫ s in (1 : ℝ)..C,
      (∑ c ∈ Finset.Icc 1 x, ((c.divisors.card : ℝ)) ^ 2 *
        (∑ n₁ ∈ (ProdP (Pzc x)).divisors.filter (fun n₁ : ℕ => (DpiC x : ℝ) < n₁),
          ∑ d₁ ∈ n₁.divisors,
            |Xpg x (Pzc x) (c * n₁) (s / d₁) (t / n₁)|)) / s) / t)
    ≤ K * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by
  obtain ⟨C8, X8, hC8pos, hMom⟩ := Work.FITop.AseqTauEightBound
  obtain ⟨xr, hRan⟩ := RhoTailRankin
  refine ⟨4 * (C8 : ℝ), by positivity, ?_⟩
  have hL1ev : ∀ᶠ x : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (x : ℝ) :=
    Work.FITop.FI_ev_log_ge_nat 1
  have hPz2ev : ∀ᶠ x : ℕ in Filter.atTop, 2 ≤ Pzc x := by
    filter_upwards [Work.FITop.FI_ev_log_ge_nat (Real.exp 1)] with x hx
    have hll1 : (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by
      have h := Real.log_le_log (Real.exp_pos 1) hx
      rwa [Real.log_exp] at h
    have hexp : (2 : ℝ) ≤ Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2) := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        linarith
      refine le_trans h2 (Real.exp_le_exp.mpr ?_)
      nlinarith
    have hPzR : (2 : ℝ) ≤ (Pzc x : ℝ) := le_trans hexp (Work.FITop.FI_Pcut_ge x)
    exact_mod_cast hPzR
  filter_upwards [hL1ev, hPz2ev, Filter.eventually_ge_atTop (max X8 xr)] with x hL1x hPz2x hx
  intro lo hi C hlo hlohi hC1 hloghi hlogC
  change (∫ t in lo..hi, (∫ s in (1 : ℝ)..C, TailInt x s t / s) / t)
    ≤ 4 * (C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ))
  have hxX8 : X8 ≤ x := le_trans (le_max_left _ _) hx
  have hxxr : xr ≤ x := le_trans (le_max_right _ _) hx
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le one_pos hL1x
  have h2Lnn : 0 ≤ 2 * Real.log (x : ℝ) := by linarith
  have hM := TailMass_le C8 x hL1x hPz2x (one_le_DpiC x) (hRan x hxxr) (hMom x hxX8)
  have hInt := RhoTailDoubleIntegralBound (F := fun s t : ℝ => TailInt x s t) (B := TailMass x)
    hlo hlohi hC1 (TailInt_nonneg x) (TailInt_le_TailMass x) (TailMass_nonneg x)
  have hlogCnn : 0 ≤ Real.log C := Real.log_nonneg hC1
  have hratio : 1 ≤ hi / lo := (one_le_div hlo).mpr hlohi
  have hlognn : 0 ≤ Real.log (hi / lo) := Real.log_nonneg hratio
  have hstep1 : (∫ t in lo..hi, (∫ s in (1 : ℝ)..C, TailInt x s t / s) / t)
      ≤ TailMass x * (2 * Real.log (x : ℝ)) * (2 * Real.log (x : ℝ)) :=
    hInt.trans (mul_le_mul (mul_le_mul_of_nonneg_left hlogC (TailMass_nonneg x)) hloghi
      hlognn (mul_nonneg (TailMass_nonneg x) h2Lnn))
  have hAnn : (0 : ℝ) ≤ AcountAtilC x := Work.FITop.AcountAtil_nonneg' x
  have hstep2 : TailMass x * (2 * Real.log (x : ℝ)) * (2 * Real.log (x : ℝ))
      ≤ ((C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(6 : ℤ)))
        * (2 * Real.log (x : ℝ)) * (2 * Real.log (x : ℝ)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hM h2Lnn) (le_refl _) h2Lnn
      (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hAnn)
        (zpow_nonneg hLpos.le _)) h2Lnn)
  have hstep3 : ((C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(6 : ℤ)))
        * (2 * Real.log (x : ℝ)) * (2 * Real.log (x : ℝ))
      = 4 * (C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by
    have hpow : (Real.log (x : ℝ)) ^ (-(6 : ℤ)) * (2 * Real.log (x : ℝ))
          * (2 * Real.log (x : ℝ))
        = 4 * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by
      have hLL : (Real.log (x : ℝ)) * (Real.log (x : ℝ)) = (Real.log (x : ℝ)) ^ ((2 : ℤ)) := by
        rw [zpow_ofNat, pow_two]
      have h1 : (Real.log (x : ℝ)) ^ (-(6 : ℤ)) * (2 * Real.log (x : ℝ))
            * (2 * Real.log (x : ℝ))
          = 4 * ((Real.log (x : ℝ)) ^ (-(6 : ℤ))
            * ((Real.log (x : ℝ)) * (Real.log (x : ℝ)))) := by ring
      rw [h1, hLL]
      have hc : (-(6 : ℤ)) + (2 : ℤ) = (-(4 : ℤ)) := by norm_num
      have hcomb : (Real.log (x : ℝ)) ^ (-(6 : ℤ)) * (Real.log (x : ℝ)) ^ ((2 : ℤ))
          = (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by
        rw [← zpow_add₀ hLpos.ne', hc]
      rw [hcomb]
    calc ((C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(6 : ℤ)))
          * (2 * Real.log (x : ℝ)) * (2 * Real.log (x : ℝ))
        = (C8 : ℝ) * AcountAtilC x
            * ((Real.log (x : ℝ)) ^ (-(6 : ℤ)) * (2 * Real.log (x : ℝ))
              * (2 * Real.log (x : ℝ))) := by ring
      _ = (C8 : ℝ) * AcountAtilC x * (4 * (Real.log (x : ℝ)) ^ (-(4 : ℤ))) := by rw [hpow]
      _ = 4 * (C8 : ℝ) * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := by ring
  exact hstep1.trans (hstep2.trans (le_of_eq hstep3))

end


end Work.FIChain
