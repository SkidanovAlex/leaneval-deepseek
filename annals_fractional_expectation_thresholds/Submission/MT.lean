import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import ChallengeDeps
import Submission.Prob
import Submission.Minimals
import Submission.Qpos
import Submission.Dual
import Submission.Binom
import Submission.Mono2
import Submission.PVCore
import Submission.PVAPI
import Submission.PVIterP

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval ProbabilityTheory
open FractionalExpectationThresholds

attribute [local instance] Classical.propDecidable

namespace Submission
namespace FET

universe u
variable {X : Type u} [Fintype X]

/-- universal constant for the spread-hitting theorem. -/
noncomputable def MTK : ℝ := 2 ^ 30

/-- spread condition for weight function `ν` with rate `α`. -/
def WeightSpread (α : ℝ) (ν : Set X → ℝ) : Prop :=
  ∀ T : Set X, (∑ E : Set X, if T ⊆ E then ν E else 0) ≤ α ^ T.ncard

/-- support of a weight function. -/
def wSupp (w : Set X → ℝ) : Set (Set X) := {S | w S ≠ 0}

/-- the upward closure of the support. -/
def wUp (w : Set X → ℝ) : Set (Set X) := {Y | ∃ S, w S ≠ 0 ∧ S ⊆ Y}

/-- the upward closure is an upper set. -/
lemma isUpperSet_wUp (w : Set X → ℝ) : IsUpperSet (wUp w) := by
  intro A B hAB hA
  rcases hA with ⟨S, hS0, hSA⟩
  exact ⟨S, hS0, subset_trans hSA hAB⟩

/-- if all support elements lie in the increasing family `𝓕`, then so does the up-closure. -/
lemma wUp_subset_of_increasing {w : Set X → ℝ} {𝓕 : Set (Set X)} (h𝓕 : IsUpperSet 𝓕)
    (hwF : ∀ S, w S ≠ 0 → S ∈ 𝓕) : wUp w ⊆ 𝓕 := by
  intro Y hY
  rcases hY with ⟨S, hS0, hSY⟩
  exact h𝓕 hSY (hwF S hS0)

open Submission.PVC
open Submission.PVAPI
open Submission.PVIter
open Submission.PVIterP

/-- every cover of the support of a spread probability measure has cost at least 1. -/
lemma one_le_ecost_of_supp (α : ℝ) (ν : Set X → ℝ)
    (hν0 : ∀ S, 0 ≤ ν S) (hν1 : (∑ S : Set X, ν S) = 1)
    (hsp : WeightSpread α ν) {G : Set (Set X)} (hG : Covers G (wSupp ν)) :
    1 ≤ ecost α G := by
  classical
  let ind (S : Set X) : ℝ := ∑ T : Set X, if T ∈ G ∧ T ⊆ S then (1 : ℝ) else 0
  have hcover : ∀ S, ν S ≠ 0 → 1 ≤ ind S := by
    intro S hS
    have hmem : S ∈ wSupp ν := by simp [wSupp, hS]
    rcases hG S hmem with ⟨T, hT, hTS⟩
    unfold ind
    have hterm : (1 : ℝ) ≤ ∑ T0 : Set X, if T0 = T then (1 : ℝ) else 0 := by simp
    exact le_trans hterm (Finset.sum_le_sum (fun T0 hT0 => by
      by_cases hEq : T0 = T
      · subst T0
        simp [hT, hTS]
      · by_cases hc : T0 ∈ G ∧ T0 ⊆ S
        · simp [hEq, hc]
        · simp [hEq, hc]))
  have hmain : (∑ S : Set X, ν S) ≤ ecost α G := by
    calc
      (∑ S : Set X, ν S) ≤ ∑ S : Set X, ν S * ind S := by
        apply Finset.sum_le_sum
        intro S hS
        by_cases hν : ν S = 0
        · simp [hν]
        · have hc := hcover S hν
          have hm := mul_le_mul_of_nonneg_left hc (hν0 S)
          simpa using hm
      _ ≤ ecost α G := by
        have hd : (∑ S : Set X, ν S * ind S)
            = ∑ S : Set X, ∑ T : Set X, ν S * (if T ∈ G ∧ T ⊆ S then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro S hS
              unfold ind
              rw [Finset.mul_sum]
        have hswap : (∑ S : Set X, ∑ T : Set X, ν S * (if T ∈ G ∧ T ⊆ S then (1 : ℝ) else 0))
            = ∑ T : Set X, (∑ S : Set X, ν S * (if T ∈ G ∧ T ⊆ S then (1 : ℝ) else 0)) := by
              rw [Finset.sum_comm]
        have hcol : (∑ T : Set X, (∑ S : Set X, ν S * (if T ∈ G ∧ T ⊆ S then (1 : ℝ) else 0)))
            = ∑ T : Set X, (if T ∈ G then (∑ S : Set X, if T ⊆ S then ν S else 0) else 0) := by
              apply Finset.sum_congr rfl
              intro T hT
              by_cases hTG : T ∈ G
              · have hleft : (∑ S : Set X, ν S * (if T ∈ G ∧ T ⊆ S then (1 : ℝ) else 0))
                    = (∑ S : Set X, ν S * (if T ⊆ S then (1 : ℝ) else 0)) := by
                      apply Finset.sum_congr rfl
                      intro S hS
                      simp [hTG]
                have hright : (∑ S : Set X, ν S * (if T ⊆ S then (1 : ℝ) else 0))
                    = (∑ S : Set X, if T ⊆ S then ν S else 0) := by
                      apply Finset.sum_congr rfl
                      intro S hS
                      by_cases hTS : T ⊆ S <;> simp [hTS]
                simp [hTG, hleft, hright]
              · have hzero : (∑ S : Set X, ν S * (if T ∈ G ∧ T ⊆ S then (1 : ℝ) else 0)) = 0 := by
                    apply Finset.sum_eq_zero
                    intro S hS
                    simp [hTG]
                simp [hTG, hzero]
        have hbnd : (∑ T : Set X, (if T ∈ G then (∑ S : Set X, if T ⊆ S then ν S else 0) else 0))
            ≤ ecost α G := by
              unfold ecost
              apply Finset.sum_le_sum
              intro T hT
              by_cases hTG : T ∈ G
              · simp [hTG, hsp T]
              · simp [hTG]
        calc
          (∑ S : Set X, ν S * ind S) = ∑ S : Set X, ∑ T : Set X, ν S * (if T ∈ G ∧ T ⊆ S then (1 : ℝ) else 0) := hd
          _ = ∑ T : Set X, (∑ S : Set X, ν S * (if T ∈ G ∧ T ⊆ S then (1 : ℝ) else 0)) := hswap
          _ = ∑ T : Set X, (if T ∈ G then (∑ S : Set X, if T ⊆ S then ν S else 0) else 0) := hcol
          _ ≤ ecost α G := hbnd
  calc
    1 = (∑ S : Set X, ν S) := hν1.symm
    _ ≤ ecost α G := hmain

/-- the minimal cover cost of the support is at least 1. -/
lemma one_le_ccost_of_supp (α : ℝ) (ν : Set X → ℝ)
    (hν0 : ∀ S, 0 ≤ ν S) (hν1 : (∑ S : Set X, ν S) = 1)
    (hsp : WeightSpread α ν) (hα0 : 0 ≤ α) :
    1 ≤ ccost α (wSupp ν) := by
  apply ccost_ge_of_forall_covers
  intro G hG
  exact one_le_ecost_of_supp α ν hν0 hν1 hsp hG


/-- Bernoulli-type bound: `1-(1-x)^n ≤ n·x` for `0 ≤ x ≤ 1`. -/
lemma bernoulli_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    1 - (1 - x) ^ n ≤ (n : ℝ) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hle1 : (1 - x) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have hxm : x * (1 - x) ^ n ≤ x := by
        have hm := mul_le_mul_of_nonneg_left hle1 hx0
        simpa using hm
      rw [pow_succ']
      calc
        1 - (1 - x) * (1 - x) ^ n = (1 - (1 - x) ^ n) + x * (1 - x) ^ n := by ring
        _ ≤ (n : ℝ) * x + x := add_le_add ih hxm
        _ = ((n + 1 : ℕ) : ℝ) * x := by
          rw [Nat.cast_add]
          ring

/-- `log 2 ≥ 1/2`. -/
lemma log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have hg : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  norm_num at hg
  linarith

/-- `log ℓ ≥ log 2` for `ℓ ≥ 2`. -/
lemma log_large {ℓ : ℕ} (hℓ : 2 ≤ ℓ) : Real.log 2 ≤ Real.log (ℓ : ℝ) :=
  Real.log_le_log (by norm_num) (by exact_mod_cast hℓ)

/-- `log2 ℓ ≤ log ℓ / log 2` for `ℓ ≥ 1`. -/
lemma log2_le_log_div {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (Nat.log2 ℓ : ℝ) ≤ Real.log (ℓ : ℝ) / Real.log 2 := by
  have hp : (2 : ℕ) ^ Nat.log 2 ℓ ≤ ℓ :=
    Nat.pow_log_le_self (2 : ℕ) (by omega : ℓ ≠ 0)
  have hp' : (2 : ℝ) ^ Nat.log 2 ℓ ≤ (ℓ : ℝ) := by exact_mod_cast hp
  have hpow : (2 : ℝ) ^ Nat.log2 ℓ ≤ (ℓ : ℝ) := by
    simpa [Nat.log2_eq_log_two] using hp'
  have hpos : 0 < (2 : ℝ) ^ Nat.log2 ℓ := by positivity
  have hlog := Real.log_le_log hpos hpow
  have hmain : (Nat.log2 ℓ : ℝ) * Real.log 2 ≤ Real.log (ℓ : ℝ) := by
    have hlog2m : Real.log ((2 : ℝ) ^ Nat.log2 ℓ) = (Nat.log2 ℓ : ℝ) * Real.log 2 :=
      Real.log_pow (2 : ℝ) (Nat.log2 ℓ)
    nlinarith
  rw [le_div_iff₀ (by linarith [log_two_ge_half] : 0 < Real.log 2)]
  nlinarith

/-- `log ℓ / log 2 ≤ 2·log ℓ` for `ℓ ≥ 1` (using `log 2 ≥ 1/2` and `log ℓ ≥ 0`). -/
lemma log_div_le_two_log {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    Real.log (ℓ : ℝ) / Real.log 2 ≤ 2 * Real.log (ℓ : ℝ) := by
  have hpos : 0 < Real.log 2 := by linarith [log_two_ge_half]
  have hlog0 : 0 ≤ Real.log (ℓ : ℝ) := Real.log_nonneg (by exact_mod_cast hℓ)
  rw [div_le_iff₀ hpos]
  have h2le : 1 ≤ 2 * Real.log 2 := by linarith [log_two_ge_half]
  have hm := mul_le_mul_of_nonneg_left h2le hlog0
  ring_nf at hm ⊢
  nlinarith

/-- `d(ℓ) = log2 ℓ + 1 ≤ 4·log ℓ` for `ℓ ≥ 2`. -/
lemma log2_succ_le_four_log {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ((Nat.log2 ℓ + 1 : ℕ) : ℝ) ≤ 4 * Real.log (ℓ : ℝ) := by
  have h1 : 1 ≤ ℓ := by omega
  have hle1 : (Nat.log2 ℓ : ℝ) ≤ Real.log (ℓ : ℝ) / Real.log 2 := log2_le_log_div h1
  have hone : (1 : ℝ) ≤ Real.log (ℓ : ℝ) / Real.log 2 := by
    have hlogpos : 0 < Real.log 2 := by linarith [log_two_ge_half]
    rw [le_div_iff₀ hlogpos]
    simpa using (log_large hℓ)
  have hdiv : Real.log (ℓ : ℝ) / Real.log 2 ≤ 2 * Real.log (ℓ : ℝ) := log_div_le_two_log h1
  have hcast : ((Nat.log2 ℓ + 1 : ℕ) : ℝ) = (Nat.log2 ℓ : ℝ) + 1 := by norm_num
  have hsum : (Nat.log2 ℓ : ℝ) + 1 ≤ 2 * (Real.log (ℓ : ℝ) / Real.log 2) := by nlinarith
  have hdiv2 : 2 * (Real.log (ℓ : ℝ) / Real.log 2) ≤ 4 * Real.log (ℓ : ℝ) := by nlinarith
  nlinarith

/--
FKNP "Theorem MT" (measure form):  a spread probability weight forces a Bernoulli set of
probability `p = MTK·q·log(l 𝓕)` to lie in `𝓕` with probability at least `3/4`.
-/
theorem spread_hit (𝓕 : Set (Set X)) (h𝓕 : IsUpperSet 𝓕) (hl : 2 ≤ l 𝓕)
    (q : ℝ) (hq0 : 0 < q) (ν : Set X → ℝ)
    (hν0 : ∀ S : Set X, 0 ≤ ν S)
    (hν1 : (∑ S : Set X, ν S) = 1)
    (hνF : ∀ S : Set X, ν S ≠ 0 → S ∈ 𝓕)
    (hνℓ : ∀ S : Set X, ν S ≠ 0 → S.ncard ≤ l 𝓕)
    (hspread : WeightSpread (2 * q) ν)
    {pstar : I} (hpstar_le : (pstar : ℝ) ≤ 1)
    (hpval : (pstar : ℝ) = MTK * q * Real.log (l 𝓕)) :
    (3 / 4 : ℝ) ≤ mu pstar 𝓕 := by
  classical
  let q0 : ℝ := 2 * q
  have hq00 : 0 < q0 := by dsimp [q0]; linarith
  have hlog2ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hg : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    norm_num at hg
    linarith
  have hlogℓ : Real.log 2 ≤ Real.log (l 𝓕 : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hl)
  have hlogℓ12 : (1 / 2 : ℝ) ≤ Real.log (l 𝓕 : ℝ) := by nlinarith
  have hq01 : q0 ≤ 1 := by
    have hp1 : (2^30 : ℝ) * q * Real.log (l 𝓕 : ℝ) ≤ 1 := by
      rw [hpval] at hpstar_le
      simpa [MTK] using hpstar_le
    have hb : (2^29 : ℝ) * q ≤ 1 := by
      have hpos30 : 0 ≤ (2^30 : ℝ) * q := by positivity
      have hm := mul_le_mul_of_nonneg_left hlogℓ12 hpos30
      -- hm : (2^30 * q) * (1/2) ≤ (2^30 * q) * log(l)
      have hcalc : (2^29 : ℝ) * q ≤ (2^30 : ℝ) * q * Real.log (l 𝓕 : ℝ) := by nlinarith
      nlinarith
    dsimp [q0]
    nlinarith
  have hpval' : (pstar : ℝ) = (2^29 : ℝ) * q0 * Real.log (l 𝓕 : ℝ) := by
    rw [hpval]
    dsimp [q0, MTK]
    ring_nf
  let L : ℕ := 1024
  have hL8 : (8 : ℕ) ≤ L := by norm_num [L]
  let H : Set (Set X) := wSupp ν
  have hB : Bounded H (l 𝓕) := by
    intro S hS
    exact hνℓ S (by simpa [H, wSupp] using hS)
  have hc : 1 ≤ ccost q0 H := by
    dsimp [H]
    exact one_le_ccost_of_supp q0 ν hν0 hν1
      (by intro T; dsimp [q0]; exact hspread T) hq00.le
  have hpv := PVIterP.pvHit (X := X) (H := H) (ℓ := l 𝓕) hB (by omega : 1 ≤ l 𝓕)
      (q0 := q0) hq00 hq01 hc (L := L) hL8
  have hp3 : (3 / 4 : ℝ) ≤ mu (pD q0 hq00.le hq01 L (Nat.log2 (l 𝓕) + 1)) (Up H) := by
    simpa using hpv
  have hle1 : (pD q0 hq00.le hq01 L (Nat.log2 (l 𝓕) + 1) : I).1 ≤ (pstar : ℝ) := by
    let d : ℕ := Nat.log2 (l 𝓕) + 1
    have hd4 : (d : ℝ) ≤ 4 * Real.log (l 𝓕 : ℝ) := by
      simpa [d] using (log2_succ_le_four_log hl)
    have hLc : (L : ℝ) = 1024 := by norm_num [L]
    have hd4L : (d : ℝ) * (L : ℝ) ≤ (2^29 : ℝ) * Real.log (l 𝓕 : ℝ) := by
      calc
        (d : ℝ) * (L : ℝ) ≤ (4 * Real.log (l 𝓕 : ℝ)) * (L : ℝ) :=
          mul_le_mul_of_nonneg_right hd4 (by positivity)
        _ = (4 * Real.log (l 𝓕 : ℝ)) * (1024 : ℝ) := by rw [hLc]
        _ = (4096 : ℝ) * Real.log (l 𝓕 : ℝ) := by ring_nf
        _ ≤ (2^29 : ℝ) * Real.log (l 𝓕 : ℝ) := by
          have h4096 : (4096 : ℝ) ≤ (2^29 : ℝ) := by norm_num
          have hlg0 : 0 ≤ Real.log (l 𝓕 : ℝ) := by linarith
          exact mul_le_mul_of_nonneg_right h4096 hlg0
    have hpdL : (pD q0 hq00.le hq01 L d : I).1 ≤ (d : ℝ) * (L : ℝ) * q0 := by
      have hb := bernoulli_bound (x := q0) hq00.le hq01 (d * L)
      have hcast : (((d * L : ℕ) : ℝ) * q0) = (d : ℝ) * (L : ℝ) * q0 := by
        rw [Nat.cast_mul]
      calc
        (pD q0 hq00.le hq01 L d : I).1 = 1 - (1 - q0) ^ (d * L) := by rfl
        _ ≤ ((d * L : ℕ) : ℝ) * q0 := hb
        _ = (d : ℝ) * (L : ℝ) * q0 := hcast
    have hbudget : (d : ℝ) * (L : ℝ) * q0 ≤ (pstar : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right hd4L hq00.le
      calc
        (d : ℝ) * (L : ℝ) * q0 ≤ ((2^29 : ℝ) * Real.log (l 𝓕 : ℝ)) * q0 := hm
        _ = (2^29 : ℝ) * q0 * Real.log (l 𝓕 : ℝ) := by ring
        _ = (pstar : ℝ) := hpval'.symm
    calc
      (pD q0 hq00.le hq01 L (Nat.log2 (l 𝓕) + 1) : I).1
          = (pD q0 hq00.le hq01 L d : I).1 := by rfl
      _ ≤ (d : ℝ) * (L : ℝ) * q0 := hpdL
      _ ≤ (pstar : ℝ) := hbudget
  have hUp : IsUpperSet (Up H) := Up_upper H
  have hmon : mu (pD q0 hq00.le hq01 L (Nat.log2 (l 𝓕) + 1)) (Up H)
      ≤ mu pstar (Up H) := by
    apply mu_mono_p hUp
    exact hle1
  have hmain3 : (3 / 4 : ℝ) ≤ mu pstar (Up H) := le_trans hp3 hmon
  have hUH : Up H ⊆ 𝓕 := by
    intro Y hY
    rcases hY with ⟨S, hS, hSY⟩
    have hSF : S ∈ 𝓕 := hνF S (by simpa [H, wSupp] using hS)
    exact h𝓕 hSY hSF
  have hf : mu pstar (Up H) ≤ mu pstar 𝓕 := mu_mono_family pstar hUH
  exact le_trans hmain3 hf