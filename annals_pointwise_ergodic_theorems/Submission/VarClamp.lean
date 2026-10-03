import ChallengeDeps
import Mathlib.Tactic
import Submission.Variational
import Submission.VarSums
import Submission.Port.Aesm

/-!
# Clamping the index set of the variational norm

The Calderón transference argument requires the variational estimate for the averages
`A T (a n) X P f g` restricted to an initial segment `n ≤ K` of the index set, so that the
scales `a n` stay bounded.  We record here the facts that make this possible:

* clamping the index set at `K` does not increase the variational norm
  (`variationalNorm_comp_min_le`);
* the variational norm of `b` is the supremum over `K` of the variational norms of the clamped
  sequences `n ↦ b (min n K)` (`variationalNorm_eq_iSup_comp_min`).

We also record the monotone-convergence form of `eLpNorm` that upgrades a uniform bound for the
clamped family to a bound for the supremum (`eLpNorm_iSup_le_of_le`).
-/

set_option maxHeartbeats 1600000

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {μ : Measure 𝓧}

/-- Raising the `Lᵖ` seminorm to the `p`-th power returns the integral of the `p`-th powers of
the pointwise norms. -/
lemma eLpNorm_rpow_toReal {ε : Type*} [ENorm ε] [TopologicalSpace ε] {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hptop : p ≠ ∞) (u : 𝓧 → ε) (hu : AEStronglyMeasurable u μ := by pw_aesm) :
    (eLpNorm u p μ) ^ p.toReal = ∫⁻ x, ‖u x‖ₑ ^ p.toReal ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hu]
  have hq : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp0, hptop⟩
  rw [one_div]
  exact ENNReal.rpow_inv_rpow hq _

/-! ## `rpow` and suprema -/

/-- For `q > 0`, the `q`-th power commutes with suprema in `ℝ≥0∞`. -/
lemma iSup_rpow_eq {ι : Type*} {q : ℝ} (hq : 0 < q) (f : ι → ℝ≥0∞) :
    (⨆ i, f i) ^ q = ⨆ i, (f i) ^ q := by
  have hle : (⨆ i, f i) ^ q ≤ ⨆ i, (f i) ^ q := by
    have hqinv : 0 ≤ q⁻¹ := inv_nonneg.mpr hq.le
    calc (⨆ i, f i) ^ q ≤ ((⨆ i, (f i) ^ q) ^ q⁻¹) ^ q := by
          refine ENNReal.rpow_le_rpow (iSup_le fun i => ?_) hq.le
          calc f i = ((f i) ^ q) ^ q⁻¹ := (ENNReal.rpow_rpow_inv hq.ne' _).symm
            _ ≤ (⨆ j, (f j) ^ q) ^ q⁻¹ :=
                ENNReal.rpow_le_rpow (le_iSup (fun j => (f j) ^ q) i) hqinv
      _ = ⨆ i, (f i) ^ q := ENNReal.rpow_inv_rpow hq.ne' _
  exact le_antisymm hle (iSup_le fun i => ENNReal.rpow_le_rpow (le_iSup f i) hq.le)

/-- For monotone sequences in `ℝ≥0∞`, the supremum of the sums is the sum of the suprema. -/
lemma iSup_add_monotone {a b : ℕ → ℝ≥0∞} (ha : Monotone a) (hb : Monotone b) :
    (⨆ n, a n + b n) = (⨆ n, a n) + (⨆ n, b n) := by
  have h2 : (⨆ n, a n) + (⨆ m, b m) = ⨆ n, ⨆ m, (a n + b m) := by
    rw [ENNReal.iSup_add]
    refine iSup_congr fun n => ?_
    rw [add_comm (a n), ENNReal.iSup_add]
    exact iSup_congr fun m => add_comm _ _
  refine le_antisymm (iSup_le fun n => add_le_add (le_iSup a n) (le_iSup b n)) ?_
  calc (⨆ n, a n) + (⨆ m, b m) = ⨆ n, ⨆ m, (a n + b m) := h2
    _ ≤ ⨆ n, (a n + b n) := iSup_le fun n => iSup_le fun m => by
        rcases le_total n m with h | h
        · exact le_trans (add_le_add_left (ha h) _) (le_iSup (fun k => a k + b k) m)
        · exact le_trans (add_le_add_right (hb h) _) (le_iSup (fun k => a k + b k) n)

/-! ## Clamping the index set -/

/-- Clamping the index map at `K` does not increase the variational part. -/
lemma varPart_comp_min_le (r : ℝ≥0) (b : ℕ → ℂ) (K : ℕ) :
    varPart r (fun n => b (min n K)) ≤ varPart r b := by
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  have hmono : Monotone fun i => min (N i) K := fun i j hij => min_le_min (hN hij) le_rfl
  refine le_iSup_of_le J (le_iSup_of_le (fun i => min (N i) K) (le_iSup_of_le hmono ?_))
  exact le_of_eq rfl

/-- Clamping the index set at `K` does not increase the variational norm. -/
lemma variationalNorm_comp_min_le (r : ℝ≥0) (b : ℕ → ℂ) (K : ℕ) :
    variationalNorm r (fun n => b (min n K)) ≤ variationalNorm r b := by
  rw [variationalNorm_eq_add, variationalNorm_eq_add]
  exact add_le_add (iSup_le fun n => le_iSup (fun m => ‖b m‖ₑ) (min n K))
    (varPart_comp_min_le r b K)

/-- Clamping is monotone in the clamp. -/
lemma varPart_comp_min_mono (r : ℝ≥0) (b : ℕ → ℂ) {K K' : ℕ} (hKK' : K ≤ K') :
    varPart r (fun n => b (min n K)) ≤ varPart r (fun n => b (min n K')) := by
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  have hmono : Monotone fun i => min (N i) K := fun i j hij => min_le_min (hN hij) le_rfl
  refine le_iSup_of_le J (le_iSup_of_le (fun i => min (N i) K) (le_iSup_of_le hmono ?_))
  have hfuneq : (fun i : Fin J => b (min (N (↑i + 1)) K) - b (min (N ↑i) K))
      = (fun i : Fin J => b (min (min (N (↑i + 1)) K) K') - b (min (min (N ↑i) K) K')) := by
    funext i
    show b (min (N (↑i + 1)) K) - b (min (N ↑i) K)
      = b (min (min (N (↑i + 1)) K) K') - b (min (min (N ↑i) K) K')
    rw [min_assoc, min_eq_left hKK', min_assoc, min_eq_left hKK']
  rw [hfuneq]

/-- The variational norm of the clamped sequence is monotone in `K`. -/
lemma variationalNorm_comp_min_mono (r : ℝ≥0) (b : ℕ → ℂ) {K K' : ℕ} (hKK' : K ≤ K') :
    variationalNorm r (fun n => b (min n K)) ≤ variationalNorm r (fun n => b (min n K')) := by
  have h1 : (fun n => b (min n K)) = (fun n => b (min (min n K) K')) := by
    funext n
    rw [min_assoc, min_eq_left hKK']
  rw [h1]
  simpa using variationalNorm_comp_min_le r (fun m => b (min m K')) K

/-- The supremum part of the variational norm is the supremum of its clamped versions. -/
lemma iSup_enorm_eq_iSup_comp_min (b : ℕ → ℂ) :
    (⨆ n, ‖b n‖ₑ) = ⨆ K, (⨆ n, ‖b (min n K)‖ₑ) := by
  refine le_antisymm (iSup_le fun n => ?_)
    (iSup_le fun K => iSup_le fun n => le_iSup (fun m => ‖b m‖ₑ) (min n K))
  refine le_trans ?_ (le_iSup (fun K => ⨆ m, ‖b (min m K)‖ₑ) n)
  simpa [min_self] using le_iSup (fun m => ‖b (min m n)‖ₑ) n

/-- The variational part is the supremum of its clamped versions. -/
lemma varPart_eq_iSup_comp_min (r : ℝ≥0) (b : ℕ → ℂ) :
    varPart r b = ⨆ K, varPart r (fun n => b (min n K)) := by
  refine le_antisymm ?_ (iSup_le fun K => varPart_comp_min_le r b K)
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  refine le_trans ?_ (le_iSup (fun K => varPart r (fun n => b (min n K))) (N J))
  have hfuneq : (fun i : Fin J => b (N (↑i + 1)) - b (N ↑i))
      = (fun i : Fin J => b (min (N (↑i + 1)) (N J)) - b (min (N ↑i) (N J))) := by
    funext i
    show b (N (↑i + 1)) - b (N ↑i) = b (min (N (↑i + 1)) (N J)) - b (min (N ↑i) (N J))
    rw [min_eq_left (hN (Nat.succ_le_of_lt i.isLt)),
      min_eq_left (hN (le_trans (Nat.le_succ ↑i) (Nat.succ_le_of_lt i.isLt)))]
  rw [hfuneq]
  exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))

/-- The variational norm of `b` is the supremum of the variational norms of its clamped
versions. -/
lemma variationalNorm_eq_iSup_comp_min (r : ℝ≥0) (b : ℕ → ℂ) :
    variationalNorm r b = ⨆ K, variationalNorm r (fun n => b (min n K)) := by
  refine le_antisymm ?_ (iSup_le fun K => variationalNorm_comp_min_le r b K)
  have hsup := iSup_enorm_eq_iSup_comp_min b
  have hvar := varPart_eq_iSup_comp_min r b
  rw [variationalNorm_eq_add, hsup, hvar]
  rw [← iSup_add_monotone
    (a := fun K => ⨆ n, ‖b (min n K)‖ₑ)
    (b := fun K => varPart r (fun n => b (min n K)))
    (fun i j hij => iSup_le fun n =>
      le_trans (le_of_eq (by rw [min_eq_left (le_trans (min_le_right n i) hij)]))
        (le_iSup (fun m => ‖b (min m j)‖ₑ) (min n i)))
    (fun i j hij => varPart_comp_min_mono r b hij)]
  exact iSup_le fun K =>
    le_trans (le_of_eq (variationalNorm_eq_add r (fun n => b (min n K))).symm)
      (le_iSup (fun K => variationalNorm r (fun n => b (min n K))) K)

/-- **Monotone convergence for `eLpNorm`.**  A uniform bound for a monotone family of
`ℝ≥0∞`-valued functions bounds the `Lᵖ` seminorm of its pointwise supremum. -/
lemma eLpNorm_iSup_le_of_le {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    {u : ℕ → 𝓧 → ℝ≥0∞} (hu : ∀ n, AEMeasurable (u n) μ)
    (hmono : ∀ x, Monotone fun n => u n x) {C : ℝ≥0∞} (hC : ∀ n, eLpNorm (u n) p μ ≤ C) :
    eLpNorm (fun x => ⨆ n, u n x) p μ ≤ C := by
  have hqpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hq : p.toReal ≠ 0 := hqpos.ne'
  have key : (eLpNorm (fun x => ⨆ n, u n x) p μ) ^ p.toReal ≤ C ^ p.toReal := by
    rw [eLpNorm_rpow_toReal hp0 hptop _ (AEMeasurable.iSup hu).aestronglyMeasurable]
    rw [show (∫⁻ x, ‖(⨆ n, u n x)‖ₑ ^ p.toReal ∂μ)
        = ∫⁻ x, (⨆ n, u n x) ^ p.toReal ∂μ from
      lintegral_congr fun x => by simp only [enorm_eq_self]]
    rw [show (∫⁻ x, (⨆ n, u n x) ^ p.toReal ∂μ)
        = ∫⁻ x, ⨆ n, (u n x) ^ p.toReal ∂μ from
      lintegral_congr fun x => iSup_rpow_eq hqpos (fun n => u n x)]
    rw [lintegral_iSup' (fun n => (hu n).pow_const _)
      (Filter.Eventually.of_forall fun x => fun i j hij =>
        ENNReal.rpow_le_rpow (hmono x hij) hqpos.le)]
    refine iSup_le fun n => ?_
    calc ∫⁻ x, (u n x) ^ p.toReal ∂μ = ∫⁻ x, ‖u n x‖ₑ ^ p.toReal ∂μ :=
          lintegral_congr fun x => by simp only [enorm_eq_self]
      _ = (eLpNorm (u n) p μ) ^ p.toReal := (eLpNorm_rpow_toReal hp0 hptop (u n) (hu n).aestronglyMeasurable).symm
      _ ≤ C ^ p.toReal := ENNReal.rpow_le_rpow (hC n) hqpos.le
  calc eLpNorm (fun x => ⨆ n, u n x) p μ
      = ((eLpNorm (fun x => ⨆ n, u n x) p μ) ^ p.toReal) ^ (p.toReal)⁻¹ :=
        (ENNReal.rpow_rpow_inv hq _).symm
    _ ≤ (C ^ p.toReal) ^ (p.toReal)⁻¹ := ENNReal.rpow_le_rpow key (by positivity)
    _ = C := ENNReal.rpow_rpow_inv hq _

end PointwiseErgodicTheorems
end Submission
