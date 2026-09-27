import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Hcond_le_Hcond_add
import Submission.Work.EKLC6Core.Hcond_cofinality
import Submission.Work.EKLC6Core.countableGenEntropy
import Submission.Work.EKLC6Core.CountablePartTrunc
import Submission.Work.EKLC6Core.Hcond_mono

/-!
# Pisa 7.50: geometric decay of part measures gives finite static conditional entropy

The static conditional entropy `HcondSig μ (σ (range P)) ⊥` of a countable partition `P` is finite
as soon as the part measures decay geometrically, `μ (P n) ≤ 1/(n+2)²`.

The proof has three independent ingredients, all established above the main theorem:

* `Hcond_bot_eq_Hfam` — for `⊥` the conditional expectation is the (constant) mean, so the
  conditional entropy of a finite partition against `⊥` is its Shannon entropy `Hfam`;
* `Hfam_truncPart_eq` / `Hfam_truncPart_le` — the Shannon entropy of the `l`-th truncation of `P`
  is `∑_{k<l} negMulLog (μ (P k)) + negMulLog (1 - μ (⋃_{k<l} P k))`, and this is bounded uniformly
  in `l` by `(∑' n, negMulLog (1/(n+2)²)) + 1`;
* `ofReal_Hcond_le_iSup_of_partSigma_iSup` (the cofinality lemma) — the supremum over *all* finite
  sub-partitions of `σ (range P)` is attained on the truncations.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Analytic auxiliary facts about `Real.negMulLog` -/

/-- `negMulLog (1/x²) ≤ 4/x^{3/2}` for `x ≥ 1`.  The logarithm grows slower than any positive
power, so `-log x ≤ 2 x^{1/2}` and the claim follows. -/
lemma negMulLog_inv_sq_le (x : ℝ) (hx : 1 ≤ x) :
    Real.negMulLog (1 / x^2) ≤ 4 / x^((3:ℝ)/2) := by
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
  have hxsq : 0 < x^2 := pow_pos hxpos 2
  have hlog : Real.log (1 / x^2) = -(2 * Real.log x) := by
    rw [one_div, Real.log_inv, Real.log_pow]; push_cast; ring
  have hneg : Real.negMulLog (1 / x^2) = 2 * Real.log x / x^2 := by
    simp only [Real.negMulLog_def, hlog]; ring
  rw [hneg]
  have hlt : Real.log x ≤ 2 * x^((1:ℝ)/2) := by
    have h := Real.log_le_rpow_div (le_of_lt hxpos) (show (0:ℝ) < 1/2 by norm_num)
    rwa [show x ^ ((1:ℝ)/2) / (1/2) = 2 * x^((1:ℝ)/2) by ring] at h
  rw [div_le_div_iff₀ hxsq (Real.rpow_pos_of_pos hxpos _)]
  calc 2 * Real.log x * x ^ ((3:ℝ)/2)
      ≤ 2 * (2 * x ^ ((1:ℝ)/2)) * x ^ ((3:ℝ)/2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hxpos) _); linarith
    _ = 4 * (x ^ ((1:ℝ)/2) * x ^ ((3:ℝ)/2)) := by ring
    _ = 4 * x ^ 2 := by rw [← Real.rpow_add hxpos]; norm_num
    _ = 4 * x^2 := by ring

/-- The sequence `negMulLog (1/(n+2)²) = 2 log(n+2)/(n+2)²` is summable. -/
lemma summable_negMulLog_inv_sq :
    Summable (fun n : ℕ => Real.negMulLog (1 / ((n:ℝ) + 2) ^ 2)) := by
  have hbase : Summable (fun n : ℕ => (1:ℝ) / (n : ℝ) ^ ((3:ℝ)/2)) := by
    rw [Real.summable_one_div_nat_rpow]; norm_num
  have hshift : Summable (fun n : ℕ => (1:ℝ) / (((n+2 : ℕ) : ℝ)) ^ ((3:ℝ)/2)) :=
    (summable_nat_add_iff 2).mpr hbase
  have hb : Summable (fun n : ℕ => (1:ℝ) / ((n:ℝ)+2) ^ ((3:ℝ)/2)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hshift
  have hg : Summable (fun n : ℕ => (4:ℝ) * ((1:ℝ) / ((n:ℝ)+2) ^ ((3:ℝ)/2))) :=
    Summable.mul_left (4:ℝ) hb
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hg
  · refine Real.negMulLog_nonneg (by positivity) ?_
    rw [one_div]
    exact inv_le_one_of_one_le₀ (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  · have hx1 : (1:ℝ) ≤ (n:ℝ) + 2 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith
    have h1 := negMulLog_inv_sq_le ((n:ℝ)+2) hx1
    calc Real.negMulLog (1 / ((n:ℝ) + 2) ^ 2)
        ≤ 4 / ((n:ℝ)+2) ^ ((3:ℝ)/2) := h1
      _ = 4 * (1 / ((n:ℝ)+2) ^ ((3:ℝ)/2)) := by rw [mul_one_div]

/-- `1/4 ≤ e⁻¹`, used to place `1/(n+2)²` in the increasing range of `negMulLog`. -/
lemma exp_neg_one_ge_quarter : (1/4 : ℝ) ≤ Real.exp (-1) := by
  have h1 : (1:ℝ)/4 ≤ 1 / Real.exp 1 :=
    one_div_le_one_div_of_le (Real.exp_pos 1)
      (le_of_lt (lt_trans Real.exp_one_lt_three (show (3:ℝ) < 4 by norm_num)))
  rw [show Real.exp (-1) = 1 / Real.exp 1 from by rw [Real.exp_neg, one_div]]
  exact h1

/-- `Real.negMulLog` is strictly increasing on `[0, e⁻¹]`. -/
lemma strictMonoOn_negMulLog :
    StrictMonoOn Real.negMulLog (Set.Icc 0 (Real.exp (-1))) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) Real.continuous_negMulLog.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  have hxpos : 0 < x := hx.1
  rw [Real.deriv_negMulLog (ne_of_gt hxpos)]
  have hlt : Real.log x < -1 := by
    rw [Real.log_lt_iff_lt_exp hxpos]; exact hx.2
  linarith

/-- `Real.negMulLog` is monotone on `[0, e⁻¹]`. -/
lemma monotoneOn_negMulLog :
    MonotoneOn Real.negMulLog (Set.Icc 0 (Real.exp (-1))) :=
  strictMonoOn_negMulLog.monotoneOn

/-! ## The conditional entropy against `⊥` is the Shannon entropy -/

/-- For the trivial σ-algebra `⊥` every conditional expectation is the (constant) mean, so the
conditional entropy `Hcond μ P ⊥` is the Shannon entropy `Hfam μ P.parts` of the partition. -/
lemma Hcond_bot_eq_Hfam {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (P : @FinPart X mX) :
    @Hcond X mX μ P (⊥ : MeasurableSpace X) = @Hfam X mX (Fin P.n) _ μ P.parts := by
  rw [Hcond_eq_sum_integral (mX := mX) (m := (⊥ : MeasurableSpace X)) (μ := μ) P]
  simp only [Hfam]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : μ[((@FinPart.parts X mX P i).indicator (fun _ => (1:ℝ))) | (⊥ : MeasurableSpace X)]
      = fun _ => (μ (@FinPart.parts X mX P i)).toReal := by
    rw [condExp_bot]
    funext x
    rw [integral_indicator_const (1:ℝ) (@FinPart.measurable X mX P i)]
    simp [Measure.real]
  rw [h1]
  simp [integral_const]

/-! ## The truncation of a countable partition -/

/-- The Shannon entropy of the `l`-th truncation splits into the parts `P 0, …, P (l-1)` and the
tail. -/
lemma Hfam_truncPart_eq {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (P : ℕ → Set X) (hPmeas : ∀ n : ℕ, MeasurableSet (P n))
    (hPdisj : ∀ m n : ℕ, m ≠ n → Disjoint (P m) (P n)) (l : ℕ) :
    Hfam μ (truncPart P hPmeas hPdisj l).parts
      = (∑ k : Fin l, Real.negMulLog ((μ (P k)).toReal))
        + Real.negMulLog ((μ ((⋃ j : Fin l, P (j : ℕ))ᶜ)).toReal) := by
  rw [Hfam]
  change (∑ i : Fin (l+1), Real.negMulLog ((μ ((truncPart P hPmeas hPdisj l).parts i)).toReal))
      = (∑ k : Fin l, Real.negMulLog ((μ (P k)).toReal))
        + Real.negMulLog ((μ ((⋃ j : Fin l, P (j : ℕ))ᶜ)).toReal)
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    have hk : (truncPart P hPmeas hPdisj l).parts (Fin.castSucc k) = P (k:ℕ) := by
      have hfin : (Fin.castSucc k : Fin (l+1)) = ⟨(k:ℕ), by show (k:ℕ) < l+1; omega⟩ :=
        Fin.ext rfl
      rw [hfin]
      exact truncPart_apply_lt (hPmeas := hPmeas) (hPdisj := hPdisj) k.isLt
    rw [hk]
  · rw [show (truncPart P hPmeas hPdisj l).parts (Fin.last l) = (⋃ j : Fin l, P (j:ℕ))ᶜ from
      truncPart_apply_last (hPmeas := hPmeas) (hPdisj := hPdisj) (Fin.last l) (by simp)]

/-- **The uniform entropy bound on truncations.**  If `μ (P n) ≤ 1/(n+2)²` then the Shannon entropy
of every truncation of `P` is at most `∑' n, negMulLog (1/(n+2)²) + 1 < ∞`. -/
lemma Hfam_truncPart_le {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (P : ℕ → Set X)
    (hPmeas : ∀ n : ℕ, MeasurableSet (P n))
    (hPdisj : ∀ m n : ℕ, m ≠ n → Disjoint (P m) (P n))
    (hdecay : ∀ n : ℕ, μ (P n) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 2) ^ 2)) (l : ℕ) :
    Hfam μ (truncPart P hPmeas hPdisj l).parts
      ≤ (∑' n : ℕ, Real.negMulLog (1 / ((n : ℝ) + 2) ^ 2)) + 1 := by
  rw [Hfam_truncPart_eq μ P hPmeas hPdisj l]
  have hsumm : Summable (fun n : ℕ => Real.negMulLog (1 / ((n : ℝ) + 2) ^ 2)) :=
    summable_negMulLog_inv_sq
  have hnonneg : ∀ n : ℕ, 0 ≤ Real.negMulLog (1 / ((n : ℝ) + 2) ^ 2) := fun n =>
    Real.negMulLog_nonneg (by positivity) (by
      rw [one_div]; exact inv_le_one_of_one_le₀ (by nlinarith [Nat.cast_nonneg (α := ℝ) n]))
  refine add_le_add ?_ ?_
  · have hterm : ∀ k : Fin l, Real.negMulLog ((μ (P k)).toReal)
        ≤ Real.negMulLog (1 / (((k:ℕ):ℝ) + 2) ^ 2) := by
      intro k
      have hle : (μ (P k)).toReal ≤ 1 / (((k:ℕ):ℝ) + 2) ^ 2 := by
        calc (μ (P k)).toReal
            ≤ (ENNReal.ofReal (1 / (((k:ℕ):ℝ) + 2) ^ 2)).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdecay (k:ℕ))
          _ = 1 / (((k:ℕ):ℝ) + 2) ^ 2 := ENNReal.toReal_ofReal (by positivity)
      have hexp : 1 / (((k:ℕ):ℝ) + 2) ^ 2 ≤ Real.exp (-1) :=
        le_trans (by
          apply one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 4)
          nlinarith [Nat.cast_nonneg (α := ℝ) (k:ℕ)]) exp_neg_one_ge_quarter
      exact monotoneOn_negMulLog ⟨ENNReal.toReal_nonneg, le_trans hle hexp⟩
        ⟨le_trans ENNReal.toReal_nonneg hle, hexp⟩ hle
    calc (∑ k : Fin l, Real.negMulLog ((μ (P k)).toReal))
        ≤ ∑ k : Fin l, Real.negMulLog (1 / (((k:ℕ):ℝ) + 2) ^ 2) :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = ∑ n ∈ Finset.range l, Real.negMulLog (1 / ((n:ℝ) + 2) ^ 2) :=
          Fin.sum_univ_eq_sum_range (fun n => Real.negMulLog (1 / ((n:ℝ) + 2) ^ 2)) l
      _ ≤ ∑' n : ℕ, Real.negMulLog (1 / ((n : ℝ) + 2) ^ 2) :=
          hsumm.sum_le_tsum (Finset.range l) (fun i _ => hnonneg i)
  · have hx : (0:ℝ) ≤ (μ ((⋃ j : Fin l, P (j:ℕ))ᶜ)).toReal := ENNReal.toReal_nonneg
    calc Real.negMulLog ((μ ((⋃ j : Fin l, P (j:ℕ))ᶜ)).toReal)
        ≤ 1 - (μ ((⋃ j : Fin l, P (j:ℕ))ᶜ)).toReal := Real.negMulLog_le_one_sub_self hx
      _ ≤ 1 := by linarith

/-! ## Main theorem: Pisa 7.50 -/

-- Pisa 7.50 in a *general, statable* form: geometric decay of the part measures of a countable
-- partition forces its static conditional entropy to be finite.
-- `HcondSig μ (σ (range P)) ⊥ = ⨆ (R : FinPart // σ R ≤ σ (range P)), ofReal (H_μ(R))`.
-- Intended use: the finite-entropy clause of `Work.EKLC6Core.Ch_GeoData` (the last open input of
-- component C6, see Submission/Work/EKLC6Core/ENTROPY_GEN_NOTE.md §6.4); the construction is free
-- to *choose* the enumeration of its cells (and to split large cells) so that the decay hypothesis
-- `μ (P n) ≤ 1/(n+2)^2` holds — the source's cell construction indeed produces measures of this
-- order (Pisa 7.50, using the covering counts of Pisa 7.46).
-- Proof sketch (see the review on record): for finite `R` with `σ R ≤ σ (range P)` every part of
-- `R` is a union of atoms (`P n` and the leftover `Z = X \ ⋃ P n`), so by disjointness plus
-- superadditivity of `f = Real.negMulLog` (the proved
-- `Work.EKLC6Core.Hcond_le_Hcond_add`, iterated) `Σ_i f (μ R_i) ≤ Σ_n f (μ (P n)) + f (μ Z)`;
-- `f` is increasing on `[0, 1/e]`, `f (1/(n+2)^2) = 2 log (n+2)/(n+2)^2` is summable, and
-- `f ≤ 1/e` on `[0,1]` handles the leftover; hence `HcondSig μ (σ (range P)) ⊥` is bounded by a
-- finite constant.  With `A' = ⊥` the conditional expectations are the constants `μ (R_i)`, so
-- `Hcond μ R ⊥ = Σ_i f (μ R_i)` (this is `Work.EKLC6Core.Hcond_eq_sum_integral` +
-- `condExp_const`).
theorem HcondSig_ne_top_of_measure_decay {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (P : ℕ → Set Work.EKLContract.X3)
    (hPmeas : ∀ n : ℕ, MeasurableSet (P n))
    (hPdisj : ∀ m n : ℕ, m ≠ n → Disjoint (P m) (P n))
    (hdecay : ∀ n : ℕ, μ (P n) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 2) ^ 2)) :
    @Work.EKLC6Core.HcondSig Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 μ
      (MeasurableSpace.generateFrom (Set.range P))
      (⊥ : MeasurableSpace Work.EKLContract.X3) ≠ ⊤ := by
  set C : ℝ := (∑' n : ℕ, Real.negMulLog (1 / ((n : ℝ) + 2) ^ 2)) + 1 with hC
  have hmono : Monotone fun l => @partSigma X3 instMeasurableSpaceX3 (truncPart P hPmeas hPdisj l) :=
    monotone_nat_of_le_succ (fun l => partSigma_truncPart_mono l)
  have hSm : ∀ l : ℕ,
      @partSigma X3 instMeasurableSpaceX3 (truncPart P hPmeas hPdisj l) ≤ instMeasurableSpaceX3 := by
    intro l
    rw [partSigma]
    exact MeasurableSpace.generateFrom_le (by
      rintro s ⟨i, rfl⟩
      exact (@FinPart.measurable X3 instMeasurableSpaceX3 (truncPart P hPmeas hPdisj l)) i)
  have hbound : ∀ R : {R : @FinPart X3 instMeasurableSpaceX3 //
      @partSigma X3 instMeasurableSpaceX3 R ≤ MeasurableSpace.generateFrom (Set.range P)},
      ENNReal.ofReal (@Hcond X3 instMeasurableSpaceX3 μ R.1 (⊥ : MeasurableSpace X3))
        ≤ ENNReal.ofReal C := by
    intro R
    have hR : @partSigma X3 instMeasurableSpaceX3 R.1
        ≤ ⨆ l, @partSigma X3 instMeasurableSpaceX3 (truncPart P hPmeas hPdisj l) := by
      rw [iSup_partSigma_truncPart]; exact R.2
    have h1 := ofReal_Hcond_le_iSup_of_partSigma_iSup (mX := instMeasurableSpaceX3) μ R.1
      (fun l => truncPart P hPmeas hPdisj l) hmono bot_le hSm hR
    refine le_trans h1 (iSup_le (fun l => ?_))
    have h2 : @Hcond X3 instMeasurableSpaceX3 μ (truncPart P hPmeas hPdisj l) (⊥ : MeasurableSpace X3)
        ≤ C := by
      rw [hC, Hcond_bot_eq_Hfam (mX := instMeasurableSpaceX3)]
      exact Hfam_truncPart_le (mX := instMeasurableSpaceX3) μ P hPmeas hPdisj hdecay l
    exact ENNReal.ofReal_le_ofReal h2
  have hle : @Work.EKLC6Core.HcondSig Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 μ
      (MeasurableSpace.generateFrom (Set.range P))
      (⊥ : MeasurableSpace Work.EKLContract.X3) ≤ ENNReal.ofReal C := by
    rw [HcondSig]
    exact iSup_le hbound
  exact ne_top_of_lt (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)

end Work.EKLC6Core

end
