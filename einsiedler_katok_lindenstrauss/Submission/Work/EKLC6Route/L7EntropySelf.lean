import Mathlib
import Submission.Work.EKLC6Route.L7Aux
import Submission.Work.EKLComp.negMulLog_sum_le_card_mul_log
import Submission.Work.EKLComp.mul_log_inv_le_index

/-!
# `Work.EKLC6Route.L7EntropySelf` — the entropy bookkeeping of `L7` (independent proof)

The abstract entropy bound needed by `Work.EKLC6Route.tsum_negMulLog_ne_top`: pieces `D i J c`
with measurable envelopes `E i J c`, level marginals controlled by `q` (Kac) and depth marginals
decaying like `jIdx J`, have finite Shannon entropy.

The proof is a two-stage Shannon bound: at fixed `(i,J)` the `γ`-sum is bounded by the Shannon
entropy of the at most `N i` cells, and the resulting expression is then summed over `i` and `J`
using the two summability inputs `hkac` (weighted by `i`) and `hdecay` (weighted by `jIdx J`),
with the combined index `i + jIdx J` controlling the error term.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Work.EKLC6Route

noncomputable section

theorem tsum_negMulLog_cellDepth_self
    {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsProbabilityMeasure μ] {γ : Type*} [Countable γ]
    (E : ℕ → Option ℕ → γ → Set X) (hEmeas : ∀ i J c, MeasurableSet (E i J c))
    (hEdisj : ∀ i J c i' J' c', (i, J, c) ≠ (i', J', c') → Disjoint (E i J c) (E i' J' c'))
    (q : ℕ → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (hlevel : ∀ i, (∑' J : Option ℕ, ∑' c : γ, μ (E i J c)) ≤ ENNReal.ofReal (q i))
    (hqsum : (∑' i : ℕ, ENNReal.ofReal (q i)) ≤ 2)
    (hkac : (∑' i : ℕ, ENNReal.ofReal ((i : ℝ) * q i)) ≤ 1)
    (e : Option ℕ → ℝ) (he0 : ∀ J, 0 ≤ e J)
    (hdepth : ∀ J, (∑' i : ℕ, ∑' c : γ, μ (E i J c)) ≤ ENNReal.ofReal (e J))
    (hdecay : (∑' J : Option ℕ, ENNReal.ofReal ((jIdx J : ℝ) * e J)) ≤ 4)
    (D : ℕ → Option ℕ → γ → Set X) (hDE : ∀ i J c, D i J c ⊆ E i J c)
    (C : ℕ → Finset γ) (hCne : ∀ i, (C i).Nonempty)
    (hCemp : ∀ i J c, c ∉ C i → D i J c = ∅)
    (N : ℕ → ℕ) (hCcard : ∀ i, (C i).card ≤ N i) (hN1 : ∀ i, 1 ≤ N i)
    (c₀ κ : ℝ) (hc₀ : 0 ≤ c₀) (hκ : 0 ≤ κ)
    (hNbd : ∀ i, (N i : ℝ) ≤ c₀ * Real.exp (κ * i)) :
    (∑' p : ℕ × (Option ℕ × γ),
      ENNReal.ofReal (Real.negMulLog ((μ (D p.1 p.2.1 p.2.2)).toReal))) ≠ ⊤ := by
  classical
  have hmass1 : ∀ s : Set X, (μ s).toReal ≤ 1 := fun s =>
    calc (μ s).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top
            (calc μ s ≤ μ Set.univ := measure_mono (Set.subset_univ s)
              _ = 1 := measure_univ)
      _ = 1 := by simp
  -- ## 1. The masses of the finite cell families
  have hSq : ∀ i J, (∑ c ∈ C i, (μ (D i J c)).toReal) ≤ q i := by
    intro i J
    calc (∑ c ∈ C i, (μ (D i J c)).toReal)
        = ((∑ c ∈ C i, μ (D i J c)) : ℝ≥0∞).toReal :=
          (ENNReal.toReal_sum fun c _ => measure_ne_top μ _).symm
      _ ≤ ((∑' J' : Option ℕ, ∑' c : γ, μ (E i J' c)) : ℝ≥0∞).toReal := by
          refine ENNReal.toReal_mono ?_ ?_
          · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hlevel i)
          · calc (∑ c ∈ C i, μ (D i J c)) ≤ ∑ c ∈ C i, μ (E i J c) :=
                  Finset.sum_le_sum fun c _ => measure_mono (hDE i J c)
              _ ≤ ∑' c : γ, μ (E i J c) := ENNReal.sum_le_tsum _
              _ ≤ ∑' J' : Option ℕ, ∑' c : γ, μ (E i J' c) := ENNReal.le_tsum (f := fun J' : Option ℕ => ∑' c : γ, μ (E i J' c)) J
      _ ≤ q i := by
          rw [← ENNReal.toReal_ofReal (hq0 i)]
          exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (hlevel i)
  have hSe : ∀ i J, (∑ c ∈ C i, (μ (D i J c)).toReal) ≤ e J := by
    intro i J
    calc (∑ c ∈ C i, (μ (D i J c)).toReal)
        = ((∑ c ∈ C i, μ (D i J c)) : ℝ≥0∞).toReal :=
          (ENNReal.toReal_sum fun c _ => measure_ne_top μ _).symm
      _ ≤ ((∑' i' : ℕ, ∑' c : γ, μ (E i' J c)) : ℝ≥0∞).toReal := by
          refine ENNReal.toReal_mono ?_ ?_
          · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdepth J)
          · calc (∑ c ∈ C i, μ (D i J c)) ≤ ∑ c ∈ C i, μ (E i J c) :=
                  Finset.sum_le_sum fun c _ => measure_mono (hDE i J c)
              _ ≤ ∑' c : γ, μ (E i J c) := ENNReal.sum_le_tsum _
              _ ≤ ∑' i' : ℕ, ∑' c : γ, μ (E i' J c) := ENNReal.le_tsum (f := fun i' : ℕ => ∑' c : γ, μ (E i' J c)) i
      _ ≤ e J := by
          rw [← ENNReal.toReal_ofReal (he0 J)]
          exact ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdepth J)
  have hS1 : ∀ i J, (∑ c ∈ C i, (μ (D i J c)).toReal) ≤ 1 := by
    intro i J
    have hdisj : (↑(C i) : Set γ).PairwiseDisjoint (fun c => E i J c) := by
      intro c _ c' _ hcc'
      exact hEdisj i J c i J c' (by
        intro h
        exact hcc' ((Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2))
    calc (∑ c ∈ C i, (μ (D i J c)).toReal)
        = ((∑ c ∈ C i, μ (D i J c)) : ℝ≥0∞).toReal :=
          (ENNReal.toReal_sum fun c _ => measure_ne_top μ _).symm
      _ ≤ ((∑ c ∈ C i, μ (E i J c)) : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun c _ => measure_ne_top μ _)
            (Finset.sum_le_sum fun c _ => measure_mono (hDE i J c))
      _ = (μ (⋃ c ∈ C i, E i J c)).toReal := by
          rw [measure_biUnion_finset hdisj fun c _ => hEmeas i J c]
      _ ≤ (μ Set.univ).toReal :=
          ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.subset_univ _))
      _ = 1 := by simp
  -- ## 2. The per-level-and-depth Shannon bound
  have hA : ∀ i J, (∑' c : γ, ENNReal.ofReal (Real.negMulLog ((μ (D i J c)).toReal)))
      ≤ ENNReal.ofReal ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i)
          + (((i : ℝ) + (jIdx J : ℝ)) * (∑ c ∈ C i, (μ (D i J c)).toReal)
            + (((i : ℝ) + (jIdx J : ℝ)) + 1) * Real.exp (-((i : ℝ) + (jIdx J : ℝ))))) := by
    intro i J
    set S : ℝ := ∑ c ∈ C i, (μ (D i J c)).toReal with hS
    set idx : ℝ := (i : ℝ) + (jIdx J : ℝ) with hidx
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun c _ => ENNReal.toReal_nonneg
    have hSle1 : S ≤ 1 := hS1 i J
    have hidx0 : 0 ≤ idx := by
      rw [hidx]; positivity
    have hNpos : (0 : ℝ) < N i := by exact_mod_cast hN1 i
    have hlogN0 : 0 ≤ Real.log (N i) := Real.log_nonneg (by exact_mod_cast hN1 i)
    have hzero : ∀ c : γ, c ∉ C i →
        ENNReal.ofReal (Real.negMulLog ((μ (D i J c)).toReal)) = 0 := by
      intro c hc
      rw [hCemp i J c hc, measure_empty, ENNReal.toReal_zero, Real.negMulLog_zero,
        ENNReal.ofReal_zero]
    rw [tsum_eq_sum hzero,
      ← ENNReal.ofReal_sum_of_nonneg (fun c _ => Real.negMulLog_nonneg ENNReal.toReal_nonneg
        (hmass1 _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsh := Work.EKLComp.negMulLog_sum_le_card_mul_log (C i) (hCne i)
      (fun c => (μ (D i J c)).toReal) (fun c _ => ENNReal.toReal_nonneg)
    refine le_trans hsh ?_
    rcases eq_or_lt_of_le hS0 with hS0' | hSpos
    · -- S = 0: the left side is `0` and the right side is nonnegative
      have hz : (∑ c ∈ C i, (μ (D i J c)).toReal) = 0 := by rw [← hS]; exact hS0'.symm
      rw [hz]
      simp only [zero_mul, add_zero, zero_add]
      positivity
    · -- S > 0
      have hcardpos : 0 < ((C i).card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr (hCne i)
      have hlog_le : Real.log (((C i).card : ℝ) / S) ≤ Real.log ((N i : ℝ) / S) := by
        refine Real.log_le_log (div_pos hcardpos hSpos) ?_
        exact div_le_div_of_nonneg_right (by exact_mod_cast hCcard i) hS0
      have hstep1 : (∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (((C i).card : ℝ) / S)
          ≤ S * Real.log ((N i : ℝ) / S) := by
        rw [← hS]
        exact mul_le_mul_of_nonneg_left hlog_le hS0
      refine le_trans hstep1 ?_
      have hsplit : Real.log ((N i : ℝ) / S) = Real.log (N i) + Real.log (1 / S) := by
        rw [Real.log_div (ne_of_gt hNpos) (ne_of_gt hSpos), Real.log_div one_ne_zero
          (ne_of_gt hSpos), Real.log_one]
        ring
      have hη : S * Real.log (1 / S) = Real.negMulLog S := by
        rw [Real.negMulLog_def, one_div, Real.log_inv]; ring
      have herr := Work.EKLComp.mul_log_inv_le_index S hS0 hSle1 (i + jIdx J)
      have herr' : S * Real.log (1 / S) ≤ idx * S + (idx + 1) * Real.exp (-idx) := by
        have h1 : ((i + jIdx J : ℕ) : ℝ) = idx := by
          rw [hidx]; push_cast; ring
        rw [h1] at herr
        calc S * Real.log (1 / S) ≤ idx * S + idx * Real.exp (-idx) + Real.exp (-idx) := herr
          _ = idx * S + (idx + 1) * Real.exp (-idx) := by ring
      have hmul : S * Real.log ((N i : ℝ) / S) = S * Real.log (N i) + S * Real.log (1 / S) := by
        rw [hsplit]; ring
      rw [hmul]
      linarith [herr', hlogN0, hS0]
  -- ## 3. Assembly: reduce the triple sum to the iterated sum of the per-(i,J) bounds
  have hB : (∑' p : ℕ × (Option ℕ × γ),
        ENNReal.ofReal (Real.negMulLog ((μ (D p.1 p.2.1 p.2.2)).toReal)))
      ≤ ∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
          ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i)
            + (((i : ℝ) + (jIdx J : ℝ)) * (∑ c ∈ C i, (μ (D i J c)).toReal)
              + (((i : ℝ) + (jIdx J : ℝ)) + 1) * Real.exp (-((i : ℝ) + (jIdx J : ℝ))))) := by
    rw [ENNReal.tsum_prod']
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [ENNReal.tsum_prod']
    exact ENNReal.tsum_le_tsum fun J => hA i J
  -- ## 4. The three terms of the per-level bound
  have one_le_c₀ : 1 ≤ c₀ := by
    have h := hNbd 0
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one] at h
    have h1 : (1 : ℝ) ≤ (N 0 : ℝ) := by exact_mod_cast hN1 0
    linarith
  have hlogc₀ : 0 ≤ Real.log c₀ := Real.log_nonneg one_le_c₀
  have hlogN : ∀ i, Real.log (N i) ≤ Real.log c₀ + κ * (i : ℝ) := by
    intro i
    have hc0pos : 0 < c₀ := lt_of_lt_of_le one_pos one_le_c₀
    calc Real.log (N i) ≤ Real.log (c₀ * Real.exp (κ * (i : ℝ))) :=
          Real.log_le_log (by exact_mod_cast hN1 i) (hNbd i)
      _ = Real.log c₀ + κ * (i : ℝ) := by
          rw [Real.log_mul (ne_of_gt hc0pos) (Real.exp_ne_zero _), Real.log_exp]
  -- (C1) the `log (N i)` term
  have hC1 : (∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
        ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i)))
      ≤ 2 * ENNReal.ofReal (Real.log c₀) + ENNReal.ofReal κ := by
    have hstep : ∀ i : ℕ, (∑' J : Option ℕ, ENNReal.ofReal
          ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i)))
        ≤ ENNReal.ofReal (q i * Real.log (N i)) := by
      intro i
      have hsumJ : (∑' J : Option ℕ, ENNReal.ofReal
            ((∑ c ∈ C i, (μ (D i J c)).toReal))) ≤ ENNReal.ofReal (q i) := by
        refine le_trans (ENNReal.tsum_le_tsum fun J => ?_) (hlevel i)
        calc ENNReal.ofReal ((∑ c ∈ C i, (μ (D i J c)).toReal))
            = ENNReal.ofReal (((∑ c ∈ C i, μ (D i J c)) : ℝ≥0∞).toReal) := by
              rw [ENNReal.toReal_sum fun c _ => measure_ne_top μ _]
          _ ≤ ((∑ c ∈ C i, μ (D i J c)) : ℝ≥0∞) := ENNReal.ofReal_toReal_le
          _ ≤ ∑' c : γ, μ (E i J c) :=
              le_trans (Finset.sum_le_sum fun c _ => measure_mono (hDE i J c))
                (ENNReal.sum_le_tsum _)
      calc (∑' J : Option ℕ, ENNReal.ofReal
              ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i)))
          = ENNReal.ofReal (Real.log (N i)) * (∑' J : Option ℕ, ENNReal.ofReal
              ((∑ c ∈ C i, (μ (D i J c)).toReal))) := by
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun J => ?_
            rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun c _ => ENNReal.toReal_nonneg)]
            ring
        _ ≤ ENNReal.ofReal (Real.log (N i)) * ENNReal.ofReal (q i) :=
            mul_le_mul_right hsumJ _
        _ = ENNReal.ofReal (q i * Real.log (N i)) := by
            rw [ENNReal.ofReal_mul (hq0 i)]; ring
    have hpt : ∀ i : ℕ, ENNReal.ofReal (q i * Real.log (N i))
        ≤ ENNReal.ofReal (Real.log c₀ * q i) + ENNReal.ofReal (κ * ((i : ℝ) * q i)) := by
      intro i
      rw [← ENNReal.ofReal_add (mul_nonneg hlogc₀ (hq0 i))
        (mul_nonneg hκ (mul_nonneg (Nat.cast_nonneg i) (hq0 i)))]
      refine ENNReal.ofReal_le_ofReal ?_
      have h := hlogN i
      nlinarith [hq0 i]
    calc (∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
            ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i)))
        ≤ ∑' i : ℕ, ENNReal.ofReal (q i * Real.log (N i)) := ENNReal.tsum_le_tsum hstep
      _ ≤ ∑' i : ℕ, (ENNReal.ofReal (Real.log c₀ * q i)
            + ENNReal.ofReal (κ * ((i : ℝ) * q i))) := ENNReal.tsum_le_tsum hpt
      _ = (∑' i : ℕ, ENNReal.ofReal (Real.log c₀ * q i))
            + ∑' i : ℕ, ENNReal.ofReal (κ * ((i : ℝ) * q i)) := ENNReal.tsum_add
      _ = ENNReal.ofReal (Real.log c₀) * (∑' i : ℕ, ENNReal.ofReal (q i))
            + ENNReal.ofReal κ * (∑' i : ℕ, ENNReal.ofReal ((i : ℝ) * q i)) := by
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
          congr 1
          · exact tsum_congr fun i => ENNReal.ofReal_mul hlogc₀
          · exact tsum_congr fun i => ENNReal.ofReal_mul hκ
      _ ≤ ENNReal.ofReal (Real.log c₀) * 2 + ENNReal.ofReal κ * 1 :=
          add_le_add (mul_le_mul_right hqsum _) (mul_le_mul_right hkac _)
      _ = 2 * ENNReal.ofReal (Real.log c₀) + ENNReal.ofReal κ := by
          rw [mul_one, mul_comm]
  -- (C2) the `(i + jIdx J) * S` term
  have hC2 : (∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
        (((i : ℝ) + (jIdx J : ℝ)) * (∑ c ∈ C i, (μ (D i J c)).toReal))) ≤ 5 := by
    have hsplit : ∀ (i : ℕ) (J : Option ℕ),
        ENNReal.ofReal (((i : ℝ) + (jIdx J : ℝ)) * (∑ c ∈ C i, (μ (D i J c)).toReal))
          = ENNReal.ofReal ((i : ℝ) * (∑ c ∈ C i, (μ (D i J c)).toReal))
            + ENNReal.ofReal ((jIdx J : ℝ) * (∑ c ∈ C i, (μ (D i J c)).toReal)) := by
      intro i J
      rw [← ENNReal.ofReal_add
        (mul_nonneg (Nat.cast_nonneg i) (Finset.sum_nonneg fun c _ => ENNReal.toReal_nonneg))
        (mul_nonneg (jIdx_nonneg J) (Finset.sum_nonneg fun c _ => ENNReal.toReal_nonneg))]
      congr 1
      ring
    have hC2a : (∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
          ((i : ℝ) * (∑ c ∈ C i, (μ (D i J c)).toReal))) ≤ 1 := by
      have hstep : ∀ i : ℕ, (∑' J : Option ℕ, ENNReal.ofReal
            ((i : ℝ) * (∑ c ∈ C i, (μ (D i J c)).toReal)))
          ≤ ENNReal.ofReal ((i : ℝ) * q i) := by
        intro i
        calc (∑' J : Option ℕ, ENNReal.ofReal
                ((i : ℝ) * (∑ c ∈ C i, (μ (D i J c)).toReal)))
            = ENNReal.ofReal (i : ℝ) * (∑' J : Option ℕ, ENNReal.ofReal
                ((∑ c ∈ C i, (μ (D i J c)).toReal))) := by
              rw [← ENNReal.tsum_mul_left]
              exact tsum_congr fun J => by
                rw [ENNReal.ofReal_mul (Nat.cast_nonneg i)]
          _ ≤ ENNReal.ofReal (i : ℝ) * ENNReal.ofReal (q i) :=
              mul_le_mul_right (by
                refine le_trans (ENNReal.tsum_le_tsum fun J => ?_) (hlevel i)
                calc ENNReal.ofReal ((∑ c ∈ C i, (μ (D i J c)).toReal))
                    = ENNReal.ofReal (((∑ c ∈ C i, μ (D i J c)) : ℝ≥0∞).toReal) := by
                      rw [ENNReal.toReal_sum fun c _ => measure_ne_top μ _]
                  _ ≤ ((∑ c ∈ C i, μ (D i J c)) : ℝ≥0∞) := ENNReal.ofReal_toReal_le
                  _ ≤ ∑' c : γ, μ (E i J c) :=
                      le_trans (Finset.sum_le_sum fun c _ => measure_mono (hDE i J c))
                        (ENNReal.sum_le_tsum _)) (ENNReal.ofReal (i : ℝ))
          _ = ENNReal.ofReal ((i : ℝ) * q i) := by
              rw [ENNReal.ofReal_mul (Nat.cast_nonneg i)]
      exact le_trans (ENNReal.tsum_le_tsum hstep) hkac
    have hC2b : (∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
          ((jIdx J : ℝ) * (∑ c ∈ C i, (μ (D i J c)).toReal))) ≤ 4 := by
      rw [ENNReal.tsum_comm]
      have hstep : ∀ J : Option ℕ, (∑' i : ℕ, ENNReal.ofReal
            ((jIdx J : ℝ) * (∑ c ∈ C i, (μ (D i J c)).toReal)))
          ≤ ENNReal.ofReal ((jIdx J : ℝ) * e J) := by
        intro J
        calc (∑' i : ℕ, ENNReal.ofReal
                ((jIdx J : ℝ) * (∑ c ∈ C i, (μ (D i J c)).toReal)))
            = ENNReal.ofReal (jIdx J : ℝ) * (∑' i : ℕ, ENNReal.ofReal
                ((∑ c ∈ C i, (μ (D i J c)).toReal))) := by
              rw [← ENNReal.tsum_mul_left]
              exact tsum_congr fun i => by
                rw [ENNReal.ofReal_mul (jIdx_nonneg J)]
          _ ≤ ENNReal.ofReal (jIdx J : ℝ) * ENNReal.ofReal (e J) :=
              mul_le_mul_right (by
                refine le_trans (ENNReal.tsum_le_tsum fun i => ?_) (hdepth J)
                calc ENNReal.ofReal ((∑ c ∈ C i, (μ (D i J c)).toReal))
                    = ENNReal.ofReal (((∑ c ∈ C i, μ (D i J c)) : ℝ≥0∞).toReal) := by
                      rw [ENNReal.toReal_sum fun c _ => measure_ne_top μ _]
                  _ ≤ ((∑ c ∈ C i, μ (D i J c)) : ℝ≥0∞) := ENNReal.ofReal_toReal_le
                  _ ≤ ∑' c : γ, μ (E i J c) :=
                      le_trans (Finset.sum_le_sum fun c _ => measure_mono (hDE i J c))
                        (ENNReal.sum_le_tsum _)) (ENNReal.ofReal (jIdx J : ℝ))
          _ = ENNReal.ofReal ((jIdx J : ℝ) * e J) := by
              rw [ENNReal.ofReal_mul (jIdx_nonneg J)]
      exact le_trans (ENNReal.tsum_le_tsum hstep) hdecay
    calc (∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
            (((i : ℝ) + (jIdx J : ℝ)) * (∑ c ∈ C i, (μ (D i J c)).toReal)))
        = ∑' i : ℕ, ∑' J : Option ℕ, (ENNReal.ofReal
              ((i : ℝ) * (∑ c ∈ C i, (μ (D i J c)).toReal))
            + ENNReal.ofReal ((jIdx J : ℝ) * (∑ c ∈ C i, (μ (D i J c)).toReal))) :=
          tsum_congr fun i => tsum_congr fun J => hsplit i J
      _ = (∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
              ((i : ℝ) * (∑ c ∈ C i, (μ (D i J c)).toReal)))
            + ∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
              ((jIdx J : ℝ) * (∑ c ∈ C i, (μ (D i J c)).toReal)) := by
          rw [← ENNReal.tsum_add]
          exact tsum_congr fun i => ENNReal.tsum_add
      _ ≤ 1 + 4 := add_le_add hC2a hC2b
      _ = 5 := by norm_num
  -- (C3) the exponential error term
  have hsumm1 : Summable (fun i : ℕ => (i : ℝ) * Real.exp (-(i : ℝ))) := by
    have h := Real.summable_pow_mul_exp_neg_nat_mul 1 (show (0 : ℝ) < 1 by norm_num)
    simpa [pow_one, one_mul] using h
  have hsumm0 : Summable (fun i : ℕ => Real.exp (-(i : ℝ))) := Real.summable_exp_neg_nat
  have hmajB : Summable (fun j : ℕ =>
      2 * Real.exp (-1) * ((j : ℝ) * Real.exp (-(j : ℝ)) + Real.exp (-(j : ℝ)))) :=
    (hsumm1.add hsumm0).mul_left _
  have hsummB : Summable (fun j : ℕ =>
      (((j + 1 : ℕ) : ℝ) + 1) * Real.exp (-(((j + 1 : ℕ) : ℝ)))) := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hmajB
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hkey : ((j : ℝ) + 2) ≤ 2 * ((j : ℝ) + 1) := by linarith
    calc (((j + 1 : ℕ) : ℝ) + 1) * Real.exp (-(((j + 1 : ℕ) : ℝ)))
        = ((j : ℝ) + 2) * (Real.exp (-(j : ℝ)) * Real.exp (-1 : ℝ)) := by
          push_cast
          rw [show -((j : ℝ) + 1) = -(j : ℝ) + -1 by ring, Real.exp_add]
          ring
      _ ≤ (2 * ((j : ℝ) + 1)) * (Real.exp (-(j : ℝ)) * Real.exp (-1 : ℝ)) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = 2 * Real.exp (-1) * ((j : ℝ) * Real.exp (-(j : ℝ)) + Real.exp (-(j : ℝ))) := by ring
  have hsummA : Summable (fun i : ℕ => 2 * ((i : ℝ) + 1) * Real.exp (-(i : ℝ))) := by
    have h : Summable (fun i : ℕ =>
        2 * ((i : ℝ) * Real.exp (-(i : ℝ)) + Real.exp (-(i : ℝ)))) :=
      (hsumm1.add hsumm0).mul_left 2
    refine h.congr fun i => ?_
    ring
  have hC3 : (∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
        ((((i : ℝ) + (jIdx J : ℝ)) + 1) * Real.exp (-((i : ℝ) + (jIdx J : ℝ))))) < ⊤ := by
    have hpt : ∀ (i : ℕ) (J : Option ℕ),
        ENNReal.ofReal ((((i : ℝ) + (jIdx J : ℝ)) + 1)
            * Real.exp (-((i : ℝ) + (jIdx J : ℝ))))
          ≤ ENNReal.ofReal (2 * ((i : ℝ) + 1) * Real.exp (-(i : ℝ)))
            * ENNReal.ofReal (((jIdx J : ℝ) + 1) * Real.exp (-(jIdx J : ℝ))) := by
      intro i J
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      have hj : (0 : ℝ) ≤ (jIdx J : ℝ) := jIdx_nonneg J
      have hexp : Real.exp (-((i : ℝ) + (jIdx J : ℝ)))
          = Real.exp (-(i : ℝ)) * Real.exp (-(jIdx J : ℝ)) := by
        rw [show -((i : ℝ) + (jIdx J : ℝ)) = -(i : ℝ) + -(jIdx J : ℝ) by ring,
          Real.exp_add]
      rw [hexp]
      have hkey : ((i : ℝ) + (jIdx J : ℝ)) + 1 ≤ 2 * ((i : ℝ) + 1) * ((jIdx J : ℝ) + 1) := by
        nlinarith
      calc (((i : ℝ) + (jIdx J : ℝ)) + 1) * (Real.exp (-(i : ℝ)) * Real.exp (-(jIdx J : ℝ)))
          ≤ (2 * ((i : ℝ) + 1) * ((jIdx J : ℝ) + 1))
              * (Real.exp (-(i : ℝ)) * Real.exp (-(jIdx J : ℝ))) :=
            mul_le_mul_of_nonneg_right hkey (by positivity)
        _ = (2 * ((i : ℝ) + 1) * Real.exp (-(i : ℝ)))
              * (((jIdx J : ℝ) + 1) * Real.exp (-(jIdx J : ℝ))) := by ring
    calc (∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
            ((((i : ℝ) + (jIdx J : ℝ)) + 1) * Real.exp (-((i : ℝ) + (jIdx J : ℝ)))))
        ≤ ∑' i : ℕ, ∑' J : Option ℕ, (ENNReal.ofReal (2 * ((i : ℝ) + 1) * Real.exp (-(i : ℝ)))
            * ENNReal.ofReal (((jIdx J : ℝ) + 1) * Real.exp (-(jIdx J : ℝ)))) :=
          ENNReal.tsum_le_tsum fun i => ENNReal.tsum_le_tsum fun J => hpt i J
      _ = (∑' i : ℕ, ENNReal.ofReal (2 * ((i : ℝ) + 1) * Real.exp (-(i : ℝ))))
            * (∑' J : Option ℕ, ENNReal.ofReal
                (((jIdx J : ℝ) + 1) * Real.exp (-(jIdx J : ℝ)))) := by
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr fun i => ?_
          rw [ENNReal.tsum_mul_left]
      _ < ⊤ := by
          refine ENNReal.mul_lt_top ?_ ?_
          · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsummA]
            exact ENNReal.ofReal_lt_top
          · refine lt_of_le_of_lt (tsum_option_le (fun J : Option ℕ =>
              ENNReal.ofReal (((jIdx J : ℝ) + 1) * Real.exp (-(jIdx J : ℝ))))) ?_
            have heq : (∑' a : ℕ, ENNReal.ofReal
                  (((jIdx (some a) : ℝ) + 1) * Real.exp (-(jIdx (some a) : ℝ))))
                = ∑' a : ℕ, ENNReal.ofReal
                  ((((a + 1 : ℕ) : ℝ) + 1) * Real.exp (-(((a + 1 : ℕ) : ℝ)))) :=
              tsum_congr fun a => by simp [jIdx_some]
            rw [heq, ← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsummB]
            exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  -- ## 5. Assembly
  have hTsum : (∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
        ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i)
          + (((i : ℝ) + (jIdx J : ℝ)) * (∑ c ∈ C i, (μ (D i J c)).toReal)
            + (((i : ℝ) + (jIdx J : ℝ)) + 1) * Real.exp (-((i : ℝ) + (jIdx J : ℝ)))))) < ⊤ := by
    have hsplit : ∀ (i : ℕ) (J : Option ℕ),
        ENNReal.ofReal ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i)
          + (((i : ℝ) + (jIdx J : ℝ)) * (∑ c ∈ C i, (μ (D i J c)).toReal)
            + (((i : ℝ) + (jIdx J : ℝ)) + 1) * Real.exp (-((i : ℝ) + (jIdx J : ℝ)))))
          = ENNReal.ofReal ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i))
            + (ENNReal.ofReal (((i : ℝ) + (jIdx J : ℝ)) * (∑ c ∈ C i, (μ (D i J c)).toReal))
              + ENNReal.ofReal ((((i : ℝ) + (jIdx J : ℝ)) + 1)
                  * Real.exp (-((i : ℝ) + (jIdx J : ℝ))))) := by
      intro i J
      rw [← ENNReal.ofReal_add
        (mul_nonneg (by positivity) (Finset.sum_nonneg fun c _ => ENNReal.toReal_nonneg))
        (by positivity),
        ← ENNReal.ofReal_add
        (mul_nonneg (Finset.sum_nonneg fun c _ => ENNReal.toReal_nonneg)
          (Real.log_nonneg (by exact_mod_cast hN1 i)))
        (add_nonneg
          (mul_nonneg (by positivity) (Finset.sum_nonneg fun c _ => ENNReal.toReal_nonneg))
          (by positivity))]
    calc (∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
            ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i)
              + (((i : ℝ) + (jIdx J : ℝ)) * (∑ c ∈ C i, (μ (D i J c)).toReal)
                + (((i : ℝ) + (jIdx J : ℝ)) + 1)
                    * Real.exp (-((i : ℝ) + (jIdx J : ℝ))))))
        = ∑' i : ℕ, ∑' J : Option ℕ, (ENNReal.ofReal
              ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i))
            + (ENNReal.ofReal (((i : ℝ) + (jIdx J : ℝ))
                * (∑ c ∈ C i, (μ (D i J c)).toReal))
              + ENNReal.ofReal ((((i : ℝ) + (jIdx J : ℝ)) + 1)
                  * Real.exp (-((i : ℝ) + (jIdx J : ℝ)))))) :=
          tsum_congr fun i => tsum_congr fun J => hsplit i J
      _ = ∑' i : ℕ, ((∑' J : Option ℕ, ENNReal.ofReal
              ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i)))
            + ∑' J : Option ℕ, (ENNReal.ofReal (((i : ℝ) + (jIdx J : ℝ))
                * (∑ c ∈ C i, (μ (D i J c)).toReal))
              + ENNReal.ofReal ((((i : ℝ) + (jIdx J : ℝ)) + 1)
                  * Real.exp (-((i : ℝ) + (jIdx J : ℝ)))))) := by
          refine tsum_congr fun i => ?_
          rw [ENNReal.tsum_add]
      _ = ∑' i : ℕ, ((∑' J : Option ℕ, ENNReal.ofReal
              ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i)))
            + ((∑' J : Option ℕ, ENNReal.ofReal (((i : ℝ) + (jIdx J : ℝ))
                * (∑ c ∈ C i, (μ (D i J c)).toReal)))
              + ∑' J : Option ℕ, ENNReal.ofReal ((((i : ℝ) + (jIdx J : ℝ)) + 1)
                  * Real.exp (-((i : ℝ) + (jIdx J : ℝ)))))) := by
          refine tsum_congr fun i => ?_
          rw [ENNReal.tsum_add]
      _ = (∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
              ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i)))
            + ∑' i : ℕ, ((∑' J : Option ℕ, ENNReal.ofReal (((i : ℝ) + (jIdx J : ℝ))
                * (∑ c ∈ C i, (μ (D i J c)).toReal)))
              + ∑' J : Option ℕ, ENNReal.ofReal ((((i : ℝ) + (jIdx J : ℝ)) + 1)
                  * Real.exp (-((i : ℝ) + (jIdx J : ℝ))))) := by
          rw [ENNReal.tsum_add]
      _ = (∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal
              ((∑ c ∈ C i, (μ (D i J c)).toReal) * Real.log (N i)))
            + ((∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal (((i : ℝ) + (jIdx J : ℝ))
                * (∑ c ∈ C i, (μ (D i J c)).toReal)))
              + ∑' i : ℕ, ∑' J : Option ℕ, ENNReal.ofReal ((((i : ℝ) + (jIdx J : ℝ)) + 1)
                  * Real.exp (-((i : ℝ) + (jIdx J : ℝ))))) := by
          rw [ENNReal.tsum_add]
      _ < ⊤ := by
          refine ENNReal.add_lt_top.mpr ⟨?_, ENNReal.add_lt_top.mpr ⟨?_, ?_⟩⟩
          · exact lt_of_le_of_lt hC1 (by
              rw [ENNReal.add_lt_top]
              exact ⟨ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top,
                ENNReal.ofReal_lt_top⟩)
          · exact lt_of_le_of_lt hC2 (by norm_num)
          · exact hC3
  exact ne_of_lt (lt_of_le_of_lt hB hTsum)

end

end Work.EKLC6Route
