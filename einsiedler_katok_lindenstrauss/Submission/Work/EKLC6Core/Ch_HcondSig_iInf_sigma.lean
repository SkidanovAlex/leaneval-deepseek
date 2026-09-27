import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Hcond_mono
import Submission.Work.EKLC6Core.HcondFam_partSigmaFam
import Submission.Work.EKLC6Core.BiGenAux
import Submission.Work.EKLC6Core.exists_Hcond_le_of_iSup_le_zero
import Submission.Work.EKLComp.Hcond_joinTwo
import Submission.Work.EKLComp.hPart_eq_ent_of_generating
import Submission.Work.EKLGen.tendsto_Hcond_iSup_univ
import Submission.Work.EKLGen.Hcond_iInf_of_tendsto
import Submission.Work.EKLGen.exists_partSigma_tendsto
import Submission.Work.EKLContract.Consistency

/-!
# `HcondSig` is continuous from above along an increasing sequence of σ-algebras

`HcondSig μ M C = ⨆_{P : partSigma P ≤ M} ofReal (Hcond μ P C)` is the conditional entropy of the
countably generated σ-algebra `M` given the conditioning σ-algebra `C`; it is the supremum of the
conditional entropies of the finite sub-partitions of `M` (the σ-algebra form of the entropy of
Pisa 7.6 / the C6 component of the EKL contract).

The main theorem `Ch_HcondSig_iInf_sigma` of this file is continuity from above in the
*conditioning* σ-algebra: for an increasing sequence `C : ℕ → MeasurableSpace X` of sub-σ-algebras
of the ambient `mX`,

  `(⨅ l, HcondSig μ M (C l)) = HcondSig μ M (⨆ l, C l)`,

provided `HcondSig μ M (C 0) < ⊤`.  Without the finiteness hypothesis the statement is false (the
dyadic filtration with `M = borel` on `[0,1]` gives `∞ = 0`).  The finiteness makes the quantities
`Hcond μ (F m) (C 0)` along a generating chain `F` of `M` uniformly bounded, which controls the
chain-rule error `Hcond μ P.1 C ≤ Hcond μ (F m) C + Hcond μ P.1 (partSigma (F m) ⊔ C)` uniformly
in the partition `P`.

The proof is the usual exchange of a `sup` over a refining chain with a `liminf`:

* `HcondSig μ M B = ⨆ n, ofReal (Hcond μ (F n) B)` for a refining chain generating `M`
  (`Ch_HcondSig_eq_iSup_chain`), obtained from the chain rule for `Hcond` (subadditivity of
  `-x log x` plus `condExp` additivity over a partition, `Ch_Hcond_le_Hcond_add`) and Lévy's
  theorem along the chain;
* the conditional entropies of `B` given `partSigma (F n) ∨ B` tend to `0`
  (`Ch_HcondSig_iInf_chain_sup_eq_zero`);
* so `⨅ l, HcondSig μ M (C l) ≤ ofReal (Hcond μ (F n) (⨆ l, C l)) + HcondSig μ M (partSigma (F n) ⊔ C 0)`
  for every `n`; taking the infimum over `n` and using Lévy in `l` finishes.
-/

open MeasureTheory Filter
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1000000

namespace Work.EKLC6Core

/-! ## 1. Subadditivity of `x ↦ -x log x` -/

/-- `-x log x` is subadditive on the region `x, y ≥ 0`, `x + y ≤ 1`. -/
theorem Ch_negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y ≤ 1) :
    Real.negMulLog (x + y) ≤ Real.negMulLog x + Real.negMulLog y := by
  have hxy : 0 ≤ x + y := add_nonneg hx hy
  rcases eq_or_lt_of_le hxy with hzero | hpos
  · have hx0 : x = 0 := le_antisymm (by linarith) hx
    have hy0 : y = 0 := le_antisymm (by linarith) hy
    rw [hx0, hy0, Real.negMulLog_zero]
    norm_num
  · have hne : x + y ≠ 0 := ne_of_gt hpos
    obtain ⟨p, hp⟩ : ∃ p : ℝ, p = x / (x + y) := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = y / (x + y) := ⟨_, rfl⟩
    have hpqq : p + q = 1 := by
      rw [hp, hq, ← add_div, div_eq_one_iff_eq hne]
    have hpnn : 0 ≤ Real.negMulLog p := by
      refine Real.negMulLog_nonneg ?_ ?_
      · rw [hp]; exact div_nonneg hx hxy
      · rw [hp]; exact (div_le_one hpos).mpr (by linarith)
    have hqnn : 0 ≤ Real.negMulLog q := by
      refine Real.negMulLog_nonneg ?_ ?_
      · rw [hq]; exact div_nonneg hy hxy
      · rw [hq]; exact (div_le_one hpos).mpr (by linarith)
    have h1 : (x + y) * p = x := by
      rw [hp, ← mul_div_assoc, mul_comm (x + y) x, mul_div_cancel_right₀ x hne]
    have h2 : (x + y) * q = y := by
      rw [hq, ← mul_div_assoc, mul_comm (x + y) y, mul_div_cancel_right₀ y hne]
    have hpx : Real.negMulLog x = p * Real.negMulLog (x + y) + (x + y) * Real.negMulLog p := by
      have hh := Real.negMulLog_mul (x + y) p
      rwa [h1] at hh
    have hpy : Real.negMulLog y = q * Real.negMulLog (x + y) + (x + y) * Real.negMulLog q := by
      have hh := Real.negMulLog_mul (x + y) q
      rwa [h2] at hh
    have hkey : 0 ≤ (x + y) * Real.negMulLog p + (x + y) * Real.negMulLog q :=
      add_nonneg (mul_nonneg hxy hpnn) (mul_nonneg hxy hqnn)
    have hsum : p * Real.negMulLog (x + y) + q * Real.negMulLog (x + y)
        = Real.negMulLog (x + y) := by
      rw [← add_mul, hpqq, one_mul]
    rw [hpx, hpy]
    linarith [hkey, hsum]

/-- Iterated subadditivity: if the `a i` are nonnegative and sum to at most `1`, then `-x log x`
of the total is at most the sum of the individual values. -/
theorem Ch_negMulLog_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (h1 : ∑ i ∈ s, a i ≤ 1) :
    Real.negMulLog (∑ i ∈ s, a i) ≤ ∑ i ∈ s, Real.negMulLog (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hi0 : 0 ≤ a i := ha i (Finset.mem_insert_self i s)
    have hs0 : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hsum0 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg hs0
    have h2 : a i + ∑ j ∈ s, a j ≤ 1 := by simpa [Finset.sum_insert hi] using h1
    have hs1 : ∑ j ∈ s, a j ≤ 1 := by linarith
    have hA := Ch_negMulLog_add_le hi0 hsum0 h2
    have hB := ih hs0 hs1
    linarith

/-! ## 2. `Hcond` is nonnegative -/

theorem Ch_Hcond_nonneg {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (P : @Work.EKLContract.FinPart X mX) :
    0 ≤ @Work.EKLContract.Hcond X mX μ P m := by
  by_cases hm : m ≤ mX
  · rw [Work.EKLC6Core.Hcond_eq_sum_integral (mX := mX) (m := m) (μ := μ) P]
    refine Finset.sum_nonneg fun i _ => integral_nonneg_of_ae ?_
    filter_upwards [Work.EKLC6Core.condExp_mem_Icc (mX := mX) (m := m) (μ := μ) hm
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (P.parts i) x).1)
      (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc (P.parts i) x).2)
      ((integrable_const (1:ℝ)).indicator (P.measurable i))] with x hx
    exact Real.negMulLog_nonneg hx.1 hx.2
  · rw [Work.EKLC6Core.Hcond_eq_zero_of_not_le (mX := mX) (m := m) (μ := μ) P hm]

/-! ## 3. The conditional expectation of an atom splits over a refining partition -/

/-- `condExp` of the indicator of an atom of `P` is, almost everywhere, the sum of the conditional
expectations of its pieces with respect to the partition `Q`. -/
theorem Ch_condExp_indicator_split {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (Q P : @Work.EKLContract.FinPart X mX) (i : Fin P.n) :
    MeasureTheory.condExp m μ ((P.parts i).indicator (fun _ => (1:ℝ)))
      =ᵐ[μ] fun x => ∑ j : Fin Q.n, MeasureTheory.condExp m μ
        ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x := by
  classical
  have hpt : ((P.parts i).indicator (fun _ => (1:ℝ)))
      = (∑ j ∈ (Finset.univ : Finset (Fin Q.n)),
          fun x => ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x) := by
    funext x
    rw [Finset.sum_apply]
    by_cases hx : x ∈ P.parts i
    · have hxcover : x ∈ ⋃ j, Q.parts j := by rw [Q.cover]; trivial
      obtain ⟨j₀, hj₀⟩ := Set.mem_iUnion.mp hxcover
      rw [Finset.sum_eq_single j₀]
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.mem_inter hj₀ hx)]
      · intro j _ hjne
        rw [Set.indicator_of_notMem]
        intro hmem
        exact Set.disjoint_left.mp (Q.disjoint hjne) hmem.1 hj₀
      · intro h; exact absurd (Finset.mem_univ j₀) h
    · rw [Set.indicator_of_notMem hx]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [Set.indicator_of_notMem]
      intro hmem; exact hx hmem.2
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin Q.n)),
      Integrable (fun x => ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x) μ :=
    fun j _ => (integrable_const (1:ℝ)).indicator ((Q.measurable j).inter (P.measurable i))
  have h := MeasureTheory.condExp_finsetSum (μ := μ) (s := Finset.univ)
    (f := fun j : Fin Q.n => fun x => ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x)
    hint m
  filter_upwards [h] with x hx
  rw [hpt]
  rw [hx]
  rw [Finset.sum_apply]

/-! ## 4. The chain-rule inequality for `Hcond` -/

/-- `H_μ(P | m) ≤ H_μ(Q | m) + H_μ(P | σ(Q) ∨ m)`: the entropy of `P` given `m` is at most the
entropy of `Q` given `m` plus the part of the information of `P` that only becomes visible after
passing to the join with `σ(Q)`. -/
theorem Ch_Hcond_le_Hcond_add {X : Type*} {m : MeasurableSpace X} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (P Q : @Work.EKLContract.FinPart X mX) :
    @Work.EKLContract.Hcond X mX μ P m
      ≤ @Work.EKLContract.Hcond X mX μ Q m
        + @Work.EKLContract.Hcond X mX μ P ((@Work.EKLContract.partSigma X mX Q) ⊔ m) := by
  classical
  by_cases hm : m ≤ mX
  swap
  · have hm1 : ¬ ((@Work.EKLContract.partSigma X mX Q) ⊔ m) ≤ mX :=
      fun h => hm (le_trans le_sup_right h)
    rw [Work.EKLC6Core.Hcond_eq_zero_of_not_le (mX := mX) (m := m) (μ := μ) P hm,
      Work.EKLC6Core.Hcond_eq_zero_of_not_le (mX := mX) (m := m) (μ := μ) Q hm,
      Work.EKLC6Core.Hcond_eq_zero_of_not_le (mX := mX)
        (m := (@Work.EKLContract.partSigma X mX Q) ⊔ m) (μ := μ) P hm1]
    norm_num
  · have hIntSet : ∀ s : Set X, MeasurableSet s → Integrable (fun x => Real.negMulLog
        (MeasureTheory.condExp m μ (s.indicator (fun _ => (1:ℝ))) x)) μ := by
      intro s hs
      exact Work.EKLC6Core.integrable_negMulLog_condExp (mX := mX) (m := m) (μ := μ)
        (f := s.indicator (fun _ => (1:ℝ)))
        (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc s x).1)
        (Filter.Eventually.of_forall fun x => (Work.EKLC6Core.indicator_mem_Icc s x).2)
        ((integrable_const (1:ℝ)).indicator hs)
    have hIntP : ∀ i : Fin P.n, Integrable (fun x => Real.negMulLog
        (MeasureTheory.condExp m μ ((P.parts i).indicator (fun _ => (1:ℝ))) x)) μ :=
      fun i => hIntSet _ (P.measurable i)
    have hIntQP : ∀ i : Fin P.n, ∀ j : Fin Q.n, Integrable (fun x => Real.negMulLog
        (MeasureTheory.condExp m μ ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x)) μ :=
      fun i j => hIntSet _ ((Q.measurable j).inter (P.measurable i))
    -- the pointwise inequality of the integrands, almost everywhere
    have hae : (fun x => ∑ i : Fin P.n, Real.negMulLog
          (MeasureTheory.condExp m μ ((P.parts i).indicator (fun _ => (1:ℝ))) x))
        ≤ᵐ[μ] (fun x => ∑ i : Fin P.n, ∑ j : Fin Q.n, Real.negMulLog
          (MeasureTheory.condExp m μ ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x)) := by
      have hsplit : ∀ i : Fin P.n, ∀ᵐ x ∂μ, Real.negMulLog
            (MeasureTheory.condExp m μ ((P.parts i).indicator (fun _ => (1:ℝ))) x)
          ≤ ∑ j : Fin Q.n, Real.negMulLog
            (MeasureTheory.condExp m μ ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x) := by
        intro i
        have heq := Ch_condExp_indicator_split (mX := mX) (m := m) (μ := μ) Q P i
        have hmem : ∀ j : Fin Q.n, ∀ᵐ x ∂μ,
            MeasureTheory.condExp m μ ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x
              ∈ Set.Icc (0:ℝ) 1 := fun j =>
          Work.EKLC6Core.condExp_mem_Icc (mX := mX) (m := m) (μ := μ) hm
            (Filter.Eventually.of_forall fun x =>
              (Work.EKLC6Core.indicator_mem_Icc (Q.parts j ∩ P.parts i) x).1)
            (Filter.Eventually.of_forall fun x =>
              (Work.EKLC6Core.indicator_mem_Icc (Q.parts j ∩ P.parts i) x).2)
            ((integrable_const (1:ℝ)).indicator ((Q.measurable j).inter (P.measurable i)))
        have hmemP : ∀ᵐ x ∂μ,
            MeasureTheory.condExp m μ ((P.parts i).indicator (fun _ => (1:ℝ))) x
              ∈ Set.Icc (0:ℝ) 1 :=
          Work.EKLC6Core.condExp_mem_Icc (mX := mX) (m := m) (μ := μ) hm
            (Filter.Eventually.of_forall fun x =>
              (Work.EKLC6Core.indicator_mem_Icc (P.parts i) x).1)
            (Filter.Eventually.of_forall fun x =>
              (Work.EKLC6Core.indicator_mem_Icc (P.parts i) x).2)
            ((integrable_const (1:ℝ)).indicator (P.measurable i))
        filter_upwards [heq, MeasureTheory.ae_all_iff.mpr hmem, hmemP] with x hxeq hxmem hxP
        rw [show MeasureTheory.condExp m μ ((P.parts i).indicator (fun _ => (1:ℝ))) x
              = ∑ j : Fin Q.n, MeasureTheory.condExp m μ
                  ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x from hxeq]
        refine Ch_negMulLog_sum_le Finset.univ
          (fun j : Fin Q.n => MeasureTheory.condExp m μ
            ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x)
          (fun j _ => (hxmem j).1) ?_
        have hsum1 : ∑ j : Fin Q.n, MeasureTheory.condExp m μ
              ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x ≤ 1 := by
          rw [← hxeq]; exact hxP.2
        simpa using hsum1
      refine (MeasureTheory.ae_all_iff.mpr hsplit).mono fun x hx => ?_
      exact Finset.sum_le_sum fun i _ => hx i
    -- the right-hand side, as an integral of the double sum
    have hR : (∫ x, ∑ i : Fin P.n, ∑ j : Fin Q.n, Real.negMulLog
          (MeasureTheory.condExp m μ ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x) ∂μ)
        = @Work.EKLContract.Hcond X mX μ Q m
          + @Work.EKLContract.Hcond X mX μ P ((@Work.EKLContract.partSigma X mX Q) ⊔ m) := by
      rw [show (@Work.EKLContract.partSigma X mX Q) ⊔ m
            = m ⊔ (@Work.EKLContract.partSigma X mX Q) from sup_comm _ _,
        ← Work.EKLComp.Hcond_joinTwo (mX := mX) μ Q P m,
        Work.EKLComp.Hcond_joinTwo_reindex (m := m) (μ := μ) Q P]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∑ i : Fin P.n, ∑ j : Fin Q.n, Real.negMulLog
            (MeasureTheory.condExp m μ ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x))
        = (∑ i : Fin Q.n, ∑ j : Fin P.n, Real.negMulLog
            (MeasureTheory.condExp m μ ((Q.parts i ∩ P.parts j).indicator (fun _ => (1:ℝ))) x))
      rw [Finset.sum_comm]
    calc @Work.EKLContract.Hcond X mX μ P m
        = ∑ i : Fin P.n, ∫ x, Real.negMulLog
            (MeasureTheory.condExp m μ ((P.parts i).indicator (fun _ => (1:ℝ))) x) ∂μ :=
          Work.EKLC6Core.Hcond_eq_sum_integral (mX := mX) (m := m) (μ := μ) P
      _ = ∫ x, ∑ i : Fin P.n, Real.negMulLog
            (MeasureTheory.condExp m μ ((P.parts i).indicator (fun _ => (1:ℝ))) x) ∂μ :=
          (integral_finsetSum Finset.univ (fun i _ => hIntP i)).symm
      _ ≤ ∫ x, ∑ i : Fin P.n, ∑ j : Fin Q.n, Real.negMulLog
            (MeasureTheory.condExp m μ ((Q.parts j ∩ P.parts i).indicator (fun _ => (1:ℝ))) x) ∂μ :=
          integral_mono_ae (integrable_finsetSum Finset.univ (fun i _ => hIntP i))
            (integrable_finsetSum Finset.univ (fun i _ =>
              integrable_finsetSum Finset.univ (fun j _ => hIntQP i j))) hae
      _ = @Work.EKLContract.Hcond X mX μ Q m
            + @Work.EKLContract.Hcond X mX μ P
              ((@Work.EKLContract.partSigma X mX Q) ⊔ m) := hR

/-! ## 5. Elementary helpers for the `ℝ≥0∞` assembly -/

/-- A sequence tending to `A` has, for each `ε > 0`, a term below `A + ε`. -/
theorem Ch_exists_le_add_of_tendsto {a : ℕ → ℝ} {A : ℝ}
    (h : Filter.Tendsto a Filter.atTop (nhds A)) :
    ∀ ε : ℝ, 0 < ε → ∃ l, a l ≤ A + ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) ε hε
  exact ⟨N, by
    have h1 := hN N le_rfl
    rw [Real.dist_eq] at h1
    linarith [(abs_lt.mp h1).2]⟩

/-- If a nonnegative sequence of reals stays below `A + ε` for every `ε > 0` (somewhere), then the
`ℝ≥0∞`-infimum of its `ofReal` values is at most `ofReal A`. -/
theorem Ch_iInf_ofReal_le {a : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ ε : ℝ, 0 < ε → ∃ l, a l ≤ A + ε) :
    (⨅ l, ENNReal.ofReal (a l)) ≤ ENNReal.ofReal A := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨l, hl⟩ := h (ε : ℝ) (by exact_mod_cast hε)
  calc (⨅ l, ENNReal.ofReal (a l)) ≤ ENNReal.ofReal (a l) := iInf_le _ l
    _ ≤ ENNReal.ofReal (A + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hl
    _ = ENNReal.ofReal A + (ε : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add hA (by positivity), ENNReal.ofReal_coe_nnreal]

/-! ## 6. Monotonicity of `HcondSig` in the conditioning σ-algebra -/

/-- `HcondSig μ M ·` is antitone in the conditioning σ-algebra. -/
theorem Ch_HcondSig_antitone_cond {X : Type*} {M C C' : MeasurableSpace X}
    [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (h : C ≤ C') :
    @HcondSig X mX μ M C' ≤ @HcondSig X mX μ M C := by
  refine iSup_le fun P => ?_
  refine le_trans (ENNReal.ofReal_le_ofReal
    (Hcond_mono (mX := mX) μ P.1 C C' h)) ?_
  exact le_iSup (fun Q : {Q : @Work.EKLContract.FinPart X mX //
      (@Work.EKLContract.partSigma X mX Q) ≤ M} =>
    ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ Q.1 C)) P

/-! ## 7. The supremum over finite sub-partitions is attained along a generating chain -/

/-- **The chain identity.**  For a monotonically refining sequence `F` of finite partitions whose
σ-algebras increase to `M`, the supremum defining `HcondSig μ M B` is attained along `F`. -/
theorem Ch_HcondSig_eq_iSup_chain {X : Type*} {M B : MeasurableSpace X} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (F : ℕ → @Work.EKLContract.FinPart X mX)
    (hFle : ∀ n, (@Work.EKLContract.partSigma X mX (F n)) ≤ M)
    (hFmono : ∀ n, (@Work.EKLContract.partSigma X mX (F n))
      ≤ (@Work.EKLContract.partSigma X mX (F (n + 1))))
    (hFsup : (⨆ n, (@Work.EKLContract.partSigma X mX (F n))) = M) (hB : B ≤ mX) :
    @HcondSig X mX μ M B = ⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B) := by
  have hpartX : ∀ n, (@Work.EKLContract.partSigma X mX (F n)) ≤ mX := by
    intro n
    rw [Work.EKLContract.partSigma]
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨i, rfl⟩
    exact (F n).measurable i
  have hmonoA : Monotone (fun n => (@Work.EKLContract.partSigma X mX (F n)) ⊔ B) :=
    monotone_nat_of_le_succ fun n => sup_le_sup_right (hFmono n) B
  have hsupA : (⨆ n, (@Work.EKLContract.partSigma X mX (F n)) ⊔ B) = M ⊔ B := by
    rw [iSup_sup_eq, hFsup, iSup_const]
  have hleA : ∀ n, (@Work.EKLContract.partSigma X mX (F n)) ⊔ B ≤ mX :=
    fun n => sup_le (hpartX n) hB
  have hnonnegQ : ∀ n, 0 ≤ @Work.EKLContract.Hcond X mX μ (F n) B :=
    fun n => Ch_Hcond_nonneg (mX := mX) (m := B) μ (F n)
  refine le_antisymm ?_ ?_
  · refine iSup_le fun P => ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    -- the entropy of `P.1` given `partSigma (F n) ⊔ B` tends to `0`
    have h0 : @Work.EKLContract.Hcond X mX μ P.1 (M ⊔ B) ≤ 0 := by
      have h1 := Hcond_mono (mX := mX) μ P.1
        (@Work.EKLContract.partSigma X mX P.1) (M ⊔ B) (le_trans P.2 le_sup_left)
      rw [Work.EKLC6Core.BiGenAux.Hcond_partSigma_eq_zero (mX := mX) μ P.1] at h1
      exact h1
    obtain ⟨N, hN⟩ := Work.EKLC6Core.exists_Hcond_le_of_iSup_le_zero (mX := mX) μ P.1
      (fun n => (@Work.EKLContract.partSigma X mX (F n)) ⊔ B) hmonoA hleA
      (by rw [hsupA]; exact h0) (by exact_mod_cast hε)
    -- the chain-rule bound
    have hD := Ch_Hcond_le_Hcond_add (mX := mX) (m := B) (μ := μ) P.1 (F N)
    calc ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1 B)
        ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F N) B
            + @Work.EKLContract.Hcond X mX μ P.1
              ((@Work.EKLContract.partSigma X mX (F N)) ⊔ B)) :=
          ENNReal.ofReal_le_ofReal hD
      _ = ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F N) B)
            + ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1
              ((@Work.EKLContract.partSigma X mX (F N)) ⊔ B)) :=
          ENNReal.ofReal_add (hnonnegQ N)
            (Ch_Hcond_nonneg (mX := mX) (m := _) μ P.1)
      _ ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F N) B) + (ε : ℝ≥0∞) := by
          refine add_le_add_right ?_ _
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal hN
      _ ≤ (⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B)) + (ε : ℝ≥0∞) :=
          add_le_add_left (le_iSup (fun n =>
            ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B)) N) _
  · refine iSup_le fun n => ?_
    exact le_iSup (fun Q : {Q : @Work.EKLContract.FinPart X mX //
        (@Work.EKLContract.partSigma X mX Q) ≤ M} =>
      ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ Q.1 B)) ⟨F n, hFle n⟩

/-! ## 8. The chain rule at the level of `HcondSig` -/

/-- **The `HcondSig` chain rule.**  For a finite partition `F` with `partSigma F ≤ M`, splitting
off the information of `B` already contained in `partSigma F` gives
`HcondSig μ M B = ofReal (Hcond μ F B) + HcondSig μ M (partSigma F ⊔ B)`. -/
theorem Ch_HcondSig_eq_add {X : Type*} {M B : MeasurableSpace X} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (F : @Work.EKLContract.FinPart X mX) (hF : (@Work.EKLContract.partSigma X mX F) ≤ M) :
    @HcondSig X mX μ M B
      = ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
        + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX F) ⊔ B) := by
  have hnonnegF : 0 ≤ @Work.EKLContract.Hcond X mX μ F B :=
    Ch_Hcond_nonneg (mX := mX) (m := B) μ F
  refine le_antisymm ?_ ?_
  · refine iSup_le fun P => ?_
    have hD := Ch_Hcond_le_Hcond_add (mX := mX) (m := B) (μ := μ) P.1 F
    calc ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1 B)
        ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B
            + @Work.EKLContract.Hcond X mX μ P.1
              ((@Work.EKLContract.partSigma X mX F) ⊔ B)) := ENNReal.ofReal_le_ofReal hD
      _ = ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
            + ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1
              ((@Work.EKLContract.partSigma X mX F) ⊔ B)) :=
          ENNReal.ofReal_add hnonnegF (Ch_Hcond_nonneg (mX := mX) (m := _) μ P.1)
      _ ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
            + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX F) ⊔ B) :=
          add_le_add_right (le_iSup (fun Q : {Q : @Work.EKLContract.FinPart X mX //
            (@Work.EKLContract.partSigma X mX Q) ≤ M} =>
            ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ Q.1
              ((@Work.EKLContract.partSigma X mX F) ⊔ B))) P) _
  · haveI : Nonempty {Q : @Work.EKLContract.FinPart X mX //
        (@Work.EKLContract.partSigma X mX Q) ≤ M} :=
      ⟨⟨Work.EKLContract.trivPart X,
        by rw [Work.EKLContract.partSigma_trivPart X]; exact bot_le⟩⟩
    have key : ∀ P : {P : @Work.EKLContract.FinPart X mX //
        (@Work.EKLContract.partSigma X mX P) ≤ M},
        ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
          + ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1
              ((@Work.EKLContract.partSigma X mX F) ⊔ B))
        ≤ @HcondSig X mX μ M B := by
      intro P
      have hj := Work.EKLComp.Hcond_joinTwo (mX := mX) μ F P.1 B
      have hpart : (@Work.EKLContract.partSigma X mX
          (@Work.EKLComp.joinTwo X mX F P.1)) ≤ M := by
        rw [Work.EKLComp.partSigma_joinTwo (mX := mX)]; exact sup_le hF P.2
      have h1 : ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ
          (@Work.EKLComp.joinTwo X mX F P.1) B) ≤ @HcondSig X mX μ M B :=
        le_iSup (fun Q : {Q : @Work.EKLContract.FinPart X mX //
          (@Work.EKLContract.partSigma X mX Q) ≤ M} =>
          ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ Q.1 B)) ⟨_, hpart⟩
      refine le_trans (le_of_eq ?_) h1
      rw [hj, ENNReal.ofReal_add hnonnegF (Ch_Hcond_nonneg (mX := mX) (m := _) μ P.1),
        show B ⊔ (@Work.EKLContract.partSigma X mX F)
          = (@Work.EKLContract.partSigma X mX F) ⊔ B from sup_comm B _]
    calc ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
          + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX F) ⊔ B)
        = ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
          + ⨆ P : {P : @Work.EKLContract.FinPart X mX //
              (@Work.EKLContract.partSigma X mX P) ≤ M},
              ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1
                ((@Work.EKLContract.partSigma X mX F) ⊔ B)) := rfl
      _ = ⨆ P : {P : @Work.EKLContract.FinPart X mX //
              (@Work.EKLContract.partSigma X mX P) ≤ M},
              (ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ F B)
                + ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ P.1
                  ((@Work.EKLContract.partSigma X mX F) ⊔ B))) := ENNReal.add_iSup _
      _ ≤ @HcondSig X mX μ M B := iSup_le key

/-! ## 9. Lévy from above for `HcondSig` -/

/-- With `HcondSig μ M B < ∞`, the conditional entropies of `B` given `partSigma (F n) ⊔ B` tend
to `0`. -/
theorem Ch_HcondSig_iInf_chain_sup_eq_zero {X : Type*} {M B : MeasurableSpace X}
    [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (F : ℕ → @Work.EKLContract.FinPart X mX)
    (hFle : ∀ n, (@Work.EKLContract.partSigma X mX (F n)) ≤ M)
    (hFmono : ∀ n, (@Work.EKLContract.partSigma X mX (F n))
      ≤ (@Work.EKLContract.partSigma X mX (F (n + 1))))
    (hFsup : (⨆ n, (@Work.EKLContract.partSigma X mX (F n))) = M) (hB : B ≤ mX)
    (hfin : @HcondSig X mX μ M B ≠ ⊤) :
    (⨅ n, @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ B)) = 0 := by
  have hchain : @HcondSig X mX μ M B
      = ⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B) :=
    Ch_HcondSig_eq_iSup_chain (mX := mX) (M := M) (B := B) μ F hFle hFmono hFsup hB
  have hfin' : (@HcondSig X mX μ M B) ≠ ⊤ := hfin
  have h_eq : (⨅ n, @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ B))
      = ⨅ n, (@HcondSig X mX μ M B
          - ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B)) := by
    refine iInf_congr fun n => ?_
    have h := Ch_HcondSig_eq_add (mX := mX) (M := M) (B := B) μ (F n) (hFle n)
    rw [add_comm] at h
    exact (ENNReal.sub_eq_of_eq_add (ne_of_lt ENNReal.ofReal_lt_top) h).symm
  have haX : (⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B)) ≠ ⊤ := by
    rw [← hchain]; exact hfin'
  have hsub : (⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B))
        - ⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B)
      = ⨅ n, ((⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B))
        - ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) B)) :=
    ENNReal.sub_iSup haX
  rw [h_eq, hchain, ← hsub, tsub_self]

/-! ## 10. The main theorem -/

theorem Ch_HcondSig_iInf_sigma {X : Type*} [mX : MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (M : MeasurableSpace X)
    (hMgen : ∃ b : Set (Set X), b.Countable ∧ M = MeasurableSpace.generateFrom b)
    (hMle : M ≤ mX) (C : ℕ → MeasurableSpace X) (hCmono : Monotone C)
    (hCle : ∀ l, C l ≤ mX) (hfin : @Work.EKLC6Core.HcondSig X mX μ M (C 0) ≠ ⊤) :
    (⨅ l, @Work.EKLC6Core.HcondSig X mX μ M (C l))
      = @Work.EKLC6Core.HcondSig X mX μ M (⨆ l, C l) := by
  obtain ⟨b, hbc, hbgen⟩ := hMgen
  -- a countably generating sequence for `M`, measurable for the ambient σ-algebra
  have hseq : ∃ f : ℕ → Set X, (∀ n, @MeasurableSet X M (f n)) ∧
      MeasurableSpace.generateFrom (Set.range f) = M := by
    letI : MeasurableSpace X := M
    haveI : MeasurableSpace.CountablyGenerated X := ⟨b, hbc, hbgen⟩
    exact ⟨MeasurableSpace.natGeneratingSequence X,
      fun n => MeasurableSpace.measurableSet_natGeneratingSequence n,
      MeasurableSpace.generateFrom_natGeneratingSequence X⟩
  obtain ⟨f, hfM, hfgen⟩ := hseq
  have hfX : ∀ n, @MeasurableSet X mX (f n) :=
    fun n => (MeasurableSpace.le_def.mp hMle) (f n) (hfM n)
  obtain ⟨F, hF1, hF2, hF3⟩ :=
    Work.EKLGen.exists_finPart_chain_of_generating (mX := mX) f hfX
  have hFle : ∀ n, (@Work.EKLContract.partSigma X mX (F n)) ≤ M :=
    fun n => by rw [← hfgen]; exact hF1 n
  have hFmono : ∀ n, (@Work.EKLContract.partSigma X mX (F n))
      ≤ (@Work.EKLContract.partSigma X mX (F (n + 1))) := hF2
  have hFsup : (⨆ n, (@Work.EKLContract.partSigma X mX (F n))) = M := by rw [hF3, hfgen]
  refine le_antisymm ?_ ?_
  · -- the hard direction
    have hchainS : @HcondSig X mX μ M (⨆ l, C l)
        = ⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (⨆ l, C l)) :=
      Ch_HcondSig_eq_iSup_chain (mX := mX) (M := M) (B := ⨆ l, C l) μ F hFle hFmono hFsup
        (iSup_le hCle)
    have hstep5 : (⨅ n, @HcondSig X mX μ M
        ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))) = 0 :=
      Ch_HcondSig_iInf_chain_sup_eq_zero (mX := mX) (M := M) (B := C 0) μ F hFle hFmono hFsup
        (hCle 0) hfin
    have step_a : ∀ n, (⨅ l, @HcondSig X mX μ M (C l))
        ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (⨆ l, C l))
          + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0)) := by
      intro n
      have hpoint : ∀ l, @HcondSig X mX μ M (C l)
          ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (C l))
            + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0)) := by
        intro l
        rw [Ch_HcondSig_eq_add (mX := mX) (M := M) (B := C l) μ (F n) (hFle n)]
        refine add_le_add_right ?_ _
        exact Ch_HcondSig_antitone_cond (mX := mX) (M := M) μ
          (sup_le_sup_left (hCmono (Nat.zero_le l)) _)
      calc (⨅ l, @HcondSig X mX μ M (C l))
          ≤ ⨅ l, (ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (C l))
              + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))) :=
            iInf_mono hpoint
        _ = (⨅ l, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (C l)))
              + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0)) :=
            (ENNReal.iInf_add).symm
        _ ≤ ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (⨆ l, C l))
              + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0)) := by
            refine add_le_add_left ?_ _
            refine Ch_iInf_ofReal_le (Ch_Hcond_nonneg (mX := mX) (m := _) μ (F n)) fun ε hε => ?_
            exact Ch_exists_le_add_of_tendsto
              (Work.EKLGen.tendsto_Hcond_iSup_univ (mX := mX) μ (F n) C hCmono hCle) ε hε
    calc (⨅ l, @HcondSig X mX μ M (C l))
        ≤ ⨅ n, (ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (⨆ l, C l))
            + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))) :=
          le_iInf step_a
      _ ≤ (⨆ n, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (⨆ l, C l)))
            + (⨅ n, @HcondSig X mX μ M
              ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))) := by
          have h1 : (⨅ n, (ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (⨆ l, C l))
                + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))))
              ≤ ⨅ n, ((⨆ m,
                    ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F m) (⨆ l, C l)))
                  + @HcondSig X mX μ M
                    ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))) :=
            iInf_mono fun n =>
              add_le_add_left (le_iSup (fun m =>
                ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F m) (⨆ l, C l))) n) _
          calc (⨅ n, (ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F n) (⨆ l, C l))
                + @HcondSig X mX μ M ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))))
              ≤ ⨅ n, ((⨆ m,
                    ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F m) (⨆ l, C l)))
                  + @HcondSig X mX μ M
                    ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))) := h1
            _ = (⨆ m, ENNReal.ofReal (@Work.EKLContract.Hcond X mX μ (F m) (⨆ l, C l)))
                  + (⨅ n, @HcondSig X mX μ M
                    ((@Work.EKLContract.partSigma X mX (F n)) ⊔ (C 0))) :=
                (ENNReal.add_iInf).symm
      _ = @HcondSig X mX μ M (⨆ l, C l) := by rw [← hchainS, hstep5, add_zero]
  · -- the easy direction: monotonicity in the conditioning σ-algebra
    refine le_iInf fun l =>
      Ch_HcondSig_antitone_cond (mX := mX) (M := M) μ (le_iSup C l)

end Work.EKLC6Core

end
