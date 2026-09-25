import Mathlib
import Submission.Work.BourgainPlan.Maximal.varTwoLeRmLevels
import Submission.Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal
import Submission.Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal

/-!
# The `Lᵖ` form of the Rademacher–Menshov inequality for the `2`-variation

This is **condition (2) of KMSZ Definition 5.1** (arXiv:2606.12663) for the seminorm
`S(f_n : n ≤ 2^n) := ‖V²(f_n : n ≤ 2^n)‖_{Lᵖ}`: the `Lᵖ` norm of the `2`-variation over the dyadic
window `[0, 2^n]` of an `E`-valued sequence of functions is dominated by the sum, over the `n+1`
dyadic levels `l ≤ n`, of the `Lᵖ` norms of the corresponding **dyadic block square functions**

`x ↦ (Σ_{m<2^{n−l}} ‖f_{(m+1)2^l}(x) − f_{m2^l}(x)‖²)^{1/2}`.

In KMSZ's proof of their seminorm variant of the Ionescu–Wainger multiplier theorem (Theorem 5.2),
this is the inequality which, applied to the multiplier outputs `F_n = T_{ℤ^d}J_G|m_n K_{R^d} f`,
turns the variation bound into a sum of `n+1 ≍ log N` square-function pieces, each of which is then
estimated by Khintchine and the Ionescu–Wainger theorem (uniformly in the signs).  The `log N`
there — and hence the `log log N₀` of Bourgain's (7.35) — is precisely the number `n+1` of terms of
this sum.
-/

namespace Work.BourgainPlan.Maximal

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The chains that are constant after their last relevant index `J`; a countable set. -/
private def stdChains (lo hi : ℕ) : Set (ℕ × (ℕ → ℕ)) :=
  {q | Monotone q.2 ∧ (∀ j ≤ q.1, lo ≤ q.2 j ∧ q.2 j ≤ hi) ∧ ∀ j, q.1 ≤ j → q.2 j = q.2 q.1}

private lemma stdChains_countable (lo hi : ℕ) : (stdChains lo hi).Countable := by
  refine Set.MapsTo.countable_of_injOn (f := fun q : ℕ × (ℕ → ℕ) =>
    (q.1, (List.range (q.1 + 1)).map q.2)) (Set.mapsTo_univ _ _) ?_ Set.countable_univ
  rintro ⟨J, t⟩ ⟨-, -, htc⟩ ⟨J', t'⟩ ⟨-, -, htc'⟩ heq
  simp only [Prod.mk.injEq] at heq htc htc'
  obtain ⟨rfl, hl⟩ := heq
  have hval : ∀ j ≤ J, t j = t' j := fun j hj =>
    (List.map_inj_left.mp hl) j (List.mem_range.mpr (by omega))
  simp only [Prod.mk.injEq, true_and]
  funext j
  rcases le_or_gt j J with hj | hj
  · exact hval j hj
  · rw [htc j hj.le, htc' j hj.le, hval J le_rfl]

private lemma varTwo_eq_biSup_stdChains {E : Type*} [SeminormedAddCommGroup E]
    (lo hi : ℕ) (a : ℕ → E) :
    varTwo lo hi a = ⨆ q ∈ stdChains lo hi, ENNReal.ofReal (chainSq q.1 a q.2) := by
  apply le_antisymm
  · unfold varTwo
    refine iSup_le fun J => iSup_le fun t => iSup_le fun ht => iSup_le fun hr => ?_
    set t' : ℕ → ℕ := fun j => t (min j J) with ht'
    have hmem : (J, t') ∈ stdChains lo hi := by
      refine ⟨fun i j hij => ht (min_le_min_right J hij), fun j hj => ?_, fun j hj => ?_⟩
      · simp only [ht', min_eq_left hj]; exact hr j hj
      · simp only [ht', min_eq_right hj, min_self]
    have hcs : chainSq J a t = chainSq J a t' := by
      unfold chainSq
      refine congrArg Real.sqrt (Finset.sum_congr rfl fun j hj => ?_)
      have hj' : j + 1 ≤ J := Finset.mem_range.mp hj
      simp only [ht', min_eq_left hj', min_eq_left (show j ≤ J by omega)]
    rw [hcs]
    exact le_iSup₂ (f := fun q (_ : q ∈ stdChains lo hi) => ENNReal.ofReal (chainSq q.1 a q.2))
      (J, t') hmem
  · refine iSup₂_le fun q hq => ?_
    unfold varTwo
    exact le_iSup_of_le q.1 (le_iSup_of_le q.2 (le_iSup_of_le hq.1 (le_iSup_of_le hq.2.1 le_rfl)))

/-- **The `Lᵖ` (integrated) form of the `2`-variation Rademacher–Menshov inequality.** -/
theorem varELpNormLe {X : Type*} [MeasurableSpace X] {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure X) (n : ℕ) {p : ℝ} (hp : 1 ≤ p)
    (f : ℕ → X → E) (hf : ∀ i, AEMeasurable (f i) μ) :
    eLpNorm (fun x => varTwo 0 (2 ^ n) (fun i => f i x)) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal 2 * ∑ l ∈ Finset.range (n + 1),
          eLpNorm (fun x => ENNReal.ofReal (rmLevel n l (fun i => f i x)))
            (ENNReal.ofReal p) μ := by
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hp0ne : ENNReal.ofReal p ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one hp)
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hRm : ∀ l, AEMeasurable (fun x => ENNReal.ofReal (rmLevel n l (fun i => f i x))) μ := by
    intro l
    apply ENNReal.measurable_ofReal.comp_aemeasurable
    unfold rmLevel
    apply AEMeasurable.sqrt
    refine Finset.aemeasurable_fun_sum _ (fun m _ => ?_)
    have h1 : AEMeasurable
        (fun x => ‖f ((m + 1) * 2 ^ l) x - f (m * 2 ^ l) x‖) μ :=
      ((hf ((m + 1) * 2 ^ l)).sub (hf (m * 2 ^ l))).norm
    exact h1.pow_const 2
  have hpoint : ∀ x, varTwo 0 (2 ^ n) (fun i => f i x)
      ≤ ENNReal.ofReal 2 * ∑ l ∈ Finset.range (n + 1),
          ENNReal.ofReal (rmLevel n l (fun i => f i x)) := by
    intro x
    have h := varTwo_le_rmLevels n 0 (fun i => f i x)
    simp only [Nat.zero_add] at h
    refine h.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_sum_of_nonneg (fun l _ => rmLevel_nonneg n l _)]
  have h1 : eLpNorm (fun x => varTwo 0 (2 ^ n) (fun i => f i x)) (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun x => ENNReal.ofReal 2 * ∑ l ∈ Finset.range (n + 1),
          ENNReal.ofReal (rmLevel n l (fun i => f i x))) (ENNReal.ofReal p) μ := by
    have hvm : AEMeasurable (fun x => varTwo 0 (2 ^ n) (fun i => f i x)) μ := by
      simp_rw [varTwo_eq_biSup_stdChains]
      refine AEMeasurable.biSup _ (stdChains_countable 0 (2 ^ n)) fun q _ => ?_
      apply ENNReal.measurable_ofReal.comp_aemeasurable
      unfold chainSq
      apply AEMeasurable.sqrt
      refine Finset.aemeasurable_fun_sum _ (fun j _ => ?_)
      exact (((hf (q.2 (j + 1))).sub (hf (q.2 j))).norm).pow_const 2
    apply eLpNorm_mono_enorm hvm.aestronglyMeasurable
    intro x
    rw [enorm_eq_self, enorm_eq_self]
    exact hpoint x
  have hV : eLpNorm (fun x => ENNReal.ofReal 2 * ∑ l ∈ Finset.range (n + 1),
        ENNReal.ofReal (rmLevel n l (fun i => f i x))) (ENNReal.ofReal p) μ
      = ENNReal.ofReal 2 * eLpNorm (fun x => ∑ l ∈ Finset.range (n + 1),
          ENNReal.ofReal (rmLevel n l (fun i => f i x))) (ENNReal.ofReal p) μ :=
    Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
      (V := fun x => ∑ l ∈ Finset.range (n + 1),
        ENNReal.ofReal (rmLevel n l (fun i => f i x)))
      ENNReal.ofReal_ne_top hp0ne hptop
  have hsum : eLpNorm (fun x => ∑ l ∈ Finset.range (n + 1),
        ENNReal.ofReal (rmLevel n l (fun i => f i x))) (ENNReal.ofReal p) μ
      ≤ ∑ l ∈ Finset.range (n + 1),
          eLpNorm (fun x => ENNReal.ofReal (rmLevel n l (fun i => f i x)))
            (ENNReal.ofReal p) μ :=
    Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal hp1 (fun l _ => hRm l)
  exact (h1.trans (le_of_eq hV)).trans (mul_le_mul_right hsum (ENNReal.ofReal 2))

end

end Work.BourgainPlan.Maximal
