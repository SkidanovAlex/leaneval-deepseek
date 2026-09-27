import Mathlib
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.mixture_entropy_le
import Submission.Work.EKLComp.hPart_exists_refining

/-!
# C3 (E3) — affinity of Kolmogorov–Sinai entropy in the measure

For probability measures `μ`, `ν` on a measurable space, a measurable `T` preserving both,
and `c : ℝ≥0∞` with `c ≤ 1`:

`ent (c • μ + (1 - c) • ν) T = c * ent μ T + (1 - c) * ent ν T`.

The proof has three layers.

* **Pointwise in the partition.**  For a fixed finite partition `P` the two sequences
  `N ↦ Hfam m (joinSets T P N)` and `N ↦ c₀ * Hfam μ (joinSets T P N) + c₁ * Hfam ν (joinSets T P N)`
  (with `c₀ = c.toReal`, `c₁ = (1 - c).toReal`) differ by the constant `log 2` at every `N`:
  the lower bound is concavity of `Real.negMulLog` on each atom, and the upper bound is the
  entropy-of-a-mixture estimate `mixture_entropy_le` applied to the atom masses.  Since both
  sides are subadditive, Fekete's lemma (`Core.hPart_eq_lim`) turns the inequality of the
  sequences into an inequality of the limits, which are the `hPart`'s; the reverse inequality
  is an infimum estimate.  Hence the identity holds for each single partition `P`.

* **Supremum over partitions.**  `ent` is the supremum of `ENNReal.ofReal (hPart …)` over
  finite partitions, so it remains to replace `ofReal (c₀ f + c₁ g)` by
  `c * ofReal f + (1 - c) * ofReal g` and to commute the supremum with the convex combination.
  The two directions are: each summand is bounded by the corresponding supremum (easy), and
  the set of finite partitions is directed under refinement (`commonRefinement`), so that
  `⨆ P ⨆ Q ≤ ⨆ P`; this is exactly the hypothesis of `ENNReal.iSup_add_iSup`, supplied by
  `hPart_le_of_refines`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.EKLComp

open Work.EKLContract

/-! ## 1. Two elementary lemmas -/

/-- The mixture measure, evaluated on a set, in terms of the two measures. -/
lemma ent_affine_mixture_apply {X : Type} [mX : MeasurableSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ≥0∞) (hc : c ≤ 1) (s : Set X) :
    ((c • μ + (1 - c) • ν) s).toReal
      = c.toReal * (μ s).toReal + (1 - c).toReal * (ν s).toReal := by
  have h1 : c * μ s ≠ ∞ :=
    ENNReal.mul_ne_top (ne_of_lt (lt_of_le_of_lt hc ENNReal.one_lt_top)) (measure_ne_top μ s)
  have h2 : (1 - c) * ν s ≠ ∞ :=
    ENNReal.mul_ne_top (ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top))
      (measure_ne_top ν s)
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  show (c • μ s + (1 - c) • ν s).toReal = c.toReal * (μ s).toReal + (1 - c).toReal * (ν s).toReal
  rw [show c • μ s = c * μ s from rfl, show (1 - c) • ν s = (1 - c) * ν s from rfl,
    ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul]

/-- Concavity of `Real.negMulLog` in the form needed on the atoms of a partition. -/
lemma ent_affine_negMulLog_combo {p p' x y : ℝ} (hp : 0 ≤ p) (hp' : 0 ≤ p') (hpw : p + p' = 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    p * Real.negMulLog x + p' * Real.negMulLog y ≤ Real.negMulLog (p * x + p' * y) := by
  have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := ![p, p']) (p := ![x, y])
    (fun i _ => by fin_cases i <;> simp [hp, hp']) (by simp [Fin.sum_univ_two, hpw])
    (fun i _ => by fin_cases i <;> simp [hx, hy])
  simpa [Fin.sum_univ_two] using h

/-- The weight `1 - c` is the complementary weight of `c`, in `ℝ`. -/
lemma ent_affine_toReal_compl {c : ℝ≥0∞} (hc : c ≤ 1) : c.toReal + (1 - c).toReal = 1 := by
  rw [ENNReal.toReal_sub_of_le hc ENNReal.one_ne_top, ENNReal.toReal_one]
  ring

/-! ## 2. `hPart` is affine in the measure -/

/-- **Affinity of `hPart` in the measure**, for a fixed finite partition. -/
theorem ent_affine_hPart_mixture {X : Type} [mX : MeasurableSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (T : X → X) (c : ℝ≥0∞) (hc : c ≤ 1)
    (hmpμ : MeasurePreserving T μ μ) (hmpν : MeasurePreserving T ν ν) (P : FinPart X) :
    hPart (c • μ + (1 - c) • ν) T P
      = c.toReal * hPart μ T P + (1 - c).toReal * hPart ν T P := by
  have hT : Measurable T := hmpμ.measurable
  set m : Measure X := c • μ + (1 - c) • ν with hm
  have hpp' : c.toReal + (1 - c).toReal = 1 := ent_affine_toReal_compl hc
  haveI hmprob : IsProbabilityMeasure m := by
    rw [hm]
    refine ⟨?_⟩
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      show c • (μ Set.univ) = c * μ Set.univ from rfl,
      show (1 - c) • (ν Set.univ) = (1 - c) * ν Set.univ from rfl,
      measure_univ, measure_univ, mul_one, mul_one]
    exact add_tsub_cancel_of_le hc
  have hmpm : MeasurePreserving T m m := by
    refine ⟨hT, ?_⟩
    rw [hm, Measure.map_add _ _ hT, Measure.map_smul, Measure.map_smul,
      hmpμ.map_eq, hmpν.map_eq] <;> try fun_prop
  -- the per-atom lower bound: concavity of `negMulLog`
  have hkey1 : ∀ N : ℕ, c.toReal * Hfam μ (joinSets T P N)
      + (1 - c).toReal * Hfam ν (joinSets T P N) ≤ Hfam m (joinSets T P N) := by
    intro N
    rw [Hfam, Hfam, Hfam, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [hm, ent_affine_mixture_apply μ ν c hc (joinSets T P N w)]
    exact ent_affine_negMulLog_combo ENNReal.toReal_nonneg ENNReal.toReal_nonneg hpp'
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  -- the per-atom upper bound: entropy of a mixture
  have hkey2 : ∀ N : ℕ, Hfam m (joinSets T P N)
      ≤ c.toReal * Hfam μ (joinSets T P N) + (1 - c).toReal * Hfam ν (joinSets T P N)
        + Real.log 2 := by
    intro N
    have hmp := Core.joinSets_isMPart hT P N
    have hq1 : ∑ w : Fin N → Fin P.n, (μ (joinSets T P N w)).toReal = 1 :=
      Core.IsMPart.sum_measure_toReal μ hmp
    have hr1 : ∑ w : Fin N → Fin P.n, (ν (joinSets T P N w)).toReal = 1 :=
      Core.IsMPart.sum_measure_toReal ν hmp
    have key := mixture_entropy_le c.toReal (1 - c).toReal
      (fun w : Fin N → Fin P.n => (μ (joinSets T P N w)).toReal)
      (fun w : Fin N → Fin P.n => (ν (joinSets T P N w)).toReal)
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg hpp' (fun w => ENNReal.toReal_nonneg)
      (fun w => ENNReal.toReal_nonneg) hq1 hr1
    have hcongr : (∑ w : Fin N → Fin P.n, Real.negMulLog ((m (joinSets T P N w)).toReal))
        = ∑ w : Fin N → Fin P.n, Real.negMulLog (c.toReal * (μ (joinSets T P N w)).toReal
            + (1 - c).toReal * (ν (joinSets T P N w)).toReal) := by
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hm, ent_affine_mixture_apply μ ν c hc (joinSets T P N w)]
    rw [Hfam, Hfam, Hfam, hcongr]
    exact key
  -- Fekete: both sides converge to the corresponding `hPart`
  have hsubμ : Subadditive (fun N => Hfam μ (joinSets T P N)) :=
    fun a b => Core.Hfam_joinSets_add_le μ hmpμ P a b
  have hsubν : Subadditive (fun N => Hfam ν (joinSets T P N)) :=
    fun a b => Core.Hfam_joinSets_add_le ν hmpν P a b
  have hsubm : Subadditive (fun N => Hfam m (joinSets T P N)) :=
    fun a b => Core.Hfam_joinSets_add_le m hmpm P a b
  have hbddμ : BddBelow (Set.range fun N : ℕ => Hfam μ (joinSets T P N) / (N : ℝ)) :=
    ⟨0, by rintro _ ⟨N, rfl⟩; exact div_nonneg (Core.Hfam_nonneg μ _) (Nat.cast_nonneg N)⟩
  have hbddν : BddBelow (Set.range fun N : ℕ => Hfam ν (joinSets T P N) / (N : ℝ)) :=
    ⟨0, by rintro _ ⟨N, rfl⟩; exact div_nonneg (Core.Hfam_nonneg ν _) (Nat.cast_nonneg N)⟩
  have hbddm : BddBelow (Set.range fun N : ℕ => Hfam m (joinSets T P N) / (N : ℝ)) :=
    ⟨0, by rintro _ ⟨N, rfl⟩; exact div_nonneg (Core.Hfam_nonneg m _) (Nat.cast_nonneg N)⟩
  have htμ : Tendsto (fun N : ℕ => Hfam μ (joinSets T P N) / (N : ℝ)) atTop (𝓝 (hPart μ T P)) := by
    rw [Core.hPart_eq_lim μ hmpμ P hsubμ]; exact hsubμ.tendsto_lim hbddμ
  have htν : Tendsto (fun N : ℕ => Hfam ν (joinSets T P N) / (N : ℝ)) atTop (𝓝 (hPart ν T P)) := by
    rw [Core.hPart_eq_lim ν hmpν P hsubν]; exact hsubν.tendsto_lim hbddν
  have htm : Tendsto (fun N : ℕ => Hfam m (joinSets T P N) / (N : ℝ)) atTop (𝓝 (hPart m T P)) := by
    rw [Core.hPart_eq_lim m hmpm P hsubm]; exact hsubm.tendsto_lim hbddm
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hcomb : Tendsto (fun N : ℕ => c.toReal * (Hfam μ (joinSets T P N) / (N : ℝ))
      + (1 - c).toReal * (Hfam ν (joinSets T P N) / (N : ℝ)) + Real.log 2 / (N : ℝ))
      atTop (𝓝 (c.toReal * hPart μ T P + (1 - c).toReal * hPart ν T P)) := by
    have hlog : Tendsto (fun N : ℕ => Real.log 2 / (N : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
    have hbase := (htμ.const_mul c.toReal).add (htν.const_mul (1 - c).toReal)
    simpa [add_assoc] using hbase.add hlog
  have hcomb' : Tendsto (fun N : ℕ => c.toReal * (Hfam μ (joinSets T P N) / (N : ℝ))
      + (1 - c).toReal * (Hfam ν (joinSets T P N) / (N : ℝ)))
      atTop (𝓝 (c.toReal * hPart μ T P + (1 - c).toReal * hPart ν T P)) :=
    (htμ.const_mul c.toReal).add (htν.const_mul (1 - c).toReal)
  refine le_antisymm ?_ ?_
  · refine le_of_tendsto_of_tendsto' htm hcomb fun N => ?_
    calc Hfam m (joinSets T P N) / (N : ℝ)
        ≤ (c.toReal * Hfam μ (joinSets T P N) + (1 - c).toReal * Hfam ν (joinSets T P N)
            + Real.log 2) / (N : ℝ) :=
          div_le_div_of_nonneg_right (hkey2 N) (Nat.cast_nonneg N)
      _ = c.toReal * (Hfam μ (joinSets T P N) / (N : ℝ))
            + (1 - c).toReal * (Hfam ν (joinSets T P N) / (N : ℝ)) + Real.log 2 / (N : ℝ) := by
          rw [add_div, add_div, mul_div_assoc, mul_div_assoc]
  · refine le_of_tendsto_of_tendsto' hcomb' htm fun N => ?_
    have hstep : c.toReal * (Hfam μ (joinSets T P N) / (N : ℝ))
        + (1 - c).toReal * (Hfam ν (joinSets T P N) / (N : ℝ))
        = (c.toReal * Hfam μ (joinSets T P N) + (1 - c).toReal * Hfam ν (joinSets T P N))
          / (N : ℝ) := by
      rw [add_div, mul_div_assoc, mul_div_assoc]
    rw [hstep]
    exact div_le_div_of_nonneg_right (hkey1 N) (Nat.cast_nonneg N)

/-! ## 3. The main theorem -/

theorem ent_affine {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (ν : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure ν] (T : X → X) (c : ENNReal) (hc : c ≤ 1)
    (hT : Measurable T) (hmpμ : MeasureTheory.MeasurePreserving T μ μ)
    (hmpν : MeasureTheory.MeasurePreserving T ν ν) :
    Work.EKLContract.ent (c • μ + (1 - c) • ν) T =
      c * Work.EKLContract.ent μ T + (1 - c) * Work.EKLContract.ent ν T := by
  -- the identity for a single partition, valued in `ℝ≥0∞`
  have hP : ∀ P : FinPart X, ENNReal.ofReal (hPart (c • μ + (1 - c) • ν) T P)
      = c * ENNReal.ofReal (hPart μ T P) + (1 - c) * ENNReal.ofReal (hPart ν T P) := by
    intro P
    rw [ent_affine_hPart_mixture μ ν T c hc hmpμ hmpν P,
      ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg (Core.hPart_nonneg μ T P))
        (mul_nonneg ENNReal.toReal_nonneg (Core.hPart_nonneg ν T P)),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (ne_of_lt (lt_of_le_of_lt hc ENNReal.one_lt_top)),
      ENNReal.ofReal_toReal (ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top))]
  -- directedness of the partitions under refinement lets the two suprema be merged
  have hdir : ∀ P Q : FinPart X, ∃ R : FinPart X,
      c * ENNReal.ofReal (hPart μ T P) + (1 - c) * ENNReal.ofReal (hPart ν T Q)
        ≤ c * ENNReal.ofReal (hPart μ T R) + (1 - c) * ENNReal.ofReal (hPart ν T R) := by
    intro P Q
    refine ⟨commonRefinement P Q, ?_⟩
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (ENNReal.ofReal_le_ofReal (hPart_le_of_refines μ hT (refines_commonRefinement_left P Q)))
        bot_le)
      (mul_le_mul_of_nonneg_left
        (ENNReal.ofReal_le_ofReal (hPart_le_of_refines ν hT (refines_commonRefinement_right P Q)))
        bot_le)
  calc Work.EKLContract.ent (c • μ + (1 - c) • ν) T
      = ⨆ P : FinPart X, ENNReal.ofReal (hPart (c • μ + (1 - c) • ν) T P) := rfl
    _ = ⨆ P : FinPart X,
          (c * ENNReal.ofReal (hPart μ T P) + (1 - c) * ENNReal.ofReal (hPart ν T P)) :=
        iSup_congr fun P => hP P
    _ = (⨆ P : FinPart X, c * ENNReal.ofReal (hPart μ T P))
        + ⨆ P : FinPart X, (1 - c) * ENNReal.ofReal (hPart ν T P) :=
        (ENNReal.iSup_add_iSup hdir).symm
    _ = c * (⨆ P : FinPart X, ENNReal.ofReal (hPart μ T P))
        + (1 - c) * ⨆ P : FinPart X, ENNReal.ofReal (hPart ν T P) := by
        rw [← ENNReal.mul_iSup, ← ENNReal.mul_iSup]
    _ = c * Work.EKLContract.ent μ T + (1 - c) * Work.EKLContract.ent ν T := rfl

end Work.EKLComp
