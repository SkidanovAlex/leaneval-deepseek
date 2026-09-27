import Submission.Work.EKLComp.EntGenDefs
import Submission.Work.EKLComp.atom_sub_le_badSet
import Submission.Work.EKLComp.EntGenScalar

/-!
# The smallness estimate for the conditional entropy `CH(P,Q)`

If the atoms of `Q` are approximated by unions of atoms of `R` up to measure `ε`, then
`CH μ R Q ≤ 2·Q.n·ε + 3·Q.n·√ε`.  The proof is a per-atom estimate (the scalar bound
`negMulLog_sum_le_delta` plus the geometric estimate `atom_sub_le_badSet`) summed over the atoms
of `R`.
-/

open MeasureTheory
open scoped ENNReal BigOperators symmDiff

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.EKLComp

open Work.EKLContract

variable {X : Type} [mX : MeasurableSpace X]

/-- The "bad set" of a family of unions of atoms relative to `Q`. -/
def badSet (R Q : FinPart X) (J : Fin Q.n → Set (Fin R.n)) : Set X :=
  ⋃ i, symmDiff (unionAtoms R (J i)) (Q.parts i)

theorem badSet_eq (R Q : FinPart X) (J : Fin Q.n → Set (Fin R.n)) :
    badSet R Q J
      = ⋃ i, ((unionAtoms R (J i)) \ (Q.parts i) ∪ (Q.parts i \ unionAtoms R (J i))) := by
  ext x
  simp only [badSet, Set.mem_iUnion, Set.mem_symmDiff, Set.mem_union, Set.mem_sdiff]

theorem badSet_measurable (R Q : FinPart X) (J : Fin Q.n → Set (Fin R.n)) :
    MeasurableSet (badSet R Q J) := by
  rw [badSet_eq]
  exact MeasurableSet.iUnion fun i =>
    ((unionAtoms_measurable R (J i)).diff (Q.measurable i)).union
      ((Q.measurable i).diff (unionAtoms_measurable R (J i)))


/-- The repackaging of the scalar estimate used below. -/
theorem negMulLog_sum_le_delta' {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hcb : ∀ i, c i ≤ ∑ j, c j) (i₀ : Fin n) :
    ∑ i, Real.negMulLog (c i) ≤ Real.negMulLog (∑ i, c i)
      + 2 * (∑ i, c i - c i₀)
      + 2 * (Real.sqrt n * Real.sqrt ((∑ i, c i) * (2 * (∑ i, c i - c i₀)))) := by
  linarith [negMulLog_sum_le_delta_le c hc hcb i₀]

/-- **Per-atom estimate.** -/
theorem atom_defect_le (μ : Measure X) [IsProbabilityMeasure μ] (R Q : FinPart X)
    (J : Fin Q.n → Set (Fin R.n)) (j : Fin R.n) (i₀ : Fin Q.n)
    (hi₀ : ∀ i, (μ (R.parts j ∩ Q.parts i)).toReal
      ≤ (μ (R.parts j ∩ Q.parts i₀)).toReal) :
    (∑ i, Real.negMulLog ((μ (R.parts j ∩ Q.parts i)).toReal))
        - Real.negMulLog ((μ (R.parts j)).toReal)
      ≤ 2 * (μ (R.parts j ∩ badSet R Q J)).toReal
        + 2 * (Real.sqrt (Q.n : ℝ)
            * Real.sqrt (2 * ((μ (R.parts j)).toReal * (μ (R.parts j ∩ badSet R Q J)).toReal))) := by
  have hsum : ∑ i, (μ (R.parts j ∩ Q.parts i)).toReal = (μ (R.parts j)).toReal := by
    rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top μ _),
      Core.IsMPart.sum_measure_inter μ (isMPart_parts Q) (R.measurable j)]
  have hc0 : ∀ i, 0 ≤ (μ (R.parts j ∩ Q.parts i)).toReal := fun i => ENNReal.toReal_nonneg
  have hcb : ∀ i, (μ (R.parts j ∩ Q.parts i)).toReal
      ≤ ∑ i', (μ (R.parts j ∩ Q.parts i')).toReal := by
    intro i
    rw [hsum]
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono Set.inter_subset_left)
  have hdelta := negMulLog_sum_le_delta' (fun i => (μ (R.parts j ∩ Q.parts i)).toReal) hc0 hcb i₀
  rw [hsum] at hdelta
  have hkey : (μ (R.parts j)).toReal - (μ (R.parts j ∩ Q.parts i₀)).toReal
      ≤ (μ (R.parts j ∩ badSet R Q J)).toReal := atom_sub_le_badSet μ R Q J j i₀ hi₀
  have hb0 : 0 ≤ (μ (R.parts j)).toReal := ENNReal.toReal_nonneg
  have harg : (μ (R.parts j)).toReal
        * (2 * ((μ (R.parts j)).toReal - (μ (R.parts j ∩ Q.parts i₀)).toReal))
      ≤ 2 * ((μ (R.parts j)).toReal * (μ (R.parts j ∩ badSet R Q J)).toReal) := by
    nlinarith [hb0, hkey]
  have hsqrt : Real.sqrt ((μ (R.parts j)).toReal
        * (2 * ((μ (R.parts j)).toReal - (μ (R.parts j ∩ Q.parts i₀)).toReal)))
      ≤ Real.sqrt (2 * ((μ (R.parts j)).toReal * (μ (R.parts j ∩ badSet R Q J)).toReal)) :=
    Real.sqrt_le_sqrt harg
  have hsqrt' : Real.sqrt (Q.n : ℝ) * Real.sqrt ((μ (R.parts j)).toReal
        * (2 * ((μ (R.parts j)).toReal - (μ (R.parts j ∩ Q.parts i₀)).toReal)))
      ≤ Real.sqrt (Q.n : ℝ)
        * Real.sqrt (2 * ((μ (R.parts j)).toReal * (μ (R.parts j ∩ badSet R Q J)).toReal)) :=
    mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)
  linarith [hdelta, hkey, hsqrt']

/-- **The smallness estimate**: if every atom of `Q` is approximated, up to measure `ε`, by a union
of atoms of `R`, then `CH μ R Q ≤ 2·Q.n·ε + 3·Q.n·√ε`. -/
theorem CHp_le_of_unions (μ : Measure X) [IsProbabilityMeasure μ] (R Q : FinPart X)
    (J : Fin Q.n → Set (Fin R.n)) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ i, (μ (symmDiff (unionAtoms R (J i)) (Q.parts i))).toReal < ε) :
    CHp μ R Q ≤ 2 * (Q.n : ℝ) * ε + 3 * (Q.n : ℝ) * Real.sqrt ε := by
  rcases Nat.eq_zero_or_pos Q.n with hn | hn
  · haveI : IsEmpty (Fin Q.n) := ⟨fun q => by
      have h : q.1 < 0 := hn ▸ q.2
      exact Nat.not_lt_zero q.1 h⟩
    have h1 : Hfam μ (joinFam R.parts Q.parts) = 0 := by
      rw [Hfam]
      refine Finset.sum_eq_zero fun q _ => ?_
      exact False.elim (isEmptyElim q.2)
    have h2 : 0 ≤ Hfam μ R.parts := Core.Hfam_nonneg μ _
    rw [CHp_eq, h1, hn]
    simp only [Nat.cast_zero, mul_zero, zero_mul]
    linarith
  · haveI : Nonempty (Fin Q.n) := ⟨⟨0, hn⟩⟩
    -- the maximizing index for each atom of `R`
    have hex : ∀ j : Fin R.n, ∃ i : Fin Q.n, ∀ i' : Fin Q.n,
        (μ (R.parts j ∩ Q.parts i')).toReal ≤ (μ (R.parts j ∩ Q.parts i)).toReal := by
      intro j
      obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin Q.n))
        (fun i => (μ (R.parts j ∩ Q.parts i)).toReal) Finset.univ_nonempty
      exact ⟨i, fun i' => hi i' (Finset.mem_univ i')⟩
    set i₀ : Fin R.n → Fin Q.n := fun j => Classical.choose (hex j) with hi₀def
    have hi₀ : ∀ j i', (μ (R.parts j ∩ Q.parts i')).toReal
        ≤ (μ (R.parts j ∩ Q.parts (i₀ j))).toReal := fun j => Classical.choose_spec (hex j)
    -- sum identities
    have hbj : ∑ j, (μ (R.parts j)).toReal = 1 :=
      Core.IsMPart.sum_measure_toReal μ (isMPart_parts R)
    have hSsum : ∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal = (μ (badSet R Q J)).toReal := by
      have hunion : (⋃ j, (R.parts j ∩ badSet R Q J)) = badSet R Q J := by
        rw [← Set.iUnion_inter, R.cover, Set.univ_inter]
      have h1 := measureReal_iUnion_fintype (μ := μ)
        (f := fun j : Fin R.n => R.parts j ∩ badSet R Q J)
        (fun j j' hjj' => (R.disjoint hjj').mono Set.inter_subset_left Set.inter_subset_left)
        (fun j => (R.measurable j).inter (badSet_measurable R Q J))
        (fun j => measure_ne_top μ _)
      rw [hunion] at h1
      exact h1.symm
    have hSle : ∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal
        ≤ (Q.n : ℝ) * ε := by
      have h1 : (μ (badSet R Q J)).toReal
          ≤ ∑ i, (μ (symmDiff (unionAtoms R (J i)) (Q.parts i))).toReal := by
        rw [badSet]
        exact measureReal_iUnion_fintype_le _
      have h2 : ∑ i, (μ (symmDiff (unionAtoms R (J i)) (Q.parts i))).toReal < (Q.n : ℝ) * ε := by
        have h3 : ∑ i : Fin Q.n, ε = (Q.n : ℝ) * ε := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp
        rw [← h3]
        exact Finset.sum_lt_sum (fun i _ => le_of_lt (h i))
          ⟨⟨0, hn⟩, Finset.mem_univ _, h ⟨0, hn⟩⟩
      linarith [hSsum]
    -- sum of the square roots
    have hsqrtsum : ∑ j, Real.sqrt (2 * ((μ (R.parts j)).toReal
          * (μ (R.parts j ∩ badSet R Q J)).toReal))
        ≤ Real.sqrt 2 * Real.sqrt (∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal) := by
      have hcs := Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
        (f := fun j : Fin R.n => 2 * (μ (R.parts j)).toReal)
        (g := fun j : Fin R.n => (μ (R.parts j ∩ badSet R Q J)).toReal)
        (fun j => by positivity) (fun j => ENNReal.toReal_nonneg)
      have hterm : ∀ j : Fin R.n,
          Real.sqrt (2 * (μ (R.parts j)).toReal)
              * Real.sqrt ((μ (R.parts j ∩ badSet R Q J)).toReal)
            = Real.sqrt (2 * ((μ (R.parts j)).toReal
                * (μ (R.parts j ∩ badSet R Q J)).toReal)) := by
        intro j
        rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 2 * (μ (R.parts j)).toReal from by positivity)]
        congr 1
        ring
      have hsum_f : ∑ j : Fin R.n, 2 * (μ (R.parts j)).toReal = 2 := by
        rw [← Finset.mul_sum, hbj, mul_one]
      have hsum_g : ∑ j : Fin R.n, (μ (R.parts j ∩ badSet R Q J)).toReal
          = (∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal) := rfl
      calc ∑ j, Real.sqrt (2 * ((μ (R.parts j)).toReal
              * (μ (R.parts j ∩ badSet R Q J)).toReal))
          = ∑ j, Real.sqrt (2 * (μ (R.parts j)).toReal)
              * Real.sqrt ((μ (R.parts j ∩ badSet R Q J)).toReal) := by
            exact Finset.sum_congr rfl fun j _ => (hterm j).symm
        _ ≤ Real.sqrt (∑ j : Fin R.n, 2 * (μ (R.parts j)).toReal)
              * Real.sqrt (∑ j : Fin R.n, (μ (R.parts j ∩ badSet R Q J)).toReal) := hcs
        _ = Real.sqrt 2 * Real.sqrt (∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal) := by
            rw [hsum_f]
    -- the entropy split
    have hCH : CHp μ R Q = (∑ j, ∑ i, Real.negMulLog ((μ (R.parts j ∩ Q.parts i)).toReal))
        - ∑ j, Real.negMulLog ((μ (R.parts j)).toReal) := by
      simp only [CHp_eq, Hfam]
      congr 1
      rw [Core.sum_prod_univ]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [joinFam_apply]
    have hbody : (∑ j, ∑ i, Real.negMulLog ((μ (R.parts j ∩ Q.parts i)).toReal))
        - ∑ j, Real.negMulLog ((μ (R.parts j)).toReal)
        ≤ ∑ j, (2 * (μ (R.parts j ∩ badSet R Q J)).toReal
            + 2 * (Real.sqrt (Q.n : ℝ) * Real.sqrt (2 * ((μ (R.parts j)).toReal
                * (μ (R.parts j ∩ badSet R Q J)).toReal)))) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun j _ => atom_defect_le μ R Q J j (i₀ j) (hi₀ j)
    -- final arithmetic
    have hsqrt_bound : Real.sqrt (Q.n : ℝ)
          * (Real.sqrt 2 * Real.sqrt (∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal))
        ≤ Real.sqrt 2 * ((Q.n : ℝ) * Real.sqrt ε) := by
      have hn0 : (0 : ℝ) ≤ (Q.n : ℝ) := Nat.cast_nonneg _
      have hS0 : 0 ≤ ∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal :=
        Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
      have hAB : Real.sqrt (Q.n : ℝ)
            * Real.sqrt (∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal)
          ≤ (Q.n : ℝ) * Real.sqrt ε := by
        rw [← Real.sqrt_mul hn0]
        have h2 : (Q.n : ℝ) * (∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal)
            ≤ (Q.n : ℝ) * ((Q.n : ℝ) * ε) := by nlinarith [hSle, hn0]
        calc Real.sqrt ((Q.n : ℝ) * (∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal))
            ≤ Real.sqrt ((Q.n : ℝ) * ((Q.n : ℝ) * ε)) := Real.sqrt_le_sqrt h2
          _ = (Q.n : ℝ) * Real.sqrt ε := by
              rw [Real.sqrt_mul hn0, Real.sqrt_mul hn0, ← mul_assoc, Real.mul_self_sqrt hn0]
      calc Real.sqrt (Q.n : ℝ)
            * (Real.sqrt 2 * Real.sqrt (∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal))
          = Real.sqrt 2 * (Real.sqrt (Q.n : ℝ)
              * Real.sqrt (∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal)) := by ring
        _ ≤ Real.sqrt 2 * ((Q.n : ℝ) * Real.sqrt ε) :=
            mul_le_mul_of_nonneg_left hAB (Real.sqrt_nonneg 2)
    have hfinal : ∑ j, (2 * (μ (R.parts j ∩ badSet R Q J)).toReal
          + 2 * (Real.sqrt (Q.n : ℝ) * Real.sqrt (2 * ((μ (R.parts j)).toReal
              * (μ (R.parts j ∩ badSet R Q J)).toReal))))
        ≤ 2 * ((Q.n : ℝ) * ε) + 3 * ((Q.n : ℝ) * Real.sqrt ε) := by
      have hsum2 : ∑ j, (2 * (μ (R.parts j ∩ badSet R Q J)).toReal
          + 2 * (Real.sqrt (Q.n : ℝ) * Real.sqrt (2 * ((μ (R.parts j)).toReal
              * (μ (R.parts j ∩ badSet R Q J)).toReal))))
          = 2 * (∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal)
            + 2 * (Real.sqrt (Q.n : ℝ)
              * ∑ j, Real.sqrt (2 * ((μ (R.parts j)).toReal
                  * (μ (R.parts j ∩ badSet R Q J)).toReal))) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.mul_sum]
        · rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [hsum2]
      have hA : 2 * (∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal) ≤ 2 * ((Q.n : ℝ) * ε) := by
        linarith [hSle]
      have hB : 2 * (Real.sqrt (Q.n : ℝ)
            * ∑ j, Real.sqrt (2 * ((μ (R.parts j)).toReal
                * (μ (R.parts j ∩ badSet R Q J)).toReal)))
          ≤ 3 * ((Q.n : ℝ) * Real.sqrt ε) := by
        have h2le : Real.sqrt 2 ≤ (3 : ℝ) / 2 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
        have hnn : 0 ≤ (Q.n : ℝ) * Real.sqrt ε := by positivity
        have hstep : Real.sqrt (Q.n : ℝ)
              * ∑ j, Real.sqrt (2 * ((μ (R.parts j)).toReal
                  * (μ (R.parts j ∩ badSet R Q J)).toReal))
            ≤ Real.sqrt (Q.n : ℝ) * (Real.sqrt 2
                * Real.sqrt (∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal)) :=
          mul_le_mul_of_nonneg_left hsqrtsum (Real.sqrt_nonneg _)
        have hstep2 : Real.sqrt (Q.n : ℝ) * (Real.sqrt 2
              * Real.sqrt (∑ j, (μ (R.parts j ∩ badSet R Q J)).toReal))
            ≤ Real.sqrt 2 * ((Q.n : ℝ) * Real.sqrt ε) := hsqrt_bound
        have hstep3 : Real.sqrt 2 * ((Q.n : ℝ) * Real.sqrt ε)
            ≤ (3 / 2) * ((Q.n : ℝ) * Real.sqrt ε) :=
          mul_le_mul_of_nonneg_right h2le hnn
        linarith [hstep, hstep2, hstep3]
      linarith
    calc CHp μ R Q
        = (∑ j, ∑ i, Real.negMulLog ((μ (R.parts j ∩ Q.parts i)).toReal))
            - ∑ j, Real.negMulLog ((μ (R.parts j)).toReal) := hCH
      _ ≤ ∑ j, (2 * (μ (R.parts j ∩ badSet R Q J)).toReal
            + 2 * (Real.sqrt (Q.n : ℝ) * Real.sqrt (2 * ((μ (R.parts j)).toReal
                * (μ (R.parts j ∩ badSet R Q J)).toReal)))) := hbody
      _ ≤ 2 * ((Q.n : ℝ) * ε) + 3 * ((Q.n : ℝ) * Real.sqrt ε) := hfinal
      _ = 2 * (Q.n : ℝ) * ε + 3 * (Q.n : ℝ) * Real.sqrt ε := by ring


/-- **Smallness of `CHp μ (P M) Q`.**  Given an increasing family `P` whose generated
σ-algebras generate `mX`, the conditional entropy of any fixed finite partition `Q` relative to
`P M` is arbitrarily small for `M` large. -/
theorem CHp_small (μ : Measure X) [IsProbabilityMeasure μ]
    (P : ℕ → FinPart X) (hmono : ∀ m, Refines (P (m + 1)) (P m))
    (hgen : (⨆ m, partSigma (P m)) = mX) (Q : FinPart X) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, CHp μ (P M) Q ≤ ε := by
  intro ε hε
  set δ : ℝ := min 1 ((ε / (6 * ((Q.n : ℝ) + 1))) ^ 2) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have happrox : ∀ i : Fin Q.n, ∃ M : ℕ, ∃ T : Set X,
      (partSigma (P M)).MeasurableSet' T ∧ (μ (symmDiff (Q.parts i) T)).toReal < δ :=
    fun i => exists_measurable_approx μ P hmono hgen (Q.parts i) (Q.measurable i) hδ0
  choose M T hTmeas hTapprox using happrox
  set M₀ : ℕ := (Finset.univ : Finset (Fin Q.n)).sup M with hM₀
  have hMle : ∀ i : Fin Q.n, M i ≤ M₀ := fun i => Finset.le_sup (Finset.mem_univ i)
  have hpart : ∀ i : Fin Q.n, partSigma (P (M i)) ≤ partSigma (P M₀) :=
    fun i => partSigma_mono_iterate P hmono (hMle i)
  have hTmeas' : ∀ i : Fin Q.n, (partSigma (P M₀)).MeasurableSet' (T i) :=
    fun i => (MeasurableSpace.le_def.mp (hpart i)) (T i) (hTmeas i)
  have hJ : ∀ i : Fin Q.n, ∃ J : Set (Fin (P M₀).n), T i = unionAtoms (P M₀) J := by
    intro i
    obtain ⟨J, hJ⟩ := (partSigma_eq_unions_atoms (P M₀) (T i)).mp (hTmeas' i)
    exact ⟨J, by rw [hJ, unionAtoms]⟩
  choose J hJeq using hJ
  have hmain : CHp μ (P M₀) Q ≤ 2 * (Q.n : ℝ) * δ + 3 * (Q.n : ℝ) * Real.sqrt δ :=
    CHp_le_of_unions μ (P M₀) Q J (le_of_lt hδ0) fun i => by
      rw [← hJeq i, symmDiff_comm]
      exact hTapprox i
  refine ⟨M₀, le_trans hmain ?_⟩
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hn0 : (0 : ℝ) ≤ (Q.n : ℝ) := Nat.cast_nonneg _
  have hδle : δ ≤ Real.sqrt δ := by
    have h : δ ^ 2 ≤ δ := by nlinarith [hδ1, le_of_lt hδ0]
    calc δ = Real.sqrt (δ ^ 2) := (Real.sqrt_sq (le_of_lt hδ0)).symm
      _ ≤ Real.sqrt δ := Real.sqrt_le_sqrt h
  have hsqrt_le : Real.sqrt δ ≤ ε / (6 * ((Q.n : ℝ) + 1)) := by
    refine le_trans (Real.sqrt_le_sqrt (min_le_right _ _)) ?_
    rw [Real.sqrt_sq (by positivity)]
  have hkey : 2 * (Q.n : ℝ) * δ + 3 * (Q.n : ℝ) * Real.sqrt δ ≤ ε := by
    have h1 : 2 * (Q.n : ℝ) * δ ≤ 2 * (Q.n : ℝ) * Real.sqrt δ := by nlinarith [hδle, hn0]
    have h2 : 3 * ((Q.n : ℝ) * Real.sqrt δ) ≤ 3 * (ε / 5) := by
      have h3 : (Q.n : ℝ) * Real.sqrt δ ≤ ε / 5 := by
        have h4 : (Q.n : ℝ) * Real.sqrt δ
            ≤ (Q.n : ℝ) * (ε / (6 * ((Q.n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hsqrt_le hn0
        have h5 : (Q.n : ℝ) * (ε / (6 * ((Q.n : ℝ) + 1))) ≤ ε / 5 := by
          have h6 : (Q.n : ℝ) / (6 * ((Q.n : ℝ) + 1)) ≤ (1 : ℝ) / 5 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            linarith
          calc (Q.n : ℝ) * (ε / (6 * ((Q.n : ℝ) + 1)))
              = ((Q.n : ℝ) / (6 * ((Q.n : ℝ) + 1))) * ε := by ring
            _ ≤ ((1 : ℝ) / 5) * ε := mul_le_mul_of_nonneg_right h6 (le_of_lt hε)
            _ = ε / 5 := by ring
        linarith [h4, h5]
      linarith [h3]
    nlinarith [h1, h2, hε]
  exact hkey

end Work.EKLComp
