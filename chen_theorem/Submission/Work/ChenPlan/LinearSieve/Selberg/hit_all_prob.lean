import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.vocab
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.ExpLaw
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.PiSetup
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.PiSplit
import Submission.Work.ChenPlan.LinearSieve.Selberg.hit_all_prob_aux
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.summable_cY_ae
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.refsum_main

/-!
# Independence of the interval-hit events of the exponential partial-sum process

Let `x : ℕ → ℝ` be an iid standard-exponential sequence and `Tf k x = x 0 + ⋯ + x (k-1)` its
partial sums (a unit-rate Poisson process).  For a finite family of pairwise disjoint half-open
intervals `(a i, b i]` with `0 ≤ a i ≤ b i`, the events "some partial sum lies in `(a i, b i]`"
are independent with probabilities `1 - exp (-(b i - a i))`; this is `allHit_measure` below.

The proof is an induction on the number of intervals: peel off the interval with the smallest
left endpoint, use the strong-Markov ("splitting") property which says that the hit events below
the end of that interval are independent of the future, and apply the induction hypothesis to
the (translated) remaining family.

The statement `hit_all_prob` then transports this to an arbitrary iid sequence on an arbitrary
probability space via the identification of its law with the canonical product law `canonM`.
-/

namespace Work.ChenPlan.LinearSieve.Selberg

open MeasureTheory
open scoped ENNReal
open Work.ChenPlan.LinearSieve.Selberg.Alt
open Work.ChenPlan.LinearSieve.Selberg.HitAux

/-- **The canonical computation.**  For a finite family of pairwise disjoint half-open intervals
`(a i, b i]` with `0 ≤ a i`, the probability (under the canonical iid exponential product law)
that every interval contains a partial sum of the sequence is the product of `1 - exp (-(b-a))`. -/
theorem allHit_measure (m : ℕ) : ∀ {ι : Type*} (a b : ι → ℝ) (U : Finset ι), U.card ≤ m →
    (∀ i ∈ U, 0 ≤ a i) → (∀ i ∈ U, a i ≤ b i) →
    (∀ i ∈ U, ∀ j ∈ U, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j))) →
    (PiN expLaw) (⋂ i ∈ U, Hit (a i) (b i))
      = ∏ i ∈ U, ENNReal.ofReal (1 - Real.exp (-(b i - a i))) := by
  classical
  induction m with
  | zero =>
      intro ι a b U hU ha hab hdisj
      have hU0 : U = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hU)
      subst hU0
      simp
  | succ m ih =>
      intro ι a b U hU ha hab hdisj
      by_cases hsmall : U.card ≤ m
      · exact ih a b U hsmall ha hab hdisj
      · have hcard : U.card = m + 1 := by
          have h1 : m < U.card := Nat.lt_of_not_le hsmall
          omega
        have hne : U.Nonempty := Finset.card_pos.mp (by omega)
        by_cases hemp : ∃ i ∈ U, a i = b i
        · obtain ⟨i, hiU, hieq⟩ := hemp
          have hempty : Hit (a i) (b i) = ∅ := by
            ext x
            simp only [Hit, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
            intro k
            rw [hieq, Set.Ioc_self]
            exact Set.notMem_empty x
          have hsub : (⋂ k ∈ U, Hit (a k) (b k)) ⊆ Hit (a i) (b i) := by
            intro x hx
            simp only [Set.mem_iInter] at hx
            exact hx i hiU
          have hzero : (PiN expLaw) (⋂ k ∈ U, Hit (a k) (b k)) = 0 :=
            measure_mono_null hsub (by rw [hempty]; exact measure_empty)
          rw [hzero]
          exact (Finset.prod_eq_zero hiU (by
            rw [hieq, sub_self, neg_zero, Real.exp_zero]; simp)).symm
        · have hemp' : ∀ i ∈ U, a i ≠ b i := fun i hi h => hemp ⟨i, hi, h⟩
          obtain ⟨j, hjU, hjmin⟩ := Finset.exists_min_image U a hne
          have hjW : j ∉ U.erase j := Finset.notMem_erase j U
          have hUins : U = insert j (U.erase j) := (Finset.insert_erase hjU).symm
          have herase : (insert j (U.erase j)).erase j = U.erase j := Finset.erase_insert hjW
          have hcardW : (U.erase j).card = m := by
            rw [Finset.card_erase_of_mem hjU]; omega
          have hlt : a j < b j := lt_of_le_of_ne (hab j hjU) (hemp' j hjU)
          have hA : ∀ i ∈ U.erase j, b j ≤ a i := by
            intro i hiW
            have hiU : i ∈ U := Finset.mem_of_mem_erase hiW
            have hij : i ≠ j := (Finset.mem_erase.mp hiW).1
            by_contra hcon
            have hai : a i < b j := not_le.mp hcon
            have hibi : a i < b i := lt_of_le_of_ne (hab i hiU) (hemp' i hiU)
            set u : ℝ := (a i + min (b i) (b j)) / 2 with hu
            have hmin_gt : a i < min (b i) (b j) := lt_min hibi hai
            have hd := hdisj i hiU j hjU hij
            rw [Set.disjoint_left] at hd
            have hu1 : u ∈ Set.Ioc (a i) (b i) := by
              rw [Set.mem_Ioc]
              exact ⟨by rw [hu]; linarith [hjmin i hiU],
                by rw [hu]; linarith [min_le_left (b i) (b j)]⟩
            have hu2 : u ∈ Set.Ioc (a j) (b j) := by
              rw [Set.mem_Ioc]
              exact ⟨by rw [hu]; linarith [hjmin i hiU],
                by rw [hu]; linarith [min_le_right (b i) (b j)]⟩
            exact hd hu1 hu2
          have hsp := splitting (μ := expLaw) hasExpLaw_expLaw (t := b j) (a := a j)
            (le_trans (ha j hjU) (le_of_lt hlt)) hlt
            (fun i : ↥(U.erase j) => a i) (fun i : ↥(U.erase j) => b i)
            (fun i => hA i i.2)
          have hAll_eq : AllHit (fun i : ↥(U.erase j) => a i - b j)
                (fun i : ↥(U.erase j) => b i - b j)
              = ⋂ i ∈ (Finset.univ : Finset ↥(U.erase j)), Hit (a i - b j) (b i - b j) := by
            ext x
            simp only [AllHit, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_univ,
              true_implies, Set.mem_setOf_eq]
            exact Iff.rfl
          have hih := ih (fun i : ↥(U.erase j) => a i - b j)
            (fun i : ↥(U.erase j) => b i - b j)
            (Finset.univ : Finset ↥(U.erase j))
            (by rw [Finset.card_univ, Fintype.card_coe, hcardW])
            (fun i _ => sub_nonneg.mpr (hA i i.2))
            (fun i _ => sub_le_sub_right (hab i (Finset.mem_of_mem_erase i.2)) (b j))
            (fun i _ i' _ hii' => by
              rw [Set.disjoint_left]
              intro x hx hx'
              have hd := hdisj i (Finset.mem_of_mem_erase i.2) i'
                (Finset.mem_of_mem_erase i'.2) (fun h => hii' (Subtype.ext h))
              rw [Set.disjoint_left] at hd
              have h1 : x + b j ∈ Set.Ioc (a i) (b i) := by
                rw [Set.mem_Ioc] at hx ⊢
                exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
              have h2 : x + b j ∈ Set.Ioc (a i') (b i') := by
                rw [Set.mem_Ioc] at hx' ⊢
                exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
              exact hd h1 h2)
          have hih' : (PiN expLaw)
                (AllHit (fun i : ↥(U.erase j) => a i - b j)
                  (fun i : ↥(U.erase j) => b i - b j))
              = ∏ i ∈ U.erase j, ENNReal.ofReal (1 - Real.exp (-(b i - a i))) := by
            rw [hAll_eq, hih,
              Finset.prod_coe_sort (U.erase j) (fun y : ι =>
                ENNReal.ofReal (1 - Real.exp (-((b y - b j) - (a y - b j)))))]
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [show (b i - b j) - (a i - b j) = b i - a i from by ring]
          have hsetU : (⋂ i ∈ U, Hit (a i) (b i))
              = Hit (a j) (b j) ∩ AllHit (fun i : ↥(U.erase j) => a i)
                (fun i : ↥(U.erase j) => b i) := by
            rw [hUins, herase]
            ext x
            simp only [AllHit, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff,
              Finset.mem_insert, Set.mem_setOf_eq]
            constructor
            · intro h
              exact ⟨h j (Or.inl rfl), fun i => h i (Or.inr i.2)⟩
            · rintro ⟨h1, h2⟩ i (rfl | hi)
              · exact h1
              · exact h2 ⟨i, hi⟩
          have hprodU : (∏ i ∈ U, ENNReal.ofReal (1 - Real.exp (-(b i - a i))))
              = ENNReal.ofReal (1 - Real.exp (-(b j - a j)))
                * ∏ i ∈ U.erase j, ENNReal.ofReal (1 - Real.exp (-(b i - a i))) := by
            rw [hUins, Finset.prod_insert hjW, herase]
          rw [hsetU, hsp, hit_single hasExpLaw_expLaw (ha j hjU) (hab j hjU), hih', hprodU]

/-- The canonical statement in the `IntervalHit` vocabulary of `Alt.vocab`, for a family indexed
by a finite type. -/
theorem canon_allHit_prob {ι : Type*} [Fintype ι] (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hab : ∀ i, a i ≤ b i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (U : Finset ι) :
    (PiN expLaw)
        (⋂ i ∈ U, Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i))
      = ∏ i ∈ U, ENNReal.ofReal (1 - Real.exp (-(b i - a i))) := by
  rw [show (⋂ i ∈ U, Alt.IntervalHit (fun i (x : ℕ → ℝ) => x i) (a i) (b i))
      = ⋂ i ∈ U, Hit (a i) (b i) from rfl]
  exact allHit_measure U.card a b U le_rfl (fun i _ => ha i) (fun i _ => hab i)
    (fun i _ j _ hij => hdisj i j hij)

theorem hit_all_prob {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (E : ℕ → Ω → ℝ) (hEmeas : ∀ i, AEMeasurable (E i) P)
    (hElaw : ∀ i, Work.ChenPlan.LinearSieve.Selberg.Alt.IsStdExp (E i) P)
    (hindep : ProbabilityTheory.iIndepFun E P)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hab : ∀ i, a i ≤ b i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (U : Finset ι) :
    ENNReal.toReal (P (⋂ i ∈ U, Work.ChenPlan.LinearSieve.Selberg.Alt.IntervalHit E (a i) (b i)))
      = ∏ i ∈ U, (1 - Real.exp (-(b i - a i))) := by
  classical
  have hΦ : AEMeasurable (fun ω : Ω => fun i : ℕ => E i ω) P :=
    aemeasurable_pi_iff.mpr hEmeas
  have hmap : P.map (fun ω : Ω => fun i : ℕ => E i ω) = PiN expLaw := by
    have h := map_seq_eq_canonM P E hEmeas hElaw hindep
    rwa [show (PiN expLaw : Measure (ℕ → ℝ)) = canonM from rfl]
  have hpre : (fun ω : Ω => fun i : ℕ => E i ω) ⁻¹' (⋂ i ∈ U, Hit (a i) (b i))
      = ⋂ i ∈ U, Alt.IntervalHit E (a i) (b i) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq, Hit, Alt.IntervalHit, Tf,
      partialSum]
  have hmeas : MeasurableSet (⋂ i ∈ U, Hit (a i) (b i)) :=
    U.finite_toSet.measurableSet_biInter (fun i _ => measurableSet_Hit)
  have hmain : P (⋂ i ∈ U, Alt.IntervalHit E (a i) (b i))
      = ∏ i ∈ U, ENNReal.ofReal (1 - Real.exp (-(b i - a i))) := by
    rw [← hpre, ← Measure.map_apply_of_aemeasurable hΦ hmeas, hmap]
    exact canon_allHit_prob a b ha hab hdisj U
  rw [hmain, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_ofReal (by
    have h1 : Real.exp (-(b i - a i)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith [hab i]
    linarith)]

end Work.ChenPlan.LinearSieve.Selberg
