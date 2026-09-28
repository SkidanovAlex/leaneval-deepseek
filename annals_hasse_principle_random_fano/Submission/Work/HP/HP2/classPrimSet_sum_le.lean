import Mathlib
import Submission.Work.HP.PFCountDefs
import Submission.Work.HP.HP2.finite_eNorm_ball

set_option autoImplicit false
noncomputable section
open Finset

namespace Work.HP.HP2

/-- **The class pieces are disjoint and sit inside `primConeSet`.** For a `Finset G` of integer
vectors in the box `[0,W)^{n+1}` that are primitive at every prime divisor of `W` and satisfy
`W ∣ f_a(b)`, the sum over `b ∈ G` of the cardinalities of the per-class sets `classPrimSet b` is at
most the cardinality of `primConeSet` (the index set of `NVloc`).

Route.
* Inclusion: for `v ∈ classPrimSet d n a b W α R` we have `IsPrim v`, `eNorm v ≤ R` and the cone
  condition outright, and `(W : ℤ) ∣ formEval d n a v` because `v ≡ b (mod W)` and `W ∣ f_a(b)`
  (`Work.HP.formEval_congr_mod`), so `v ∈ primConeSet`.
* Disjointness: if `v ∈ classPrimSet b ∩ classPrimSet b'` then `W ∣ (b i - b' i)` for all `i` while
  `0 ≤ b i, b' i < W`, so `b = b'` (if `W = 0` the box condition is unsatisfiable, so `G = ∅` and the
  claim is trivial).
* Then `∑_{b ∈ G} #(classPrimSet b) = #(⋃_{b ∈ G} classPrimSet b) ≤ #primConeSet`, using
  `Set.Finite.ncard_biUnion`/`ncard_le_ncard` and the finiteness of the sets involved
  (`classPrimSet b ⊆ {v | eNorm v ≤ R}`, `primConeSet ⊆ Xi d n B`). -/
theorem classPrimSet_sum_le (d n : ℕ) (a : Work.HP.Mon d n → ℤ) (W : ℕ) (α R : ℝ)
    (G : Finset (Fin (n + 1) → ℤ))
    (hG : ∀ b ∈ G, (∀ i, 0 ≤ b i ∧ b i < W) ∧
        (∀ p : ℕ, p.Prime → p ∣ W → ∃ i, ¬ (p : ℤ) ∣ b i) ∧
        (W : ℤ) ∣ Work.HP.formEval d n a b) :
    ∑ b ∈ G, ((Work.HP.classPrimSet d n a b W α R).ncard : ℝ)
      ≤ ((Work.HP.primConeSet d n a α R W).ncard : ℝ) := by
  classical
  -- ## Inclusion of each class into `primConeSet`.
  have hsub : ∀ b ∈ G,
      Work.HP.classPrimSet d n a b W α R ⊆ Work.HP.primConeSet d n a α R W := by
    intro b hb v hv
    simp only [Work.HP.classPrimSet, Set.mem_ofPred_eq] at hv
    obtain ⟨hprim, hnorm, hmod, hcone⟩ := hv
    have hfevb : (W : ℤ) ∣ Work.HP.formEval d n a b := (hG b hb).2.2
    have h1 : (W : ℤ) ∣ Work.HP.formEval d n a v - Work.HP.formEval d n a b :=
      Work.HP.formEval_congr_mod a W v b hmod
    have h2 : Work.HP.formEval d n a v
        = (Work.HP.formEval d n a v - Work.HP.formEval d n a b) + Work.HP.formEval d n a b := by
      ring
    simp only [Work.HP.primConeSet, Set.mem_ofPred_eq]
    refine ⟨hprim, hnorm, ?_, hcone⟩
    rw [h2]
    exact dvd_add h1 hfevb
  -- ## Pairwise disjointness of the classes.
  have hdisj : (G : Set (Fin (n + 1) → ℤ)).PairwiseDisjoint
      (fun b => Work.HP.classPrimSet d n a b W α R) := by
    intro b hb b' hb' hne
    change Disjoint (Work.HP.classPrimSet d n a b W α R)
      (Work.HP.classPrimSet d n a b' W α R)
    rw [Set.disjoint_left]
    intro v hv hv'
    have hbeq : b = b' := by
      funext i
      simp only [Work.HP.classPrimSet, Set.mem_ofPred_eq] at hv hv'
      have hmodb : (W : ℤ) ∣ v i - b i := hv.2.2.1 i
      have hmodb' : (W : ℤ) ∣ v i - b' i := hv'.2.2.1 i
      have hdvd : (W : ℤ) ∣ b i - b' i := by
        have h3 : (W : ℤ) ∣ (v i - b i) - (v i - b' i) := dvd_sub hmodb hmodb'
        have h4 : (v i - b i) - (v i - b' i) = -(b i - b' i) := by ring
        rw [h4, dvd_neg] at h3
        exact h3
      have hboxb := (hG b hb).1 i
      have hboxb' := (hG b' hb').1 i
      have habs : |b i - b' i| < (W : ℤ) := by
        rw [abs_lt]
        exact ⟨by linarith [hboxb.1, hboxb'.2], by linarith [hboxb.2, hboxb'.1]⟩
      exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd habs)
    exact hne hbeq
  -- ## Finiteness of the pieces.
  have hTfin : ∀ b, (Work.HP.classPrimSet d n a b W α R).Finite := by
    intro b
    refine (finite_eNorm_ball (ι := Fin (n + 1)) R).subset ?_
    intro v hv
    simp only [Work.HP.classPrimSet, Set.mem_ofPred_eq] at hv
    exact hv.2.1
  have hSfin : (Work.HP.primConeSet d n a α R W).Finite := by
    refine (finite_eNorm_ball (ι := Fin (n + 1)) R).subset ?_
    intro v hv
    simp only [Work.HP.primConeSet, Set.mem_ofPred_eq] at hv
    exact hv.2.1
  -- ## The union has the sum of the cardinalities, and lies in `primConeSet`.
  have hunion : (⋃ b ∈ (G : Set (Fin (n + 1) → ℤ)),
        Work.HP.classPrimSet d n a b W α R).ncard
      = ∑ᶠ b ∈ (G : Set (Fin (n + 1) → ℤ)),
        (Work.HP.classPrimSet d n a b W α R).ncard :=
    G.finite_toSet.ncard_biUnion (fun b _ => hTfin b) hdisj
  have hsubU : (⋃ b ∈ (G : Set (Fin (n + 1) → ℤ)),
        Work.HP.classPrimSet d n a b W α R) ⊆ Work.HP.primConeSet d n a α R W := by
    intro v hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨b, hbt, hvb⟩ := hv
    exact hsub b hbt hvb
  have hle : (⋃ b ∈ (G : Set (Fin (n + 1) → ℤ)),
        Work.HP.classPrimSet d n a b W α R).ncard
      ≤ (Work.HP.primConeSet d n a α R W).ncard :=
    Set.ncard_le_ncard hsubU hSfin
  -- ## Assemble.
  have hN : ∑ b ∈ G, (Work.HP.classPrimSet d n a b W α R).ncard
      ≤ (Work.HP.primConeSet d n a α R W).ncard := by
    calc ∑ b ∈ G, (Work.HP.classPrimSet d n a b W α R).ncard
        = ∑ᶠ b ∈ (G : Set (Fin (n + 1) → ℤ)),
            (Work.HP.classPrimSet d n a b W α R).ncard := by
          rw [finsum_mem_eq_finite_toFinset_sum _ G.finite_toSet,
            Finset.finite_toSet_toFinset]
      _ = (⋃ b ∈ (G : Set (Fin (n + 1) → ℤ)),
            Work.HP.classPrimSet d n a b W α R).ncard := hunion.symm
      _ ≤ (Work.HP.primConeSet d n a α R W).ncard := hle
  have hcast : ((∑ b ∈ G, (Work.HP.classPrimSet d n a b W α R).ncard : ℕ) : ℝ)
      = ∑ b ∈ G, ((Work.HP.classPrimSet d n a b W α R).ncard : ℝ) := by
    push_cast
    ring
  rw [← hcast]
  exact_mod_cast hN

end Work.HP.HP2
