import Submission.NBody.MarchalMultiIsolated
import Submission.NBody.MarchalEnergyLowerBound
import Submission.NBody.MarchalCollPartition
import Submission.NBody.MarchalIsolatedCollision

/-!
# The isolatedness of a locally minimal collision (multi-class assembly)

This module assembles the multi-class isolatedness theorem `isolated_of_local_min_multi` with the
energy lower bound `exists_multiRelEnergy_lower_bound`: an `h`-minimiser with a collision in
`[c,d] ⊆ (a,b)` has a collision time in `[c,d]` which is *isolated*.

The two ingredients are:

* `exists_local_min_pairs` — a collision time whose colliding-pair set is locally constant;
* `exists_multiRelEnergy_lower_bound` — the sum of the relative energies of the collision classes is
  bounded below on a neighbourhood of that collision.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- The collision union is the union of the collision classes. -/
lemma multiUnion_collClasses {γ : ℝ → EN E N} {t₀ : ℝ} :
    multiUnion (collClasses γ t₀) = collUnion γ t₀ := rfl

/-- **A locally minimal collision is isolated** (multi-class form).  An `h`-minimiser with a
collision in `[c,d] ⊆ (a,b)` has a collision time `t₁ ∈ [c,d]` which is the only collision time of
`[c,d]` in a neighbourhood of itself. -/
theorem exists_isolated_collision_multi {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b c d : ℝ}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b) (hcld : c < d)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (hcd : Icc c d ⊆ Ioo a b)
    (hcoll : ∃ t ∈ Icc c d, ¬ WithoutCollisions (γ t)) :
    ∃ t₁ ∈ Icc c d, ¬ WithoutCollisions (γ t₁) ∧
      ∃ η > 0, η ≤ 1 ∧ ∀ t ∈ Icc c d, |t - t₁| < η → t ≠ t₁ → WithoutCollisions (γ t) := by
  classical
  have hcontab : ContinuousOn γ (Icc a b) := by
    have h := hac.continuousOn
    rwa [Set.uIcc_of_le hab.le] at h
  have hcontcd : ContinuousOn γ (Icc c d) :=
    hcontab.mono (fun t ht => ⟨(hcd ht).1.le, (hcd ht).2.le⟩)
  obtain ⟨t₁, ht₁, hcoll₁, ε, hεpos, hloc⟩ := exists_local_min_pairs hcontcd hcoll
  have ht₁Ioo : t₁ ∈ Ioo a b := hcd ht₁
  obtain ⟨ν, hνpos, ε₀, hε₀pos, hsepc⟩ :=
    exists_separation_of_collClasses (γ := γ) (a := a) (b := b) (t₀ := t₁) hcontab ht₁Ioo
  set ks : Finset (Finset (Fin N)) := collClasses γ t₁ with hksdef
  have hmulti : multiUnion ks = collUnion γ t₁ := by rw [hksdef]; exact multiUnion_collClasses
  -- the interval on which the separation (and the local constancy of the colliding pairs) holds
  set ε₁ : ℝ := min (ε₀ / 2) (ε / 2) with hε₁def
  have hε₁pos : 0 < ε₁ := lt_min (by linarith) (by linarith)
  have hε₁le₀ : ε₁ ≤ ε₀ / 2 := min_le_left _ _
  have hε₁leε : ε₁ ≤ ε / 2 := min_le_right _ _
  set A : ℝ := max c (t₁ - ε₁) with hAdef
  set B : ℝ := min d (t₁ + ε₁) with hBdef
  have hAle : A ≤ t₁ := max_le ht₁.1 (by linarith)
  have ht₁leB : t₁ ≤ B := le_min ht₁.2 (by linarith)
  have hAB : A < B := by
    rcases lt_or_eq_of_le ht₁.1 with hc | hc
    · rcases lt_or_eq_of_le ht₁.2 with hd | hd
      · have hA : A < t₁ := by rw [hAdef]; exact max_lt hc (by linarith)
        have hB : t₁ < B := by rw [hBdef]; exact lt_min hd (by linarith)
        linarith
      · have hB : B = t₁ := by rw [hBdef, hd]; exact min_eq_left (by linarith)
        have hA : A < t₁ := by rw [hAdef]; exact max_lt hc (by linarith)
        rw [hB]; exact hA
    · have hA : A = t₁ := by rw [hAdef, ← hc]; exact max_eq_left (by linarith)
      rcases eq_or_lt_of_le ht₁.2 with hd | hd
      · rw [hc, hd] at hcld; exact absurd hcld (lt_irrefl d)
      · have hB : t₁ < B := by rw [hBdef]; exact lt_min hd (by linarith)
        rw [hA]; exact hB
  have hAac : a < A := lt_of_lt_of_le (hcd (left_mem_Icc.mpr hcld.le)).1 (le_max_left c _)
  have hBbd : B < b := lt_of_le_of_lt (min_le_left d _) (hcd (right_mem_Icc.mpr hcld.le)).2
  have hABsub : Icc A B ⊆ Ioo (t₁ - ε₀) (t₁ + ε₀) := by
    intro t ht
    have h1 : t₁ - ε₀ / 2 ≤ A := le_trans (by linarith [hε₁le₀]) (le_max_right c _)
    have h2 : B ≤ t₁ + ε₀ / 2 := le_trans (min_le_right d _) (by linarith [hε₁le₀])
    exact ⟨by linarith [h1, ht.1, hε₀pos], by linarith [h2, ht.2, hε₀pos]⟩
  have hABcd : Icc A B ⊆ Icc c d :=
    Set.Icc_subset_Icc (le_max_left c _) (min_le_left d _)
  have hABε : Icc A B ⊆ Ioo (t₁ - ε) (t₁ + ε) := by
    intro t ht
    have h1 : t₁ - ε₁ ≤ A := le_max_right c _
    have h2 : B ≤ t₁ + ε₁ := min_le_right d _
    exact ⟨by linarith [h1, ht.1, hε₁leε, hεpos], by linarith [h2, ht.2, hε₁leε, hεpos]⟩
  -- the motion is collision free wherever the collision classes are spread out
  have hncW : ∀ t ∈ Ioo A B, 0 < multiInertia m ks (γ t) → WithoutCollisions (γ t) := by
    intro t ht hFt
    by_contra hcol
    have h1 : ∃ i j, i ≠ j ∧ γ t i = γ t j := by
      by_contra h
      exact hcol fun i j hij hr => h ⟨i, j, hij, by
        rw [r_eq_norm_sub, norm_eq_zero, sub_eq_zero] at hr
        exact hr⟩
    have htcd : t ∈ Icc c d := hABcd ⟨ht.1.le, ht.2.le⟩
    have htε : |t - t₁| < ε := by
      have hmem := hABε ⟨ht.1.le, ht.2.le⟩
      rw [abs_lt]
      exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    have heq : collPairs γ t = collPairs γ t₁ := hloc t htcd htε h1
    have h0 : multiInertia m ks (γ t) = 0 :=
      hksdef ▸ multiInertia_collClasses_eq_zero_of_collPairs_eq hm heq
    exact absurd h0 (ne_of_gt hFt)
  -- the sum of the relative energies is bounded below on `(A,B)`
  have hsepAB : ∀ t ∈ Icc A B, ∀ k ∈ ks, ClusterSeparatedWeak k (γ t) ν :=
    fun t ht k hk => (hsepc t (hABsub ht)).1 k (hksdef ▸ hk)
  have hsepTAB : ∀ t ∈ Icc A B, ∀ i ∉ multiUnion ks, ∀ j ∉ multiUnion ks,
      i ≠ j → ν ≤ r (γ t) i j := by
    intro t ht i hi j hj hij
    exact (hsepc t (hABsub ht)).2 i (by rwa [← hmulti]) j (by rwa [← hmulti]) hij
  obtain ⟨C, hCnn, hC⟩ := exists_multiRelEnergy_lower_bound (m := m) (h := h) (γ := γ)
    (a := a) (b := b) (A := A) (B := B) (ν := ν) (ks := ks)
    hm hh hab hac hmin hfin hAB hAac hBbd hνpos
    (fun k hk => collClasses_nonempty (hksdef ▸ hk))
    (fun k hk k' hk' hne => disjoint_collClasses (γ := γ) (t₀ := t₁) k
      (by rwa [hksdef] at hk) k' (by rwa [hksdef] at hk') hne)
    hsepAB hsepTAB hncW
  -- the radius on which the lower bound applies
  set δc : ℝ := if t₁ = c then ε₁ else t₁ - c with hδcdef
  set δd : ℝ := if t₁ = d then ε₁ else d - t₁ with hδddef
  have hδcpos : 0 < δc := by
    rw [hδcdef]
    split_ifs with h
    · exact hε₁pos
    · exact sub_pos.mpr (lt_of_le_of_ne ht₁.1 (Ne.symm h))
  have hδdpos : 0 < δd := by
    rw [hδddef]
    split_ifs with h
    · exact hε₁pos
    · exact sub_pos.mpr (lt_of_le_of_ne ht₁.2 h)
  set εE : ℝ := min ε₁ (min δc δd) with hεEdef
  have hεEpos : 0 < εE := lt_min hε₁pos (lt_min hδcpos hδdpos)
  have hεEle₁ : εE ≤ ε₁ := min_le_left _ _
  have hεEleδc : εE ≤ δc := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεEleδd : εE ≤ δd := le_trans (min_le_right _ _) (min_le_right _ _)
  have hE : ∀ t ∈ Icc c d, |t - t₁| < εE → 0 < multiInertia m ks (γ t) →
      -C ≤ multiRelEnergy m ks (γ t) (deriv γ t) := by
    intro t htcd hlt hFt
    have hF0 : multiInertia m ks (γ t₁) = 0 :=
      hksdef ▸ multiInertia_collClasses_eq_zero_of_collPairs_eq hm rfl
    have htne : t ≠ t₁ := fun h => by rw [h] at hFt; exact absurd hFt (not_lt.mpr (le_of_eq hF0))
    have hlt1 : |t - t₁| < ε₁ := lt_of_lt_of_le hlt hεEle₁
    have hltc : |t - t₁| < δc := lt_of_lt_of_le hlt hεEleδc
    have hltd : |t - t₁| < δd := lt_of_lt_of_le hlt hεEleδd
    refine hC t ⟨?_, ?_⟩ hFt
    · rw [hAdef]
      refine max_lt ?_ ?_
      · rw [abs_lt] at hltc
        by_cases htc : t₁ = c
        · exact lt_of_le_of_ne htcd.1 (by rw [← htc]; exact Ne.symm htne)
        · rw [hδcdef] at hltc
          simp only [if_neg htc] at hltc
          linarith [hltc.1]
      · rw [abs_lt] at hlt1
        linarith [hlt1.1]
    · rw [hBdef]
      refine lt_min ?_ ?_
      · rw [abs_lt] at hltd
        by_cases htd : t₁ = d
        · exact lt_of_le_of_ne htcd.2 (by rw [← htd]; exact htne)
        · rw [hδddef] at hltd
          simp only [if_neg htd] at hltd
          linarith [hltd.2]
      · rw [abs_lt] at hlt1
        linarith [hlt1.2]
  obtain ⟨η, hηpos, hη1, hiso⟩ := isolated_of_local_min_multi (m := m) (h := h) (γ := γ)
    (a := a) (b := b) (c := c) (d := d) (t₁ := t₁) (C₁ := C) (εE := εE)
    hm hh hab hac hmin hfin hcd ht₁ hcoll₁ ⟨ε, hεpos, hloc⟩ hεEpos hCnn hE
  exact ⟨t₁, ht₁, hcoll₁, η, hηpos, hη1, hiso⟩

end Submission.NBody
