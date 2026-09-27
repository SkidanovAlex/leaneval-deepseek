import Mathlib
import Submission.Work.EKLComp.EntGenDefs

/-!
# `atom_sub_le_badSet`

A purely measure-theoretic counting lemma used in the generating-sequence part of the entropy
computation.

Let `μ` be a probability measure on `X`, `R` and `Q` two finite measurable partitions, `j` an
atom of `R`, and `J i` a set of `R`-atoms for every atom `i` of `Q` (intuitively:
`⋃_{j' ∈ J i} R_{j'}` is the piece of the `R`-partition sitting inside `Q_i`, so that
`symmDiff (unionAtoms R (J i)) (Q.parts i)` is the "boundary" of `Q_i` with respect to `R`).

Assume that `μ (R_j ∩ Q_{i₀})` is maximal among the numbers `μ (R_j ∩ Q_i)`, `i : Fin Q.n`.
Then

`μ (R_j) - μ (R_j ∩ Q_{i₀}) ≤ μ (R_j ∩ ⋃_i symmDiff (unionAtoms R (J i)) (Q.parts i))`,

i.e. *off the boundary of `Q` with respect to `R`, the mass of `R_j` sits in a single atom of
`Q`* — a "Shannon–McMillan" style statement: on `R_j`, all `Q`-atoms other than one have mass
bounded by the boundary term.

The heart of the argument is the pointwise criterion `mem_badUnion_iff`: for `x ∈ R_j ∩ Q_i`,

`x ∉ ⋃_i symmDiff (unionAtoms R (J i)) (Q.parts i)`

holds exactly when `j` belongs to `J i` and to no other `J i'`.  Consequently, if
`{i | j ∈ J i}` is not a singleton, `R_j` is entirely contained in the bad set, and otherwise
`R_j` minus the bad set is contained in the single atom `Q_{i₁}` with `J i₁ ∋ j`; in that case
`μ (R_j \ Q_{i₁}) ≤ μ (bad set)` and the maximality hypothesis `hi₀` finishes the job.
-/

namespace Work.EKLComp

open MeasureTheory
open Work.EKLContract
open scoped symmDiff

variable {X : Type} [mX : MeasurableSpace X]

/-- The union of the symmetric differences `unionAtoms R (J i) Δ Q.parts i`. -/
def badUnion (R Q : FinPart X) (J : Fin Q.n → Set (Fin R.n)) : Set X :=
  ⋃ i : Fin Q.n, symmDiff (unionAtoms R (J i)) (Q.parts i)

/-- A point of the atom `R_j` belongs to `unionAtoms R J` iff `j ∈ J` (the atoms of `R` are
pairwise disjoint). -/
theorem mem_unionAtoms_iff {R : FinPart X} {J : Set (Fin R.n)} {j : Fin R.n} {x : X}
    (hx : x ∈ R.parts j) : (x ∈ unionAtoms R J ↔ j ∈ J) := by
  constructor
  · intro h
    obtain ⟨j', hj', hxj'⟩ := mem_unionAtoms.mp h
    rcases eq_or_ne j' j with h' | h'
    · exact h' ▸ hj'
    · exact absurd hx (Set.disjoint_left.mp (R.disjoint h') hxj')
  · intro hj
    exact mem_unionAtoms.mpr ⟨j, hj, hx⟩

/-- Pointwise description of the bad set: for `x ∈ R_j ∩ Q_i` the point `x` is outside the bad
set exactly when `j ∈ J i` and `j ∉ J i'` for every other atom index `i'`. -/
theorem mem_badUnion_iff (R Q : FinPart X) (J : Fin Q.n → Set (Fin R.n)) {j : Fin R.n} {x : X}
    (hx : x ∈ R.parts j) (i : Fin Q.n) (hxi : x ∈ Q.parts i) :
    (x ∈ badUnion R Q J ↔ ¬ (j ∈ J i ∧ ∀ i' : Fin Q.n, i' ≠ i → j ∉ J i')) := by
  have hUA : ∀ i : Fin Q.n, (x ∈ unionAtoms R (J i) ↔ j ∈ J i) := fun i =>
    mem_unionAtoms_iff (R := R) (J := J i) hx
  have hQeq : ∀ i' : Fin Q.n, (x ∈ Q.parts i' ↔ i' = i) := by
    intro i'
    constructor
    · intro h
      by_contra hne
      exact Set.disjoint_left.mp (Q.disjoint hne) h hxi
    · intro h; subst h; exact hxi
  rw [badUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨i', hi'⟩
    rintro ⟨hji, huniq⟩
    rw [Set.mem_symmDiff] at hi'
    rcases hi' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hne : i' ≠ i := fun h => h2 ((hQeq i').mpr h)
      exact huniq i' hne ((hUA i').mp h1)
    · have hii : i' = i := (hQeq i').mp h1
      exact (hii ▸ h2) ((hUA i).mpr hji)
  · intro h
    by_cases hji : j ∈ J i
    · push Not at h
      obtain ⟨i', hi'ne, hi'mem⟩ := h hji
      refine ⟨i', ?_⟩
      rw [Set.mem_symmDiff]
      exact Or.inl ⟨(hUA i').mpr hi'mem, fun hxq => hi'ne ((hQeq i').mp hxq)⟩
    · refine ⟨i, ?_⟩
      rw [Set.mem_symmDiff]
      exact Or.inr ⟨hxi, fun hxa => hji ((hUA i).mp hxa)⟩

theorem atom_sub_le_badSet {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] (R Q : Work.EKLContract.FinPart X)
    (J : Fin Q.n → Set (Fin R.n)) (j : Fin R.n) (i₀ : Fin Q.n)
    (hi₀ : ∀ i : Fin Q.n, (μ (R.parts j ∩ Q.parts i)).toReal
      ≤ (μ (R.parts j ∩ Q.parts i₀)).toReal) :
    (μ (R.parts j)).toReal - (μ (R.parts j ∩ Q.parts i₀)).toReal
      ≤ (μ (R.parts j ∩ ⋃ i : Fin Q.n,
          symmDiff (Work.EKLComp.unionAtoms R (J i)) (Q.parts i))).toReal := by
  classical
  set B := ⋃ i : Fin Q.n, symmDiff (unionAtoms R (J i)) (Q.parts i) with hB
  have hcrit : ∀ (x : X) (i : Fin Q.n), x ∈ R.parts j → x ∈ Q.parts i →
      (x ∈ B ↔ ¬ (j ∈ J i ∧ ∀ i' : Fin Q.n, i' ≠ i → j ∉ J i')) :=
    fun x i hx hxi => mem_badUnion_iff R Q J hx i hxi
  have hQR : ∀ x : X, x ∈ R.parts j → ∃ i : Fin Q.n, x ∈ Q.parts i := by
    intro x _
    have h : x ∈ ⋃ i, Q.parts i := by rw [Q.cover]; exact Set.mem_univ x
    simpa only [Set.mem_iUnion] using h
  have hfin : ∀ s : Set X, μ s ≠ ⊤ := by
    intro s
    have h : μ s ≤ 1 := by
      calc μ s ≤ μ Set.univ := measure_mono (Set.subset_univ s)
        _ = 1 := measure_univ
    exact ne_top_of_le_ne_top ENNReal.one_ne_top h
  -- The core inequality: `μ R_j` is dominated by the bad part plus `μ (R_j ∩ Q_{i₀})`.
  have hkey : μ (R.parts j) ≤ μ (R.parts j ∩ B) + μ (R.parts j ∩ Q.parts i₀) := by
    by_cases huniq : ∃! i : Fin Q.n, j ∈ J i
    · -- exactly one index `i₁` with `j ∈ J i₁`: off the bad set, `R_j` lies in `Q_{i₁}`,
      -- and `hi₀` at `i₁` bounds `μ (R_j ∩ Q_{i₁})` by `μ (R_j ∩ Q_{i₀})`.
      obtain ⟨i₁, hi₁mem, hi₁uniq⟩ := huniq
      have hsub : R.parts j \ Q.parts i₁ ⊆ R.parts j ∩ B := by
        rintro x ⟨hxj, hxq⟩
        refine ⟨hxj, ?_⟩
        obtain ⟨i, hxi⟩ := hQR x hxj
        have hne : i ≠ i₁ := fun h => hxq (h ▸ hxi)
        have hnot : ¬ (j ∈ J i ∧ ∀ i' : Fin Q.n, i' ≠ i → j ∉ J i') := by
          rintro ⟨hji, _⟩
          exact hne (hi₁uniq i hji)
        exact (hcrit x i hxj hxi).mpr hnot
      have hmono : μ (R.parts j \ Q.parts i₁) ≤ μ (R.parts j ∩ B) := measure_mono hsub
      have hsplit : μ (R.parts j \ Q.parts i₁) + μ (R.parts j ∩ Q.parts i₁) = μ (R.parts j) := by
        rw [add_comm]
        exact measure_inter_add_sdiff (R.parts j) (Q.measurable i₁)
      have hle : μ (R.parts j ∩ Q.parts i₁) ≤ μ (R.parts j ∩ Q.parts i₀) :=
        (ENNReal.toReal_le_toReal (hfin _) (hfin _)).mp (hi₀ i₁)
      calc μ (R.parts j) = μ (R.parts j \ Q.parts i₁) + μ (R.parts j ∩ Q.parts i₁) :=
            hsplit.symm
        _ ≤ μ (R.parts j ∩ B) + μ (R.parts j ∩ Q.parts i₀) := add_le_add hmono hle
    · -- `{i | j ∈ J i}` is empty or has at least two elements: `R_j` is contained in the bad set.
      have hsub : R.parts j ⊆ B := by
        intro x hxj
        obtain ⟨i, hxi⟩ := hQR x hxj
        have hnot : ¬ (j ∈ J i ∧ ∀ i' : Fin Q.n, i' ≠ i → j ∉ J i') := by
          rintro ⟨hji, hall⟩
          exact huniq ⟨i, hji, fun i' hi' => by
            by_contra hne
            exact hall i' hne hi'⟩
        exact (hcrit x i hxj hxi).mpr hnot
      have hEq : R.parts j ∩ B = R.parts j := Set.inter_eq_left.mpr hsub
      rw [hEq]
      exact le_add_right le_rfl
  have h2 : (μ (R.parts j)).toReal
      ≤ (μ (R.parts j ∩ B)).toReal + (μ (R.parts j ∩ Q.parts i₀)).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin _, hfin _⟩) hkey
    rwa [ENNReal.toReal_add (hfin _) (hfin _)] at h
  linarith

end Work.EKLComp
