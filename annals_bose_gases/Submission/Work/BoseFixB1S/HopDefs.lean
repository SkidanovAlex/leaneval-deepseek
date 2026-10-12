import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.BoxHopDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.HopDefs` — the *edge* (child) vocabulary of the hopping layer

The crossing term `(V/2)·(boxCrossPart − 2μP̃)` of the sliding box is, by
`Work.BoseFixB1.boxCrossPart_centred`,

    (V/2)·(boxCrossPart − 2μP̃)
      = Σᵢ ∫_{abox} (QᵢΦ)·(fib₁(xᵢ) − κ)·(Pᵢ(n₀Φ) − (1+m)·PᵢΦ) ,   κ = M₁/V , m = μV .

Decomposing `Φ` in the three-way joint components `ψ_{S,T} = boxCompT V A S T Φ` of the commuting
family `(Pᵢ, Qᵢ, Rᵢ)ᵢ` (see `BoxSpectralDefs`), the only surviving pairings move the slot `i` from
the `P`-side to the `Q`-side: the **child** of `(S,T)` at the slot `i ∈ S`,

    c_i(S,T) = (S∖{i}, T∪{i}) .

This module fixes that vocabulary and records the elementary combinatorics of the child map (the
slot types of a pair and of its child agree everywhere except in slot `i`), which the
spectral-expansion lemmas use.

* `hopChild i p` — the child of the pair `p` at the slot `i`;
* `hopPairSet i` — the disjoint pairs whose first component contains `i` (the parents of slot `i`);
* `hopChildMass V A m Φ i` — the slot-`i` part `Wᵢ` of the children mass `boxChildW`:
  `Σ_{p ∋ i, realised} ‖ψ_{c_i(p)}‖²·(|p.1| − 1 − m)²`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The **child** of the pair `p` at the slot `i`: the slot `i` is moved from the `P`-part to the
`Q`-part. -/
def hopChild {N : ℕ} (i : Fin N) (p : Finset (Fin N) × Finset (Fin N)) :
    Finset (Fin N) × Finset (Fin N) :=
  (p.1.erase i, insert i p.2)

/-- The disjoint pairs whose first (`P`) component contains the slot `i`. -/
def hopPairSet {N : ℕ} (i : Fin N) : Finset (Finset (Fin N) × Finset (Fin N)) :=
  (Work.BoseFixB1.disjPairs N).filter (fun p => i ∈ p.1)

/-- The **slot-`i` children mass** `Wᵢ = Σ_{p ∋ i, realised} ‖ψ_{c_i(p)}‖²·(|p.1| − 1 − m)²`.

The sum runs over the realised edges (the parent of positive mass); the child of zero mass
contributes `0` to `boxChildW` as well, so the two forms agree (`hopChildWSplit`). -/
def hopChildMass {N : ℕ} (volA ℓ : ℝ) (A : Set E3) (m : ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (i : Fin N) : ℝ :=
  ∑ p ∈ hopPairSet i,
    (if 0 < Work.BoseFixB1.boxCompTMass volA ℓ A p Φ
      then Work.BoseFixB1.boxCompTMass volA ℓ A (hopChild i p) Φ
        * ((p.1.card : ℝ) - 1 - m) ^ 2
      else 0)

theorem mem_hopPairSet {N : ℕ} {i : Fin N} {p : Finset (Fin N) × Finset (Fin N)} :
    p ∈ hopPairSet i ↔ p ∈ Work.BoseFixB1.disjPairs N ∧ i ∈ p.1 := by
  simp [hopPairSet]

/-- The child of a realised parent is a realised pair. -/
theorem hopChild_mem_disjPairs {N : ℕ} {i : Fin N} {p : Finset (Fin N) × Finset (Fin N)}
    (hp : p ∈ Work.BoseFixB1.disjPairs N) (hi : i ∈ p.1) :
    hopChild i p ∈ Work.BoseFixB1.disjPairs N := by
  rw [Work.BoseFixB1.mem_disjPairs] at hp ⊢
  refine Finset.disjoint_left.mpr fun j hj hji => ?_
  rw [hopChild] at hj hji
  simp only [Finset.mem_erase, Finset.mem_insert] at hj hji
  rcases hji with hji | hji
  · exact hj.1 hji
  · exact (Finset.disjoint_left.mp hp) hj.2 hji

/-- The slot `i` is a `Q`-slot of the child. -/
theorem mem_hopChild_snd {N : ℕ} (i : Fin N) (p : Finset (Fin N) × Finset (Fin N)) :
    i ∈ (hopChild i p).2 := by
  rw [hopChild]
  exact Finset.mem_insert_self i p.2

/-- The child moves the slot `i` and keeps every other slot. -/
theorem hopChild_fst {N : ℕ} (i : Fin N) (p : Finset (Fin N) × Finset (Fin N)) :
    (hopChild i p).1 = p.1.erase i := rfl

theorem hopChild_snd {N : ℕ} (i : Fin N) (p : Finset (Fin N) × Finset (Fin N)) :
    (hopChild i p).2 = insert i p.2 := rfl

/-- **The slot types of the child**: they agree with those of the parent in every slot different
from `i`, and the slot `i` is a `Q`-slot. -/
theorem orthSlotType_hopChild {N : ℕ} {i j : Fin N} (hij : j ≠ i)
    {p : Finset (Fin N) × Finset (Fin N)} (hp : Disjoint p.1 p.2) :
    orthSlotType (hopChild i p).1 (hopChild i p).2 j = orthSlotType p.1 p.2 j := by
  by_cases hj : j ∈ p.1
  · have h1 : j ∈ p.1.erase i := by
      rw [Finset.mem_erase]; exact ⟨hij, hj⟩
    rw [hopChild]
    unfold orthSlotType
    rw [if_pos h1, if_pos hj]
  · by_cases hj2 : j ∈ p.2
    · have h1 : j ∉ p.1.erase i := fun h => hj (Finset.mem_erase.mp h).2
      have h2 : j ∈ insert i p.2 := Finset.mem_insert_of_mem hj2
      rw [hopChild]
      unfold orthSlotType
      rw [if_neg h1, if_pos h2, if_neg hj, if_pos hj2]
    · have h1 : j ∉ p.1.erase i := fun h => hj (Finset.mem_erase.mp h).2
      have h2 : j ∉ insert i p.2 := by
        rw [Finset.mem_insert]
        rintro (h | h)
        · exact hij h
        · exact hj2 h
      rw [hopChild]
      unfold orthSlotType
      rw [if_neg h1, if_neg h2, if_neg hj, if_neg hj2]

/-- The slot `i` of the child is a `Q`-slot, whereas it is a `P`-slot of the parent. -/
theorem orthSlotType_hopChild_self {N : ℕ} {i : Fin N}
    {p : Finset (Fin N) × Finset (Fin N)} (hp : Disjoint p.1 p.2) (hi : i ∈ p.1) :
    orthSlotType (hopChild i p).1 (hopChild i p).2 i = 1
      ∧ orthSlotType p.1 p.2 i = 0 := by
  constructor
  · unfold orthSlotType hopChild
    rw [if_neg (by simp), if_pos (Finset.mem_insert_self i p.2)]
  · unfold orthSlotType
    rw [if_pos hi]

/-- **The child is the only pair whose slot types agree with the parent's outside the slot `i`.**
If `q` is a `Q`-pair at the slot `i` whose types agree with those of the `P`-pair `p` in every
other slot, then `q = hopChild i p`. -/
theorem eq_hopChild_of_types_agree {N : ℕ} {i : Fin N}
    {p q : Finset (Fin N) × Finset (Fin N)} (hp : Disjoint p.1 p.2) (hq : Disjoint q.1 q.2)
    (hpi : i ∈ p.1) (hqi : i ∈ q.2)
    (h : ∀ j : Fin N, j ≠ i → orthSlotType q.1 q.2 j = orthSlotType p.1 p.2 j) :
    q = hopChild i p := by
  have hmem : ∀ j : Fin N, j ≠ i → (j ∈ q.1 ↔ j ∈ p.1) ∧ (j ∈ q.2 ↔ j ∈ p.2) := by
    intro j hj
    have ht := h j hj
    have ht' : orthSlotType p.1 p.2 j = orthSlotType q.1 q.2 j := ht.symm
    constructor
    · rw [← orthSlotType_eq_zero_iff q.1 q.2 j, ← orthSlotType_eq_zero_iff p.1 p.2 j, ht]
    · constructor
      · intro hjq
        have h1 : orthSlotType q.1 q.2 j = 1 :=
          (orthSlotType_eq_one_iff hq j).mpr ⟨Finset.disjoint_right.mp hq hjq, hjq⟩
        rw [← ht'] at h1
        exact ((orthSlotType_eq_one_iff hp j).mp h1).2
      · intro hjp
        have h1 : orthSlotType p.1 p.2 j = 1 :=
          (orthSlotType_eq_one_iff hp j).mpr ⟨Finset.disjoint_right.mp hp hjp, hjp⟩
        rw [← ht] at h1
        exact ((orthSlotType_eq_one_iff hq j).mp h1).2
  have hfst : q.1 = p.1.erase i := by
    ext j
    rw [Finset.mem_erase]
    constructor
    · intro hj
      have hji : j ≠ i := by
        rintro rfl
        exact (Finset.disjoint_left.mp hq) hj hqi
      exact ⟨hji, (hmem j hji).1.mp hj⟩
    · intro hj
      obtain ⟨hji, hjp⟩ := hj
      exact (hmem j hji).1.mpr hjp
  have hsnd : q.2 = insert i p.2 := by
    ext j
    rw [Finset.mem_insert]
    constructor
    · intro hj
      by_cases hji : j = i
      · exact Or.inl hji
      · exact Or.inr ((hmem j hji).2.mp hj)
    · intro hj
      rcases hj with hji | hjp
      · subst hji; exact hqi
      · by_cases hji : j = i
        · subst hji; exact hqi
        · exact (hmem j hji).2.mpr hjp
  exact Prod.ext (hfst.trans (hopChild_fst i p).symm) (hsnd.trans (hopChild_snd i p).symm)

/-- **The mismatch form of the previous lemma**: a `Q`-pair at the slot `i` that is not the child
of the `P`-pair `p` has a slot type differing from that of `p` in some slot `j ≠ i`. -/
theorem exists_type_mismatch_of_ne_hopChild {N : ℕ} {i : Fin N}
    {p q : Finset (Fin N) × Finset (Fin N)} (hp : Disjoint p.1 p.2) (hq : Disjoint q.1 q.2)
    (hpi : i ∈ p.1) (hqi : i ∈ q.2) (hne : q ≠ hopChild i p) :
    ∃ j : Fin N, j ≠ i ∧ orthSlotType q.1 q.2 j ≠ orthSlotType p.1 p.2 j := by
  by_contra hcon
  push_neg at hcon
  exact hne (eq_hopChild_of_types_agree hp hq hpi hqi hcon)

end Work.BoseFixB1S
