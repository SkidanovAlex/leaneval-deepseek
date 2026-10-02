import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.KahnPartition

namespace Work.Deep.Nibble

open scoped BigOperators

/-!
# Counting the vertex sets of the colour classes of a colouring

This module proves the double-counting identity

`∑_j |S ∩ classVert φ j| = ∑_{v ∈ S} d_𝓖(v)`

for a colouring `φ` of a hypergraph `𝓖` on `Fin n`: summing over the colours the
number of vertices of `S` covered by a colour class counts every pair `(v, e)`
with `v ∈ S` and `e ∋ v` exactly once, because distinct edges through `v` have
distinct colours (they meet in `v`), while two distinct colours can cover `v`
only through distinct edges through `v`.

The key ingredient is `card_colors_covering`: for a fixed vertex `v`, the number
of colour classes covering `v` is the degree of `v`.
-/

variable {n : ℕ} {𝓖 : HG n} {c : ℕ}

/-- Membership in the vertex set covered by a colour class: `v` lies in
`classVert φ j` exactly when some edge of colour `j` contains `v`. -/
lemma mem_classVert_iff (φ : 𝓖.Coloring (Fin c)) (v : Fin n) (j : Fin c) :
    v ∈ classVert φ j ↔ ∃ e : 𝓖, φ.labels e = j ∧ v ∈ (e : Set (Fin n)) := by
  rw [classVert, Set.mem_sUnion]
  constructor
  · rintro ⟨t, ⟨x, hx, rfl⟩, hv⟩
    exact ⟨x, hx, hv⟩
  · rintro ⟨e, he, hv⟩
    exact ⟨(e : Set (Fin n)), ⟨e, he, rfl⟩, hv⟩

/-- Distinct edges through a common vertex carry distinct colours. -/
lemma labels_injOn_through (φ : 𝓖.Coloring (Fin c)) (v : Fin n) :
    Set.InjOn (fun e : 𝓖 => φ.labels e) {e : 𝓖 | v ∈ (e : Set (Fin n))} := by
  intro e₁ h₁ e₂ h₂ hlab
  by_contra hne
  exact φ.isColoring e₁ e₂ hne ⟨v, h₁, h₂⟩ hlab

/-- The number of colour classes covering a vertex is its degree: colour classes
covering `v` correspond bijectively to the edges through `v` (by their colour). -/
lemma card_colors_covering (φ : 𝓖.Coloring (Fin c)) (v : Fin n) :
    Nat.card {j : Fin c // v ∈ classVert φ j}
      = ErdosFaberLovaszConjecture.hypergraphDegree 𝓖 v := by
  classical
  rw [ErdosFaberLovaszConjecture.hypergraphDegree]
  have key : ∀ e : {e : 𝓖 // v ∈ (e : Set (Fin n))},
      v ∈ classVert φ (φ.labels e.1) :=
    fun e => (mem_classVert_iff φ v (φ.labels e.1)).mpr ⟨e.1, rfl, e.2⟩
  refine le_antisymm ?_ ?_
  · refine Nat.card_le_card_of_surjective
      (fun e : {e : 𝓖 // v ∈ (e : Set (Fin n))} =>
        (⟨φ.labels e.1, key e⟩ : {j : Fin c // v ∈ classVert φ j})) ?_
    rintro ⟨j, hj⟩
    obtain ⟨e, he, hv⟩ := (mem_classVert_iff φ v j).mp hj
    exact ⟨⟨e, hv⟩, Subtype.ext he⟩
  · refine Nat.card_le_card_of_injective
      (fun e : {e : 𝓖 // v ∈ (e : Set (Fin n))} =>
        (⟨φ.labels e.1, key e⟩ : {j : Fin c // v ∈ classVert φ j})) ?_
    rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ hEq
    have hlab : φ.labels e₁ = φ.labels e₂ := congrArg Subtype.val hEq
    have heq : e₁ = e₂ := by
      by_contra hne
      exact φ.isColoring e₁ e₂ hne ⟨v, h₁, h₂⟩ hlab
    exact Subtype.ext heq

/-- The cardinality of a finite set as a sum of indicators. -/
lemma ncard_cast_eq_sum_indicator (A : Set (Fin n)) :
    ((A.ncard : ℕ) : ℝ) = ∑ v : Fin n, A.indicator (fun _ => (1 : ℝ)) v := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  have hf : A.toFinset = Finset.univ.filter (fun v : Fin n => v ∈ A) := by ext v; simp
  rw [hf, ← Finset.sum_boole (fun v : Fin n => v ∈ A) Finset.univ]
  simp only [Set.indicator_apply]

/-- A fixed vertex is counted once per colour class covering it, and the number
of those classes is its degree. -/
lemma sum_indicator_classVert (φ : 𝓖.Coloring (Fin c)) (v : Fin n) :
    (∑ j : Fin c, (classVert φ j).indicator (fun _ => (1 : ℝ)) v)
      = ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓖 v : ℕ) : ℝ) := by
  classical
  have h1 : ∀ j : Fin c, (classVert φ j).indicator (fun _ => (1 : ℝ)) v
      = (if v ∈ classVert φ j then (1 : ℝ) else 0) := fun j => Set.indicator_apply _ _ _
  simp only [h1]
  rw [Finset.sum_boole]
  have h2 : (Finset.univ.filter (fun j : Fin c => v ∈ classVert φ j)).card
      = Nat.card {j : Fin c // v ∈ classVert φ j} := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_ofFinset (p := {j : Fin c | v ∈ classVert φ j})
      (Finset.univ.filter (fun j : Fin c => v ∈ classVert φ j))
      (fun a => by simp [Finset.mem_filter])).symm
  rw [h2, card_colors_covering]

/-- **Double counting: the colour classes cover every edge at every vertex.**  For a colouring `φ` of a hypergraph `𝓖` on `Fin n` with `c ≥ 1` colours and any set `S` of vertices, the sum over the colours `j` of the number of vertices of `S` covered by the class of `j` equals the sum of the degrees `d_𝓖(v)` over `v ∈ S`.  Indeed, each pair `(v, e)` with `v ∈ S` and `e ∋ v` contributes exactly once: to the class of the colour of `e`, and distinct edges through `v` have distinct colours because they meet in `v`. -/
theorem sum_classVert_ncard_eq {n : ℕ} {𝓖 : HG n} {c : ℕ} (hc : 1 ≤ c)
    (φ : 𝓖.Coloring (Fin c)) (S : Set (Fin n)) :
    (∑ j : Fin c, ((S ∩ classVert φ j).ncard : ℝ))
      = ∑ v : Fin n, S.indicator
          (fun v => ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓖 v : ℕ) : ℝ)) v := by
  classical
  have hterm : ∀ j : Fin c, ((S ∩ classVert φ j).ncard : ℝ)
      = ∑ v : Fin n, (S ∩ classVert φ j).indicator (fun _ => (1 : ℝ)) v :=
    fun j => ncard_cast_eq_sum_indicator (S ∩ classVert φ j)
  calc (∑ j : Fin c, ((S ∩ classVert φ j).ncard : ℝ))
      = ∑ j : Fin c, ∑ v : Fin n, (S ∩ classVert φ j).indicator (fun _ => (1 : ℝ)) v :=
        Finset.sum_congr rfl (fun j _ => hterm j)
    _ = ∑ v : Fin n, ∑ j : Fin c, (S ∩ classVert φ j).indicator (fun _ => (1 : ℝ)) v :=
        Finset.sum_comm
    _ = ∑ v : Fin n, S.indicator
          (fun v => ((ErdosFaberLovaszConjecture.hypergraphDegree 𝓖 v : ℕ) : ℝ)) v := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        by_cases hv : v ∈ S
        · have hcongr : (∑ j : Fin c, (S ∩ classVert φ j).indicator (fun _ => (1 : ℝ)) v)
              = ∑ j : Fin c, (classVert φ j).indicator (fun _ => (1 : ℝ)) v := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Set.indicator_apply, Set.indicator_apply]
            simp [hv]
          rw [hcongr, sum_indicator_classVert φ v, Set.indicator_of_mem hv]
        · rw [Set.indicator_of_notMem hv]
          refine Finset.sum_eq_zero (fun j _ => ?_)
          rw [Set.indicator_apply]
          simp [hv]

end Work.Deep.Nibble
