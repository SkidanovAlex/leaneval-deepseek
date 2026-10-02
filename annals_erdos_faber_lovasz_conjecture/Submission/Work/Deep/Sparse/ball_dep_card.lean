import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.FiringDefs

/-!
# Dependency neighbourhoods of balls

`Work.Deep.Sparse.ball G v` is the set of vertices whose colours determine the fired
colours at `v` (the neighbours of `v` together with their neighbours).  This module
bounds the number of vertices `w` whose ball meets `ball G v`:  the balls are
symmetric (`ball_mem_comm`), so any such `w` lies in the ball of some `z ∈ ball G v`,
and each ball has at most `D + D²` elements when all degrees are at most `D`
(`ball_card_le`).  Hence the "dependency neighbourhood" of `v` has at most
`(D + D²)² ≤ (D + 1)⁴` elements.
-/

namespace Work.Deep.Sparse

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Balls are symmetric in their two arguments: `u` lies in the ball of `v` iff `v`
lies in the ball of `u`. -/
lemma ball_mem_comm (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} :
    u ∈ ball G v ↔ v ∈ ball G u := by
  rw [mem_ball_iff, mem_ball_iff]
  constructor
  · rintro (h | ⟨x, hvx, hxu⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨x, hxu.symm, hvx.symm⟩
  · rintro (h | ⟨x, hux, hxv⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨x, hxv.symm, hux.symm⟩

/-- In a graph of maximum degree at most `D`, a ball contains at most `D + D²`
vertices: at most `D` neighbours of the centre, each contributing at most `D`
neighbours of its own. -/
lemma ball_card_le (G : SimpleGraph V) [DecidableRel G.Adj] {D : ℕ}
    (hdeg : ∀ x : V, G.degree x ≤ D) (v : V) :
    (ball G v).card ≤ D + D * D := by
  have hdv : G.degree v ≤ D := hdeg v
  have hnb : (G.neighborFinset v).card = G.degree v :=
    SimpleGraph.card_neighborFinset_eq_degree G v
  have hbi : ((G.neighborFinset v).biUnion (fun x => G.neighborFinset x)).card ≤ D * D := by
    have hb : ((G.neighborFinset v).biUnion (fun x => G.neighborFinset x)).card
        ≤ ∑ x ∈ G.neighborFinset v, (G.neighborFinset x).card := Finset.card_biUnion_le
    have h1 : ∑ x ∈ G.neighborFinset v, (G.neighborFinset x).card
        ≤ (G.neighborFinset v).card * D := by
      have h2 : ∑ x ∈ G.neighborFinset v, (G.neighborFinset x).card
          ≤ ∑ x ∈ G.neighborFinset v, D := Finset.sum_le_sum fun x _ => hdeg x
      have h3 : ∑ x ∈ G.neighborFinset v, D = (G.neighborFinset v).card * D := by
        rw [Finset.sum_const, smul_eq_mul]
      omega
    have hmul : (G.neighborFinset v).card * D ≤ D * D := by
      have hnb' : (G.neighborFinset v).card ≤ D := by omega
      exact Nat.mul_le_mul hnb' (le_refl D)
    omega
  have hu : (G.neighborFinset v ∪ (G.neighborFinset v).biUnion (fun x => G.neighborFinset x)).card
      ≤ (G.neighborFinset v).card
        + ((G.neighborFinset v).biUnion (fun x => G.neighborFinset x)).card :=
    Finset.card_union_le _ _
  have hball : (ball G v).card
      = (G.neighborFinset v ∪ (G.neighborFinset v).biUnion (fun x => G.neighborFinset x)).card :=
    rfl
  omega

/-- **Bound on the dependency neighbourhood of a ball.**  If every degree is at most
`D`, then the set of vertices `w` whose ball meets `ball G v` has at most
`(D + 1)⁴ + 1` elements.  Indeed, by symmetry `w` then lies in `ball G z` for some
`z ∈ ball G v`, and each of the at most `D + D² ≤ (D + 1)²` points `z` of `ball G v`
has a ball of size at most `D + D² ≤ (D + 1)²`. -/
theorem ball_dep_card {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hdeg : ∀ x : V, G.degree x ≤ D) (v : V) :
    (Finset.univ.filter (fun w : V => ((Work.Deep.Sparse.ball G v) ∩ (Work.Deep.Sparse.ball G w)).Nonempty)).card
      ≤ (D + 1) ^ 4 + 1 := by
  have hsub : (Finset.univ.filter (fun w : V => ((ball G v) ∩ (ball G w)).Nonempty))
      ⊆ (ball G v).biUnion (fun z => ball G z) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨-, hne⟩ := hw
    obtain ⟨z, hz⟩ := hne
    obtain ⟨hz1, hz2⟩ := Finset.mem_inter.mp hz
    rw [Finset.mem_biUnion]
    exact ⟨z, hz1, (ball_mem_comm G).mp hz2⟩
  have h1 : (Finset.univ.filter (fun w : V => ((ball G v) ∩ (ball G w)).Nonempty)).card
      ≤ ((ball G v).biUnion (fun z => ball G z)).card := Finset.card_le_card hsub
  have h2 : ((ball G v).biUnion (fun z => ball G z)).card
      ≤ ∑ z ∈ ball G v, (ball G z).card := Finset.card_biUnion_le
  have h3 : ∑ z ∈ ball G v, (ball G z).card ≤ (ball G v).card * (D + D * D) := by
    have h4 : ∑ z ∈ ball G v, (ball G z).card ≤ ∑ z ∈ ball G v, (D + D * D) :=
      Finset.sum_le_sum fun z _ => ball_card_le G hdeg z
    have h5 : ∑ z ∈ ball G v, (D + D * D) = (ball G v).card * (D + D * D) := by
      rw [Finset.sum_const, smul_eq_mul]
    omega
  have h6 : (ball G v).card ≤ D + D * D := ball_card_le G hdeg v
  have h7 : (ball G v).card * (D + D * D) ≤ (D + 1) ^ 4 + 1 := by
    have hle : D + D * D ≤ (D + 1) ^ 2 := by
      have hsq : (D + 1) ^ 2 = D * D + 2 * D + 1 := by ring
      omega
    have hmul : (ball G v).card * (D + D * D) ≤ (D + 1) ^ 2 * (D + 1) ^ 2 :=
      Nat.mul_le_mul (h6.trans hle) hle
    have hring : (D + 1) ^ 2 * (D + 1) ^ 2 = (D + 1) ^ 4 := by ring
    omega
  omega

end Work.Deep.Sparse
