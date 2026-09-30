import Submission.Work.BMF.adi_graph_aux
import Submission.Work.BMF.polyrel_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N5 `adi_cycles`: the un-restricted quadruple graph

The counting of `Work.BMF.adi_cycles` averages over the primes `q ∈ [P₂/2, P₂]`.  For that
averaging it is convenient to have the *un-restricted* graph (all edges of `D.edges`, no prime
condition) together with the bicycles of that graph, and to relate the `q`-th bicycle set
`bikeSet D q ℓ` to it.

This file contains only definitions (and their immediate unfolding lemmas).
-/

namespace Work.BMF

open Polynomial Finset Real

variable {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}

/-- The adjacency of the full quadruple graph (`x` and `y` joined whenever some edge of
`D.edges` has exactly these two endpoints). -/
def GAdjAll (D : QuadData k f c C X L P₁ P₂) (x y : GVert D) : Prop :=
  ∃ e ∈ D.edges, (e.x₁ = x.1 ∧ e.x₂ = y.1) ∨ (e.x₁ = y.1 ∧ e.x₂ = x.1)

noncomputable instance (D : QuadData k f c C X L P₁ P₂) :
    DecidableRel (GAdjAll (P₂ := P₂) D) := fun x y => Classical.dec _

lemma GAdjAll_symm (D : QuadData k f c C X L P₁ P₂) (x y : GVert D) :
    GAdjAll D x y ↔ GAdjAll D y x := by
  constructor <;> rintro ⟨e, he, h | h⟩
  · exact ⟨e, he, Or.inr h⟩
  · exact ⟨e, he, Or.inl h⟩
  · exact ⟨e, he, Or.inr h⟩
  · exact ⟨e, he, Or.inl h⟩

lemma GAdjQ_le_GAdjAll (D : QuadData k f c C X L P₁ P₂) {q : ℕ} {x y : GVert D}
    (h : GAdjQ D q x y) : GAdjAll D x y := by
  obtain ⟨e, he, _, h⟩ := h
  exact ⟨e, he, h⟩

/-- All walks of length `ℓ` in the full graph. -/
noncomputable def walkSetAll (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) :
    Finset (Fin (ℓ + 1) → GVert D) :=
  (Finset.univ : Finset (Fin (ℓ + 1) → GVert D)).filter
    (fun W => ∀ j : Fin ℓ, GAdjAll D (W j.castSucc) (W j.succ))

/-- Closed walks of length `ℓ` in the full graph based at the interval with left endpoint `x`. -/
noncomputable def closedWalkAll (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) (x : ℝ) :
    Finset (Fin (ℓ + 1) → GVert D) :=
  (walkSetAll D ℓ).filter
    (fun W => W ⟨ℓ, Nat.lt_succ_self ℓ⟩ = W 0 ∧ (W 0).1 = x)

/-- The bicycles of the full graph: a full-graph edge together with a closed full-graph walk
through each of its endpoints. -/
noncomputable def bikeSetAll (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) :
    Finset (Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) :=
  (D.edges).sigma (fun e =>
    (closedWalkAll D ℓ e.x₁).product (closedWalkAll D ℓ e.x₂))

lemma card_bikeSetAll (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) :
    (bikeSetAll D ℓ).card =
      ∑ e ∈ D.edges, (closedWalkAll D ℓ e.x₁).card * (closedWalkAll D ℓ e.x₂).card := by
  rw [bikeSetAll, Finset.card_sigma]
  exact Finset.sum_congr rfl (fun e _ => Finset.card_product ..)

/-- The constant of a chain of `n` `PolyRel`-steps each of constant `C`. -/
noncomputable def cycConst (k : ℕ) (C : ℝ) : ℕ → ℝ
  | 0 => max C 1
  | (n + 1) => transConst k (cycConst k C n) C

@[simp] lemma cycConst_zero (k : ℕ) (C : ℝ) : cycConst k C 0 = max C 1 := rfl

@[simp] lemma cycConst_succ (k : ℕ) (C : ℝ) (n : ℕ) :
    cycConst k C (n + 1) = transConst k (cycConst k C n) C := rfl

lemma one_le_cycConst (k : ℕ) (C : ℝ) : 1 ≤ cycConst k C 0 := le_max_right _ _

lemma cycConst_pos (k : ℕ) {C : ℝ} (hC : 0 < C) (n : ℕ) : 0 < cycConst k C n := by
  induction n with
  | zero => simp only [cycConst_zero]; exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  | succ m ih =>
      rw [cycConst_succ]
      exact transConst_pos ih hC

lemma le_cycConst_succ (k : ℕ) {C : ℝ} (hC : 0 < C) (n : ℕ) :
    cycConst k C n ≤ cycConst k C (n + 1) := by
  rw [cycConst_succ]
  exact le_transConst_self (cycConst_pos k hC n) hC

/-- The intermediate dilation factor `A_j = ∏_{j' < j} U_{j'} · ∏_{j' ≥ j} V_{j'}` of the
telescoping of the edge relations around a cycle. -/
noncomputable def cycFac (ℓ : ℕ) (V U : Fin ℓ → ℕ) (j : ℕ) : ℕ :=
  (∏ j' ∈ Finset.univ.filter (fun j' : Fin ℓ => j'.val < j), U j') *
    (∏ j' ∈ Finset.univ.filter (fun j' : Fin ℓ => j ≤ j'.val), V j')

/-- The dilation factor that carries the `j`-th edge relation to the `j`-th intermediate
interval: `A_j / V_j = ∏_{j' < j} U_{j'} · ∏_{j' > j} V_{j'}`. -/
noncomputable def aaV (ℓ : ℕ) (V U : Fin ℓ → ℕ) (j : Fin ℓ) : ℕ :=
  (∏ j' ∈ Finset.univ.filter (fun j' : Fin ℓ => j'.val < j.val), U j') *
    (∏ j' ∈ Finset.univ.filter (fun j' : Fin ℓ => j.val < j'.val), V j')

/-- The bicycles of the full graph one of whose cycles is nearly degenerate (with constant
`C₀`); the "candidate tuples" of the counting. -/
noncomputable def candSet (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) (N C₀ P₁ : ℝ) :
    Finset (Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) :=
  (bikeSetAll D ℓ).filter (fun t =>
    |((walkProdV D ℓ t.2.1 : ℕ) : ℝ) - ((walkProdU D ℓ t.2.1 : ℕ) : ℝ)| ≤ C₀ * P₁ ^ ℓ / N ∧
    |((walkProdV D ℓ t.2.2 : ℕ) : ℝ) - ((walkProdU D ℓ t.2.2 : ℕ) : ℝ)| ≤ C₀ * P₁ ^ ℓ / N)

/-- A bicycle is good if both its cycles are non-degenerate and its common prime set is large. -/
def goodBike (N c₅ P₁ δ : ℝ) (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ)
    (t : Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) : Prop :=
  ¬ degenerateAt N c₅ P₁ D ℓ t.2.1 ∧ ¬ degenerateAt N c₅ P₁ D ℓ t.2.2 ∧
    veryGoodAt D 0 ℓ δ t


/-- The primes `q ∈ [P₂/2, P₂]` for which a bicycle belongs to `bikeSet D q ℓ`: `q` lies in the
prime set of the middle edge and in the `q`-adjacency of every step of both cycles.  For a
bicycle of `bikeSetAll` this is *exactly* the set of `q` with `t ∈ bikeSet D q ℓ`. -/
noncomputable def bikePrimesQ (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ)
    (t : Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) : Finset ℕ :=
  (primesIn (P₂ / 2) P₂).filter (fun q => q ∈ edgeS D t.1 ∧
    (∀ j : Fin ℓ, GAdjQ D q (t.2.1 j.castSucc) (t.2.1 j.succ)) ∧
    (∀ j : Fin ℓ, GAdjQ D q (t.2.2 j.castSucc) (t.2.2 j.succ)))

/-- A bicycle is *very good* if the set of primes supporting it is large. -/
def veryGoodQ (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) (δ : ℝ)
    (t : Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) : Prop :=
  δ * pi0 P₂ < ((bikePrimesQ D ℓ t).card : ℝ)

/-- A bicycle of the full graph is good if both cycles are non-degenerate (with constant `c₅`,
relative to `N`) and it is very good. -/
def goodBikeQ (N c₅ δ : ℝ) (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ)
    (t : Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) : Prop :=
  ¬ degenerateAt N c₅ P₁ D ℓ t.2.1 ∧ ¬ degenerateAt N c₅ P₁ D ℓ t.2.2 ∧ veryGoodQ D ℓ δ t


/-- The bicycles of `bikeSet D q ℓ` that are good. -/
noncomputable def goodBikeSet (D : QuadData k f c C X L P₁ P₂) (q ℓ : ℕ) (N c₅ δ : ℝ) :
    Finset (Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) := by
  classical
  exact (bikeSet D q ℓ).filter (fun t => goodBikeQ N c₅ δ D ℓ t)

end Work.BMF
