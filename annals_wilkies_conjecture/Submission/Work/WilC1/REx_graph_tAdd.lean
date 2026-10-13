import Mathlib
import Submission.Work.WilC1.Defs
import Submission.Work.WilC1.REx_preimage
import Submission.Work.WilC1.REx_inter
import Submission.Work.WilC1.REx_proj
import Submission.Work.WilC1.REx_union

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC1

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture

/-!
  WilC1 — the graph of a sum of two terms.

  `GraphSet (tAdd a b) ⊆ (ι ⊕ Fin 1) → ℝ` is the graph of the term function of the sum `a + b`:
  the last coordinate equals `Term.realize (x ∘ Sum.inl) a + Term.realize (x ∘ Sum.inl) b`.

  The sum is handled by introducing two fresh witness coordinates `u 0`, `u 1`
  (index type `Fin 2`), so that the ambient space is `(ι ⊕ Fin 1) ⊕ Fin 2`.  In it we intersect

  * the lift of `GraphSet a` along the embedding `addLift 0`, which keeps the coordinates of `ι`,
    keeps the value coordinate and *moves it to the fresh coordinate* `Sum.inr 0`;
  * the same lift of `GraphSet b` along `addLift 1`;
  * the zero set of the addition constraint `value = u 0 + u 1`.

  Projecting the two fresh coordinates away (`REx.existsBlock`) and using that in an additive
  group the equation `v = u 0 + u 1` is solvable for `u` exactly when `v` is arbitrary gives the
  graph of `tAdd a b`.
-/

/-- The embedding of the index type `ι ⊕ Fin 1` (coordinates plus the value coordinate) into
`(ι ⊕ Fin 1) ⊕ Fin k` that keeps the coordinates and the value coordinate in place and sends the
value coordinate `Sum.inr 0` to the fresh coordinate `Sum.inr j`. -/
def addLift {ι : Type*} {k : ℕ} (j : Fin k) : (ι ⊕ Fin 1) → (ι ⊕ Fin 1) ⊕ Fin k :=
  Sum.map Sum.inl (fun _ : Fin 1 => j)

/-- The image of a lifted tuple `Sum.elim x u` reads the value coordinate as `u j`, while the
variables of a term are still read off from `x`. -/
theorem addLift_mem_graphSet {ι : Type*} {k : ℕ} (j : Fin k) (t : LRc.Term ι)
    (x : (ι ⊕ Fin 1) → ℝ) (u : Fin k → ℝ) :
    (Sum.elim x u ∘ addLift j) ∈ GraphSet t ↔ u j = Term.realize (x ∘ Sum.inl) t := by
  have h1 : (Sum.elim x u ∘ addLift j) (Sum.inr 0) = u j := rfl
  have h2 : (Sum.elim x u ∘ addLift j) ∘ Sum.inl = x ∘ Sum.inl := by
    funext i
    rfl
  simp only [Set.mem_ofPred_eq, GraphSet]
  rw [h1, h2]

/-- The graph of a term is `REx`, by induction on the term; the additive case. -/
theorem REx_graph_tAdd {ι : Type*} {a b : WilkiesDesign.CG.LRc.Term ι}
    (ha : REx (ι ⊕ Fin 1) (GraphSet a)) (hb : REx (ι ⊕ Fin 1) (GraphSet b)) :
    REx (ι ⊕ Fin 1) (GraphSet (tAdd a b)) := by
  -- The lift of the graph of `a` to the ambient space with two fresh coordinates.
  have hA : REx ((ι ⊕ Fin 1) ⊕ Fin 2)
      {w : ((ι ⊕ Fin 1) ⊕ Fin 2) → ℝ | w ∘ addLift (0 : Fin 2) ∈ GraphSet a} :=
    REx_preimage (addLift (0 : Fin 2)) ha
  -- The lift of the graph of `b` to the same space, using the other fresh coordinate.
  have hB : REx ((ι ⊕ Fin 1) ⊕ Fin 2)
      {w : ((ι ⊕ Fin 1) ⊕ Fin 2) → ℝ | w ∘ addLift (1 : Fin 2) ∈ GraphSet b} :=
    REx_preimage (addLift (1 : Fin 2)) hb
  -- The equation `value = u 0 + u 1` is a zero set.
  have hC : REx ((ι ⊕ Fin 1) ⊕ Fin 2)
      {w : ((ι ⊕ Fin 1) ⊕ Fin 2) → ℝ |
        w (Sum.inl (Sum.inr 0)) = w (Sum.inr 0) + w (Sum.inr 1)} := by
    refine REx.congr ?_ (REx.zeroSet (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))) -
      MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 2))) -
      MvPolynomial.X (Sum.inl (Sum.inr (1 : Fin 2)))))
    ext w
    simp only [Set.mem_ofPred_eq, rexpEval_sub, rexpEval_X_inl, sub_eq_zero]
    constructor <;> intro h <;> linarith
  have hABC := REx_inter (REx_inter hA hB) hC
  -- Project the two fresh coordinates away.
  refine REx.congr ?_ (hABC.existsBlock (μ := Fin 2))
  ext x
  simp only [Set.mem_ofPred_eq, GraphSet, realize_tAdd]
  constructor
  · -- A witness `u` forces the value coordinate to be the sum of the two values.
    rintro ⟨u, ⟨⟨hA', hB'⟩, hC'⟩⟩
    have e1 : u 0 = Term.realize (x ∘ Sum.inl) a :=
      (addLift_mem_graphSet (0 : Fin 2) a x u).mp hA'
    have e2 : u 1 = Term.realize (x ∘ Sum.inl) b :=
      (addLift_mem_graphSet (1 : Fin 2) b x u).mp hB'
    have hC'' : x (Sum.inr 0) = u 0 + u 1 := by simpa using hC'
    rw [← e1, ← e2]
    exact hC''
  · -- Solve the constraint `x (Sum.inr 0) = u 0 + u 1` by taking the two values as witnesses.
    intro hx
    refine ⟨![Term.realize (x ∘ Sum.inl) a, Term.realize (x ∘ Sum.inl) b], ⟨⟨?_, ?_⟩, ?_⟩⟩
    · exact (addLift_mem_graphSet (0 : Fin 2) a x _).mpr rfl
    · exact (addLift_mem_graphSet (1 : Fin 2) b x _).mpr rfl
    · simpa using hx

end Work.WilC1
