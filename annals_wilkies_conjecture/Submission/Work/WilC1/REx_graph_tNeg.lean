import Mathlib
import Submission.Work.WilC1.Defs
import Submission.Work.WilC1.REx_preimage
import Submission.Work.WilC1.REx_inter
import Submission.Work.WilC1.REx_proj
import Submission.Work.WilC1.REx_union

namespace Work.WilC1

open FirstOrder FirstOrder.Language

/-- `REx` is closed under taking the graph of the negated term.

The graph of `tNeg t` is obtained from the graph of `t` by negating the value coordinate.  Rather
than acting on the coordinate block directly (which a pullback along a coordinate map cannot do),
we move to the larger space with a fresh last coordinate `u`: the pullback of `GraphSet t` along
the map which replaces the value coordinate by `u` expresses "the graph of `t` holds with `u` as
value", and intersecting it with the linear condition `u = -x(Inr 0)` forces the original value
coordinate `x(Inr 0)` to be `-(value of t)`.  Projecting the fresh coordinate away gives
`GraphSet (tNeg t)`. -/
theorem REx_graph_tNeg {ι : Type*} {t : WilkiesDesign.CG.LRc.Term ι}
    (h : REx (ι ⊕ Fin 1) (GraphSet t)) : REx (ι ⊕ Fin 1) (GraphSet (tNeg t)) := by
  -- the map replacing the value coordinate of `x` by the fresh coordinate of `u`
  let f : (ι ⊕ Fin 1) → ((ι ⊕ Fin 1) ⊕ Fin 1) :=
    Sum.map (Sum.inl : ι → ι ⊕ Fin 1) (id : Fin 1 → Fin 1)
  -- the linear polynomial `u 0 + x (Inr 0)`
  let Q : MvPolynomial (((ι ⊕ Fin 1) ⊕ Fin 1) ⊕ ((ι ⊕ Fin 1) ⊕ Fin 1)) ℝ :=
    MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1)))
      + MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1))))
  have key_val : ∀ (x : (ι ⊕ Fin 1) → ℝ) (u : Fin 1 → ℝ),
      ((Sum.elim x u) ∘ f) (Sum.inr 0) = u 0 := fun x u => rfl
  have key_inl : ∀ (x : (ι ⊕ Fin 1) → ℝ) (u : Fin 1 → ℝ),
      ((Sum.elim x u) ∘ f) ∘ Sum.inl = x ∘ Sum.inl := fun x u => rfl
  have key_Q : ∀ (x : (ι ⊕ Fin 1) → ℝ) (u : Fin 1 → ℝ),
      rexpEval (Sum.elim x u) Q = u 0 + x (Sum.inr 0) := by
    intro x u
    simp [Q, rexpEval_X_inl]
  -- pull back the graph of `t` along `f`, viewed on the enlarged space
  have hY1 : REx ((ι ⊕ Fin 1) ⊕ Fin 1)
      {W : ((ι ⊕ Fin 1) ⊕ Fin 1) → ℝ | W ∘ f ∈ GraphSet t} := REx_preimage f h
  -- the linear condition `u 0 + x (Inr 0) = 0`
  have hY2 : REx ((ι ⊕ Fin 1) ⊕ Fin 1)
      {W : ((ι ⊕ Fin 1) ⊕ Fin 1) → ℝ | rexpEval W Q = 0} := REx.zeroSet Q
  have hY := REx_inter hY1 hY2
  have hZ := REx.existsBlock (μ := Fin 1) hY
  refine REx.congr ?_ hZ
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, GraphSet]
  constructor
  · rintro ⟨u, hg, hq⟩
    rw [key_val x u, key_inl x u] at hg
    rw [key_Q x u] at hq
    rw [realize_tNeg]
    linarith
  · intro hx
    rw [realize_tNeg] at hx
    refine ⟨fun _ => Term.realize (x ∘ Sum.inl) t, ?_, ?_⟩
    · simp only [key_val, key_inl]
    · simp only [key_Q]
      linarith

end Work.WilC1
