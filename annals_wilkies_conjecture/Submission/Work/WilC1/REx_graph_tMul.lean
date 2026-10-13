import Mathlib
import Submission.Work.WilC1.Defs
import Submission.Work.WilC1.REx_preimage
import Submission.Work.WilC1.REx_inter
import Submission.Work.WilC1.REx_proj
import Submission.Work.WilC1.REx_union

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC1

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture

/-!
  WilC1 — the graph of a product of two terms is `REx`.

  The graph of `tMul a b` in `ℝ^{ι ⊕ Fin 1}` is the set of tuples `x` with
  `x (Sum.inr 0) = A(x) · B(x)`, where `A(x)`, `B(x)` are the values of `a`, `b` at `x ∘ Sum.inl`.

  The proof extends the index type to `τ := (ι ⊕ Fin 1) ⊕ Fin 2`, whose last two coordinates
  `u₀ = w (Sum.inr 0)`, `u₁ = w (Sum.inr 1)` serve as registers for `A` and `B`:
  * `{w | u₀ = A(w)}` and `{w | u₁ = B(w)}` are pullbacks of `GraphSet a`, `GraphSet b` along the
    maps `spreadMap 0`, `spreadMap 1` (which copy the `ι`-coordinates and move the last coordinate
    of the source into the register `u_j`) — `REx` by `REx_preimage`;
  * `{w | w (Sum.inl (Sum.inr 0)) = u₀ · u₁}` is a zero set — `REx` by `REx.zeroSet`.
  Intersecting (`REx_inter`) and projecting the registers away (`REx.existsBlock`) gives the graph,
  the final set equality being pure `Sum.elim` bookkeeping. -/

/-- The `ι`-tuple of original coordinates of an extended tuple `w : ℝ^{(ι ⊕ Fin 1) ⊕ Fin 2}`. -/
private def baseTuple {ι : Type*} (w : ((ι ⊕ Fin 1) ⊕ Fin 2) → ℝ) : ι → ℝ :=
  fun i => w (Sum.inl (Sum.inl i))

/-- `spreadMap j` keeps the `ι`-coordinates of a tuple in `ℝ^{ι ⊕ Fin 1}` and moves its last
coordinate to the `j`-th new slot. -/
private def spreadMap {ι : Type*} (j : Fin 2) : (ι ⊕ Fin 1) → (ι ⊕ Fin 1) ⊕ Fin 2 :=
  Sum.elim (fun i : ι => Sum.inl (Sum.inl i)) (fun _ : Fin 1 => Sum.inr j)

/-- Reading off the base coordinates of a tuple split as `Sum.elim x u`. -/
private theorem baseTuple_elim {ι : Type*} (x : (ι ⊕ Fin 1) → ℝ) (u : Fin 2 → ℝ) :
    baseTuple (Sum.elim x u) = (fun i => x (Sum.inl i)) := rfl

/-- The pullback of `GraphSet t` along `spreadMap j` is the set of extended tuples whose `j`-th
register holds the value of `t` at the base coordinates. -/
private theorem preimage_GraphSet_spreadMap {ι : Type*} (t : LRc.Term ι) (j : Fin 2) :
    {w : ((ι ⊕ Fin 1) ⊕ Fin 2) → ℝ | w ∘ spreadMap j ∈ GraphSet t}
      = {w | w (Sum.inr j) = Term.realize (baseTuple w) t} := by
  ext w
  have h1 : (w ∘ spreadMap j) (Sum.inr (0 : Fin 1)) = w (Sum.inr j) := by
    simp only [Function.comp_apply, spreadMap, Sum.elim_inr]
  have h2 : (w ∘ spreadMap j) ∘ (Sum.inl : ι → ι ⊕ Fin 1) = baseTuple w := rfl
  simp only [GraphSet, Set.mem_ofPred_eq, h1, h2]

theorem REx_graph_tMul {ι : Type*} {a b : WilkiesDesign.CG.LRc.Term ι}
    (ha : REx (ι ⊕ Fin 1) (GraphSet a)) (hb : REx (ι ⊕ Fin 1) (GraphSet b)) :
    REx (ι ⊕ Fin 1) (GraphSet (tMul a b)) := by
  -- the two register conditions, as pullbacks of the two graphs
  have hA : REx ((ι ⊕ Fin 1) ⊕ Fin 2)
      {w : ((ι ⊕ Fin 1) ⊕ Fin 2) → ℝ |
        w (Sum.inr (0 : Fin 2)) = Term.realize (baseTuple w) a} :=
    REx.congr (preimage_GraphSet_spreadMap a 0) (REx_preimage (spreadMap (ι := ι) 0) ha)
  have hB : REx ((ι ⊕ Fin 1) ⊕ Fin 2)
      {w : ((ι ⊕ Fin 1) ⊕ Fin 2) → ℝ |
        w (Sum.inr (1 : Fin 2)) = Term.realize (baseTuple w) b} :=
    REx.congr (preimage_GraphSet_spreadMap b 1) (REx_preimage (spreadMap (ι := ι) 1) hb)
  -- the multiplication condition, as a zero set
  have hZ : REx ((ι ⊕ Fin 1) ⊕ Fin 2)
      {w : ((ι ⊕ Fin 1) ⊕ Fin 2) → ℝ |
        w (Sum.inl (Sum.inr (0 : Fin 1))) = w (Sum.inr (0 : Fin 2)) * w (Sum.inr (1 : Fin 2))} := by
    refine REx.congr ?_ (REx.zeroSet (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))) -
      MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 2))) * MvPolynomial.X (Sum.inl (Sum.inr (1 : Fin 2)))))
    ext w
    simp only [Set.mem_ofPred_eq, rexpEval_sub, rexpEval_mul, rexpEval_X_inl, sub_eq_zero]
  have hAll : REx ((ι ⊕ Fin 1) ⊕ Fin 2)
      ({w : ((ι ⊕ Fin 1) ⊕ Fin 2) → ℝ |
        w (Sum.inr (0 : Fin 2)) = Term.realize (baseTuple w) a} ∩
      {w : ((ι ⊕ Fin 1) ⊕ Fin 2) → ℝ |
        w (Sum.inr (1 : Fin 2)) = Term.realize (baseTuple w) b} ∩
      {w : ((ι ⊕ Fin 1) ⊕ Fin 2) → ℝ |
        w (Sum.inl (Sum.inr (0 : Fin 1))) = w (Sum.inr (0 : Fin 2)) * w (Sum.inr (1 : Fin 2))}) :=
    REx_inter (REx_inter hA hB) hZ
  refine REx.congr ?_ (hAll.existsBlock (μ := Fin 2))
  -- project the two registers away: the surviving tuples are exactly the graph of `tMul a b`
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, GraphSet, Sum.elim_inl, Sum.elim_inr,
    realize_tMul]
  constructor
  · rintro ⟨u, ⟨h1, h2⟩, h3⟩
    rw [h1, h2] at h3
    exact h3
  · intro h
    refine ⟨![Term.realize (fun i => x (Sum.inl i)) a, Term.realize (fun i => x (Sum.inl i)) b],
      ⟨?_, ?_⟩, ?_⟩
    · rw [baseTuple_elim]; simp
    · rw [baseTuple_elim]; simp
    · show x (Sum.inr 0) = Term.realize (x ∘ Sum.inl) a * Term.realize (x ∘ Sum.inl) b
      exact h

end Work.WilC1
