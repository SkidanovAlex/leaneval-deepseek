import Mathlib
import Submission.Work.WilG4c.StepTupleDefs
import Submission.Work.WilG4c.clampFamGraph
import Submission.Work.WilG4c.SurrogateSliceFamGraphMem
import Submission.Work.WilG4c.famGraph_gam_eq_graphOf
import Submission.Work.WilG4c.SlicedSurrogateDefs

namespace Work.WilG4c

/-- **The `Ω`-membership of the members of the tuple of BNZ §5.4.**  The tuple
`Work.WilkG4c.tupleFunc F γs` indexes (via `Sum.inl`) the clamped choice coordinates
`clamp01 (γs i m l x ι)` and (via `Sum.inr c'`) the sliced surrogates
`surrogateSlice p n (F i) (clamp ∘ γs i m) (canonList c'.1) l x`.  If every choice coordinate
`γs i m` has an `Ω`-bounded graph (format `A0`, degree `eval ![D,r] B0`) and every member
`F i` has an `Ω`-bounded graph, then every tuple member has an `Ω`-bounded graph, with format
`A` and degree `eval ![D,r] B` independent of the index and of `k`. -/
theorem tupleFamGraphMem (S : WilkiesDesign.SOMin) (hcd : WilkiesDesign.SOMin.SharpCD S)
    (hder : WilkiesDesign.SOMin.SharpDeriv S) (p n : ℕ) :
    ∀ (A0 : ℕ) (B0 : MvPolynomial (Fin 2) ℕ) (F0 : ℕ),
      ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (D r k : ℕ) (F : Work.WilkG4c.Family k p (n + 1))
        (γs : (i : Fin k) → Work.WilkG4c.MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ)),
        (∀ (i : Fin k) (m : Work.WilkG4c.MIdx n r) (ι : Fin n),
          WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
            γs i m (fun a : Fin p => w (Fin.castSucc a)) (w (Fin.last p)) ι)
            ∈ S.Ω A0 (MvPolynomial.eval ![D, r] B0) (p + 1 + 1)) →
        (∀ i : Fin k, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
        ∀ x : Work.WilkG4c.TupleIdx k n r,
          WilkiesDesign.CG.famGraph (Work.WilkG4c.tupleFunc F γs x)
            ∈ S.Ω A (MvPolynomial.eval ![D, r] B) (p + 1 + 1) := by
  intro A0 B0 F0
  -- the clamp device for `(l,u) ↦ γs i m l (u 0) j`
  obtain ⟨a, c, hclamp⟩ := clampFamGraph S p 1
  -- the sliced surrogate of `F i` along the (clamped) curve
  obtain ⟨A1, B1, K, hSurr⟩ := SurrogateSliceFamGraphMem S hcd hder p n F0
  refine ⟨max (A0 + a) (A1 + n * (A0 + a)),
    (B0 + MvPolynomial.C c)
      + (B1 + MvPolynomial.C n * (B0 + MvPolynomial.C c) + MvPolynomial.C K), ?_⟩
  intro D r k F γs hγ hF x
  -- the degree of the constructed polynomial, evaluated
  have hBval : MvPolynomial.eval ![D, r]
      ((B0 + MvPolynomial.C c)
        + (B1 + MvPolynomial.C n * (B0 + MvPolynomial.C c) + MvPolynomial.C K))
      = (MvPolynomial.eval ![D, r] B0 + c)
        + (MvPolynomial.eval ![D, r] B1
            + n * (MvPolynomial.eval ![D, r] B0 + c) + K) := by
    simp [MvPolynomial.eval_add, MvPolynomial.eval_mul]
  rcases x with ⟨i, m, s⟩
  -- the *unclamped* curve coordinates, as one-variable families
  have hGmem : ∀ j : Fin n,
      WilkiesDesign.CG.famGraph
        (fun (l : Fin p → ℝ) (x : Fin 1 → ℝ) => γs i m l (x 0) j)
        ∈ S.Ω A0 (MvPolynomial.eval ![D, r] B0) (p + 1 + 1) := by
    intro j
    rw [Work.WilG4c.famGraph_gam_eq_graphOf p n (γs i m) j]
    exact hγ i m j
  -- the *clamped* curve coordinates: the clamp device, uniformly in the coordinate
  have hcl : ∀ j : Fin n,
      WilkiesDesign.CG.famGraph
        (fun (l : Fin p → ℝ) (x : Fin 1 → ℝ) => Work.WilG4c.clamp01 (γs i m l (x 0) j))
        ∈ S.Ω (A0 + a) (MvPolynomial.eval ![D, r] B0 + c) (p + 1 + 1) :=
    hclamp (F0 := A0) (D := MvPolynomial.eval ![D, r] B0)
      (F := fun (j : Fin n) (l : Fin p → ℝ) (x : Fin 1 → ℝ) => γs i m l (x 0) j) hGmem
  rcases s with ι | c'
  · -- the clamped coordinate `(l,u) ↦ clamp01 (γs i m l (u 0) ι)`
    rw [Work.WilkG4c.tupleFunc_inl]
    refine Work.WilG5.mem_mono (S := S) (hcl ι) _ _ (le_max_left _ _) ?_
    rw [hBval]
    exact Nat.le_add_right _ _
  · -- the sliced surrogate `(l,u) ↦ surrogateSlice p n (F i) (clamp ∘ γs i m) M l (u 0)`
    rw [Work.WilkG4c.tupleFunc_inr]
    have hlen : (Work.WilkG4c.canonList (fun i => (c'.1 i : ℕ))).length ≤ r := by
      rw [Work.WilkG4c.canonList_length]
      exact c'.2
    have hsur := hSurr (A0 + a) (MvPolynomial.eval ![D, r] B0 + c) D r (F i)
      (Work.WilkG4c.gclOf γs i m) (Work.WilkG4c.canonList (fun i => (c'.1 i : ℕ)))
      (hF i) hcl hlen
    refine Work.WilG5.mem_mono (S := S) hsur _ _ (le_max_right _ _) ?_
    rw [hBval]
    exact Nat.le_add_left _ _

end Work.WilG4c
