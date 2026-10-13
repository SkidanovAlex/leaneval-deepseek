/-
  WilG4c / `StepTupleBig` — the padded tuple of BNZ §5.4 and its `Ω`-graph bounds.

  `Work.WilkG4c.tupleFamBig` pads the tuple of §5.4 to the explicit polynomial member count
  `tupleSizeBig k n r = k (r+1)^(n+1) (n + (r+1)^n)` (the constant `1/2` on the padding
  indices).  This is what lets `F1Affine` be applied at a `k` that is a polynomial *expression*
  in `k, r`, so that its count polynomial becomes an explicit substitution with no monotonicity
  argument.  This file records the three facts the assembly reads off the padded tuple: the
  `Ω`-membership of the graphs, the values in `(0,1)`, and the passage of `F1Affine`'s output
  back to `H1Chart`.
-/
import Mathlib
import Submission.Work.WilG4c.StepTupleDefs
import Submission.Work.WilG4c.tupleFamGraphMem
import Submission.Work.WilG4c.StepH1Out
import Submission.Work.WilG4c.LipDefs
import Submission.Work.WilG4c.SlicedSurrogateDefs
import Submission.Work.WilG4c.sliceGraph_mem_gen
import Submission.Work.WilG4c.StepHigherDefs

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- The graph of a constant function is `Ω`-bounded with format `p + m + 1` and degree `1`. -/
theorem famGraph_const_mem (S : SOMin) (p m : ℕ) (c : ℝ) :
    CG.famGraph (fun (_ : Fin p → ℝ) (_ : Fin m → ℝ) => c)
      ∈ S.Ω (p + m + 1) 1 (p + m + 1) :=
  Work.WilG4c.graphOf_const_mem (S := S) (m := p + m) c

/-- **The `Ω`-graph bounds of the padded tuple.** -/
theorem tupleFamBig_graph_mem (S : SOMin) (hcd : SOMin.SharpCD S) (hder : SOMin.SharpDeriv S)
    (p n : ℕ) :
    ∀ (A0 : ℕ) (B0 : MvPolynomial (Fin 2) ℕ) (F0 : ℕ),
      ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (D r k : ℕ) (F : Family k p (n + 1))
        (γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ)),
        (∀ (i : Fin k) (m : MIdx n r) (ι : Fin n),
          graphOf (fun w : Fin (p + 1) → ℝ =>
            γs i m (fun a : Fin p => w (Fin.castSucc a)) (w (Fin.last p)) ι)
            ∈ S.Ω A0 (MvPolynomial.eval ![D, r] B0) (p + 1 + 1)) →
        (∀ i : Fin k, famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
        ∀ j : Fin (tupleSizeBig k n r),
          famGraph (tupleFamBig F γs j) ∈ S.Ω A (MvPolynomial.eval ![D, r] B) (p + 1 + 1) := by
  intro A0 B0 F0
  obtain ⟨A, B, hT⟩ := Work.WilG4c.tupleFamGraphMem S hcd hder p n A0 B0 F0
  refine ⟨max A (p + 1 + 1), B + MvPolynomial.C 1, ?_⟩
  intro D r k F γs hγs hF j
  rw [tupleFamBig]
  split_ifs with h
  · exact Work.WilG1.Omega.mono (hT D r k F γs hγs hF _) (le_max_left _ _) (by
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_C]
      omega)
  · exact Work.WilG1.Omega.mono (famGraph_const_mem S p 1 (1 / 2))
      (le_max_right _ _) (by
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_C]
      omega)

/-- **The values of the padded tuple lie in `(0,1)`.** -/
theorem tupleFamBig_val {k p n r : ℕ} {F : Family k p (n + 1)}
    {γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ)}
    (hY : Work.WilkG4c.YBound F r) :
    ∀ (j : Fin (tupleSizeBig k n r)) (l : Fin p → ℝ) (t : Fin 1 → ℝ),
      t ∈ openCube 1 → tupleFamBig F γs j l t ∈ Set.Ioo (0 : ℝ) 1 := by
  intro j l t ht
  rw [tupleFamBig]
  split_ifs with h
  · obtain ⟨i, m, s⟩ := (Fintype.equivFin (TupleIdx k n r)).symm ⟨(j : ℕ), h⟩
    rcases s with ι | c'
    · rw [tupleFunc_inl]
      exact Work.WilG4c.clamp01_mem _
    · rw [tupleFunc_inr]
      have ht0 : t 0 ∈ Work.WilkG4c.I := by
        have := ht 0
        simpa [WilkiesDesign.openCube, Work.WilkG4c.I] using this
      have hcl : (fun ι : Fin n => Work.WilkG4c.gclOf γs i m l (t 0) ι)
          ∈ WilkiesDesign.openCube n := fun ι => Work.WilG4c.clamp01_mem _
      refine Work.WilkG4c.surrogateSlice_mem_Ioo (M := canonList (fun i => (c'.1 i : ℕ)))
        (fun _ => ?_)
      have hlen : (canonList (fun i => (c'.1 i : ℕ))).length ≤ r := by
        rw [Work.WilkG4c.canonList_length]
        exact c'.2
      have hb := hY i l (t 0) ht0 (canonList (fun i => (c'.1 i : ℕ))).length hlen
        (fun ι => Work.WilkG4c.gclOf γs i m l (t 0) ι) hcl
      refine le_trans ?_ hb
      have h1 := ContinuousMultilinearMap.le_opNorm
        (iteratedFDeriv ℝ (canonList (fun i => (c'.1 i : ℕ))).length
          (Work.WilkG4c.slice (F i l) (t 0))
          (fun ι => Work.WilkG4c.gclOf γs i m l (t 0) ι))
        (fun j => Pi.single ((canonList (fun i => (c'.1 i : ℕ))).get j) 1)
      have h2 : (∏ x : Fin (canonList (fun i => (c'.1 i : ℕ))).length,
          ‖(Pi.single ((canonList (fun i => (c'.1 i : ℕ))).get x) (1 : ℝ)
            : Fin n → ℝ)‖) = 1 := by
        refine Finset.prod_eq_one fun x _ => ?_
        rw [Pi.norm_single, norm_one]
      rw [h2, mul_one] at h1
      exact h1
  · norm_num

/-- **`F1Affine`'s output on the padded tuple yields `H1Chart`.** -/
theorem h1Chart_of_f1affine_big {k p n r : ℕ} {F : Family k p (n + 1)}
    {γs : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ)}
    {Φ₀ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ))}
    (h : ∀ cb ∈ Φ₀,
      (∀ l : Fin p → ℝ, 0 < cb.2 l ∧ 0 ≤ cb.1 l ∧ cb.1 l + cb.2 l ≤ 1) ∧
      ∀ j : Fin (tupleSizeBig k n r), ∀ l : Fin p → ℝ,
        ContDiffOn ℝ (r + 1)
          (fun t : Fin 1 → ℝ => tupleFamBig F γs j l (fun _ => cb.1 l + cb.2 l * t 0))
          (openCube 1) ∧
        ∀ q ≤ r + 1, ∀ t ∈ openCube 1,
          ‖iteratedFDeriv ℝ q
            (fun t : Fin 1 → ℝ => tupleFamBig F γs j l (fun _ => cb.1 l + cb.2 l * t 0)) t‖ ≤ 1) :
    ∀ cb ∈ Φ₀, H1Chart F γs cb.1 cb.2 := by
  intro cb hcb
  obtain ⟨hcond, hmem⟩ := h cb hcb
  refine ⟨hcond, fun x l => ?_⟩
  have hx := hmem ⟨((Fintype.equivFin (TupleIdx k n r)) x : ℕ),
      lt_of_lt_of_le (Fintype.equivFin (TupleIdx k n r) x).isLt (tupleSize_le_big k n r)⟩ l
  rwa [tupleFamBig_eq F γs x] at hx

end Work.WilkG4c
