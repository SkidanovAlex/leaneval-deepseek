import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.sl3_pivot_bounded
import Submission.Work.LT.sl3_diagonal_eq_prod

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/LT/DESIGN.md first (the orchestrator's design; your lemma is one node of its DAG). Shared definitions: Submission/Work/LT/Defs.lean (namespace Work.LT) — do NOT edit it; if you need a new shared definition, put it in your own file. Siblings are being proved in parallel; import them when they land.

# sl3_bounded_generation — guidance

Gaussian elimination in `SL₃` over the field `ZMod p`.
* Mathlib: `Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec` gives
  `M = L.prod * diagonal D * L'.prod` with `L, L'` lists of `TransvectionStruct`s, and the
  construction's lists have length bounded in terms of `n = 3` only (inspect
  `listTransvecCol`, `listTransvecRow`: each has length `n - 1`, plus the recursive block). If
  extracting the length bound from the Mathlib proof is awkward, redo elimination by hand for `3×3`
  (at most ~12 transvections to reach a diagonal matrix).
* Diagonal of determinant 1: `diag(a, a⁻¹, 1) = E₁₂(a-1)… ` — the Whitehead identity writes it as a
  product of 4 elementary matrices; `diag(a,b,c)` with `abc = 1` is a product of two such.
* Convert `TransvectionStruct` `(i,j,c)` to `sl3E p i j c` (`i ≠ j` from the structure); the
  determinant-1 subtype coercion is `Subtype.ext` + `Matrix.SpecialLinearGroup.coe_mul`/`coe_prod`.
Any explicit `L` (say 40) is fine. Expected size: 200–500 lines.
-/

namespace Work.LT

open Matrix

/-! ### Coercion plumbing

The subtype `Matrix.SpecialLinearGroup (Fin 3) (ZMod p)` is a `def` of a subtype, so pushing the
coercion to matrices through products needs the option below (as Mathlib itself does in
`SpecialLinearGroup.lean`). -/

set_option backward.isDefEq.respectTransparency false in
/-- `sl3E` is `Matrix.SpecialLinearGroup.transvection` away from the diagonal. -/
lemma sl3E_eq_transvection {p : ℕ} (i j : Fin 3) (hij : i ≠ j) (t : ZMod p) :
    sl3E p i j t = Matrix.SpecialLinearGroup.transvection hij t := by
  refine Subtype.ext ?_
  rw [sl3E, dite_eq_right hij]
  rfl

/-- The coercion of a product of transvections is the product of the underlying matrices. -/
lemma coe_prod_tSL {p : ℕ} (L : List (Matrix.TransvectionStruct (Fin 3) (ZMod p))) :
    (((L.map Matrix.TransvectionStruct.toSpecialLinearGroup).prod :
        Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))
      = (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  rw [← Matrix.SpecialLinearGroup.coeMonoidHom_apply, map_list_prod, List.map_map]
  rfl

/-- A list of transvections encoded as triples multiplies to the same element as the list of
`TransvectionStruct`s it comes from. -/
lemma map_triple_sl3E {p : ℕ} (L : List (Matrix.TransvectionStruct (Fin 3) (ZMod p))) :
    ((L.map (fun t => (t.i, t.j, t.c))).map (fun x => sl3E p x.1 x.2.1 x.2.2)).prod =
      (L.map Matrix.TransvectionStruct.toSpecialLinearGroup).prod := by
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [sl3E_eq_transvection t.i t.j t.hij t.c]
  exact (Matrix.TransvectionStruct.toSpecialLinearGroup_def t).symm

/-- **Bounded elementary generation of `SL₃` over a field.** Every element of `SL₃(ℤ/p)` is a
product of at most `L` elementary matrices `E_ij(t)` (`i ≠ j`, `t` arbitrary), with `L`
independent of `p` (Gaussian elimination). -/
theorem sl3_bounded_generation :
    ∃ L : ℕ, ∀ (p : ℕ) [Fact p.Prime] (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
      ∃ l : List (Fin 3 × Fin 3 × ZMod p), l.length ≤ L ∧ (∀ x ∈ l, x.1 ≠ x.2.1) ∧
        g = (l.map (fun x => sl3E p x.1 x.2.1 x.2.2)).prod := by
  refine ⟨100, fun p hp g => ?_⟩
  -- Gaussian elimination: at most 20 row operations and 20 column operations bring `g` to a
  -- diagonal matrix `diagonal D`.
  obtain ⟨L, L', D, hLD, hLlen, hL'len⟩ :=
    sl3_pivot_bounded (g : Matrix (Fin 3) (Fin 3) (ZMod p))
  -- Every transvection has determinant one, so `D 0 * D 1 * D 2 = 1`.
  have hdet : Matrix.det (Matrix.diagonal D) = 1 := by
    have h := congrArg Matrix.det hLD
    simp only [Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod,
      Matrix.SpecialLinearGroup.det_coe, mul_one] at h
    exact h.symm
  -- A determinant-one diagonal matrix is a product of at most 12 elementary matrices.
  obtain ⟨dl, hdllen, hdlnz, hdl⟩ := sl3_diagonal_eq_prod p D hdet
  -- Invert the elimination: `g = A * diagonal D * B` with `A`, `B` (short) products of
  -- transvections.
  let Arl : List (Fin 3 × Fin 3 × ZMod p) :=
    (L.reverse.map Matrix.TransvectionStruct.inv).map fun t => (t.i, t.j, t.c)
  let Brl : List (Fin 3 × Fin 3 × ZMod p) :=
    (L'.reverse.map Matrix.TransvectionStruct.inv).map fun t => (t.i, t.j, t.c)
  refine ⟨Arl ++ dl ++ Brl, ?_, ?_, ?_⟩
  · -- length
    have h1 : Arl.length = L.length := by simp [Arl]
    have h2 : Brl.length = L'.length := by simp [Brl]
    simp only [List.length_append, h1, h2]
    omega
  · -- every factor is off-diagonal
    intro x hx
    simp only [List.mem_append, Arl, Brl, List.mem_map] at hx
    rcases hx with (⟨t, -, rfl⟩ | hx) | ⟨t, -, rfl⟩
    · exact t.hij
    · exact hdlnz x hx
    · exact t.hij
  · have hArl : ((L.reverse.map Matrix.TransvectionStruct.inv).map
          Matrix.TransvectionStruct.toSpecialLinearGroup).prod =
        (Arl.map (fun x => sl3E p x.1 x.2.1 x.2.2)).prod := by
      simp only [Arl]
      exact (map_triple_sl3E _).symm
    have hBrl : ((L'.reverse.map Matrix.TransvectionStruct.inv).map
          Matrix.TransvectionStruct.toSpecialLinearGroup).prod =
        (Brl.map (fun x => sl3E p x.1 x.2.1 x.2.2)).prod := by
      simp only [Brl]
      exact (map_triple_sl3E _).symm
    have hgroup : ((L.map Matrix.TransvectionStruct.toSpecialLinearGroup).prod) * g *
        ((L'.map Matrix.TransvectionStruct.toSpecialLinearGroup).prod) =
        (⟨Matrix.diagonal D, hdet⟩ : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) := by
      refine Subtype.ext ?_
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          coe_prod_tSL, coe_prod_tSL]
      exact hLD
    have hA : ((L.reverse.map Matrix.TransvectionStruct.inv).map
          Matrix.TransvectionStruct.toSpecialLinearGroup).prod *
        (L.map Matrix.TransvectionStruct.toSpecialLinearGroup).prod = 1 := by
      refine Subtype.ext ?_
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
        coe_prod_tSL, coe_prod_tSL, List.map_map]
      exact Matrix.TransvectionStruct.reverse_inv_prod_mul_prod L
    have hB : (L'.map Matrix.TransvectionStruct.toSpecialLinearGroup).prod *
        ((L'.reverse.map Matrix.TransvectionStruct.inv).map
          Matrix.TransvectionStruct.toSpecialLinearGroup).prod = 1 := by
      refine Subtype.ext ?_
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
        coe_prod_tSL, coe_prod_tSL, List.map_map]
      exact Matrix.TransvectionStruct.prod_mul_reverse_inv_prod L'
    have hg : g = ((L.reverse.map Matrix.TransvectionStruct.inv).map
          Matrix.TransvectionStruct.toSpecialLinearGroup).prod * ⟨Matrix.diagonal D, hdet⟩ *
        ((L'.reverse.map Matrix.TransvectionStruct.inv).map
          Matrix.TransvectionStruct.toSpecialLinearGroup).prod := by
      rw [eq_inv_of_mul_eq_one_left hA, eq_inv_of_mul_eq_one_right hB, ← hgroup]
      group
    calc g = (Arl.map (fun x => sl3E p x.1 x.2.1 x.2.2)).prod *
          (dl.map (fun x => sl3E p x.1 x.2.1 x.2.2)).prod *
          (Brl.map (fun x => sl3E p x.1 x.2.1 x.2.2)).prod := by
          rw [hg, hdl, hArl, hBrl]
      _ = ((Arl.map (fun x => sl3E p x.1 x.2.1 x.2.2)) ++
            (dl.map (fun x => sl3E p x.1 x.2.1 x.2.2)) ++
            (Brl.map (fun x => sl3E p x.1 x.2.1 x.2.2))).prod := by
          rw [List.prod_append, List.prod_append, mul_assoc]
      _ = ((Arl ++ dl ++ Brl).map (fun x => sl3E p x.1 x.2.1 x.2.2)).prod := by
          rw [List.map_append, List.map_append]

end Work.LT
