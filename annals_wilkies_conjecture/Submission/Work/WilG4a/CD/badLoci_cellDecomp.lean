/-
  WilG4a/CD -- a cell decomposition adapted to the first `j + 1` bad loci of a family.

  Given a family `f` whose graph is `Ω F0 D`-definable, the `SharpDeriv` hypothesis makes every
  bad locus `badLocus f i` (`= ` the complement of the interior of the `C^i` locus, in
  coordinates `(parameters, x)`) `Ω`-definable with format independent of `i` and degree
  `b₀.eval ![D, i]`.  Feeding the `j + 1` sets `badLocus f 0, …, badLocus f j` into sharp cell
  decomposition (`exists_cell_partition_refining`, with index type `Fin (j + 1)`) produces a
  partition of `ℝ^{p+1}` into cells each of which lies wholly inside or wholly outside every one
  of them.

  The only work is bookkeeping of the format/degree polynomials: the cell count bound
  `b₁.eval ![b₀.eval ![D,j], j+1]` and the cell degree bound `c₁.eval (b₀.eval ![D,j])` have to
  be merged into a single polynomial `b` in `(D, j)`.  This is what the two lemmas
  `exists_eval_comp` / `exists_eval_shift` (from `Bounds`) and `mvpoly_eval_eval2` provide; the
  sum of the resulting polynomials dominates both, using that all coefficients are natural
  numbers so that the evaluations are nonnegative and monotone for the `Ω`-degree.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilE9.Ift.OneShot.mvpoly_eval_eval2
import Submission.Work.WilG4a.CD.badLocusUnion_mem
import Submission.Work.WilG4a.exists_cell_partition_refining

namespace Work.WilG4a.CD

/-- Substituting a natural multivariate polynomial into a `ℕ`-polynomial commutes with
evaluation: `(Polynomial.eval₂ C b₀ c).eval v = c.eval (b₀.eval v)`.  (Re-exported in the
`Fin 2` shape used below.) -/
theorem eval_eval₂_C (b₀ : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ) (D j : ℕ) :
    MvPolynomial.eval ![D, j] (Polynomial.eval₂ MvPolynomial.C b₀ c) =
      c.eval (MvPolynomial.eval ![D, j] b₀) :=
  Work.WilE9.Ift.OneShot.mvpoly_eval_eval2 b₀ c

theorem badLoci_cellDecomp (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        ∃ (m : ℕ) (κ : Fin m → Set (Fin (p + 1) → ℝ)),
          m ≤ MvPolynomial.eval ![D, j] b ∧
          (∀ σ, κ σ ∈ S.Ω a (MvPolynomial.eval ![D, j] b) (p + 1)) ∧
          (∀ σ, WilkiesDesign.IsCell (p + 1) (κ σ)) ∧
          (∀ z : Fin (p + 1) → ℝ, ∃ σ, z ∈ κ σ) ∧
          (∀ (i : ℕ), i ≤ j → ∀ σ, Disjoint (κ σ) (Work.WilG4a.badLocus f i) ∨ κ σ ⊆ Work.WilG4a.badLocus f i) := by
  classical
  -- The bad loci themselves are `Ω`-definable with format `a₀` and degree `b₀.eval ![D, i]`.
  obtain ⟨a₀, b₀, hb₀⟩ := Work.WilG4a.badLocus_mem S hder p F0
  -- Sharp cell decomposition for the format `a₀` in dimension `p + 1`.
  obtain ⟨a₁, b₁, c₁, hb₁⟩ := Work.WilG4a.exists_cell_partition_refining S hcd a₀ (p + 1)
  -- `d₁` realises the shift `j ↦ j + 1` of the count polynomial `b₁` …
  obtain ⟨d₁, hd₁⟩ := Work.WilG4a.exists_eval_shift b₁
  -- … and `d₂` realises the substitution of the degree polynomial `b₀` in its first variable.
  obtain ⟨d₂, hd₂⟩ := Work.WilG4a.exists_eval_comp d₁ b₀
  -- The merged polynomial: `d₂` dominates the count bound, `eval₂ C b₀ c₁` the degree bound.
  refine ⟨a₁, Polynomial.eval₂ MvPolynomial.C b₀ c₁ + d₂, ?_⟩
  intro D j f hf
  -- All `badLocus f i`, `i ≤ j`, are `Ω a₀ (b₀.eval ![D,j])` by monotonicity of the degree.
  have hfam : ∀ i : Fin (j + 1),
      Work.WilG4a.badLocus f (i : ℕ) ∈ S.Ω a₀ (MvPolynomial.eval ![D, j] b₀) (p + 1) := by
    intro i
    refine Work.WilG4a.mono_D_le S (hb₀ D (i : ℕ) hf) ?_
    refine eval_le_eval_of_le (f := ![D, (i : ℕ)]) (g := ![D, j]) (fun s => ?_) b₀
    fin_cases s
    · simp
    · exact Nat.lt_succ_iff.mp i.isLt
  obtain ⟨m, hm, κ, hmem, hcell, hcover, _hdisj, href⟩ :=
    hb₁ (MvPolynomial.eval ![D, j] b₀) (Fin (j + 1))
      (fun i : Fin (j + 1) => Work.WilG4a.badLocus f (i : ℕ)) hfam
  refine ⟨m, κ, ?_, ?_, hcell, hcover, ?_⟩
  · -- the count bound `m ≤ b₁.eval ![b₀.eval ![D,j], j+1] = d₂.eval ![D,j]`
    have hshift : b₁.eval ![MvPolynomial.eval ![D, j] b₀, j + 1] = d₂.eval ![D, j] :=
      (hd₁ (MvPolynomial.eval ![D, j] b₀) j).trans (hd₂ D j)
    have hm' : m ≤ d₂.eval ![D, j] := by
      simpa only [Fintype.card_fin, hshift] using hm
    calc m ≤ d₂.eval ![D, j] := hm'
      _ ≤ (Polynomial.eval₂ MvPolynomial.C b₀ c₁ + d₂).eval ![D, j] := by
          rw [MvPolynomial.eval_add]
          exact Nat.le_add_left _ _
  · -- the cell degree bound `c₁.eval (b₀.eval ![D,j]) ≤ (eval₂ C b₀ c₁ + d₂).eval ![D,j]`
    intro σ
    refine Work.WilG4a.mono_D_le S (hmem σ) ?_
    rw [MvPolynomial.eval_add, eval_eval₂_C]
    exact Nat.le_add_right _ _
  · -- refinement of each individual bad locus
    intro i hi σ
    exact href ⟨i, Nat.lt_succ_of_le hi⟩ σ

end Work.WilG4a.CD
