import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.CD.sliceContDiffAt_mem
import Submission.Work.WilG4a.CD.graphFam_param_mem
import Submission.Work.WilG4a.oneDim_nonCk_finite

namespace Work.WilG4a.CD

open WilkiesDesign WilkiesConjecture Work.WilG4a Work.WilG0

/-!
# `slice_bad_finite`

The set of `x` at which the one-variable *slice* `x ↦ f l x` of an `Ω F D (p+2)`-definable
family `f : ℝᵖ × ℝ → ℝ` fails to be `C^j` is finite.

The reduction is to the one-variable result `Work.WilG4a.oneDim_nonCk_finite`.  The slice is a
*constant-parameter* member of the family, so its graph is `Ω`-definable by the
parametrisation lemma `Work.WilG4a.CD.graphFam_param_mem` applied with `k = 0` parameters and
the constant parametrisation `Ψ := fun _ => l`; the graph of `Ψ` is the singleton `{l}`, which
is `Ω`-definable as an intersection of coordinate hyperplanes (`paramGraph_const_mem`).
-/

/-- **The graph of the constant parametrisation `u ↦ l` is `Ω`-definable.**  In the layout of
`paramGraph` (first `k = 0` coordinates the parameter `u`, last `p` the value) this is simply
the singleton `{l}`, i.e. the intersection of the `p` coordinate hyperplanes `z j = l j`.
Format `p + 1`, degree `p` (one hyperplane per coordinate). -/
lemma paramGraph_const_mem (S : SOMin) (p : ℕ) (l : Fin p → ℝ) :
    paramGraph (fun _ : Fin 0 → ℝ => l) ∈ S.Ω (0 + p + 1) p (0 + p) := by
  have hset : paramGraph (fun _ : Fin 0 → ℝ => l) =
      ⋂ j : Fin p, {z : Fin (0 + p) → ℝ | z (Fin.natAdd 0 j) = l j} := by
    ext z
    simp only [mem_paramGraph, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hset]
  have hH : ∀ j : Fin p,
      {z : Fin (0 + p) → ℝ | z (Fin.natAdd 0 j) = l j} ∈ S.Ω (0 + p) 1 (0 + p) := by
    intro j
    have h := S.hyp (0 + p) (MvPolynomial.X (Fin.natAdd 0 j) - MvPolynomial.C (l j))
    have hdeg : (MvPolynomial.X (Fin.natAdd 0 j) - MvPolynomial.C (l j)).totalDegree ≤ 1 :=
      le_trans (MvPolynomial.totalDegree_sub _ _)
        (by simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C])
    have h' := mem_mono h le_rfl hdeg
    simpa [MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero] using h'
  simpa using S.inter (fun _ : Fin p => 1)
    (fun j : Fin p => {z : Fin (0 + p) → ℝ | z (Fin.natAdd 0 j) = l j}) hH

theorem slice_bad_finite (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) {p F D : ℕ}
    (f : (Fin p → ℝ) → ℝ → ℝ) (hf : Work.WilG4a.graphFam f ∈ S.Ω F D (p + 1 + 1)) (l : Fin p → ℝ) (j : ℕ) :
    {x : ℝ | ¬ ContDiffAt ℝ j (fun x : ℝ => f l x) x}.Finite := by
  -- The graph of the slice is `Ω`-definable: pull the family back along the constant
  -- parametrisation `Ψ u = l`.
  obtain ⟨A, B, hAB⟩ := graphFam_param_mem S hcd p 0 F (0 + p + 1)
  have hparam : paramGraph (fun _ : Fin 0 → ℝ => l) ∈ S.Ω (0 + p + 1) p (0 + p) :=
    paramGraph_const_mem S p l
  have hres := hAB D p f (fun _ : Fin 0 → ℝ => l) hf hparam
  have hg' : graphOf (fun x : Fin 1 → ℝ => (fun y : ℝ => f l y) (x 0)) ∈
      S.Ω A (MvPolynomial.eval ![D, p] B) 2 := by
    rw [← graphFam_const (fun y : ℝ => f l y)]
    simpa using hres
  -- Apply the one-variable result to the slice.
  have hfin := oneDim_nonCk_finite S hcd hder (fun y : ℝ => f l y) hg' j
  simpa using hfin

end Work.WilG4a.CD
