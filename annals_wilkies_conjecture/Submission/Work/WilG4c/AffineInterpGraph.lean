import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.AffineInterpDefs
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG4a.affine_chart_graph_mem
import Submission.Work.WilG4a.affine_comb_graph_mem

set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## The projection identity

The construction of `AffineInterpGraph` mirrors `Work.WilG4a.affine_chart_graph_mem`: the
interpolant is obtained in `ℝ^{m+4}`, with coordinates `(params, t, y, u, v)` where `u` and
`v` record `lo` and `hi` of the parameters, as the projection along the last two coordinates
of

  `acgSetA m lo ∩ acgSetB m hi ∩ ipRelSet m`,

the relation `ipRelSet m` being `y = u + (v - u) * t`.  The projection identity is stated in
the `graphOf` spelling used by the target. -/

theorem ipProjInterp (m : ℕ) (lo hi : (Fin m → ℝ) → ℝ) :
    Work.WilG0.projLastIter (m + 2) 2
        (Work.WilG4a.acgSetA m lo ∩ Work.WilG4a.acgSetB m hi ∩ ipRelSet m) =
      graphOf (fun z : Fin (m + 1) → ℝ =>
        lo (Fin.init z) + (hi (Fin.init z) - lo (Fin.init z)) * z (Fin.last m)) := by
  -- `Work.WilG4a.graphFam f` is by definition the graph of `z ↦ f (Fin.init z) (z (Fin.last _))`
  have hRHS : graphOf (fun z : Fin (m + 1) → ℝ =>
        lo (Fin.init z) + (hi (Fin.init z) - lo (Fin.init z)) * z (Fin.last m)) =
      Work.WilG4a.graphFam (fun l (t : ℝ) => lo l + (hi l - lo l) * t) := rfl
  rw [hRHS, Work.WilG0.projLastIter_eq]
  ext x
  rw [Work.WilG4a.mem_graphFam]
  constructor
  · rintro ⟨w, hw⟩
    rw [Set.mem_inter_iff, Set.mem_inter_iff] at hw
    obtain ⟨⟨hA, hB⟩, hR⟩ := hw
    rw [Work.WilG4a.mem_acgSetA, Work.WilG4a.acgSnocU, Work.WilG4a.acgSnocParFun,
      Work.WilG4a.acgParFun] at hA
    rw [Work.WilG4a.mem_acgSetB, Work.WilG4a.acgSnocV, Work.WilG4a.acgSnocParFun,
      Work.WilG4a.acgParFun] at hB
    rw [mem_ipRelSet, Work.WilG4a.acgSnocY, Work.WilG4a.acgSnocU, Work.WilG4a.acgSnocV,
      Work.WilG4a.acgSnocT] at hR
    rw [← hA, ← hB]
    exact hR
  · intro hx
    rw [← Work.WilG4a.acgParFun] at hx
    set w : Fin 2 → ℝ := ![
      lo (fun i : Fin m => x (Fin.castAdd 2 i)),
      hi (fun i : Fin m => x (Fin.castAdd 2 i))] with hwdef
    have hw0 : w 0 = lo (fun i : Fin m => x (Fin.castAdd 2 i)) := by simp [hwdef]
    have hw1 : w 1 = hi (fun i : Fin m => x (Fin.castAdd 2 i)) := by simp [hwdef]
    refine ⟨w, ?_⟩
    rw [Set.mem_inter_iff, Set.mem_inter_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Work.WilG4a.mem_acgSetA, Work.WilG4a.acgSnocU, Work.WilG4a.acgSnocParFun]
      exact hw0
    · rw [Work.WilG4a.mem_acgSetB, Work.WilG4a.acgSnocV, Work.WilG4a.acgSnocParFun]
      exact hw1
    · rw [mem_ipRelSet, Work.WilG4a.acgSnocY, Work.WilG4a.acgSnocU, Work.WilG4a.acgSnocV,
        Work.WilG4a.acgSnocT, hw0, hw1]
      exact hx

/-- **Affine interpolation of two `Ω`-graphs, with a uniform degree transform.**
Given `Ω`-definable graphs of `lo, hi : ℝ^m → ℝ` at format `F` and degree `eval ![D,1] b`,
the graph of `z ↦ lo (Fin.init z) + (hi (Fin.init z) - lo (Fin.init z)) * z (Fin.last m)` (a
subset of `ℝ^{m+2}`) is `Ω`-definable at format `F + a` and degree
`eval ![D,1] (C 2 * b + C c)`, with `a, c` independent of `F`, `D`, `b`. -/
theorem AffineInterpGraph (S : SOMin) (m : ℕ) :
    ∃ (a c : ℕ), ∀ (F D : ℕ) (b : MvPolynomial (Fin 2) ℕ) (lo hi : (Fin m → ℝ) → ℝ),
      graphOf lo ∈ S.Ω F (MvPolynomial.eval ![D, 1] b) (m + 1) →
      graphOf hi ∈ S.Ω F (MvPolynomial.eval ![D, 1] b) (m + 1) →
      graphOf (fun z : Fin (m + 1) → ℝ =>
          lo (Fin.init z) + (hi (Fin.init z) - lo (Fin.init z)) * (z (Fin.last m))) ∈
        S.Ω (F + a) (MvPolynomial.eval ![D, 1] (MvPolynomial.C 2 * b + MvPolynomial.C c))
          (m + 1 + 1) := by
  refine ⟨5 * m + 17, 6, ?_⟩
  intro F D b lo hi hlo hhi
  -- the two graph pieces, obtained by substituting `acgIotaA m`, `acgIotaB m`
  have hA : Work.WilG4a.acgSetA m lo ∈
      S.Ω (F + 2 * ((m + 4) + (m + 1)) + 1) (MvPolynomial.eval ![D, 1] b + 2) (m + 4) :=
    Work.WilG4a.subst_mem_aux S (Work.WilG4a.acgIotaA m) hlo
  have hB : Work.WilG4a.acgSetB m hi ∈
      S.Ω (F + 2 * ((m + 4) + (m + 1)) + 1) (MvPolynomial.eval ![D, 1] b + 2) (m + 4) :=
    Work.WilG4a.subst_mem_aux S (Work.WilG4a.acgIotaB m) hhi
  -- the relation `y = u + (v - u) * t`, at degree `2`
  have hR : ipRelSet m ∈ S.Ω (m + 4) 2 (m + 4) := ipRelSet_mem S m
  have hR2 : ipRelSet m ∈ S.Ω (F + 2 * ((m + 4) + (m + 1)) + 1 + 1) 2 (m + 4) :=
    Work.WilG5.mem_mono hR _ 2 (by omega) le_rfl
  have hI : (Work.WilG4a.acgSetA m lo ∩ Work.WilG4a.acgSetB m hi ∩ ipRelSet m) ∈
      S.Ω (F + 2 * ((m + 4) + (m + 1)) + 1 + 1 + 1)
        ((MvPolynomial.eval ![D, 1] b + 2) + (MvPolynomial.eval ![D, 1] b + 2) + 2)
        (m + 4) :=
    Work.WilG4a.inter_mem2 (Work.WilG4a.inter_mem2 hA hB) hR2
  -- projection along the last two coordinates
  have hP := Work.WilG0.projLastIter_mem S (m + 2) 2 _ _
    (Work.WilG4a.acgSetA m lo ∩ Work.WilG4a.acgSetB m hi ∩ ipRelSet m) hI
  rw [ipProjInterp m lo hi] at hP
  -- bookkeeping: the degree is exactly `2 * eval ![D,1] b + 6`
  have hcoef : MvPolynomial.eval ![D, 1] (MvPolynomial.C 2 * b + MvPolynomial.C 6) =
      2 * MvPolynomial.eval ![D, 1] b + 6 := by
    simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [hcoef]
  exact Work.WilG5.mem_mono hP (F + (5 * m + 17))
    (2 * MvPolynomial.eval ![D, 1] b + 6) (by omega) (by omega)

end Work.WilG4c
