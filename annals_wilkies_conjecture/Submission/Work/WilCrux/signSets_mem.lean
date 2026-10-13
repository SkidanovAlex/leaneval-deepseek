import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4a.derivGraph_mem
import Submission.Work.WilG4a.lip_loci_defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG4a.domLoci_mem
import Submission.Work.WilG4a.lipschitz_chart_good_on

/-!
# `Work.WilCrux.signSets_mem`

For a one-variable function `h : ℝ → ℝ` whose graph in `ℝ²` is `Ω F D 2`-definable, the two
sign loci `{x | 0 < deriv h x}` and `{x | deriv h x < 0}` are `Ω a (b.eval D) 1`-definable, with
a format `a` and a degree polynomial `b` depending only on `F`.

The work is done by `Work.WilG4a.domLoci_mem` applied to the zero-parameter family
`f := fun (_ : Fin 0 → ℝ) (x : ℝ) => h x`, whose graph is exactly the graph of `h` and whose
slice derivative is `deriv h`.  The only thing left is the identification of
`Work.WilG4a.posSet f` / `Work.WilG4a.negSet f` with the two sign loci of `deriv h`.
-/

set_option autoImplicit false

namespace Work.WilCrux

open WilkiesDesign

/-- `∃ s, HasDerivAt h s x ∧ 0 < s` is exactly `0 < deriv h x`.  (When `h` is not
differentiable at `x`, `deriv h x = 0`, which is not positive.) -/
private lemma exists_pos_hasDerivAt_iff (h : ℝ → ℝ) (x : ℝ) :
    (∃ s : ℝ, HasDerivAt h s x ∧ 0 < s) ↔ 0 < deriv h x := by
  constructor
  · rintro ⟨s, hs, hpos⟩; rwa [hs.deriv]
  · intro hpos
    exact ⟨deriv h x, hasDerivAt_deriv_iff.mpr
      (differentiableAt_of_deriv_ne_zero (ne_of_gt hpos)), hpos⟩

/-- `∃ s, HasDerivAt h s x ∧ s < 0` is exactly `deriv h x < 0`. -/
private lemma exists_neg_hasDerivAt_iff (h : ℝ → ℝ) (x : ℝ) :
    (∃ s : ℝ, HasDerivAt h s x ∧ s < 0) ↔ deriv h x < 0 := by
  constructor
  · rintro ⟨s, hs, hpos⟩; rwa [hs.deriv]
  · intro hpos
    exact ⟨deriv h x, hasDerivAt_deriv_iff.mpr
      (differentiableAt_of_deriv_ne_zero (ne_of_lt hpos)), hpos⟩

/-- The graph of `h` is the graph of the zero-parameter family `fun _ x => h x`. -/
private lemma graphFam_zero (h : ℝ → ℝ) :
    Work.WilG4a.graphFam (fun (_ : Fin 0 → ℝ) (x : ℝ) => h x)
      = graphOf (fun z : Fin 1 → ℝ => h (z 0)) := by
  unfold Work.WilG4a.graphFam
  congr 1

/-- The slice function of the zero-parameter family `fun _ x => h x` is `h`. -/
private lemma sliceFun_zero (h : ℝ → ℝ) (z : Fin 1 → ℝ) :
    Work.WilG4a.sliceFun (fun (_ : Fin 0 → ℝ) (x : ℝ) => h x) z = h := by
  funext y
  simp [Work.WilG4a.sliceFun, Work.WilG4a.famFun]

/-- `posSet` of the zero-parameter family is the positivity locus of `deriv h`. -/
private lemma posSet_zero (h : ℝ → ℝ) :
    Work.WilG4a.posSet (fun (_ : Fin 0 → ℝ) (x : ℝ) => h x)
      = {z : Fin 1 → ℝ | 0 < deriv h (z 0)} := by
  ext z
  have hlast : (z : Fin 1 → ℝ) (Fin.last 0) = z 0 := by congr 1
  simp only [Work.WilG4a.posSet, Set.mem_ofPred_eq, Work.WilG4a.IsSliceDeriv,
    sliceFun_zero h z, hlast]
  exact exists_pos_hasDerivAt_iff h (z 0)

/-- `negSet` of the zero-parameter family is the negativity locus of `deriv h`. -/
private lemma negSet_zero (h : ℝ → ℝ) :
    Work.WilG4a.negSet (fun (_ : Fin 0 → ℝ) (x : ℝ) => h x)
      = {z : Fin 1 → ℝ | deriv h (z 0) < 0} := by
  ext z
  have hlast : (z : Fin 1 → ℝ) (Fin.last 0) = z 0 := by congr 1
  simp only [Work.WilG4a.negSet, Set.mem_ofPred_eq, Work.WilG4a.IsSliceDeriv,
    sliceFun_zero h z, hlast]
  exact exists_neg_hasDerivAt_iff h (z 0)

theorem signSets_mem (S : WilkiesDesign.SOMin) (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) (h : ℝ → ℝ),
        WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => h (x 0)) ∈ S.Ω F D 2 →
          {z : Fin 1 → ℝ | 0 < deriv h (z 0)} ∈ S.Ω a (b.eval D) 1 ∧
          {z : Fin 1 → ℝ | deriv h (z 0) < 0} ∈ S.Ω a (b.eval D) 1 := by
  obtain ⟨a, b, hmem⟩ := Work.WilG4a.domLoci_mem S 0 F
  refine ⟨a, b, ?_⟩
  intro D h hh
  have hg : Work.WilG4a.graphFam (fun (_ : Fin 0 → ℝ) (x : ℝ) => h x) ∈ S.Ω F D 2 := by
    rw [graphFam_zero h]; exact hh
  obtain ⟨-, hpos, hneg⟩ := hmem D
    (f := fun (_ : Fin 0 → ℝ) (x : ℝ) => h x) (g := fun (_ : Fin 0 → ℝ) (x : ℝ) => h x)
    hg hg
  constructor
  · rw [← posSet_zero h]; exact hpos
  · rw [← negSet_zero h]; exact hneg

end Work.WilCrux
