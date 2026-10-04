import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Faà di Bruno for `pdVec`

`pdVec s l f x` is the `s`-fold partial derivative of `f` at `x` along the coordinate directions
`l 0, …, l (s-1)`.  By `Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv` it equals
`iteratedFDeriv ℝ s f x (fun j => Pi.single (l j) 1)`.

This file proves the Faà di Bruno formula for such derivatives, i.e. the chain rule for the
composition with a vector valued map `V : (ι → ℝ) → (Fin m → ℂ)` and an outer map
`Φ : (Fin m → ℂ) → ℂ`, summing over the ordered set partitions of `{0, …, s-1}`
(`OrderedFinpartition s`, the indexing of the Faà di Bruno formula in Mathlib):

`iteratedFDeriv ℝ s (Φ ∘ V) x v = ∑ c, (iteratedFDeriv ℝ c.length Φ (V x))
    (fun i => iteratedFDeriv ℝ (c.partSize i) V x (v ∘ c.emb i))`.

The proof combines Mathlib's analytic Faà di Bruno formula (`iteratedFDeriv_comp`, which expresses
the iterated derivative of a composition through `FormalMultilinearSeries.taylorComp`) with the
componentwise description of `iteratedFDeriv` for maps into a finite product
(`ContinuousLinearMap.iteratedFDeriv_comp_left`, applied to the coordinate projections).
-/

namespace Work.Diff.STE.Comp3

/-- The `j`-th component of the `k`-th iterated derivative of `V` is the `k`-th iterated
derivative of the `j`-th component of `V`.  (`ι` is finite so that `ι → ℝ` is a normed space.) -/
theorem iteratedFDeriv_component_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (k : ℕ) (V : (ι → ℝ) → (Fin m → ℂ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (x : ι → ℝ) (w : Fin k → (ι → ℝ)) :
    (fun j : Fin m => iteratedFDeriv ℝ k (fun y => V y j) x w) = iteratedFDeriv ℝ k V x w := by
  funext j
  have h2 : iteratedFDeriv ℝ k (fun y => V y j) x
      = (ContinuousLinearMap.proj j).compContinuousMultilinearMap (iteratedFDeriv ℝ k V x) := by
    have h := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (ContinuousLinearMap.proj j) (f := V) (x := x) hV.contDiffAt (i := k)
      (WithTop.coe_le_coe.mpr le_top : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    convert h using 2
    funext y
    rfl
  rw [h2, ContinuousLinearMap.compContinuousMultilinearMap_coe]
  rfl

/-- Faà di Bruno formula for iterated Fréchet derivatives of a composition `Φ ∘ V` of a scalar
function `Φ` on `Fin m → ℂ` with a curve `V`, evaluated on an arbitrary `s`-tuple of vectors:
the sum over the ordered set partitions of `Fin s`. -/
theorem iteratedFDeriv_comp_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (s : ℕ) (Φ : (Fin m → ℂ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (V : (ι → ℝ) → (Fin m → ℂ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (x : ι → ℝ)
    (v : Fin s → (ι → ℝ)) :
    iteratedFDeriv ℝ s (fun y => Φ (V y)) x v
      = ∑ c : OrderedFinpartition s,
          (iteratedFDeriv ℝ c.length Φ (V x))
            (fun i => iteratedFDeriv ℝ (c.partSize i) V x (v ∘ c.emb i)) := by
  have h1 : iteratedFDeriv ℝ s (fun y => Φ (V y)) x
      = (ftaylorSeries ℝ Φ (V x)).taylorComp (ftaylorSeries ℝ V x) s :=
    iteratedFDeriv_comp (g := Φ) (f := V) (hΦ.contDiffAt) (hV.contDiffAt)
      (WithTop.coe_le_coe.mpr le_top : ((s : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  rw [h1]
  simp only [FormalMultilinearSeries.taylorComp, ftaylorSeries, sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply]

theorem faaDiBruno_vec {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (s : ℕ) (Φ : (Fin m → ℂ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (V : (ι → ℝ) → (Fin m → ℂ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (x : ι → ℝ) (l : Fin s → ι) :
    Work.Diff.STE.pdVec s l (fun y => Φ (V y)) x
      = ∑ c : OrderedFinpartition s,
          (iteratedFDeriv ℝ c.length Φ (V x))
            (fun i => (fun j : Fin m =>
              iteratedFDeriv ℝ (c.partSize i) (fun y => V y j) x
                (fun j' => Pi.single (l (c.emb i j')) 1))) := by
  rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv s (fun y => Φ (V y)) (hΦ.comp hV) x l]
  rw [iteratedFDeriv_comp_sum s Φ hΦ V hV x (fun j => Pi.single (l j) 1)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  congr 1
  funext i
  exact (iteratedFDeriv_component_apply (c.partSize i) V hV x
    ((fun j : Fin s => Pi.single (l j) (1 : ℝ)) ∘ c.emb i)).symm

end Work.Diff.STE.Comp3
