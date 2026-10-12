import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The permutation action commutes with the graph point

`graphPoint N L F` is the pair `(F, ∇F)` attached to a smooth test function `F`
supported in the open box, as an element of the ambient space
`Amb N = L²(Conf N) × ∏_{j : GIdx N} L²(Conf N)`.

The permutation `σ` of the particles acts on `Amb N` by `permAmb N σ`, and on
test functions by `permTest N L σ`.  This module proves the compatibility of
the two actions:

`permAmb N σ (graphPoint N L F) = graphPoint N L (permTest N L σ F)`,

i.e. `σ · (F, ∇F) = (σ · F, ∇(σ · F))`.  The function parts agree because
`permLp` is a composition with the measure preserving map `tauPerm σ`; the
gradient parts agree by the chain rule, since `tauPerm σ` is the continuous
linear map `actPermL N σ = actPerm N σ`, whose derivative at every point is
itself, together with the index identity
`actPermL N σ (kcDir N i k) = kcDir N (σ.symm i) k`.
-/

open MeasureTheory Filter
open Work.BoseSym
open Submission.BoseGases (kcDir actPerm actPermL)
open scoped ContDiff

namespace Work.BoseSym.Perm

/-- On test functions, the composition with the measure preserving particle
permutation `tauPerm σ` is the same operation as `permLp N σ`, at the level of
`MemLp.toLp`. -/
lemma permLp_toLp {N : ℕ} (σ : Equiv.Perm (Fin N)) {f : Conf N → ℝ} (hf : MemLp f 2 (volC N)) :
    permLp N σ (MemLp.toLp f hf)
      = MemLp.toLp (fun x => f (tauPerm N σ x))
          (hf.comp_measurePreserving (measurePreserving_tauPerm N σ)) := by
  apply Lp.ext
  have hT := (measurePreserving_tauPerm N σ).quasiMeasurePreserving
  refine (permLp_coeFn σ (MemLp.toLp f hf)).trans ?_
  refine (hT.ae_eq (MemLp.coeFn_toLp hf)).trans ?_
  exact (MemLp.coeFn_toLp _).symm

/-- The linear map `actPermL N σ` of the corpus is the particle permutation
`tauPerm N σ`. -/
lemma actPermL_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Conf N) :
    actPermL N σ x = tauPerm N σ x := rfl

/-- The particle permutation `tauPerm σ` permutes the coordinate directions by
`σ.symm`: `tauPerm σ (kcDir N i k) = kcDir N (σ.symm i) k`. -/
lemma tauPerm_kcDir {N : ℕ} (σ : Equiv.Perm (Fin N)) (i : Fin N) (k : Fin 3) :
    tauPerm N σ (kcDir N i k) = kcDir N (σ.symm i) k := by
  ext j
  simp only [kcDir, tauPerm, Function.update_apply]
  by_cases h : j = σ.symm i
  · subst h
    simp
  · have h2 : σ j ≠ i := by
      intro hh
      apply h
      rw [← hh, Equiv.symm_apply_apply]
    simp [h, h2]

/-- The chain rule for the particle permutation: differentiating `F ∘ tauPerm σ`
in the coordinate direction `(i,k)` gives the derivative of `F` at the permuted
point in the permuted direction `(σ.symm i, k)`. -/
lemma fderiv_tauPerm_dir {N : ℕ} (σ : Equiv.Perm (Fin N)) {F : Conf N → ℝ}
    (hF : ContDiff ℝ ∞ F) (x : Conf N) (i : Fin N) (k : Fin 3) :
    fderiv ℝ (fun y => F (tauPerm N σ y)) x (kcDir N i k)
      = fderiv ℝ F (tauPerm N σ x) (kcDir N (σ.symm i) k) := by
  have hT : HasFDerivAt (fun y : Conf N => tauPerm N σ y) (actPermL N σ) x :=
    ContinuousLinearMap.hasFDerivAt (actPermL N σ)
  have hFd : HasFDerivAt F (fderiv ℝ F (tauPerm N σ x)) (tauPerm N σ x) :=
    (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun y : Conf N => F (tauPerm N σ y))
      ((fderiv ℝ F (tauPerm N σ x)) ∘SL (actPermL N σ)) x := hFd.comp x hT
  rw [hcomp.fderiv]
  rw [ContinuousLinearMap.comp_apply]
  congr 1
  ext j
  simp only [kcDir, actPermL, actPerm, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, Function.update_apply]
  by_cases h : j = σ.symm i
  · subst h
    simp
  · have h2 : σ j ≠ i := by
      intro hh
      apply h
      rw [← hh, Equiv.symm_apply_apply]
    simp [h, h2]

/-- The permutation action on the ambient space commutes with taking the graph
point of a test function. -/
theorem graphPoint_permTest {N : ℕ} {L : ℝ} (σ : Equiv.Perm (Fin N)) (F : testSub N L) :
    permAmb N σ (graphPoint N L F) = graphPoint N L (permTest N L σ F) := by
  apply Prod.ext
  · simp only [permAmb_fst, graphPoint]
    rw [permLp_toLp]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.refl _ _)
  · funext j
    obtain ⟨i, k⟩ := j
    simp only [permAmb_snd, graphPoint]
    rw [permLp_toLp]
    apply MemLp.toLp_congr
    filter_upwards with x
    exact (fderiv_tauPerm_dir σ F.2.1 x i k).symm

end Work.BoseSym.Perm
