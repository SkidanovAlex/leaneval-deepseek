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
# The Dirichlet energy space `Hsub N L` is invariant under permutations

This module proves that the permutation action `permAmb N σ` on the ambient
space `Amb N` maps the Dirichlet energy space `Hsub N L` into itself.

The proof has two ingredients.

* `permAmb N σ` is (the underlying function of) a continuous linear map of
  `Amb N`.  It therefore suffices to check invariance on the generating set
  `Set.range (graphPoint N L)` of `Hsub N L` and to pass to the topological
  closure.

* On the generators,
  `permAmb N σ (graphPoint N L F) = graphPoint N L (permTest N L σ F)`,
  where `permTest N L σ F` is the permuted test function: the function part is
  immediate from `Lp.toLp_compMeasurePreserving`, and the gradient part is the
  chain rule for `F ∘ tauPerm σ`, whose derivative is
  `fderiv F (tauPerm σ x) ∘ actPermL N σ`; the linear map `actPermL N σ` sends
  the coordinate direction `kcDir N i k` to `kcDir N (σ⁻¹ i) k`.
-/

namespace Work.BoseSym.Perm

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real ContDiff ENNReal NNReal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The permutation action as a continuous linear map -/

/-- The permutation action on `L²` as a continuous linear map (it is in fact an
isometry); its underlying function is `permLp N σ`. -/
noncomputable def permLpCLM (N : ℕ) (σ : Equiv.Perm (Fin N)) : L2 N →L[ℝ] L2 N :=
  (Lp.compMeasurePreservingₗᵢ ℝ (tauPerm N σ)
    (measurePreserving_tauPerm N σ)).toContinuousLinearMap

/-- The permutation action on the ambient space, as a continuous linear map. -/
noncomputable def permAmbCLM (N : ℕ) (σ : Equiv.Perm (Fin N)) : Amb N →L[ℝ] Amb N :=
  ContinuousLinearMap.prod
    ((permLpCLM N σ).comp (ContinuousLinearMap.fst ℝ (L2 N) (GIdx N → L2 N)))
    (ContinuousLinearMap.pi (fun j : GIdx N =>
      (permLpCLM N σ).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : GIdx N => L2 N)
        (σ.symm j.1, j.2)).comp (ContinuousLinearMap.snd ℝ (L2 N) (GIdx N → L2 N)))))

/-- The continuous linear map `permAmbCLM N σ` has the same underlying function
as `permAmb N σ`. -/
@[simp] lemma permAmbCLM_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (p : Amb N) :
    permAmbCLM N σ p = permAmb N σ p := rfl

/-! ## Permuting an `L²` element given by `MemLp.toLp` -/

/-- Composing a measure-preserving map with an element of `L²` written as
`MemLp.toLp` composes the representing function. -/
lemma permLp_toLp {N : ℕ} (σ : Equiv.Perm (Fin N)) {f : Conf N → ℝ} (hf : MemLp f 2 (volC N)) :
    permLp N σ (MemLp.toLp f hf) =
      (hf.comp_measurePreserving (measurePreserving_tauPerm N σ)).toLp
        (fun x => f (tauPerm N σ x)) :=
  Lp.toLp_compMeasurePreserving hf (measurePreserving_tauPerm N σ)

/-! ## The chain rule for `F ∘ tauPerm σ` -/

/-- The derivative of `y ↦ f (tauPerm σ y)` is the derivative of `f` at
`tauPerm σ x`, composed with the linear map `actPermL N σ` implementing the
relabelling of the particles. -/
lemma fderiv_comp_tauPerm {N : ℕ} (σ : Equiv.Perm (Fin N)) {f : Conf N → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : Conf N) :
    fderiv ℝ (fun y => f (tauPerm N σ y)) x =
      (fderiv ℝ f (tauPerm N σ x)).comp (actPermL N σ) := by
  have hL : HasFDerivAt (⇑(actPermL N σ)) (actPermL N σ) x := ContinuousLinearMap.hasFDerivAt _
  have hf' : HasFDerivAt f (fderiv ℝ f (⇑(actPermL N σ) x)) (⇑(actPermL N σ) x) :=
    (hf.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  exact (hf'.comp x hL).fderiv

/-- The linear relabelling `actPermL N σ` sends the coordinate direction
`kcDir N i k` to `kcDir N (σ⁻¹ i) k`. -/
lemma actPermL_kcDir {N : ℕ} (σ : Equiv.Perm (Fin N)) (i : Fin N) (k : Fin 3) :
    (actPermL N σ) (kcDir N i k) = kcDir N (σ.symm i) k := by
  show (fun j : Fin N => (Function.update (0 : Conf N) i (kcStdBasis k)) (σ j))
      = Function.update (0 : Conf N) (σ.symm i) (kcStdBasis k)
  exact Function.update_comp_equiv (0 : Conf N) σ i (kcStdBasis k)

/-- Chain rule paired with `actPermL_kcDir`: the coordinate derivative of
`f ∘ tauPerm σ` in the direction of particle `i`, coordinate `k` is the
coordinate derivative of `f` at the permuted point, in the direction of
particle `σ⁻¹ i`. -/
lemma fderiv_comp_tauPerm_kcDir {N : ℕ} (σ : Equiv.Perm (Fin N)) {f : Conf N → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : Conf N) (i : Fin N) (k : Fin 3) :
    fderiv ℝ (fun y => f (tauPerm N σ y)) x (kcDir N i k) =
      fderiv ℝ f (tauPerm N σ x) (kcDir N (σ.symm i) k) := by
  rw [fderiv_comp_tauPerm σ hf x, ContinuousLinearMap.comp_apply, actPermL_kcDir]

/-! ## The permutation action on the generating graph points -/

/-- The permutation action sends the graph point of `F` to the graph point of
the permuted test function. -/
lemma permAmb_graphPoint {N : ℕ} {L : ℝ} (σ : Equiv.Perm (Fin N)) (F : testSub N L) :
    permAmb N σ (graphPoint N L F) = graphPoint N L (permTest N L σ F) := by
  apply Prod.ext
  · simp only [permAmb_fst, graphPoint]
    exact permLp_toLp σ
      (memLp_of_contDiff_hasCompactSupport F.2.1 (hasCompactSupport_of_testFun F.2))
  · funext j
    simp only [permAmb_snd, graphPoint, permTest]
    rw [permLp_toLp]
    apply MemLp.toLp_congr
    filter_upwards with x
    exact (fderiv_comp_tauPerm_kcDir σ F.2.1 x j.1 j.2).symm

/-- A generator of the Dirichlet space stays in the Dirichlet space under the
permutation action. -/
lemma permAmb_graphPoint_mem {N : ℕ} {L : ℝ} (σ : Equiv.Perm (Fin N)) (F : testSub N L) :
    permAmb N σ (graphPoint N L F) ∈ Hsub N L := by
  rw [permAmb_graphPoint σ F]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨permTest N L σ F, rfl⟩)

/-- **The Dirichlet energy space is invariant under permutations of the
particles.** -/
theorem permAmb_mem_Hsub {N : ℕ} {L : ℝ} (σ : Equiv.Perm (Fin N)) {p : Amb N}
    (hp : p ∈ Hsub N L) : permAmb N σ p ∈ Hsub N L := by
  have hle : Submodule.span ℝ (Set.range (graphPoint N L)) ≤
      Submodule.comap (permAmbCLM N σ).toLinearMap (Hsub N L) := by
    rw [Submodule.span_le]
    rintro q ⟨F, rfl⟩
    exact Submodule.mem_comap.mpr (permAmb_graphPoint_mem σ F)
  have hclosed : IsClosed ((Submodule.comap (permAmbCLM N σ).toLinearMap (Hsub N L)) :
      Set (Amb N)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (permAmbCLM N σ).continuous
  have hle2 : Hsub N L ≤
      Submodule.comap (permAmbCLM N σ).toLinearMap (Hsub N L) := by
    show (Submodule.span ℝ (Set.range (graphPoint N L))).topologicalClosure ≤ _
    exact Submodule.topologicalClosure_minimal _ hle hclosed
  have hp' : permAmbCLM N σ p ∈ Hsub N L := hle2 hp
  rwa [permAmbCLM_apply] at hp'

end

end Work.BoseSym.Perm
