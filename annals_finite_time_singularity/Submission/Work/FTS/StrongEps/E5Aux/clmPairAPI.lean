/-
Copyright: work module for the Elgindi finite-time singularity project.

# The canonical identification `ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)` and the Fréchet derivative
of an uncurried two-variable function

The target lemma `Work.FTS.StrongEps.E5Aux.contDiffOn_two_of_locUnif_slots` proves that a
locally uniform limit of `C²` functions (whose `D_zⁱD_θ^j`-slots converge locally uniformly
for `i + j ≤ 2`) is `C²`.  The proof runs through Mathlib's
`hasFDerivAt_of_tendstoLocallyUniformlyOn`: the Fréchet derivative of an uncurried
two-variable function `u : ℝ → ℝ → ℝ` at a point `p` is the pair of its two partial
derivatives, i.e. `fderiv ℝ (uncurry u) p = clmPair (∂_z u p, ∂_θ u p)`.

This file provides that identification (`fderiv_uncurry_eq_clmPair`), the extensionality
lemma that makes it usable (`clm_eq_of_fst_snd`), the transfer of locally uniform
convergence through `clmPair`, and a small utility (`tlu_const`) for constant sequences.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter Set

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false

/-- The canonical linear isomorphism `ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)`,
`(a,b) ↦ ((x,y) ↦ a * x + b * y)`, packaged as a continuous linear map. -/
def clmPair : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ (ContinuousLinearMap.fst ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ))
    + ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℝ))

theorem clmPair_apply (a b x y : ℝ) : clmPair (a, b) (x, y) = a * x + b * y := by
  simp only [clmPair, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  show x * a + y * b = a * x + b * y
  ring

@[simp] theorem clmPair_fst (a b : ℝ) : clmPair (a, b) (1, 0) = a := by
  rw [clmPair_apply]; ring

@[simp] theorem clmPair_snd (a b : ℝ) : clmPair (a, b) (0, 1) = b := by
  rw [clmPair_apply]; ring

/-- Two continuous linear functionals on `ℝ × ℝ` that agree on the two basis vectors agree. -/
theorem clm_eq_of_fst_snd {L M : (ℝ × ℝ) →L[ℝ] ℝ} (h1 : L (1, 0) = M (1, 0))
    (h2 : L (0, 1) = M (0, 1)) : L = M := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by
    ext <;> simp
  rw [hv, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, h2]

/-- **The Fréchet derivative of an uncurried two-variable function** is the pair of its
partial derivatives. -/
theorem fderiv_uncurry_eq_clmPair {u : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry u) p) :
    fderiv ℝ (Function.uncurry u) p
      = clmPair (Work.Spaces.pz u p.1 p.2, Work.Spaces.pth u p.1 p.2) := by
  refine clm_eq_of_fst_snd ?_ ?_
  · rw [clmPair_fst]
    exact (Work.Spaces.pz_eq_fderiv h).symm
  · rw [clmPair_snd]
    exact (Work.Spaces.pth_eq_fderiv h).symm

/-- Locally uniform convergence passes through the continuous linear map `clmPair`. -/
theorem tendstoLocallyUniformlyOn_clmPair {A B : ℕ → ℝ × ℝ → ℝ} {a b : ℝ × ℝ → ℝ}
    {s : Set (ℝ × ℝ)}
    (hA : TendstoLocallyUniformlyOn A a Filter.atTop s)
    (hB : TendstoLocallyUniformlyOn B b Filter.atTop s) :
    TendstoLocallyUniformlyOn (fun n p => clmPair (A n p, B n p))
      (fun p => clmPair (a p, b p)) Filter.atTop s :=
  (ContinuousLinearMap.uniformContinuous clmPair).comp_tendstoLocallyUniformlyOn
    (hA.prodMk hB)

/-- A constant sequence converges locally uniformly to its value. -/
theorem tlu_const {α β : Type*} [TopologicalSpace α] [UniformSpace β] (g : α → β)
    (s : Set α) :
    TendstoLocallyUniformlyOn (fun _ : ℕ => g) g Filter.atTop s := by
  intro u hu x _
  exact ⟨Set.univ, Filter.univ_mem,
    Filter.Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩

end Work.FTS.StrongEps.E5Aux
