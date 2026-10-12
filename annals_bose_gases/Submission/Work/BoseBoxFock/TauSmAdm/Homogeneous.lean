import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Module.ModuleTopology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/TauSmAdm/Homogeneous.lean`

Auxiliary material for `Work.BoseBoxFock.tauSm_admissible`.

**Homogeneity of iterated derivatives.**  If `H : E → ℝ` is positively homogeneous of degree `k`
(`H (c • y) = c^k * H y` for `c > 0`) and `C^n` on an open set `s` containing `x` and `t • x`
(`t > 0`), then

  `t^n • D^n H (t • x) = t^k • D^n H x`.

The proof composes the identity `H ∘ (t • ·) = t^k • H` (equality of functions) with the chain
rule for a continuous linear map on the right (`ContinuousLinearMap.iteratedFDerivWithin_comp_right`,
on the open set `s`) and the scalar-multiple rule for `iteratedFDeriv`.

Applied to `H = fun y : ℝ³ => ‖y‖` (`k = 1`) and `H = fun y => ‖y‖^2` (`k = 2`), this gives the
decay of the sixth derivatives of these two functions along rays, hence the tail bound in
`tauSm_admissible`.
-/

noncomputable section

namespace Work.BoseBoxFock.TauSmAdm

/-- Composing a multilinear form with `t • 1` in every variable multiplies it by `t ^ n`. -/
theorem compCLM_const_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} (t : ℝ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) :
    A.compContinuousLinearMap (fun _ => t • (1 : E →L[ℝ] E)) = t ^ n • A := by
  ext m
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const,
    Finset.card_fin, ContinuousMultilinearMap.smul_apply]

/-- **Homogeneity of the `n`-th iterated derivative** of a positively homogeneous function. -/
theorem iteratedFDeriv_smul_of_homogeneous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : E → ℝ} {k n : ℕ} {t : ℝ} (ht : 0 < t) {s : Set E} (hso : IsOpen s) {x : E}
    (hxs : x ∈ s) (htxs : t • x ∈ s)
    (hH : ∀ c : ℝ, 0 < c → ∀ y : E, H (c • y) = c ^ k * H y)
    (hC : ContDiffOn ℝ (↑n : WithTop ℕ∞) H s) :
    t ^ n • iteratedFDeriv ℝ n H (t • x) = t ^ k • iteratedFDeriv ℝ n H x := by
  have hx' : ContDiffAt ℝ (↑n : WithTop ℕ∞) H x := (hC x hxs).contDiffAt (hso.mem_nhds hxs)
  have hpre : IsOpen ((fun z : E => t • (1 : E →L[ℝ] E) z) ⁻¹' s) :=
    hso.preimage (continuous_const.smul continuous_id)
  have hxpre : x ∈ (fun z : E => t • (1 : E →L[ℝ] E) z) ⁻¹' s := by
    simp only [Set.mem_preimage, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
    exact htxs
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right (t • (1 : E →L[ℝ] E)) hC
    hso.uniqueDiffOn hpre.uniqueDiffOn htxs (le_refl (↑n : WithTop ℕ∞))
  have hA : iteratedFDeriv ℝ n (fun z => H (t • z)) x
      = (iteratedFDeriv ℝ n H (t • x)).compContinuousLinearMap (fun _ => t • (1 : E →L[ℝ] E)) := by
    rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => H (t • z)) n hpre hxpre,
      ← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := H) n hso htxs]
    exact hcomp
  have hB : iteratedFDeriv ℝ n (fun z => H (t • z)) x = t ^ k • iteratedFDeriv ℝ n H x := by
    have hfun : (fun z : E => H (t • z)) = (fun z : E => t ^ k * H z) := funext (hH t ht)
    rw [hfun]
    rw [show (fun z : E => t ^ k * H z) = t ^ k • H from rfl]
    rw [iteratedFDeriv_const_smul_apply (𝕜 := ℝ) hx']
  rw [hA] at hB
  rw [compCLM_const_smul t] at hB
  exact hB

end Work.BoseBoxFock.TauSmAdm
