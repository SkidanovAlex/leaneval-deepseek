import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Invariance of the potential energy under the permutation action

The potential energy of an element `p = (u, ∇u)` of the ambient space is
`potSq W p = ∫ x, W x * (u x)²`, and the permutation `σ` of the particles acts
on the function part by composition with `tauPerm σ`,
`(permLp σ u) x = u (tauPerm σ x)` almost everywhere.

If the potential `W` is invariant under the particle permutation,
`W (tauPerm σ x) = W x`, then the potential energy is invariant:

`potSq W (permAmb N σ p) = potSq W p`.

The proof is the change of variables `x ↦ tauPerm σ x`, legitimate because
`tauPerm σ` is a measurable embedding preserving Lebesgue measure
(`measurePreserving_tauPerm`).  The two quantities are

`∫ x, W x * (u (tauPerm σ x))²`  and  `∫ y, W y * (u y)²`,

and since `W (tauPerm σ x) = W x` the first integrand is
`(fun y => W y * (u y)²) (tauPerm σ x)`.
-/

open MeasureTheory Filter
open Work.BoseSym

namespace Work.BoseSym.Perm

/-- The particle permutation `tauPerm N σ` is a measurable embedding. -/
lemma measurableEmbedding_tauPerm (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    MeasurableEmbedding (tauPerm N σ) := by
  have hfun : ((MeasurableEquiv.piCongrLeft (fun _ : Fin N => E3) σ.symm : Conf N ≃ᵐ Conf N) :
      Conf N → Conf N) = tauPerm N σ := by
    funext x i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, tauPerm]
  rw [← hfun]
  exact (MeasurableEquiv.piCongrLeft (fun _ : Fin N => E3) σ.symm).measurableEmbedding

/-- Change of variables for the particle permutation: the Lebesgue integral of
`g ∘ tauPerm σ` equals the integral of `g`. -/
lemma integral_comp_tauPerm {N : ℕ} (σ : Equiv.Perm (Fin N)) (g : Conf N → ℝ) :
    (∫ x, g (tauPerm N σ x)) = ∫ y, g y :=
  MeasurePreserving.integral_comp (measurePreserving_tauPerm N σ)
    (measurableEmbedding_tauPerm N σ) g

theorem potSq_permAmb {N : ℕ} {W : Conf N → ℝ} (hW : ∀ σ x, W (tauPerm N σ x) = W x)
    (σ : Equiv.Perm (Fin N)) (p : Amb N) :
    potSq W (permAmb N σ p) = potSq W p := by
  -- Replace the permuted `L²` element by its almost everywhere description.
  have h1 : potSq W (permAmb N σ p)
      = ∫ x, W x * ((p.1 : Conf N → ℝ) (tauPerm N σ x)) ^ 2 := by
    simp only [potSq, permAmb_fst]
    refine integral_congr_ae ?_
    filter_upwards [permLp_coeFn σ p.1] with x hx
    rw [hx]
  -- Use the invariance of `W` to recognise the integrand as a composition.
  have h2 : (∫ x, W x * ((p.1 : Conf N → ℝ) (tauPerm N σ x)) ^ 2)
      = ∫ x, W (tauPerm N σ x) * ((p.1 : Conf N → ℝ) (tauPerm N σ x)) ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hW σ x]
  -- Change variables.
  have h3 : (∫ x, W (tauPerm N σ x) * ((p.1 : Conf N → ℝ) (tauPerm N σ x)) ^ 2)
      = ∫ y, W y * ((p.1 : Conf N → ℝ) y) ^ 2 :=
    integral_comp_tauPerm σ (fun y => W y * ((p.1 : Conf N → ℝ) y) ^ 2)
  exact h1.trans (h2.trans h3)

end Work.BoseSym.Perm
