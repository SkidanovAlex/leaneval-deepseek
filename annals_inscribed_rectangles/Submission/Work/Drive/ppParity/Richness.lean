import Mathlib
import Submission.Work.Drive.ppParity.ShiftDeriv
import Submission.Work.Drive.pairMeet2

/-!
# The richness of the intrinsic pair family: the parameter-derivative at a meet

**S3's analytic heart** (`NOTES_LEAD_residency.md`): at a meet of the perturbed pair family the
parameter-derivative of the charted pair map is onto `Tgt 8`.  The perturbation is *intrinsic*
(`Ξ (w s • unpackFst τ)` on the first block, `Ξ (w s • unpackSnd τ)` on the second), so the two
blocks move independently; the derivative of each block factors through the corresponding block
projection `unpackFst`/`unpackSnd` of the parameter and is onto there as soon as the weight does not
vanish (`ChartPert`'s third clause) — which is exactly the "`w s ≠ 0`" richness of the lead's plan.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

variable {Q : ℂ → CappingSpace}

/-- **The richness of the intrinsically perturbed pair family.** -/
theorem surjective_fderiv_ppDiff_shift
    {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace} (hΞ : ChartPert Q 4 Ξ)
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {V W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    (w : ℝ → ℝ) (τ : EuclideanSpace ℝ (Fin 8)) (x : EuclideanSpace ℝ (Fin 9))
    (p p' : CappingSpace)
    (hsrc : ppShift Ξ w (unpackFst τ) E (ftS x) (ftU x) ∈ (chr p).source)
    (hsrc' : ppShift Ξ w (unpackSnd τ) E' (ftS x) (ftU x) ∈ (chr p').source)
    (hwne : w (ftS x) ≠ 0) :
    Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 8) =>
      ppDiff p p' (ppShift Ξ w (unpackFst τ') E) (ppShift Ξ w (unpackSnd τ') E') V W x) τ) := by
  refine surjective_fderiv_pairDiff2_of_block 8
    (fun τ' (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) =>
      chr p (Ξ (w s • unpackFst τ') (E s u)))
    (fun τ' (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) =>
      chr p' (Ξ (w s • unpackSnd τ') (E' s u)))
    (fun _ (y : EuclideanSpace ℝ (Fin 3)) => chr p (V y))
    (fun _ (z : EuclideanSpace ℝ (Fin 3)) => chr p' (W z))
    τ x
    ((shiftBlockCLM Ξ (E (ftS x) (ftU x)) (w (ftS x) • unpackFst τ) p).comp
      (w (ftS x) • unpackFst))
    ((shiftBlockCLM Ξ (E' (ftS x) (ftU x)) (w (ftS x) • unpackSnd τ) p').comp
      (w (ftS x) • unpackSnd))
    0 0 ?_ ?_ (hasFDerivAt_const _ _) (hasFDerivAt_const _ _) ?_
  · exact hasFDerivAt_chart_clm (Ξ := Ξ) hΞ (E (ftS x) (ftU x)) (w (ftS x) • unpackFst) τ p hsrc
  · exact hasFDerivAt_chart_clm (Ξ := Ξ) hΞ (E' (ftS x) (ftU x)) (w (ftS x) • unpackSnd) τ p' hsrc'
  · intro a b
    obtain ⟨u₁, hu₁⟩ := exists_shiftBlockCLM_smul (Ξ := Ξ) hΞ (E (ftS x) (ftU x))
      (w (ftS x) • unpackFst τ) p hsrc (w (ftS x)) hwne a
    obtain ⟨u₂, hu₂⟩ := exists_shiftBlockCLM_smul (Ξ := Ξ) hΞ (E' (ftS x) (ftU x))
      (w (ftS x) • unpackSnd τ) p' hsrc' (w (ftS x)) hwne b
    refine ⟨pairUp u₁ u₂, ?_, ?_, rfl, rfl⟩
    · show ((shiftBlockCLM Ξ (E (ftS x) (ftU x)) (w (ftS x) • unpackFst τ) p).comp
        (w (ftS x) • unpackFst)) (pairUp u₁ u₂) = a
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, unpackFst_pairUp]
      exact hu₁
    · show ((shiftBlockCLM Ξ (E' (ftS x) (ftU x)) (w (ftS x) • unpackSnd τ) p').comp
        (w (ftS x) • unpackSnd)) (pairUp u₁ u₂) = b
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, unpackSnd_pairUp]
      exact hu₂

end

end Work.Drive
