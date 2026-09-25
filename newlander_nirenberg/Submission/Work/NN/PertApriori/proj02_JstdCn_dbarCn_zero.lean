import Mathlib
import Submission.Work.NN.PertApriori.pertAprioriDefs
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.Algebra
import Submission.Work.NN.Assemble.nonempty_dbarJSolver_std
import Submission.Work.NN.Final.proj02_integrable_flat
import Submission.Work.Core.ConstCase

namespace Work.NN.PertApriori

open scoped ContDiff

/-!
# `∂̄₀` of a smooth function is `∂̄₀`-closed (the standard-structure integrability `∂̄² = 0`)

This is the `A = 0` case of the "hint" hypothesis of the perturbed a priori chapter: for the
*standard* structure `JstdCn n` on `ℂⁿ`, the `(0,2)`-part of the exterior derivative of
`z ↦ dbarCn (JstdCn n) w z` vanishes for every smooth `w`.

The proof does not recompute the classical identity `∂̄_J² = 0`.  Instead it *transports* the
already proved statement `Work.NN.Final.proj02_integrable_flat` (which is
`Work.NN.Core.dbar_sq_zero` transported to the flat model along an arbitrary linear equivalence
`T : ℝ^{2n} ≃ ℂⁿ`) to the standard structure: choose any real-linear isomorphism
`T : E n ≃L[ℝ] F n` (e.g. one produced by the equality of the real dimensions
`2n = finrank ℝ ℂⁿ`), take the constant structure `stdOf T` on `ℝ^{2n}` — which is an almost
complex structure with vanishing Nijenhuis tensor, being the transport of multiplication by `i` —
and use that the transport `Jtr (stdOf T) T` of `stdOf T` back along `T` is *exactly* `JstdCn n`.
-/

/-- The transported standard structure `Jtr (stdOf T) T` is the standard structure `JstdCn n` of
the flat model: `tupleDeriv T (T⁻¹ (i · T w)) = i · w`. -/
lemma Jtr_stdOf_eq_JstdCn {n : ℕ} (T : LeanEval.Geometry.NewlanderNirenberg.E n ≃L[ℝ]
    Submission.F n) :
    Work.NN.Final.Jtr (Submission.stdOf T) T = Work.NN.Core.JstdCn n := by
  funext z
  apply ContinuousLinearMap.ext
  intro w
  have h1 : (T : LeanEval.Geometry.NewlanderNirenberg.E n →L[ℝ] Submission.F n)
      (Work.NN.Core.tupleDerivInv T w) = Submission.ecL n w := by
    rw [show Work.NN.Core.tupleDerivInv T w
        = (T.symm : Submission.F n →L[ℝ] LeanEval.Geometry.NewlanderNirenberg.E n)
            (Submission.ecL n w) from rfl]
    exact T.apply_symm_apply (Submission.ecL n w)
  have h2 : (T.symm : Submission.F n →L[ℝ] LeanEval.Geometry.NewlanderNirenberg.E n)
      (Complex.I • Submission.ecL n w) = Work.NN.Core.tupleDerivInv T (Complex.I • w) := by
    rw [← Submission.ecL_smul]
    rfl
  show Work.NN.Core.tupleDeriv T (Submission.stdOf T (Work.NN.Core.tupleDerivInv T z)
      (Work.NN.Core.tupleDerivInv T w)) = Work.NN.Core.JstdCn n z w
  rw [Submission.stdOf_apply, h1, h2, Work.NN.Core.tupleDeriv_tupleDerivInv]
  exact (Work.NN.Core.JstdCn_apply n z w).symm

theorem proj02_JstdCn_dbarCn_zero {n : ℕ} (w : Work.NN.PertApriori.Cn n → ℂ)
    (hw : ∀ m : ℕ, ContDiff ℝ m w) (z V W : Work.NN.PertApriori.Cn n) :
    Work.NN.Final.proj02 (Work.NN.Core.JstdCn n)
      (fun z' => Work.NN.Final.dOne
        (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n) w z'') z') z V W = 0 := by
  -- the real dimensions of `ℝ^{2n}` and of `ℂⁿ` agree, so there is a real-linear isomorphism
  have hE : Module.finrank ℝ (LeanEval.Geometry.NewlanderNirenberg.E n) = 2 * n := by
    rw [finrank_euclideanSpace]
    simp
  have hF : Module.finrank ℝ (Submission.F n) = 2 * n := by
    have h1 : Module.finrank ℂ (Submission.F n) = n := by
      rw [finrank_euclideanSpace]
      simp
    have h2 := Module.finrank_mul_finrank ℝ ℂ (Submission.F n)
    rw [h1, Complex.finrank_real_complex] at h2
    exact h2.symm
  let T : LeanEval.Geometry.NewlanderNirenberg.E n ≃L[ℝ] Submission.F n :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (hE.trans hF.symm)
  have hJtr : Work.NN.Final.Jtr (Submission.stdOf T) T = Work.NN.Core.JstdCn n :=
    Jtr_stdOf_eq_JstdCn T
  -- integrability of the transported standard structure, transported back to the flat model
  have h := Work.NN.Final.proj02_integrable_flat (n := n) (U := Set.univ) isOpen_univ
    (J := Submission.stdOf T) (Submission.isAlmostComplexOn_stdOf T Set.univ)
    (Submission.nijenhuisVanishesOn_stdOf T Set.univ) T hw (z := z) (Set.mem_univ _) V W
  rw [hJtr] at h
  exact h

end Work.NN.PertApriori
