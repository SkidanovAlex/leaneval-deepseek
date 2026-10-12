import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.sliceF_mem_monSpan
import Submission.Work.BoseBoxFock.sliceF_symm
import Submission.Work.BoseBoxFock.symm_mem_span_range_boxRealiseC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sliceFCRealise` — the slice of a sector **is** a model state

The BF3c selection (`FINDING_BF3c_selection_s8.md` §1, `FINDING_BF3c_realcomplex_RESOLUTION.md`
§3.4) produces, after a sector `S` and a complement configuration `y`, the slice
`Work.BoseBoxFock.sliceF e S Φ y` of the sector state `Φ_S = slotExact e S Φ`.  This module
assembles the three ingredients proved separately into the statement the model map needs:

* `Work.BoseBoxFock.sliceF_symm` — the slice is symmetric;
* `Work.BoseBoxFock.sliceF_mem_monSpan` — the slice lies in the `ℂ`-span of the monomials
  `∏_i e (l i) (u i)`;
* `Work.BoseBoxFock.symm_mem_span_range_boxRealiseC` — a symmetric element of that span is
  `boxRealiseC` of a complexified Fock vector;

giving

    ∃ Ψ : CFock m, boxRealiseC e S.card Ψ = sliceF e S Φ y .

With `boxRealiseC_eq_re_add_im` (`complexRealise.lean`) this yields the **two real** model vectors
`realPart Ψ`, `imagPart Ψ` whose realisations are the real and imaginary parts of the slice, whose
`bomb`-forms add up to the complex form (`FINDING_BF3c_realcomplex_RESOLUTION.md` §1.3), and the
binary selection picks the admissible one — the step that `FINDING_BF3c_selection_s8.md` §2
believed to be an obstruction.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The slice of a sector is a model state.**  For the sector `S` of a continuous, compactly
supported, symmetric state `Φ` and any complement configuration `y`, the slice
`sliceF e S Φ y` is the `ℂ`-linear realisation of some complexified Fock vector. -/
theorem exists_boxRealiseC_eq_sliceF {m n : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (S : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦsym : ∀ σ : Equiv.Perm (Fin n),
      (fun x : Fin n → EuclideanSpace ℝ (Fin 3) => Φ (x ∘ σ)) = Φ)
    (y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) :
    ∃ Ψ : CFock m, boxRealiseC e S.card Ψ = sliceF e S Φ y :=
  symm_mem_span_range_boxRealiseC e (sliceF_symm e he hec S Φ hΦ hΦc hΦsym y)
    (sliceF_mem_monSpan e he hec S Φ hΦ hΦc y)

/-- **The real model vectors of the slice.**  Concretely, the slice is the sum of the realisations
of two *real* Fock vectors; these are the candidates of the binary selection. -/
theorem exists_realFock_eq_sliceF_re_im {m n : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (S : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦsym : ∀ σ : Equiv.Perm (Fin n),
      (fun x : Fin n → EuclideanSpace ℝ (Fin 3) => Φ (x ∘ σ)) = Φ)
    (y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) :
    ∃ Ψ₁ Ψ₂ : Work.BoseB4.RealFock m,
      Work.BoseDict.boxRealise e S.card Ψ₁
        + Complex.I • Work.BoseDict.boxRealise e S.card Ψ₂ = sliceF e S Φ y := by
  obtain ⟨Ψ, hΨ⟩ := exists_boxRealiseC_eq_sliceF e he hec S Φ hΦ hΦc hΦsym y
  refine ⟨realPart Ψ, imagPart Ψ, ?_⟩
  rw [← boxRealiseC_eq_re_add_im e Ψ, hΨ]

end Work.BoseBoxFock
