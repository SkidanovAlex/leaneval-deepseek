import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine
import Submission.Work.CR.Flat.Cauchy.exists_dbar_solution_open_of_unit
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Core.bmRow_holder
import Submission.Work.NN.Core.exists_contDiff_bump_of_isCompact_subset
import Submission.Work.NN.Final.bmDefect_eq_local
import Submission.Work.NN.Final.bmDefectTwo
import Submission.Work.NN.Final.twoRec
import Submission.Work.NN.Final.uS2_solves
import Submission.Work.NN.Final.uS2_estimate
import Submission.Work.NN.Final.uS2_smooth
import Submission.Work.NN.Final.uS2_contDiff
import Submission.Work.NN.Final.twoCoreAux

namespace Work.NN.Final

/-- The flat `(0,2)`-Poincaré operator on nested polydiscs, with the full `C^{k,α}` gain, in the exact form required by the `FlatTwo` interface. CAUTION (found in review): the `(0,2)`-equation alone does not control the top-order derivatives of a solution, since its kernel (the `∂̄`-closed `(0,1)`-forms, i.e. the `∂̄h`) is large; hence a one-shot interior Schauder estimate for an arbitrary solution (the analogue of `dbar_interior_oneshot`) is FALSE and cannot serve as the bootstrap step. The linear `T2` must be a canonical order-`-1` solution operator (e.g. the Koppelman-Leray operator for the polydisc) or an equivalent gauge-fixed operator with an explicit estimate. Usable inputs: `polydisc_dbar_schauder_open` (`(0,1)` case with gain, proved), `flat_dbar_twoForm_Ck`/`flat_twoForm_smooth` (supported `(0,2)` case with gain), the Bochner-Martinelli machinery of `Work.CR.Flat.Cauchy`, the Hölder algebra of `Work.CR.Flat.Holder`, and `Work.Hormander.Weights`. For `n = 1` the statement is vacuously satisfied by `T2 = 0` (antisymmetry forces `η 0 0 = 0`). -/
theorem twoCore {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ (T2 : (Fin n → Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] (Fin n → (Fin n → ℂ) → ℂ)) (C2 : ℕ → ℝ),
      (∀ k, 0 < C2 k) ∧
      (∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
        (∀ j l, ContDiffOn ℝ (1 : ℕ∞) (η j l) (Work.NN.Final.pd n ρ 4)) →
        (∀ j l z, η j l z = - η l j z) → Work.NN.Final.Clos2 n ρ 4 η →
        ∀ j l z, z ∈ Work.NN.Final.pd n ρ 2 →
          Work.CR.Flat.dbarCoord j (T2 η l) z - Work.CR.Flat.dbarCoord l (T2 η j) z = η j l z) ∧
      (∀ (k : ℕ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
        (∀ j l, ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) (η j l) (Work.NN.Final.pd n ρ 4)) →
        (∀ j l z, η j l z = - η l j z) → Work.NN.Final.Clos2 n ρ 4 η → ∀ j : Fin n,
          Work.CR.Flat.holderNorm (k + 1) α (T2 η j) (Work.NN.Final.pd n ρ 2)
            ≤ ENNReal.ofReal (C2 k) * ∑ j, ∑ l, Work.CR.Flat.holderNorm k α (η j l) (Work.NN.Final.pd n ρ 4)) ∧
      (∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
        (∀ j l, ContDiffOn ℝ (⊤ : ℕ∞) (η j l) (Work.NN.Final.pd n ρ 4)) →
        (∀ j l z, η j l z = - η l j z) → Work.NN.Final.Clos2 n ρ 4 η →
        ∀ j : Fin n, ContDiffOn ℝ (⊤ : ℕ∞) (T2 η j) (Work.NN.Final.pd n ρ 2)) :=
  twoCoreAux hρ hα0 hα1

end Work.NN.Final
