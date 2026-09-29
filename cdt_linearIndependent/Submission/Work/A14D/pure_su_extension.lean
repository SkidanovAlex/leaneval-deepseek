import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.pure_pullback_cont

/-!
# `Work.A14D.pure_su_extension`

The seven pure pullbacks `Σ_k [xᵏ]((pureB j).subst sympY)·zᵏ` are holomorphic on the unit disc
(`Work.C17.Bsubst_differentiableOn`); they extend holomorphically to the whole half plane `SU`
(this is the `S = SU` case of the generic continuation `Work.A14D.cont_half`; in particular the
point `2 ∈ SU` is not excluded).
-/

namespace Work.A14D

open Complex Metric
open scoped Topology BigOperators

noncomputable section

theorem pure_su_extension (j : Fin 7) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F SU ∧ ∀ z ∈ SU ∩ Metric.ball (0 : ℂ) 1,
      F z = ∑' k : ℕ,
        ((PowerSeries.coeff k ((Submission.CDTPlan.pureB j).subst Submission.CDT.sympY) : ℚ) : ℂ)
          * z ^ k :=
  cont_half isOpen_SU_H_cont convex_SU one_notMem_SU zero_notMem_SU I_half_mem_SU j

end

end Work.A14D
