import Submission.Grassmann.SwitchingRoles
import Submission.Grassmann.HypHyperUC
import Submission.Grassmann.DerivativeDegree

/-!
# Rewriting `D4` in the coordinate model

`D4 V₁ W₁ f` (in `HypHyperUC.lean`) is the *intrinsic* form of the shifted 4-norm
`E_T ‖D_{V₁,W₁,T}[f]‖₂⁴`.  This file rewrites it with the concrete coordinate Laplacians
`Dop0S` of `SwitchingRoles.lean`, so that the paper's induction
(`lem:upper bound on 4-norms of the derivatives given induction hypothesis`) can be run
in the coordinate model used by `after_restricting`.

Main result:

  `D4 V₁ W₁ (Lsub V₁ W₁ g) = 2^{-mn} Σ_T (l2sq (Dop0S V₁ W₁ T g))²`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-- **`D4` in the coordinate model**: the intrinsic fourth-moment of the derivative
`D_{V₁,W₁,T}[Lsub V₁ W₁ g]` equals the average over `T` of the squared `L²`-norm of the
coordinate expression `Dop0S V₁ W₁ T g`. -/
theorem D4_Lsub_eq_sum_l2sq (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    D4 V₁ W₁ (Lsub V₁ W₁ g) =
      ((2 : ℝ) ^ (m * n))⁻¹ * ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
        (l2sq (Dop0S V₁ W₁ T g)) ^ 2 := by
  rw [D4]
  congr 1
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  rw [Dop0S, Lsub]
  exact (l2sq_restr_shift_eq_homSub V₁ W₁ (Qp V₁) (Ip W₁) (ker_Qp V₁) (range_Qp V₁)
    (range_Ip W₁) (ker_Ip W₁) T (lapMulN (hybridPredSub V₁ W₁) g)).symm

end

end Submission.Grassmann
