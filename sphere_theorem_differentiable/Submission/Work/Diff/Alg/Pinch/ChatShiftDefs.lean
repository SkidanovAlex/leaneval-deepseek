import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Strict
import Submission.Work.Diff.Alg.Pinch.Chat
import Submission.Work.Diff.Alg.Pinch.ChatDefs
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.Ccone_transversal_a_aux
import Submission.Work.Diff.Alg.Pinch.ell_isAlgCurv
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic
import Submission.Work.Diff.Alg.Pinch.inPIC2_comp_bound
import Submission.Work.Diff.Alg.Pinch.Chat_exhaust
import Submission.Work.Diff.Alg.Pinch.Chat_lagrange
import Submission.Work.Diff.Alg.Pinch.Phi_wedge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for `Work.Diff.Alg.Pinch.chat_shift_inclusion`

The Böhm–Wilking family `Chat n s = Ĉ(s)` is `ell a b '' Dpic p` with parameters `(a,b,p)` given by
Brendle–Schoen (`Chat_eq_Ccone`, and its `b = 1/2` counterpart).  The key computation behind the
"shift inclusion" `R + c•Iso ∈ Ĉ(s) → R + 2c•Iso ∈ Ĉ(s+ε)` is the identity

`linv a' b' (ell a b S + t • Iso n) = S + γ₁ • (Ric₀ S ∧ id) + γ₂ • Iso n,`

`γ₁ = (b - b')/(1 + (n-2)b')`,  `γ₂ = (t + 2·scalAlg S·(a - a')/n)/(1 + 2(n-1)a'),`

which is purely linear-algebraic (`linv_ell_add_smul_Iso`).  The two quantities `γ₁`, `γ₂` are
recorded here, together with the two scalar "room" inequalities

`|γ₁| C_EF C_T σ ≤ γ₂`  and  `γ₂ (n-1)(1-P') ≥ |γ₁| (n-2) C_ric σ + σ (P' - P)/n`

(`ChSRoom`) which are exactly what is needed to absorb the `γ₁ • (Ric₀ S ∧ id)` perturbation when
passing from `Dpic P` to `Dpic P'`: `C_EF` bounds the isotropic curvature form `EF` of an algebraic
tensor by `‖D‖ · EF (Iso n)`, `C_T` bounds `‖Ric₀ S ∧ id‖` by `C_T · scalAlg S` and `C_ric` bounds
`|⟨Ric₀ S v, v⟩|` by `C_ric · scalAlg S · ‖v‖²` for `InPIC2` tensors `S`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

/-- The coefficient `γ₁ = (b - b')/(1 + (n-2)b')` of the `Ric₀ ∧ id` term in
`linv a' b' (ell a b S + t • Iso n)`. -/
noncomputable def chSg1 (n : ℕ) (b b' : ℝ) : ℝ := (b - b') / (1 + ((n : ℝ) - 2) * b')

/-- The coefficient `γ₂ = (t + 2σ(a-a')/n)/(1+2(n-1)a')` of the `Iso` term in
`linv a' b' (ell a b S + t • Iso n)`, evaluated at `σ = scalAlg S`. -/
noncomputable def chSg2 (n : ℕ) (a a' t σ : ℝ) : ℝ :=
  (t + 2 * σ * (a - a') / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a')

/-- The two "room" conditions making `S + γ₁ • (Ric₀ S ∧ id) + γ₂ • Iso n` lie in `Dpic P'`
whenever `S ∈ Dpic P` with `scalAlg S = σ` (`γ₁ = chSg1 n b b'`, `γ₂ = chSg2 n a a' t σ`). -/
def ChSRoom (n : ℕ) (C_EF C_T C_ric : ℝ) (a a' b b' P P' t σ : ℝ) : Prop :=
  |chSg1 n b b'| * C_EF * C_T * σ ≤ chSg2 n a a' t σ ∧
    chSg2 n a a' t σ * ((n : ℝ) - 1) * (1 - P') ≥
      |chSg1 n b b'| * ((n : ℝ) - 2) * C_ric * σ + σ * (P' - P) / (n : ℝ)

end Work.Diff.Alg.Pinch
