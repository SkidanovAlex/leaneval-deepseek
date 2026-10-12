import Mathlib.Data.Real.Basic
import Submission.Work.BoseC3QAll.Est1.Reduction
import Submission.Work.BoseC3QAll.Est1.estT2sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.estQ3oneA` — FS `eq:EstimateQ3Tilde1` (`lem:EstimatesOnQ3-js`, piece 1)

The target: `EstQ3oneA K₀ b₀ hb₀` (`Statements.lean`), i.e. at small diluteness
`t = μa³` and `b ≥ b₀`,

`-(C·e1A E)‖Φ‖² ≤ ⟨Φ, (Q3oneT + (1-𝓁²)·dNumOpR(P_H) + (𝓁²/2)·dNumOpR(P_H^q) + Q2ex
  + (b/100)·gapOpT) Φ⟩` for every `Φ` of FS's window `T.NWindow E.bigM`.

The proof is the assembly `Est1.estQ3oneA_of_pieces`
(`Submission/Work/BoseB7A/Est1/Assembly.lean`), applied through the verified
reduction `Est1.estQ3oneA_of_estT2sum`
(`Submission/Work/BoseB7A/Est1/Reduction.lean`), whose three inputs are

* **piece B** — `Est1.estT2sum` (`Est1/estT2sum.lean`): the sum bound
  `Σ_k c_k⁻¹‖Y_kΦ‖² ≤ (𝓁²/4)⟨R_{P_H^q}⟩ + 2ρ_zŴ₁ω(0)⟨G Φ⟩ + C·e1A·‖Φ‖² + (b/200)⟨gapOpT⟩`
  (FS's `T₂,op` + `T₂,comm`, `eq:T2opprime`/`eq:EstimT2comm`, FS lines 3058–3230);
* **piece C** — `Est1.estR1` (`Est1/estR1.lean`): the linear leftover `R1`
  (FS's `T₁` and the commutator part of `T₂`, FS lines 3300–3320);
* **the substitution hypothesis** — `Glue.substHyp_of_kernel`: `Q3KernelFSAll` at
  small `t` gives `SubstHypG`, which the shift decomposition
  `Est1.Q3oneT_shift` needs.

The `Q₂^ex` cancellation is performed inside the assembly through
`Q3KernelFSAll.q2exLower`; the reserve bookkeeping is
`Σ_{k∈P_H} c_k⟨b_k†b_k⟩ = (1-𝓁²)⟨R_{P_H}⟩` (piece D, `Est1.compSquare_sum` with
`Est1.sum_cD_mul_bp_eq`) and the gap budget is
`b/100 ≥ b/400 (q2exLower) + b/200 (piece B) + b/800 (piece C)`.

`Est1/estT2.lean` holds the *refuted* earlier statement of piece B as a
`Prop`-valued `def` (`Work.BoseC3QAll.Est1.estT2`), refuted `sorry`-free in
`Est1/estT2_false.lean` (`Work.BoseC3QAll.Est1.not_estT2`); the abandoned earlier
routes to the `σ₂`/piece-B bounds were retired — see `SCRATCH_HISTORY.md`.
-/

namespace Work.BoseC3QAll

theorem estQ3oneA (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : Work.BoseC3QAll.EstQ3oneA K₀ b₀ hb₀ :=
  Est1.estQ3oneA_of_estT2sum K₀ b₀ hb₀ (Est1.estT2sum K₀ b₀ hb₀)

end Work.BoseC3QAll
