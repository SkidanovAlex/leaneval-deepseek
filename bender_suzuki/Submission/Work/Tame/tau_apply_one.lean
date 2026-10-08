import Mathlib
import Submission.Work.Tame.Tau
import Submission.Work.Tame.projEC_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Classical

namespace Work.Tame

/-- The Dade map `τ` of (9.4) kills the identity on functions of degree `0`.  Expanding (9.4) at
`1`: `Ind_𝔏^X α (1) = [X:𝔏]·α(1) = 0`, `α_{i1}(1) = α(projEC 1) = α(1) = 0` (using Feit–Thompson's
`𝔎_i ∩ 𝔏 = 1`, which makes `projEC Lhat (Hs i) 1 = 1`), and
`α_{i2}(1) = [𝔑_i : 𝔏 ∩ 𝔑_i]·α_i(1) = 0`.

The hypotheses `Hs i ⊓ 𝔏 = ⊥` are exactly `IsTamelyImbedded.supp_inf`; they are supplied by the
caller from `IsTamelyImbedded` together with `(Dset Lhat).Nonempty`, and are vacuous when `n = 0`. -/
theorem tau_apply_one {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (hinf : ∀ i : Fin n, Hs i ⊓ Lgrp Lhat = ⊥)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α 1 = 0) : tau Lhat n Hs α 1 = 0 := by
  -- Expand (9.4) at `1`, then evaluate each induction via `indFun_apply_one`.
  rw [tau_apply, Work.Induction.indFun_apply_one, hα, mul_zero, zero_add]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Work.Induction.indFun_apply_one]
  -- `α_{i1}(1) = α(projEC 1) = α(1) = 0`, using `𝔎_i ∩ 𝔏 = 1`.
  have h1 : alphaI1LM Lhat (Hs i) α 1 = 0 := by
    rw [alphaI1LM_apply, projEC_one (hinf i)]
    simpa using hα
  -- `α_{i2}(1) = [𝔑_i : 𝔏 ∩ 𝔑_i]·α(1) = 0`.
  have h2 : alphaI2LM Lhat (Hs i) α 1 = 0 := by
    rw [alphaI2LM_apply, Work.Induction.indFun_apply_one]
    simp [hα]
  rw [Pi.sub_apply, h1, h2, sub_zero, mul_zero]

end Work.Tame
