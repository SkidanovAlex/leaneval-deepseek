import Mathlib
import Submission.Work.CLift.analytic
import Submission.Work.CLift.ode_holds
import Submission.Work.CLift.hasDerivAt_U

/-!
# Area CLift — the ODE (system form) satisfied by the gauge coordinate `v = Vp`

`Vp m n ra rb rab r0 x = (U₁(x) − U₀(x)/2 − β)/(x+1)` is the gauge coordinate of the
pulled-back scalar ODE `P₂U₂ + P₁U₁ + P₀U₀ = R`.  This file proves that, at every
point `‖x‖ < 1/2` with `x ≠ −1` and `R2p m n x ≠ 0`, the function `Vp` satisfies the
first-order *linear system*

`v' = A₂₁·U₀ + A₂₂·v + c₂`,

where `A₂₁ = Muq/R2`, `A₂₂ = Nq/R2 − 1/2`, `c₂ = Mc/(2(a+b)R2)` are the gauge-normalised
coefficients (`Work.CLift.defs`).  The proof is the quotient rule, together with the
three gauge identities `Mu_identity`, `Nq_identity`, `Mc_identity` and the ODE
`ode_holds` which expresses `U₂` through `U₀, U₁`.
-/

set_option maxHeartbeats 4000000

namespace Work.CLift

open Work.CLift Submission.CDTPlan

noncomputable section

/-- `a + b ≠ 0` in `ℂ`, where `a = 2m+1`, `b = 2n+1`. -/
lemma aa_add_bb_ne_zero (m n : ℕ) : (aa m : ℂ) + (bb n : ℂ) ≠ 0 := by
  have hcast : ((aa m : ℂ) + (bb n : ℂ)) = ((2 * m + 2 * n + 2 : ℕ) : ℂ) := by
    simp only [aa, bb]; push_cast; ring
  rw [hcast]
  exact_mod_cast (by omega : (2 * m + 2 * n + 2 : ℕ) ≠ 0)

/-- The algebraic content of the system for `Vp`: after substituting the ODE for `U₂` and the
three gauge identities, the quotient-rule derivative of `(U₁ − U₀/2 − β)/(x+1)` equals
`A₂₁U₀ + A₂₂·(U₁ − U₀/2 − β)/(x+1) + c₂`. -/
lemma vp_algebra (m n : ℕ) (ra rb rab : ℤ) (x u0 u1 u2 : ℂ)
    (hODE : P2p m n x * u2 + P1p m n x * u1 + P0p m n x * u0 = Rhp m n ra rb rab x)
    (hD : x + 1 ≠ 0) (hR2 : R2p m n x ≠ 0) :
    ((u2 - u1 / 2) * (x + 1) - (u1 - u0 / 2 - bbeta m n ra rb)) / (x + 1) ^ 2
      = A21 m n x * u0
        + A22 m n x * ((u1 - u0 / 2 - bbeta m n ra rb) / (x + 1))
        + c2 m n ra rb rab x := by
  have hD2 : (x + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hab' : (aa m : ℂ) + (bb n : ℂ) ≠ 0 := aa_add_bb_ne_zero m n
  have hab : (2 * ((aa m : ℂ) + (bb n : ℂ))) ≠ 0 := mul_ne_zero two_ne_zero hab'
  have hmu : Muqp m n x = (-(P1p m n x) / 2 - P0p m n x - P2p m n x / 4) / (x + 1) ^ 2 := by
    rw [eq_div_iff hD2, Mu_identity]; ring
  have hnq : Nqp m n x = (-(P1p m n x + R2p m n x)) / (x + 1) := by
    rw [eq_div_iff hD, Nq_identity]; ring
  have hmc : Mcqp m n ra rb rab x = (2 * ((aa m : ℂ) + (bb n : ℂ)) * Rhp m n ra rb rab x
      - ((ra : ℂ) + (rb : ℂ)) * (P1p m n x + P2p m n x / 2)) / (x + 1) ^ 2 := by
    rw [eq_div_iff hD2, Mc_identity]; ring
  have hp2 : P2p m n x = (x + 1) * R2p m n x := by simp only [P2p, R2p]; ring
  simp only [A21, A22, c2, bbeta]
  rw [hmu, hnq, hmc, ← hODE, hp2]
  field_simp [hD, hR2, hab, hab']
  ring

theorem hasDerivAt_Vp (m n : ℕ) (ra rb rab r0 : ℤ) (hR : PRadius) (hAdm : CAdm m n)
    (hRel : CRel m n ra rb rab r0) (x : ℂ) (hx : ‖x‖ < 1 / 2) (hx1 : x ≠ -1)
    (hR2 : R2p m n x ≠ 0) :
    HasDerivAt (Vp m n ra rb rab r0)
      (A21 m n x * U0 m n ra rb rab r0 x + A22 m n x * Vp m n ra rb rab r0 x
        + c2 m n ra rb rab x) x := by
  obtain ⟨hU0, hU1⟩ := hasDerivAt_U m n ra rb rab r0 hR hAdm hRel x hx
  have hODE : P2p m n x * U2 m n ra rb rab r0 x + P1p m n x * U1 m n ra rb rab r0 x
      + P0p m n x * U0 m n ra rb rab r0 x = Rhp m n ra rb rab x :=
    ode_holds m n ra rb rab r0 hR hAdm hRel x (le_of_lt hx)
  have hD : x + 1 ≠ 0 := by intro h; exact hx1 (by linear_combination h)
  have hnum : HasDerivAt (fun y : ℂ =>
      U1 m n ra rb rab r0 y - U0 m n ra rb rab r0 y / 2 - bbeta m n ra rb)
      (U2 m n ra rb rab r0 x - U1 m n ra rb rab r0 x / 2) x :=
    (hU1.sub (hU0.div_const 2)).sub_const _
  have hden : HasDerivAt (fun y : ℂ => y + 1) 1 x := by
    simpa using (hasDerivAt_id x).add_const 1
  have hV : HasDerivAt (Vp m n ra rb rab r0)
      (((U2 m n ra rb rab r0 x - U1 m n ra rb rab r0 x / 2) * (x + 1)
        - (U1 m n ra rb rab r0 x - U0 m n ra rb rab r0 x / 2 - bbeta m n ra rb) * 1)
        / (x + 1) ^ 2) x := hnum.div hden hD
  refine hV.congr_deriv ?_
  simp only [mul_one]
  rw [vp_algebra m n ra rb rab x (U0 m n ra rb rab r0 x) (U1 m n ra rb rab r0 x)
    (U2 m n ra rb rab r0 x) hODE hD hR2]
  simp only [Vp]

end

end Work.CLift
