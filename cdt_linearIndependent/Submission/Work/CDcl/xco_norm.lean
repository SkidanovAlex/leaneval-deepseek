import Mathlib
import Submission.Work.CDcl.xrel_defs
import Submission.Work.CDcl.xco_ode_P
import Submission.Work.CDcl.xco_ode_Pw_alt
import Submission.Work.CDcl.xco_iter

/-!
# `Work.CDcl.xco_norm`: the normal form of `Aᵏ` on `P` and on `P∘φ`

`Aop f = ρ·f'` acts on `Pfun` and on `Pwfun` by the two order-two ODEs of `xco_ode_P`,
`xco_ode_Pw`; iterating gives the coefficient sequences `Pseq` and `Pwseq` of `xrel_defs.lean`
and hence the normal form of `Tfun k = Aop^[k] (Tfun 0)`.
-/

noncomputable section

open Polynomial PowerSeries

namespace Work.CDcl

theorem Aop_add (x y : LF) : Aop (x + y) = Aop x + Aop y := by
  simp only [Aop, dL_add, mul_add]

/-- `Aop` of a rational multiple of an element. -/
theorem Aop_toL_mul (c : RatFunc ℚ) (x : LF) :
    Aop (toL c * x) = toL (rhoK * Submission.CDT.dRat c) * x + toL c * Aop x := by
  rw [Aop, dL_toL_mul]
  have h : rhoL * (toL (Submission.CDT.dRat c) * x + toL c * dL x)
      = (rhoL * toL (Submission.CDT.dRat c)) * x + toL c * (rhoL * dL x) := by ring
  rw [h, ← Aop]
  simp only [rhoL, ← toL_mul]

/-- `Aop` of a rational constant. -/
theorem Aop_toL (c : RatFunc ℚ) : Aop (toL c) = toL (rhoK * Submission.CDT.dRat c) := by
  rw [Aop, dL_toL]
  simp only [rhoL, ← toL_mul]

theorem iterate_Aop_add (k : ℕ) (x y : LF) :
    Aop^[k] (x + y) = Aop^[k] x + Aop^[k] y := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, Aop_add]

/-- `Aop` of `Pfun`. -/
theorem Aop_Pfun (a b : ℚ) (ra rb rab r0 : ℤ) :
    Aop (Pfun a b ra rb rab r0) = toL rhoK * dL (Pfun a b ra rb rab r0) := by
  simp only [Aop, rhoL]

/-- `Aop` of `dL Pfun`, via the ODE `xco_ode_P`. -/
theorem Aop_dL_Pfun (a b : ℚ) (ra rb rab r0 : ℤ) :
    Aop (dL (Pfun a b ra rb rab r0))
      = toL (rhoK * betaK a b) * Pfun a b ra rb rab r0
        + toL (rhoK * alphaK a b) * dL (Pfun a b ra rb rab r0)
        + toL (rhoK * gammaK a b ra rb rab r0) := by
  rw [Aop, xco_ode_P a b ra rb rab r0]
  rw [show rhoL = toL rhoK from rfl, show alphaL a b = toL (alphaK a b) from rfl,
    show betaL a b = toL (betaK a b) from rfl,
    show gammaL a b ra rb rab r0 = toL (gammaK a b ra rb rab r0) from rfl,
    toL_mul, toL_mul, toL_mul]
  ring

/-- `Aop` of `Pwfun`. -/
theorem Aop_Pwfun (a b : ℚ) (ra rb rab r0 : ℤ) :
    Aop (Pwfun a b ra rb rab r0) = toL rhoK * dL (Pwfun a b ra rb rab r0) := by
  simp only [Aop, rhoL]

/-- `Aop` of `dL Pwfun`, via the ODE `xco_ode_Pw`. -/
theorem Aop_dL_Pwfun (a b : ℚ) (ra rb rab r0 : ℤ) :
    Aop (dL (Pwfun a b ra rb rab r0))
      = toL (rhoK * betaKt a b) * Pwfun a b ra rb rab r0
        + toL (rhoK * alphaKt a b) * dL (Pwfun a b ra rb rab r0)
        + toL (rhoK * gammaKt a b ra rb rab r0) := by
  rw [Aop, xco_ode_Pw a b ra rb rab r0]
  rw [show rhoL = toL rhoK from rfl, show alphaLt a b = toL (alphaKt a b) from rfl,
    show betaLt a b = toL (betaKt a b) from rfl,
    show gammaLt a b ra rb rab r0 = toL (gammaKt a b ra rb rab r0) from rfl,
    toL_mul, toL_mul, toL_mul]
  ring

set_option maxHeartbeats 1600000 in
/-- The normal form of `Aop^[k]` on `Pfun`. -/
theorem iterate_Aop_Pfun (a b : ℚ) (ra rb rab r0 : ℤ) (k : ℕ) :
    Aop^[k] (Pfun a b ra rb rab r0)
      = toL ((Pseq a b ra rb rab r0 k).1) * Pfun a b ra rb rab r0
        + toL ((Pseq a b ra rb rab r0 k).2.1) * dL (Pfun a b ra rb rab r0)
        + toL ((Pseq a b ra rb rab r0 k).2.2) := by
  induction k with
  | zero =>
      simp only [Function.iterate_zero_apply, Pseq, toL_one, toL_zero]
      ring
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [Pseq]
      rw [Aop_add, Aop_add, Aop_toL_mul, Aop_toL_mul, Aop_toL, Aop_Pfun, Aop_dL_Pfun]
      simp only [map_mul, map_add]
      ring

set_option maxHeartbeats 1600000 in
/-- The normal form of `Aop^[k]` on `Pwfun`. -/
theorem iterate_Aop_Pwfun (a b : ℚ) (ra rb rab r0 : ℤ) (k : ℕ) :
    Aop^[k] (Pwfun a b ra rb rab r0)
      = toL ((Pwseq a b ra rb rab r0 k).1) * Pwfun a b ra rb rab r0
        + toL ((Pwseq a b ra rb rab r0 k).2.1) * dL (Pwfun a b ra rb rab r0)
        + toL ((Pwseq a b ra rb rab r0 k).2.2) := by
  induction k with
  | zero =>
      simp only [Function.iterate_zero_apply, Pwseq, toL_one, toL_zero]
      ring
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [Pwseq]
      rw [Aop_add, Aop_add, Aop_toL_mul, Aop_toL_mul, Aop_toL, Aop_Pwfun, Aop_dL_Pwfun]
      simp only [map_mul, map_add]
      ring

/-- **The normal form of the pullbacks `T k = Aᵏ (T 0)`.** -/
theorem xco_norm (a b : ℚ) (ra rb rab r0 : ℤ) (k : ℕ) :
    Tfun a b ra rb rab r0 k
      = toL ((Pseq a b ra rb rab r0 k).1) * Pfun a b ra rb rab r0
        + toL ((Pseq a b ra rb rab r0 k).2.1) * dL (Pfun a b ra rb rab r0)
        + toL ((Pwseq a b ra rb rab r0 k).1) * Pwfun a b ra rb rab r0
        + toL ((Pwseq a b ra rb rab r0 k).2.1) * dL (Pwfun a b ra rb rab r0)
        + toL ((Pseq a b ra rb rab r0 k).2.2 + (Pwseq a b ra rb rab r0 k).2.2) := by
  rw [← xco_iter a b ra rb rab r0 k, Tfun_zero]
  simp only [Sfun]
  rw [iterate_Aop_add, iterate_Aop_Pfun, iterate_Aop_Pwfun]
  rw [show toL ((Pseq a b ra rb rab r0 k).2.2 + (Pwseq a b ra rb rab r0 k).2.2)
        = toL ((Pseq a b ra rb rab r0 k).2.2) + toL ((Pwseq a b ra rb rab r0 k).2.2)
      from toL_add _ _]
  ring

end Work.CDcl
