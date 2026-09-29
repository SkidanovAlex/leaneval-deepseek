import Mathlib
import Submission.Work.CDcl.xrel_defs
import Submission.Work.CDcl.xco_ode_P
import Submission.Work.CDcl.xco_iter
import Submission.Work.CDcl.xrel_linalg
import Submission.Work.CDcl.g_pullback

/-!
# `Work.CDcl.g_relation`: an independent route to the `ℚ[x]`-relation among the pullbacks

This module proves, without using `Work.CDcl.x_relation`'s chain, the nontrivial `ℚ[x]`-linear
relation `Σ_{k<5} Q k · T k = r` among the pullbacks `T k = (G^{(k)})∘y` of
`G0 = Sym⁺(logP a b ra rb rab r0)`.  It uses

* `Submission.Work.CDcl.xco_ode_P` (the order-two ODE for `P = logP`),
* `Submission.Work.CDcl.g_pullback` (the pulled-back order-two ODE for `Pw = P∘φ`,
  proved independently here),
* `Submission.Work.CDcl.xco_iter` (`Aᵏ (T 0) = T k`), and
* `Submission.Work.CDcl.xrel_linalg` (the linear-algebra step for five vectors in a four- or
  five-dimensional `ℚ(x)`-span).

The normal-form induction (`gr_iterate_Aop_Pfun`, `gr_iterate_Aop_Pwfun`, `gr_xco_norm`) is
reproved here for `Pw` from the pullback ODE of `g_pullback`, so that this route does not
depend on `Submission.Work.CDcl.xco_ode_Pw`.
-/

noncomputable section

open Polynomial PowerSeries

namespace Work.CDcl

theorem grAop_add (x y : LF) : Aop (x + y) = Aop x + Aop y := by
  simp only [Aop, dL_add, mul_add]

/-- `Aop` of a rational multiple of an element. -/
theorem grAop_toL_mul (c : RatFunc ℚ) (x : LF) :
    Aop (toL c * x) = toL (rhoK * Submission.CDT.dRat c) * x + toL c * Aop x := by
  rw [Aop, dL_toL_mul]
  have : rhoL * (toL (Submission.CDT.dRat c) * x + toL c * dL x)
      = (rhoL * toL (Submission.CDT.dRat c)) * x + toL c * (rhoL * dL x) := by ring
  rw [this, ← Aop]
  simp only [rhoL, ← toL_mul]

/-- `Aop` of a rational constant. -/
theorem grAop_toL (c : RatFunc ℚ) : Aop (toL c) = toL (rhoK * Submission.CDT.dRat c) := by
  rw [Aop, dL_toL]
  simp only [rhoL, ← toL_mul]

theorem gr_iterate_Aop_add (k : ℕ) (x y : LF) :
    Aop^[k] (x + y) = Aop^[k] x + Aop^[k] y := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, grAop_add]

/-- `Aop` of `Pfun`. -/
theorem grAop_Pfun (a b : ℚ) (ra rb rab r0 : ℤ) :
    Aop (Pfun a b ra rb rab r0) = toL rhoK * dL (Pfun a b ra rb rab r0) := by
  simp only [Aop, rhoL]

/-- `Aop` of `dL Pfun`, via the ODE `xco_ode_P`. -/
theorem grAop_dL_Pfun (a b : ℚ) (ra rb rab r0 : ℤ) :
    Aop (dL (Pfun a b ra rb rab r0))
      = toL (rhoK * betaK a b) * Pfun a b ra rb rab r0
        + toL (rhoK * alphaK a b) * dL (Pfun a b ra rb rab r0)
        + toL (rhoK * gammaK a b ra rb rab r0) := by
  rw [Aop, xco_ode_P a b ra rb rab r0]
  have h : rhoL * (alphaL a b * dL (Pfun a b ra rb rab r0) + betaL a b * Pfun a b ra rb rab r0
      + gammaL a b ra rb rab r0)
      = toL (rhoK * betaK a b) * Pfun a b ra rb rab r0
        + toL (rhoK * alphaK a b) * dL (Pfun a b ra rb rab r0)
        + toL (rhoK * gammaK a b ra rb rab r0) := by
    rw [show rhoL = toL rhoK from rfl, show alphaL a b = toL (alphaK a b) from rfl,
      show betaL a b = toL (betaK a b) from rfl,
      show gammaL a b ra rb rab r0 = toL (gammaK a b ra rb rab r0) from rfl,
      toL_mul, toL_mul, toL_mul]
    ring
  exact h

/-- `Aop` of `Pwfun`. -/
theorem grAop_Pwfun (a b : ℚ) (ra rb rab r0 : ℤ) :
    Aop (Pwfun a b ra rb rab r0) = toL rhoK * dL (Pwfun a b ra rb rab r0) := by
  simp only [Aop, rhoL]

/-- `Aop` of `dL Pwfun`, via the pullback ODE `g_ode_Pw`. -/
theorem grAop_dL_Pwfun (a b : ℚ) (ra rb rab r0 : ℤ) :
    Aop (dL (Pwfun a b ra rb rab r0))
      = toL (rhoK * betaKt a b) * Pwfun a b ra rb rab r0
        + toL (rhoK * alphaKt a b) * dL (Pwfun a b ra rb rab r0)
        + toL (rhoK * gammaKt a b ra rb rab r0) := by
  rw [Aop, g_ode_Pw a b ra rb rab r0]
  have h : rhoL * (alphaLt a b * dL (Pwfun a b ra rb rab r0)
      + betaLt a b * Pwfun a b ra rb rab r0
      + gammaLt a b ra rb rab r0)
      = toL (rhoK * betaKt a b) * Pwfun a b ra rb rab r0
        + toL (rhoK * alphaKt a b) * dL (Pwfun a b ra rb rab r0)
        + toL (rhoK * gammaKt a b ra rb rab r0) := by
    rw [show rhoL = toL rhoK from rfl, show alphaLt a b = toL (alphaKt a b) from rfl,
      show betaLt a b = toL (betaKt a b) from rfl,
      show gammaLt a b ra rb rab r0 = toL (gammaKt a b ra rb rab r0) from rfl,
      toL_mul, toL_mul, toL_mul]
    ring
  exact h

set_option maxHeartbeats 800000 in
/-- The normal form of `Aop^[k]` on `Pfun`. -/
theorem gr_iterate_Aop_Pfun (a b : ℚ) (ra rb rab r0 : ℤ) (k : ℕ) :
    Aop^[k] (Pfun a b ra rb rab r0)
      = toL ((Pseq a b ra rb rab r0 k).1) * Pfun a b ra rb rab r0
        + toL ((Pseq a b ra rb rab r0 k).2.1) * dL (Pfun a b ra rb rab r0)
        + toL ((Pseq a b ra rb rab r0 k).2.2) := by
  induction k with
  | zero =>
      simp only [Function.iterate_zero_apply, Pseq]
      simp [toL_one, toL_zero]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [Pseq]
      simp only [grAop_add, grAop_toL_mul, grAop_toL, grAop_Pfun, grAop_dL_Pfun]
      simp only [map_mul, map_add]
      ring

set_option maxHeartbeats 800000 in
/-- The normal form of `Aop^[k]` on `Pwfun`. -/
theorem gr_iterate_Aop_Pwfun (a b : ℚ) (ra rb rab r0 : ℤ) (k : ℕ) :
    Aop^[k] (Pwfun a b ra rb rab r0)
      = toL ((Pwseq a b ra rb rab r0 k).1) * Pwfun a b ra rb rab r0
        + toL ((Pwseq a b ra rb rab r0 k).2.1) * dL (Pwfun a b ra rb rab r0)
        + toL ((Pwseq a b ra rb rab r0 k).2.2) := by
  induction k with
  | zero =>
      simp only [Function.iterate_zero_apply, Pwseq]
      simp [toL_one, toL_zero]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [Pwseq]
      simp only [grAop_add, grAop_toL_mul, grAop_toL, grAop_Pwfun, grAop_dL_Pwfun]
      simp only [map_mul, map_add]
      ring

/-- **The normal form of the pullbacks `T k = Aᵏ (T 0)`** (independent route). -/
theorem gr_xco_norm (a b : ℚ) (ra rb rab r0 : ℤ) (k : ℕ) :
    Tfun a b ra rb rab r0 k
      = toL ((Pseq a b ra rb rab r0 k).1) * Pfun a b ra rb rab r0
        + toL ((Pseq a b ra rb rab r0 k).2.1) * dL (Pfun a b ra rb rab r0)
        + toL ((Pwseq a b ra rb rab r0 k).1) * Pwfun a b ra rb rab r0
        + toL ((Pwseq a b ra rb rab r0 k).2.1) * dL (Pwfun a b ra rb rab r0)
        + toL ((Pseq a b ra rb rab r0 k).2.2 + (Pwseq a b ra rb rab r0 k).2.2) := by
  rw [← xco_iter a b ra rb rab r0 k, Tfun_zero]
  rw [show Sfun a b ra rb rab r0 = Pfun a b ra rb rab r0 + Pwfun a b ra rb rab r0 from rfl]
  rw [gr_iterate_Aop_add, gr_iterate_Aop_Pfun, gr_iterate_Aop_Pwfun, toL_add]
  ring

/-- **`Work.CDcl.g_relation`**: a nontrivial `ℚ[x]`-linear relation among the five pullbacks. -/
theorem g_relation (a b : ℚ) (ra rb rab r0 : ℤ) :
    ∃ (Q : Fin 5 → Polynomial ℚ) (r : Polynomial ℚ), Q ≠ 0 ∧
      (∑ k : Fin 5, (Q k : PowerSeries ℚ) * Work.CDcl.T a b ra rb rab r0 k)
        = (r : PowerSeries ℚ) := by
  let U : Fin 5 → Fin 4 → RatFunc ℚ := fun k i =>
    if i = 0 then (Pseq a b ra rb rab r0 (k : ℕ)).1
    else if i = 1 then (Pseq a b ra rb rab r0 (k : ℕ)).2.1
    else if i = 2 then (Pwseq a b ra rb rab r0 (k : ℕ)).1
    else (Pwseq a b ra rb rab r0 (k : ℕ)).2.1
  let D : Fin 5 → RatFunc ℚ := fun k =>
    (Pseq a b ra rb rab r0 (k : ℕ)).2.2 + (Pwseq a b ra rb rab r0 (k : ℕ)).2.2
  have hF : ∀ k : Fin 5,
      Tfun a b ra rb rab r0 (k : ℕ)
        = toL (U k 0) * Pfun a b ra rb rab r0
          + toL (U k 1) * dL (Pfun a b ra rb rab r0)
          + toL (U k 2) * Pwfun a b ra rb rab r0
          + toL (U k 3) * dL (Pwfun a b ra rb rab r0) + toL (D k) := by
    intro k
    have h := gr_xco_norm a b ra rb rab r0 (k : ℕ)
    have h0 : U k 0 = (Pseq a b ra rb rab r0 (k : ℕ)).1 := rfl
    have h1 : U k 1 = (Pseq a b ra rb rab r0 (k : ℕ)).2.1 := rfl
    have h2 : U k 2 = (Pwseq a b ra rb rab r0 (k : ℕ)).1 := rfl
    have h3 : U k 3 = (Pwseq a b ra rb rab r0 (k : ℕ)).2.1 := rfl
    rw [h0, h1, h2, h3]
    exact h
  obtain ⟨Q, r, hQ, hrel⟩ := xrel_linalg (fun k => Tfun a b ra rb rab r0 (k : ℕ))
    (Pfun a b ra rb rab r0) (dL (Pfun a b ra rb rab r0))
    (Pwfun a b ra rb rab r0) (dL (Pwfun a b ra rb rab r0)) U D hF
  refine ⟨Q, r, hQ, ?_⟩
  apply IsFractionRing.injective (PowerSeries ℚ) LF
  have h1 : algebraMap (PowerSeries ℚ) LF
      (∑ k : Fin 5, (Q k : PowerSeries ℚ) * Work.CDcl.T a b ra rb rab r0 (k : ℕ))
      = ∑ k : Fin 5, toL (Q k) * Tfun a b ra rb rab r0 (k : ℕ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hQk : algebraMap (PowerSeries ℚ) LF (Q k : PowerSeries ℚ) = toL (Q k) := by
      simp only [RatFunc.coePolynomial, toL_algebraMap]
    have hTk : algebraMap (PowerSeries ℚ) LF (Work.CDcl.T a b ra rb rab r0 (k : ℕ))
        = Tfun a b ra rb rab r0 (k : ℕ) := rfl
    rw [map_mul, hQk, hTk]
  rw [h1, hrel]
  simp only [RatFunc.coePolynomial, toL_algebraMap]

end Work.CDcl
