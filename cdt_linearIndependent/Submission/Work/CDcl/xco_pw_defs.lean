import Mathlib
import Submission.Work.CDcl.xrel_defs

/-!
# The `φ`-pullback of `ℚ⟦x⟧` into `ℚ((x))` (setup for `Work.CDcl.xco_ode_Pw`)

We fix the Möbius involution `φ = sympPhi` and study the ring hom

`σ : ℚ⟦x⟧ → ℚ((x))`,  `σ f = f(φ(x))`  (`= Φ ∘ subst sympPhi`),

together with the multiplier `Ψ = φ' = Φ(sympPhi')`.  The chain rules `dL_sig`, `dL_dL_sig`
turn the order-two ODE satisfied by `P = logP` into the pulled-back ODE for `Pw = P ∘ φ`.
-/

noncomputable section

namespace Work.CDcl

open Polynomial PowerSeries

/-- `σ : ℚ⟦x⟧ → ℚ((x))`, the `φ`-pullback `f ↦ Φ(f∘φ)`. -/
noncomputable def sig : PowerSeries ℚ →+* LF :=
  (algebraMap (PowerSeries ℚ) LF).comp
    (PowerSeries.substAlgHom Submission.CDT.sympPhi_hasSubst).toRingHom

/-- `Ψ = φ' = Φ(sympPhi')` in `ℚ((x))`. -/
noncomputable def PsiL : LF :=
  algebraMap (PowerSeries ℚ) LF ((PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi)

/-- `σ f = algebraMap _ _ (f.subst sympPhi)`. -/
theorem sig_apply (f : PowerSeries ℚ) :
    sig f = algebraMap (PowerSeries ℚ) LF (f.subst Submission.CDT.sympPhi) := by
  simp only [sig, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    PowerSeries.coe_substAlgHom]

/-- `Pwfun` is `σ (logP …)`. -/
theorem Pwfun_eq_sig (a b : ℚ) (ra rb rab r0 : ℤ) :
    Pwfun a b ra rb rab r0 = sig (Submission.CDT.logP a b ra rb rab r0) := by
  rw [Pwfun, sig_apply]

/-- `Ψ = toL (dRat phiK)`. -/
theorem PsiL_eq : PsiL = toL (Submission.CDT.dRat phiK) :=
  Work.CDcl.substPhi_deriv

/-- `dL Ψ = toL (dRat (dRat phiK))`. -/
theorem dL_PsiL_eq : dL PsiL = toL (Submission.CDT.dRat (Submission.CDT.dRat phiK)) := by
  rw [PsiL_eq, dL_toL]

/-- **`σ` on polynomials**: `σ q = toL (q(phiK))`. -/
theorem sig_poly (q : Polynomial ℚ) :
    sig ((q : Polynomial ℚ) : PowerSeries ℚ) = toL (q.eval₂ (algebraMap ℚ K) phiK) := by
  rw [sig_apply]
  exact Work.CDcl.substPhi_poly q

/-- **Chain rule for `σ`**: `(σ f)' = σ(f') · φ'`. -/
theorem dL_sig (f : PowerSeries ℚ) :
    dL (sig f) = sig ((PowerSeries.derivative (R := ℚ)) f) * PsiL := by
  have hsub : (PowerSeries.derivative (R := ℚ)) (f.subst Submission.CDT.sympPhi)
      = ((PowerSeries.derivative (R := ℚ)) f).subst Submission.CDT.sympPhi
        * (PowerSeries.derivative (R := ℚ)) Submission.CDT.sympPhi :=
    PowerSeries.derivative_subst Submission.CDT.sympPhi_hasSubst
  rw [sig_apply, dL_algebraMap, hsub, map_mul]
  simp only [PsiL, sig_apply]

/-- **Second chain rule**: `(σ f)'' = σ(f'') · φ'² + σ(f') · φ''`. -/
theorem dL_dL_sig (f : PowerSeries ℚ) :
    dL (dL (sig f))
      = sig ((PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) f)) * PsiL ^ 2
        + sig ((PowerSeries.derivative (R := ℚ)) f) * dL PsiL := by
  rw [dL_sig f, dL_mul, dL_sig ((PowerSeries.derivative (R := ℚ)) f)]
  ring

end Work.CDcl
