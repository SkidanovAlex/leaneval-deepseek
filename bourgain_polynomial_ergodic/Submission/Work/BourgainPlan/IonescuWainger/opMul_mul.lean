import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **Associativity of the `L^∞`-action on `L²(𝕋)`.**  The pointwise product of two `L^∞`-classes
acts on `L²` by the composition of the individual actions: `(Φ • Ψ) • G = Φ • (Ψ • G)`. -/
theorem Lp_smul_smul (Φ Ψ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (G : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
    (Φ • Ψ) • G = Φ • (Ψ • G) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := ⊤) (r := ⊤) Φ Ψ,
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) (Φ • Ψ) G,
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) Ψ G,
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) Φ (Ψ • G)] with ξ h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.mul_apply, smul_eq_mul]
  rw [mul_assoc]

-- Multiplicativity of the L-infinity-symbol action on the ell-two sequences: composing the multipliers
-- with symbols Psi and Phi gives the multiplier with the product symbol.  Route: ftLp_opMul rewrites
-- ftLp( opMul Phi (opMul Psi f) ) as Phi bullet (Psi bullet ftLp f) and the associativity of the Lp
-- scalar action turns that into (Phi bullet Psi) bullet ftLp f, which is ftLp( opMul (Phi bullet Psi) f )
-- by ftLp_opMul again; the coefficient sequences then agree.  The landed opMul_opMul is the special
-- case where the product acts as Phi.
theorem opMul_mul (Φ Ψ : MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    Work.BourgainPlan.IonescuWainger.opMul Φ (Work.BourgainPlan.IonescuWainger.opMul Ψ f hf)
        (Work.BourgainPlan.IonescuWainger.opMul_memℓp Ψ f hf)
      = Work.BourgainPlan.IonescuWainger.opMul (Φ • Ψ) f hf := by
  have key : opMulLp Φ (opMul Ψ f hf) (opMul_memℓp Ψ f hf) = opMulLp (Φ • Ψ) f hf := by
    simp only [opMulLp]
    rw [ftLp_opMul Ψ f hf]
    exact (Lp_smul_smul Φ Ψ (ftLp f hf)).symm
  funext n
  show ((fourierBasis (T := 1)).repr (opMulLp Φ (opMul Ψ f hf) (opMul_memℓp Ψ f hf)) : ℤ → ℂ) n
      = ((fourierBasis (T := 1)).repr (opMulLp (Φ • Ψ) f hf) : ℤ → ℂ) n
  rw [key]

end

end Work.BourgainPlan.IonescuWainger
