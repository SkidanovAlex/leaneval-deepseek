import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.Ksfr_eq
import Submission.Work.BoseBoxFock.PCFU.dictBricks
import Submission.Work.BoseBoxFock.PCFU.expIntegral_eq_ofReal_cosIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseBoxFock.PCFU.Ksfr_eq_lowKer` — the `lowKer`-form of the `s`-frame evaluation

`Ksfr v fc μ N z = Σ_{s ∈ excited (Lab N)} f_L(s)·e^{i⟪kmom s, z⟫}`
(`Work.BoseBoxFock.pcfFrameDefs`) is the periodised multiplier kernel of the low-cut symbol
`f(‖p‖/κ)`, at `ℓ = ellH v μ` and `κ = ((d)²·sideAt μ (a v))⁻¹`.  `Work.BoseBoxFock.Ksfr_eq`
evaluates it in the *complex phasor* form

    Ksfr v fc μ N z = ℓ³·Σ'_d (2π)⁻³∫_p e^{i⟪p, z + ℓ•latVec d⟫}·f(‖p‖/κ)  − 1 .

The position-space half of the cubic dictionary (`PCFU/dictBricks.lean`) needs the *real* kernel
form, in which the `d`-summand is the kernel of `lowMult`/`lowSlot`, namely

    lowKer fc κ q = (2π)⁻³∫_p f(‖p‖/κ)·cos⟪p, q⟫ ,     q = z + ℓ•latVec d .

The two forms are related by the elementary, but essential, fact that the inverse transform of a
**radial real** symbol is real: `p ↦ f(‖p‖/κ)` is even and `p ↦ -p` preserves Lebesgue measure, so
the sine part `∫_p f(‖p‖/κ)·sin⟪p,q⟫` is the integral of an odd function and vanishes.  That
identity is the delegated sibling module
`Work.BoseBoxFock.PCFU.expIntegral_eq_ofReal_cosIntegral`:

    ∫_p e^{i⟪p,q⟫}·↑(f(‖p‖/κ)) = ↑(∫_p f(‖p‖/κ)·cos⟪p,q⟫) .

Per `d`, unpacking `lowKer` and `Complex.ofReal_mul` therefore gives `lowKer_eq_coeff_mul`
(`lowKer` *is* `(2π)⁻³` times the phasor integral); summing over the latticial images
`d ↦ z + ℓ•latVec d` with `tsum_congr` and transporting through `Ksfr_eq` yields the target.

Everything here is `sorry`-free.
-/

/-- **The per-`d` dictionary step, or: `lowKer` is `(2π)⁻³` times the complex phasor integral.**
Unpacking `lowKer` and `Complex.ofReal_mul` reduces this to the sibling identity
`expIntegral_eq_ofReal_cosIntegral` (the inverse transform of a radial real symbol is real). -/
theorem lowKer_eq_coeff_mul (fc : Work.BoseBoxFix.LowCut) {κ : ℝ} (hκ : 0 < κ) (q : E3) :
    ((lowKer fc κ q : ℝ) : ℂ) =
      ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) *
        ∫ p : E3,
          Complex.exp (Complex.I * (inner ℝ p q : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) := by
  rw [lowKer]
  rw [Complex.ofReal_mul]
  rw [expIntegral_eq_ofReal_cosIntegral fc hκ q]

theorem Ksfr_eq_lowKer {v : EuclideanSpace ℝ (Fin 3) → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ * Work.BoseBoxFock.ellH v μ
      / (2 * Real.pi) ≤ (N : ℝ)) (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.Ksfr v fc μ N z
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3 * (∑' d : Fin 3 → ℤ,
          ((Work.BoseBoxFock.PCFU.lowKer fc
            (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
            (z + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) - 1 := by
  have hmain := Work.BoseBoxFock.Ksfr_eq (v := v) (fc := fc) (μ := μ) (N := N) hℓ hκ hN z
  rw [hmain]
  have hsum : (∑' d : Fin 3 → ℤ, ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) *
        ∫ p : EuclideanSpace ℝ (Fin 3),
          Complex.exp (Complex.I * (inner ℝ p
            (z + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℂ)) *
            ((fc.f (‖p‖ / (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)) : ℝ) : ℂ))
      = ∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
            (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
            (z + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ) :=
    tsum_congr fun d => (lowKer_eq_coeff_mul fc hκ _).symm
  rw [hsum]

end Work.BoseBoxFock.PCFU
