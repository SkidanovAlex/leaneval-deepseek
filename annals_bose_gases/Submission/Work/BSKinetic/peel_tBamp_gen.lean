import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.tBamp_peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Peeling the slot-`i` amplitude `tBamp` for a compactly supported window

`BoseGases.kcInsN n i : kcE3 × X n ≃ᵐ X (n+1)` inserts a one-particle position in the
`i`-th slot.  The amplitude `tBamp W p Ψ i x` does not depend on the value of `x` in the
`i`-th slot (that coordinate is integrated over), so the ambient integral over
`abox (n+1) a` factorises with the `i`-th slot contributing exactly `volume (acube a) = a³`:

    (a³)⁻¹ ∫_{abox (n+1) a} ‖tBamp W p Φ i x‖² dx
        = ∫_{abox n a} ‖tBamp W p Φ i (kcInsN n i (0,r))‖² dr,

and the remaining amplitude is, at every `r`, the `p`-convention Fourier transform of the
windowed inserted fibre `z ↦ W z·Φ (kcInsN n i (z,r))`.

This is `SmallBoxTBWord.tBamp_peel`, but for a window that merely *has compact support*
(`W` vanishes off a compact `K`) rather than for a window supported in the cube `acube a`.
The support hypothesis is only ever used to make the defining integral of `tBamp`
convergent and continuous in `x`; the peel itself is insensitive to the shape of the
support, since the slot-`i` coordinate of `x` is integrated over regardless.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BSKinetic

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1  `tBamp` as a set integral over the support -/

/-- Since `W` vanishes off `K`, the (unrestricted) defining integral of `tBamp` may be
written as a set integral over `K`. -/
lemma tBamp_eq_setIntegral_of_support {K : Set ℝ³} {W : ℝ³ → ℝ}
    (hWs : ∀ z : ℝ³, z ∉ K → W z = 0)
    {n : ℕ} {Φ : X (n + 1) → ℝ} (i : Fin (n + 1)) (p : ℝ³) (x : X (n + 1)) :
    Work.SmallBoxTBWord.tBamp W p Φ i x = ∫ z in K,
      (W z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Φ (Function.update x i z) : ℂ) := by
  rw [Work.SmallBoxTBWord.tBamp]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
    (f := fun z : ℝ³ => (W z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Φ (Function.update x i z) : ℂ))
    (fun z hz => by simp [hWs z hz])).symm

/-! ## 2  Continuity of the squared amplitude -/

/-- **The squared amplitude is continuous in the configuration**, for a continuous window of
compact support.  In the set-integral form of §1 the integrand is jointly continuous on
`X (n+1) × K`, with `K` compact. -/
lemma continuous_tBamp_norm_sq_of_support {K : Set ℝ³} (hK : IsCompact K)
    {W : ℝ³ → ℝ} (hW : Continuous W) (hWs : ∀ z : ℝ³, z ∉ K → W z = 0)
    {n : ℕ} {Φ : X (n + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (n + 1)) (p : ℝ³) :
    Continuous (fun x : X (n + 1) => ‖Work.SmallBoxTBWord.tBamp W p Φ i x‖ ^ 2) := by
  have hF : Continuous (Function.uncurry (fun (x : X (n + 1)) (z : ℝ³) =>
      (W z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Φ (Function.update x i z) : ℂ))) := by
    rw [show (Function.uncurry (fun (x : X (n + 1)) (z : ℝ³) =>
        (W z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Φ (Function.update x i z) : ℂ)))
        = fun q : X (n + 1) × ℝ³ => (W q.2 : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ))) *
            (Φ (Function.update q.1 i q.2) : ℂ) from rfl]
    have h1 : Continuous (fun q : X (n + 1) × ℝ³ => (W q.2 : ℂ)) :=
      Complex.continuous_ofReal.comp (hW.comp continuous_snd)
    have h2 : Continuous (fun q : X (n + 1) × ℝ³ =>
        Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ)))) :=
      Complex.continuous_exp.comp
        ((continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_const.inner continuous_snd))).neg)
    have h3 : Continuous (fun q : X (n + 1) × ℝ³ => (Φ (Function.update q.1 i q.2) : ℂ)) :=
      Complex.continuous_ofReal.comp (hΦ.comp (continuous_update i))
    exact (h1.mul h2).mul h3
  have hcont : Continuous (fun x : X (n + 1) =>
      ∫ z in K, (W z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Φ (Function.update x i z) : ℂ)) :=
    Commons.Analysis.Calculus.continuous_setIntegral_isCompact (E := ℂ) hK hF
  refine ((hcont.norm).pow 2).congr (fun x => ?_)
  rw [tBamp_eq_setIntegral_of_support hWs i p x]
  rfl

/-! ## 3  The peel -/

/-- **Peeling the slot-`i` amplitude for a compactly supported continuous window.** -/
theorem peel_tBamp_gen {n : ℕ} {a : ℝ} (ha : 0 < a) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : Continuous W)
    (hWs : ∀ z, z ∉ K → W z = 0)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : Continuous Φ)
    (i : Fin (n + 1)) (p : EuclideanSpace ℝ (Fin 3)) :
    (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) a,
        ‖Work.SmallBoxTBWord.tBamp W p Φ i x‖ ^ 2
      = ∫ r in Submission.BoseGases.abox n a,
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
            (W z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 := by
  have hcont : Continuous (fun x : X (n + 1) => ‖Work.SmallBoxTBWord.tBamp W p Φ i x‖ ^ 2) :=
    BSKinetic.continuous_tBamp_norm_sq_of_support hK hW hWs hΦ i p
  have hind : ∀ (r : X n) (y y' : ℝ³),
      ‖Work.SmallBoxTBWord.tBamp W p Φ i (kcInsN n i (y, r))‖ ^ 2
        = ‖Work.SmallBoxTBWord.tBamp W p Φ i (kcInsN n i (y', r))‖ ^ 2 := by
    intro r y y'
    rw [Work.SmallBoxTBWord.tBamp_kcInsN_indep i p r y y']
  have hpeel := Work.SmallBoxBridge.Fourier.peel_slot_abox ha i hcont hind
  calc (a ^ 3)⁻¹ * ∫ x in abox (n + 1) a, ‖Work.SmallBoxTBWord.tBamp W p Φ i x‖ ^ 2
      = ∫ r in abox n a, ‖Work.SmallBoxTBWord.tBamp W p Φ i (kcInsN n i (0, r))‖ ^ 2 :=
        hpeel
    _ = ∫ r in abox n a,
          ‖kinFT (fun z : ℝ³ => (W z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 := by
        refine integral_congr_ae (Eventually.of_forall (fun r => ?_))
        simp only [Work.SmallBoxTBWord.tBamp_kcInsN_eq_kinFT i p r 0]

end Work.BSKinetic
