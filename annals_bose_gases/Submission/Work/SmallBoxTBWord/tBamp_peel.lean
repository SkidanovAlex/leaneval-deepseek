import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Peeling the slot-`i` amplitude `tBamp` (the `kcInsN` slot integral)

`BoseGases.kcInsN n i : kcE3 × X n ≃ᵐ X (n+1)` inserts a one-particle position in the
`i`-th slot.  Because the window `W` of `tBamp` is supported in the one-particle cube
`acube a`, the amplitude `tBamp W p Ψ i x` only depends on `x` *outside* the `i`-th slot;
consequently the ambient integral over `abox (n+1) a` factorises, the `i`-th slot
contributing exactly `volume (acube a) = a³`:

    (a³)⁻¹ ∫_{abox (n+1) a} ‖tBamp W p Φ i x‖² dx
        = ∫_{abox n a} ‖tBamp W p Φ i (kcInsN n i (0,r))‖² dr,

and the remaining amplitude is, at every `r`, the `p`-convention Fourier transform of the
windowed inserted fibre `z ↦ W z·Φ (kcInsN n i (z,r))`.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.SmallBoxTBWord

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1  `tBamp` as a set integral over the window cube -/

/-- Since `W` vanishes off `acube a`, the (unrestricted) defining integral of `tBamp` may
be written as a set integral over the window cube. -/
lemma tBamp_eq_setIntegral {a : ℝ} {W : ℝ³ → ℝ}
    (hWsupp : ∀ z : ℝ³, z ∉ acube a → W z = 0)
    {n : ℕ} {Φ : X (n + 1) → ℝ} (i : Fin (n + 1)) (p : ℝ³) (x : X (n + 1)) :
    tBamp W p Φ i x = ∫ z in acube a,
      (W z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Φ (Function.update x i z) : ℂ) := by
  rw [tBamp]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := acube a)
    (f := fun z : ℝ³ => (W z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Φ (Function.update x i z) : ℂ))
    (fun z hz => by simp [hWsupp z hz])).symm

/-! ## 2  Continuity of the squared amplitude -/

/-- **The squared amplitude is continuous in the configuration.**  In the set-integral
form of §1 the integrand is jointly continuous on `X (n+1) × acube a`, with the
one-particle cube compact. -/
lemma continuous_tBamp_norm_sq {a : ℝ} (ha : 0 < a) {W : ℝ³ → ℝ} (hW : Continuous W)
    (hWsupp : ∀ z : ℝ³, z ∉ acube a → W z = 0)
    {n : ℕ} {Φ : X (n + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (n + 1)) (p : ℝ³) :
    Continuous (fun x : X (n + 1) => ‖tBamp W p Φ i x‖ ^ 2) := by
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
      ∫ z in acube a, (W z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Φ (Function.update x i z) : ℂ)) :=
    Commons.Analysis.Calculus.continuous_setIntegral_isCompact (E := ℂ)
      (acube_compact ha) hF
  refine ((hcont.norm).pow 2).congr (fun x => ?_)
  rw [tBamp_eq_setIntegral hWsupp i p x]
  rfl

/-! ## 3  The amplitude does not depend on the `i`-th slot -/

/-- The `i`-th slot of `tBamp`'s argument is integrated over, so the amplitude is
independent of the value of `x` in that slot. -/
lemma tBamp_kcInsN_indep {W : ℝ³ → ℝ} {n : ℕ} {Φ : X (n + 1) → ℝ}
    (i : Fin (n + 1)) (p : ℝ³) (r : X n) (y y' : ℝ³) :
    tBamp W p Φ i (kcInsN n i (y, r)) = tBamp W p Φ i (kcInsN n i (y', r)) := by
  rw [tBamp]
  refine integral_congr_ae (Eventually.of_forall (fun z => ?_))
  simp only [Work.SmallBoxBridge.Fourier.update_kcInsN]

/-! ## 4  The remaining amplitude is the Fourier transform of the inserted fibre -/

/-- At `x = kcInsN n i (y,r)` the amplitude is the `p`-convention Fourier transform of the
windowed fibre `z ↦ W z·Φ (kcInsN n i (z,r))` (the `tBamp` analogue of
`rawSlotAmp_eq_kinFT`). -/
lemma tBamp_kcInsN_eq_kinFT {W : ℝ³ → ℝ} {n : ℕ} {Φ : X (n + 1) → ℝ}
    (i : Fin (n + 1)) (p : ℝ³) (r : X n) (y : ℝ³) :
    tBamp W p Φ i (kcInsN n i (y, r))
      = kinFT (fun z : ℝ³ => (W z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p := by
  rw [tBamp, kinFT]
  refine integral_congr_ae (Eventually.of_forall (fun z => ?_))
  simp only [Work.SmallBoxBridge.Fourier.update_kcInsN]
  ring

/-! ## 5  The peel -/

theorem tBamp_peel {n : ℕ} {a : ℝ} (ha : 0 < a) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : Continuous W) (hWsupp : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Submission.BoseGases.acube a → W z = 0)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : Continuous Φ)
    (i : Fin (n + 1)) (p : EuclideanSpace ℝ (Fin 3)) :
    (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) a,
        ‖Work.SmallBoxTBWord.tBamp W p Φ i x‖ ^ 2
      = ∫ r in Submission.BoseGases.abox n a,
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (W z : ℂ) *
            (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 := by
  have hcont : Continuous (fun x : X (n + 1) => ‖tBamp W p Φ i x‖ ^ 2) :=
    continuous_tBamp_norm_sq ha hW hWsupp hΦ i p
  have hind : ∀ (r : X n) (y y' : ℝ³),
      ‖tBamp W p Φ i (kcInsN n i (y, r))‖ ^ 2 = ‖tBamp W p Φ i (kcInsN n i (y', r))‖ ^ 2 := by
    intro r y y'
    rw [tBamp_kcInsN_indep i p r y y']
  have hpeel := Work.SmallBoxBridge.Fourier.peel_slot_abox ha i hcont hind
  calc (a ^ 3)⁻¹ * ∫ x in abox (n + 1) a, ‖tBamp W p Φ i x‖ ^ 2
      = ∫ r in abox n a, ‖tBamp W p Φ i (kcInsN n i (0, r))‖ ^ 2 := hpeel
    _ = ∫ r in abox n a,
          ‖kinFT (fun z : ℝ³ => (W z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 := by
        refine integral_congr_ae (Eventually.of_forall (fun r => ?_))
        simp only [tBamp_kcInsN_eq_kinFT i p r 0]

end Work.SmallBoxTBWord
