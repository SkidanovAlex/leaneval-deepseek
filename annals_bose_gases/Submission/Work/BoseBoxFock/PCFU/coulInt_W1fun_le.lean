import ChallengeDeps
import Submission.Work.BoseB1Cube.newtonSelfEnergy
import Submission.Work.BoseBoxFock.L1Tails.coulInt_integrable_of_le
import Submission.Work.BoseBoxFock.L1Tails.coulombDual
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
import Submission.Work.BoseFixR.FarLat.g0_coulPot_lintegral_ae_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.coulInt_W1fun_le`

The Coulomb energy of the FS §4 kernel `W₁ = W1fun v h ℓ = wScaled ℓ (g₀)` in the concrete
dilute regime `R ≤ ℓ·chiR0`:

    `∫∫ W₁(x)W₁(y)/‖x−y‖ ≤ 256π²·(a v)`   and   `coulInt W₁ ∈ L¹`.

This is T5 of the `L¹`-tail chapter (`Submission/Work/BoseBoxFock/L1Tails/W1fun_coulomb_le`)
with its abstract regime hypotheses `hC, hr₁, hT, hcond` replaced by the honest concrete one
`hreg : R ≤ ℓ * chiR0` (`ChiWitness.convScale_ge_half_ball` is exactly that hypothesis).

**Route.**  In the dilute regime the renormalisation factor `(χ⋆χ)(·/ℓ)` is `≥ 1/2` on the
support `ball 0 R` of `g₀ = v(1−ω)`, so a.e. `W₁ ≤ 2·g₀` and `0 ≤ W₁`.  The engine
`L1Tails.coulInt_integrable_of_le` (`g := g₀`, `A := W₁`, `c := 2`, `κ := 8π`) then gives
integrability and

    `∫ coulInt W₁ ≤ 2²·8π·∫g₀ = 32π·(8π·a v) = 256π²·(a v)`,

using the single-slice Newtonian bound `∫⁻_y g₀(y)‖x−y‖⁻¹ ≤ 8π` a.e. of
`Work.BoseFixR.FarLat.g0_coulPot_lintegral_ae_le` and `∫g₀ = 8π(a v)`.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem coulInt_W1fun_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hℓ : 0 < ℓ) (hreg : R ≤ ℓ * Submission.BoseGases.chiR0) :
    MeasureTheory.Integrable (Work.BoseBoxFock.coulInt (Work.BoseFixR.W1fun v h ℓ))
      ∧ ∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          Work.BoseBoxFock.coulInt (Work.BoseFixR.W1fun v h ℓ) p ≤ 256 * Real.pi ^ 2 * BoseGases.a v := by
  -- `g₀ = v(1−ω)`: integrable, a.e. nonnegative, mass `8π(a v)`, Newtonian slices `≤ 8π`.
  have hgI : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hgnn : ∀ᵐ x : E3, 0 ≤ Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  have hgmass : (∫ x : E3, Submission.BoseGases.g0 v h x) = 8 * Real.pi * BoseGases.a v :=
    Submission.BoseGases.g0_integral hR hv_supp h
  have hslice : ∀ᵐ x : E3,
      (∫⁻ y : E3, ENNReal.ofReal (Submission.BoseGases.g0 v h y * ‖x - y‖⁻¹))
        ≤ ENNReal.ofReal (8 * Real.pi) :=
    Work.BoseFixR.FarLat.g0_coulPot_lintegral_ae_le (v := v) h hv hvrad hR hv_supp
  -- `W₁ = wScaled ℓ (g₀)`: integrable, a.e. nonnegative, a.e. `≤ 2 g₀`.
  have hW1I : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hreg
  have hW1nn : ∀ᵐ x : E3, 0 ≤ Work.BoseFixR.W1fun v h ℓ x :=
    Submission.BoseGases.wScaled_g0_nonneg_ae hR hv hvrad hv_supp h
  have hW1le : ∀ᵐ x : E3, Work.BoseFixR.W1fun v h ℓ x ≤ 2 * Submission.BoseGases.g0 v h x := by
    have hsupp : ∀ z : E3, R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
      fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
    filter_upwards [hgnn] with x hgx
    have habs : |Work.BoseFixR.W1fun v h ℓ x| ≤ 2 * |Submission.BoseGases.g0 v h x| :=
      Submission.BoseGases.wScaled_abs_le_two hℓ hR.le hreg hsupp x
    rw [abs_of_nonneg hgx] at habs
    exact le_trans (le_abs_self _) habs
  -- the dominated-Coulomb engine
  obtain ⟨hint, hbound⟩ :=
    Work.BoseBoxFock.L1Tails.coulInt_integrable_of_le
      (g := Submission.BoseGases.g0 v h) (A := Work.BoseFixR.W1fun v h ℓ)
      (c := 2) (κ := 8 * Real.pi) (by norm_num) (by positivity)
      hgI hgnn hW1I hW1nn hW1le hslice
  refine ⟨hint, ?_⟩
  calc ∫ p : E3 × E3, Work.BoseBoxFock.coulInt (Work.BoseFixR.W1fun v h ℓ) p
      ≤ 2 ^ 2 * (8 * Real.pi) * (∫ x : E3, Submission.BoseGases.g0 v h x) := hbound
    _ = 2 ^ 2 * (8 * Real.pi) * (8 * Real.pi * BoseGases.a v) := by rw [hgmass]
    _ = 256 * Real.pi ^ 2 * BoseGases.a v := by ring

end Work.BoseBoxFock.PCFU
