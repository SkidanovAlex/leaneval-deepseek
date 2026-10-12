import ChallengeDeps
import Submission.Work.BoseFixR.FarZPDefs
import Submission.Work.BoseFixR.IntegrableChatW1sq
import Submission.Work.BoseFixR.LatGreen.coulomb_integral_eq_autocorr
import Submission.Work.ESYRound8.Dict.wScaled_even
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.farLatFourier` — the Coulomb identity `∫ A_W/‖·‖ = 8π·farMass`

The target is the Fourier–Coulomb ("Newtonian energy") identity in the autocorrelation form

  `∫ z, (∫ x, W x · W (x + z)) / ‖z‖ = 8π · (2π)⁻³ ∫ q, Ŵ(q)²/(2‖q‖²)`,

for `W = W₁ = W1fun v h (ell v μ)`.  Equivalently, with `I := ∫ q, Ŵ(q)²/(2‖q‖²)`,

  `4 · (2π)⁻³ · I = (2π)⁻¹ · ∫∫ W(x)W(y)/‖x−y‖`   (`LatGreen.coulomb_fourier_side`)
  `∫∫ W(x)W(y)/‖x−y‖ = ∫ u, (∫ x, W x W(x+u))/‖u‖` (`LatGreen.coulomb_pair_eq_autocorr_integral`)

which multiply to `∫ z, A_W z/‖z‖ = 2π·4·(2π)⁻³·I = 8π·(2π)⁻³·I = 8π·farMass`.

The two corpus lemmas above require a **pointwise** nonnegative kernel, while the corpus only
knows `W₁ ≥ 0` a.e. (`wScaled_g0_nonneg_ae`).  So the whole content of this file is the a.e.
bookkeeping: replace `W` by the pointwise nonnegative representative `W⁺ = max W 0` (even,
`L¹`, a.e. equal to `W`), apply the two lemmas to `W⁺`, and push the result back to `W` using
that both `chat` (`Work.BoseB7AK.C3Q.chat_congr_ae`) and the autocorrelation
(`autocorr_congr_ae` below, via translation invariance of Lebesgue measure) see only the a.e.
class.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseFixR

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The autocorrelation depends only on the a.e. class of the kernel.**

For `U =ᵐ V` and every shift `u`,
`∫ x, U x · U (x + u) = ∫ x, V x · V (x + u)`.

For the second factor one pulls `U =ᵐ V` back along the (measure preserving) translation
`x ↦ x + u` using `Measure.QuasiMeasurePreserving.ae_eq_comp`. -/
lemma autocorr_congr_ae {U V : E3 → ℝ} (h : U =ᵐ[volume] V) (u : E3) :
    (∫ x : E3, U x * U (x + u)) = ∫ x : E3, V x * V (x + u) := by
  refine MeasureTheory.integral_congr_ae ?_
  have h2 : (fun x : E3 => U (x + u)) =ᵐ[volume] (fun x : E3 => V (x + u)) :=
    (MeasureTheory.measurePreserving_add_right (volume : Measure E3) u).quasiMeasurePreserving
      |>.ae_eq_comp h
  filter_upwards [h, h2] with x hx hx2
  rw [hx, hx2]

/-- **The Fourier–Coulomb identity in the autocorrelation form**, for a kernel which is only
nonnegative a.e.

  `∫ z, (∫ x, U x · U (x + z))/‖z‖ = 8π · (2π)⁻³ ∫ q, Û(q)²/(2‖q‖²)`.

Proof: apply `LatGreen.coulomb_fourier_side` and `LatGreen.coulomb_pair_eq_autocorr_integral`
to the pointwise nonnegative representative `U⁺ = max U 0` and transfer the result back along
`U⁺ =ᵐ U`. -/
theorem coulomb_autocorr_eq {U : E3 → ℝ} (hU1 : MeasureTheory.Integrable U)
    (hU0 : 0 ≤ᵐ[volume] U) (hUe : ∀ x, U (-x) = U x)
    (hint : MeasureTheory.Integrable
      (fun q : E3 => (Work.BoseFixR.chat U q) ^ 2 / (2 * ‖q‖ ^ 2))) :
    (∫ z : E3, (∫ x : E3, U x * U (x + z)) / ‖z‖)
      = 8 * Real.pi * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ q : E3, (Work.BoseFixR.chat U q) ^ 2 / (2 * ‖q‖ ^ 2)) := by
  -- the pointwise nonnegative representative `U⁺ = max U 0`
  set Up : E3 → ℝ := fun x => max (U x) 0 with hUp
  have hUp0 : ∀ x, 0 ≤ Up x := fun x => by rw [hUp]; exact le_max_right _ _
  have hUpe : ∀ x, Up (-x) = Up x := fun x => by rw [hUp]; simp only [hUe x]
  have hae : Up =ᵐ[volume] U :=
    hU0.mono (fun x hx => by rw [hUp]; exact max_eq_left hx)
  have hUp1 : MeasureTheory.Integrable Up := hU1.congr hae.symm
  have hintp : MeasureTheory.Integrable
      (fun q : E3 => (Work.BoseFixR.chat Up q) ^ 2 / (2 * ‖q‖ ^ 2)) := by
    refine hint.congr ?_
    filter_upwards with q
    rw [Work.BoseB7AK.C3Q.chat_congr_ae hae q]
  -- the two halves of the identity, at `U⁺`
  have hfour := Work.BoseFixR.LatGreen.coulomb_fourier_side hUp1 hUp0 hUpe hintp
  have hpair := Work.BoseFixR.LatGreen.coulomb_pair_eq_autocorr_integral hUp1 hUp0 hUpe hintp
  -- transfer both sides back to `U`
  have hIp : (∫ q : E3, (Work.BoseFixR.chat Up q) ^ 2 / (2 * ‖q‖ ^ 2))
      = ∫ q : E3, (Work.BoseFixR.chat U q) ^ 2 / (2 * ‖q‖ ^ 2) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with q
    rw [Work.BoseB7AK.C3Q.chat_congr_ae hae q]
  have hKp : (∫ u : E3, (∫ x : E3, Up x * Up (x + u)) / ‖u‖)
      = ∫ u : E3, (∫ x : E3, U x * U (x + u)) / ‖u‖ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with u
    rw [autocorr_congr_ae hae u]
  -- the combined momentum space identity, at `U`
  have key : 4 * ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ q : E3, (Work.BoseFixR.chat U q) ^ 2 / (2 * ‖q‖ ^ 2))
      = (2 * Real.pi)⁻¹ *
        (∫ u : E3, (∫ x : E3, U x * U (x + u)) / ‖u‖) := by
    rw [← hIp, ← hKp, ← hpair]
    exact hfour
  -- inversion of the constant
  have hcancel : (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1 := by
    rw [mul_inv_cancel₀ (by positivity : (2 * Real.pi) ≠ 0)]
  have hK : (∫ u : E3, (∫ x : E3, U x * U (x + u)) / ‖u‖)
      = (2 * Real.pi) * (4 * ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ q : E3, (Work.BoseFixR.chat U q) ^ 2 / (2 * ‖q‖ ^ 2)) := by
    rw [key, ← mul_assoc, hcancel, one_mul]
  rw [hK]
  ring

theorem farLatFourier {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) {μ : ℝ} (hμ : 0 < μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0) :
    (∫ z : EuclideanSpace ℝ (Fin 3),
        (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) x
          * Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) (x + z)) / ‖z‖)
      = 8 * Real.pi * Work.BoseFixR.farMass v h μ := by
  have hℓ : 0 < Work.BoseFixR.ell v μ := Work.BoseFixR.ell_pos' v hμ hav
  -- the kernel `W = W₁`, and its basic properties
  have hWev : ∀ x : E3, Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) (-x)
      = Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) x :=
    fun x => Work.ESYRound8.Dict.wScaled_even (Submission.BoseGases.g0_even hvrad h)
      (Work.BoseFixR.ell v μ) x
  have hW1 : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hW0 : 0 ≤ᵐ[volume] (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) :=
    Submission.BoseGases.wScaled_g0_nonneg_ae hR hv hvrad hv_supp h
  have hint : MeasureTheory.Integrable
      (fun q : E3 => (Work.BoseFixR.chat
        (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)) :=
    Work.BoseFixR.IntegrableChatW1sq h hv hvrad hR hℓ hv_supp hRℓ
  -- the identity, and the definition of `farMass`
  have hmain := coulomb_autocorr_eq hW1 hW0 hWev hint
  have hfar : Work.BoseFixR.farMass v h μ = ((2 * Real.pi) ^ 3)⁻¹ *
      ∫ q : E3, (Work.BoseFixR.chat
        (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2) := rfl
  rw [hfar]
  exact hmain

end Work.BoseFixR
