import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem
import Submission.Work.FTS.EllipticEst.AngClean.IPMem_F_Phi
import Submission.Work.FTS.EllipticEst.Honest.AesmCross.aesmSliceCross
import Submission.Work.FTS.EllipticEst.Honest.AesmCross.aesmProdCross
import Submission.Work.Blocks.HkMem_of_majorant_aesm
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TT.weakIPMems` — the six cross-honesty pairings of the weak level-`0` class

For a datum `(F,Ψ)` of the weak class `TT.EllWeakPos α 0 F Ψ` together with the two Step-1
honesties `HkMem α 0 Ψ` and `HkMem α 0 (z∂_zΨ)`, the six pairings against
`B = ∂_θθΨ = pthIter 2 Ψ` that the Step-2 identity `Σ Iᵢ = -IP F B` consumes are honest
(`AngSecond.IPMem`):

`IPMem F B`, `IPMem (z²∂_zzΨ) B`, `IPMem (z∂_zΨ) B`, `IPMem (∂_θ(tan θ·Ψ)) B`,
`IPMem Ψ B`, `IPMem B B`.

## Route

Five of the six first slots are already known to be honest:

* `F`, `z²∂_zzΨ`, `∂_θθΨ` are the `HkMem α 0` fields of `EllWeakPos`;
* `Ψ` and `z∂_zΨ` are the two additional hypotheses.

All six first slots (and the second slot `B`) agree on the open quadrant with a `C^∞` profile
(`SmoothOpen`): for the smooth profiles this is immediate, and for the source `F` the equation
`bslOp α Ψ = F` identifies `F` there with the smooth `bslOp α Ψ`.  The diagonal honesties
`IPMem g g` come from `HkMem α 0 g` (`AngClean.HkMem_zero_IPMem`), and the mixed honesty
`IPMem g B` then follows from `AngClean.IPMem_of_diag_aesm` (the polarisation
`|g B| ≤ g² + B²`), whose only extra inputs are the a.e. strong measurabilities supplied by
`Honest.AesmCross.aesmSliceCross` and `aesmProdCross` from the two `SmoothOpen` representatives.

The only first slot that is *not* a field or an hypothesis is the angular term
`u = ∂_θ(tan θ·Ψ)`.  Its honesty follows from the equation on the open quadrant, rewritten as

  `∂_θ(tan θ·Ψ) = α²z²∂_zzΨ + F + α(5+α)z∂_zΨ + ∂_θθΨ + 6Ψ`,

each summand of which is `HkMem α 0`; the five-term Cauchy–Schwarz domination of the
`ℋ⁰`-integrand and `Blocks.HkMem_of_majorant_aesm` then give `HkMem α 0 u`.  This is the weak
(`EllWeakPos`) version of `Honest.HonMemU.honMemPthTan`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## Cross honesty from the two diagonal honesties and open-quadrant smoothness -/

/-- **Cross honesty from the two diagonal honesties and open-quadrant smoothness.**

If `g` and `h` are honest (`HkMem α 0`, hence `IPMem` on the diagonal) and each agrees on the
open quadrant with a `C^∞` profile (`AgreeOnQ g g'`, `SmoothOpen g'`, and likewise for `h`),
then the mixed pairing `IPMem g h` is honest. -/
private theorem ipMem_of_agreeOnQ {α : ℝ} {g h g' h' : ℝ → ℝ → ℝ}
    (hg' : Work.FTS.EllipticEst.SmoothOpen g') (hh' : Work.FTS.EllipticEst.SmoothOpen h')
    (hgg : Work.FTS.EllipticEst.AgreeOnQ g g') (hhh : Work.FTS.EllipticEst.AgreeOnQ h h')
    (hmg : Work.Spaces.HkMem α 0 g) (hmh : Work.Spaces.HkMem α 0 h) :
    Work.FTS.EllipticEst.AngSecond.IPMem g h :=
  Work.FTS.EllipticEst.AngClean.IPMem_of_diag_aesm
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmg)
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmh)
    (fun z hz => Work.FTS.EllipticEst.Honest.AesmCross.aesmSliceCross hg' hh' hgg hhh z hz)
    (Work.FTS.EllipticEst.Honest.AesmCross.aesmProdCross hg' hh' hgg hhh)

/-! ## The equation, solved for `∂_θ(tan θ · Ψ)` -/

/-- **`(PolarBSL)` solved for the second derivatives.**  On the open quadrant,
`α² z²∂_zzΨ = -F - α(5+α) z∂_zΨ - ∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`. -/
private theorem EllWeakPos.eq_solve {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      = -F z θ - α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)
        - Work.Spaces.pthIter 2 Ψ z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ := by
  have hb := h.eq z hz θ h0 h1
  rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at hb
  linarith [hb]

/-! ## Helpers for the honesty of `∂_θ(tan θ · Ψ)` -/

/-- The level-`0` `HkIntegrand` vanishes at the left angular boundary. -/
private lemma hki_zero (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z 0 = 0 := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
  simp [Work.Spaces.eta]

/-- The level-`0` `HkIntegrand` vanishes at the right angular boundary. -/
private lemma hki_pi (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
  have hs : Real.sin (2 * (Real.pi / 2)) = 0 := by
    rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  rw [hs]
  simp [Work.Spaces.eta]

/-- The five-term Cauchy–Schwarz inequality, with the common factor `c` factored out. -/
private lemma sq_sum_five (a1 a2 a3 a4 a5 c : ℝ) :
    ((a1 + a2 + a3 + a4 + a5) * c) ^ 2
      ≤ 5 * ((a1 * c) ^ 2 + (a2 * c) ^ 2 + (a3 * c) ^ 2 + (a4 * c) ^ 2 + (a5 * c) ^ 2) := by
  have h1 : (a1 + a2 + a3 + a4 + a5) ^ 2 ≤ 5 * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2 + a4 ^ 2 + a5 ^ 2) := by
    nlinarith [sq_nonneg (a1 - a2), sq_nonneg (a1 - a3), sq_nonneg (a1 - a4),
      sq_nonneg (a1 - a5), sq_nonneg (a2 - a3), sq_nonneg (a2 - a4), sq_nonneg (a2 - a5),
      sq_nonneg (a3 - a4), sq_nonneg (a3 - a5), sq_nonneg (a4 - a5)]
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg c)
  nlinarith [h2]

/-- Integrability on `Iz` of the `θ`-integral of a pointwise sum of two functions, given the
integrability of the angular slices and of the two `θ`-integrals. -/
private theorem integrableOn_integral_add {f g : ℝ → ℝ → ℝ}
    (hf : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ)
    (hg : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => g z θ) Work.Spaces.Iθ)
    (hF : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ) Work.Spaces.Iz)
    (hG : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, g z θ) Work.Spaces.Iz) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ + g z θ) Work.Spaces.Iz := by
  refine (hF.add hG).congr ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    with z hz
  exact (MeasureTheory.integral_add (hf z hz) (hg z hz)).symm

/-- The pointwise majorant of the level-`0` `HkIntegrand` of `∂_θ(tan θ · Ψ)`: it is the sum of
the five summands appearing in the rearranged equation, each dominating term weighted by the
Cauchy–Schwarz constant `5`. -/
private def Mj (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  5 * (Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
    + Work.Spaces.HkIntegrand α 0 F z θ
    + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ
    + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
    + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * Ψ z θ) z θ)

/-- **The pointwise domination.**  If `u = g₁ + ⋯ + g₅` on the open quadrant then the
level-`0` `HkIntegrand` of `u` is dominated on the closed quadrant by `5` times the sum of the
`HkIntegrand`s of the `gᵢ`.

On the open quadrant this is the five-term Cauchy–Schwarz inequality (`sq_sum_five`); on the
boundary it is trivial because the angular weight vanishes there (`HkIntegrand_zero_z`,
`hki_zero`, `hki_pi`). -/
private theorem hki_le_five {α : ℝ} {u g1 g2 g3 g4 g5 : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      u z θ = g1 z θ + g2 z θ + g3 z θ + g4 z θ + g5 z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 u z θ
        ≤ 5 * (Work.Spaces.HkIntegrand α 0 g1 z θ + Work.Spaces.HkIntegrand α 0 g2 z θ
              + Work.Spaces.HkIntegrand α 0 g3 z θ + Work.Spaces.HkIntegrand α 0 g4 z θ
              + Work.Spaces.HkIntegrand α 0 g5 z θ) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ 5 * (Work.Spaces.HkIntegrand α 0 g1 z θ
      + Work.Spaces.HkIntegrand α 0 g2 z θ + Work.Spaces.HkIntegrand α 0 g3 z θ
      + Work.Spaces.HkIntegrand α 0 g4 z θ + Work.Spaces.HkIntegrand α 0 g5 z θ) := by
    intro z θ
    have e1 := Work.Spaces.HkIntegrand_nonneg α 0 g1 z θ
    have e2 := Work.Spaces.HkIntegrand_nonneg α 0 g2 z θ
    have e3 := Work.Spaces.HkIntegrand_nonneg α 0 g3 z θ
    have e4 := Work.Spaces.HkIntegrand_nonneg α 0 g4 z θ
    have e5 := Work.Spaces.HkIntegrand_nonneg α 0 g5 z θ
    linarith
  intro z hz θ hθ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [← hz0, Work.Spaces.HkIntegrand_zero_z]
    exact hnn 0 θ
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · rw [← hθ0, hki_zero]
      exact hnn z 0
    · rcases eq_or_lt_of_le hθ.2 with hθ2 | hθlt
      · rw [hθ2, hki_pi]
        exact hnn z (Real.pi / 2)
      · simp only [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq, h z hzpos θ hθpos hθlt]
        exact sq_sum_five _ _ _ _ _ _

/-! ## Honesty of `∂_θ(tan θ · Ψ)` -/

/-- **`HkMem α 0 (∂_θ(tan θ · Ψ))`.**  The rearranged equation expresses `∂_θ(tan θ·Ψ)` as the
sum of the five `HkMem α 0` profiles `α²z²∂_zzΨ`, `F`, `α(5+α)z∂_zΨ`, `∂_θθΨ`, `6Ψ`, so the
five-term Cauchy–Schwarz domination (`hki_le_five`) of the `ℋ⁰`-integrands closes it. -/
private theorem hkMem_pth_tan_mul (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ)
    (hΨ : Work.Spaces.HkMem α 0 Ψ)
    (hzΨ : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)) :
    Work.Spaces.HkMem α 0 (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) := by
  set u : ℝ → ℝ → ℝ := Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) with hu
  -- `u` is `C^∞` on the open quadrant
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl
  have htanΨ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl htan hΨso
  have htgt : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.SmoothOpen.pth htanΨ
  have hcont := Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand htgt α 0
  -- the a.e. strong measurability of the integrand of `u`
  have haesmJoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have haesmSlice : ∀ z ∈ Work.Spaces.Iz, AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 0 u z θ) (volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [show (fun θ => Work.Spaces.HkIntegrand α 0 u z θ) = fun θ => (0 : ℝ) from by
        funext θ
        rw [← hz0, Work.Spaces.HkIntegrand_zero_z]]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos
  have haesmOuter : AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      (volume.restrict Work.Spaces.Iz) := haesmJoint.integral_prod_right'
  -- the five sample `ℋ⁰` functions
  have hm1 : Work.Spaces.HkMem α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 0 (α ^ 2) h.memA
  have hm2 : Work.Spaces.HkMem α 0 F := h.memF
  have hm3 : Work.Spaces.HkMem α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 0 (α * (5 + α)) hzΨ
  have hm4 : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ) := h.memB
  have hm5 : Work.Spaces.HkMem α 0 (fun z θ => 6 * Ψ z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 0 6 hΨ
  -- integrability of the angular slices of the majorant
  have hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Mj α F Ψ z θ) Work.Spaces.Iθ := by
    intro z hz
    simp only [Mj]
    have h12 : Integrable (fun θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ) (volume.restrict Work.Spaces.Iθ) :=
      (hm1.1 z hz).add (hm2.1 z hz)
    have h123 : Integrable (fun θ => (Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h12.add (hm3.1 z hz)
    have h1234 : Integrable (fun θ => ((Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h123.add (hm4.1 z hz)
    have h12345 : Integrable (fun θ => (((Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * Ψ z θ) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h1234.add (hm5.1 z hz)
    exact h12345.const_mul 5
  -- integrability of the `θ`-integral of the majorant
  have hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Mj α F Ψ z θ) Work.Spaces.Iz := by
    have hs1 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
        (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) Work.Spaces.Iz := hm1.2
    have hs2 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)) Work.Spaces.Iz :=
      integrableOn_integral_add
        (f := fun z θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0 F z θ)
        hm1.1 hm2.1 hm1.2 hm2.2
    have hs3 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        ((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ))
        Work.Spaces.Iz :=
      integrableOn_integral_add (f := fun z θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        (fun z hz => (hm1.1 z hz).add (hm2.1 z hz)) hm3.1 hs2 hm3.2
    have hs4 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)) Work.Spaces.Iz :=
      integrableOn_integral_add (f := fun z θ => (Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        (fun z hz => ((hm1.1 z hz).add (hm2.1 z hz)).add (hm3.1 z hz)) hm4.1 hs3 hm4.2
    have hs5 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        ((((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * Ψ z θ) z θ)) Work.Spaces.Iz :=
      integrableOn_integral_add (f := fun z θ => ((Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * Ψ z θ) z θ)
        (fun z hz => (((hm1.1 z hz).add (hm2.1 z hz)).add (hm3.1 z hz)).add (hm4.1 z hz))
        hm5.1 hs4 hm5.2
    have hkey : (fun z => ∫ θ in Work.Spaces.Iθ, Mj α F Ψ z θ)
        = fun z => 5 * ∫ θ in Work.Spaces.Iθ,
            ((((Work.Spaces.HkIntegrand α 0
              (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
            + Work.Spaces.HkIntegrand α 0 F z θ)
            + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
            + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
            + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * Ψ z θ) z θ) := by
      funext z
      simp only [Mj]
      exact MeasureTheory.integral_const_mul 5 _
    rw [hkey]
    exact hs5.const_mul 5
  -- the pointwise domination
  have hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 u z θ ≤ Mj α F Ψ z θ := by
    have hb := hki_le_five (α := α) (u := u)
      (g1 := fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      (g2 := F) (g3 := fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ))
      (g4 := Work.Spaces.pthIter 2 Ψ) (g5 := fun z θ => 6 * Ψ z θ)
      (fun z hz θ hθ0 hθ1 => by
        have h0 := EllWeakPos.eq_solve h hz hθ0 hθ1
        linarith [h0])
    intro z hz θ hθ
    simp only [Mj]
    exact hb z hz θ hθ
  exact Work.Blocks.HkMem_of_majorant_aesm α 0 haesmSlice haesmOuter hMslice hMz hle

/-! ## The six cross-honesty pairings -/

theorem weakIPMems (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ)
    (hmΨ : Work.Spaces.HkMem α 0 Ψ)
    (hmG : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)) :
    Work.FTS.EllipticEst.AngSecond.IPMem F (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => z * Work.Spaces.pz Ψ z θ)
      (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem Ψ (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem (Work.Spaces.pthIter 2 Ψ)
      (Work.Spaces.pthIter 2 Ψ) := by
  -- `Ψ` is `C^∞` on the open quadrant, hence so are all the profiles below.
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hBso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    (hΨso.pth).pth
  have hAso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
      (hΨso.pzIter 2)
  have hGso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
      hΨso.pz
  have huso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.pth (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hΨso)
  -- the source is the smooth `bslOp α Ψ` on the open quadrant
  have hFso : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨso
  have hFag : Work.FTS.EllipticEst.AgreeOnQ F (Work.Elliptic.bslOp α Ψ) :=
    fun z θ hz hθ0 hθ1 => (h.eq z hz θ hθ0 hθ1).symm
  -- the angular profile `∂_θ(tan θ·Ψ)` is honest
  have hu : Work.Spaces.HkMem α 0
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) :=
    hkMem_pth_tan_mul α F Ψ h hmΨ hmG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ipMem_of_agreeOnQ hFso hBso hFag (fun _ _ _ _ _ => rfl) h.memF h.memB
  · exact ipMem_of_agreeOnQ hAso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      h.memA h.memB
  · exact ipMem_of_agreeOnQ hGso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      hmG h.memB
  · exact ipMem_of_agreeOnQ huso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      hu h.memB
  · exact ipMem_of_agreeOnQ hΨso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      hmΨ h.memB
  · exact ipMem_of_agreeOnQ hBso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      h.memB h.memB

end Work.FTS.EllipticEst.TT
