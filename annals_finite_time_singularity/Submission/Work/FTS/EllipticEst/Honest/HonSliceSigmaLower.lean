import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.bt_integral_weight_id

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## The primitive of the `σ`-weighted self-form of `Lzero1`

For `σ η θ = sin(2θ)^{-η}` the function

  `H θ = -u'(θ)·u(θ)·σ(θ) + (1/2) u(θ)²·σ'(θ) + (1/2) tan θ·u(θ)²·σ(θ)`

is a primitive of the `σ`-weighted `Lzero1`-self-form: `H'` equals the `σ`-weighted
self-form minus `(u')²σ` and the singular negative potential; `H` vanishes at both
endpoints of `(0, π/2)`, which yields the weighted integration-by-parts identity used
below. -/

/-- The primitive of the `σ`-weighted `Lzero1` self-form. -/
def honPrim (η : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => - deriv u θ * u θ * sig η θ + (1 / 2) * (u θ) ^ 2 * sigD η θ
    + (1 / 2) * Real.tan θ * (u θ) ^ 2 * sig η θ

/-- The `D_z^0`-slot piece of the self-form: `Lzero1 u · u · σ`. -/
def honLz (η : ℝ) (u : ℝ → ℝ) : ℝ → ℝ := fun θ => Lzero1 u θ * u θ * sig η θ

/-- The piece `(u')²σ`. -/
def honDu (η : ℝ) (u : ℝ → ℝ) : ℝ → ℝ := fun θ => (deriv u θ) ^ 2 * sig η θ

/-- The piece `u²σ`. -/
def honU2 (η : ℝ) (u : ℝ → ℝ) : ℝ → ℝ := fun θ => (u θ) ^ 2 * sig η θ

/-- The positive piece `u²σ·(1/2)(1-η)/cos²θ`. -/
def honCc (η : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (u θ) ^ 2 * sig η θ * (1 / 2 * (1 - η) / Real.cos θ ^ 2)

/-- The singular piece `u²cos²(2θ)σ/sin²(2θ)`. -/
def honHc (η : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ / (Real.sin (2 * θ)) ^ 2

/-- The auxiliary weight `u²/sin(2θ)^{2+η}` (the left side of the sharp Hardy bound). -/
def honFull (η : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (u θ) ^ 2 / (Real.sin (2 * θ)) ^ (2 + η)

/-- The derivative of `honPrim η u`: the `σ`-weighted self-form, rearranged. -/
def honPrimDeriv (η : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (honLz η u θ - honDu η u θ - honCc η u θ) + (η + 6) * honU2 η u θ
    + 2 * η * (1 + η) * honHc η u θ

/-- The claim that the primitive `honPrim η u` vanishes at both endpoints. -/
def HonPrimTendstoProp (η : ℝ) (u : ℝ → ℝ) : Prop :=
  Filter.Tendsto (fun θ => - deriv u θ * u θ * sig η θ + (1 / 2) * (u θ) ^ 2 * sigD η θ
        + (1 / 2) * Real.tan θ * (u θ) ^ 2 * sig η θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => - deriv u θ * u θ * sig η θ + (1 / 2) * (u θ) ^ 2 * sigD η θ
        + (1 / 2) * Real.tan θ * (u θ) ^ 2 * sig η θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)

/-! ## Elementary facts on the open interval -/

lemma sin_ne_zero_of_Iθo {θ : ℝ} (hθ : θ ∈ Iθo) : Real.sin θ ≠ 0 :=
  ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))

lemma cos_ne_zero_of_Iθo {θ : ℝ} (hθ : θ ∈ Iθo) : Real.cos θ ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)

lemma sin_two_ne_zero_of_Iθo {θ : ℝ} (hθ : θ ∈ Iθo) : Real.sin (2 * θ) ≠ 0 :=
  ne_of_gt (sin_two_pos_of_Iθo hθ)

lemma sin_two_nonneg_of_Icc {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-! ## The derivative of `sigD` -/

lemma hasDerivAt_sigD (η : ℝ) {θ : ℝ} (hθ : θ ∈ Iθo) :
    HasDerivAt (sigD η)
      (4 * η * sig η θ
        + 4 * η * (1 + η) * (Real.cos (2 * θ) / Real.sin (2 * θ)) ^ 2 * sig η θ) θ := by
  have h := (rho_hasDerivAt η hθ).const_mul (-2 * η)
  have hfun : (fun θ' => -2 * η * rho η θ') = fun θ' => sigD η θ' := by
    funext θ'
    rw [sigD_eq_neg_two_mul_rho]
  rw [hfun] at h
  refine h.congr_deriv ?_
  have hs := sin_two_pos_of_Iθo hθ
  simp only [rhoD, sig]
  rw [show -2 * η * (-2 * (Real.sin (2 * θ)) ^ (-η)
        - 2 * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
      = 4 * η * (Real.sin (2 * θ)) ^ (-η)
        + 4 * η * (η + 1) * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))
      by ring]
  rw [show -(2 + η) = -2 + -η by ring, Real.rpow_add hs]
  rw [show (Real.sin (2 * θ)) ^ (-2 : ℝ) = 1 / (Real.sin (2 * θ)) ^ 2 by
    rw [Real.rpow_neg (le_of_lt hs), Real.rpow_two]
    ring]
  field_simp
  ring

/-! ## The derivative of `tan θ · u θ` -/

lemma deriv_tan_mul {u : ℝ → ℝ} {θ : ℝ} (hu : HasDerivAt u (deriv u θ) θ)
    (hc : Real.cos θ ≠ 0) :
    deriv (fun t => Real.tan t * u t) θ
      = 1 / Real.cos θ ^ 2 * u θ + Real.tan θ * deriv u θ := by
  change deriv (Real.tan * u) θ = 1 / Real.cos θ ^ 2 * u θ + Real.tan θ * deriv u θ
  exact ((Real.hasDerivAt_tan hc).mul hu).deriv

/-- `sigD η θ = -2η·cos(2θ)/sin(2θ)·sig η θ` on the open interval. -/
lemma sigD_eq_ratio (η : ℝ) {θ : ℝ} (hθ : θ ∈ Iθo) :
    sigD η θ = -2 * η * (Real.cos (2 * θ) / Real.sin (2 * θ)) * sig η θ := by
  have hs := sin_two_pos_of_Iθo hθ
  simp only [sigD, sig]
  rw [show -η - 1 = -η + (-1) by ring, Real.rpow_add hs, Real.rpow_neg_one]
  ring

/-! ## The pointwise identity -/

theorem honPrim_hasDerivAt (η : ℝ) (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Iθo)
    (hu : HasDerivAt u (deriv u θ) θ) (hdu : HasDerivAt (deriv u) (deriv (deriv u) θ) θ) :
    HasDerivAt (honPrim η u) (honPrimDeriv η u θ) θ := by
  have hsig : HasDerivAt (sig η) (sigD η θ) θ := sig_hasDerivAt η hθ
  have hsigD := hasDerivAt_sigD η hθ
  have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ :=
    Real.hasDerivAt_tan (cos_ne_zero_of_Iθo hθ)
  have hZ := deriv_tan_mul (u := u) hu (cos_ne_zero_of_Iθo hθ)
  have hA : HasDerivAt (fun θ => deriv u θ * u θ * sig η θ)
      (deriv (deriv u) θ * u θ * sig η θ + deriv u θ * deriv u θ * sig η θ
        + deriv u θ * u θ * sigD η θ) θ := by
    convert ((hdu.mul hu).mul hsig) using 1
    simp only [Pi.mul_apply]
    ring
  have hB : HasDerivAt (fun θ => (u θ) ^ 2 * sigD η θ)
      (2 * u θ * deriv u θ * sigD η θ
        + (u θ) ^ 2 * (4 * η * sig η θ
          + 4 * η * (1 + η) * (Real.cos (2 * θ) / Real.sin (2 * θ)) ^ 2 * sig η θ)) θ := by
    convert ((hu.pow 2).mul hsigD) using 1
    simp only [Pi.pow_apply]
    ring
  have hC : HasDerivAt (fun θ => Real.tan θ * ((u θ) ^ 2 * sig η θ))
      (1 / Real.cos θ ^ 2 * ((u θ) ^ 2 * sig η θ)
        + Real.tan θ * (2 * u θ * deriv u θ * sig η θ + (u θ) ^ 2 * sigD η θ)) θ := by
    convert (htan.mul ((hu.pow 2).mul hsig)) using 1
    simp only [Pi.pow_apply, Pi.mul_apply]
    ring
  have hsum := ((hA.neg.add (hB.const_mul (1 / 2))).add (hC.const_mul (1 / 2)))
  have hfun : honPrim η u = fun θ => - (deriv u θ * u θ * sig η θ)
      + 1 / 2 * ((u θ) ^ 2 * sigD η θ) + 1 / 2 * (Real.tan θ * ((u θ) ^ 2 * sig η θ)) := by
    funext θ
    simp only [honPrim]
    ring
  rw [hfun]
  refine hsum.congr_deriv ?_
  have hsin0 : Real.sin θ ≠ 0 := sin_ne_zero_of_Iθo hθ
  have hcos0 : Real.cos θ ≠ 0 := cos_ne_zero_of_Iθo hθ
  have hs20 : Real.sin (2 * θ) ≠ 0 := sin_two_ne_zero_of_Iθo hθ
  simp only [honPrimDeriv, honLz, honDu, honCc, honU2, honHc, Lzero1]
  rw [hZ]
  rw [sigD_eq_ratio η hθ]
  rw [Real.tan_eq_sin_div_cos, Real.cos_two_mul, Real.sin_two_mul]
  field_simp
  ring_nf

/-! ## The weighted integration by parts identity -/

/-- A property holding on `Iθo = (0, π/2)` holds almost everywhere for `volume` restricted
to `Iθ = [0, π/2]`. -/
lemma eventually_ae_Iθ_of_Ioo {p : ℝ → Prop} (h : ∀ θ ∈ Iθo, p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl,
    Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with θ hθ
  exact h θ hθ

/-- The integral of a function over the open interval `(0, π/2)` equals its integral over
`[0, π/2]` (the two differ by a null set). -/
lemma integral_Icc_eq_integral_Ioo_hon (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in Iθo, g θ := by
  simp only [Work.Spaces.Iθ, Iθo]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **The `σ`-weighted self-form identity of `Lzero1`** (honest class).  Under the honest
regularity (`C²` on the open interval) and the endpoint vanishing of the primitive, the
`σ`-weighted pairing of `Lzero1 u` with `u` splits into four pieces: the derivative energy,
the positive `sec²` term, the mass term and the singular negative term. -/
theorem honSliceIdentity (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u Iθo) (hlim : HonPrimTendstoProp η u)
    (hint_lz : IntegrableOn (honLz η u) Iθo) (hint_du : IntegrableOn (honDu η u) Iθo)
    (hint_u2 : IntegrableOn (honU2 η u) Iθo) (hint_cc : IntegrableOn (honCc η u) Iθo)
    (hint_hc : IntegrableOn (honHc η u) Iθo) :
    (∫ θ in Work.Spaces.Iθ, honLz η u θ)
      = (∫ θ in Work.Spaces.Iθ, honDu η u θ) + (∫ θ in Work.Spaces.Iθ, honCc η u θ)
        - (η + 6) * (∫ θ in Work.Spaces.Iθ, honU2 η u θ)
        - 2 * η * (1 + η) * (∫ θ in Work.Spaces.Iθ, honHc η u θ) := by
  have hderiv : ∀ θ ∈ Iθo, HasDerivAt (honPrim η u) (honPrimDeriv η u θ) θ := by
    intro θ hθ
    have hmem : Iθo ∈ nhds θ := IsOpen.mem_nhds isOpen_Ioo hθ
    have h1 : HasDerivAt u (deriv u θ) θ :=
      ((hu.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
    have h2 : HasDerivAt (deriv u) (deriv (deriv u) θ) θ := by
      have hd : ContDiffOn ℝ 1 (deriv u) Iθo := hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
      exact ((hd.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
    exact honPrim_hasDerivAt η u hθ h1 h2
  have h1 : IntegrableOn (fun θ => honLz η u θ - honDu η u θ - honCc η u θ) Iθo :=
    (hint_lz.sub hint_du).sub hint_cc
  have h2 : IntegrableOn (fun θ => (η + 6) * honU2 η u θ) Iθo := hint_u2.const_mul (η + 6)
  have h3 : IntegrableOn (fun θ => 2 * η * (1 + η) * honHc η u θ) Iθo :=
    hint_hc.const_mul (2 * η * (1 + η))
  have h12 : IntegrableOn
      (fun θ => (honLz η u θ - honDu η u θ - honCc η u θ) + (η + 6) * honU2 η u θ) Iθo :=
    h1.add h2
  have hD : IntegrableOn (honPrimDeriv η u) Iθo := h12.add h3
  have hFTC := integral_Ioo_eq_sub_of_tendsto (a := 0) (b := Real.pi / 2) (m := 0) (l := 0)
    (by linarith [Real.pi_pos]) hderiv hD hlim.1 hlim.2
  have hzero : (∫ θ in Iθo, honPrimDeriv η u θ) = 0 := by
    have h := hFTC
    simp only [Iθo] at h ⊢
    linarith [h]
  have e1 : (∫ θ in Iθo, honPrimDeriv η u θ)
      = (∫ θ in Iθo, (fun θ => (honLz η u θ - honDu η u θ - honCc η u θ)
            + (η + 6) * honU2 η u θ) θ)
        + (∫ θ in Iθo, 2 * η * (1 + η) * honHc η u θ) := integral_add h12 h3
  have e2 : (∫ θ in Iθo, (fun θ => (honLz η u θ - honDu η u θ - honCc η u θ)
            + (η + 6) * honU2 η u θ) θ)
      = (∫ θ in Iθo, honLz η u θ - honDu η u θ - honCc η u θ)
        + (∫ θ in Iθo, (η + 6) * honU2 η u θ) := integral_add h1 h2
  have e3 : (∫ θ in Iθo, honLz η u θ - honDu η u θ - honCc η u θ)
      = (∫ θ in Iθo, honLz η u θ - honDu η u θ) - (∫ θ in Iθo, honCc η u θ) :=
    integral_sub (hint_lz.sub hint_du) hint_cc
  have e4 : (∫ θ in Iθo, honLz η u θ - honDu η u θ)
      = (∫ θ in Iθo, honLz η u θ) - (∫ θ in Iθo, honDu η u θ) :=
    integral_sub hint_lz hint_du
  have e5 : (∫ θ in Iθo, (η + 6) * honU2 η u θ) = (η + 6) * (∫ θ in Iθo, honU2 η u θ) :=
    integral_const_mul _ _
  have e6 : (∫ θ in Iθo, 2 * η * (1 + η) * honHc η u θ)
      = (2 * η * (1 + η)) * (∫ θ in Iθo, honHc η u θ) := integral_const_mul _ _
  have hcomb : (∫ θ in Iθo, honLz η u θ) - (∫ θ in Iθo, honDu η u θ)
      - (∫ θ in Iθo, honCc η u θ) + (η + 6) * (∫ θ in Iθo, honU2 η u θ)
      + 2 * η * (1 + η) * (∫ θ in Iθo, honHc η u θ) = 0 := by
    linarith [hzero, e1, e2, e3, e4, e5, e6]
  rw [← integral_Icc_eq_integral_Ioo_hon (honLz η u),
    ← integral_Icc_eq_integral_Ioo_hon (honDu η u),
    ← integral_Icc_eq_integral_Ioo_hon (honCc η u),
    ← integral_Icc_eq_integral_Ioo_hon (honU2 η u),
    ← integral_Icc_eq_integral_Ioo_hon (honHc η u)] at hcomb
  linarith [hcomb]

/-! ## The comparison of the singular piece with the Hardy weight -/

lemma honHc_le_honFull (η : ℝ) (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Iθo) :
    honHc η u θ ≤ honFull η u θ := by
  have hs := sin_two_pos_of_Iθo hθ
  have hσ : 0 ≤ sig η θ := Real.rpow_nonneg hs.le _
  have hc2 : (Real.cos (2 * θ)) ^ 2 ≤ 1 := by
    have h := Real.abs_cos_le_one (2 * θ)
    nlinarith [abs_nonneg (Real.cos (2 * θ)), sq_nonneg (Real.cos (2 * θ)), abs_le.mp h]
  have hfull : honFull η u θ = (u θ) ^ 2 * sig η θ / (Real.sin (2 * θ)) ^ 2 := by
    simp only [honFull, sig]
    rw [show (2 : ℝ) + η = 2 + η by ring, Real.rpow_add hs (2 : ℝ) η, Real.rpow_two,
      Real.rpow_neg hs.le]
    field_simp
  rw [hfull]
  have hnum : (u θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig η θ ≤ (u θ) ^ 2 * sig η θ := by
    have h2 : 0 ≤ (u θ) ^ 2 * sig η θ := mul_nonneg (sq_nonneg _) hσ
    nlinarith [hc2, h2, sq_nonneg (u θ)]
  exact div_le_div_of_nonneg_right hnum (sq_nonneg _)

theorem HonSliceSigmaLower (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ → ℝ,
      ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
      ContDiffOn ℝ 1 u (Set.Icc 0 (Real.pi / 2)) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.Lzero1 u θ * u θ * (Real.sin (2 * θ)) ^ (-η))
        Work.Spaces.Iθ →
      ((1 - η) / (1 + η)) * (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        ≤ (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 u θ * u θ * (Real.sin (2 * θ)) ^ (-η))
          + K * (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
  obtain ⟨CH, hCH0, hHardyBase⟩ := hardy_shift_two_same_weight η hη0 hη1
  refine ⟨η + 6 + 2 * η * (1 + η) * CH, by positivity, ?_⟩
  intro u hu2 hu1 h0 hπ hint_du hint_ddu hint_u hint_lz
  obtain ⟨C, hC0, hbdIcc, hbdd⟩ := Work.Elliptic.contDiffOn_one_bounds hu1 h0 hπ
  have hb1 : ∀ θ ∈ Iθo, |u θ| ≤ C * θ := fun θ hθ =>
    le_trans (hbdIcc θ (Ioo_subset_Icc_self hθ))
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hC0)
  have hb2 : ∀ θ ∈ Iθo, |u θ| ≤ C * (Real.pi / 2 - θ) := fun θ hθ =>
    le_trans (hbdIcc θ (Ioo_subset_Icc_self hθ))
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hC0)
  have hb3 : ∀ θ ∈ Iθo, |deriv u θ| ≤ C := fun θ hθ => by
    rw [← Real.norm_eq_abs]
    exact hbdd θ hθ
  have hu_cont : ContinuousOn u Iθo := hu2.continuousOn
  have hlim : HonPrimTendstoProp η u :=
    HonPrimitiveTendsto η hη0 hη1 u C hC0 hb1 hb2 hb3
  obtain ⟨hcc, hhc⟩ := HonAuxIntegrable η hη0 hη1 u C hC0 hu_cont hb1 hb2
  have hfull : IntegrableOn (honFull η u) Iθo :=
    HonFullWeightIntegrable η hη0 hη1 u C hC0 hu_cont hb1 hb2
  have hid := honSliceIdentity η hη0 hη1 u hu2 hlim
    (hint_lz.mono_set Ioo_subset_Icc_self) hint_du hint_u hcc hhc
  -- the sharp Hardy bound on the full weight
  have hsin_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => sin_two_nonneg_of_Icc hθ
  have hAeq : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 / (Real.sin (2 * θ)) ^ η)
      = ∫ θ in Work.Spaces.Iθ, honDu η u θ := by
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro θ hθ
    simp only [honDu, sig]
    rw [div_eq_mul_inv, Real.rpow_neg (hsin_nn θ hθ)]
  have hBeq : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 / (Real.sin (2 * θ)) ^ η)
      = ∫ θ in Work.Spaces.Iθ, honU2 η u θ := by
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro θ hθ
    simp only [honU2, sig]
    rw [div_eq_mul_inv, Real.rpow_neg (hsin_nn θ hθ)]
  have hHardy' : (∫ θ in Work.Spaces.Iθ, honFull η u θ)
      ≤ 1 / (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honDu η u θ)
        + CH * (∫ θ in Work.Spaces.Iθ, honU2 η u θ) := by
    have h := hHardyBase u hu1 h0 hπ
    rw [show (1 : ℝ) / (η + 1) ^ 2 = 1 / (1 + η) ^ 2 by ring] at h
    rw [hAeq, hBeq] at h
    exact h
  have hHtG : (∫ θ in Work.Spaces.Iθ, honHc η u θ) ≤ (∫ θ in Work.Spaces.Iθ, honFull η u θ) := by
    have hhcI : IntegrableOn (honHc η u) Work.Spaces.Iθ :=
      hhc.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (a := 0) (b := Real.pi / 2)).symm
    have hfullI : IntegrableOn (honFull η u) Work.Spaces.Iθ :=
      hfull.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (a := 0) (b := Real.pi / 2)).symm
    refine MeasureTheory.integral_mono_of_nonneg ?_ hfullI ?_
    · refine eventually_ae_Iθ_of_Ioo ?_
      intro θ hθ
      have hs := sin_two_pos_of_Iθo hθ
      exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (Real.rpow_nonneg hs.le _)) (sq_nonneg _)
    · refine eventually_ae_Iθ_of_Ioo ?_
      intro θ hθ
      exact honHc_le_honFull η u hθ
  have hHtBound : (∫ θ in Work.Spaces.Iθ, honHc η u θ)
      ≤ 1 / (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honDu η u θ)
        + CH * (∫ θ in Work.Spaces.Iθ, honU2 η u θ) := le_trans hHtG hHardy'
  have hH2 : (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honHc η u θ)
      ≤ (∫ θ in Work.Spaces.Iθ, honDu η u θ)
        + (1 + η) ^ 2 * CH * (∫ θ in Work.Spaces.Iθ, honU2 η u θ) := by
    have hne : (1 + η) ^ 2 ≠ 0 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hHtBound (by positivity : (0:ℝ) ≤ (1 + η) ^ 2)
    have he : (1 + η) ^ 2 * (1 / (1 + η) ^ 2 * (∫ θ in Work.Spaces.Iθ, honDu η u θ)
          + CH * (∫ θ in Work.Spaces.Iθ, honU2 η u θ))
        = (∫ θ in Work.Spaces.Iθ, honDu η u θ)
          + (1 + η) ^ 2 * CH * (∫ θ in Work.Spaces.Iθ, honU2 η u θ) := by
      field_simp
    linarith [h1, he]
  have hCc0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, honCc η u θ := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    refine eventually_ae_Iθ_of_Ioo ?_
    intro θ hθ
    have hs := sin_two_pos_of_Iθo hθ
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _))
      (div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hη1.le)) (sq_nonneg _))
  have hP0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, honU2 η u θ := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    refine eventually_ae_Iθ_of_Ioo ?_
    intro θ hθ
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_pos_of_Iθo hθ).le _)
  have hne1 : (0 : ℝ) < 1 + η := by linarith
  have hmain : (1 + η) * ((1 - η) / (1 + η) * (∫ θ in Work.Spaces.Iθ, honDu η u θ))
      ≤ (1 + η) * ((∫ θ in Work.Spaces.Iθ, honLz η u θ)
        + (η + 6 + 2 * η * (1 + η) * CH) * (∫ θ in Work.Spaces.Iθ, honU2 η u θ)) := by
    have he : (1 + η) * ((1 - η) / (1 + η) * (∫ θ in Work.Spaces.Iθ, honDu η u θ))
        = (1 - η) * (∫ θ in Work.Spaces.Iθ, honDu η u θ) := by
      field_simp
    rw [he]
    nlinarith [hid, hCc0, hH2, hP0]
  exact le_of_mul_le_mul_left hmain hne1

end

end Work.FTS.EllipticEst.Honest
