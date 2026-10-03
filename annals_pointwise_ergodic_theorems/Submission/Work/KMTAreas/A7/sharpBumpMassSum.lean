/-
# The sharp mass sums of the §6 bumps (`sharpBumpMassSum`)

The `ℓ¹(ℤ)`-mass of the lattice samples of the (inverse) Fourier transform of the bumps
`varphiN N k₁`, `varphitildeN d N k₂` and of their `θ`- and `θ²`-weighted versions.  With
`a := 2^{k₁}/N ≤ 1` (the `mainRegime` hypothesis `2^{k₁} ≤ N`) and `w := 2^{dk₂}/N^d ≤ 1` one has

  `∑_p ‖𝓕⁻(φ_N)(u−p)‖ ≲ 1`,  `∑_p ‖𝓕⁻(θφ_N)(u−p)‖ ≲ a`,  `∑_p ‖𝓕⁻(θ²φ_N)(u−p)‖ ≲ a²`,

and the same for `φ̃_N` with `w` in place of `a`.  These are the *sharp* forms (the companion
results `Work.KMTPlan.A6.bumpFourierMass`, `…bumpFourierMassDeriv` give `(1+a)^j`); the sharpness
in the regime `a ≪ 1` is what makes the `N⁻¹` gain of the §6 mass bound survive.

All the work is done by `bfm_mass_dilated`, `bfm_mass_dilated_deriv` and the `θ²`-analogue proved
here, applied to the bumps written as dilations of the fixed seeds `kmtEta`, `lacψ`, `bfmBump d`
(and of their `θ^j`-weighted versions, whose inverse Fourier transforms again decay quadratically).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.HiFibreDefs
import Submission.Work.KMTPlan.A6.bumpFourierMassDeriv

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger
open Work.KMTContract
open Work.KMTPlan.A6

/-! ## The general `θ²`-weighted dilation estimate -/

/-- Quadratic decay of `𝓕⁻ (θ ↦ θ² · m θ)` for `m` of class `C²` with compact support. -/
theorem bfm_decay_deriv2 (m : ℝ → ℂ) (hcd : ContDiff ℝ 2 m) (hcs : HasCompactSupport m) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
      ‖FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) ^ 2 * m θ) y‖
        ≤ C / (1 + |y|) ^ 2 := by
  have hcd' : ContDiff ℝ 2 (fun θ : ℝ => (θ : ℂ) * m θ) := bfm_contDiff_mul_id m hcd
  have hcs' : HasCompactSupport (fun θ : ℝ => (θ : ℂ) * m θ) :=
    bfm_hasCompactSupport_mul_id m hcs
  have hfun : (fun θ : ℝ => (θ : ℂ) ^ 2 * m θ)
      = fun θ : ℝ => (θ : ℂ) * ((θ : ℂ) * m θ) := by
    funext θ; ring
  rw [hfun]
  exact bfm_decay_deriv (fun θ : ℝ => (θ : ℂ) * m θ) hcd' hcs'

/-- **The lattice mass of the `θ²`-weighted dilation.**  If `𝓕⁻ (θ ↦ θ² m θ)` decays quadratically
with constant `C` then the lattice mass of the `θ²`-weighted Fourier transform of `θ ↦ m (c θ)` is
at most `(C/c²) · 4 (1 + 1/c)`. -/
theorem bfm_mass_dilated_sq {m : ℝ → ℂ} {C c : ℝ} (hc : 0 < c)
    (hdec : ∀ y : ℝ, ‖FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) ^ 2 * m θ) y‖
      ≤ C / (1 + |y|) ^ 2) (u : ℝ) :
    (∑' p : ℤ, ‖∫ θ : ℝ, (θ : ℂ) ^ 2 * m (c * θ) * ee ((u - (p : ℝ)) * θ)‖)
      ≤ (C / c ^ 2) * (4 * (1 + 1 / c)) := by
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hdil : ∀ x : ℝ,
      FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) ^ 2 * m (c * θ)) x
        = (c : ℂ)⁻¹ * ((c : ℂ)⁻¹ * ((c : ℂ)⁻¹
            * FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) ^ 2 * m θ) (x / c))) := by
    intro x
    have hfun : (fun θ : ℝ => (θ : ℂ) ^ 2 * m (c * θ))
        = (c : ℂ)⁻¹ • ((c : ℂ)⁻¹
            • (fun θ : ℝ => (((c * θ : ℝ)) : ℂ) ^ 2 * m (c * θ))) := by
      funext θ
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (((c * θ : ℝ)) : ℂ) = (c : ℂ) * (θ : ℂ) by push_cast; ring]
      field_simp
    rw [hfun, bfm_fourierInv_smul, bfm_fourierInv_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show FourierTransformInv.fourierInv
          (fun θ : ℝ => (((c * θ : ℝ)) : ℂ) ^ 2 * m (c * θ)) x
        = (c : ℂ)⁻¹ * FourierTransformInv.fourierInv
            (fun θ : ℝ => (θ : ℂ) ^ 2 * m θ) (x / c) from
      congrFun (Work.KMTAreas.A7.fourierInv_comp_mul (fun θ : ℝ => (θ : ℂ) ^ 2 * m θ) hc) x]
  have h1 : ∀ p : ℤ,
      (∫ θ : ℝ, (θ : ℂ) ^ 2 * m (c * θ) * ee ((u - (p : ℝ)) * θ))
        = (c : ℂ)⁻¹ * ((c : ℂ)⁻¹ * ((c : ℂ)⁻¹ * FourierTransformInv.fourierInv
            (fun θ : ℝ => (θ : ℂ) ^ 2 * m θ) ((u - (p : ℝ)) / c))) := by
    intro p
    exact (bfm_integral_eq_fourierInv (fun θ : ℝ => (θ : ℂ) ^ 2 * m (c * θ))
      (u - (p : ℝ))).trans (hdil (u - (p : ℝ)))
  -- apply the `θ`-weighted lattice-mass lemma to `g = c⁻¹ 𝓕⁻ (θ² m θ)`
  have hcinv : ‖(c : ℂ)⁻¹‖ = c⁻¹ := by
    rw [norm_inv, show ‖(c : ℂ)‖ = |c| from RCLike.norm_ofReal c, abs_of_pos hc]
  have hdec' : ∀ y : ℝ,
      ‖(c : ℂ)⁻¹ * FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) ^ 2 * m θ) y‖
        ≤ (C / c) / (1 + |y|) ^ 2 := by
    intro y
    rw [norm_mul, hcinv]
    have h1' : c⁻¹ * ‖FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) ^ 2 * m θ) y‖
        ≤ c⁻¹ * (C / (1 + |y|) ^ 2) :=
      mul_le_mul_of_nonneg_left (hdec y) (by positivity)
    refine h1'.trans (le_of_eq ?_)
    have hcne' : c ≠ 0 := hc.ne'
    have hd : (1 + |y|) ^ 2 ≠ 0 := by positivity
    simp only [div_eq_mul_inv]
    field_simp
  have hmain := bfm_tsum_mass_deriv (g := fun y : ℝ =>
      (c : ℂ)⁻¹ * FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) ^ 2 * m θ) y)
    (C := C / c) (c := c) hc hdec' u
  calc (∑' p : ℤ, ‖∫ θ : ℝ, (θ : ℂ) ^ 2 * m (c * θ) * ee ((u - (p : ℝ)) * θ)‖)
      = ∑' p : ℤ, ‖(c : ℂ)⁻¹ * ((c : ℂ)⁻¹ * ((c : ℂ)⁻¹ * FourierTransformInv.fourierInv
            (fun θ : ℝ => (θ : ℂ) ^ 2 * m θ) ((u - (p : ℝ)) / c)))‖ :=
        tsum_congr (fun p => congrArg norm (h1 p))
    _ ≤ (C / c / c) * (4 * (1 + 1 / c)) := hmain
    _ = (C / c ^ 2) * (4 * (1 + 1 / c)) := by
        rw [div_div]
        ring

/-! ## The arithmetic of the absorption -/

/-- **The absorption of the dilation factors.**  If `1/c ≤ A·a` with `A ≥ 1` and `0 ≤ a ≤ 1`,
then `(C/c^j) · 4(1+1/c) ≤ (4(1+A) C A^j) a^j`. -/
theorem arith_absorb {C c a A : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hA : 1 ≤ A) (hx : 1 / c ≤ A * a) (j : ℕ) :
    (C / c ^ j) * (4 * (1 + 1 / c)) ≤ (4 * (1 + A) * C * A ^ j) * a ^ j := by
  have hx0 : (0 : ℝ) ≤ 1 / c := by positivity
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hAa : (1 / c) ^ j ≤ (A * a) ^ j := pow_le_pow_left₀ hx0 hx j
  have hAa0 : (0 : ℝ) ≤ A * a := mul_nonneg hA0 ha0
  have hfour : 4 * (1 + 1 / c) ≤ 4 * (1 + A) := by
    have : 1 / c ≤ A := le_trans hx (by nlinarith [hA0, ha0, ha1, hA])
    linarith
  have hci : C / c ^ j = C * (1 / c) ^ j := by rw [one_div_pow]; ring
  rw [hci]
  have step : C * (1 / c) ^ j * (4 * (1 + 1 / c)) ≤ C * (A * a) ^ j * (4 * (1 + A)) := by
    have h1 : (0 : ℝ) ≤ 4 * (1 + 1 / c) := by linarith
    have h2 : C * (1 / c) ^ j ≤ C * (A * a) ^ j := mul_le_mul_of_nonneg_left hAa hC
    have h3 : (0 : ℝ) ≤ C * (A * a) ^ j := mul_nonneg hC (pow_nonneg hAa0 j)
    nlinarith [h2, hfour, h1, h3]
  refine step.trans (le_of_eq ?_)
  rw [mul_pow]
  ring

/-! ## The `θ`- and `θ²`-weighted mass sums of a dilated seed -/

/-- **The `θ`-weighted mass sum of a dilation.**  If `𝓕⁻ (θ ↦ θ m θ)` decays quadratically and
`1/c ≤ A a`, then the `θ`-weighted mass sum of `θ ↦ m (c θ)` is `≲ A a`. -/
theorem mass_deriv_dilated {m : ℝ → ℂ} {C c a A : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hA : 1 ≤ A) (hx : 1 / c ≤ A * a)
    (hdec : ∀ y : ℝ, ‖FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) * m θ) y‖
      ≤ C / (1 + |y|) ^ 2) (u : ℝ) :
    (∑' p : ℤ, ‖∫ θ : ℝ, (θ : ℂ) * m (c * θ) * ee ((u - (p : ℝ)) * θ)‖)
      ≤ (4 * (1 + A) * C * A) * a := by
  have h := bfm_mass_dilated_deriv (m := m) (C := C) (c := c) hc hdec u
  have h2 := arith_absorb hC hc ha0 ha1 hA hx 1
  refine h.trans ?_
  simpa using h2

/-- **The `θ²`-weighted mass sum of a dilation.** -/
theorem mass_sq_dilated {m : ℝ → ℂ} {C c a A : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hA : 1 ≤ A) (hx : 1 / c ≤ A * a)
    (hdec : ∀ y : ℝ, ‖FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) ^ 2 * m θ) y‖
      ≤ C / (1 + |y|) ^ 2) (u : ℝ) :
    (∑' p : ℤ, ‖∫ θ : ℝ, (θ : ℂ) ^ 2 * m (c * θ) * ee ((u - (p : ℝ)) * θ)‖)
      ≤ (4 * (1 + A) * C * A ^ 2) * a ^ 2 := by
  have h := bfm_mass_dilated_sq (m := m) (C := C) (c := c) hc hdec u
  have h2 := arith_absorb hC hc ha0 ha1 hA hx 2
  refine h.trans ?_
  simpa using h2

/-- **The (unweighted) mass sum of a dilation.** -/
theorem mass_zero_dilated {m : ℝ → ℂ} {C c a A : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hA : 1 ≤ A) (hx : 1 / c ≤ A * a)
    (hdec : ∀ y : ℝ, ‖FourierTransformInv.fourierInv m y‖ ≤ C / (1 + |y|) ^ 2) (u : ℝ) :
    (∑' p : ℤ, ‖∫ θ : ℝ, m (c * θ) * ee ((u - (p : ℝ)) * θ)‖)
      ≤ (4 * (1 + A) * C) * 1 := by
  have h := bfm_mass_dilated (m := m) (C := C) (c := c) hc hdec u
  have h2 := arith_absorb (C := C) (c := c) (a := a) (A := A) hC hc ha0 ha1 hA hx 0
  refine h.trans ?_
  simpa using h2

/-- The big constant of `sharpBumpMassSum`. -/
private def bigConst (D K : ℝ) : ℝ := 1000 * (1 + D) ^ 3 * K

/-- A numerical comparison: `48 K` is dominated by the big constant. -/
private lemma absorb_small {K D c : ℝ} (hK0 : 0 < K) (hD1 : 1 ≤ D) (hc0 : 0 ≤ c)
    (hc : c ≤ 48 * K) : c ≤ bigConst D K := by
  have hK : 0 ≤ K := hK0.le
  have hD8 : (8 : ℝ) ≤ (1 + D) ^ 3 := by
    have h2 : (2 : ℝ) ≤ 1 + D := by linarith
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (1 + D) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
  have hbig : (48 : ℝ) * K ≤ bigConst D K := by
    have h8 : (48 : ℝ) ≤ 48 * (1 + D) ^ 3 := by nlinarith [hD8]
    rw [bigConst]
    nlinarith [h8, hK]
  linarith

/-- A numerical comparison for the `varphitildeN` family: `4(1+D) j C` with `0 ≤ j ≤ D²`
and `C ≤ K` is dominated by the big constant. -/
private lemma absorb_mid {K D C j : ℝ} (hK0 : 0 < K) (hD1 : 1 ≤ D) (hC0 : 0 ≤ C) (hC : C ≤ K)
    (hj0 : 0 ≤ j) (hj : j ≤ D ^ 2) : 4 * (1 + D) * j * C ≤ bigConst D K := by
  have hK : 0 ≤ K := hK0.le
  have hDn : 0 ≤ D := by linarith
  have hD2 : (1 : ℝ) ≤ D ^ 2 := one_le_pow₀ hD1
  have hjc : j * C ≤ D ^ 2 * K := by
    have h1 : j * C ≤ D ^ 2 * C := mul_le_mul_of_nonneg_right hj hC0
    have h2 : D ^ 2 * C ≤ D ^ 2 * K := mul_le_mul_of_nonneg_left hC (by positivity)
    linarith
  have hmono : 4 * (1 + D) * (j * C) ≤ 4 * (1 + D) * (D ^ 2 * K) :=
    mul_le_mul_of_nonneg_left hjc (by positivity)
  have hbig : 4 * (1 + D) * (D ^ 2 * K) ≤ bigConst D K := by
    have hDn1 : (0 : ℝ) ≤ 1 + D := by linarith
    have hsq : D ^ 2 ≤ (1 + D) ^ 2 := by nlinarith [hD1]
    have hkey : 4 * D ^ 2 ≤ 1000 * (1 + D) ^ 2 := by nlinarith [hsq, hDn]
    have h1 : 4 * (1 + D) * D ^ 2 ≤ 1000 * (1 + D) ^ 3 := by
      have h3 : 4 * D ^ 2 * (1 + D) ≤ 1000 * (1 + D) ^ 2 * (1 + D) :=
        mul_le_mul_of_nonneg_right hkey hDn1
      calc 4 * (1 + D) * D ^ 2 = 4 * D ^ 2 * (1 + D) := by ring
        _ ≤ 1000 * (1 + D) ^ 2 * (1 + D) := h3
        _ = 1000 * (1 + D) ^ 3 := by ring
    rw [bigConst]
    nlinarith [h1, hK]
  linarith [hmono, hbig]

/-- **The sharp mass sums of the §6 bumps.**  See the file docstring. -/
theorem sharpBumpMassSum (P : Polynomial ℤ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (N k₁ : ℕ), 1 ≤ N → (2 : ℝ) ^ k₁ ≤ (N : ℝ) → ∀ u : ℝ,
        (∑' p : ℤ, ‖bumpFT (varphiN N k₁) (u - (p : ℝ))‖) ≤ C) ∧
      (∀ (N k₁ : ℕ), 1 ≤ N → (2 : ℝ) ^ k₁ ≤ (N : ℝ) → ∀ u : ℝ,
        (∑' p : ℤ, ‖bumpFT (fun x : ℝ => x * varphiN N k₁ x) (u - (p : ℝ))‖)
          ≤ C * ((2 : ℝ) ^ k₁ / (N : ℝ))) ∧
      (∀ (N k₁ : ℕ), 1 ≤ N → (2 : ℝ) ^ k₁ ≤ (N : ℝ) → ∀ u : ℝ,
        (∑' p : ℤ, ‖bumpFT (fun x : ℝ => x ^ 2 * varphiN N k₁ x) (u - (p : ℝ))‖)
          ≤ C * ((2 : ℝ) ^ k₁ / (N : ℝ)) ^ 2) ∧
      (∀ (N k₂ : ℕ), 1 ≤ N → (2 : ℝ) ^ (P.natDegree * k₂) ≤ (N : ℝ) ^ P.natDegree → ∀ u : ℝ,
        (∑' p : ℤ, ‖bumpFT (varphitildeN P.natDegree N k₂) (u - (p : ℝ))‖) ≤ C) ∧
      (∀ (N k₂ : ℕ), 1 ≤ N → (2 : ℝ) ^ (P.natDegree * k₂) ≤ (N : ℝ) ^ P.natDegree → ∀ u : ℝ,
        (∑' p : ℤ, ‖bumpFT (fun x : ℝ => x * varphitildeN P.natDegree N k₂ x) (u - (p : ℝ))‖)
          ≤ C * ((2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree)) ∧
      (∀ (N k₂ : ℕ), 1 ≤ N → (2 : ℝ) ^ (P.natDegree * k₂) ≤ (N : ℝ) ^ P.natDegree → ∀ u : ℝ,
        (∑' p : ℤ, ‖bumpFT (fun x : ℝ => x ^ 2 * varphitildeN P.natDegree N k₂ x) (u - (p : ℝ))‖)
          ≤ C * ((2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) ^ 2) := by
  obtain ⟨Cφ0, hφ0pos, hφ0⟩ := bfm_decay_kmtEta
  obtain ⟨Cψ0, hψ0pos, hψ0⟩ := bfm_decay_lacψ
  obtain ⟨CB0, hB0pos, hB0⟩ := bfm_decay_bfmBump P.natDegree
  obtain ⟨Cφ1, hφ1pos, hφ1⟩ := bfm_decay_kmtEta_deriv
  obtain ⟨Cψ1, hψ1pos, hψ1⟩ := bfm_decay_lacψ_deriv
  obtain ⟨CB1, hB1pos, hB1⟩ := bfm_decay_bfmBump_deriv P.natDegree
  obtain ⟨Cφ2, hφ2pos, hφ2⟩ :=
    bfm_decay_deriv2 kmtEta (bfm_contDiff_kmtEta 2) bfm_hasCompactSupport_kmtEta
  obtain ⟨Cψ2, hψ2pos, hψ2⟩ :=
    bfm_decay_deriv2 Work.KMTAreas.A7.lacψ
      (by rw [← bfmBump_one]; exact contDiff_bfmBump 1)
      (by rw [← bfmBump_one]; exact hasCompactSupport_bfmBump 1)
  obtain ⟨CB2, hB2pos, hB2⟩ :=
    bfm_decay_deriv2 (bfmBump P.natDegree) (contDiff_bfmBump P.natDegree)
      (hasCompactSupport_bfmBump P.natDegree)
  set K : ℝ := Cφ0 + Cψ0 + CB0 + Cφ1 + Cψ1 + CB1 + Cφ2 + Cψ2 + CB2 + 1 with hK
  have hK0 : 0 < K := by
    rw [hK]; linarith [hφ0pos, hψ0pos, hB0pos, hφ1pos, hψ1pos, hB1pos, hφ2pos, hψ2pos, hB2pos]
  have hKge : ∀ x ∈ ({Cφ0, Cψ0, CB0, Cφ1, Cψ1, CB1, Cφ2, Cψ2, CB2} : Finset ℝ), x ≤ K := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [hK]; rcases hx with h|h|h|h|h|h|h|h|h <;> linarith
  have hKφ0 : Cφ0 ≤ K := by rw [hK]; linarith
  have hKψ0 : Cψ0 ≤ K := by rw [hK]; linarith
  have hKB0 : CB0 ≤ K := by rw [hK]; linarith
  have hKφ1 : Cφ1 ≤ K := by rw [hK]; linarith
  have hKψ1 : Cψ1 ≤ K := by rw [hK]; linarith
  have hKB1 : CB1 ≤ K := by rw [hK]; linarith
  have hKφ2 : Cφ2 ≤ K := by rw [hK]; linarith
  have hKψ2 : Cψ2 ≤ K := by rw [hK]; linarith
  have hKB2 : CB2 ≤ K := by rw [hK]; linarith
  set D : ℝ := (2 : ℝ) ^ P.natDegree with hD
  have hD1 : (1 : ℝ) ≤ D := one_le_pow₀ (by norm_num)
  have hD0 : (0 : ℝ) < D := by linarith
  refine ⟨1000 * (1 + D) ^ 3 * K,
    by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `j = 0`, `varphiN`
    intro N k₁ hN hk u
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    rcases Nat.eq_zero_or_pos k₁ with hk0 | hkpos
    · subst hk0
      rw [bfm_varphiN_zero N]
      simp only [bumpFT]
      have hc : (0 : ℝ) < (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have ha0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      have ha1 : (1 : ℝ) / (N : ℝ) ≤ 1 := by rw [div_le_one hNpos]; exact hN1
      have hx : 1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) ≤ 2 * (1 / (N : ℝ)) := by
        have h := bfm_inv_pow_logN_le hN
        rw [show (2 : ℝ) / (N : ℝ) = 2 * (1 / (N : ℝ)) by ring] at h
        exact h
      have h := mass_zero_dilated (m := kmtEta) (C := Cφ0) (c :=
        (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) (a := 1 / (N : ℝ)) (A := 2)
        hφ0pos.le hc ha0 ha1 (by norm_num) hx hφ0 u
      refine h.trans ?_
      have hc4 : 4 * (1 + 2) * Cφ0 ≤
          1000 * (1 + D) ^ 3 * K :=
        by simpa [bigConst] using absorb_small hK0 hD1 (by positivity) (by nlinarith [hKφ0, hK0, hD1, sq_nonneg D])
      simpa using hc4
    · rw [bfm_varphiN_pos N k₁ hkpos]
      simp only [bumpFT]
      have hc : (0 : ℝ) < Work.KMTAreas.A7.lacσ N k₁ := Work.KMTAreas.A7.lacσ_pos N k₁
      have ha0 : (0 : ℝ) ≤ (2 : ℝ) ^ k₁ / (N : ℝ) := by positivity
      have ha1 : (2 : ℝ) ^ k₁ / (N : ℝ) ≤ 1 := by rw [div_le_one hNpos]; exact hk
      have hx : 1 / Work.KMTAreas.A7.lacσ N k₁ ≤ 2 * ((2 : ℝ) ^ k₁ / (N : ℝ)) := by
        have h := bfm_inv_lacσ_le (N := N) (k := k₁) hN
        rw [show 2 * (2 : ℝ) ^ k₁ / (N : ℝ) = 2 * ((2 : ℝ) ^ k₁ / (N : ℝ)) by ring] at h
        exact h
      have h := mass_zero_dilated (m := Work.KMTAreas.A7.lacψ) (C := Cψ0) (c :=
        Work.KMTAreas.A7.lacσ N k₁) (a := (2 : ℝ) ^ k₁ / (N : ℝ)) (A := 2)
        hψ0pos.le hc ha0 ha1 (by norm_num) hx hψ0 u
      refine h.trans ?_
      have hc4 : 4 * (1 + 2) * Cψ0 ≤
          1000 * (1 + D) ^ 3 * K :=
        by simpa [bigConst] using absorb_small hK0 hD1 (by positivity) (by nlinarith [hKψ0, hK0, hD1, sq_nonneg D])
      simpa using hc4
  · -- `j = 1`, `varphiN`
    intro N k₁ hN hk u
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    rcases Nat.eq_zero_or_pos k₁ with hk0 | hkpos
    · subst hk0
      rw [bfm_varphiN_zero N]
      simp only [bumpFT]
      have hc : (0 : ℝ) < (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have ha0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      have ha1 : (1 : ℝ) / (N : ℝ) ≤ 1 := by rw [div_le_one hNpos]; exact hN1
      have hx : 1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) ≤ 2 * (1 / (N : ℝ)) := by
        have h := bfm_inv_pow_logN_le hN
        rw [show (2 : ℝ) / (N : ℝ) = 2 * (1 / (N : ℝ)) by ring] at h
        exact h
      have h := mass_deriv_dilated (m := kmtEta) (C := Cφ1) (c :=
        (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) (a := 1 / (N : ℝ)) (A := 2)
        hφ1pos.le hc ha0 ha1 (by norm_num) hx hφ1 u
      refine h.trans ?_
      have hc4 : 4 * (1 + 2) * Cφ1 * 2 ≤
          1000 * (1 + D) ^ 3 * K :=
        by simpa [bigConst] using absorb_small hK0 hD1 (by positivity) (by nlinarith [hKφ1, hK0, hD1, sq_nonneg D])
      have := mul_le_mul_of_nonneg_right hc4 ha0
      simpa using this
    · rw [bfm_varphiN_pos N k₁ hkpos]
      simp only [bumpFT]
      have hc : (0 : ℝ) < Work.KMTAreas.A7.lacσ N k₁ := Work.KMTAreas.A7.lacσ_pos N k₁
      have ha0 : (0 : ℝ) ≤ (2 : ℝ) ^ k₁ / (N : ℝ) := by positivity
      have ha1 : (2 : ℝ) ^ k₁ / (N : ℝ) ≤ 1 := by rw [div_le_one hNpos]; exact hk
      have hx : 1 / Work.KMTAreas.A7.lacσ N k₁ ≤ 2 * ((2 : ℝ) ^ k₁ / (N : ℝ)) := by
        have h := bfm_inv_lacσ_le (N := N) (k := k₁) hN
        rw [show 2 * (2 : ℝ) ^ k₁ / (N : ℝ) = 2 * ((2 : ℝ) ^ k₁ / (N : ℝ)) by ring] at h
        exact h
      have h := mass_deriv_dilated (m := Work.KMTAreas.A7.lacψ) (C := Cψ1) (c :=
        Work.KMTAreas.A7.lacσ N k₁) (a := (2 : ℝ) ^ k₁ / (N : ℝ)) (A := 2)
        hψ1pos.le hc ha0 ha1 (by norm_num) hx hψ1 u
      refine h.trans ?_
      have hc4 : 4 * (1 + 2) * Cψ1 * 2 ≤
          1000 * (1 + D) ^ 3 * K :=
        by simpa [bigConst] using absorb_small hK0 hD1 (by positivity) (by nlinarith [hKψ1, hK0, hD1, sq_nonneg D])
      have := mul_le_mul_of_nonneg_right hc4 ha0
      simpa using this
  · -- `j = 2`, `varphiN`
    intro N k₁ hN hk u
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    rcases Nat.eq_zero_or_pos k₁ with hk0 | hkpos
    · subst hk0
      rw [bfm_varphiN_zero N]
      simp only [bumpFT]
      have hc : (0 : ℝ) < (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have ha0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      have ha1 : (1 : ℝ) / (N : ℝ) ≤ 1 := by rw [div_le_one hNpos]; exact hN1
      have hx : 1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) ≤ 2 * (1 / (N : ℝ)) := by
        have h := bfm_inv_pow_logN_le hN
        rw [show (2 : ℝ) / (N : ℝ) = 2 * (1 / (N : ℝ)) by ring] at h
        exact h
      have h := mass_sq_dilated (m := kmtEta) (C := Cφ2) (c :=
        (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) (a := 1 / (N : ℝ)) (A := 2)
        hφ2pos.le hc ha0 ha1 (by norm_num) hx hφ2 u
      refine h.trans ?_
      have hc4 : 4 * (1 + 2) * Cφ2 * 2 ^ 2 ≤
          1000 * (1 + D) ^ 3 * K :=
        by simpa [bigConst] using absorb_small hK0 hD1 (by positivity) (by nlinarith [hKφ2, hK0, hD1, sq_nonneg D])
      have := mul_le_mul_of_nonneg_right hc4 (pow_nonneg ha0 2)
      simpa using this
    · rw [bfm_varphiN_pos N k₁ hkpos]
      simp only [bumpFT]
      have hc : (0 : ℝ) < Work.KMTAreas.A7.lacσ N k₁ := Work.KMTAreas.A7.lacσ_pos N k₁
      have ha0 : (0 : ℝ) ≤ (2 : ℝ) ^ k₁ / (N : ℝ) := by positivity
      have ha1 : (2 : ℝ) ^ k₁ / (N : ℝ) ≤ 1 := by rw [div_le_one hNpos]; exact hk
      have hx : 1 / Work.KMTAreas.A7.lacσ N k₁ ≤ 2 * ((2 : ℝ) ^ k₁ / (N : ℝ)) := by
        have h := bfm_inv_lacσ_le (N := N) (k := k₁) hN
        rw [show 2 * (2 : ℝ) ^ k₁ / (N : ℝ) = 2 * ((2 : ℝ) ^ k₁ / (N : ℝ)) by ring] at h
        exact h
      have h := mass_sq_dilated (m := Work.KMTAreas.A7.lacψ) (C := Cψ2) (c :=
        Work.KMTAreas.A7.lacσ N k₁) (a := (2 : ℝ) ^ k₁ / (N : ℝ)) (A := 2)
        hψ2pos.le hc ha0 ha1 (by norm_num) hx hψ2 u
      refine h.trans ?_
      have hc4 : 4 * (1 + 2) * Cψ2 * 2 ^ 2 ≤
          1000 * (1 + D) ^ 3 * K :=
        by simpa [bigConst] using absorb_small hK0 hD1 (by positivity) (by nlinarith [hKψ2, hK0, hD1, sq_nonneg D])
      have := mul_le_mul_of_nonneg_right hc4 (pow_nonneg ha0 2)
      simpa using this
  · -- `j = 0`, `varphitildeN`
    intro N k₂ hN hk u
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hNpow : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
    rcases Nat.eq_zero_or_pos k₂ with hk0 | hkpos
    · subst hk0
      rw [bfm_varphitildeN_zero P.natDegree N]
      simp only [bumpFT, mul_zero, pow_zero]
      have hc : (0 : ℝ) < (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have ha0 : (0 : ℝ) ≤ 1 / (N : ℝ) ^ P.natDegree := by positivity
      have ha1 : (1 : ℝ) / (N : ℝ) ^ P.natDegree ≤ 1 := by
        rw [div_le_one hNpow]; exact one_le_pow₀ hN1
      have hx : 1 / (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))
          ≤ D * (1 / (N : ℝ) ^ P.natDegree) := by
        have h := bfm_inv_etaScale_le (d := P.natDegree) (N := N) hN
        rw [hD]
        rw [show (2 : ℝ) ^ P.natDegree / (N : ℝ) ^ P.natDegree
            = (2 : ℝ) ^ P.natDegree * (1 / (N : ℝ) ^ P.natDegree) by ring] at h
        exact h
      have h := mass_zero_dilated (m := kmtEta) (C := Cφ0) (c :=
        (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)))
        (a := 1 / (N : ℝ) ^ P.natDegree) (A := D)
        hφ0pos.le hc ha0 ha1 hD1 hx hφ0 u
      refine h.trans ?_
      have hc4 : 4 * (1 + D) * Cφ0 ≤
          1000 * (1 + D) ^ 3 * K :=
        by simpa [bigConst] using absorb_mid (K := K) (D := D) (C := Cφ0) (j := 1) hK0 hD1 (by positivity) hKφ0 (by nlinarith [hD1]) (by nlinarith [hD1])
      simpa using hc4
    · rw [bfm_varphitildeN_pos P.natDegree N k₂ hkpos]
      simp only [bumpFT]
      have hc : (0 : ℝ) < bfmTildeScale P.natDegree N k₂ := by
        rw [bfmTildeScale]; exact Real.rpow_pos_of_pos (by norm_num) _
      have ha0 : (0 : ℝ) ≤ (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree := by positivity
      have ha1 : (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree ≤ 1 := by
        rw [div_le_one hNpow]; exact hk
      have hx : 1 / bfmTildeScale P.natDegree N k₂ ≤ D * ((2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) := by
        have h := bfm_inv_tildeScale_le (d := P.natDegree) (N := N) (k := k₂) hN
        rw [hD]
        rw [show (2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree
            = (2 : ℝ) ^ P.natDegree
              * ((2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) by ring] at h
        exact h
      have h := mass_zero_dilated (m := bfmBump P.natDegree) (C := CB0) (c :=
        bfmTildeScale P.natDegree N k₂)
        (a := (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) (A := D)
        hB0pos.le hc ha0 ha1 hD1 hx hB0 u
      refine h.trans ?_
      have hc4 : 4 * (1 + D) * CB0 ≤
          1000 * (1 + D) ^ 3 * K :=
        by simpa [bigConst] using absorb_mid (K := K) (D := D) (C := CB0) (j := 1) hK0 hD1 (by positivity) hKB0 (by nlinarith [hD1]) (by nlinarith [hD1])
      simpa using hc4
  · -- `j = 1`, `varphitildeN`
    intro N k₂ hN hk u
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hNpow : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
    rcases Nat.eq_zero_or_pos k₂ with hk0 | hkpos
    · subst hk0
      rw [bfm_varphitildeN_zero P.natDegree N]
      simp only [bumpFT, mul_zero, pow_zero]
      have hc : (0 : ℝ) < (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have ha0 : (0 : ℝ) ≤ 1 / (N : ℝ) ^ P.natDegree := by positivity
      have ha1 : (1 : ℝ) / (N : ℝ) ^ P.natDegree ≤ 1 := by
        rw [div_le_one hNpow]; exact one_le_pow₀ hN1
      have hx : 1 / (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))
          ≤ D * (1 / (N : ℝ) ^ P.natDegree) := by
        have h := bfm_inv_etaScale_le (d := P.natDegree) (N := N) hN
        rw [hD]
        rw [show (2 : ℝ) ^ P.natDegree / (N : ℝ) ^ P.natDegree
            = (2 : ℝ) ^ P.natDegree * (1 / (N : ℝ) ^ P.natDegree) by ring] at h
        exact h
      have h := mass_deriv_dilated (m := kmtEta) (C := Cφ1) (c :=
        (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)))
        (a := 1 / (N : ℝ) ^ P.natDegree) (A := D)
        hφ1pos.le hc ha0 ha1 hD1 hx hφ1 u
      refine h.trans ?_
      have hc4 : 4 * (1 + D) * Cφ1 * D ≤
          1000 * (1 + D) ^ 3 * K := by
        have hmid := absorb_mid (K := K) (D := D) (C := Cφ1) (j := D) hK0 hD1 (by positivity) hKφ1 (by nlinarith [hD1]) (by nlinarith [hD1])
        simpa [bigConst, mul_comm, mul_left_comm, mul_assoc] using hmid
      have := mul_le_mul_of_nonneg_right hc4 ha0
      simpa using this
    · rw [bfm_varphitildeN_pos P.natDegree N k₂ hkpos]
      simp only [bumpFT]
      have hc : (0 : ℝ) < bfmTildeScale P.natDegree N k₂ := by
        rw [bfmTildeScale]; exact Real.rpow_pos_of_pos (by norm_num) _
      have ha0 : (0 : ℝ) ≤ (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree := by positivity
      have ha1 : (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree ≤ 1 := by
        rw [div_le_one hNpow]; exact hk
      have hx : 1 / bfmTildeScale P.natDegree N k₂ ≤ D * ((2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) := by
        have h := bfm_inv_tildeScale_le (d := P.natDegree) (N := N) (k := k₂) hN
        rw [hD]
        rw [show (2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree
            = (2 : ℝ) ^ P.natDegree
              * ((2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) by ring] at h
        exact h
      have h := mass_deriv_dilated (m := bfmBump P.natDegree) (C := CB1) (c :=
        bfmTildeScale P.natDegree N k₂)
        (a := (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) (A := D)
        hB1pos.le hc ha0 ha1 hD1 hx hB1 u
      refine h.trans ?_
      have hc4 : 4 * (1 + D) * CB1 * D ≤
          1000 * (1 + D) ^ 3 * K := by
        have hmid := absorb_mid (K := K) (D := D) (C := CB1) (j := D) hK0 hD1 (by positivity) hKB1 (by nlinarith [hD1]) (by nlinarith [hD1])
        simpa [bigConst, mul_comm, mul_left_comm, mul_assoc] using hmid
      have := mul_le_mul_of_nonneg_right hc4 ha0
      simpa using this
  · -- `j = 2`, `varphitildeN`
    intro N k₂ hN hk u
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hNpow : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
    rcases Nat.eq_zero_or_pos k₂ with hk0 | hkpos
    · subst hk0
      rw [bfm_varphitildeN_zero P.natDegree N]
      simp only [bumpFT, mul_zero, pow_zero]
      have hc : (0 : ℝ) < (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have ha0 : (0 : ℝ) ≤ 1 / (N : ℝ) ^ P.natDegree := by positivity
      have ha1 : (1 : ℝ) / (N : ℝ) ^ P.natDegree ≤ 1 := by
        rw [div_le_one hNpow]; exact one_le_pow₀ hN1
      have hx : 1 / (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))
          ≤ D * (1 / (N : ℝ) ^ P.natDegree) := by
        have h := bfm_inv_etaScale_le (d := P.natDegree) (N := N) hN
        rw [hD]
        rw [show (2 : ℝ) ^ P.natDegree / (N : ℝ) ^ P.natDegree
            = (2 : ℝ) ^ P.natDegree * (1 / (N : ℝ) ^ P.natDegree) by ring] at h
        exact h
      have h := mass_sq_dilated (m := kmtEta) (C := Cφ2) (c :=
        (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)))
        (a := 1 / (N : ℝ) ^ P.natDegree) (A := D)
        hφ2pos.le hc ha0 ha1 hD1 hx hφ2 u
      refine h.trans ?_
      have hc4 : 4 * (1 + D) * Cφ2 * D ^ 2 ≤
          1000 * (1 + D) ^ 3 * K := by
        have hmid := absorb_mid (K := K) (D := D) (C := Cφ2) (j := D ^ 2) hK0 hD1 (by positivity) hKφ2 (by nlinarith [hD1]) (by nlinarith [hD1])
        simpa [bigConst, mul_comm, mul_left_comm, mul_assoc] using hmid
      have := mul_le_mul_of_nonneg_right hc4 (pow_nonneg ha0 2)
      simpa using this
    · rw [bfm_varphitildeN_pos P.natDegree N k₂ hkpos]
      simp only [bumpFT]
      have hc : (0 : ℝ) < bfmTildeScale P.natDegree N k₂ := by
        rw [bfmTildeScale]; exact Real.rpow_pos_of_pos (by norm_num) _
      have ha0 : (0 : ℝ) ≤ (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree := by positivity
      have ha1 : (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree ≤ 1 := by
        rw [div_le_one hNpow]; exact hk
      have hx : 1 / bfmTildeScale P.natDegree N k₂ ≤ D * ((2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) := by
        have h := bfm_inv_tildeScale_le (d := P.natDegree) (N := N) (k := k₂) hN
        rw [hD]
        rw [show (2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree
            = (2 : ℝ) ^ P.natDegree
              * ((2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) by ring] at h
        exact h
      have h := mass_sq_dilated (m := bfmBump P.natDegree) (C := CB2) (c :=
        bfmTildeScale P.natDegree N k₂)
        (a := (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) (A := D)
        hB2pos.le hc ha0 ha1 hD1 hx hB2 u
      refine h.trans ?_
      have hc4 : 4 * (1 + D) * CB2 * D ^ 2 ≤
          1000 * (1 + D) ^ 3 * K := by
        have hmid := absorb_mid (K := K) (D := D) (C := CB2) (j := D ^ 2) hK0 hD1 (by positivity) hKB2 (by nlinarith [hD1]) (by nlinarith [hD1])
        simpa [bigConst, mul_comm, mul_left_comm, mul_assoc] using hmid
      have := mul_le_mul_of_nonneg_right hc4 (pow_nonneg ha0 2)
      simpa using this

end

end Work.KMTAreas.A7
