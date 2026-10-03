/-
# The `θ`-weighted Fourier mass of the KMT bumps (`bumpFourierMassDeriv`)

This module proves `Work.KMTPlan.A6.bumpFourierMassDeriv`, the *derivative* companion of
`Work.KMTPlan.A6.bumpFourierMass`: the `ℓ¹(ℤ)`-mass of the `θ`-weighted Fourier transform of the
Ionescu--Wainger bumps `varphiN N k₁`, `varphitildeN d N k₂` along a lattice translate of the
real line,

  `∑_p ‖∫ θ, θ · φ_{N,k₁}(θ) · e((u-p)θ)‖  ≲ (1 + 2^{k₁}/N)²`

(resp. `(1 + 2^{d k₂}/N^d)²`).  The extra `θ` factor is a derivative in the physical variable, so
each bound carries the *square* of the mass factor of `bumpFourierMass`.

## The mechanism

Writing `ψ_m (θ) = θ · m θ` for the relevant bump `m`, the integral is the inverse Fourier
transform of `θ ↦ θ · m (c θ)` at the lattice point `u - p` (`bfm_integral_eq_fourierInv`), and
the dilation identity

  `𝓕⁻ (θ ↦ θ · m (c θ)) x = c⁻² · 𝓕⁻ (ψ_m) (x / c)`

(`bfm_fourierInv_theta_comp_mul`, from `fourierInv_comp_mul` and the linearity of `𝓕⁻`) turns the
mass sum into the lattice sum of `‖𝓕⁻ ψ_m ((u-p)/c)‖`.  Since `ψ_m = θ ↦ θ m θ` is again `C²` with
compact support, `bfm_fourierInv_decay` gives quadratic decay with a constant *independent of `c`*,
and `bfm_tsum_mass` (`latticeQuadMass`) bounds the lattice sum by `C/c · 4(1 + 1/c)`.  The
arithmetic `1/c ≲ 2^{k}/N` then produces the square `(1 + 2^{k}/N)²` of the mass factor.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.bumpFourierMass

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger
open Work.KMTContract

/-! ## Linearity and dilation of `𝓕⁻` -/

/-- The inverse Fourier transform commutes with multiplication by a constant. -/
theorem bfm_fourierInv_smul (r : ℂ) (f : ℝ → ℂ) :
    FourierTransformInv.fourierInv (r • f) = r • FourierTransformInv.fourierInv f :=
  VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (-innerₗ ℝ) f r

/-- **Dilation with the `θ` factor.**  For `c > 0`, the inverse Fourier transform of
`θ ↦ θ · m (c θ)` is `c⁻²` times the inverse Fourier transform of `θ ↦ θ · m θ` at `x / c`. -/
theorem bfm_fourierInv_theta_comp_mul (m : ℝ → ℂ) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) * m (c * θ)) x
      = (c : ℂ)⁻¹ * ((c : ℂ)⁻¹
          * FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) * m θ) (x / c)) := by
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hfun : (fun θ : ℝ => (θ : ℂ) * m (c * θ))
      = (c : ℂ)⁻¹ • (fun θ : ℝ => (((c * θ : ℝ)) : ℂ) * m (c * θ)) := by
    funext θ
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (((c * θ : ℝ)) : ℂ) = (c : ℂ) * (θ : ℂ) by push_cast; ring]
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  rw [hfun, bfm_fourierInv_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show FourierTransformInv.fourierInv
        (fun θ : ℝ => (((c * θ : ℝ)) : ℂ) * m (c * θ)) x
      = (c : ℂ)⁻¹ * FourierTransformInv.fourierInv
          (fun θ : ℝ => (θ : ℂ) * m θ) (x / c) from
    congrFun (Work.KMTAreas.A7.fourierInv_comp_mul (fun θ : ℝ => (θ : ℂ) * m θ) hc) x]

/-! ## The multiplier by `θ` of a bump -/

/-- `θ ↦ θ · m θ` is `C²` when `m` is. -/
theorem bfm_contDiff_mul_id (m : ℝ → ℂ) (hm : ContDiff ℝ 2 m) :
    ContDiff ℝ 2 (fun θ : ℝ => (θ : ℂ) * m θ) :=
  (Complex.ofRealCLM.contDiff (n := 2)).mul hm

/-- `θ ↦ θ · m θ` has compact support when `m` does. -/
theorem bfm_hasCompactSupport_mul_id (m : ℝ → ℂ) (hm : HasCompactSupport m) :
    HasCompactSupport (fun θ : ℝ => (θ : ℂ) * m θ) :=
  HasCompactSupport.mul_left (f := fun θ : ℝ => (θ : ℂ)) hm

/-- Quadratic decay of `𝓕⁻ (θ ↦ θ · m θ)` for a `C²` compactly supported `m`, with an explicit
constant (via `bfm_fourierInv_decay`). -/
theorem bfm_decay_deriv (m : ℝ → ℂ) (hcd : ContDiff ℝ 2 m) (hcs : HasCompactSupport m) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
      ‖FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) * m θ) y‖
        ≤ C / (1 + |y|) ^ 2 :=
  bfm_fourierInv_decay (fun θ : ℝ => (θ : ℂ) * m θ)
    (bfm_contDiff_mul_id m hcd) (bfm_hasCompactSupport_mul_id m hcs)

theorem bfm_decay_kmtEta_deriv : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
    ‖FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) * kmtEta θ) y‖
      ≤ C / (1 + |y|) ^ 2 :=
  bfm_decay_deriv kmtEta (bfm_contDiff_kmtEta 2) bfm_hasCompactSupport_kmtEta

theorem bfm_decay_bfmBump_deriv (d : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
    ‖FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) * bfmBump d θ) y‖
      ≤ C / (1 + |y|) ^ 2 :=
  bfm_decay_deriv (bfmBump d) (contDiff_bfmBump d) (hasCompactSupport_bfmBump d)

theorem bfm_decay_lacψ_deriv : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
    ‖FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) * Work.KMTAreas.A7.lacψ θ) y‖
      ≤ C / (1 + |y|) ^ 2 := by
  obtain ⟨C, hC, h⟩ := bfm_decay_bfmBump_deriv 1
  exact ⟨C, hC, fun y => by rw [← bfmBump_one]; exact h y⟩

/-! ## The lattice sum of the `θ`-weighted mass -/

/-- **The lattice mass of a decaying `𝓕⁻ ψ`, with the two `c⁻¹` factors.**  If
`‖g y‖ ≤ C (1+|y|)^{-2}` then `∑_n ‖c⁻¹ (c⁻¹ g ((u-n)/c))‖ ≤ (C/c) · 4 (1 + 1/c)`. -/
theorem bfm_tsum_mass_deriv {g : ℝ → ℂ} {C c : ℝ} (hc : 0 < c)
    (hdec : ∀ y : ℝ, ‖g y‖ ≤ C / (1 + |y|) ^ 2) (u : ℝ) :
    (∑' n : ℤ, ‖(c : ℂ)⁻¹ * ((c : ℂ)⁻¹ * g ((u - (n : ℝ)) / c))‖)
      ≤ (C / c) * (4 * (1 + 1 / c)) := by
  have hdec' : ∀ y : ℝ, ‖(c : ℂ)⁻¹ * g y‖ ≤ (C / c) / (1 + |y|) ^ 2 := by
    intro y
    have hcinv : ‖(c : ℂ)⁻¹‖ = c⁻¹ := by
      rw [norm_inv, show ‖(c : ℂ)‖ = |c| from RCLike.norm_ofReal c, abs_of_pos hc]
    rw [norm_mul, hcinv]
    have h1 : c⁻¹ * ‖g y‖ ≤ c⁻¹ * (C / (1 + |y|) ^ 2) :=
      mul_le_mul_of_nonneg_left (hdec y) (by positivity)
    refine h1.trans (le_of_eq ?_)
    have hcne : c ≠ 0 := hc.ne'
    have hd : (1 + |y|) ^ 2 ≠ 0 := by positivity
    simp only [div_eq_mul_inv]
    ring
  exact bfm_tsum_mass (g := fun y : ℝ => (c : ℂ)⁻¹ * g y) (C := C / c) hc hdec' u

/-- **The mass of the `θ`-weighted dilation.**  If `𝓕⁻ (θ ↦ θ · m θ)` decays quadratically with
constant `C`, then the `ℓ¹`-mass of the `θ`-weighted Fourier transform of `θ ↦ m (c θ)` is at most
`(C/c) · 4 (1 + 1/c)`. -/
theorem bfm_mass_dilated_deriv {m : ℝ → ℂ} {C c : ℝ} (hc : 0 < c)
    (hdec : ∀ y : ℝ, ‖FourierTransformInv.fourierInv (fun θ : ℝ => (θ : ℂ) * m θ) y‖
      ≤ C / (1 + |y|) ^ 2) (u : ℝ) :
    (∑' p : ℤ, ‖∫ θ : ℝ, (θ : ℂ) * m (c * θ) * Work.KMTAreas.A7.ee ((u - (p : ℝ)) * θ)‖)
      ≤ (C / c) * (4 * (1 + 1 / c)) := by
  have h1 : ∀ p : ℤ,
      (∫ θ : ℝ, (θ : ℂ) * m (c * θ) * Work.KMTAreas.A7.ee ((u - (p : ℝ)) * θ))
        = (c : ℂ)⁻¹ * ((c : ℂ)⁻¹ * FourierTransformInv.fourierInv
            (fun θ : ℝ => (θ : ℂ) * m θ) ((u - (p : ℝ)) / c)) := by
    intro p
    exact (bfm_integral_eq_fourierInv (fun θ : ℝ => (θ : ℂ) * m (c * θ)) (u - (p : ℝ))).trans
      (bfm_fourierInv_theta_comp_mul m hc (u - (p : ℝ)))
  calc (∑' p : ℤ, ‖∫ θ : ℝ, (θ : ℂ) * m (c * θ)
          * Work.KMTAreas.A7.ee ((u - (p : ℝ)) * θ)‖)
      = ∑' p : ℤ, ‖(c : ℂ)⁻¹ * ((c : ℂ)⁻¹ * FourierTransformInv.fourierInv
            (fun θ : ℝ => (θ : ℂ) * m θ) ((u - (p : ℝ)) / c))‖ :=
        tsum_congr (fun p => congrArg norm (h1 p))
    _ ≤ (C / c) * (4 * (1 + 1 / c)) := bfm_tsum_mass_deriv hc hdec u

/-! ## The arithmetic of the square -/

/-- If `1/c ≤ A t` with `c > 0`, `A ≥ 1`, `t ≥ 0` and `C ≥ 0`, then
`(C/c) · 4 (1 + 1/c) ≤ 4 C A² (1+t)²`: the `x ↦ x (1+x)` factor turns into the square `(1+t)²`. -/
theorem bfm_deriv_single_scale {C c t A : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hA : 1 ≤ A)
    (ht : 0 ≤ t) (hx : 1 / c ≤ A * t) :
    (C / c) * (4 * (1 + 1 / c)) ≤ 4 * C * A ^ 2 * (1 + t) ^ 2 := by
  have hcne : c ≠ 0 := hc.ne'
  have hx0 : (0 : ℝ) ≤ 1 / c := by positivity
  have hkey : (1 / c) * (1 + 1 / c) ≤ A ^ 2 * (1 + t) ^ 2 := by
    nlinarith [hx, ht, hA, hx0]
  have hstep : (C / c) * (4 * (1 + 1 / c)) = 4 * C * ((1 / c) * (1 + 1 / c)) := by
    simp only [div_eq_mul_inv, one_mul]
    ring
  rw [hstep]
  calc 4 * C * ((1 / c) * (1 + 1 / c)) ≤ 4 * C * (A ^ 2 * (1 + t) ^ 2) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 4 * C * A ^ 2 * (1 + t) ^ 2 := by ring

/-! ## The main theorem -/

theorem bumpFourierMassDeriv (P : Polynomial ℤ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (N k₁ : ℕ), 1 ≤ N → ∀ u : ℝ,
        (∑' p : ℤ, ‖∫ θ : ℝ, (θ : ℂ) * Work.KMTAreas.A7.varphiN N k₁ θ
            * Work.KMTAreas.A7.ee ((u - (p : ℝ)) * θ)‖)
          ≤ C * (1 + (2 : ℝ) ^ k₁ / (N : ℝ)) ^ 2) ∧
      (∀ (N k₂ : ℕ), 1 ≤ N → ∀ u : ℝ,
        (∑' p : ℤ, ‖∫ θ : ℝ, (θ : ℂ) * Work.KMTAreas.A7.varphitildeN (P.natDegree) N k₂ θ
            * Work.KMTAreas.A7.ee ((u - (p : ℝ)) * θ)‖)
          ≤ C * (1 + (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ (P.natDegree)) ^ 2) := by
  obtain ⟨Cη, hCηpos, hCη⟩ := bfm_decay_kmtEta_deriv
  obtain ⟨Cψ, hCψpos, hCψ⟩ := bfm_decay_lacψ_deriv
  obtain ⟨Cd, hCdpos, hCd⟩ := bfm_decay_bfmBump_deriv P.natDegree
  have hCη0 : (0 : ℝ) ≤ Cη := hCηpos.le
  have hCψ0 : (0 : ℝ) ≤ Cψ := hCψpos.le
  have hCd0 : (0 : ℝ) ≤ Cd := hCdpos.le
  set A : ℝ := max 2 ((2 : ℝ) ^ P.natDegree) with hAdef
  have hA1 : (1 : ℝ) ≤ A := le_trans (by norm_num) (le_max_left _ _)
  have hA2 : (2 : ℝ) ≤ A := le_max_left _ _
  have hAd : (2 : ℝ) ^ P.natDegree ≤ A := le_max_right _ _
  set Cb : ℝ := 4 * (Cη + Cψ + Cd) * A ^ 2 + 1 with hCbdef
  have hCbpos : (0 : ℝ) < Cb := by rw [hCbdef]; positivity
  have hCA_eta : 4 * Cη * A ^ 2 ≤ Cb := by
    rw [hCbdef]; nlinarith [hCη0, hCψ0, hCd0, sq_nonneg A]
  have hCA_psi : 4 * Cψ * A ^ 2 ≤ Cb := by
    rw [hCbdef]; nlinarith [hCη0, hCψ0, hCd0, sq_nonneg A]
  have hCA_d : 4 * Cd * A ^ 2 ≤ Cb := by
    rw [hCbdef]; nlinarith [hCη0, hCψ0, hCd0, sq_nonneg A]
  refine ⟨Cb, hCbpos, ?_, ?_⟩
  · intro N k₁ hN u
    rcases Nat.eq_zero_or_pos k₁ with hk | hk
    · subst hk
      rw [bfm_varphiN_zero N, pow_zero]
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) :=
        Real.rpow_pos_of_pos (by norm_num) _
      refine le_trans (bfm_mass_dilated_deriv (m := kmtEta) (C := Cη) hpos hCη u) ?_
      have hx : 1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) ≤ A * (1 / (N : ℝ)) := by
        have h := bfm_inv_pow_logN_le (N := N) hN
        have h2 : (2 : ℝ) / (N : ℝ) = 2 * (1 / (N : ℝ)) := by ring
        have ht0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
        calc 1 / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) ≤ 2 / (N : ℝ) := h
          _ = 2 * (1 / (N : ℝ)) := h2
          _ ≤ A * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_right hA2 ht0
      have hscale := bfm_deriv_single_scale (C := Cη)
        (c := (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) (t := 1 / (N : ℝ)) (A := A)
        hCη0 hpos hA1 (by positivity) hx
      exact le_trans hscale (mul_le_mul_of_nonneg_right hCA_eta (by positivity))
    · rw [bfm_varphiN_pos N k₁ (by omega)]
      have hpos : (0 : ℝ) < Work.KMTAreas.A7.lacσ N k₁ := Work.KMTAreas.A7.lacσ_pos N k₁
      refine le_trans (bfm_mass_dilated_deriv (m := Work.KMTAreas.A7.lacψ) (C := Cψ)
        hpos hCψ u) ?_
      have hx : 1 / Work.KMTAreas.A7.lacσ N k₁ ≤ A * ((2 : ℝ) ^ k₁ / (N : ℝ)) := by
        have h := bfm_inv_lacσ_le (N := N) (k := k₁) hN
        have h2 : 2 * (2 : ℝ) ^ k₁ / (N : ℝ) = 2 * ((2 : ℝ) ^ k₁ / (N : ℝ)) := by ring
        have ht0 : (0 : ℝ) ≤ (2 : ℝ) ^ k₁ / (N : ℝ) := by positivity
        calc 1 / Work.KMTAreas.A7.lacσ N k₁ ≤ 2 * (2 : ℝ) ^ k₁ / (N : ℝ) := h
          _ = 2 * ((2 : ℝ) ^ k₁ / (N : ℝ)) := h2
          _ ≤ A * ((2 : ℝ) ^ k₁ / (N : ℝ)) := mul_le_mul_of_nonneg_right hA2 ht0
      have hscale := bfm_deriv_single_scale (C := Cψ)
        (c := Work.KMTAreas.A7.lacσ N k₁) (t := (2 : ℝ) ^ k₁ / (N : ℝ)) (A := A)
        hCψ0 hpos hA1 (by positivity) hx
      exact le_trans hscale (mul_le_mul_of_nonneg_right hCA_psi (by positivity))
  · intro N k₂ hN u
    rcases Nat.eq_zero_or_pos k₂ with hk | hk
    · subst hk
      rw [bfm_varphitildeN_zero P.natDegree N, mul_zero, pow_zero]
      have hpos : (0 : ℝ) < (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      refine le_trans (bfm_mass_dilated_deriv (m := kmtEta) (C := Cη) hpos hCη u) ?_
      have hx : 1 / (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))
          ≤ A * (1 / (N : ℝ) ^ P.natDegree) := by
        have h := bfm_inv_etaScale_le (d := P.natDegree) (N := N) hN
        have h2 : (2 : ℝ) ^ P.natDegree / (N : ℝ) ^ P.natDegree
            = (2 : ℝ) ^ P.natDegree * (1 / (N : ℝ) ^ P.natDegree) := by ring
        have ht0 : (0 : ℝ) ≤ 1 / (N : ℝ) ^ P.natDegree := by positivity
        calc 1 / (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))
            ≤ (2 : ℝ) ^ P.natDegree / (N : ℝ) ^ P.natDegree := h
          _ = (2 : ℝ) ^ P.natDegree * (1 / (N : ℝ) ^ P.natDegree) := h2
          _ ≤ A * (1 / (N : ℝ) ^ P.natDegree) := mul_le_mul_of_nonneg_right hAd ht0
      have hscale := bfm_deriv_single_scale (C := Cη)
        (c := (2 : ℝ) ^ ((P.natDegree : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)))
        (t := 1 / (N : ℝ) ^ P.natDegree) (A := A)
        hCη0 hpos hA1 (by positivity) hx
      exact le_trans hscale (mul_le_mul_of_nonneg_right hCA_eta (by positivity))
    · rw [bfm_varphitildeN_pos P.natDegree N k₂ (by omega)]
      have hpos : (0 : ℝ) < bfmTildeScale P.natDegree N k₂ := by
        rw [bfmTildeScale]; exact Real.rpow_pos_of_pos (by norm_num) _
      refine le_trans (bfm_mass_dilated_deriv (m := bfmBump P.natDegree) (C := Cd)
        hpos hCd u) ?_
      have hx : 1 / bfmTildeScale P.natDegree N k₂
          ≤ A * ((2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) := by
        have h := bfm_inv_tildeScale_le (d := P.natDegree) (N := N) (k := k₂) hN
        have h2 : (2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree
            = (2 : ℝ) ^ P.natDegree
              * ((2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) := by ring
        have ht0 : (0 : ℝ) ≤ (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree := by positivity
        calc 1 / bfmTildeScale P.natDegree N k₂
            ≤ (2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree := h
          _ = (2 : ℝ) ^ P.natDegree
                * ((2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) := h2
          _ ≤ A * ((2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) :=
              mul_le_mul_of_nonneg_right hAd ht0
      have hscale := bfm_deriv_single_scale (C := Cd)
        (c := bfmTildeScale P.natDegree N k₂)
        (t := (2 : ℝ) ^ (P.natDegree * k₂) / (N : ℝ) ^ P.natDegree) (A := A)
        hCd0 hpos hA1 (by positivity) hx
      exact le_trans hscale (mul_le_mul_of_nonneg_right hCA_d (by positivity))

end

end Work.KMTPlan.A6
