import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.WinAuxDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.WinAuxAssembly` — the image-sum estimate of the W-route

The W-route (`LEAD_DESIGN_formrowkin.md` §3) reduces the aliasing defect of the windowed mean-free
state to the *position-space image sum*

`Σ'_{m ≠ 0} Re ∫ conj(g x)·symOp σ g (x + ℓ•m)`,   `g = winState ℓ ψ`,

which is paid by the reserve `‖D⁶σ‖₁·ℓ⁻³·gapBare ℓ 0 ψ`.  The mechanism is:

* `g = χ_Λ·Q_Λψ` vanishes outside the *open* ball of radius `ℓ/2`, so for `m ≠ 0` the shifted
  argument `x + ℓ•m` lies strictly outside `tsupport g` — the decay hypothesis W2 applies;
* on the support, `χ_Λ(x) ≤ C (winD ℓ x/ℓ)³` (W0) and
  `‖x + ℓ•m − y‖ ≥ ℓ(‖m‖−1) + winD ℓ x + winD ℓ y`, giving the summable majorant
  `(1 + ‖m‖)⁻⁶`;
* the resulting double integral factorises and is closed by Cauchy–Schwarz against
  `gapBare ℓ 0 ψ = ∫_Λ (Q_Λψ)²`.

This module proves the assembly with the three analytic ingredients (the pointwise geometric
bound, the integrability of `winW`, and the Cauchy–Schwarz estimate) taken as *hypotheses*, so
that it is independent of their proofs.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The ℓ-uniform flatness bound of the window

`chiLam_le_cubic_flat` gives the flatness constant only at a fixed `ℓ`; the underlying
`Work.BoseFixB1.chi_boundary_taylor` produces a constant that is independent of `ℓ`. -/

lemma chiLam_le_flatC {C : ℝ}
    (hC : ∀ z : E3, ‖z‖ ≤ 1 / 2 → Submission.BoseGases.chi z ≤ C * (1 / 2 - ‖z‖) ^ 3)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (x : E3) :
    Work.BoseK15.corpusBox.chiLam ℓ x ≤ C * (winD ℓ x / ℓ) ^ 3 := by
  have hchi : Work.BoseK15.corpusBox.chiLam ℓ x = Submission.BoseGases.chi ((ℓ⁻¹) • x) := rfl
  have hnorm : ‖(ℓ⁻¹) • x‖ = ‖x‖ / ℓ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le), inv_mul_eq_div]
  rw [hchi]
  by_cases hz : ‖(ℓ⁻¹) • x‖ ≤ 1 / 2
  · have hxle : ‖x‖ ≤ ℓ / 2 := by
      have h := hz
      rw [hnorm] at h
      rw [div_le_iff₀ hℓ] at h
      linarith
    have hmax : winD ℓ x = ℓ / 2 - ‖x‖ := by
      rw [winD]; exact max_eq_right (by linarith)
    have harg : (1 / 2 - ‖(ℓ⁻¹) • x‖) = winD ℓ x / ℓ := by
      rw [hnorm, hmax]; field_simp
    rw [← harg]
    exact hC ((ℓ⁻¹) • x) hz
  · have hz' : 1 / 2 < ‖(ℓ⁻¹) • x‖ := lt_of_not_ge hz
    rw [Submission.BoseGases.chi_eq_zero_of_norm_gt _ hz']
    have hxle : ℓ / 2 ≤ ‖x‖ := by
      have h := hz'
      rw [hnorm] at h
      rw [lt_div_iff₀ hℓ] at h
      linarith
    have hmax : winD ℓ x = 0 := by
      rw [winD]; exact max_eq_left (by linarith)
    rw [hmax, zero_div, zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero]

/-! ## 2. The pointwise bound of the image integrand -/

/-- **The pointwise image bound.**  On `supp g` the window is bounded by the cubic flatness, and
the separation `‖x + ℓ•m − y‖ ≥ ℓ(‖m‖−1) + winD ℓ x + winD ℓ y` turns the `|·|⁻⁶` decay into the
summable weight `(1 + ‖m‖)⁻⁶`. -/
lemma winAux_pointwise {ℓ C₀ : ℝ} (hℓ : 0 < ℓ) (hC₀0 : 0 ≤ C₀)
    (hflat : ∀ x : E3, Work.BoseK15.corpusBox.chiLam ℓ x ≤ C₀ * (winD ℓ x / ℓ) ^ 3)
    (hgeom : ∀ (x y : E3) (m : Fin 3 → ℤ), m ≠ 0 →
      (winD ℓ x / ℓ) ^ 3 * (winD ℓ y / ℓ) ^ 3 / ‖x + ℓ • latVec m - y‖ ^ 6
        ≤ (ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6 * ((1 + ‖latVec m‖) ^ 6)⁻¹)
    (ψ : E3 → ℝ) {m : Fin 3 → ℤ} (hm : m ≠ 0) (x y : E3) :
    ‖winState ℓ ψ x‖ * (‖winState ℓ ψ y‖ / ‖x + ℓ • latVec m - y‖ ^ 6)
      ≤ (C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
          * ((1 + ‖latVec m‖) ^ 6)⁻¹)) * winW ℓ ψ x * winW ℓ ψ y := by
  have hgx := winState_norm_le_of hℓ hC₀0 hflat ψ x
  have hgy := winState_norm_le_of hℓ hC₀0 hflat ψ y
  have hWx : 0 ≤ winW ℓ ψ x := winW_nonneg ℓ ψ x
  have hWy : 0 ≤ winW ℓ ψ y := winW_nonneg ℓ ψ y
  have hD6 : 0 ≤ ‖x + ℓ • latVec m - y‖ ^ 6 := by positivity
  have hpx : 0 ≤ (winD ℓ x / ℓ) ^ 3 := by
    have : 0 ≤ winD ℓ x / ℓ := div_nonneg (winD_nonneg ℓ x) hℓ.le
    positivity
  have hpy : 0 ≤ (winD ℓ y / ℓ) ^ 3 := by
    have : 0 ≤ winD ℓ y / ℓ := div_nonneg (winD_nonneg ℓ y) hℓ.le
    positivity
  have hAx : 0 ≤ C₀ * (winD ℓ x / ℓ) ^ 3 * winW ℓ ψ x :=
    mul_nonneg (mul_nonneg hC₀0 hpx) hWx
  have hBy : 0 ≤ C₀ * (winD ℓ y / ℓ) ^ 3 * winW ℓ ψ y :=
    mul_nonneg (mul_nonneg hC₀0 hpy) hWy
  -- two one-sided divisions
  have h1 : ‖winState ℓ ψ y‖ / ‖x + ℓ • latVec m - y‖ ^ 6
      ≤ (C₀ * (winD ℓ y / ℓ) ^ 3 * winW ℓ ψ y) / ‖x + ℓ • latVec m - y‖ ^ 6 :=
    div_le_div_of_nonneg_right hgy hD6
  have h2 : ‖winState ℓ ψ x‖ * (‖winState ℓ ψ y‖ / ‖x + ℓ • latVec m - y‖ ^ 6)
      ≤ ‖winState ℓ ψ x‖ *
        ((C₀ * (winD ℓ y / ℓ) ^ 3 * winW ℓ ψ y) / ‖x + ℓ • latVec m - y‖ ^ 6) :=
    mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have h3 : ‖winState ℓ ψ x‖ *
        ((C₀ * (winD ℓ y / ℓ) ^ 3 * winW ℓ ψ y) / ‖x + ℓ • latVec m - y‖ ^ 6)
      ≤ (C₀ * (winD ℓ x / ℓ) ^ 3 * winW ℓ ψ x) *
        ((C₀ * (winD ℓ y / ℓ) ^ 3 * winW ℓ ψ y) / ‖x + ℓ • latVec m - y‖ ^ 6) :=
    mul_le_mul_of_nonneg_right hgx (div_nonneg hBy hD6)
  refine le_trans h2 (le_trans h3 ?_)
  have hfac : (C₀ * (winD ℓ x / ℓ) ^ 3 * winW ℓ ψ x) *
        ((C₀ * (winD ℓ y / ℓ) ^ 3 * winW ℓ ψ y) / ‖x + ℓ • latVec m - y‖ ^ 6)
      = (C₀ * C₀ * ((winD ℓ x / ℓ) ^ 3 * (winD ℓ y / ℓ) ^ 3
            / ‖x + ℓ • latVec m - y‖ ^ 6)) * winW ℓ ψ x * winW ℓ ψ y := by
    ring
  rw [hfac]
  have hgeom' := hgeom x y m hm
  have hC2 : 0 ≤ C₀ * C₀ := mul_nonneg hC₀0 hC₀0
  have hWxy : 0 ≤ winW ℓ ψ x * winW ℓ ψ y := mul_nonneg hWx hWy
  have h1' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgeom' hC2) hWxy
  have h1'' : (C₀ * C₀ * ((winD ℓ x / ℓ) ^ 3 * (winD ℓ y / ℓ) ^ 3
          / ‖x + ℓ • latVec m - y‖ ^ 6)) * (winW ℓ ψ x * winW ℓ ψ y)
      ≤ (C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6 * ((1 + ‖latVec m‖) ^ 6)⁻¹))
          * (winW ℓ ψ x * winW ℓ ψ y) := h1'
  calc (C₀ * C₀ * ((winD ℓ x / ℓ) ^ 3 * (winD ℓ y / ℓ) ^ 3
          / ‖x + ℓ • latVec m - y‖ ^ 6)) * winW ℓ ψ x * winW ℓ ψ y
      = (C₀ * C₀ * ((winD ℓ x / ℓ) ^ 3 * (winD ℓ y / ℓ) ^ 3
          / ‖x + ℓ • latVec m - y‖ ^ 6)) * (winW ℓ ψ x * winW ℓ ψ y) := by ring
    _ ≤ (C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6 * ((1 + ‖latVec m‖) ^ 6)⁻¹))
          * (winW ℓ ψ x * winW ℓ ψ y) := h1''
    _ = (C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
          * ((1 + ‖latVec m‖) ^ 6)⁻¹)) * winW ℓ ψ x * winW ℓ ψ y := by ring



/-! ## 3. The assembly -/

/-- **The image-sum leaf `W3` from the three analytic inputs.**  The hypotheses are exactly the
pointwise geometric bound (`winAux_geom`), the integrability of the weight (`winAux_winW_integrable`)
and the Cauchy–Schwarz estimate (`winAux_winW_cs`); the conclusion is the statement requested by
`Work.BoseBoxFock.winState_image_sum_le`. -/
theorem winAuxAssembly
    (hW2 : ∀ {σ : E3 → ℝ} {g : E3 → ℂ}
      (hσ : ContDiff ℝ (⊤ : ENat) σ)
      (hσ6 : MeasureTheory.Integrable (fun p : E3 => ‖iteratedFDeriv ℝ 6 σ p‖))
      (hσg : ∃ A : ℝ, ∀ p : E3, |σ p| ≤ A * (1 + ‖p‖) ^ 2)
      (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) {x : E3}
      (hx : x ∉ tsupport g),
      ‖symOp σ g x‖ ≤ 27 * ((2 * Real.pi) ^ 3)⁻¹ * iterDerivL1 6 σ *
        ∫ y : E3, ‖g y‖ / ‖x - y‖ ^ 6)
    (hgeom : ∀ {ℓ : ℝ}, 0 < ℓ → ∀ (x y : E3) (m : Fin 3 → ℤ), m ≠ 0 →
      (winD ℓ x / ℓ) ^ 3 * (winD ℓ y / ℓ) ^ 3 / ‖x + ℓ • latVec m - y‖ ^ 6
        ≤ (ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6 * ((1 + ‖latVec m‖) ^ 6)⁻¹)
    (hwinWint : ∀ {ℓ : ℝ}, 0 < ℓ → ∀ {ψ : E3 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) ψ →
      MeasureTheory.Integrable (winW ℓ ψ))
    (hcs : ∀ {ℓ : ℝ}, 0 < ℓ → ∀ {ψ : E3 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∫ z : E3, winW ℓ ψ z) ^ 2 ≤ ℓ ^ 3 * Work.BoseKinLoc.gapBare ℓ 0 ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ : ℝ}, 0 < ℓ → ∀ (σ : E3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) σ →
      (∃ A : ℝ, ∀ p, |σ p| ≤ A * (1 + ‖p‖) ^ 2) →
      MeasureTheory.Integrable (fun p : E3 => ‖iteratedFDeriv ℝ 6 σ p‖) →
      ∀ (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      ‖∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
          (∫ x : E3,
            (starRingEnd ℂ) (winState ℓ ψ x) *
              symOp σ (winState ℓ ψ)
                (x + ℓ • latVec m)).re)‖
        ≤ C * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (ℓ ^ 3)⁻¹ *
            Work.BoseKinLoc.gapBare ℓ 0 ψ := by
  obtain ⟨C₀, hC₀pos, hC₀tay⟩ := Work.BoseFixB1.chi_boundary_taylor 3
  have hC₀0 : 0 ≤ C₀ := le_of_lt hC₀pos
  have hflat : ∀ (ℓ : ℝ), 0 < ℓ → ∀ x : E3,
      Work.BoseK15.corpusBox.chiLam ℓ x ≤ C₀ * (winD ℓ x / ℓ) ^ 3 :=
    fun ℓ hℓ x => chiLam_le_flatC (fun z hz => hC₀tay z hz) hℓ x
  have hSsum : Summable (fun m : Fin 3 → ℤ => ((1 + ‖latVec m‖) ^ 6)⁻¹) :=
    summable_one_add_norm_latVec_pow_inv (by norm_num : 4 ≤ 6)
  set Ssum : ℝ := ∑' m : Fin 3 → ℤ, ((1 + ‖latVec m‖) ^ 6)⁻¹ with hSsumdef
  have hSsum0 : 0 ≤ Ssum := by
    rw [hSsumdef]; exact tsum_nonneg (fun m => by positivity)
  refine ⟨27 * ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * C₀) * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6 * Ssum,
    ?_, ?_⟩
  · have h1 : 0 ≤ 27 * ((2 * Real.pi) ^ 3)⁻¹ := by
      have h : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
      exact mul_nonneg (by norm_num) h
    have h2 : 0 ≤ C₀ * C₀ := mul_nonneg hC₀0 hC₀0
    have h3 : 0 ≤ ((2 : ℝ) ^ 6)⁻¹ := by norm_num
    have h4 : 0 ≤ (3 : ℝ) ^ 6 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4) hSsum0
  · intro ℓ hℓ σ hσ hσg hσ6 ψ hψ
    have hD0 : 0 ≤ ∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖ :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall (fun p => norm_nonneg _))
    have hG0 : 0 ≤ Work.BoseKinLoc.gapBare ℓ 0 ψ := Work.BoseKinLoc.gapBare_nonneg ℓ 0 ψ
    have hWint : MeasureTheory.Integrable (winW ℓ ψ) := hwinWint hℓ hψ
    have hUG : (∫ z : E3, winW ℓ ψ z) * (∫ z : E3, winW ℓ ψ z)
        ≤ ℓ ^ 3 * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
      have h := hcs hℓ hψ
      rwa [sq] at h
    have hpow : (ℓ ^ 6)⁻¹ * ℓ ^ 3 = (ℓ ^ 3)⁻¹ := by
      have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
      have h3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 hℓne
      rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add, mul_inv]
      rw [mul_assoc, inv_mul_cancel₀ h3, mul_one]
    have hDne : (0 : ℝ) ≤ 27 * ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) := by
      have h : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
      exact mul_nonneg (mul_nonneg (by norm_num) h) hD0
    have hconst : (0 : ℝ) ≤ 27 * ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * C₀) * ((2 : ℝ) ^ 6)⁻¹
        * (3 : ℝ) ^ 6 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * ((ℓ ^ 6)⁻¹ * ℓ ^ 3)
        * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
      have h27 : 0 ≤ 27 * ((2 * Real.pi) ^ 3)⁻¹ := by
        have h : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
        exact mul_nonneg (by norm_num) h
      have hC2 : 0 ≤ C₀ * C₀ := mul_nonneg hC₀0 hC₀0
      have h26 : 0 ≤ ((2 : ℝ) ^ 6)⁻¹ := by norm_num
      have h36 : 0 ≤ (3 : ℝ) ^ 6 := by positivity
      have h5 : 0 ≤ (ℓ ^ 6)⁻¹ * ℓ ^ 3 := mul_nonneg (by positivity) (by positivity)
      have hX : 0 ≤ ((((27 * ((2 * Real.pi) ^ 3)⁻¹) * (C₀ * C₀)) * ((2 : ℝ) ^ 6)⁻¹)
            * (3 : ℝ) ^ 6) * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * ((ℓ ^ 6)⁻¹ * ℓ ^ 3) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h27 hC2) h26) h36) hD0) h5
      exact mul_nonneg hX hG0
    have hper : ∀ m : Fin 3 → ℤ,
        ‖(if m = 0 then (0 : ℝ) else
          (∫ x : E3,
            (starRingEnd ℂ) (winState ℓ ψ x) *
              symOp σ (winState ℓ ψ)
                (x + ℓ • latVec m)).re)‖
        ≤ (27 * ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * C₀) * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
            * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * ((ℓ ^ 6)⁻¹ * ℓ ^ 3)
            * Work.BoseKinLoc.gapBare ℓ 0 ψ) * ((1 + ‖latVec m‖) ^ 6)⁻¹ := by
      intro m
      by_cases hm : m = 0
      · subst hm
        rw [if_pos rfl, norm_zero]
        exact mul_nonneg hconst (by positivity)
      · rw [if_neg hm, Real.norm_eq_abs]
        -- (a) `|Re ∫| ≤ ∫ ‖g x‖·‖symOp …‖`
        have hlead : |(∫ x : E3, (starRingEnd ℂ) (winState ℓ ψ x) *
              symOp σ (winState ℓ ψ) (x + ℓ • latVec m)).re|
            ≤ ∫ x : E3, ‖winState ℓ ψ x‖ * ‖symOp σ (winState ℓ ψ) (x + ℓ • latVec m)‖ := by
          refine le_trans (Complex.abs_re_le_norm
            (∫ x : E3, (starRingEnd ℂ) (winState ℓ ψ x) *
              symOp σ (winState ℓ ψ) (x + ℓ • latVec m))) ?_
          have h1 := MeasureTheory.norm_integral_le_integral_norm (μ := (volume : Measure E3))
            (fun x : E3 => (starRingEnd ℂ) (winState ℓ ψ x) *
              symOp σ (winState ℓ ψ) (x + ℓ • latVec m))
          refine le_trans h1 (le_of_eq ?_)
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          simp only [norm_mul, Complex.norm_conj]
        -- (b) pointwise bound of the shifted symbol
        have hB : ∀ x : E3, ‖winState ℓ ψ x‖ * ‖symOp σ (winState ℓ ψ) (x + ℓ • latVec m)‖
            ≤ (27 * ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖))
              * (∫ y : E3, ‖winState ℓ ψ x‖ *
                  (‖winState ℓ ψ y‖ / ‖x + ℓ • latVec m - y‖ ^ 6)) := by
          intro x
          by_cases hx0 : winState ℓ ψ x = 0
          · rw [hx0, norm_zero, zero_mul]
            simp
          · have hxlt : ‖x‖ < ℓ / 2 := norm_lt_half_of_winState_ne_zero hℓ ψ hx0
            have hout : x + ℓ • latVec m ∉ tsupport (winState ℓ ψ) := by
              intro hmem
              have h1 := winState_tsupport_subset hℓ ψ hmem
              rw [Metric.mem_closedBall, dist_zero_right] at h1
              have hm1 : (1 : ℝ) ≤ ‖latVec m‖ := norm_latVec_ge_one hm
              have h2 : ℓ * ‖latVec m‖ ≤ ‖x + ℓ • latVec m‖ + ‖x‖ := by
                have h3 := norm_sub_le (x + ℓ • latVec m) x
                have h4 : (x + ℓ • latVec m) - x = ℓ • latVec m := by abel
                rw [h4, norm_smul, Real.norm_of_nonneg hℓ.le] at h3
                linarith
              nlinarith [h1, h2, hℓ, hm1, hxlt]
            have hW2x := hW2 (σ := σ) (g := winState ℓ ψ) hσ hσ6 hσg
              (winState_contDiff hℓ hψ) (winState_hasCompactSupport hℓ ψ) hout
            rw [show iterDerivL1 6 σ = ∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖ from rfl] at hW2x
            have hW2x' := mul_le_mul_of_nonneg_left hW2x (norm_nonneg (winState ℓ ψ x))
            refine le_trans hW2x' (le_of_eq ?_)
            rw [MeasureTheory.integral_const_mul]
            ring
        -- (c) the inner integral
        have hA : ∀ x : E3,
            (∫ y : E3, ‖winState ℓ ψ x‖ * (‖winState ℓ ψ y‖ / ‖x + ℓ • latVec m - y‖ ^ 6))
              ≤ (C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                    * ((1 + ‖latVec m‖) ^ 6)⁻¹)) * winW ℓ ψ x
                  * (∫ z : E3, winW ℓ ψ z) := by
          intro x
          have hmaj : MeasureTheory.Integrable (fun y : E3 =>
              (C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                    * ((1 + ‖latVec m‖) ^ 6)⁻¹)) * winW ℓ ψ x * winW ℓ ψ y) :=
            hWint.const_mul _
          have hmono := MeasureTheory.integral_mono_of_nonneg
            (μ := (volume : Measure E3))
            (f := fun y : E3 => ‖winState ℓ ψ x‖ *
              (‖winState ℓ ψ y‖ / ‖x + ℓ • latVec m - y‖ ^ 6))
            (g := fun y : E3 => (C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                    * ((1 + ‖latVec m‖) ^ 6)⁻¹)) * winW ℓ ψ x * winW ℓ ψ y)
            (Filter.Eventually.of_forall (fun y =>
              mul_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) (by positivity))))
            hmaj
            (Filter.Eventually.of_forall (fun y =>
              winAux_pointwise hℓ hC₀0 (hflat ℓ hℓ) (hgeom hℓ) ψ hm x y))
          calc (∫ y : E3, ‖winState ℓ ψ x‖ *
                (‖winState ℓ ψ y‖ / ‖x + ℓ • latVec m - y‖ ^ 6))
              ≤ ∫ y : E3, (C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                    * ((1 + ‖latVec m‖) ^ 6)⁻¹)) * winW ℓ ψ x * winW ℓ ψ y := hmono
            _ = ((C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                    * ((1 + ‖latVec m‖) ^ 6)⁻¹)) * winW ℓ ψ x)
                  * (∫ z : E3, winW ℓ ψ z) := by
                rw [MeasureTheory.integral_const_mul]
            _ = (C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                    * ((1 + ‖latVec m‖) ^ 6)⁻¹)) * winW ℓ ψ x
                  * (∫ z : E3, winW ℓ ψ z) := by ring
        -- (d) the outer integral
        have hC : (∫ x : E3, ‖winState ℓ ψ x‖ *
              ‖symOp σ (winState ℓ ψ) (x + ℓ • latVec m)‖)
            ≤ ((27 * ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖))
                * ((C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                    * ((1 + ‖latVec m‖) ^ 6)⁻¹))
                  * (∫ z : E3, winW ℓ ψ z)))
              * (∫ z : E3, winW ℓ ψ z) := by
          have hpt : ∀ x : E3, ‖winState ℓ ψ x‖ * ‖symOp σ (winState ℓ ψ) (x + ℓ • latVec m)‖
              ≤ ((27 * ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖))
                * ((C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                    * ((1 + ‖latVec m‖) ^ 6)⁻¹))
                  * (∫ z : E3, winW ℓ ψ z))) * winW ℓ ψ x := by
            intro x
            refine le_trans (le_trans (hB x) (mul_le_mul_of_nonneg_left (hA x) hDne)) (le_of_eq ?_)
            ring
          have hmaj : MeasureTheory.Integrable (fun x : E3 =>
              ((27 * ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖))
                * ((C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                    * ((1 + ‖latVec m‖) ^ 6)⁻¹))
                  * (∫ z : E3, winW ℓ ψ z))) * winW ℓ ψ x) :=
            hWint.const_mul _
          have hmono := MeasureTheory.integral_mono_of_nonneg
            (μ := (volume : Measure E3))
            (f := fun x : E3 => ‖winState ℓ ψ x‖ *
              ‖symOp σ (winState ℓ ψ) (x + ℓ • latVec m)‖)
            (g := fun x : E3 =>
              ((27 * ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖))
                * ((C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                    * ((1 + ‖latVec m‖) ^ 6)⁻¹))
                  * (∫ z : E3, winW ℓ ψ z))) * winW ℓ ψ x)
            (Filter.Eventually.of_forall (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
            hmaj
            (Filter.Eventually.of_forall hpt)
          rw [MeasureTheory.integral_const_mul] at hmono
          exact hmono
        -- (e) close with Cauchy–Schwarz
        have hKm0 : 0 ≤ C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
            * ((1 + ‖latVec m‖) ^ 6)⁻¹) := by
          have h1 : 0 ≤ C₀ * C₀ := mul_nonneg hC₀0 hC₀0
          have h2 : 0 ≤ (ℓ ^ 6)⁻¹ := by positivity
          have h3 : 0 ≤ ((2 : ℝ) ^ 6)⁻¹ := by norm_num
          have h4 : 0 ≤ (3 : ℝ) ^ 6 := by positivity
          have h5 : 0 ≤ ((1 + ‖latVec m‖) ^ 6)⁻¹ := by positivity
          exact mul_nonneg h1 (mul_nonneg (mul_nonneg (mul_nonneg h2 h3) h4) h5)
        refine le_trans (le_trans hlead hC) ?_
        have h2 : (C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                  * ((1 + ‖latVec m‖) ^ 6)⁻¹))
              * ((∫ z : E3, winW ℓ ψ z) * (∫ z : E3, winW ℓ ψ z))
            ≤ (C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                  * ((1 + ‖latVec m‖) ^ 6)⁻¹))
              * (ℓ ^ 3 * Work.BoseKinLoc.gapBare ℓ 0 ψ) :=
          mul_le_mul_of_nonneg_left hUG hKm0
        have h3 : (27 * ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖))
              * ((C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                  * ((1 + ‖latVec m‖) ^ 6)⁻¹))
                * ((∫ z : E3, winW ℓ ψ z) * (∫ z : E3, winW ℓ ψ z)))
            ≤ (27 * ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖))
              * ((C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                  * ((1 + ‖latVec m‖) ^ 6)⁻¹))
                * (ℓ ^ 3 * Work.BoseKinLoc.gapBare ℓ 0 ψ)) :=
          mul_le_mul_of_nonneg_left h2 hDne
        have h4 : ((27 * ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖))
                * ((C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                    * ((1 + ‖latVec m‖) ^ 6)⁻¹))
                  * (∫ z : E3, winW ℓ ψ z)))
              * (∫ z : E3, winW ℓ ψ z)
            = (27 * ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖))
              * ((C₀ * C₀ * ((ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
                  * ((1 + ‖latVec m‖) ^ 6)⁻¹))
                * ((∫ z : E3, winW ℓ ψ z) * (∫ z : E3, winW ℓ ψ z))) := by ring
        refine le_trans (le_of_eq h4) (le_trans h3 (le_of_eq ?_))
        ring
    -- Step F: sum over the lattice
    have hsumm : Summable (fun m : Fin 3 → ℤ =>
        ‖(if m = 0 then (0 : ℝ) else
          (∫ x : E3,
            (starRingEnd ℂ) (winState ℓ ψ x) *
              symOp σ (winState ℓ ψ) (x + ℓ • latVec m)).re)‖) :=
      Summable.of_norm_bounded
        (hSsum.mul_left (27 * ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * C₀) * ((2 : ℝ) ^ 6)⁻¹
            * (3 : ℝ) ^ 6 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * ((ℓ ^ 6)⁻¹ * ℓ ^ 3)
            * Work.BoseKinLoc.gapBare ℓ 0 ψ))
        (fun m => by
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact hper m)
    have hfinal : (∑' m : Fin 3 → ℤ, (27 * ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * C₀)
            * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖)
            * ((ℓ ^ 6)⁻¹ * ℓ ^ 3) * Work.BoseKinLoc.gapBare ℓ 0 ψ)
            * ((1 + ‖latVec m‖) ^ 6)⁻¹)
        = (27 * ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * C₀) * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6 * Ssum)
            * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (ℓ ^ 3)⁻¹
            * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
      rw [tsum_mul_left, hSsumdef, hpow]
      ring
    calc ‖∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
            (∫ x : E3,
              (starRingEnd ℂ) (winState ℓ ψ x) *
                symOp σ (winState ℓ ψ)
                  (x + ℓ • latVec m)).re)‖
        ≤ ∑' m : Fin 3 → ℤ, ‖(if m = 0 then (0 : ℝ) else
            (∫ x : E3,
              (starRingEnd ℂ) (winState ℓ ψ x) *
                symOp σ (winState ℓ ψ)
                  (x + ℓ • latVec m)).re)‖ := norm_tsum_le_tsum_norm hsumm
      _ ≤ ∑' m : Fin 3 → ℤ, (27 * ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * C₀) * ((2 : ℝ) ^ 6)⁻¹
            * (3 : ℝ) ^ 6 * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * ((ℓ ^ 6)⁻¹ * ℓ ^ 3)
            * Work.BoseKinLoc.gapBare ℓ 0 ψ) * ((1 + ‖latVec m‖) ^ 6)⁻¹ :=
          Summable.tsum_le_tsum (fun m => hper m) hsumm
            (hSsum.mul_left _)
      _ = (27 * ((2 * Real.pi) ^ 3)⁻¹ * (C₀ * C₀) * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6 * Ssum)
            * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (ℓ ^ 3)⁻¹
            * Work.BoseKinLoc.gapBare ℓ 0 ψ := hfinal

end Work.BoseBoxFock
