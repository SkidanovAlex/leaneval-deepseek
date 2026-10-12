import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.C3Q.I2_integral_bound
import Submission.Work.BoseBogFS.W1_mass_bounds
import Submission.Work.BoseBogFS.chat_zero_eq_integral
import Submission.Work.BoseBogFS.existsAdmRegime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.ZPE1E2Row` — the `E₁`–`E₂` comparison of the mass step,
## **with the integral parenthesised** (self-contained, no `ZPLatticeAux` dependency)

The statement requested under the name `Work.BoseBogFS.ZPE1E2Compare` is

```
|((2π)³)⁻¹ * ℓ³ * ∫ p, Ŵ₁(p)²/(2‖p‖²) - ℓ³ * Ŵ₁ω(0)| ≤ C * ℓ² * (∫W₁)²
```

written with the `- ℓ³ * Ŵ₁ω(0)` on the line *after* the integral body.  In Lean the body of
`∫ p, …` extends to the next delimiter, so that text elaborates as

```
|(2π)⁻³ * ℓ³ * ∫ p, ( Ŵ₁(p)²/(2‖p‖²) - ℓ³ * Ŵ₁ω(0) )| ≤ C * ℓ² * (∫W₁)² ,
```

i.e. **with the subtraction inside the Bochner integral** (machine check:
`∫ x : ℝ, f x - 1` elaborates as `∫ x : ℝ, (f x - 1)`; equivalently, in
`|(2)⁻¹ * ∫ p : ℝ³, (0:ℝ) - p 0|` the bound variable `p` is in scope in the subtracted term).
That formalised statement is *vacuous*: the integrand differs from the nonnegative
`Ŵ₁(p)²/(2‖p‖²)` by the constant `ℓ³ * Ŵ₁ω(0) =: c`, which is strictly positive (it dominates
`∫g₀ω ≥ 4π(a v)²/R > 0`, `Work.KernelL2.g0w0Mass_ge_newton`), while `|Ŵ₁(p)| ≤ 16πa`
(`Work.BoseB7AK.W1rows.W1hat_abs_le`) makes the integrand non-integrable; the Bochner integral of
a non-integrable function is the junk value `0`, so the claim degenerates to
`0 ≤ C * ℓ² * (∫W₁)²` and carries **none** of the intended `E₁`–`E₂` content.

## What is proved here

The intended row, with the integral parenthesised — the comparison of the continuum Coulomb
integral of `W₁` with its mass value that the mass step of `Work.BoseBogFS.ZPLatticeRow`
consumes:

* `E₁ := (2π)⁻³ ∫_p Ŵ₁(p)²/(2‖p‖²)`,
* `E₂ := Ŵ₁ω(0) = ∫W₁ω`,

and `ZPE1E2Row` states `|ℓ³E₁ − ℓ³E₂| ≤ C ℓ² (∫W₁)²`.

It is stated in the raw vocabulary `Ŵ₁ = W1fun v h (ell v μ)`, `Ŵ₁ω = W1omegaFun v h (ell v μ)`
so that it depends on **no** chapter file beyond `BoseFixR.Defs` and the corpus's `I2_integral_bound`
/ `W1_mass_bounds` / `existsAdmRegime` rows; the `W1At`/`W1ωAt` spelling of the same row is
`Work.BoseBogFS.ZPE1E2Corrected` (`ZPE1E2Corrected.lean`), which is definitionally this statement.

## Route

With `E₃ := ∫g₀ω` (`g₀ = v(1−ω)`, `ω = Classical.choose h`):

* `|E₁ − E₃| ≤ C₂(R/ℓ)²E₃` — FS `eq:I2-integral` (`Work.BoseB7AK.C3Q.I2_integral_bound`);
* `E₃ ≤ E₂ ≤ (1 + 2C₁(R/ℓ)²)E₃` — FS `eq:W1-g` (`W1_sharp_ae_aux`'s a.e. sandwich
  `g₀ ≤ W₁ ≤ (1+2C₁(R/ℓ)²)g₀`, multiplied by `0 ≤ ω ≤ 1` a.e.);
* `E₃ ≤ ∫g₀ = 8πa` — `ω ≤ 1` a.e.;
* `∫W₁ ≥ 8πa` — `W1_mass_bounds`.

Hence `|E₁ − E₂| ≤ (C₂ + 2C₁)(R/ℓ)²·8πa`, and with the box side dominating the prescribed
constant `(C₂+2C₁)R²/(8πa)` (`exists_adm_ell_ge`, available because `Adm` bounds the diluteness
`μa³` only from above) this is `≤ (∫W₁)²/ℓ`:

`(C₂+2C₁)8πaℓR² ≤ ℓ²(8πa)² ≤ ℓ²(∫W₁)²`.

The regime rows (`R ≤ ℓ·chiR0`, `R/ℓ ≤ 1/4`, `C₁(R/ℓ)² ≤ 1/2`, `ℓ ≥ 1`) are
`Work.BoseBogFS.existsAdmRegime`.  The close-density hypothesis `CloseCondFS v μ ρ` is unused:
the row is independent of `ρ`.
-/

noncomputable section
open MeasureTheory Metric
open scoped Real

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

theorem ZPE1E2Row :
    ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ},
      0 < R → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v → tsupport v ⊆ Metric.ball 0 R →
      0 < _root_.BoseGases.a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ ρ : ℝ, Work.BoseBoxFock.CloseCondFS v μ ρ →
          |((2 * Real.pi) ^ 3)⁻¹ * (Work.BoseFixR.ell v μ) ^ 3
              * (∫ p : EuclideanSpace ℝ (Fin 3),
                  (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) p) ^ 2
                    / (2 * ‖p‖ ^ 2))
            - (Work.BoseFixR.ell v μ) ^ 3
                * Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseFixR.ell v μ)) 0|
          ≤ C * (Work.BoseFixR.ell v μ) ^ 2
              * (∫ x : EuclideanSpace ℝ (Fin 3),
                  Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ) x) ^ 2 := by
  intro v h R hR hv hvrad hv_supp hav
  -- the two global constants of FS `eq:I2-integral` and `eq:W1-g`
  obtain ⟨C₁, hC₁0, hC₁⟩ := Work.BoseB7AK.C3Q.conv3chi_dev_quad
  obtain ⟨C₂, hC₂0, hI2⟩ := Work.BoseB7AK.C3Q.I2_integral_bound
  -- the diluteness threshold at which the box side exceeds `(C₂+2C₁)R²/(8πa)`
  have hMpos : 0 < max 1 ((C₂ + 2 * C₁) * R ^ 2 / (8 * Real.pi * _root_.BoseGases.a v)) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Work.BoseBogFS.exists_adm_ell_ge (v := v) hav hMpos
  -- the regime threshold (`R ≤ ℓ chiR0`, `R/ℓ ≤ 1/4`, `C₁(R/ℓ)² ≤ 1/2`)
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Work.BoseBogFS.existsAdmRegime (v := v) (R := R)
    (C := C₁) (r₁ := 1 / 4) hR hav hC₁0 (by norm_num)
  refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, 1, zero_le_one, ?_⟩
  intro μ hμ ρ hρ
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ := ⟨hμ.1, le_trans hμ.2.1 (min_le_left _ _), hμ.2.2⟩
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ := ⟨hμ.1, le_trans hμ.2.1 (min_le_right _ _), hμ.2.2⟩
  obtain ⟨hRℓ, hr₁, hcond⟩ := hε₂ μ hAdm₂
  have hℓge : max 1 ((C₂ + 2 * C₁) * R ^ 2 / (8 * Real.pi * _root_.BoseGases.a v))
      ≤ Work.BoseFixR.ell v μ := hε₁ μ hAdm₁
  have hℓpos : 0 < Work.BoseFixR.ell v μ := lt_of_lt_of_le hMpos hℓge
  -- abbreviate the box side
  set L : ℝ := Work.BoseFixR.ell v μ with hL
  -- the integrability and a.e. data
  have hE3int : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.g0 v h x * Classical.choose h x) :=
    Submission.BoseGases.g0w0_integrable hR hv hvrad hv_supp h
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hE3supp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ →
      Submission.BoseGases.g0 v h z * Classical.choose h z = 0 := by
    intro z hz
    rw [Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h, zero_mul]
  have hW1ωint : MeasureTheory.Integrable (Work.BoseFixR.W1omegaFun v h L) :=
    Submission.BoseGases.wScaled_integrable_ae hℓpos hR.le hRℓ hE3int hE3supp
  have hprod_eq : (fun x : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixR.W1fun v h L x * Classical.choose h x)
      = Work.BoseFixR.W1omegaFun v h L := by
    funext x
    simp only [Work.BoseFixR.W1fun, Work.BoseFixR.W1omegaFun, Submission.BoseGases.wScaled,
      div_eq_mul_inv]
    ring
  have hprodint : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixR.W1fun v h L x * Classical.choose h x) := by
    rw [hprod_eq]
    exact hW1ωint
  have hωb := Submission.BoseGases.chosen_w0_bounds_ae (v := v) (R := R) hR hv hvrad hv_supp h
  have hω0 : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Classical.choose h x := hωb.1
  have hω1 : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), Classical.choose h x ≤ 1 := hωb.2
  have hg0nn : ∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Submission.BoseGases.g0 v h x :=
    Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  have hWsh := Work.BoseB7AK.C3Q.W1_sharp_ae_aux (v := v) (R := R) (ℓ := L) (C₁ := C₁)
    hR hℓpos hC₁0 hC₁ hv hvrad hv_supp h hRℓ
  have hW1ge := Work.BoseB7AK.C3Q.I2_g0_le_W1fun_ae (v := v) (R := R) (ℓ := L)
    hR hℓpos hv hvrad hv_supp h hRℓ
  -- FS `eq:I2-integral`
  have hI2' := hI2 (v := v) (R := R) (ℓ := L) hR hℓpos hv hvrad hv_supp h hRℓ
  -- the mass sandwich of `W₁`
  have hmass := Work.BoseBogFS.W1_mass_bounds (v := v) (h := h) (R := R) (ℓ := L)
    (r₁ := 1 / 4) (C := C₁) hR hv hvrad hv_supp hC₁0 (by norm_num) hℓpos
    (fun x _ => hC₁ x) hr₁ hcond
  have hW1low : 8 * Real.pi * _root_.BoseGases.a v
      ≤ ∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h L x := hmass.1
  -- the elementary integral comparisons
  have hG3le : (∫ x : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.g0 v h x * Classical.choose h x)
      ≤ 8 * Real.pi * _root_.BoseGases.a v := by
    have hmono := MeasureTheory.integral_mono_ae hE3int hg0int (by
      filter_upwards [hω1, hg0nn] with x h1 h0
      calc Submission.BoseGases.g0 v h x * Classical.choose h x
          ≤ Submission.BoseGases.g0 v h x * 1 := mul_le_mul_of_nonneg_left h1 h0
        _ = Submission.BoseGases.g0 v h x := mul_one _)
    rwa [Submission.BoseGases.g0_integral hR hv_supp h] at hmono
  have hG32 : (∫ x : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.g0 v h x * Classical.choose h x)
      ≤ ∫ x : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixR.W1fun v h L x * Classical.choose h x := by
    refine MeasureTheory.integral_mono_ae hE3int hprodint ?_
    filter_upwards [hW1ge, hω0] with x hx h0
    exact mul_le_mul_of_nonneg_right hx h0
  have hG2upper : (∫ x : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixR.W1fun v h L x * Classical.choose h x)
      ≤ (1 + 2 * C₁ * (R / L) ^ 2)
        * ∫ x : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.g0 v h x * Classical.choose h x := by
    have hmono := MeasureTheory.integral_mono_ae hprodint (hE3int.const_mul _) (by
      filter_upwards [hWsh, hω0] with x hx h0
      calc Work.BoseFixR.W1fun v h L x * Classical.choose h x
          ≤ ((1 + 2 * C₁ * (R / L) ^ 2) * Submission.BoseGases.g0 v h x)
              * Classical.choose h x := mul_le_mul_of_nonneg_right hx.2 h0
        _ = (1 + 2 * C₁ * (R / L) ^ 2)
              * (Submission.BoseGases.g0 v h x * Classical.choose h x) := by ring)
    rwa [MeasureTheory.integral_const_mul] at hmono
  -- the value of `Ŵ₁ω(0)`
  have hE2eq : Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h L) 0
      = ∫ x : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixR.W1fun v h L x * Classical.choose h x := by
    rw [chat_zero_eq_integral _ hW1ωint, ← hprod_eq]
  -- the key bound
  have hkey : |((2 * Real.pi) ^ 3)⁻¹
        * (∫ p : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h L) p) ^ 2 / (2 * ‖p‖ ^ 2))
      - ∫ x : EuclideanSpace ℝ (Fin 3),
          Work.BoseFixR.W1fun v h L x * Classical.choose h x|
      ≤ (C₂ + 2 * C₁) * (R / L) ^ 2 * (8 * Real.pi * _root_.BoseGases.a v) := by
    have hsplit : ((2 * Real.pi) ^ 3)⁻¹
          * (∫ p : EuclideanSpace ℝ (Fin 3),
              (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h L) p) ^ 2 / (2 * ‖p‖ ^ 2))
        - ∫ x : EuclideanSpace ℝ (Fin 3),
            Work.BoseFixR.W1fun v h L x * Classical.choose h x
        = (((2 * Real.pi) ^ 3)⁻¹
              * (∫ p : EuclideanSpace ℝ (Fin 3),
                  (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h L) p) ^ 2 / (2 * ‖p‖ ^ 2))
            - ∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.g0 v h x * Classical.choose h x)
          + ((∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.g0 v h x * Classical.choose h x)
            - ∫ x : EuclideanSpace ℝ (Fin 3),
                Work.BoseFixR.W1fun v h L x * Classical.choose h x) := by ring
    rw [hsplit]
    have h3 : |(∫ x : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.g0 v h x * Classical.choose h x)
        - ∫ x : EuclideanSpace ℝ (Fin 3),
            Work.BoseFixR.W1fun v h L x * Classical.choose h x|
        ≤ 2 * C₁ * (R / L) ^ 2
          * (∫ x : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.g0 v h x * Classical.choose h x) := by
      rw [abs_of_nonpos (by linarith)]
      linarith [hG2upper]
    have h4 : C₂ * (R / L) ^ 2
            * (∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.g0 v h x * Classical.choose h x)
          + 2 * C₁ * (R / L) ^ 2
            * (∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.g0 v h x * Classical.choose h x)
        ≤ (C₂ + 2 * C₁) * (R / L) ^ 2 * (8 * Real.pi * _root_.BoseGases.a v) := by
      have hs : (0 : ℝ) ≤ (R / L) ^ 2 := sq_nonneg _
      have hC : (0 : ℝ) ≤ C₂ + 2 * C₁ := by linarith
      have h5 : (C₂ + 2 * C₁) * (R / L) ^ 2
            * (∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.g0 v h x * Classical.choose h x)
          ≤ (C₂ + 2 * C₁) * (R / L) ^ 2 * (8 * Real.pi * _root_.BoseGases.a v) :=
        mul_le_mul_of_nonneg_left hG3le (mul_nonneg hC hs)
      nlinarith [h5]
    calc |(((2 * Real.pi) ^ 3)⁻¹
            * (∫ p : EuclideanSpace ℝ (Fin 3),
                (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h L) p) ^ 2 / (2 * ‖p‖ ^ 2))
          - ∫ x : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.g0 v h x * Classical.choose h x)
        + ((∫ x : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.g0 v h x * Classical.choose h x)
          - ∫ x : EuclideanSpace ℝ (Fin 3),
              Work.BoseFixR.W1fun v h L x * Classical.choose h x)|
        ≤ |((2 * Real.pi) ^ 3)⁻¹
              * (∫ p : EuclideanSpace ℝ (Fin 3),
                  (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h L) p) ^ 2 / (2 * ‖p‖ ^ 2))
            - ∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.g0 v h x * Classical.choose h x|
          + |(∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.g0 v h x * Classical.choose h x)
            - ∫ x : EuclideanSpace ℝ (Fin 3),
                Work.BoseFixR.W1fun v h L x * Classical.choose h x| := abs_add_le _ _
      _ ≤ C₂ * (R / L) ^ 2
              * (∫ x : EuclideanSpace ℝ (Fin 3),
                  Submission.BoseGases.g0 v h x * Classical.choose h x)
          + 2 * C₁ * (R / L) ^ 2
            * (∫ x : EuclideanSpace ℝ (Fin 3),
                Submission.BoseGases.g0 v h x * Classical.choose h x) :=
          add_le_add hI2' h3
      _ ≤ (C₂ + 2 * C₁) * (R / L) ^ 2 * (8 * Real.pi * _root_.BoseGases.a v) := h4
  -- the arithmetic: the prescribed lower bound for the box side
  have hCR : (C₂ + 2 * C₁) * R ^ 2 ≤ 8 * Real.pi * _root_.BoseGases.a v * L := by
    have h8 : 0 < 8 * Real.pi * _root_.BoseGases.a v := by positivity
    have h1 : (C₂ + 2 * C₁) * R ^ 2 / (8 * Real.pi * _root_.BoseGases.a v) ≤ L :=
      le_trans (le_max_right _ _) hℓge
    rw [div_le_iff₀ h8] at h1
    linarith [h1]
  have hmain : (C₂ + 2 * C₁) * (8 * Real.pi * _root_.BoseGases.a v) * L * R ^ 2
      ≤ L ^ 2 * (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h L x) ^ 2 := by
    have h8L : (0 : ℝ) ≤ 8 * Real.pi * _root_.BoseGases.a v * L := by positivity
    have hchain : (C₂ + 2 * C₁) * (8 * Real.pi * _root_.BoseGases.a v) * L * R ^ 2
        ≤ (8 * Real.pi * _root_.BoseGases.a v * L) ^ 2 := by
      have h1 : (C₂ + 2 * C₁) * (8 * Real.pi * _root_.BoseGases.a v) * L * R ^ 2
          = (8 * Real.pi * _root_.BoseGases.a v * L) * ((C₂ + 2 * C₁) * R ^ 2) := by ring
      rw [h1]
      simpa [pow_two] using mul_le_mul_of_nonneg_left hCR h8L
    have hchain2 : (8 * Real.pi * _root_.BoseGases.a v * L) ^ 2
        ≤ ((∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h L x) * L) ^ 2 := by
      refine pow_le_pow_left₀ h8L ?_ 2
      exact mul_le_mul_of_nonneg_right hW1low hℓpos.le
    calc (C₂ + 2 * C₁) * (8 * Real.pi * _root_.BoseGases.a v) * L * R ^ 2
        ≤ (8 * Real.pi * _root_.BoseGases.a v * L) ^ 2 := hchain
      _ ≤ ((∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h L x) * L) ^ 2 := hchain2
      _ = L ^ 2 * (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h L x) ^ 2 := by ring
  -- the comparison, with `L` pulled out of the absolute value
  have hstep1 : |((2 * Real.pi) ^ 3)⁻¹ * L ^ 3
          * (∫ p : EuclideanSpace ℝ (Fin 3),
              (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h L) p) ^ 2 / (2 * ‖p‖ ^ 2))
        - L ^ 3 * (∫ x : EuclideanSpace ℝ (Fin 3),
            Work.BoseFixR.W1fun v h L x * Classical.choose h x)|
        = L ^ 3 * |((2 * Real.pi) ^ 3)⁻¹
            * (∫ p : EuclideanSpace ℝ (Fin 3),
                (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h L) p) ^ 2 / (2 * ‖p‖ ^ 2))
          - ∫ x : EuclideanSpace ℝ (Fin 3),
              Work.BoseFixR.W1fun v h L x * Classical.choose h x| := by
    rw [show ((2 * Real.pi) ^ 3)⁻¹ * L ^ 3
          * (∫ p : EuclideanSpace ℝ (Fin 3),
              (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h L) p) ^ 2 / (2 * ‖p‖ ^ 2))
        - L ^ 3 * (∫ x : EuclideanSpace ℝ (Fin 3),
            Work.BoseFixR.W1fun v h L x * Classical.choose h x)
        = L ^ 3 * (((2 * Real.pi) ^ 3)⁻¹
            * (∫ p : EuclideanSpace ℝ (Fin 3),
                (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h L) p) ^ 2 / (2 * ‖p‖ ^ 2))
          - ∫ x : EuclideanSpace ℝ (Fin 3),
              Work.BoseFixR.W1fun v h L x * Classical.choose h x) by ring,
      abs_mul, abs_of_nonneg (pow_nonneg hℓpos.le 3)]
  have hgoal : |((2 * Real.pi) ^ 3)⁻¹ * L ^ 3
        * (∫ p : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h L) p) ^ 2 / (2 * ‖p‖ ^ 2))
      - L ^ 3 * Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h L) 0|
      ≤ 1 * L ^ 2 * (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h L x) ^ 2 := by
    rw [hE2eq, hstep1]
    calc L ^ 3 * |((2 * Real.pi) ^ 3)⁻¹
          * (∫ p : EuclideanSpace ℝ (Fin 3),
              (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h L) p) ^ 2 / (2 * ‖p‖ ^ 2))
        - ∫ x : EuclideanSpace ℝ (Fin 3),
            Work.BoseFixR.W1fun v h L x * Classical.choose h x|
        ≤ L ^ 3 * ((C₂ + 2 * C₁) * (R / L) ^ 2 * (8 * Real.pi * _root_.BoseGases.a v)) :=
          mul_le_mul_of_nonneg_left hkey (pow_nonneg hℓpos.le 3)
      _ = (C₂ + 2 * C₁) * (8 * Real.pi * _root_.BoseGases.a v) * L * R ^ 2 := by
          have hLne : L ≠ 0 := ne_of_gt hℓpos
          field_simp
      _ ≤ L ^ 2 * (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h L x) ^ 2 := hmain
      _ = 1 * L ^ 2 * (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h L x) ^ 2 := by
          ring
  exact hgoal

end Work.BoseBogFS
