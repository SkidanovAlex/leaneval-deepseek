import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.symR_floor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.symR_floor_gen` — the pointwise floor with a *quantitative* `χ̂²`-row

This is `Work.BoseBoxFock.symR_floor` (`Submission/Work/BoseBoxFock/symR_floor.lean`) with the
`χ̂²`(`g`)-normalisation `Σ_{k ∈ excited Mode} (χ̂²_k)² ≤ 1` replaced by the quantitative
hypothesis `Σ_{k ∈ excited Mode} (χ̂²_k)² ≤ Kχb` (`0 ≤ Kχb`).  The only place where the
normalisation enters is the `r¹`-row `D1F`, whose `g`-part is bounded by Cauchy–Schwarz
against `√(Σ (χ̂²_k)²) · √K ‖w‖²`; with the quantitative bound this becomes

    `|⟪w, D1F w⟫_{g-part}| ≤ 4 ℓ⁻³ Ŵ₁ω(0) √(Kχb · K) r ‖w‖²`

instead of the `√K`-version.  The `f`-part (`Σ_k χ̂_k² ≤ 1`), the `r²`-row `D2F` and the
`r⁰`-row `D0F` are unchanged; the three rows are assembled exactly as in `symR_floor`.

Everything is a verbatim adaptation of `Work.BoseBoxFock.symR_row_D1F` /
`Work.BoseBoxFock.symR_floor` with `1 ↦ Real.sqrt Kχb` in the `hs1` step of the `g`-row,
`Real.sqrt (Kχb * K) = Real.sqrt Kχb * Real.sqrt K` (`Real.sqrt_mul`) at the end of the row,
and the same substitution in the assembly's arithmetic.
-/

namespace Work.BoseBoxFock

noncomputable section

open scoped BigOperators

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-! ## 1. The `r¹`-row `D1F` with the quantitative `χ̂²` bound -/

/-- The `r¹`-row of the discrepancy with the quantitative `χ̂²`(`g`)-row bound `Kχb`:
the `χ̂`(`f`)-row is controlled by `hKc` (`nPlusChi f ≤ Kc‖w‖²`, `Σ_k χ̂_k² ≤ 1`) and the
`χ̂²`(`g`)-row by the orthonormality of `g` on the excited modes together with `hK`
(`n₊ ≤ K‖w‖²`) and `Σ_{k∈exc} (χ̂²_k)² ≤ Kχb`, giving `√(Kχb · K)`. -/
lemma symR_row_D1F_gen {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode)
    (hℓ : 0 < E.ell) (hω0 : 0 ≤ E.W1omega0)
    (hgonb : ∀ s ∈ Work.BoseB7.excited Mode, ∀ t ∈ Work.BoseB7.excited Mode,
      Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0)
    (K Kc Kχb : ℝ) (hK0 : 0 ≤ K) (hKc0 : 0 ≤ Kc) (hKχb0 : 0 ≤ Kχb)
    (hχ2 : (∑ k : Mode, E.hatChi k ^ 2) ≤ 1)
    (hχ2b : (∑ k ∈ Work.BoseB7.excited Mode, E.hatChiSq k ^ 2) ≤ Kχb)
    (w : cfock (Excited m))
    (hKc : (inner ℂ w (nPlusChi f w)).re ≤ Kc * ‖w‖ ^ 2)
    (hK : (inner ℂ w (nPlusC (m := m) w)).re ≤ K * ‖w‖ ^ 2) :
    (inner ℂ w (D1F f g E w)).re
      ≥ -(4 * i3F E * (|E.W1 0| * Real.sqrt Kc
            + E.W1omega0 * Real.sqrt (Kχb * K))) * ‖w‖ ^ 2 := by
  have hi3 : 0 < i3F E := i3_pos E hℓ
  set Pf : ℝ := (inner ℂ w ((BchiC (Finset.univ : Finset Mode) E.hatChi 1 f
      + BchiA (Finset.univ : Finset Mode) E.hatChi 1 f) w)).re with hPf
  set Pg : ℝ := (inner ℂ w ((BchiC (Work.BoseB7.excited Mode) E.hatChiSq 1 g
      + BchiA (Work.BoseB7.excited Mode) E.hatChiSq 1 g) w)).re with hPg
  have hsplit : (inner ℂ w (D1F f g E w)).re
      = (-(2 * i3F E * E.W1 0)) * Pf + (-(2 * i3F E * E.W1omega0)) * Pg := by
    rw [D1F, hPf, hPg]
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    simp only [kfb_inner_addR, kfb_inner_smulR, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hPf_abs : |Pf| ≤ 2 * Real.sqrt Kc * ‖w‖ ^ 2 := by
    have hb := chiRowFinset_bound (Finset.univ : Finset Mode) E.hatChi f w
    have hword : (∑ k ∈ (Finset.univ : Finset Mode), ((E.hatChi k : ℝ) : ℂ) •
          (annOfE (f k) + creOfE (f k)))
        = BchiC (Finset.univ : Finset Mode) E.hatChi 1 f
          + BchiA (Finset.univ : Finset Mode) E.hatChi 1 f := by
      rw [BchiC_add_BchiA]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_mul]
    rw [hword] at hb
    have hnsq : (∑ k ∈ (Finset.univ : Finset Mode), ‖annOfE (f k) w‖ ^ 2)
        = (inner ℂ w (nPlusChi f w)).re := by
      rw [chiRow_nPlusChi_re]
    have hs2 : Real.sqrt (∑ k ∈ (Finset.univ : Finset Mode), ‖annOfE (f k) w‖ ^ 2)
        ≤ Real.sqrt Kc * ‖w‖ := by
      rw [hnsq, ← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_mul hKc0]
      exact Real.sqrt_le_sqrt hKc
    have hs1 : Real.sqrt (∑ k ∈ (Finset.univ : Finset Mode), E.hatChi k ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      simpa using hχ2
    calc |Pf| ≤ 2 * Real.sqrt (∑ k ∈ (Finset.univ : Finset Mode), E.hatChi k ^ 2)
          * Real.sqrt (∑ k ∈ (Finset.univ : Finset Mode), ‖annOfE (f k) w‖ ^ 2) * ‖w‖ := hb
      _ ≤ 2 * 1 * (Real.sqrt Kc * ‖w‖) * ‖w‖ := by gcongr
      _ = 2 * Real.sqrt Kc * ‖w‖ ^ 2 := by ring
  have hPg_abs : |Pg| ≤ 2 * Real.sqrt Kχb * Real.sqrt K * ‖w‖ ^ 2 := by
    have hb := chiRowFinset_bound (Work.BoseB7.excited Mode) E.hatChiSq g w
    have hword : (∑ k ∈ Work.BoseB7.excited Mode, ((E.hatChiSq k : ℝ) : ℂ) •
          (annOfE (g k) + creOfE (g k)))
        = BchiC (Work.BoseB7.excited Mode) E.hatChiSq 1 g
          + BchiA (Work.BoseB7.excited Mode) E.hatChiSq 1 g := by
      rw [BchiC_add_BchiA]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_mul]
    rw [hword] at hb
    have hnsq : (∑ k ∈ Work.BoseB7.excited Mode, ‖annOfE (g k) w‖ ^ 2)
        ≤ (inner ℂ w (nPlusC (m := m) w)).re :=
      sum_annOfE_normSq_le_nPlusC (Work.BoseB7.excited Mode) g hgonb w
    have hs2 : Real.sqrt (∑ k ∈ Work.BoseB7.excited Mode, ‖annOfE (g k) w‖ ^ 2)
        ≤ Real.sqrt K * ‖w‖ := by
      rw [← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_mul hK0]
      exact Real.sqrt_le_sqrt (le_trans hnsq hK)
    have hs1 : Real.sqrt (∑ k ∈ Work.BoseB7.excited Mode, E.hatChiSq k ^ 2)
        ≤ Real.sqrt Kχb := Real.sqrt_le_sqrt hχ2b
    calc |Pg| ≤ 2 * Real.sqrt (∑ k ∈ Work.BoseB7.excited Mode, E.hatChiSq k ^ 2)
          * Real.sqrt (∑ k ∈ Work.BoseB7.excited Mode, ‖annOfE (g k) w‖ ^ 2) * ‖w‖ := hb
      _ ≤ 2 * Real.sqrt Kχb * (Real.sqrt K * ‖w‖) * ‖w‖ := by gcongr
      _ = 2 * Real.sqrt Kχb * Real.sqrt K * ‖w‖ ^ 2 := by ring
  rw [hsplit]
  have h1 : (-(2 * i3F E * E.W1 0)) * Pf
      ≥ -(4 * i3F E * |E.W1 0| * Real.sqrt Kc) * ‖w‖ ^ 2 := by
    have hc : |(-(2 * i3F E * E.W1 0))| = 2 * i3F E * |E.W1 0| := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_pos hi3, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have hlow : (-(2 * i3F E * E.W1 0)) * Pf ≥ -|(-(2 * i3F E * E.W1 0))| * |Pf| := by
      have h := neg_abs_le ((-(2 * i3F E * E.W1 0)) * Pf)
      rw [abs_mul] at h
      linarith
    have hup : -|(-(2 * i3F E * E.W1 0))| * |Pf|
        ≥ -|(-(2 * i3F E * E.W1 0))| * (2 * Real.sqrt Kc * ‖w‖ ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hPf_abs (abs_nonneg ((-(2 * i3F E * E.W1 0))))
      nlinarith [h]
    rw [hc] at hlow hup
    nlinarith [hlow, hup]
  have h2 : (-(2 * i3F E * E.W1omega0)) * Pg
      ≥ -(4 * i3F E * E.W1omega0 * Real.sqrt Kχb * Real.sqrt K) * ‖w‖ ^ 2 := by
    have hc : |(-(2 * i3F E * E.W1omega0))| = 2 * i3F E * E.W1omega0 := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_pos hi3, abs_of_pos (by norm_num : (0:ℝ) < 2),
        abs_of_nonneg hω0]
    have hlow : (-(2 * i3F E * E.W1omega0)) * Pg ≥ -|(-(2 * i3F E * E.W1omega0))| * |Pg| := by
      have h := neg_abs_le ((-(2 * i3F E * E.W1omega0)) * Pg)
      rw [abs_mul] at h
      linarith
    have hup : -|(-(2 * i3F E * E.W1omega0))| * |Pg|
        ≥ -|(-(2 * i3F E * E.W1omega0))| * (2 * Real.sqrt Kχb * Real.sqrt K * ‖w‖ ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hPg_abs (abs_nonneg ((-(2 * i3F E * E.W1omega0))))
      nlinarith [h]
    rw [hc] at hlow hup
    nlinarith [hlow, hup]
  have haux : (-(2 * i3F E * E.W1 0)) * Pf + (-(2 * i3F E * E.W1omega0)) * Pg
      ≥ -(4 * i3F E * |E.W1 0| * Real.sqrt Kc) * ‖w‖ ^ 2
        + -(4 * i3F E * E.W1omega0 * Real.sqrt Kχb * Real.sqrt K) * ‖w‖ ^ 2 := add_le_add h1 h2
  have heq : -(4 * i3F E * (|E.W1 0| * Real.sqrt Kc
          + E.W1omega0 * Real.sqrt (Kχb * K))) * ‖w‖ ^ 2
      = -(4 * i3F E * |E.W1 0| * Real.sqrt Kc) * ‖w‖ ^ 2
        + -(4 * i3F E * E.W1omega0 * Real.sqrt Kχb * Real.sqrt K) * ‖w‖ ^ 2 := by
    rw [Real.sqrt_mul hKχb0]
    ring
  rw [heq]
  linarith [haux]

/-! ## 2. The assembly -/

theorem symR_floor_gen {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (f g : Mode → Fin m → ℝ)
    (BNH : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (PHs : Finset Mode) (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (gHat0 : ℝ) (hℓ : 0 < E.ell) (hPH : PHs = F.PHset E)
    (hcH : 0 ≤ Work.BoseBoxFock.cHCF E gHat0) (hω0 : 0 ≤ E.W1omega0)
    (hφ : ∀ k : Mode, f k 0 = 0)
    (hgonb : ∀ s ∈ Work.BoseB7.excited Mode, ∀ t ∈ Work.BoseB7.excited Mode,
      Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0)
    (hdisc : ∀ r : ℝ, 0 ≤ r →
      Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
          - Work.BoseBoxFock.KzOpC f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)
        = ((r ^ 2 : ℝ) : ℂ) • Work.BoseBoxFock.D2F f E gHat0
          + ((r : ℝ) : ℂ) • Work.BoseBoxFock.D1F f g E
          + Work.BoseBoxFock.D0F f E gHat0)
    (K Kc Kχb Wsup : ℝ) (hK0 : 0 ≤ K) (hKc0 : 0 ≤ Kc) (hKχb0 : 0 ≤ Kχb)
    (hWsup : ∀ k : Mode, |E.W1 k + E.W1omega k| ≤ Wsup)
    (hχ2 : (∑ k : Mode, E.hatChi k ^ 2) ≤ 1)
    (hχ2b : (∑ k ∈ Work.BoseB7.excited Mode, E.hatChiSq k ^ 2) ≤ Kχb) :
    ∀ r : ℝ, 0 ≤ r → ∀ w : Work.BoseB4.cfock (Work.BoseB4.Excited m),
      (inner ℂ w (Work.BoseBoxFock.nPlusChi f w)).re ≤ Kc * ‖w‖ ^ 2 →
      (inner ℂ w (Work.BoseBoxFock.nPlusC (m := m) w)).re ≤ K * ‖w‖ ^ 2 →
      (inner ℂ w ((Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
          - Work.BoseBoxFock.KzOpC f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)) w)).re
        ≥ -(((4 * Work.BoseBoxFock.cHCF E gHat0) * r ^ 2
              + (4 * (Work.BoseBoxFock.i3F E)
                  * (|E.W1 0| * Real.sqrt Kc + E.W1omega0 * Real.sqrt (Kχb * K))) * r
              + (|2 * Work.BoseBoxFock.cHCF E gHat0 + E.mu * gHat0|
                  + (Work.BoseBoxFock.i3F E) * (Wsup + |E.W1 0 + E.W1omega0|) * Kc)))
          * ‖w‖ ^ 2 := by
  intro r hr w hKc hK
  have h2 := symR_row_D2F f E gHat0 hℓ hω0 w
  have h1 := symR_row_D1F_gen f g E hℓ hω0 hgonb K Kc Kχb hK0 hKc0 hKχb0 hχ2 hχ2b w hKc hK
  have h0 := symR_row_D0F f E gHat0 Kc Wsup hℓ hWsup w hKc
  have hL : (inner ℂ w ((Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
        - Work.BoseBoxFock.KzOpC f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)) w)).re
      = r ^ 2 * (inner ℂ w (Work.BoseBoxFock.D2F f E gHat0 w)).re
        + r * (inner ℂ w (Work.BoseBoxFock.D1F f g E w)).re
        + (inner ℂ w (Work.BoseBoxFock.D0F f E gHat0 w)).re := by
    rw [hdisc r hr]
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    simp only [kfb_inner_addR, kfb_inner_smulR, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hL]
  have hA : r ^ 2 * (-(4 * Work.BoseBoxFock.cHCF E gHat0) * ‖w‖ ^ 2)
      ≤ r ^ 2 * (inner ℂ w (Work.BoseBoxFock.D2F f E gHat0 w)).re :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg r)
  have hB : r * (-(4 * (Work.BoseBoxFock.i3F E)
        * (|E.W1 0| * Real.sqrt Kc
          + E.W1omega0 * Real.sqrt (Kχb * K))) * ‖w‖ ^ 2)
      ≤ r * (inner ℂ w (Work.BoseBoxFock.D1F f g E w)).re :=
    mul_le_mul_of_nonneg_left h1 hr
  have hC : -(|2 * Work.BoseBoxFock.cHCF E gHat0 + E.mu * gHat0|
        + (Work.BoseBoxFock.i3F E) * (Wsup + |E.W1 0 + E.W1omega0|) * Kc) * ‖w‖ ^ 2
      ≤ (inner ℂ w (Work.BoseBoxFock.D0F f E gHat0 w)).re := h0
  have hring : -(((4 * Work.BoseBoxFock.cHCF E gHat0) * r ^ 2
        + (4 * (Work.BoseBoxFock.i3F E)
            * (|E.W1 0| * Real.sqrt Kc + E.W1omega0 * Real.sqrt (Kχb * K))) * r
        + (|2 * Work.BoseBoxFock.cHCF E gHat0 + E.mu * gHat0|
            + (Work.BoseBoxFock.i3F E) * (Wsup + |E.W1 0 + E.W1omega0|) * Kc)))
        * ‖w‖ ^ 2
      = r ^ 2 * (-(4 * Work.BoseBoxFock.cHCF E gHat0) * ‖w‖ ^ 2)
        + r * (-(4 * (Work.BoseBoxFock.i3F E)
            * (|E.W1 0| * Real.sqrt Kc
              + E.W1omega0 * Real.sqrt (Kχb * K))) * ‖w‖ ^ 2)
        + (-(|2 * Work.BoseBoxFock.cHCF E gHat0 + E.mu * gHat0|
            + (Work.BoseBoxFock.i3F E) * (Wsup + |E.W1 0 + E.W1omega0|) * Kc) * ‖w‖ ^ 2) := by
    ring
  rw [hring]
  linarith [hA, hB, hC]

end

end Work.BoseBoxFock
