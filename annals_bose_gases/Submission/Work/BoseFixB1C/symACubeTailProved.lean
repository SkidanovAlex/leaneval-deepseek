import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.chiSmall_kinFT_decay
import Submission.Work.BoseFixB1S.cubeFamFormFtruncTendsto2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1C.symACubeTailProved` — the cube tail scalar, **proved**

This module proves `Work.BoseFixB1C.symACube_tail_scalar`, a byte-for-byte drop-in for the
`sorry`-carrying `Work.BoseFixB1B.symACube_tail_scalar`
(`Submission/Work/BoseFixB1B/symACube_tail_scalar.lean`, the **sole** `sorryAx` origin of the
decision-(B) chain `kineticHalfCube_le_mainWord → OneBodyKineticHalfCube → KineticHalfCube →
SlidingBCube`, see `Submission/Work/BoseFixB1C/PLAN_SlidingBCube.md`).

Statement.  `∃ ε₀ > 0`, `∀ μ` with `Adm v ε₀ μ`,

    symACube M 1 (fsKinCoeff ((2s)⁻¹)) 0 · chiSupAbs²  ≤  (bValue/4)·d² ,

with `M = 48`, `s = X = (μa³)^{1/323}`, `d = X⁶ = (μa³)^{6/323}`.

## Proof

`symACube M 1 F 0 = (2π)⁻³ ∫_p F‖p‖·profHatCube(M,p)²` definitionally (`1⁻¹•p = p`, `0 + p = p`).
The polynomial tail of the symbol is small because the cube bump's Fourier transform decays
polynomially:

1. **`profHatCube` is the modulus of the cube bump's Fourier transform**:
   `Work.BoseFixB1S.cubeKinFT_chiSmall` (PROVED, axiom-clean) gives
   `kinFT (chiSmall M : E3 → ℂ) p = (profHatCube M p : ℂ)`; hence
   `|profHatCube M p| = ‖kinFT (chiSmall M) p‖` (`profHatCube_abs_eq_kinFT`).
2. **Decay** (`profHatCube_decay`): `Work.BoseFixB1B.chiSmall_kinFT_decay 47 48` (PROVED,
   axiom-clean, `C^{47}` regularity of `chiSmall 48`) at `ρ = 1`, `u = 0` gives
   `|profHatCube 48 p| ≤ C/(1+‖p‖)⁴⁷`.
3. **The cutoff tail**: for `c > 0`, `r ≥ 0` and any `k`,
   `[r − c]₊² ≤ (c^k)⁻¹ (1+r)^{k+2}` (`fsKinCoeff_le_inv_pow_mul`): if `r ≤ c` the left side
   vanishes; if `r > c` then `c^k (r−c)² < r^k r² = r^{k+2} ≤ (1+r)^{k+2}`.
4. **Integration** (`symACube_fsKinCoeff_integral_le`): with `k = 84`, `N = 47` the pointwise
   product is `≤ (c^84)⁻¹ C² (1+‖p‖)^{-8}`, whose integral is `K8 = ∫(1+‖p‖)^{-8}` (finite,
   `integrable_one_add_norm`, dim 3 < 8).
5. **Arithmetic**: `c = (2s)⁻¹`, so `(c^84)⁻¹ = 2^84 s^84`; `d = s^6`, so `d² = s^12`.  With
   `Pi0 := (2π)⁻³·2^84·C²·K8·chiSupAbs²/(bValue/4)` and `ε₀ := (1/(Pi0+1))^{323/72}`, the hypothesis
   `μa³ ≤ ε₀` gives `s ≤ (1/(Pi0+1))^{1/72}`, hence `s^72·Pi0 ≤ 1`, and finally
   `(2π)⁻³(2s)^84 C² K8 chiSupAbs² ≤ (bValue/4)s^12`.

No integration by parts, no `Fisher`/`Fourier` API: the only analytic inputs are the two PROVED
decay lemmas on disk.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1C

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. `profHatCube` is the modulus of the cube bump's Fourier transform -/

/-- `profHatCube M p = |kinFT (chiSmall M) p|`: the cosine profile is the *real part* of the
cube bump's `p`-convention Fourier transform (`Work.BoseFixB1S.cubeKinFT_chiSmall`). -/
theorem profHatCube_abs_eq_kinFT (M : ℕ) (hM : 1 ≤ M) (p : E3) :
    |Work.BoseFixB1S.profHatCube M p|
      = ‖Submission.BoseGases.kinFT
          (fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ)) p‖ := by
  rw [Work.BoseFixB1S.cubeKinFT_chiSmall M hM p]
  exact (RCLike.norm_ofReal (K := ℂ) (Work.BoseFixB1S.profHatCube M p)).symm

/-- **Fourier decay of the cube cosine profile**: for `N + 1 ≤ M` there is `C ≥ 0` with
`|profHatCube M p| ≤ C / (1+‖p‖)^N` — the `L¹`/IBP decay of the `C^{M−1}` bump. -/
theorem profHatCube_decay (N M : ℕ) (hNM : N + 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : E3,
      |Work.BoseFixB1S.profHatCube M p| ≤ C / (1 + ‖p‖) ^ N := by
  obtain ⟨C, hC0, hC⟩ := Work.BoseFixB1B.chiSmall_kinFT_decay N M hNM
  refine ⟨C, hC0, fun p => ?_⟩
  have hfun : (fun z : E3 => (Submission.BoseGases.chiSmall M ((1 : ℝ)⁻¹ • z - (0 : E3)) : ℂ))
      = fun z : E3 => (Submission.BoseGases.chiSmall M z : ℂ) := by
    funext z
    simp
  have h := hC 1 (by norm_num) (by norm_num) (0 : E3) p
  rw [hfun] at h
  simp only [one_pow, mul_one, one_mul] at h
  rw [profHatCube_abs_eq_kinFT M (by omega) p]
  exact h

/-! ## 2. The elementary cutoff tail -/

/-- **The cutoff tail**: `[r − c]₊² ≤ (c^k)⁻¹ (1+r)^{k+2}` for `c > 0`, `r ≥ 0`, any `k`.
For `r ≤ c` the left side vanishes; for `r > c`, `c^k (r−c)² < r^k r² = r^{k+2} ≤ (1+r)^{k+2}`. -/
theorem fsKinCoeff_le_inv_pow_mul {c : ℝ} (hc : 0 < c) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    Submission.BoseGases.fsKinCoeff c r ≤ (c ^ k)⁻¹ * (1 + r) ^ (k + 2) := by
  rw [Submission.BoseGases.fsKinCoeff]
  rcases le_or_gt r c with h | h
  · rw [max_eq_right (by linarith : r - c ≤ 0), zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hc.le k)) (pow_nonneg (by linarith) _)
  · rw [max_eq_left (by linarith : 0 ≤ r - c)]
    have hck : 0 < c ^ k := pow_pos hc k
    have hkey : c ^ k * (r - c) ^ 2 ≤ (1 + r) ^ (k + 2) := by
      have h1 : c ^ k * (r - c) ^ 2 ≤ r ^ k * (r - c) ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc.le h.le k) (sq_nonneg _)
      have h2 : r ^ k * (r - c) ^ 2 ≤ r ^ k * r ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ r - c) (by linarith) 2)
          (pow_nonneg hr k)
      have h3 : r ^ k * r ^ 2 = r ^ (k + 2) := (pow_add r k 2).symm
      have h4 : r ^ (k + 2) ≤ (1 + r) ^ (k + 2) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      linarith [h1, h2, h3.le, h3.ge, h4]
    have hkey' : (r - c) ^ 2 * c ^ k ≤ (1 + r) ^ (k + 2) := by
      rw [mul_comm]; exact hkey
    have hfin : (r - c) ^ 2 ≤ (1 + r) ^ (k + 2) / c ^ k := (le_div_iff₀ hck).mpr hkey'
    rwa [div_eq_inv_mul] at hfin

/-! ## 3. The reference integral `K8 = ∫(1+‖p‖)^{-8}` -/

/-- The (finite) reference integral `∫_{E3} (1+‖p‖)^{-8} dp`. -/
noncomputable def K8 : ℝ := ∫ p : E3, ((1 + ‖p‖) ^ 8)⁻¹

theorem K8_nonneg : 0 ≤ K8 :=
  integral_nonneg fun p => inv_nonneg.mpr (pow_nonneg (by positivity) 8)

/-- `(1+‖p‖)^{-j}` is integrable in dimension `3` as soon as `j > 3`
(`integrable_one_add_norm`). -/
theorem integrable_one_add_norm_pow_inv (j : ℕ) (hj : 3 < j) :
    Integrable (fun p : E3 => ((1 + ‖p‖) ^ j)⁻¹) volume := by
  have h := integrable_one_add_norm (μ := (volume : Measure E3)) (r := (j : ℝ)) (by
    rw [finrank_euclideanSpace_fin]
    exact_mod_cast hj)
  refine h.congr ?_
  filter_upwards with p
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

/-! ## 4. The symbol integral against a polynomially decaying profile -/

/-- `a^86 · (a^94)⁻¹ = (a^8)⁻¹`. -/
theorem pow86_mul_inv_pow94 (a : ℝ) (ha : a ≠ 0) :
    a ^ 86 * (a ^ 94)⁻¹ = (a ^ 8)⁻¹ := by
  have h : a ^ 86 = a ^ 94 * (a ^ 8)⁻¹ := by
    rw [show (86 : ℕ) = 94 - 8 from by norm_num, pow_sub₀ a ha (by norm_num)]
  rw [h, mul_assoc, mul_comm ((a ^ 8)⁻¹) ((a ^ 94)⁻¹), ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero 94 ha), one_mul]

/-- **The symbol tail integral**: against a profile decaying as `C/(1+‖p‖)^47`,
`∫_p [‖p‖−c]₊² profHat² ≤ (c^84)⁻¹ C² K8`. -/
theorem symACube_fsKinCoeff_integral_le (M : ℕ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hdec : ∀ p : E3, |Work.BoseFixB1S.profHatCube M p| ≤ C / (1 + ‖p‖) ^ 47) :
    (∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖
        * (Work.BoseFixB1S.profHatCube M p) ^ 2)
      ≤ (c ^ 84)⁻¹ * C ^ 2 * K8 := by
  have hgint : Integrable (fun p : E3 => (c ^ 84)⁻¹ * C ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹) volume :=
    (integrable_one_add_norm_pow_inv 8 (by norm_num)).const_mul _
  have hpoint : ∀ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖
        * (Work.BoseFixB1S.profHatCube M p) ^ 2
      ≤ (c ^ 84)⁻¹ * C ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹ := by
    intro p
    have hr : 0 ≤ ‖p‖ := norm_nonneg p
    have h1 : Submission.BoseGases.fsKinCoeff c ‖p‖
        ≤ (c ^ 84)⁻¹ * (1 + ‖p‖) ^ 86 := fsKinCoeff_le_inv_pow_mul hc 84 hr
    have h2 : (Work.BoseFixB1S.profHatCube M p) ^ 2 ≤ C ^ 2 * ((1 + ‖p‖) ^ 94)⁻¹ := by
      have habs := hdec p
      have hsq : (Work.BoseFixB1S.profHatCube M p) ^ 2
          = |Work.BoseFixB1S.profHatCube M p| ^ 2 := (sq_abs _).symm
      rw [hsq]
      have hsq2 : (C / (1 + ‖p‖) ^ 47) ^ 2 = C ^ 2 * ((1 + ‖p‖) ^ 94)⁻¹ := by
        rw [div_pow, ← pow_mul, div_eq_mul_inv]
      rw [← hsq2]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have h3 : (c ^ 84)⁻¹ * (1 + ‖p‖) ^ 86 * (C ^ 2 * ((1 + ‖p‖) ^ 94)⁻¹)
        = (c ^ 84)⁻¹ * C ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹ := by
      rw [← pow86_mul_inv_pow94 (1 + ‖p‖) (by positivity)]
      ring
    calc Submission.BoseGases.fsKinCoeff c ‖p‖
          * (Work.BoseFixB1S.profHatCube M p) ^ 2
        ≤ ((c ^ 84)⁻¹ * (1 + ‖p‖) ^ 86) * (C ^ 2 * ((1 + ‖p‖) ^ 94)⁻¹) :=
          mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = (c ^ 84)⁻¹ * C ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹ := h3
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun p =>
      mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))
    hgint (Filter.Eventually.of_forall hpoint)
  calc (∫ p : E3, Submission.BoseGases.fsKinCoeff c ‖p‖
        * (Work.BoseFixB1S.profHatCube M p) ^ 2)
      ≤ ∫ p : E3, (c ^ 84)⁻¹ * C ^ 2 * ((1 + ‖p‖) ^ 8)⁻¹ := hmono
    _ = (c ^ 84)⁻¹ * C ^ 2 * K8 := by
        rw [MeasureTheory.integral_const_mul]
        simp only [K8]

/-! ## 5. The scalar at FS's parameters -/

/-- **The cube tail scalar**, proved: a drop-in replacement for the `sorry`-carrying
`Work.BoseFixB1B.symACube_tail_scalar` (same statement, name `symACube_tail_scalar` in the
`Work.BoseFixB1C` namespace). -/
theorem symACube_tail_scalar {v : E3 → ℝ} :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      Work.BoseFixB1S.symACube (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M 1
          (Submission.BoseGases.fsKinCoeff
            ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)) 0
        * (Submission.BoseGases.chiSupAbs) ^ 2
      ≤ (Work.BoseBox.bValue / 4) * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 := by
  obtain ⟨C, hC0, hdec48⟩ := profHatCube_decay 47 48 (by norm_num)
  have hb4 : 0 < Work.BoseBox.bValue / 4 := by norm_num [Work.BoseBox.bValue]
  have hchi : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
  set Pi0 : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * 2 ^ 84 * C ^ 2 * K8
      * Submission.BoseGases.chiSupAbs ^ 2 / (Work.BoseBox.bValue / 4) with hPi0def
  have hK8 : 0 ≤ K8 := K8_nonneg
  have hPi0nn : 0 ≤ Pi0 := by
    rw [hPi0def]
    refine div_nonneg ?_ hb4.le
    have h1 : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ * 2 ^ 84 := by positivity
    have h2 : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ * 2 ^ 84 * C ^ 2 := mul_nonneg h1 (sq_nonneg C)
    have h3 : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ * 2 ^ 84 * C ^ 2 * K8 := mul_nonneg h2 hK8
    exact mul_nonneg h3 (sq_nonneg _)
  refine ⟨(1 / (Pi0 + 1)) ^ (323 / 72 : ℝ), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro μ hAdm
  have hμ : 0 < μ := hAdm.1
  have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  set t : ℝ := μ * (_root_.BoseGases.a v) ^ 3 with htdef
  have ht0 : 0 < t := by rw [htdef]; exact mul_pos hμ (pow_pos ha 3)
  have htle : t ≤ (1 / (Pi0 + 1)) ^ (323 / 72 : ℝ) := by
    rw [htdef]; exact hAdm.2.1
  have hsi : 0 < 1 / (Pi0 + 1) := by positivity
  have hM48 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M = 48 := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by omega
  have hdec : ∀ p : E3,
      |Work.BoseFixB1S.profHatCube (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M p|
        ≤ C / (1 + ‖p‖) ^ 47 := by
    intro p
    rw [hM48]
    exact hdec48 p
  -- `s = t^{1/323}` and `d = t^{6/323} = s^6`
  have hs_eq : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s = t ^ (1 / 323 : ℝ) := by
    simp only [htdef, Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  have hd_eq : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d = t ^ (6 / 323 : ℝ) := by
    simp only [htdef, Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  have hd6 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 6 := by
    rw [hs_eq, hd_eq,
      show ((t ^ (1 / 323 : ℝ)) ^ 6) = (t ^ (1 / 323 : ℝ)) ^ (6 : ℝ) from
        (Real.rpow_natCast _ 6).symm]
    rw [← Real.rpow_mul (le_of_lt ht0) (1 / 323) 6]
    norm_num
  have hspos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s :=
    Work.BoseFixB1.adm_s_pos hAdm
  -- `s ≤ (1/(Pi0+1))^{1/72}`
  have hsle : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ≤ (1 / (Pi0 + 1)) ^ (1 / 72 : ℝ) := by
    rw [hs_eq]
    have h := Real.rpow_le_rpow (le_of_lt ht0) htle (by norm_num : (0 : ℝ) ≤ 1 / 323)
    rwa [← Real.rpow_mul hsi.le (323 / 72) (1 / 323),
      show (323 / 72 : ℝ) * (1 / 323) = 1 / 72 by norm_num] at h
  -- `s^72 · Pi0 ≤ 1`
  have hs72 : Pi0 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 72 ≤ 1 := by
    have hroot : ((1 / (Pi0 + 1)) ^ (1 / 72 : ℝ)) ^ 72 = 1 / (Pi0 + 1) := by
      rw [show ((1 / (Pi0 + 1)) ^ (1 / 72 : ℝ)) ^ 72
            = ((1 / (Pi0 + 1)) ^ (1 / 72 : ℝ)) ^ (72 : ℝ) from (Real.rpow_natCast _ 72).symm]
      rw [← Real.rpow_mul hsi.le]
      norm_num
    have h1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 72
        ≤ ((1 / (Pi0 + 1)) ^ (1 / 72 : ℝ)) ^ 72 :=
      pow_le_pow_left₀ hspos.le hsle 72
    have h2 : Pi0 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 72
        ≤ (1 / (Pi0 + 1)) * Pi0 :=
      calc Pi0 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 72
          ≤ Pi0 * (1 / (Pi0 + 1)) :=
            mul_le_mul_of_nonneg_left (h1.trans hroot.le) hPi0nn
        _ = (1 / (Pi0 + 1)) * Pi0 := mul_comm _ _
    refine h2.trans ?_
    rw [one_div, inv_mul_eq_div, div_le_one (by positivity : (0 : ℝ) < Pi0 + 1)]
    linarith
  -- the integral bound
  have hint := symACube_fsKinCoeff_integral_le
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M hC0
    (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s))
    hdec
  -- unfold the symbol
  have hsym : Work.BoseFixB1S.symACube (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M 1
      (Submission.BoseGases.fsKinCoeff
        ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)) 0
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, Submission.BoseGases.fsKinCoeff
          ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹) ‖p‖
          * (Work.BoseFixB1S.profHatCube (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M p) ^ 2 := by
    rw [Work.BoseFixB1S.symACube]
    simp only [inv_one, one_smul, zero_add]
  -- the coefficient identity `(c^84)⁻¹ = 2^84 s^84`
  have hc84 : (((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹) ^ 84)⁻¹
      = 2 ^ 84 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 84 := by
    rw [inv_pow, inv_inv, mul_pow]
  -- the arithmetic identity
  have harith : ((2 * Real.pi) ^ 3)⁻¹ * (2 ^ 84
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 84 * C ^ 2 * K8)
        * Submission.BoseGases.chiSupAbs ^ 2
      = (Work.BoseBox.bValue / 4)
        * (Pi0 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 84) := by
    have hb4ne : Work.BoseBox.bValue / 4 ≠ 0 := ne_of_gt hb4
    have hcancel : Pi0 * (Work.BoseBox.bValue / 4)
        = ((2 * Real.pi) ^ 3)⁻¹ * 2 ^ 84 * C ^ 2 * K8
          * Submission.BoseGases.chiSupAbs ^ 2 := by
      rw [hPi0def]
      exact div_mul_cancel₀ _ hb4ne
    rw [show (Work.BoseBox.bValue / 4)
          * (Pi0 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 84)
        = (Pi0 * (Work.BoseBox.bValue / 4))
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 84 from by ring,
      hcancel]
    ring
  have hstep : (Work.BoseBox.bValue / 4)
      * (Pi0 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 84)
      ≤ (Work.BoseBox.bValue / 4)
        * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 6) ^ 2) := by
    have hs12 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 12 :=
      pow_nonneg hspos.le 12
    have h84 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 84
        = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 72
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 12 := by
      rw [← pow_add]
    have h62 : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 6) ^ 2
        = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 12 := by
      rw [← pow_mul]
    have hle : Pi0 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 84
        ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 12 := by
      rw [h84, ← mul_assoc]
      calc Pi0 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 72
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 12
          ≤ 1 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 12 :=
            mul_le_mul_of_nonneg_right hs72 hs12
        _ = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 12 := one_mul _
    rw [h62]
    exact mul_le_mul_of_nonneg_left hle hb4.le
  calc Work.BoseFixB1S.symACube (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M 1
        (Submission.BoseGases.fsKinCoeff
          ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)) 0
        * (Submission.BoseGases.chiSupAbs) ^ 2
      = (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, Submission.BoseGases.fsKinCoeff
          ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹) ‖p‖
          * (Work.BoseFixB1S.profHatCube (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M p) ^ 2))
        * (Submission.BoseGases.chiSupAbs) ^ 2 := by rw [hsym]
    _ ≤ (((2 * Real.pi) ^ 3)⁻¹ * ((((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹) ^ 84)⁻¹
          * C ^ 2 * K8)) * (Submission.BoseGases.chiSupAbs) ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left hint (by positivity)
    _ = ((2 * Real.pi) ^ 3)⁻¹ * (2 ^ 84
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 84 * C ^ 2 * K8)
          * Submission.BoseGases.chiSupAbs ^ 2 := by rw [hc84]
    _ = (Work.BoseBox.bValue / 4)
        * (Pi0 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 84) := harith
    _ ≤ (Work.BoseBox.bValue / 4)
        * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 6) ^ 2 := hstep
    _ = (Work.BoseBox.bValue / 4) * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 := by
        rw [hd6]

end Work.BoseFixB1C
