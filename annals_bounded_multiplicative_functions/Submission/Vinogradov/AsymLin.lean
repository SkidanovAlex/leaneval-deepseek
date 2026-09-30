/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymExpCrude
import Submission.Vinogradov.AsymRec
import Submission.Vinogradov.DecLinBridge
import Submission.Vinogradov.Section4Exp
import Submission.Vinogradov.AsymRecIneq
import Submission.Commons.Analysis.Real.rpow_two_nat_sub_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ §4: Step 3 — the upper bound `A_l(b) ≤ c(b)·η` from the linear exponent

This module is the `asymDec_of_linExpSet` brick of the exponent bootstrap: for every exponent
`e ∈ linExpSet k` of the *linear* `ℓ²`-decoupling and every small `b > 0`, the asymmetric bilinear
exponent at split `l` is at most the Hölder combination

  `c(b) · e`,  `c(b) = (1 − ρ·b)·(p_l/p_k) + (1 − b)·((p_k − p_l)/p_k)`,  `ρ = asymRatio k l`,

i.e. `c(b)·e ∈ AsymExpSet k hk l b`.  This is GLYZ (4.5) in exponent form.

The two ingredients are:

* `asymDec_holder_reduce` — Hölder in the space variable together with the pointwise weighted
  Hölder inequality `convPow_holder_pow`, which reduces `asymLHS` to
  `uncConst² · ‖F_I‖_{p_k}^{p_l} · ‖F_J‖_{p_k}^{p_k−p_l}`;
* `DecLinBridge.lpNorm_block_le` — the localised linear decoupling of each block, which bounds
  `‖F_I‖_{p_k}` by `C₁ · ℓ²` with `C₁ = ofReal (K (2^{N−m₁})^e)`.

The block levels are `m₁ = ⌊ρbN⌋` and `m₂ = ⌊bN⌋`; the floor discrepancies contribute
`2^{N−m_i} ≤ 2·2^{N(1−c_i)}` with `c₁ = ρb`, `c₂ = b` (the commons lemma
`Commons.Analysis.Real.rpow_two_nat_sub_le`), and hence the exponent
`(1−ρb)·(p_l/p_k)·e + (1−b)·((p_k−p_l)/p_k)·e = c(b)·e`.

The module is not on the comparator chain; it is imported by `ROADMAP.lean` only.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 16000000

namespace Submission.Vinogradov

/-! ## 1. The Hölder reduction of the asymmetric bilinear functional -/

set_option maxHeartbeats 32000000 in
/-- **The Hölder reduction.**  Hölder in the space variable (exponents `p_k/p_l` and
`p_k/(p_k−p_l)`) together with the pointwise weighted Hölder inequality `convPow_holder_pow` turns
the asymmetric bilinear functional into the product of the two block `L^{p_k}` norms. -/
theorem asymDec_holder_reduce {k l N m m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    (q : Fin (2 ^ m)) (q' : Fin (2 ^ m')) (f : Fin (2 ^ N) → E k → ℂ)
    (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) :
    (∫⁻ x, convPow k (plExp l) (fun x => ∑ i ∈ blkFin N m q, f i x)
          (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x
        * convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
          (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)
      ≤ (uncConst k hk) ^ 2
        * (lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m q, f i x)) ^ (plExp l)
        * (lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m' q', f i x)) ^ (pkExp k - plExp l) := by
  classical
  have hδm : plateHalf m ≠ 0 := by rw [plateHalf]; positivity
  have hδm' : plateHalf m' ≠ 0 := by rw [plateHalf]; positivity
  set FI : E k → ℂ := fun x => ∑ i ∈ blkFin N m q, f i x with hFI
  set FJ : E k → ℂ := fun x => ∑ i ∈ blkFin N m' q', f i x with hFJ
  set ΦI : E k → ℝ≥0∞ := platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) with hΦI
  set ΦJ : E k → ℝ≥0∞ := platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q') with hΦJ
  have hFIm : Measurable FI := Finset.measurable_sum _ (fun i _ => (hf i).continuous.measurable)
  have hFJm : Measurable FJ := Finset.measurable_sum _ (fun i _ => (hf i).continuous.measurable)
  have hΦIm : Measurable ΦI := (continuous_platePhi k hk _ _).measurable
  have hΦJm : Measurable ΦJ := (continuous_platePhi k hk _ _).measurable
  have hKI : ∫⁻ y, ΦI y = uncConst k hk := by
    rw [hΦI]
    exact lintegral_platePhi hk (plateHalf m) (pieceCenter (2 ^ m) q) hδm
  have hKJ : ∫⁻ y, ΦJ y = uncConst k hk := by
    rw [hΦJ]
    exact lintegral_platePhi hk (plateHalf m') (pieceCenter (2 ^ m') q') hδm'
  have hIp : ∫⁻ x, convPow k (pkExp k) FI ΦI x
      = uncConst k hk * (lpNorm k (pE k) FI) ^ (pkExp k) := by
    rw [lintegral_convPow_eq k (pkExp k) hFIm hΦIm, hKI, lintegral_nnnorm_rpow_pk k hk FI hFIm.aestronglyMeasurable]
  have hJp : ∫⁻ x, convPow k (pkExp k) FJ ΦJ x
      = uncConst k hk * (lpNorm k (pE k) FJ) ^ (pkExp k) := by
    rw [lintegral_convPow_eq k (pkExp k) hFJm hΦJm, hKJ, lintegral_nnnorm_rpow_pk k hk FJ hFJm.aestronglyMeasurable]
  set θ : ℝ := plExp l / pkExp k with hθdef
  have hp0 : 0 < pkExp k := pkExp_pos hk
  have hθ0 : 0 < θ := by rw [hθdef]; exact div_pos (plExp_pos hl) hp0
  have hθ1 : θ < 1 := by
    rw [hθdef, div_lt_one hp0]
    exact plExp_lt_pkExp (by omega)
  have hθeq : θ * pkExp k = plExp l := by rw [hθdef]; field_simp
  have hθeq' : (1 - θ) * pkExp k = pkExp k - plExp l := by
    rw [hθdef]; field_simp
  have hptA : ∀ x : E k, convPow k (plExp l) FI ΦI x
      ≤ (convPow k (pkExp k) FI ΦI x) ^ θ * (∫⁻ y, ΦI y) ^ (1 - θ) := by
    intro x
    have h := convPow_holder_pow (k := k) (θ := θ) (p := pkExp k) hθ0 hθ1 hp0 hFIm hΦIm x
    rwa [hθeq] at h
  have hptB : ∀ x : E k, convPow k (pkExp k - plExp l) FJ ΦJ x
      ≤ (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ := by
    intro x
    have h := convPow_holder_pow (k := k) (θ := 1 - θ) (p := pkExp k)
      (by linarith) (by linarith) hp0 hFJm hΦJm x
    rw [hθeq', show 1 - (1 - θ) = θ from by ring] at h
    exact h
  have hpt : ∀ x : E k, convPow k (plExp l) FI ΦI x * convPow k (pkExp k - plExp l) FJ ΦJ x
      ≤ (∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ
        * ((convPow k (pkExp k) FI ΦI x) ^ θ
            * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ)) := by
    intro x
    refine (mul_le_mul' (hptA x) (hptB x)).trans (le_of_eq ?_)
    ring
  have hAc : AEMeasurable (fun x : E k => convPow k (pkExp k) FI ΦI x) volume :=
    (measurable_convPow k _ hFIm hΦIm).aemeasurable
  have hBc : AEMeasurable (fun x : E k => convPow k (pkExp k) FJ ΦJ x) volume :=
    (measurable_convPow k _ hFJm hΦJm).aemeasurable
  have hInt := lintegral_rpow_interp (μ := (volume : Measure (E k))) hθ0 hθ1 hAc hBc
    (measurable_const.aemeasurable : AEMeasurable (fun _ : E k => (1 : ℝ≥0∞)) volume)
  simp only [mul_one] at hInt
  have hmeasc : AEMeasurable (fun x : E k => (convPow k (pkExp k) FI ΦI x) ^ θ
      * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ)) volume :=
    (hAc.pow_const θ).mul (hBc.pow_const (1 - θ))
  have hpull : (∫⁻ x, (∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ
        * ((convPow k (pkExp k) FI ΦI x) ^ θ
            * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ)))
      = ((∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ)
        * ∫⁻ x, (convPow k (pkExp k) FI ΦI x) ^ θ
            * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ) := by
    rw [lintegral_const_mul'' (f := fun x : E k =>
      (convPow k (pkExp k) FI ΦI x) ^ θ * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ))
      (((∫⁻ y, ΦI y) ^ (1 - θ)) * ((∫⁻ y, ΦJ y) ^ θ)) hmeasc]
  have hmain : ((∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ)
        * ((∫⁻ x, convPow k (pkExp k) FI ΦI x) ^ θ
            * (∫⁻ x, convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ))
      = (uncConst k hk) ^ 2 * (lpNorm k (pE k) FI) ^ (plExp l)
          * (lpNorm k (pE k) FJ) ^ (pkExp k - plExp l) := by
    rw [hKI, hKJ, hIp, hJp]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0.le,
      ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ 1 - θ)]
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    rw [show pkExp k * θ = plExp l from by rw [hθdef]; field_simp,
      show pkExp k * (1 - θ) = pkExp k - plExp l from by rw [hθdef]; field_simp]
    have hK1 : uncConst k hk ^ (1 - θ) * uncConst k hk ^ θ = uncConst k hk := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith : (0:ℝ) ≤ 1 - θ) hθ0.le]
      rw [show (1 - θ) + θ = 1 from by ring, ENNReal.rpow_one]
    have hK2 : uncConst k hk ^ θ * uncConst k hk ^ (1 - θ) = uncConst k hk := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hθ0.le (by linarith : (0:ℝ) ≤ 1 - θ)]
      rw [show θ + (1 - θ) = 1 from by ring, ENNReal.rpow_one]
    rw [hK1,
      show uncConst k hk * (uncConst k hk ^ θ * (lpNorm k (pE k) FI) ^ (plExp l)
            * (uncConst k hk ^ (1 - θ) * (lpNorm k (pE k) FJ) ^ (pkExp k - plExp l)))
          = (uncConst k hk ^ θ * uncConst k hk ^ (1 - θ))
            * (uncConst k hk * ((lpNorm k (pE k) FI) ^ (plExp l)
              * (lpNorm k (pE k) FJ) ^ (pkExp k - plExp l))) from by ac_rfl,
      hK2, pow_two]
    ac_rfl
  calc (∫⁻ x, convPow k (plExp l) FI ΦI x * convPow k (pkExp k - plExp l) FJ ΦJ x)
      ≤ ∫⁻ x, (∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ
          * ((convPow k (pkExp k) FI ΦI x) ^ θ
              * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ)) := lintegral_mono hpt
    _ = ((∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ)
          * ∫⁻ x, (convPow k (pkExp k) FI ΦI x) ^ θ
              * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ) := hpull
    _ ≤ ((∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ)
          * ((∫⁻ x, convPow k (pkExp k) FI ΦI x) ^ θ
              * (∫⁻ x, convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ)) :=
        mul_le_mul' le_rfl hInt
    _ = (uncConst k hk) ^ 2 * (lpNorm k (pE k) FI) ^ (plExp l)
          * (lpNorm k (pE k) FJ) ^ (pkExp k - plExp l) := hmain

/-! ## 2. The Hölder coefficient `c(b)` of the step -/

/-- The Hölder coefficient `c(b) = (1 − ρ·b)·(p_l/p_k) + (1 − b)·((p_k − p_l)/p_k)`. -/
noncomputable def linCoef (k l : ℕ) (b : ℝ) : ℝ :=
  (1 - asymRatio k l * b) * (plExp l / pkExp k)
    + (1 - b) * ((pkExp k - plExp l) / pkExp k)

lemma linCoef_nonneg {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1) {b : ℝ}
    (hb : 0 ≤ b) (hρb : asymRatio k l * b ≤ 1) (hb1 : b ≤ 1) :
    0 ≤ linCoef k l b := by
  have hpk : 0 < pkExp k := pkExp_pos hk
  have hsub : 0 ≤ pkExp k - plExp l := pkExp_sub_plExp_nonneg (by omega)
  have h1 : 0 ≤ 1 - asymRatio k l * b := by linarith
  have h2 : 0 ≤ 1 - b := by linarith
  have h3 : 0 ≤ plExp l / pkExp k := div_nonneg (plExp_nonneg l) hpk.le
  have h4 : 0 ≤ (pkExp k - plExp l) / pkExp k := div_nonneg hsub hpk.le
  rw [linCoef]
  exact add_nonneg (mul_nonneg h1 h3) (mul_nonneg h2 h4)

lemma linCoef_mul_pk {k l : ℕ} (hk : 1 ≤ k) (b : ℝ) :
    linCoef k l b * pkExp k
      = (1 - asymRatio k l * b) * plExp l + (1 - b) * (pkExp k - plExp l) := by
  have hpk : pkExp k ≠ 0 := (pkExp_pos hk).ne'
  rw [linCoef]
  field_simp

set_option maxHeartbeats 32000000 in
lemma linCoef_const_bound {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    {e b K U : ℝ} (he : 0 ≤ e) (hb : 0 ≤ b) (hK : 0 < K) (hU : 0 ≤ U)
    (hρb : asymRatio k l * b ≤ 1) (hb1 : b ≤ 1)
    {N m₁ m₂ : ℕ} (hm₁ : asymRatio k l * b * (N : ℝ) ≤ (m₁ : ℝ) + 1)
    (hm₂ : b * (N : ℝ) ≤ (m₂ : ℝ) + 1) :
    U * (K * ((2 : ℝ) ^ (N - m₁)) ^ e) ^ (plExp l)
        * (K * ((2 : ℝ) ^ (N - m₂)) ^ e) ^ (pkExp k - plExp l)
      ≤ U * K ^ (pkExp k) * (2 : ℝ) ^ (e * pkExp k)
          * (2 : ℝ) ^ ((N : ℝ) * (linCoef k l b * e) * pkExp k) := by
  set X₁ := ((2 : ℝ) ^ (N - m₁)) ^ e with hX₁def
  set X₂ := ((2 : ℝ) ^ (N - m₂)) ^ e with hX₂def
  set μ₁ := (N : ℝ) * (1 - asymRatio k l * b) * e with hμ₁def
  set μ₂ := (N : ℝ) * (1 - b) * e with hμ₂def
  have hpk : 0 < pkExp k := pkExp_pos hk
  have hpl : 0 ≤ plExp l := plExp_nonneg l
  have hsub : 0 ≤ pkExp k - plExp l := pkExp_sub_plExp_nonneg (by omega : l ≤ k)
  have hX₁0 : 0 ≤ X₁ := by rw [hX₁def]; positivity
  have hX₂0 : 0 ≤ X₂ := by rw [hX₂def]; positivity
  have hb₁ : X₁ ≤ (2 : ℝ) ^ μ₁ * (2 : ℝ) ^ e := by
    rw [hX₁def, hμ₁def]
    exact Commons.Analysis.Real.rpow_two_nat_sub_le (mul_nonneg (asymRatio_pos' hk hlk).le hb) hρb he hm₁
  have hb₂ : X₂ ≤ (2 : ℝ) ^ μ₂ * (2 : ℝ) ^ e := by
    rw [hX₂def, hμ₂def]
    exact Commons.Analysis.Real.rpow_two_nat_sub_le hb hb1 he hm₂
  have hpow₁ : X₁ ^ (plExp l) ≤ (2 : ℝ) ^ (μ₁ * plExp l + e * plExp l) := by
    have h := Real.rpow_le_rpow hX₁0 hb₁ hpl
    have hmr : ((2:ℝ)^μ₁ * (2:ℝ)^e) ^ (plExp l)
        = (2:ℝ)^(μ₁ * plExp l) * (2:ℝ)^(e * plExp l) := by
      rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ (2:ℝ)^μ₁)
        (by positivity : (0:ℝ) ≤ (2:ℝ)^e)]
      congr 1
      · rw [← Real.rpow_mul (x := 2) (by norm_num : (0:ℝ) ≤ 2) μ₁ (plExp l)]
      · rw [← Real.rpow_mul (x := 2) (by norm_num : (0:ℝ) ≤ 2) e (plExp l)]
    have hcomb : (2:ℝ)^(μ₁ * plExp l) * (2:ℝ)^(e * plExp l)
        = (2:ℝ)^(μ₁ * plExp l + e * plExp l) :=
      (Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _).symm
    calc X₁ ^ (plExp l) ≤ ((2:ℝ)^μ₁ * (2:ℝ)^e) ^ (plExp l) := h
      _ = (2:ℝ)^(μ₁ * plExp l) * (2:ℝ)^(e * plExp l) := hmr
      _ = (2:ℝ)^(μ₁ * plExp l + e * plExp l) := hcomb
  have hpow₂ : X₂ ^ (pkExp k - plExp l)
      ≤ (2 : ℝ) ^ (μ₂ * (pkExp k - plExp l) + e * (pkExp k - plExp l)) := by
    have h := Real.rpow_le_rpow hX₂0 hb₂ hsub
    have hmr : ((2:ℝ)^μ₂ * (2:ℝ)^e) ^ (pkExp k - plExp l)
        = (2:ℝ)^(μ₂ * (pkExp k - plExp l)) * (2:ℝ)^(e * (pkExp k - plExp l)) := by
      rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ (2:ℝ)^μ₂)
        (by positivity : (0:ℝ) ≤ (2:ℝ)^e)]
      congr 1
      · rw [← Real.rpow_mul (x := 2) (by norm_num : (0:ℝ) ≤ 2) μ₂ (pkExp k - plExp l)]
      · rw [← Real.rpow_mul (x := 2) (by norm_num : (0:ℝ) ≤ 2) e (pkExp k - plExp l)]
    have hcomb : (2:ℝ)^(μ₂ * (pkExp k - plExp l)) * (2:ℝ)^(e * (pkExp k - plExp l))
        = (2:ℝ)^(μ₂ * (pkExp k - plExp l) + e * (pkExp k - plExp l)) :=
      (Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _).symm
    calc X₂ ^ (pkExp k - plExp l) ≤ ((2:ℝ)^μ₂ * (2:ℝ)^e) ^ (pkExp k - plExp l) := h
      _ = (2:ℝ)^(μ₂ * (pkExp k - plExp l)) * (2:ℝ)^(e * (pkExp k - plExp l)) := hmr
      _ = (2:ℝ)^(μ₂ * (pkExp k - plExp l) + e * (pkExp k - plExp l)) := hcomb
  have hKsum : K ^ (plExp l) * K ^ (pkExp k - plExp l) = K ^ (pkExp k) := by
    rw [← Real.rpow_add hK, show plExp l + (pkExp k - plExp l) = pkExp k from by ring]
  have hkey : (N : ℝ) * (linCoef k l b * e) * pkExp k
      = (N : ℝ) * ((1 - asymRatio k l * b) * plExp l + (1 - b) * (pkExp k - plExp l)) * e := by
    rw [show (N : ℝ) * (linCoef k l b * e) * pkExp k
          = (N : ℝ) * e * (linCoef k l b * pkExp k) from by ring,
      linCoef_mul_pk (k := k) (l := l) hk b]
    ring
  have hexp : μ₁ * plExp l + e * plExp l
        + (μ₂ * (pkExp k - plExp l) + e * (pkExp k - plExp l))
      = e * pkExp k + (N : ℝ) * (linCoef k l b * e) * pkExp k := by
    rw [hμ₁def, hμ₂def, hkey]
    ring
  calc U * (K * X₁) ^ (plExp l) * (K * X₂) ^ (pkExp k - plExp l)
      = U * K ^ (pkExp k) * (X₁ ^ (plExp l) * X₂ ^ (pkExp k - plExp l)) := by
        rw [Real.mul_rpow hK.le hX₁0, Real.mul_rpow hK.le hX₂0, ← hKsum]; ring
    _ ≤ U * K ^ (pkExp k) * ((2 : ℝ) ^ (μ₁ * plExp l + e * plExp l)
            * (2 : ℝ) ^ (μ₂ * (pkExp k - plExp l) + e * (pkExp k - plExp l))) := by
        have hinner : X₁ ^ (plExp l) * X₂ ^ (pkExp k - plExp l)
            ≤ (2 : ℝ) ^ (μ₁ * plExp l + e * plExp l)
              * (2 : ℝ) ^ (μ₂ * (pkExp k - plExp l) + e * (pkExp k - plExp l)) :=
          calc X₁ ^ (plExp l) * X₂ ^ (pkExp k - plExp l)
              ≤ (2 : ℝ) ^ (μ₁ * plExp l + e * plExp l) * X₂ ^ (pkExp k - plExp l) :=
                mul_le_mul_of_nonneg_right hpow₁ (by positivity)
            _ ≤ (2 : ℝ) ^ (μ₁ * plExp l + e * plExp l)
                  * (2 : ℝ) ^ (μ₂ * (pkExp k - plExp l) + e * (pkExp k - plExp l)) :=
                mul_le_mul_of_nonneg_left hpow₂ (by positivity)
        exact mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = U * K ^ (pkExp k) * ((2 : ℝ) ^ (e * pkExp k)
            * (2 : ℝ) ^ ((N : ℝ) * (linCoef k l b * e) * pkExp k)) := by
        have hAB : (2 : ℝ) ^ (μ₁ * plExp l + e * plExp l)
              * (2 : ℝ) ^ (μ₂ * (pkExp k - plExp l) + e * (pkExp k - plExp l))
            = (2 : ℝ) ^ (e * pkExp k)
              * (2 : ℝ) ^ ((N : ℝ) * (linCoef k l b * e) * pkExp k) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          rw [hexp]
          rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        rw [hAB]
    _ = U * K ^ (pkExp k) * (2 : ℝ) ^ (e * pkExp k)
          * (2 : ℝ) ^ ((N : ℝ) * (linCoef k l b * e) * pkExp k) := by ring


set_option maxHeartbeats 32000000 in
/-- **GLYZ (4.5) in exponent form.**  For every exponent `e` of the linear `ℓ²`-decoupling and
every small `b > 0`, the Hölder coefficient `c(b)·e` belongs to the asymmetric exponent set. -/
theorem asymDec_of_linExpSet {k : ℕ} (hk : 1 ≤ k) {l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    {e : ℝ} (he : e ∈ linExpSet k) {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ b₀ k) :
    linCoef k l b * e ∈ AsymExpSet k hk l b := by
  classical
  obtain ⟨he0, K, hK, hD⟩ := he
  have hb0 : 0 ≤ b := hb.le
  have hb1 : b ≤ 1 := le_trans hb₁ (b₀_le_one k)
  have hlk' : l ≤ k := by omega
  have hρb : asymRatio k l * b ≤ 1 := asymRatio_mul_b_le_one hk hl hlk' hb0 hb₁
  have hpk : 0 < pkExp k := pkExp_pos hk
  have hpl : 0 ≤ plExp l := plExp_nonneg l
  have hsub : 0 ≤ pkExp k - plExp l := pkExp_sub_plExp_nonneg hlk'
  have h2pos : 0 < (2 : ℝ) := by norm_num
  have hone : (1 : ℕ) ≤ 2 := by norm_num
  have hne : (uncConst k hk) ^ 2 ≠ ⊤ := by
    rw [pow_two]
    exact ENNReal.mul_ne_top (uncConst_ne_top k hk) (uncConst_ne_top k hk)
  set U : ℝ := ((uncConst k hk) ^ 2).toReal + 1 with hUdef
  have hU1 : 1 ≤ U := by
    rw [hUdef]; have := ENNReal.toReal_nonneg (a := (uncConst k hk) ^ 2); linarith
  have hU0 : 0 ≤ U := le_trans zero_le_one hU1
  have hUpos : 0 < U := lt_of_lt_of_le one_pos hU1
  have hUeq : (uncConst k hk) ^ 2 ≤ ENNReal.ofReal U := by
    have h1 : (uncConst k hk) ^ 2 = ENNReal.ofReal (((uncConst k hk) ^ 2).toReal) :=
      (ENNReal.ofReal_toReal hne).symm
    rw [h1, hUdef]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  set K' : ℝ := (U * K ^ (pkExp k) * (2 : ℝ) ^ (e * pkExp k)) ^ (1 / pkExp k) with hK'def
  have hKeq : K' ^ (pkExp k) = U * K ^ (pkExp k) * (2 : ℝ) ^ (e * pkExp k) := by
    rw [hK'def, ← Real.rpow_mul (mul_nonneg (mul_nonneg hU0 (le_of_lt (Real.rpow_pos_of_pos hK _)))
      (le_of_lt (Real.rpow_pos_of_pos h2pos _))) (1 / pkExp k) (pkExp k), one_div,
      inv_mul_cancel₀ hpk.ne', Real.rpow_one]
  have hK'pos : 0 < K' := by
    rw [hK'def]
    exact Real.rpow_pos_of_pos
      (mul_pos (mul_pos hUpos (Real.rpow_pos_of_pos hK _))
        (Real.rpow_pos_of_pos h2pos _)) _
  refine ⟨mul_nonneg (linCoef_nonneg hk hl hlk hb0 hρb hb1) he0, K', hK'pos, 1, fun N hN => ?_⟩
  rw [asymDec_iff]
  intro q q' hsep f hf
  let m₁ : ℕ := lvlOf (asymRatio k l * b) N
  let m₂ : ℕ := lvlOf b N
  have hpow2₁ : 1 ≤ 2 ^ (N - m₁) := by
    have h : 0 < 2 ^ (N - m₁) := pow_pos (by norm_num) _
    omega
  have hpow2₂ : 1 ≤ 2 ^ (N - m₂) := by
    have h : 0 < 2 ^ (N - m₂) := pow_pos (by norm_num) _
    omega
  have hm₁N : m₁ ≤ N :=
    lvlOf_le_of_mul_le (by
      have := mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg N)
      simpa using this)
  have hm₂N : m₂ ≤ N :=
    lvlOf_le_of_mul_le (by
      have := mul_le_mul_of_nonneg_right hb1 (Nat.cast_nonneg N)
      simpa using this)
  have hm₁' : asymRatio k l * b * (N : ℝ) ≤ (m₁ : ℝ) + 1 := by
    have h := lvlOf_lt_of_lt (c := asymRatio k l * b) (N := N)
    have h2 : (m₁ : ℝ) = ((lvlOf (asymRatio k l * b) N : ℕ) : ℝ) := rfl
    rw [h2]; linarith
  have hm₂' : b * (N : ℝ) ≤ (m₂ : ℝ) + 1 := by
    have h := lvlOf_lt_of_lt (c := b) (N := N)
    have h2 : (m₂ : ℝ) = ((lvlOf b N : ℕ) : ℝ) := rfl
    rw [h2]; linarith
  have hD₁ : DecLinScale k (2 ^ (N - m₁)) 1
      (ENNReal.ofReal (K * (((2 ^ (N - m₁) : ℕ)) : ℝ) ^ e)) :=
    DecLinScale_lam_le (by positivity) (by norm_num) (by norm_num)
      (hD (2 ^ (N - m₁)) hpow2₁)
  have hD₂ : DecLinScale k (2 ^ (N - m₂)) 1
      (ENNReal.ofReal (K * (((2 ^ (N - m₂) : ℕ)) : ℝ) ^ e)) :=
    DecLinScale_lam_le (by positivity) (by norm_num) (by norm_num)
      (hD (2 ^ (N - m₂)) hpow2₂)
  have hblk₁ := lpNorm_block_le hk hm₁N q hD₁ hf
  have hblk₂ := lpNorm_block_le hk hm₂N q' hD₂ hf
  let C₁ : ℝ≥0∞ := ENNReal.ofReal (K * (((2 ^ (N - m₁) : ℕ)) : ℝ) ^ e)
  let C₂ : ℝ≥0∞ := ENNReal.ofReal (K * (((2 ^ (N - m₂) : ℕ)) : ℝ) ^ e)
  let LI : ℝ≥0∞ := l2Of (blkFin N m₁ q) (fun i => lpNorm k (pE k) (f i))
  let LJ : ℝ≥0∞ := l2Of (blkFin N m₂ q') (fun i => lpNorm k (pE k) (f i))
  let Q : ℝ≥0∞ := (ENNReal.ofReal (K' * (2 : ℝ) ^ ((N : ℝ) * (linCoef k l b * e)))) ^ (pkExp k)
  have hb₁' : lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₁ q, f i x) ≤ C₁ * LI := hblk₁
  have hb₂' : lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x) ≤ C₂ * LJ := hblk₂
  have hI : (lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₁ q, f i x)) ^ (plExp l)
      ≤ C₁ ^ (plExp l) * LI ^ (plExp l) :=
    (ENNReal.rpow_le_rpow hb₁' hpl).trans (le_of_eq (ENNReal.mul_rpow_of_nonneg _ _ hpl))
  have hJ : (lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)) ^ (pkExp k - plExp l)
      ≤ C₂ ^ (pkExp k - plExp l) * LJ ^ (pkExp k - plExp l) :=
    (ENNReal.rpow_le_rpow hb₂' hsub).trans (le_of_eq (ENNReal.mul_rpow_of_nonneg _ _ hsub))
  have hconst : (uncConst k hk) ^ 2 * C₁ ^ (plExp l) * C₂ ^ (pkExp k - plExp l) ≤ Q := by
    have hcast₁ : (((2 ^ (N - m₁) : ℕ)) : ℝ) = (2 : ℝ) ^ (N - m₁) := by
      rw [Nat.cast_pow]; norm_num
    have hcast₂ : (((2 ^ (N - m₂) : ℕ)) : ℝ) = (2 : ℝ) ^ (N - m₂) := by
      rw [Nat.cast_pow]; norm_num
    have key : (uncConst k hk) ^ 2
        * (ENNReal.ofReal (K * (((2 ^ (N - m₁) : ℕ)) : ℝ) ^ e)) ^ (plExp l)
        * (ENNReal.ofReal (K * (((2 ^ (N - m₂) : ℕ)) : ℝ) ^ e)) ^ (pkExp k - plExp l)
        ≤ (ENNReal.ofReal (K' * (2 : ℝ) ^ ((N : ℝ) * (linCoef k l b * e)))) ^ (pkExp k) := by
      rw [hcast₁, hcast₂]
      have hC₁eq : ENNReal.ofReal (K * ((2 : ℝ) ^ (N - m₁)) ^ e) ^ (plExp l)
          = ENNReal.ofReal ((K * ((2 : ℝ) ^ (N - m₁)) ^ e) ^ (plExp l)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hpl
      have hC₂eq : ENNReal.ofReal (K * ((2 : ℝ) ^ (N - m₂)) ^ e) ^ (pkExp k - plExp l)
          = ENNReal.ofReal ((K * ((2 : ℝ) ^ (N - m₂)) ^ e) ^ (pkExp k - plExp l)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hsub
      have hQeq : (ENNReal.ofReal (K' * (2 : ℝ) ^ ((N : ℝ) * (linCoef k l b * e)))) ^ (pkExp k)
          = ENNReal.ofReal (U * K ^ (pkExp k) * (2 : ℝ) ^ (e * pkExp k)
              * (2 : ℝ) ^ ((N : ℝ) * (linCoef k l b * e) * pkExp k)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (pkExp_nonneg k),
          Real.mul_rpow (le_of_lt hK'pos)
            (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * (linCoef k l b * e))),
          hKeq,
          ← Real.rpow_mul (x := 2) (by norm_num : (0 : ℝ) ≤ 2)
            ((N : ℝ) * (linCoef k l b * e)) (pkExp k)]
      rw [hC₁eq, hC₂eq, hQeq]
      refine le_trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hUeq (by positivity)) (by positivity)) ?_
      have hX0 : 0 ≤ (K * ((2 : ℝ) ^ (N - m₁)) ^ e) ^ (plExp l) := by positivity
      have h1 : ENNReal.ofReal U * ENNReal.ofReal ((K * ((2 : ℝ) ^ (N - m₁)) ^ e) ^ (plExp l))
          = ENNReal.ofReal (U * (K * ((2 : ℝ) ^ (N - m₁)) ^ e) ^ (plExp l)) :=
        (ENNReal.ofReal_mul hU0).symm
      have h2 : ENNReal.ofReal (U * (K * ((2 : ℝ) ^ (N - m₁)) ^ e) ^ (plExp l))
          * ENNReal.ofReal ((K * ((2 : ℝ) ^ (N - m₂)) ^ e) ^ (pkExp k - plExp l))
          = ENNReal.ofReal (U * (K * ((2 : ℝ) ^ (N - m₁)) ^ e) ^ (plExp l)
              * (K * ((2 : ℝ) ^ (N - m₂)) ^ e) ^ (pkExp k - plExp l)) :=
        (ENNReal.ofReal_mul (mul_nonneg hU0 hX0)).symm
      rw [h1, h2]
      exact ENNReal.ofReal_le_ofReal
        (linCoef_const_bound hk hl hlk he0 hb0 hK hU0 hρb hb1 hm₁' hm₂')
    exact key
  have hred : asymLHS k hk l N m₁ m₂ q q' f
      ≤ (uncConst k hk) ^ 2
        * (lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₁ q, f i x)) ^ (plExp l)
        * (lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)) ^ (pkExp k - plExp l) :=
    asymDec_holder_reduce hk hl hlk q q' f hf
  have hmid1 : (uncConst k hk) ^ 2
        * (lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₁ q, f i x)) ^ (plExp l)
        * (lpNorm k (pE k) (fun x => ∑ i ∈ blkFin N m₂ q', f i x)) ^ (pkExp k - plExp l)
      ≤ (uncConst k hk) ^ 2 * (C₁ ^ (plExp l) * LI ^ (plExp l))
        * (C₂ ^ (pkExp k - plExp l) * LJ ^ (pkExp k - plExp l)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hI (by positivity)) hJ (by positivity) (by positivity)
  have hmid2 : (uncConst k hk) ^ 2 * (C₁ ^ (plExp l) * LI ^ (plExp l))
        * (C₂ ^ (pkExp k - plExp l) * LJ ^ (pkExp k - plExp l))
      ≤ Q * LI ^ (plExp l) * LJ ^ (pkExp k - plExp l) := by
    rw [show (uncConst k hk) ^ 2 * (C₁ ^ (plExp l) * LI ^ (plExp l))
          * (C₂ ^ (pkExp k - plExp l) * LJ ^ (pkExp k - plExp l))
        = ((uncConst k hk) ^ 2 * C₁ ^ (plExp l) * C₂ ^ (pkExp k - plExp l))
          * LI ^ (plExp l) * LJ ^ (pkExp k - plExp l) from by ac_rfl]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst (by positivity)) (by positivity)
  exact hred.trans (hmid1.trans hmid2)


/-! ## 3. GLYZ (4.5) at `e = etaLin k` -/

/-- **GLYZ (4.5) at `e = etaLin k`.** -/
theorem Aexp_le_linCoef_mul_etaLin {k : ℕ} (hk : 1 ≤ k) {l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ b₀ k) :
    Aexp k hk l b ≤ linCoef k l b * etaLin k := by
  have hb0 : 0 ≤ b := hb.le
  have hb1 : b ≤ 1 := le_trans hb₁ (b₀_le_one k)
  have hρb : asymRatio k l * b ≤ 1 := asymRatio_mul_b_le_one hk hl (by omega) hb0 hb₁
  have hc0 : 0 ≤ linCoef k l b := linCoef_nonneg hk hl hlk hb0 hρb hb1
  rcases eq_or_lt_of_le hc0 with h0 | hpos
  · obtain ⟨e, he⟩ := linExpSet_nonempty k hk
    have hmem := asymDec_of_linExpSet hk hl hlk he hb hb₁
    have hz : linCoef k l b * e = 0 := by rw [← h0, zero_mul]
    rw [hz] at hmem
    have h : Aexp k hk l b ≤ 0 := Aexp_le_of_mem hmem
    rw [← h0, zero_mul]
    exact h
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hlt : sInf (linExpSet k) < sInf (linExpSet k) + δ / linCoef k l b := by
      have := div_pos hδ hpos
      linarith
    have hlt' : sInf (linExpSet k) < etaLin k + δ / linCoef k l b := hlt
    obtain ⟨e, he, hee⟩ :=
      (csInf_lt_iff (bddBelow_linExpSet k) (linExpSet_nonempty k hk)).mp hlt'
    have h1 : Aexp k hk l b ≤ linCoef k l b * e :=
      Aexp_le_of_mem (asymDec_of_linExpSet hk hl hlk he hb hb₁)
    have h2 : linCoef k l b * e ≤ linCoef k l b * etaLin k + δ := by
      have hmul := mul_lt_mul_of_pos_left hee hpos
      have hsplit : linCoef k l b * (etaLin k + δ / linCoef k l b)
          = linCoef k l b * etaLin k + δ := by
        rw [mul_add, mul_div_cancel₀ δ (ne_of_gt hpos)]
      linarith [hmul, hsplit ▸ hmul]
    linarith


end Submission.Vinogradov
