/-
# The degenerate modified bump `φ_{N,t,j}` at the bottom scale vanishes

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Ann. of Math. **195** (2022), §6, use the modified bumps
`φ_{N,t,j}(ξ) = (2^{-k}Nξ)^j φ_{N,t}(ξ)`, `φ̃_{N,t,j}(ξ) = (2^{-dk}N^dξ)^j φ̃_{N,t}(ξ)`
(identities `(pntj)`, `(tpntj)`) in their integration by parts.  At the *bottom* scale `k = 0`
with `j ≤ -2`, the factor `(Nξ)^j` has a non-integrable singularity of order `≥ 2` at the
frequency origin, so the periodisation `periodize φ` is *not* integrable on the frequency circle
`ℝ/ℤ`; since the IW kernel `iwKernel m j` is a Bochner integral of `fourier (-j) · m`, and the
Bochner integral of a non-integrable function is `0` (`MeasureTheory.integral_undef`), *every*
Fourier coefficient of the symbol vanishes.  Consequently the Ionescu--Wainger multiplier
`T^{≤l}_{φ_{N,t,j}} = iwConv (iwArithFreqs ρ l) (periodize φ_{N,t,j})` is the zero operator.

This module proves that statement, `varphiNtj_Tle_eq_zero`:

  `Tle ρ l (varphiNtj N 0 j t) f = 0` for every `j ≤ -2`, `t` and every `f : ℤ → ℂ`.

## Structure

* `int_coe_circ_eq_zero`, `norm_coe_le_abs`, `norm_coe_le_abs_fract`, `dist_zero_le_abs_rep` —
  elementary facts about the circle `ℝ/ℤ` and the canonical representative
  `AddCircle.equivIco 1 0`;
* `periodize_eq_two_terms` — the periodisation of a bump supported in `[-1/2,1/2]` has exactly
  the two terms `φ (fract y)` and `φ (fract y - 1)`;
* `varphiNtj_arc_bounds` — the pointwise behaviour of the bump: support in `|ξ| ≤ 2^{-Log N}`,
  an upper bound `‖φ(ξ)‖ ≤ (Nε)^j` off `|ξ| > ε`, a zero at the origin, and the lower bound
  `(Nx)⁻¹ ≤ ‖φ(x)‖` on `(0, min(2^{-Log N-1}, N⁻¹)]`;
* `lintegral_inv_Ioc_eq_top` — the divergence `∫₀^δ dx/x = ∞`;
* `not_integrable_iwSymbolSet_varphiNtj` — the symbol is not integrable;
* `iwKernel_eq_zero_of_not_integrable` — a non-integrable symbol has zero kernel
  (the `integral_undef` convention);
* `varphiNtj_Tle_eq_zero` — the conclusion.

Note: the companion module `Submission.Work.KMTAreas.A7.iwKernel_not_integrable` (which states
`iwKernel_eq_zero_of_not_integrable` for `FreqCirc`/`circleMeasure` of the `A7` namespace) does not
compile in the current workspace state (`FreqCirc` is not in scope there), so the vanishing of the
kernel is reproved here in the `Work.KMTPlan.A6` namespace.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs
import Submission.Work.KMTAreas.A7.varphiNt_bounds

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger (periodize iwSymbolSet iwArithFreqs circleMeasure
  mem_iwArithFreqs)
open Work.KMTAreas.A7 (varphiNt varphiN norm_ee ee)

/-- The frequency circle `ℝ/ℤ`. -/
abbrev FreqCirc : Type := Work.Analysis.IonescuWainger.Circle

/-! ## Elementary facts about the circle -/

/-- In `ℝ/ℤ`, the class of an integer is `0`. -/
lemma int_coe_circ_eq_zero (n : ℤ) : ((n : ℝ) : FreqCirc) = 0 := by
  have h : ((n : ℝ) : FreqCirc) = ((n • (1 : ℝ) : ℝ) : FreqCirc) := by
    rw [zsmul_eq_mul, mul_one]
  rw [h, AddCircle.coe_zsmul, AddCircle.coe_period (1 : ℝ), zsmul_zero]

/-- In `ℝ/ℤ`, the class of an integer plus a real number: `↑(x + n) = ↑x`. -/
lemma coe_add_int_eq (x : ℝ) (n : ℤ) : ((x + (n : ℝ) : ℝ) : FreqCirc) = (x : FreqCirc) := by
  rw [AddCircle.coe_add, int_coe_circ_eq_zero n, add_zero]

/-- `‖(z : ℝ/ℤ)‖ ≤ |z|`. -/
lemma norm_coe_le_abs (z : ℝ) : ‖(z : FreqCirc)‖ ≤ |z| := by
  rcases lt_or_ge |z| (1 / 2) with h | h
  · rw [show ‖(z : FreqCirc)‖ = |z| from
        (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero (x := z)).mpr (by
          simpa using h.le)]
  · exact (AddCircle.norm_le_half_period (p := (1 : ℝ)) one_ne_zero).trans (by simpa using h)

/-- The norm on `ℝ/ℤ` is bounded by the distance to the integers, computed via `Int.fract`. -/
lemma norm_coe_le_abs_fract (z : ℝ) :
    ‖(z : FreqCirc)‖ ≤ |Int.fract z| ∧ ‖(z : FreqCirc)‖ ≤ |Int.fract z - 1| := by
  have hz : (z : FreqCirc) = ((Int.fract z : ℝ) : FreqCirc) := by
    conv_lhs => rw [← Int.fract_add_floor z]
    rw [AddCircle.coe_add, int_coe_circ_eq_zero ⌊z⌋, add_zero]
  have hz1 : (z : FreqCirc) = ((Int.fract z - 1 : ℝ) : FreqCirc) := by
    have h : Int.fract z - 1 + ((⌊z⌋ : ℝ) + 1) = z := by
      have h0 := Int.fract_add_floor z
      linarith
    conv_lhs => rw [← h]
    rw [AddCircle.coe_add, show (((⌊z⌋ : ℝ) + 1 : ℝ) : FreqCirc) = 0 from by
        rw [show ((⌊z⌋ : ℝ) + 1 : ℝ) = ((⌊z⌋ + 1 : ℤ) : ℝ) by push_cast; ring]
        exact int_coe_circ_eq_zero (⌊z⌋ + 1), add_zero]
  exact ⟨by rw [hz]; exact norm_coe_le_abs _, by rw [hz1]; exact norm_coe_le_abs _⟩

/-- The canonical representative `rep ξ = (AddCircle.equivIco 1 0 ξ).val ∈ [0,1)` of a point of
the circle satisfies `dist ξ 0 ≤ |rep ξ|` and `dist ξ 0 ≤ |rep ξ - 1|`. -/
lemma dist_zero_le_abs_rep (ξ : FreqCirc) :
    dist ξ 0 ≤ |(AddCircle.equivIco (1 : ℝ) 0 ξ).val| ∧
      dist ξ 0 ≤ |(AddCircle.equivIco (1 : ℝ) 0 ξ).val - 1| := by
  set y : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hy
  have hyξ : (y : FreqCirc) = ξ := AddCircle.coe_equivIco
  have hy0 : 0 ≤ y := by rw [hy]; exact (AddCircle.equivIco (1 : ℝ) 0 ξ).2.1
  have hy1 : y < 1 := by rw [hy]; simpa using (AddCircle.equivIco (1 : ℝ) 0 ξ).2.2
  have hfract : Int.fract y = y := Int.fract_eq_self.mpr ⟨hy0, hy1⟩
  obtain ⟨h1, h2⟩ := norm_coe_le_abs_fract y
  rw [hfract] at h1 h2
  rw [hyξ] at h1 h2
  exact ⟨by simpa [dist_eq_norm] using h1, by simpa [dist_eq_norm] using h2⟩


/-! ## The periodisation of a bump supported off `(-1/2, 1/2)` -/

/-- **The periodisation of a bump supported in `[-1/2,1/2]` has two terms.**  With
`rep ξ ∈ [0,1)` the canonical representative of `ξ : ℝ/ℤ`, only the terms `k = 0` and `k = -1` of
the defining series `periodize φ ξ = ∑_k φ (rep ξ + k)` can be nonzero. -/
theorem periodize_eq_two_terms (φ : ℝ → ℂ) (hφ : ∀ x : ℝ, (1 / 2 : ℝ) ≤ |x| → φ x = 0)
    (ξ : FreqCirc) :
    periodize φ ξ = φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val)
      + φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val - 1) := by
  rw [Work.Analysis.IonescuWainger.periodize]
  set y : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hy
  have hy0 : 0 ≤ y := by rw [hy]; exact (AddCircle.equivIco (1 : ℝ) 0 ξ).2.1
  have hy1 : y < 1 := by rw [hy]; simpa using (AddCircle.equivIco (1 : ℝ) 0 ξ).2.2
  rw [tsum_eq_sum (s := ({-1, 0} : Finset ℤ)) ?_]
  · rw [Finset.sum_insert (by simp), Finset.sum_singleton]
    have h1 : y + ((-1 : ℤ) : ℝ) = y - 1 := by push_cast; ring
    have h2 : y + ((0 : ℤ) : ℝ) = y := by push_cast; ring
    rw [h1, h2, add_comm]
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨hk1, hk0⟩ := hk
    refine hφ _ ?_
    have hcases : (1 : ℤ) ≤ k ∨ k ≤ -2 := by omega
    rcases hcases with hcase | hcase
    · have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcase
      have hpos : 0 ≤ y + (k : ℝ) := by linarith
      rw [abs_of_nonneg hpos]
      linarith
    · have hk' : (k : ℝ) ≤ -2 := by exact_mod_cast hcase
      have hneg : y + (k : ℝ) ≤ 0 := by linarith
      rw [abs_of_nonpos hneg]
      linarith

/-! ## Elementary order facts for integer powers -/

/-- For a positive base `≤ 1`, lowering the base raises a non-positive power. -/
lemma zpow_le_zpow_of_pos_of_le_of_nonpos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    {j : ℤ} (hj : j ≤ 0) : a ^ j ≤ b ^ j := by
  have hnj : 0 ≤ -j := by omega
  have h1 : b ^ (-j) ≤ a ^ (-j) := zpow_le_zpow_left₀ hnj hb.le hba
  have h2 : (0 : ℝ) < a ^ (-j) := zpow_pos ha _
  have h3 : (0 : ℝ) < b ^ (-j) := zpow_pos hb _
  have h4 : a ^ j = (a ^ (-j))⁻¹ := by rw [← zpow_neg a (-j), neg_neg]
  have h5 : b ^ j = (b ^ (-j))⁻¹ := by rw [← zpow_neg b (-j), neg_neg]
  rw [h4, h5]
  exact (inv_le_inv₀ h2 h3).mpr h1

/-! ## Pointwise bounds for the degenerate bump -/

/-- The degenerate bump is the `j`-th power of the linear factor times `φ_{N,t}`. -/
lemma varphiNtj_factor (N : ℕ) (j : ℤ) (t : ℝ) (x : ℝ) :
    varphiNtj N 0 j t x = (((N : ℝ) * x : ℝ) : ℂ) ^ j * varphiNt N 0 t x := by
  simp only [varphiNtj, Nat.cast_zero, neg_zero, Real.rpow_zero, one_mul]

/-- The modulated bump is bounded by `1`. -/
lemma norm_varphiNt_zero_le_one (N : ℕ) (t x : ℝ) : ‖varphiNt N 0 t x‖ ≤ 1 := by
  rw [varphiNt, norm_mul, Work.KMTAreas.A7.norm_ee, mul_one]
  simp only [varphiN, ↓reduceIte]
  exact Work.KMTContract.norm_kmtEta_le _

/-- Where the cutoff `η` is `1`, the modulated bump has norm exactly `1`. -/
lemma norm_varphiNt_zero_eq_one (N : ℕ) (t x : ℝ)
    (h : |((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) * x| ≤ 1 / 2) :
    ‖varphiNt N 0 t x‖ = 1 := by
  rw [varphiNt, norm_mul, Work.KMTAreas.A7.norm_ee, mul_one]
  simp only [varphiN, ↓reduceIte]
  rw [Work.KMTContract.kmtEta_one h]
  simp

/-- The norm of the coerced real number `r` in `ℂ`. -/
lemma norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

/-- The support of the modulated bump. -/
lemma varphiNt_zero_support (N : ℕ) (t x : ℝ) (hx : varphiNt N 0 t x ≠ 0) :
    |x| ≤ (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) := by
  simpa using Work.KMTAreas.A7.varphiNt_support N 0 t x hx

/-- Strict support of the degenerate bump: `φ_{N,t,j} x ≠ 0` forces `|x| < 2^{-Log N}`. -/
lemma varphiNtj_zero_support_lt (N : ℕ) (j : ℤ) (t : ℝ) (x : ℝ)
    (hx : varphiNtj N 0 j t x ≠ 0) :
    |x| < (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) := by
  have hNt : varphiNt N 0 t x ≠ 0 := by
    intro h0
    exact hx (by rw [varphiNtj_factor, h0, mul_zero])
  have hη : Work.KMTContract.kmtEta ((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * x) ≠ 0 := by
    intro h0
    exact hNt (by rw [varphiNt, varphiN, if_pos rfl, h0, zero_mul])
  have h1 : ¬ (1 ≤ |(2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * x|) :=
    fun h => hη (Work.KMTContract.kmtEta_zero h)
  have h2 : |(2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * x| < 1 := lt_of_not_ge h1
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)] at h2
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    ← one_div, lt_div_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]
  linarith [h2]

/-- **Pointwise bounds for `φ_{N,t,j}` at the bottom scale `k = 0` with `j ≤ -2`.** -/
theorem varphiNtj_arc_bounds (N : ℕ) (hN : 1 ≤ N) (j : ℤ) (hj : j ≤ -2) (t : ℝ) :
    (varphiNtj N 0 j t 0 = 0) ∧
    (∀ x : ℝ, varphiNtj N 0 j t x ≠ 0 →
      |x| ≤ (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ))) ∧
    (∀ ε x : ℝ, 0 < ε → ε ≤ |x| →
      ‖varphiNtj N 0 j t x‖ ≤ ((N : ℝ) * ε) ^ j) ∧
    (∀ x : ℝ, 0 < x →
      x ≤ min ((2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ) - 1)) ((N : ℝ)⁻¹) →
      (N : ℝ)⁻¹ * x⁻¹ ≤ ‖varphiNtj N 0 j t x‖) := by
  have hjne : j ≠ 0 := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [varphiNtj_factor]
    simp [zero_zpow, hjne]
  · intro x hx
    have h2 : varphiNt N 0 t x ≠ 0 := by
      intro h0
      exact hx (by rw [varphiNtj_factor, h0, mul_zero])
    exact varphiNt_zero_support N t x h2
  · intro ε x hε hεx
    rw [varphiNtj_factor, norm_mul, norm_zpow, norm_ofReal_eq_abs]
    have h1 : |(N : ℝ) * x| = (N : ℝ) * |x| := by rw [abs_mul, abs_of_nonneg hNpos.le]
    rw [h1]
    have h2 : ‖varphiNt N 0 t x‖ ≤ 1 := norm_varphiNt_zero_le_one N t x
    have h3 : (0 : ℝ) < (N : ℝ) * |x| :=
      mul_pos hNpos (lt_of_lt_of_le hε hεx)
    calc ((N : ℝ) * |x|) ^ j * ‖varphiNt N 0 t x‖
        ≤ ((N : ℝ) * |x|) ^ j * 1 :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt (zpow_pos h3 _))
      _ = ((N : ℝ) * |x|) ^ j := mul_one _
      _ ≤ ((N : ℝ) * ε) ^ j :=
          zpow_le_zpow_of_pos_of_le_of_nonpos h3 (mul_pos hNpos hε)
            (mul_le_mul_of_nonneg_left hεx hNpos.le) (by omega)
  · intro x hx0 hxle
    have hxR : x ≤ (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ) - 1) :=
      hxle.trans (min_le_left _ _)
    have hxN : x ≤ (N : ℝ)⁻¹ := hxle.trans (min_le_right _ _)
    have hRpos : (0 : ℝ) < (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hη : |((2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)) * x| ≤ 1 / 2 := by
      have h2 : (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * x
          ≤ (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)
            * (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hxR hRpos.le
      have h3 : (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ)
          * (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ) - 1) = 1 / 2 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        have hexp : (Work.Analysis.EndVar.logN N : ℝ) +
            (-(Work.Analysis.EndVar.logN N : ℝ) - 1) = -1 := by ring
        rw [hexp, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_one]
        norm_num
      have h4 : 0 ≤ (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) * x :=
        mul_nonneg hRpos.le hx0.le
      rw [abs_of_nonneg h4]
      linarith
    have hnorm : ‖varphiNt N 0 t x‖ = 1 := norm_varphiNt_zero_eq_one N t x hη
    rw [varphiNtj_factor, norm_mul, hnorm, mul_one, norm_zpow, norm_ofReal_eq_abs,
      abs_of_nonneg (mul_nonneg hNpos.le hx0.le)]
    have hNx_le_one : (N : ℝ) * x ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hxN hNpos.le
      rwa [mul_inv_cancel₀ (ne_of_gt hNpos)] at h
    have h5 : ((N : ℝ) * x) ^ ((-1 : ℤ)) ≤ ((N : ℝ) * x) ^ j :=
      zpow_le_zpow_right_of_le_one₀ (mul_pos hNpos hx0) hNx_le_one (by omega)
    calc (N : ℝ)⁻¹ * x⁻¹ = ((N : ℝ) * x)⁻¹ := by rw [mul_inv]
      _ = ((N : ℝ) * x) ^ ((-1 : ℤ)) := by norm_num
      _ ≤ ((N : ℝ) * x) ^ j := h5

/-- `∫₀^δ dx/x = ∞`: the harmonic tail is not integrable. -/
theorem lintegral_inv_Ioc_eq_top (δ : ℝ) (hδ : 0 < δ) :
    (¬ MeasureTheory.IntegrableOn (fun x : ℝ => x⁻¹) (Set.Ioc 0 δ) MeasureTheory.volume) ∧
      (∫⁻ x in Set.Ioc 0 δ, ENNReal.ofReal x⁻¹ ∂MeasureTheory.volume = ⊤) := by
  have hnotint : ¬ IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 δ := by
    rw [intervalIntegrable_inv_iff]
    intro h
    rcases h with h | h
    · exact hδ.ne h
    · exact h (by rw [Set.uIcc_of_le hδ.le]; exact ⟨le_refl 0, hδ.le⟩)
  have h1 : ¬ IntegrableOn (fun x : ℝ => x⁻¹) (Set.Ioc 0 δ) volume := by
    intro h
    exact hnotint ((intervalIntegrable_iff (f := fun x : ℝ => x⁻¹) (a := 0) (b := δ)
      (μ := volume)).mpr (by simpa [Set.uIoc_of_le hδ.le] using h))
  refine ⟨h1, ?_⟩
  have hfin : ¬ ((∫⁻ x in Set.Ioc 0 δ, ‖x⁻¹‖ₑ ∂volume) < ⊤) := by
    intro hlt
    refine h1 ⟨(measurable_inv.aestronglyMeasurable).restrict, ?_⟩
    show (∫⁻ x : ℝ, ‖x⁻¹‖ₑ ∂(volume.restrict (Set.Ioc 0 δ))) < ⊤
    exact hlt
  have heq : (∫⁻ x in Set.Ioc 0 δ, ENNReal.ofReal x⁻¹ ∂volume)
      = ∫⁻ x in Set.Ioc 0 δ, ‖x⁻¹‖ₑ ∂volume := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [← ofReal_norm, Real.norm_of_nonneg (inv_nonneg.mpr hx.1.le)]
  rw [heq]
  exact le_antisymm le_top (not_lt.mp hfin)

/-- `0 ∈ (ℚ/ℤ)_{≤l}`. -/
lemma zero_mem_iwArithFreqs_A6 (ρ : ℝ) (l : ℕ) : (0 : FreqCirc) ∈ iwArithFreqs ρ l :=
  mem_iwArithFreqs.mpr ⟨1, Work.Analysis.IonescuWainger.one_mem_iwP ρ l, by simp⟩


/-- The circle `ℝ/ℤ` is `(0,1]` with its Lebesgue measure. -/
lemma measurePreserving_mk_circle :
    MeasurePreserving (fun x : ℝ => (x : FreqCirc)) (volume.restrict (Set.Ioc 0 1)) circleMeasure := by
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = circleMeasure := by
    rw [Work.Analysis.IonescuWainger.circleMeasure, AddCircle.volume_eq_smul_haarAddCircle,
      ENNReal.ofReal_one, one_smul]
  have h := AddCircle.measurePreserving_mk (T := (1 : ℝ)) (t := 0)
  rw [zero_add] at h
  rwa [hvol] at h

/-- The bound on the off-diagonal part of the symbol on the arc. -/
noncomputable def arcRest (N : ℕ) (j : ℤ) (s : Finset FreqCirc) (d : ℝ) : ℝ :=
  ∑ α ∈ s, 2 * ((N : ℝ) * (d / 2)) ^ j

/-- The radius of the arc on which the symbol is bounded below by `(2N a)⁻¹`. -/
noncomputable def arcDelta (N : ℕ) (j : ℤ) (s : Finset FreqCirc) (d : ℝ) : ℝ :=
  min (min (d / 4) (1 / 4))
    (min ((2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ) - 1))
      (min ((N : ℝ)⁻¹) ((2 * arcRest N j s d * (N : ℝ) + 2)⁻¹)))

/-- **The IW symbol of the degenerate bump is not integrable.**

Since `φ_{N,t,j}(ξ) = (Nξ)^j φ_{N,t}(ξ)` with `j ≤ -2`, the periodisation of `φ_{N,t,j}` has a
non-integrable singularity of order `≥ 2` at the frequency origin; the arithmetic translates
`periodize φ (· - α)`, `α ≠ 0`, of the other frequencies are bounded there, so the symbol
`∑_{α ∈ (ℚ/ℤ)_{≤l}} periodize φ (· - α)` is not integrable either. -/
theorem not_integrable_iwSymbolSet_varphiNtj (ρ : ℝ) (l N : ℕ) (hN : 1 ≤ N) (j : ℤ)
    (hj : j ≤ -2) (t : ℝ) :
    ¬ Integrable (iwSymbolSet (iwArithFreqs ρ l) (periodize (varphiNtj N 0 j t)))
      circleMeasure := by
  set A : Finset FreqCirc := iwArithFreqs ρ l with hAdef
  set φ : ℝ → ℂ := varphiNtj N 0 j t with hφdef
  set s : Finset FreqCirc := A.erase (0 : FreqCirc) with hsdef
  obtain ⟨hφ0, hsupp, hupper, hlower⟩ := varphiNtj_arc_bounds N hN j hj t
  rw [← hφdef] at hφ0 hsupp hupper hlower
  have h0A : (0 : FreqCirc) ∈ A := by rw [hAdef]; exact zero_mem_iwArithFreqs_A6 ρ l
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- the bump vanishes off `[-1/2,1/2]`
  have hL1 : (1 : ℤ) ≤ Work.Analysis.EndVar.logN N := by
    rw [Work.Analysis.EndVar.logN]
    exact_mod_cast (Nat.le_log_iff_pow_le (b := 2) (by norm_num) (x := 1) (y := max N 2)
      (by omega)).mpr (by have := le_max_right N 2; simpa using this)
  have hR_le_half : (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_one]
      norm_num
    have hL1' : (1 : ℝ) ≤ (Work.Analysis.EndVar.logN N : ℝ) := by exact_mod_cast hL1
    rw [← h2]
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by linarith)
  have hφhalf : ∀ x : ℝ, (1 / 2 : ℝ) ≤ |x| → φ x = 0 := by
    intro x hx
    by_contra hne
    have h1 : |x| < (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ)) :=
      varphiNtj_zero_support_lt N j t x (by rwa [hφdef] at hne)
    linarith
  -- the separation constant of the off-diagonal frequencies
  set d : ℝ := if h : s.Nonempty then s.inf' h (fun α => dist α (0 : FreqCirc)) else 1 with hddef
  have hdpos : 0 < d := by
    rw [hddef]
    by_cases h : s.Nonempty
    · rw [dif_pos h]
      refine (Finset.lt_inf'_iff h).2 fun α hα => ?_
      have hα' : α ∈ A.erase (0 : FreqCirc) := by rwa [hsdef] at hα
      exact dist_pos.mpr (Finset.ne_of_mem_erase hα')
    · rw [dif_neg h]; norm_num
  have hdle : ∀ α ∈ s, d ≤ dist α (0 : FreqCirc) := by
    intro α hα
    rw [hddef, dif_pos ⟨α, hα⟩]
    exact Finset.inf'_le _ hα
  -- the bound on the off-diagonal part
  set C : ℝ := arcRest N j s d with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef, arcRest]
    exact Finset.sum_nonneg fun α _ => by
      have hp : (0 : ℝ) < (N : ℝ) * (d / 2) := mul_pos hNpos (by linarith)
      exact le_of_lt (by simpa using zpow_pos hp j)
  -- the arc radius
  set δ : ℝ := arcDelta N j s d with hδdef
  have hδpos : 0 < δ := by
    have ha : 0 < d / 4 := by linarith
    have hb : 0 < (1 : ℝ) / 4 := by norm_num
    have hc : 0 < (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ) - 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have he : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hNpos
    have hf : 0 < (2 * arcRest N j s d * (N : ℝ) + 2)⁻¹ := inv_pos.mpr (by positivity)
    rw [hδdef, arcDelta]
    exact lt_min (lt_min ha hb) (lt_min hc (lt_min he hf))
  have hδd : δ ≤ d / 4 := by
    rw [hδdef, arcDelta]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hδq : δ ≤ 1 / 4 := by
    rw [hδdef, arcDelta]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hδR : δ ≤ (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ) - 1) := by
    rw [hδdef, arcDelta]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hδN : δ ≤ (N : ℝ)⁻¹ := by
    rw [hδdef, arcDelta]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδC : δ ≤ (2 * C * (N : ℝ) + 2)⁻¹ := by
    rw [hδdef, arcDelta, ← hCdef]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the pointwise lower bound on the arc
  have hkey : ∀ a : ℝ, 0 < a → a ≤ δ →
      (1 / 2) * ((N : ℝ)⁻¹ * a⁻¹) ≤ ‖iwSymbolSet A (periodize φ) (a : FreqCirc)‖ := by
    intro a ha0 haδ
    have ha1 : a ≤ 1 := by linarith
    have haR : a ≤ (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N : ℝ) - 1) := haδ.trans hδR
    have haN : a ≤ (N : ℝ)⁻¹ := haδ.trans hδN
    have haC : a ≤ (2 * C * (N : ℝ) + 2)⁻¹ := haδ.trans hδC
    -- (i) the diagonal term is `φ a`
    have hdiag : ‖periodize φ (a : FreqCirc)‖ = ‖φ a‖ := by
      rw [periodize_eq_two_terms φ hφhalf (a : FreqCirc)]
      have hxmem : a ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨ha0.le, by linarith⟩
      have hrep : (AddCircle.equivIco (1 : ℝ) 0 ((a : FreqCirc))).val = a := by
        rw [show (a : FreqCirc) = ((a : ℝ) : AddCircle (1 : ℝ)) from rfl,
          AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (x := a) hxmem]
      rw [hrep]
      have hz : φ (a - 1) = 0 := hφhalf (a - 1) (by
        have hneg : a - 1 < 0 := by linarith
        rw [abs_of_neg hneg]
        linarith)
      rw [hz, add_zero]
    -- (ii) the off-diagonal terms are bounded
    have hrest : ∀ α ∈ s, ‖periodize φ ((a : FreqCirc) - α)‖ ≤ 2 * ((N : ℝ) * (d / 2)) ^ j := by
      intro α hα
      have hdist : d / 2 ≤ dist ((a : FreqCirc) - α) (0 : FreqCirc) := by
        have h1 := dist_triangle α (a : FreqCirc) (0 : FreqCirc)
        have h2 : dist (a : FreqCirc) (0 : FreqCirc) = a := by
          rw [dist_eq_norm, sub_zero]
          have habs : |a| ≤ |(1 : ℝ)| / 2 := by
            rw [abs_of_nonneg ha0.le]; norm_num; linarith
          rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero (x := a)).mpr habs,
            abs_of_nonneg ha0.le]
        have h3 : dist α (a : FreqCirc) = dist ((a : FreqCirc) - α) (0 : FreqCirc) := by
          rw [dist_eq_norm, dist_eq_norm, sub_zero]
          exact norm_sub_rev α (a : FreqCirc)
        have h4 := hdle α hα
        linarith
      have hεpos : 0 < d / 2 := by linarith
      rw [periodize_eq_two_terms φ hφhalf ((a : FreqCirc) - α)]
      obtain ⟨hb1, hb2⟩ := dist_zero_le_abs_rep ((a : FreqCirc) - α)
      have hu1 : ‖φ ((AddCircle.equivIco (1 : ℝ) 0 ((a : FreqCirc) - α)).val)‖
          ≤ ((N : ℝ) * (d / 2)) ^ j := hupper (d / 2) _ hεpos (hdist.trans hb1)
      have hu2 : ‖φ ((AddCircle.equivIco (1 : ℝ) 0 ((a : FreqCirc) - α)).val - 1)‖
          ≤ ((N : ℝ) * (d / 2)) ^ j := hupper (d / 2) _ hεpos (hdist.trans hb2)
      calc ‖φ ((AddCircle.equivIco (1 : ℝ) 0 ((a : FreqCirc) - α)).val)
              + φ ((AddCircle.equivIco (1 : ℝ) 0 ((a : FreqCirc) - α)).val - 1)‖
          ≤ ‖φ ((AddCircle.equivIco (1 : ℝ) 0 ((a : FreqCirc) - α)).val)‖
              + ‖φ ((AddCircle.equivIco (1 : ℝ) 0 ((a : FreqCirc) - α)).val - 1)‖ := norm_add_le _ _
        _ ≤ ((N : ℝ) * (d / 2)) ^ j + ((N : ℝ) * (d / 2)) ^ j := add_le_add hu1 hu2
        _ = 2 * ((N : ℝ) * (d / 2)) ^ j := by ring
    -- (iii) split the symbol
    have hsplit : iwSymbolSet A (periodize φ) (a : FreqCirc) =
        periodize φ (a : FreqCirc) + ∑ α ∈ s, periodize φ ((a : FreqCirc) - α) := by
      rw [Work.Analysis.IonescuWainger.iwSymbolSet, ← Finset.insert_erase h0A,
        Finset.sum_insert (Finset.notMem_erase (0 : FreqCirc) A), ← hsdef]
      simp
    have hsum : ‖∑ α ∈ s, periodize φ ((a : FreqCirc) - α)‖ ≤ C := by
      rw [hCdef]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => hrest α hα)
    have hφa : (N : ℝ)⁻¹ * a⁻¹ ≤ ‖periodize φ (a : FreqCirc)‖ := by
      rw [hdiag]
      exact hlower a ha0 (le_min haR haN)
    have hCsmall : C ≤ (1 / 2) * ((N : ℝ)⁻¹ * a⁻¹) := by
      have hden : 0 < 2 * C * (N : ℝ) + 2 := by positivity
      have h1 : 2 * C * (N : ℝ) * a ≤ 2 * C * (N : ℝ) * (2 * C * (N : ℝ) + 2)⁻¹ :=
        mul_le_mul_of_nonneg_left haC (by positivity)
      have h2 : 2 * C * (N : ℝ) * (2 * C * (N : ℝ) + 2)⁻¹ < 1 := by
        rw [← div_eq_mul_inv, div_lt_one hden]
        linarith
      have h3 : C * ((N : ℝ) * a) < 1 / 2 := by nlinarith [h1, h2]
      have h4 : C < 1 / (2 * ((N : ℝ) * a)) := by
        rw [lt_div_iff₀ (by positivity)]
        nlinarith [h3]
      have h5 : 1 / (2 * ((N : ℝ) * a)) = (1 / 2) * ((N : ℝ)⁻¹ * a⁻¹) := by
        field_simp
      linarith [h4, h5.le]
    rw [hsplit]
    have htri : ‖periodize φ (a : FreqCirc)‖ - ‖∑ α ∈ s, periodize φ ((a : FreqCirc) - α)‖
        ≤ ‖periodize φ (a : FreqCirc) + ∑ α ∈ s, periodize φ ((a : FreqCirc) - α)‖ := by
      have h := norm_sub_le (periodize φ (a : FreqCirc) + ∑ α ∈ s, periodize φ ((a : FreqCirc) - α))
        (∑ α ∈ s, periodize φ ((a : FreqCirc) - α))
      have h' : (periodize φ (a : FreqCirc) + ∑ α ∈ s, periodize φ ((a : FreqCirc) - α))
          - (∑ α ∈ s, periodize φ ((a : FreqCirc) - α)) = periodize φ (a : FreqCirc) := by abel
      rw [h'] at h
      linarith
    linarith [hφa, hsum, hCsmall, htri]
  -- the finiteness of the integral over the arc forces a contradiction
  intro hint
  set F : ℝ → ℂ := fun x => iwSymbolSet A (periodize φ) (x : FreqCirc) with hFdef
  have hδ1 : δ ≤ 1 := by linarith
  have hkeyF : ∀ a : ℝ, 0 < a → a ≤ δ → (1 / 2) * ((N : ℝ)⁻¹ * a⁻¹) ≤ ‖F a‖ := by
    intro a ha0 haδ
    rw [hFdef]
    exact hkey a ha0 haδ
  have hfin : (∫⁻ a in Set.Ioc 0 δ, ‖F a‖ₑ ∂volume) < ⊤ := by
    have h1 : Integrable F (volume.restrict (Set.Ioc 0 1)) := by
      rw [hFdef]
      exact measurePreserving_mk_circle.integrable_comp_of_integrable hint
    have h2 : (∫⁻ a in Set.Ioc 0 1, ‖F a‖ₑ ∂volume) < ⊤ := h1.2
    exact lt_of_le_of_lt (lintegral_mono_set (Set.Ioc_subset_Ioc_right hδ1)) h2
  have htop : (∫⁻ a in Set.Ioc 0 δ,
      ENNReal.ofReal ((1 / 2) * ((N : ℝ)⁻¹ * a⁻¹)) ∂volume) = ⊤ := by
    have hbase := (lintegral_inv_Ioc_eq_top δ hδpos).2
    have hsplit : (fun a : ℝ => ENNReal.ofReal ((1 / 2) * ((N : ℝ)⁻¹ * a⁻¹)))
        = fun a : ℝ => ENNReal.ofReal ((1 / 2) * (N : ℝ)⁻¹) * ENNReal.ofReal a⁻¹ := by
      funext a
      rw [show (1 / 2) * ((N : ℝ)⁻¹ * a⁻¹) = ((1 / 2) * (N : ℝ)⁻¹) * a⁻¹ by ring,
        ENNReal.ofReal_mul (by positivity)]
    rw [hsplit,
      lintegral_const_mul (ENNReal.ofReal ((1 / 2) * (N : ℝ)⁻¹))
        (f := fun a : ℝ => ENNReal.ofReal a⁻¹)
        (ENNReal.measurable_ofReal.comp measurable_inv),
      hbase, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne']
  have hle : (∫⁻ a in Set.Ioc 0 δ,
        ENNReal.ofReal ((1 / 2) * ((N : ℝ)⁻¹ * a⁻¹)) ∂volume)
      ≤ ∫⁻ a in Set.Ioc 0 δ, ‖F a‖ₑ ∂volume := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hkeyF a ha.1 ha.2)
  rw [htop] at hle
  exact absurd hfin (not_lt_of_ge hle)

/-- **The kernel of a non-integrable symbol vanishes.**  `iwKernel m j = fourierCoeff m j` is the
Bochner integral `∫ t, fourier (-j) t • m t`, and the Bochner integral of a non-integrable
function is `0`. -/
theorem integrable_of_integrable_fourier_smul {m : FreqCirc → ℂ} {j : ℤ}
    (h : Integrable (fun t : FreqCirc => fourier (T := 1) j t • m t) circleMeasure) :
    Integrable m circleMeasure := by
  have h2 : Integrable (fun t : FreqCirc =>
      (fourier (T := 1) j t • m t) * fourier (T := 1) (-j) t) circleMeasure :=
    h.mul_bdd ((map_continuous (fourier (T := 1) (-j))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by rw [fourier_apply, Circle.norm_coe])
  refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
  have h1 : fourier (T := 1) j t * fourier (T := 1) (-j) t = 1 := by
    rw [← fourier_add, add_neg_cancel]
    simp
  simp only [smul_eq_mul]
  calc fourier (T := 1) j t * m t * fourier (T := 1) (-j) t
      = (fourier (T := 1) j t * fourier (T := 1) (-j) t) * m t := by ring
    _ = m t := by rw [h1, one_mul]

theorem iwKernel_eq_zero_of_not_integrable {m : FreqCirc → ℂ}
    (hm : ¬ Integrable m circleMeasure) (j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel m j = 0 := by
  rw [Work.Analysis.IWMultiplier.iwKernel, fourierCoeff,
    MeasureTheory.integral_undef (fun h => hm (integrable_of_integrable_fourier_smul h))]

/-- **The degenerate modified bump gives the zero Ionescu--Wainger multiplier.** -/
theorem varphiNtj_Tle_eq_zero (ρ : ℝ) (l N : ℕ) (j : ℤ) (hj : j ≤ -2) (t : ℝ) (f : ℤ → ℂ) :
    Work.KMTAreas.A7.Tle ρ l (Work.KMTPlan.A6.varphiNtj N 0 j t) f = 0 := by
  by_cases hN : N = 0
  · have hφz : varphiNtj N 0 j t = 0 := by
      funext x
      rw [varphiNtj_factor]
      simp [hN, zero_zpow, show j ≠ 0 by omega]
    funext n
    rw [Work.KMTAreas.A7.Tle_apply, hφz]
    simp [Work.Analysis.IWMultiplier.iwKernel, fourierCoeff,
      Work.Analysis.IonescuWainger.periodize, Work.Analysis.IonescuWainger.iwSymbolSet]
  · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    have hni := not_integrable_iwSymbolSet_varphiNtj ρ l N hN1 j hj t
    have hker : ∀ i : ℤ, Work.Analysis.IWMultiplier.iwKernel
        (iwSymbolSet (iwArithFreqs ρ l) (periodize (varphiNtj N 0 j t))) i = 0 :=
      fun i => iwKernel_eq_zero_of_not_integrable hni i
    funext n
    rw [Work.KMTAreas.A7.Tle_apply]
    simp [hker]

end

end Work.KMTPlan.A6
