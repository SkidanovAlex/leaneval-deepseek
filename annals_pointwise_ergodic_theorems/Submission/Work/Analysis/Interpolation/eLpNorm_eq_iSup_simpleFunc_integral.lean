import Mathlib
import Submission.Work.Analysis.Interpolation.Basic
import Submission.Work.Analysis.Interpolation.enorm_integral_mul_le
import Submission.Port.Aesm

namespace Work.Analysis.Interpolation

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

variable {β : Type*} [MeasurableSpace β] {ν : Measure β}

/-! ## The extremal test function of a simple function

For `q > 1` and `z : ℂ` put `psi q z = conj z * ‖z‖ ^ (q - 2)`.  This is the pointwise
"extremal multiplier" of duality for `L^q`: it makes `z * psi q z` real and equal to `‖z‖ ^ q`,
while `‖psi q z‖ = ‖z‖ ^ (q - 1)`.  For a *simple* function `s` the function
`extremizer q s = psi q ∘ s` is again simple (it is `s.bind (const _ ∘ psi q)`), which is exactly
why the duality proof reduces to the case of simple functions. -/

/-- The pointwise extremal multiplier `z ↦ conj z * ‖z‖ ^ (q - 2)`. -/
private noncomputable def psi (q : ℝ) (z : ℂ) : ℂ := conj z * Complex.ofReal ((‖z‖ : ℝ) ^ (q - 2))

private lemma psi_zero (q : ℝ) : psi q 0 = 0 := by simp [psi]

/-- The extremal test function attached to a simple function: `psi q` composed with `s`. -/
private noncomputable def extremizer (q : ℝ) (s : SimpleFunc β ℂ) : SimpleFunc β ℂ :=
  s.bind fun z => SimpleFunc.const β (psi q z)

private lemma extremizer_apply (q : ℝ) (s : SimpleFunc β ℂ) (y : β) :
    extremizer q s y = psi q (s y) := by
  simp [extremizer, SimpleFunc.bind_apply]

private lemma psi_mul {q : ℝ} (hq : 1 < q) (z : ℂ) : z * psi q z = Complex.ofReal (‖z‖ ^ q) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [psi, Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < q)), Complex.ofReal_zero]
  · have hnorm : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have h1 : z * conj z = Complex.ofReal (‖z‖ ^ 2) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc z * psi q z = (z * conj z) * Complex.ofReal ((‖z‖ : ℝ) ^ (q - 2)) := by rw [psi]; ring
      _ = Complex.ofReal (‖z‖ ^ 2) * Complex.ofReal ((‖z‖ : ℝ) ^ (q - 2)) := by rw [h1]
      _ = Complex.ofReal (‖z‖ ^ 2 * (‖z‖ : ℝ) ^ (q - 2)) := by rw [← Complex.ofReal_mul]
      _ = Complex.ofReal (‖z‖ ^ q) := by
            congr 1
            rw [← Real.rpow_natCast (‖z‖ : ℝ) 2, ← Real.rpow_add hnorm]
            congr 1; ring

private lemma norm_psi {q : ℝ} (hq : 1 < q) (z : ℂ) : ‖psi q z‖ = ‖z‖ ^ (q - 1) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [psi, Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < q - 1))]
  · have hnorm : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have hnn : (0:ℝ) ≤ ‖z‖ ^ (q - 2) := Real.rpow_nonneg hnorm.le _
    have h2 : ‖Complex.ofReal ((‖z‖ : ℝ) ^ (q - 2))‖ = (‖z‖ : ℝ) ^ (q - 2) := by
      rw [show ∀ r : ℝ, ‖Complex.ofReal r‖ = |r| from fun r => RCLike.norm_ofReal r,
        abs_of_nonneg hnn]
    rw [psi, norm_mul, Complex.norm_conj, h2]
    nth_rewrite 1 [← Real.rpow_one ‖z‖]
    rw [← Real.rpow_add hnorm]
    congr 1; ring

private lemma enorm_psi_rpow {q : ℝ} (hq : 1 < q) (z : ℂ) :
    ‖psi q z‖ₑ ^ (q / (q - 1)) = ‖z‖ₑ ^ q := by
  have hexp : (q - 1) * (q / (q - 1)) = q := by
    have h : q - 1 ≠ 0 := by linarith
    field_simp
  rw [← ofReal_norm, norm_psi hq z,
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _) (by positivity),
    ← Real.rpow_mul (norm_nonneg z), hexp,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) (by linarith : (0:ℝ) ≤ q), ← ofReal_norm]

/-- The `L^{q'}`-mass of the extremal test function of `s` is the `L^q`-mass of `s`. -/
private lemma lintegral_enorm_extremizer (ν : Measure β) {q : ℝ} (hq : 1 < q)
    (s : SimpleFunc β ℂ) :
    ∫⁻ y, ‖(extremizer q s : β → ℂ) y‖ₑ ^ (q / (q - 1)) ∂ν
      = ∫⁻ y, ‖(s : β → ℂ) y‖ₑ ^ q ∂ν := by
  refine lintegral_congr fun y => ?_
  rw [extremizer_apply, enorm_psi_rpow hq]

/-- The integral of `s` against its own extremal test function is the real number
`∫⁻ ‖s‖ₑ ^ q` (embedded in `ℂ`). -/
private lemma integral_mul_extremizer (ν : Measure β) {q : ℝ} (hq : 1 < q)
    (s : SimpleFunc β ℂ) :
    ∫ y, (s : β → ℂ) y * (extremizer q s : β → ℂ) y ∂ν
      = Complex.ofReal ((∫⁻ y, ‖(s : β → ℂ) y‖ₑ ^ q ∂ν).toReal) := by
  let W : SimpleFunc β ℂ := s.bind fun z => SimpleFunc.const β (Complex.ofReal (‖z‖ ^ q))
  have hW : ∀ y, W y = Complex.ofReal (‖(s : β → ℂ) y‖ ^ q) := by
    intro y
    simp [W, SimpleFunc.bind_apply]
  have hAE : AEStronglyMeasurable (fun y => ‖(s : β → ℂ) y‖ ^ q) ν :=
    ((Complex.continuous_re.comp_stronglyMeasurable
        (SimpleFunc.stronglyMeasurable W)).aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun y => by
        show (W y).re = ‖(s : β → ℂ) y‖ ^ q
        rw [hW y, Complex.ofReal_re])
  have hlint : ∫⁻ y, ENNReal.ofReal (‖(s : β → ℂ) y‖ ^ q) ∂ν
      = ∫⁻ y, ‖(s : β → ℂ) y‖ₑ ^ q ∂ν :=
    lintegral_congr fun y => by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith : (0:ℝ) ≤ q)]
  calc ∫ y, (s : β → ℂ) y * (extremizer q s : β → ℂ) y ∂ν
      = ∫ y, W y ∂ν := integral_congr_ae (Filter.Eventually.of_forall fun y => by
          rw [hW y]; exact psi_mul hq (s y))
    _ = ∫ y, Complex.ofReal (‖(s : β → ℂ) y‖ ^ q) ∂ν := integral_congr_ae
          (Filter.Eventually.of_forall fun y => hW y)
    _ = Complex.ofReal (∫ y, ‖(s : β → ℂ) y‖ ^ q ∂ν) := integral_complex_ofReal
    _ = Complex.ofReal ((∫⁻ y, ‖(s : β → ℂ) y‖ₑ ^ q ∂ν).toReal) := by
          congr 1
          rw [integral_eq_lintegral_of_nonneg_ae
            (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) _) hAE, hlint]

/-- The `L^q` seminorm at the exponent `ENNReal.ofReal q` (`0 < q`) as the `1/q`-th power of the
defining lower integral. -/
private lemma eLpNorm_ofReal_eq_lintegral (ν : Measure β) {q : ℝ} (hq0 : 0 < q) (u : β → ℂ)
    (hu : AEStronglyMeasurable u ν := by pw_aesm) :
    eLpNorm u (ENNReal.ofReal q) ν = (∫⁻ y, ‖u y‖ₑ ^ q ∂ν) ^ (1 / q) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hu) (ENNReal.ofReal_ne_zero_iff.mpr hq0)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq0.le]

/-! ## Truncation of an arbitrary measurable function to a bounded one on a finite measure set -/

/-- Given a measurable `f : β → ℂ` with `c < ∫⁻ ‖f‖ₑ ^ q`, there is a measurable set `A` of
finite measure on which `f` is bounded and whose partial `q`-mass already exceeds `c`. -/
private theorem exists_measurableSet_lintegral_enorm_rpow_lt {f : β → ℂ} (hf : Measurable f)
    [SigmaFinite ν] {q : ℝ} {c : ℝ≥0∞} (hc : c < ∫⁻ y, ‖f y‖ₑ ^ q ∂ν) :
    ∃ A : Set β, MeasurableSet A ∧ ν A < ⊤ ∧ (∃ N : ℝ, 0 ≤ N ∧ ∀ y ∈ A, ‖f y‖ ≤ N) ∧
      c < ∫⁻ y, ‖f y‖ₑ ^ q * (A.indicator (fun _ => 1)) y ∂ν := by
  classical
  set A : ℕ → Set β := fun k => spanningSets ν k ∩ {y | ‖f y‖ ≤ (k : ℝ)} with hA
  have hAmeas : ∀ k, MeasurableSet (A k) := fun k =>
    (measurableSet_spanningSets ν k).inter (measurableSet_le hf.norm measurable_const)
  have hAmono : Monotone A := by
    intro k l hkl y hy
    have h1 : y ∈ spanningSets ν l := spanningSets_mono hkl hy.1
    have h2 : ‖f y‖ ≤ (l : ℝ) := hy.2.trans (by exact_mod_cast hkl)
    exact ⟨h1, h2⟩
  have hind : ∀ k l, k ≤ l → ∀ y, (A k).indicator (fun _ => (1 : ℝ≥0∞)) y
      ≤ (A l).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro k l hkl y
    by_cases hy : y ∈ A k
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hAmono hkl hy)]
    · rw [Set.indicator_of_notMem hy]
      exact bot_le
  have hFmeas : ∀ k, Measurable (fun y : β => ‖f y‖ₑ ^ q * (A k).indicator (fun _ => 1) y) :=
    fun k => (hf.enorm.pow_const q).mul (measurable_const.indicator (hAmeas k))
  have hFmono : Monotone (fun (k : ℕ) (y : β) => ‖f y‖ₑ ^ q * (A k).indicator (fun _ => 1) y) := by
    intro k l hkl y
    simp only []
    exact mul_le_mul_right (hind k l hkl y) _
  have hsup : ∀ y, ⨆ k, ‖f y‖ₑ ^ q * (A k).indicator (fun _ => 1) y = ‖f y‖ₑ ^ q := by
    intro y
    refine iSup_eq_of_forall_le_of_forall_lt_exists_gt (fun k => ?_) (fun w hw => ?_)
    · by_cases hy : y ∈ A k
      · rw [Set.indicator_of_mem hy, mul_one]
      · rw [Set.indicator_of_notMem hy, mul_zero]
        exact bot_le
    · refine ⟨max (spanningSetsIndex ν y) (Nat.ceil ‖f y‖), ?_⟩
      have hmem : y ∈ A (max (spanningSetsIndex ν y) (Nat.ceil ‖f y‖)) := by
        refine ⟨spanningSets_mono (le_max_left _ _) (mem_spanningSetsIndex ν y), ?_⟩
        exact (Nat.le_ceil ‖f y‖).trans (by exact_mod_cast le_max_right _ _)
      rw [Set.indicator_of_mem hmem, mul_one]
      exact hw
  have hlint : ∫⁻ y, ‖f y‖ₑ ^ q ∂ν
      = ⨆ k, ∫⁻ y, ‖f y‖ₑ ^ q * (A k).indicator (fun _ => 1) y ∂ν := by
    rw [← lintegral_iSup hFmeas hFmono]
    exact lintegral_congr fun y => (hsup y).symm
  have hex : ∃ k, c < ∫⁻ y, ‖f y‖ₑ ^ q * (A k).indicator (fun _ => 1) y ∂ν := by
    by_contra hcon
    push_neg at hcon
    exact absurd (iSup_le hcon) (not_le.mpr (by rwa [hlint] at hc))
  obtain ⟨k, hk⟩ := hex
  exact ⟨A k, hAmeas k, (measure_mono (Set.inter_subset_left)).trans_lt (measure_spanningSets_lt_top ν k),
    ⟨k, by positivity, fun y hy => hy.2⟩, hk⟩

/-! ## The duality `‖f‖_q = sup { |∫ f g| : ‖g‖_{q'} ≤ 1 }` -/

private theorem le_iSup_of_measurable [SigmaFinite ν] {q : ℝ} (hq : 1 < q) {f : β → ℂ}
    (hf : Measurable f) :
    eLpNorm f (ENNReal.ofReal q) ν ≤
      ⨆ (g : SimpleFunc β ℂ) (_ : eLpNorm (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν ≤ 1),
        ‖∫ y, f y * (g : β → ℂ) y ∂ν‖ₑ := by
  classical
  refine le_of_forall_lt fun c hc => ?_
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : (0:ℝ) < q - 1 := by linarith
  have hq'0 : (0:ℝ) < q / (q - 1) := by positivity
  have h1q_lt : (0:ℝ) < 1 / q := by positivity
  have h1q'_nonneg : (0:ℝ) ≤ 1 / (q / (q - 1)) := by positivity
  have h1qm : (1:ℝ) / q * q = 1 := by field_simp
  have hq1m : q * (1 / q) = 1 := by field_simp
  have hrel : (1:ℝ) / q + 1 / (q / (q - 1)) = 1 := by
    have h : q - 1 ≠ 0 := by linarith
    have hqne : q ≠ 0 := by linarith
    field_simp
    ring
  haveI hTriple : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal (q / (q - 1))) 1 :=
    Real.HolderConjugate.ennrealOfReal ((Real.holderConjugate_iff_eq_conjExponent hq).mpr rfl)
  -- step 1 : unfold the left-hand side
  have hc' : c < (∫⁻ y, ‖f y‖ₑ ^ q ∂ν) ^ (1 / q) := by
    rwa [eLpNorm_ofReal_eq_lintegral ν hq0 f] at hc
  have hctop : c ≠ ⊤ := ne_top_of_lt (hc'.trans_le le_top)
  -- step 2 : raise to the `q`-th power
  have hcq : c ^ q < ∫⁻ y, ‖f y‖ₑ ^ q ∂ν := by
    have h := ENNReal.rpow_lt_rpow hc' hq0
    rwa [← ENNReal.rpow_mul, h1qm, ENNReal.rpow_one] at h
  -- step 3 : truncate to a bounded function on a finite measure set
  obtain ⟨A, hAmeas, hAfin, ⟨N, hN0, hNbdd⟩, hcA⟩ :=
    exists_measurableSet_lintegral_enorm_rpow_lt hf hcq
  set X : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ ^ q * (A.indicator (fun _ => 1)) y ∂ν with hXdef
  have hXeq : ∫⁻ y, ‖(A.indicator f) y‖ₑ ^ q ∂ν = X := by
    rw [hXdef]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy f, Set.indicator_of_mem hy, mul_one]
    · rw [Set.indicator_of_notMem hy f, Set.indicator_of_notMem hy, mul_zero, enorm_zero,
        ENNReal.zero_rpow_of_pos hq0]
  have hcX : c < X ^ (1 / q) := by
    have h := ENNReal.rpow_lt_rpow hcA h1q_lt
    rwa [← ENNReal.rpow_mul, hq1m, ENNReal.rpow_one] at h
  have hXtop : X ≠ ⊤ := by
    have hbdd : ∀ y, ‖f y‖ₑ ^ q * (A.indicator (fun _ => 1)) y
        ≤ ENNReal.ofReal (N ^ q) * (A.indicator (fun _ => 1)) y := by
      intro y
      by_cases hy : y ∈ A
      · simp only [Set.indicator_of_mem hy, mul_one]
        calc ‖f y‖ₑ ^ q ≤ (ENNReal.ofReal N) ^ q :=
              ENNReal.rpow_le_rpow
                (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hNbdd y hy)) hq0.le
          _ = ENNReal.ofReal (N ^ q) := ENNReal.ofReal_rpow_of_nonneg hN0 hq0.le
      · simp only [Set.indicator_of_notMem hy, mul_zero, le_refl]
    have hle : X ≤ ENNReal.ofReal (N ^ q) * ν A := by
      rw [hXdef]
      calc ∫⁻ y, ‖f y‖ₑ ^ q * (A.indicator (fun _ => 1)) y ∂ν
          ≤ ∫⁻ y, ENNReal.ofReal (N ^ q) * (A.indicator (fun _ => 1)) y ∂ν :=
            lintegral_mono hbdd
        _ = ENNReal.ofReal (N ^ q) * ∫⁻ y, (A.indicator (fun _ => 1)) y ∂ν :=
            lintegral_const_mul _ (measurable_const.indicator hAmeas)
        _ = ENNReal.ofReal (N ^ q) * ν A := by
            congr 1
            exact lintegral_indicator_one hAmeas
    exact (lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hAfin)).ne
  have hXpos : 0 < X := by
    rcases eq_or_ne X 0 with h0 | h0
    · rw [h0, ENNReal.zero_rpow_of_pos h1q_lt] at hcX
      exact absurd hcX (not_lt.mpr bot_le)
    · exact lt_of_le_of_ne bot_le (Ne.symm h0)
  have hXpowtop : X ^ (1 / q) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg h1q_lt.le hXtop).ne
  have hXrpos : 0 < X.toReal := ENNReal.toReal_pos hXpos.ne' hXtop
  have hcXr : c.toReal < X.toReal ^ (1 / q) := by
    have h : c.toReal < (X ^ (1 / q)).toReal :=
      (ENNReal.toReal_lt_toReal hctop hXpowtop).mpr hcX
    rwa [← ENNReal.toReal_rpow] at h
  -- step 4 : the real parameter of the approximation
  set ε : ℝ := (X.toReal ^ (1 / q) - c.toReal) / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hkey : c.toReal + 2 * ε < X.toReal ^ (1 / q) := by rw [hε]; linarith
  -- step 5 : `MemLp` of the truncated function, and a simple approximation of it
  have hLp0 : eLpNorm (A.indicator f) (ENNReal.ofReal q) ν = X ^ (1 / q) := by
    rw [eLpNorm_ofReal_eq_lintegral ν hq0 _ (hf.indicator hAmeas).aestronglyMeasurable, hXeq]
  have hMemLp0 : MemLp (A.indicator f) (ENNReal.ofReal q) ν :=
    by rw [MeasureTheory.memLp_iff, hLp0]; exact ENNReal.rpow_lt_top_of_nonneg h1q_lt.le hXtop
  obtain ⟨s₀, hs₀, hsMems₀⟩ := hMemLp0.exists_simpleFunc_eLpNorm_sub_lt ENNReal.ofReal_ne_top
    (ε := ENNReal.ofReal ε) (ENNReal.ofReal_ne_zero_iff.mpr hεpos)
  -- step 6 : restrict the approximation to `A`
  set s : SimpleFunc β ℂ :=
    s₀ * SimpleFunc.piecewise A hAmeas (SimpleFunc.const β 1) (SimpleFunc.const β 0) with hsdef
  have hs_apply : ∀ y, (s : β → ℂ) y = (s₀ : β → ℂ) y * (if y ∈ A then 1 else 0) := by
    intro y
    simp only [hsdef, SimpleFunc.mul_apply, SimpleFunc.piecewise_apply, SimpleFunc.const_apply]
  have hsoff : ∀ y, y ∉ A → (s : β → ℂ) y = 0 := by
    intro y hy
    rw [hs_apply, if_neg hy, mul_zero]
  have hsε : eLpNorm ((A.indicator f) - (s : β → ℂ)) (ENNReal.ofReal q) ν < ENNReal.ofReal ε := by
    refine lt_of_le_of_lt (eLpNorm_mono (hf := by pw_aesm) fun y => ?_) hs₀
    rw [Pi.sub_apply, Pi.sub_apply]
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy f, hs_apply, if_pos hy, mul_one]
    · rw [Set.indicator_of_notMem hy f, hs_apply, if_neg hy, mul_zero]
      simp
  have hsMem : MemLp (s : β → ℂ) (ENNReal.ofReal q) ν := by
    refine lt_of_le_of_lt (eLpNorm_mono (hf := (SimpleFunc.stronglyMeasurable s).aestronglyMeasurable)
      fun y => ?_) hsMems₀.eLpNorm_lt_top
    rw [hs_apply]
    by_cases hy : y ∈ A
    · rw [if_pos hy, mul_one]
    · rw [if_neg hy, mul_zero, norm_zero]
      exact norm_nonneg _
  -- step 7 : the extremal test function of `s` and its normalisation
  set Xs : ℝ≥0∞ := ∫⁻ y, ‖(s : β → ℂ) y‖ₑ ^ q ∂ν with hXsdef
  have hXs_eLp : eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν = Xs ^ (1 / q) := by
    rw [eLpNorm_ofReal_eq_lintegral ν hq0 _ (SimpleFunc.stronglyMeasurable s).aestronglyMeasurable, hXsdef]
  have hXstop : Xs ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_rpow_of_pos h1q_lt] at hXs_eLp
    exact absurd (hXs_eLp ▸ hsMem.eLpNorm_lt_top) (lt_irrefl _)
  set H : SimpleFunc β ℂ := extremizer q s with hH
  have hH_eLp : eLpNorm (H : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν
      = Xs ^ (1 / (q / (q - 1))) := by
    rw [eLpNorm_ofReal_eq_lintegral ν hq'0 _ (SimpleFunc.stronglyMeasurable H).aestronglyMeasurable, hH,
      lintegral_enorm_extremizer ν hq s, ← hXsdef]
  have hH_int : ∫ y, (s : β → ℂ) y * (H : β → ℂ) y ∂ν = Complex.ofReal Xs.toReal := by
    rw [hH]
    exact integral_mul_extremizer ν hq s
  -- the triangle inequality giving `Xs ≠ 0`
  have hmink : X ^ (1 / q) ≤ Xs ^ (1 / q)
      + eLpNorm ((A.indicator f) - (s : β → ℂ)) (ENNReal.ofReal q) ν := by
    have h2 : eLpNorm (A.indicator f) (ENNReal.ofReal q) ν
        ≤ eLpNorm (s : β → ℂ) (ENNReal.ofReal q) ν
          + eLpNorm ((A.indicator f) - (s : β → ℂ)) (ENNReal.ofReal q) ν := by
      have hpt : (A.indicator f) = (s : β → ℂ) + ((A.indicator f) - (s : β → ℂ)) := by
        funext y
        rw [Pi.add_apply, Pi.sub_apply]
        by_cases hy : y ∈ A
        · rw [Set.indicator_of_mem hy f]
          ring
        · rw [Set.indicator_of_notMem hy f, hsoff y hy]
          ring
      conv_lhs => rw [hpt]
      exact eLpNorm_add_le
        (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq.le)
    rw [← hLp0, ← hXs_eLp]
    exact h2
  have hXs0 : Xs ≠ 0 := by
    intro h0
    rw [h0, ENNReal.zero_rpow_of_pos h1q_lt, zero_add] at hmink
    have h1 : ENNReal.ofReal ε < X ^ (1 / q) := by
      rw [← ENNReal.ofReal_toReal hXtop,
        ENNReal.ofReal_rpow_of_nonneg (ENNReal.toReal_nonneg (a := X)) h1q_lt.le,
        ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hXrpos _), hε]
      linarith [hXrpos, ENNReal.toReal_nonneg (a := c), hcXr]
    exact absurd (h1.trans_le (hmink.trans hsε.le)) (lt_irrefl _)
  have hXsrpos : 0 < Xs.toReal := ENNReal.toReal_pos hXs0 hXstop
  -- step 8 : the normalised test function and its admissibility
  set lam : ℝ := Xs.toReal ^ (1 / q - 1) with hlam
  have hlam_nonneg : 0 ≤ lam := by rw [hlam]; exact Real.rpow_nonneg hXsrpos.le _
  have hlam_mul : lam * Xs.toReal = Xs.toReal ^ (1 / q) := by
    have h1 : lam * Xs.toReal = Xs.toReal ^ (1 / q - 1) * Xs.toReal ^ (1:ℝ) := by
      rw [hlam, Real.rpow_one]
    rw [h1, ← Real.rpow_add hXsrpos]
    congr 1; ring
  have hlam_mul' : lam * Xs.toReal ^ (1 / (q / (q - 1))) = 1 := by
    rw [hlam, ← Real.rpow_add hXsrpos,
      show 1 / q - 1 + 1 / (q / (q - 1)) = 0 by linarith, Real.rpow_zero]
  set g : SimpleFunc β ℂ := (Complex.ofReal lam) • H with hg
  have hg_apply : ∀ y, (g : β → ℂ) y = Complex.ofReal lam * (H : β → ℂ) y := by
    intro y
    rw [hg, SimpleFunc.smul_apply, smul_eq_mul]
  have hgadmissible : eLpNorm (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν ≤ 1 := by
    have h1 : eLpNorm (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν
        ≤ ‖Complex.ofReal lam‖ₑ * eLpNorm (H : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν := by
      rw [hg, SimpleFunc.coe_smul]
      exact eLpNorm_const_smul_le
    refine h1.trans ?_
    rw [hH_eLp]
    have h2 : ‖Complex.ofReal lam‖ₑ = ENNReal.ofReal lam := by
      rw [← ofReal_norm, show ‖Complex.ofReal lam‖ = |lam| from RCLike.norm_ofReal lam,
        abs_of_nonneg hlam_nonneg]
    rw [h2, ← ENNReal.ofReal_toReal hXstop,
      ENNReal.ofReal_rpow_of_nonneg (ENNReal.toReal_nonneg (a := Xs)) h1q'_nonneg,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hXsrpos.le _), hlam_mul', ENNReal.ofReal_one]
  -- step 9 : the two integral identities
  have hIntS : ∫ y, (s : β → ℂ) y * (g : β → ℂ) y ∂ν
      = Complex.ofReal (Xs.toReal ^ (1 / q)) := by
    have hstep : ∫ y, (s : β → ℂ) y * (g : β → ℂ) y ∂ν
        = ∫ y, (Complex.ofReal lam) * ((s : β → ℂ) y * (H : β → ℂ) y) ∂ν := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only []
      rw [hg_apply]
      ring
    rw [hstep]
    have hstep2 : ∫ y, (Complex.ofReal lam) * ((s : β → ℂ) y * (H : β → ℂ) y) ∂ν
        = (Complex.ofReal lam) * ∫ y, (s : β → ℂ) y * (H : β → ℂ) y ∂ν := by
      simpa only [smul_eq_mul] using
        integral_smul (Complex.ofReal lam) (fun y => (s : β → ℂ) y * (H : β → ℂ) y)
    rw [hstep2, hH_int, ← Complex.ofReal_mul, hlam_mul]
  have hnorm1 : ‖∫ y, (s : β → ℂ) y * (g : β → ℂ) y ∂ν‖ = Xs.toReal ^ (1 / q) := by
    rw [hIntS, show ‖Complex.ofReal (Xs.toReal ^ (1 / q))‖ = |Xs.toReal ^ (1 / q)| from
      RCLike.norm_ofReal _, abs_of_nonneg (Real.rpow_nonneg hXsrpos.le _)]
  have hMemLpg : MemLp (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν :=
    lt_of_le_of_lt hgadmissible ENNReal.one_lt_top
  have hMemLpe : MemLp ((A.indicator f) - (s : β → ℂ)) (ENNReal.ofReal q) ν :=
    hsε.trans ENNReal.ofReal_lt_top
  have hIntEnorm : ‖∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν‖ₑ
      ≤ ENNReal.ofReal ε := by
    have h1 : ‖∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν‖ₑ
        ≤ eLpNorm ((A.indicator f) - (s : β → ℂ)) (ENNReal.ofReal q) ν
          * eLpNorm (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν :=
      enorm_integral_mul_le hq hMemLpe.aestronglyMeasurable.aemeasurable hMemLpg.aestronglyMeasurable.aemeasurable
    have h2 := mul_le_mul' hsε.le hgadmissible
    rw [mul_one] at h2
    exact h1.trans h2
  have hIntE : ‖∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν‖ ≤ ε := by
    have h1 : (‖∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν‖ₑ).toReal ≤ ε := by
      rw [← ENNReal.toReal_ofReal hεpos.le]
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hIntEnorm
    rwa [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)] at h1
  -- step 10 : comparison of the norms
  have hIntF : ∫ y, f y * (g : β → ℂ) y ∂ν = ∫ y, (A.indicator f) y * (g : β → ℂ) y ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy f]
    · have hHy : (H : β → ℂ) y = 0 := by
        rw [hH, extremizer_apply, hsoff y hy, psi_zero]
      simp only [Set.indicator_of_notMem hy f, hg_apply, hHy, mul_zero]
  have hsplit : ∫ y, (A.indicator f) y * (g : β → ℂ) y ∂ν
      = (∫ y, (s : β → ℂ) y * (g : β → ℂ) y ∂ν)
        + ∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν := by
    have h3 : ∫ y, ((s : β → ℂ) y * (g : β → ℂ) y
          + ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y) ∂ν
        = (∫ y, (s : β → ℂ) y * (g : β → ℂ) y ∂ν)
          + ∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν :=
      integral_add (hsMem.integrable_mul hMemLpg) (hMemLpe.integrable_mul hMemLpg)
    rw [← h3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    ring
  have hmain : c.toReal < ‖(∫ y, (s : β → ℂ) y * (g : β → ℂ) y ∂ν)
      + ∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν‖ := by
    have htri : ‖∫ y, (s : β → ℂ) y * (g : β → ℂ) y ∂ν‖
        ≤ ‖(∫ y, (s : β → ℂ) y * (g : β → ℂ) y ∂ν)
            + ∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν‖
          + ‖∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν‖ := by
      have h := norm_sub_le ((∫ y, (s : β → ℂ) y * (g : β → ℂ) y ∂ν)
            + ∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν)
          (∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν)
      rwa [add_sub_cancel_right] at h
    rw [hnorm1] at htri
    have hXspowtop : Xs ^ (1 / q) ≠ ⊤ := by
      rw [← hXs_eLp]
      exact hsMem.eLpNorm_lt_top.ne
    have hminkr : X.toReal ^ (1 / q) ≤ Xs.toReal ^ (1 / q) + ε := by
      have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hXspowtop, hsε.ne_top⟩) hmink
      have h' : (eLpNorm ((A.indicator f) - (s : β → ℂ)) (ENNReal.ofReal q) ν).toReal ≤ ε := by
        rw [← ENNReal.toReal_ofReal hεpos.le]
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hsε.le
      rw [ENNReal.toReal_add hXspowtop hsε.ne_top, ← ENNReal.toReal_rpow,
        ← ENNReal.toReal_rpow] at h
      linarith
    linarith
  -- step 11 : conclude
  have hfin : c < ‖∫ y, f y * (g : β → ℂ) y ∂ν‖ₑ := by
    have hpos : (0:ℝ) < ‖(∫ y, (s : β → ℂ) y * (g : β → ℂ) y ∂ν)
        + ∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν‖ := by
      linarith [hmain, ENNReal.toReal_nonneg (a := c)]
    have h1 := (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hmain
    have h2 : ENNReal.ofReal ‖(∫ y, (s : β → ℂ) y * (g : β → ℂ) y ∂ν)
        + ∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν‖
        = ‖∫ y, f y * (g : β → ℂ) y ∂ν‖ₑ := by
      rw [ofReal_norm]
      congr 1
      rw [← hsplit, ← hIntF]
    calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hctop).symm
      _ < ENNReal.ofReal ‖(∫ y, (s : β → ℂ) y * (g : β → ℂ) y ∂ν)
            + ∫ y, ((A.indicator f) - (s : β → ℂ)) y * (g : β → ℂ) y ∂ν‖ := h1
      _ = ‖∫ y, f y * (g : β → ℂ) y ∂ν‖ₑ := h2
  exact lt_of_lt_of_le hfin (le_trans
    (le_iSup (fun _ : eLpNorm (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν ≤ 1 =>
      ‖∫ y, f y * (g : β → ℂ) y ∂ν‖ₑ) hgadmissible)
    (le_iSup (fun g : SimpleFunc β ℂ =>
      ⨆ (_ : eLpNorm (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν ≤ 1),
        ‖∫ y, f y * (g : β → ℂ) y ∂ν‖ₑ) g))

theorem eLpNorm_eq_iSup_simpleFunc_integral {β : Type*} [MeasurableSpace β] {ν : Measure β} [SigmaFinite ν] {q : ℝ} (hq : 1 < q) {f : β → ℂ} (hf : AEMeasurable f ν) : eLpNorm f (ENNReal.ofReal q) ν = ⨆ (g : SimpleFunc β ℂ) (_ : eLpNorm (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν ≤ 1), ‖∫ y, f y * (g : β → ℂ) y ∂ν‖ₑ := by
  obtain ⟨f', hf'meas, hf'ae⟩ : ∃ f' : β → ℂ, Measurable f' ∧ f =ᵐ[ν] f' :=
    ⟨hf.aestronglyMeasurable.mk f, hf.aestronglyMeasurable.measurable_mk,
      hf.aestronglyMeasurable.ae_eq_mk⟩
  have heLp : eLpNorm f (ENNReal.ofReal q) ν = eLpNorm f' (ENNReal.ofReal q) ν :=
    eLpNorm_congr_ae hf'ae
  have hSup : (⨆ (g : SimpleFunc β ℂ)
        (_ : eLpNorm (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν ≤ 1),
        ‖∫ y, f y * (g : β → ℂ) y ∂ν‖ₑ)
      = (⨆ (g : SimpleFunc β ℂ)
        (_ : eLpNorm (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν ≤ 1),
        ‖∫ y, f' y * (g : β → ℂ) y ∂ν‖ₑ) := by
    refine iSup_congr fun g => iSup_congr fun hg => ?_
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hf'ae] with y hy
    rw [hy]
  rw [heLp, hSup]
  refine le_antisymm (le_iSup_of_measurable hq hf'meas) ?_
  refine iSup_le fun g => iSup_le fun hg => ?_
  calc ‖∫ y, f' y * (g : β → ℂ) y ∂ν‖ₑ
      ≤ eLpNorm f' (ENNReal.ofReal q) ν
        * eLpNorm (g : β → ℂ) (ENNReal.ofReal (q / (q - 1))) ν :=
        enorm_integral_mul_le hq hf'meas.aemeasurable
          (SimpleFunc.stronglyMeasurable g).measurable.aemeasurable
    _ ≤ eLpNorm f' (ENNReal.ofReal q) ν * 1 := mul_le_mul' le_rfl hg
    _ = eLpNorm f' (ENNReal.ofReal q) ν := mul_one _

end Work.Analysis.Interpolation
