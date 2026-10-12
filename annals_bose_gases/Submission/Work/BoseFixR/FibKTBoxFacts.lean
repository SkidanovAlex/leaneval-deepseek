import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.q3kinDiagCore
import Submission.Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.FibKTBoxFacts`

Box facts for the slot-`i` fibre Fourier density `fibKT` of a **continuous**
(not necessarily box-supported) `(m+1)`-body state `Φ`:

* `FibKTBoxFacts` — the pointwise bound on `abox m ℓ`, the `p`-`lintegral` bound on `abox m ℓ`,
  and joint continuity of `(r,p) ↦ fibKT ℓ Φ i r p`.

The three conjuncts are proved separately:

* `fibKT_le_const_on_abox` (`FibKTLeConstOnAbox`) — the crude `L¹`-Fourier estimate
  `fibKT ≤ (chiSup·2C·ℓ³)²`.  Only continuity is needed: `Φ` is bounded by compactness on the
  image of `acube ℓ × abox m ℓ` under the (continuous) insertion map `(z,r) ↦ kcInsN m i (z,r)`
  (`fibre_bound_on_abox`), the box mean of the fibre is bounded by the same constant
  (`bsMean_abs_le_of_bound`), and the window `χ_ℓ` kills everything off `acube ℓ`.
* `fibKT_lintegral_le_on_abox` (`FibKTLintegralLeOnAbox`) — Plancherel for `L¹ ∩ L²`
  (`Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp`) applied to the mean-free windowed fibre.
* `continuous_uncurry_fibKT` — joint continuity: the fibre, its box mean, `bsQ` and finally the
  windowed Fourier integral depend continuously on `(r,p)`; the last step is the parametric
  integral theorem `continuous_parametric_integral_of_continuous` on the compact `acube ℓ`.

No support hypothesis on `Φ` is used anywhere: the vanishing off `acube ℓ` comes from the
window, not from `Φ`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Real BigOperators

namespace Work.BoseFixR

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. Elementary inputs -/

/-- The insertion `p ↦ kcInsN n i p` is continuous on `ℝ³ × X n`
(coordinatewise from `kc_insN_apply_same`/`kc_insN_apply_succ`). -/
private lemma continuous_kcInsN_pair' {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun p : ℝ³ × Submission.BoseGases.X n => Submission.BoseGases.kcInsN n i p) := by
  rw [continuous_pi_iff]
  intro j
  by_cases hj : j = i
  · subst j
    have hEq : (fun p : ℝ³ × Submission.BoseGases.X n =>
        (Submission.BoseGases.kcInsN n i p) i) = fun p => p.1 := by
      funext p; exact Submission.BoseGases.kc_insN_apply_same n i p.1 p.2
    rw [hEq]; fun_prop
  · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    have hEq : (fun p : ℝ³ × Submission.BoseGases.X n =>
        (Submission.BoseGases.kcInsN n i p) (i.succAbove j')) = fun p => p.2 j' := by
      funext p; exact Submission.BoseGases.kc_insN_apply_succ n i p.1 p.2 j'
    rw [hEq]; fun_prop

/-- The anchored window is the scaled bump. -/
private lemma bsWin_zero_eq (ℓ : ℝ) (z : ℝ³) :
    Work.BSKinetic.bsWin ℓ 0 z = Submission.BoseGases.chiScale ℓ z := by
  simp [Work.BSKinetic.bsWin]

/-- The anchored box mean is bounded by the sup of `ψ` over `acube ℓ`. -/
private lemma bsMean_abs_le_of_bound {ℓ M : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hM : 0 ≤ M) (hψ : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ M) :
    |Work.BSKinetic.bsMean ℓ 0 ψ| ≤ M := by
  have hvol : (volume : Measure ℝ³).real (Submission.BoseGases.acube ℓ) = ℓ ^ 3 := by
    rw [MeasureTheory.measureReal_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  have hI : |∫ z in Submission.BoseGases.acube ℓ, ψ z| ≤ M * ℓ ^ 3 := by
    have h1 : ‖∫ z in Submission.BoseGases.acube ℓ, ψ z‖
        ≤ M * (volume : Measure ℝ³).real (Submission.BoseGases.acube ℓ) :=
      MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
        (fun z hz => by rw [Real.norm_eq_abs]; exact hψ z hz)
    rwa [hvol, Real.norm_eq_abs] at h1
  have hpos : (0 : ℝ) < ℓ ^ 3 := by positivity
  simp only [Work.BSKinetic.bsMean, smul_zero, zero_add]
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hpos.le)]
  calc (ℓ ^ 3)⁻¹ * |∫ z in Submission.BoseGases.acube ℓ, ψ z|
      ≤ (ℓ ^ 3)⁻¹ * (M * ℓ ^ 3) := mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hpos.le)
    _ = M := by
        rw [mul_comm M (ℓ ^ 3), ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]

/-- **Uniform bound of the slot-`i` fibre on the box.**  For a continuous `(m+1)`-body state
`Φ` there is `C ≥ 0` with `|Φ (kcInsN m i (z,r))| ≤ C` for every `z ∈ acube ℓ` and every
`r ∈ abox m ℓ` (compactness of the image of `acube ℓ × abox m ℓ`). -/
private lemma fibre_bound_on_abox {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Submission.BoseGases.acube ℓ,
      ∀ r ∈ Submission.BoseGases.abox m ℓ, |Φ (Submission.BoseGases.kcInsN m i (z, r))| ≤ C := by
  have hK : IsCompact (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.abox m ℓ) :=
    (Submission.BoseGases.acube_compact hℓ).prod (Work.UBBInputs9.B.abox_isCompact m ℓ)
  have hcont : Continuous (fun q : ℝ³ × Submission.BoseGases.X m =>
      Φ (Submission.BoseGases.kcInsN m i q)) := hΦ.comp (continuous_kcInsN_pair' i)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz r hr
  have hmem : (z, r) ∈ Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.abox m ℓ := ⟨hz, hr⟩
  have h1 : ‖Φ (Submission.BoseGases.kcInsN m i (z, r))‖ ≤ C := hC (z, r) hmem
  rw [Real.norm_eq_abs] at h1
  exact le_trans h1 (le_max_left _ _)

/-- **The crude `L¹` Fourier estimate**, with the bound on `bsQ` only *on the cube*: if
`|bsQ ℓ 0 ψ| ≤ D` on `acube ℓ` then `‖kinFT (χ_ℓ · Q_ℓ ψ) p‖ ≤ chiSup · D · ℓ³`. -/
private lemma kinFT_window_bound {ℓ D : ℝ} (hℓ : 0 < ℓ) (hD : 0 ≤ D) {ψ : ℝ³ → ℝ}
    (hψ : ∀ z ∈ Submission.BoseGases.acube ℓ, |Work.BSKinetic.bsQ ℓ 0 ψ z| ≤ D) (p : ℝ³) :
    ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
        (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BSKinetic.bsQ ℓ 0 ψ z : ℂ)) p‖
      ≤ Submission.BoseGases.chiSup * D * ℓ ^ 3 := by
  have hnorm : ∀ y : ℝ³,
      ‖(Work.BSKinetic.bsWin ℓ 0 y : ℂ) * (Work.BSKinetic.bsQ ℓ 0 ψ y : ℂ)‖
        = |Work.BSKinetic.bsWin ℓ 0 y| * |Work.BSKinetic.bsQ ℓ 0 ψ y| := by
    intro y
    rw [Complex.norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have hft : ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
        (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BSKinetic.bsQ ℓ 0 ψ z : ℂ)) p‖
      ≤ ∫ y : ℝ³, ‖(Work.BSKinetic.bsWin ℓ 0 y : ℂ) * (Work.BSKinetic.bsQ ℓ 0 ψ y : ℂ)‖ := by
    rw [Submission.BoseGases.kinFT]
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq ?_
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(Complex.I * (inner ℝ p y : ℂ))).re = 0 := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero, one_mul]
  have hInt : Integrable ((Submission.BoseGases.acube ℓ).indicator
      (fun _ : ℝ³ => Submission.BoseGases.chiSup * D)) := by
    rw [MeasureTheory.integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)]
    refine MeasureTheory.integrableOn_const
      (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓ.le)) ?_
    rw [enorm_mul]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  have hval : ∫ y : ℝ³, (Submission.BoseGases.acube ℓ).indicator
      (fun _ => Submission.BoseGases.chiSup * D) y = Submission.BoseGases.chiSup * D * ℓ ^ 3 := by
    rw [MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ),
      MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
      Submission.BoseGases.acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)]
    ring
  have hpt : ∀ y : ℝ³,
      ‖(Work.BSKinetic.bsWin ℓ 0 y : ℂ) * (Work.BSKinetic.bsQ ℓ 0 ψ y : ℂ)‖
        ≤ (Submission.BoseGases.acube ℓ).indicator (fun _ => Submission.BoseGases.chiSup * D) y := by
    intro y
    by_cases hy : y ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hy, hnorm y, bsWin_zero_eq]
      exact mul_le_mul (Submission.BoseGases.abs_chiScale_le_chiSup ℓ y) (hψ y hy) (abs_nonneg _)
        (le_of_lt Submission.BoseGases.chiSup_pos)
    · rw [Set.indicator_of_notMem hy]
      have hz : Submission.BoseGases.chiScale ℓ y = 0 := by
        by_contra h
        exact hy (Submission.BoseGases.chiScale_mem_acube hℓ h)
      rw [hnorm y, bsWin_zero_eq, hz, abs_zero, zero_mul]
  calc ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
        (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BSKinetic.bsQ ℓ 0 ψ z : ℂ)) p‖
      ≤ ∫ y : ℝ³, ‖(Work.BSKinetic.bsWin ℓ 0 y : ℂ) * (Work.BSKinetic.bsQ ℓ 0 ψ y : ℂ)‖ := hft
    _ ≤ ∫ y : ℝ³, (Submission.BoseGases.acube ℓ).indicator
          (fun _ => Submission.BoseGases.chiSup * D) y :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => norm_nonneg _) hInt
          (Filter.Eventually.of_forall hpt)
    _ = Submission.BoseGases.chiSup * D * ℓ ^ 3 := hval

/-! ## 2. The pointwise bound -/

/-- **`FibKTLeConstOnAbox`**: `fibKT ℓ Φ i` is uniformly bounded on the box `abox m ℓ`. -/
theorem fibKT_le_const_on_abox {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
      ∀ p : EuclideanSpace ℝ (Fin 3), Work.BoseBox.fibKT ℓ Φ i r p ≤ K := by
  obtain ⟨C, hC0, hC⟩ := fibre_bound_on_abox hℓ hΦ i
  refine ⟨(Submission.BoseGases.chiSup * (2 * C) * ℓ ^ 3) ^ 2, sq_nonneg _, ?_⟩
  intro r hr p
  have hQ : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |Work.BSKinetic.bsQ ℓ 0 (fun w : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (w, r))) z|
        ≤ 2 * C := by
    intro z hz
    have hm : |Work.BSKinetic.bsMean ℓ 0
        (fun w : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (w, r)))| ≤ C :=
      bsMean_abs_le_of_bound hℓ hC0 (fun w hw => hC w hw r hr)
    have hrw : Work.BSKinetic.bsQ ℓ 0 (fun w : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (w, r))) z
        = Φ (Submission.BoseGases.kcInsN m i (z, r))
          - Work.BSKinetic.bsMean ℓ 0
              (fun w : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (w, r))) := rfl
    rw [hrw]
    calc |Φ (Submission.BoseGases.kcInsN m i (z, r))
            - Work.BSKinetic.bsMean ℓ 0
                (fun w : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (w, r)))|
        ≤ |Φ (Submission.BoseGases.kcInsN m i (z, r))|
          + |Work.BSKinetic.bsMean ℓ 0
                (fun w : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (w, r)))| := abs_sub _ _
      _ ≤ C + C := add_le_add (hC z hz r hr) hm
      _ = 2 * C := by ring
  have hb := kinFT_window_bound hℓ (show (0 : ℝ) ≤ 2 * C by linarith) hQ p
  calc Work.BoseBox.fibKT ℓ Φ i r p
      = ‖Submission.BoseGases.kinFT (fun z : ℝ³ =>
          (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BSKinetic.bsQ ℓ 0
            (fun w : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (w, r))) z : ℂ)) p‖ ^ 2 := rfl
    _ ≤ (Submission.BoseGases.chiSup * (2 * C) * ℓ ^ 3) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2

/-! ## 3. The `p`-`lintegral` bound (Plancherel) -/

/-- **`FibKTLintegralLeOnAbox`**: the `p`-`lintegral` of `fibKT ℓ Φ i r ·` is uniformly bounded
on the box `abox m ℓ`. -/
theorem fibKT_lintegral_le_on_abox {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
      ∫⁻ p : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (Work.BoseBox.fibKT ℓ Φ i r p)
        ≤ ENNReal.ofReal K := by
  obtain ⟨C, hC0, hC⟩ := fibre_bound_on_abox hℓ hΦ i
  set Msq : ℝ := Submission.BoseGases.chiSup * (2 * C) with hMsq
  have hMsq0 : 0 ≤ Msq := by
    rw [hMsq]; exact mul_nonneg (le_of_lt Submission.BoseGases.chiSup_pos) (by linarith)
  have hπ0 : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
  refine ⟨(2 * Real.pi) ^ 3 * Msq ^ 2 * ℓ ^ 3, ?_, ?_⟩
  · have h1 : (0 : ℝ) < ℓ ^ 3 := by positivity
    positivity
  · intro r hr
    set ψ : ℝ³ → ℝ := fun z => Φ (Submission.BoseGases.kcInsN m i (z, r)) with hψ
    have hψb : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ C := by
      intro z hz
      rw [hψ]
      exact hC z hz r hr
    have hmean : |Work.BSKinetic.bsMean ℓ 0 ψ| ≤ C := bsMean_abs_le_of_bound hℓ hC0 hψb
    have hQb : ∀ z ∈ Submission.BoseGases.acube ℓ, |Work.BSKinetic.bsQ ℓ 0 ψ z| ≤ 2 * C := by
      intro z hz
      simp only [Work.BSKinetic.bsQ]
      calc |ψ z - Work.BSKinetic.bsMean ℓ 0 ψ|
          ≤ |ψ z| + |Work.BSKinetic.bsMean ℓ 0 ψ| := abs_sub _ _
        _ ≤ C + C := add_le_add (hψb z hz) hmean
        _ = 2 * C := by ring
    have hψ_cont : Continuous ψ := by
      rw [hψ]
      exact hΦ.comp ((continuous_kcInsN_pair' i).comp (continuous_id.prodMk continuous_const))
    set u : ℝ³ → ℝ := fun z => Work.BSKinetic.bsWin ℓ 0 z * Work.BSKinetic.bsQ ℓ 0 ψ z with hu
    have hu_cont : Continuous u := by
      have hwin : Continuous (fun z : ℝ³ => Work.BSKinetic.bsWin ℓ 0 z) := by
        rw [show (fun z : ℝ³ => Work.BSKinetic.bsWin ℓ 0 z) = Submission.BoseGases.chiScale ℓ from
          funext fun z => bsWin_zero_eq ℓ z]
        exact Submission.BoseGases.chiScale_continuous ℓ
      have hq : Continuous (fun z : ℝ³ => Work.BSKinetic.bsQ ℓ 0 ψ z) := by
        rw [show (fun z : ℝ³ => Work.BSKinetic.bsQ ℓ 0 ψ z)
            = fun z : ℝ³ => ψ z - Work.BSKinetic.bsMean ℓ 0 ψ from funext fun z => rfl]
        exact hψ_cont.sub continuous_const
      rw [hu]
      exact hwin.mul hq
    have hu_supp : ∀ z : ℝ³, z ∉ Submission.BoseGases.acube ℓ → u z = 0 := by
      intro z hz
      simp only [hu]
      have h0 : Work.BSKinetic.bsWin ℓ 0 z = 0 := by
        rw [bsWin_zero_eq]
        by_contra hc
        exact hz (Submission.BoseGases.chiScale_mem_acube hℓ hc)
      rw [h0, zero_mul]
    have hu_bound : ∀ z : ℝ³, |u z| ≤ Msq := by
      intro z
      by_cases hz : z ∈ Submission.BoseGases.acube ℓ
      · rw [hu, abs_mul]
        have hw : |Work.BSKinetic.bsWin ℓ 0 z| ≤ Submission.BoseGases.chiSup := by
          rw [bsWin_zero_eq]
          exact Submission.BoseGases.abs_chiScale_le_chiSup ℓ z
        calc |Work.BSKinetic.bsWin ℓ 0 z| * |Work.BSKinetic.bsQ ℓ 0 ψ z|
            ≤ Submission.BoseGases.chiSup * (2 * C) :=
              mul_le_mul hw (hQb z hz) (abs_nonneg _)
                (le_of_lt Submission.BoseGases.chiSup_pos)
          _ = Msq := hMsq.symm
      · rw [hu_supp z hz, abs_zero]; exact hMsq0
    have hF_cont : Continuous (fun z : ℝ³ => (u z : ℂ)) := Complex.continuous_ofReal.comp hu_cont
    have hF_supp : ∀ z : ℝ³, z ∉ Submission.BoseGases.acube ℓ → (u z : ℂ) = 0 := by
      intro z hz
      rw [hu_supp z hz, Complex.ofReal_zero]
    have hF_compact : HasCompactSupport (fun z : ℝ³ => (u z : ℂ)) :=
      HasCompactSupport.intro (Submission.BoseGases.acube_compact hℓ) hF_supp
    have hmem1 : MeasureTheory.MemLp (fun z : ℝ³ => (u z : ℂ)) 1 (volume : Measure ℝ³) :=
      hF_cont.memLp_of_hasCompactSupport hF_compact
    have hmem2 : MeasureTheory.MemLp (fun z : ℝ³ => (u z : ℂ)) 2 (volume : Measure ℝ³) :=
      hF_cont.memLp_of_hasCompactSupport hF_compact
    obtain ⟨hInt, hpl⟩ := Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp hmem1 hmem2
    have hfib : ∀ p : ℝ³, Work.BoseBox.fibKT ℓ Φ i r p
        = ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (u z : ℂ)) p‖ ^ 2 := by
      intro p
      have hfun : (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ 0 z : ℂ) *
          (Work.BSKinetic.bsQ ℓ 0 (fun w : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (w, r))) z
            : ℂ)) = (fun z : ℝ³ => (u z : ℂ)) := by
        funext z
        rw [hu, hψ, Complex.ofReal_mul]
      simp only [Work.BoseBox.fibKT, Work.BoseBox.bOKT]
      rw [hfun]
    have hbound : ∫ x : ℝ³, ‖(u x : ℂ)‖ ^ 2 ≤ Msq ^ 2 * ℓ ^ 3 := by
      have hInt2 : Integrable ((Submission.BoseGases.acube ℓ).indicator (fun _ : ℝ³ => Msq ^ 2)) := by
        rw [MeasureTheory.integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)]
        refine MeasureTheory.integrableOn_const
          (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓ.le)) ?_
        rw [enorm_eq_nnnorm]
        exact ENNReal.coe_ne_top
      have hpt : ∀ x : ℝ³, ‖(u x : ℂ)‖ ^ 2
          ≤ (Submission.BoseGases.acube ℓ).indicator (fun _ => Msq ^ 2) x := by
        intro x
        by_cases hx : x ∈ Submission.BoseGases.acube ℓ
        · rw [Set.indicator_of_mem hx]
          have hux := hu_bound x
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hux 2
        · rw [Set.indicator_of_notMem hx, hu_supp x hx, Complex.ofReal_zero, norm_zero]
          norm_num
      have hval : ∫ x : ℝ³, (Submission.BoseGases.acube ℓ).indicator (fun _ => Msq ^ 2) x
          = Msq ^ 2 * ℓ ^ 3 := by
        rw [MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ),
          MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def,
          Submission.BoseGases.acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)]
        ring
      calc ∫ x : ℝ³, ‖(u x : ℂ)‖ ^ 2
          ≤ ∫ x : ℝ³, (Submission.BoseGases.acube ℓ).indicator (fun _ => Msq ^ 2) x :=
            MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _))
              hInt2 (Filter.Eventually.of_forall hpt)
        _ = Msq ^ 2 * ℓ ^ 3 := hval
    calc ∫⁻ p : ℝ³, ENNReal.ofReal (Work.BoseBox.fibKT ℓ Φ i r p)
        = ∫⁻ p : ℝ³, ENNReal.ofReal
            (‖Submission.BoseGases.kinFT (fun z : ℝ³ => (u z : ℂ)) p‖ ^ 2) :=
          MeasureTheory.lintegral_congr (fun p => by rw [hfib p])
      _ = ENNReal.ofReal (∫ p : ℝ³,
            ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (u z : ℂ)) p‖ ^ 2) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
            (Filter.Eventually.of_forall (fun p => sq_nonneg _))).symm
      _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * Msq ^ 2 * ℓ ^ 3) := by
          apply ENNReal.ofReal_le_ofReal
          have hI : ∫ p : ℝ³, ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (u z : ℂ)) p‖ ^ 2
              = (2 * Real.pi) ^ 3 * ∫ x : ℝ³, ‖(u x : ℂ)‖ ^ 2 := by
            have h1 : (2 * Real.pi) ^ 3 * (((2 * Real.pi) ^ 3)⁻¹ *
                ∫ p : ℝ³, ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (u z : ℂ)) p‖ ^ 2)
                = ∫ p : ℝ³, ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (u z : ℂ)) p‖ ^ 2 := by
              rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hπ0), one_mul]
            rw [hpl] at h1
            exact h1.symm
          rw [hI]
          calc (2 * Real.pi) ^ 3 * ∫ x : ℝ³, ‖(u x : ℂ)‖ ^ 2
              ≤ (2 * Real.pi) ^ 3 * (Msq ^ 2 * ℓ ^ 3) :=
                mul_le_mul_of_nonneg_left hbound (le_of_lt hπ0)
            _ = (2 * Real.pi) ^ 3 * Msq ^ 2 * ℓ ^ 3 := by ring

/-! ## 4. Joint continuity -/

/-- **Joint continuity of the box fibre density** `(r,p) ↦ fibKT ℓ Φ i r p`. -/
theorem continuous_uncurry_fibKT {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    Continuous (Function.uncurry (Work.BoseBox.fibKT ℓ Φ i)) := by
  -- the fibre `(r,z) ↦ Φ(kcInsN m i (z,r))` is jointly continuous
  have hfib : Continuous (fun q : Submission.BoseGases.X m × ℝ³ =>
      Φ (Submission.BoseGases.kcInsN m i (q.2, q.1))) :=
    hΦ.comp ((continuous_kcInsN_pair' i).comp (continuous_snd.prodMk continuous_fst))
  -- the box mean of the fibre is continuous in `r`
  have hmean : Continuous (fun r : Submission.BoseGases.X m =>
      Work.BSKinetic.bsMean ℓ 0 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, r)))) := by
    have h1 : Continuous (fun r : Submission.BoseGases.X m =>
        ∫ z in Submission.BoseGases.acube ℓ, Φ (Submission.BoseGases.kcInsN m i (z, r))) :=
      continuous_parametric_integral_of_continuous (μ := (volume : Measure ℝ³))
        (f := fun (r : Submission.BoseGases.X m) (z : ℝ³) =>
          Φ (Submission.BoseGases.kcInsN m i (z, r)))
        (by exact hfib)
        (Submission.BoseGases.acube_compact hℓ)
    simpa only [Work.BSKinetic.bsMean, smul_zero, zero_add] using h1.const_mul ((ℓ ^ 3)⁻¹)
  -- the mean-free fibre `bsQ` is jointly continuous
  have hQ : Continuous (fun q : Submission.BoseGases.X m × ℝ³ =>
      Work.BSKinetic.bsQ ℓ 0 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, q.1))) q.2) := by
    simp only [Work.BSKinetic.bsQ]
    exact hfib.sub (hmean.comp continuous_fst)
  -- joint continuity of the windowed Fourier integral
  have hFT : Continuous (fun q : Submission.BoseGases.X m × ℝ³ =>
      ∫ y in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.chiScale ℓ y : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ q.2 y : ℂ))) *
          (Work.BSKinetic.bsQ ℓ 0 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, q.1))) y : ℂ)
      ) := by
    refine continuous_parametric_integral_of_continuous (μ := (volume : Measure ℝ³))
      (f := fun (q : Submission.BoseGases.X m × ℝ³) (y : ℝ³) =>
        (Submission.BoseGases.chiScale ℓ y : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ q.2 y : ℂ))) *
          (Work.BSKinetic.bsQ ℓ 0 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, q.1))) y : ℂ))
      ?_ (Submission.BoseGases.acube_compact hℓ)
    have hχ : Continuous (fun w : (Submission.BoseGases.X m × ℝ³) × ℝ³ =>
        (Submission.BoseGases.chiScale ℓ w.2 : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd)
    have hexp : Continuous (fun w : (Submission.BoseGases.X m × ℝ³) × ℝ³ =>
        Complex.exp (-(Complex.I * (inner ℝ w.1.2 w.2 : ℂ)))) :=
      Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp
        (Continuous.inner continuous_fst.snd continuous_snd))).neg)
    have hQw : Continuous (fun w : (Submission.BoseGases.X m × ℝ³) × ℝ³ =>
        (Work.BSKinetic.bsQ ℓ 0 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, w.1.1))) w.2
          : ℂ)) :=
      Complex.continuous_ofReal.comp (hQ.comp (continuous_fst.fst.prodMk continuous_snd))
    exact (hχ.mul hexp).mul hQw
  -- the identity `fibKT = ‖that integral‖²`
  have hkin : ∀ q : Submission.BoseGases.X m × ℝ³,
      Submission.BoseGases.kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ 0 z : ℂ) *
          (Work.BSKinetic.bsQ ℓ 0 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, q.1))) z
            : ℂ)) q.2
        = ∫ y in Submission.BoseGases.acube ℓ,
            (Submission.BoseGases.chiScale ℓ y : ℂ) *
              Complex.exp (-(Complex.I * (inner ℝ q.2 y : ℂ))) *
              (Work.BSKinetic.bsQ ℓ 0
                (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, q.1))) y : ℂ) := by
    intro q
    calc Submission.BoseGases.kinFT (fun z : ℝ³ => (Work.BSKinetic.bsWin ℓ 0 z : ℂ) *
          (Work.BSKinetic.bsQ ℓ 0 (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, q.1))) z
            : ℂ)) q.2
        = ∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ q.2 y : ℂ))) *
            ((Submission.BoseGases.chiScale ℓ y : ℂ) *
              (Work.BSKinetic.bsQ ℓ 0
                (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, q.1))) y : ℂ)) := by
          rw [Submission.BoseGases.kinFT]
          exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by
            beta_reduce
            rw [bsWin_zero_eq ℓ y]))
      _ = ∫ y : ℝ³, (Submission.BoseGases.chiScale ℓ y : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ q.2 y : ℂ))) *
            (Work.BSKinetic.bsQ ℓ 0
              (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, q.1))) y : ℂ) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))
      _ = ∫ y in Submission.BoseGases.acube ℓ, (Submission.BoseGases.chiScale ℓ y : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ q.2 y : ℂ))) *
            (Work.BSKinetic.bsQ ℓ 0
              (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, q.1))) y : ℂ) :=
          (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
            (s := Submission.BoseGases.acube ℓ) (fun y hy => by
              have h0 : Submission.BoseGases.chiScale ℓ y = 0 := by
                by_contra hc
                exact hy (Submission.BoseGases.chiScale_mem_acube hℓ hc)
              rw [h0]; simp)).symm
  have hgoal : (Function.uncurry (Work.BoseBox.fibKT ℓ Φ i))
      = fun q : Submission.BoseGases.X m × ℝ³ =>
        ‖(∫ y in Submission.BoseGases.acube ℓ,
            (Submission.BoseGases.chiScale ℓ y : ℂ) *
              Complex.exp (-(Complex.I * (inner ℝ q.2 y : ℂ))) *
              (Work.BSKinetic.bsQ ℓ 0
                (fun z : ℝ³ => Φ (Submission.BoseGases.kcInsN m i (z, q.1))) y : ℂ))‖ ^ 2 := by
    funext q
    simp only [Function.uncurry, Work.BoseBox.fibKT, Work.BoseBox.bOKT]
    rw [hkin q]
  rw [hgoal]
  exact (hFT.norm).pow 2

/-! ## 5. The target -/

theorem FibKTBoxFacts {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
        ∀ p : EuclideanSpace ℝ (Fin 3), Work.BoseBox.fibKT ℓ Φ i r p ≤ K)
      ∧ (∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
          ∫⁻ p : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal (Work.BoseBox.fibKT ℓ Φ i r p)
            ≤ ENNReal.ofReal K)
      ∧ Continuous (Function.uncurry (Work.BoseBox.fibKT ℓ Φ i)) :=
  ⟨fibKT_le_const_on_abox hℓ hΦ i, fibKT_lintegral_le_on_abox hℓ hΦ i,
    continuous_uncurry_fibKT hℓ hΦ i⟩

end Work.BoseFixR
