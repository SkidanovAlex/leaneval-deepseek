/-
Copyright: work module for the Elgindi finite-time singularity project.

# The cut-off identity for `I1`, from scratch -- de-tainted copy

This is a copy of `Submission/Work/FTS/EllipticEst/AngSecond/I1_cut_alt.lean` (whose declaration
`I1_cutoff_identity_alt` proves the `chi_n` cut-off identity for `I1` from scratch, without the
three `sorry`-carrying modules `AngSecond.{slice_nice_ibp,swap_IP_cut,swap_nice}`), with the two
type mismatches in the `ContinuousOn.mul` arguments of `integrable_uncurry_of_bound` repaired.
It is the copy consumed by `Submission.Work.FTS.EllipticEst.AngClean.I1_ibp`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AngSecond.I1_defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# The radial cut-off identity for `I₁`, from scratch

This module proves `I1_cutoff_identity_alt`, the cut-off identity

  `IP (z² ∂_z²Ψ · χ_n) (∂_θθΨ) = - ∫_z ∫_θ σ θ · nice n Ψ z θ`,

directly from the vocabulary of `I1_defs`:

* `slice_nice_ibp_alt` is the one-dimensional integration by parts at a fixed angle
  (`slice_ibp_halfline` + `pz_mul_Dv_eq_nice`),
* `swap_IP_cut_alt`, `swap_nice_alt` exchange the two iterated integrals (Fubini), the
  integrands being supported in the compact band `[1/(2(n+1)), 4(n+1)]` of `χ_n`, where they
  are dominated by `C · |σ θ|` — a product of two integrable functions.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Real ContDiff

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The open quadrant `(0,∞) × (0,π/2)`: every integrand below is continuous there (the two
weights `w²` and `σ` are singular only on its boundary). -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The lower end of the compact band on which the cut-off `χ_n` lives. -/
abbrev zlo (n : ℕ) : ℝ := 1 / (2 * (n + 1 : ℝ))

/-- The upper end of the compact band on which the cut-off `χ_n` lives. -/
abbrev zhi (n : ℕ) : ℝ := 4 * (n + 1 : ℝ)

/-- The compact band on which the cut-off `χ_n` lives. -/
abbrev band (n : ℕ) : Set ℝ := Set.Icc (zlo n) (zhi n)

theorem band_lower_pos (n : ℕ) : (0 : ℝ) < zlo n := by
  simp only [zlo]; positivity

theorem band_upper_le (n : ℕ) : zlo n ≤ zhi n := by
  have h1 : zlo n ≤ 1 := by
    simp only [zlo]
    rw [div_le_one (by positivity)]
    linarith
  have h2 : (1 : ℝ) ≤ zhi n := by
    simp only [zhi]
    have : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    linarith
  linarith

/-! ## Continuity on the open quadrant -/

theorem continuousOn_uncurry_Qd {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g) :
    ContinuousOn (Function.uncurry g) Qd := by
  refine hg.continuousOn.mono ?_
  intro p hp
  have h1 : (0 : ℝ) < p.1 := hp.1
  have h2 : (0 : ℝ) < p.2 := hp.2.1
  have h3 : p.2 < Real.pi / 2 := hp.2.2
  refine ⟨?_, ?_, ?_⟩
  · show (-1 : ℝ) < p.1
    linarith
  · show (-1 : ℝ) < p.2
    linarith
  · show p.2 < Real.pi / 2 + 1
    linarith [Real.pi_pos]

theorem continuousOn_w2_Qd : ContinuousOn (fun p : ℝ × ℝ => w2 p.1) Qd := by
  have h : ContinuousOn (fun z : ℝ => w2 z) (Set.Ioi 0) := by
    unfold w2 Work.Spaces.w
    refine ContinuousOn.pow ?_ 2
    exact ((continuous_const.add continuous_id).pow 2).continuousOn.div
      (continuous_id.pow 2).continuousOn
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  exact h.comp continuous_fst.continuousOn (fun p hp => hp.1)

theorem continuousOn_sig_Qd : ContinuousOn (fun p : ℝ × ℝ => sig p.2) Qd := by
  have h : ContinuousOn sig (Set.Ioo 0 (Real.pi / 2)) := by
    unfold sig
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro θ hθ
      exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])))
  exact h.comp continuous_snd.continuousOn (fun p hp => hp.2)

theorem continuousOn_cut_Qd (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1) Qd :=
  ((Work.FTS.EllipticEst.cut_contDiff n).continuous.comp continuous_fst).continuousOn

theorem continuousOn_deriv_cut_Qd (n : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (Work.FTS.EllipticEst.cut n) p.1) Qd :=
  ((continuous_deriv_cut n).comp continuous_fst).continuousOn

theorem continuousOn_IPS_Qd (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    ContinuousOn (fun p : ℝ × ℝ =>
        (p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2 * Work.FTS.EllipticEst.cut n p.1)
          * Work.Spaces.pthIter 2 Ψ p.1 p.2 * w2 p.1) Qd := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2) Qd := (continuous_fst.pow 2).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 Ψ p.1 p.2) Qd :=
    continuousOn_uncurry_Qd (Work.Spaces.smoothNbhd_pzIter hΨ 2)
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 Ψ p.1 p.2) Qd :=
    continuousOn_uncurry_Qd (smoothNbhd_pthIter Ψ hΨ 2)
  exact (((h1.mul h2).mul (continuousOn_cut_Qd n)).mul h3).mul continuousOn_w2_Qd

theorem continuousOn_IPS_box (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    ContinuousOn (fun p : ℝ × ℝ =>
        (p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2 * Work.FTS.EllipticEst.cut n p.1)
          * Work.Spaces.pthIter 2 Ψ p.1 p.2 * w2 p.1) (band n ×ˢ Work.Spaces.Iθ) := by
  have ha : (0 : ℝ) < zlo n := band_lower_pos n
  have h1 : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2) (band n ×ˢ Work.Spaces.Iθ) :=
    (continuous_fst.pow 2).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 Ψ p.1 p.2)
      (band n ×ˢ Work.Spaces.Iθ) :=
    continuousOn_uncurry_smoothNbhd (Work.Spaces.smoothNbhd_pzIter hΨ 2) ha
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 Ψ p.1 p.2)
      (band n ×ˢ Work.Spaces.Iθ) :=
    continuousOn_uncurry_smoothNbhd (smoothNbhd_pthIter Ψ hΨ 2) ha
  have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1)
      (band n ×ˢ Work.Spaces.Iθ) :=
    ((Work.FTS.EllipticEst.cut_contDiff n).continuous.comp continuous_fst).continuousOn
  have h5 : ContinuousOn (fun p : ℝ × ℝ => w2 p.1) (band n ×ˢ Work.Spaces.Iθ) :=
    (continuousOn_w2' ha).comp continuous_fst.continuousOn (fun p hp => hp.1)
  exact (((h1.mul h2).mul h4).mul h3).mul h5

theorem continuousOn_uncurry_nice_Qd (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    ContinuousOn (fun p : ℝ × ℝ => nice n Ψ p.1 p.2) Qd := by
  have hG : ContinuousOn (fun p : ℝ × ℝ => G Ψ p.1 p.2) Qd :=
    continuous_fst.continuousOn.mul (continuousOn_uncurry_Qd hΨ.pz)
  have hφ : ContinuousOn (fun p : ℝ × ℝ => Phi Ψ p.1 p.2) Qd :=
    continuousOn_uncurry_Qd hΨ.pth.pth
  have hH : ContinuousOn (fun p : ℝ × ℝ => H Ψ p.1 p.2) Qd :=
    continuous_fst.continuousOn.mul (continuousOn_uncurry_Qd hΨ.pth.pth.pz)
  have hw : ContinuousOn (fun p : ℝ × ℝ => w2 p.1) Qd := continuousOn_w2_Qd
  have hz : ContinuousOn (fun p : ℝ × ℝ => p.1) Qd := continuous_fst.continuousOn
  have h1z : ContinuousOn (fun p : ℝ × ℝ => (1 : ℝ) + p.1) Qd :=
    (continuous_const.add continuous_fst).continuousOn
  have hne : ∀ p ∈ Qd, (1 : ℝ) + p.1 ≠ 0 := by
    intro p hp
    have h1 : (0 : ℝ) < p.1 := hp.1
    exact ne_of_gt (by linarith)
  have h2 : ContinuousOn (fun _ : ℝ × ℝ => (2 : ℝ)) Qd := continuousOn_const
  have hfrac : ContinuousOn (fun p : ℝ × ℝ => 4 * G Ψ p.1 p.2 * Phi Ψ p.1 p.2 / (1 + p.1)) Qd :=
    ((continuousOn_const (c := (4 : ℝ)).mul hG).mul hφ).div h1z hne
  have hsum : ContinuousOn (fun p : ℝ × ℝ => 2 * G Ψ p.1 p.2 * Phi Ψ p.1 p.2
      + G Ψ p.1 p.2 * H Ψ p.1 p.2 - 4 * G Ψ p.1 p.2 * Phi Ψ p.1 p.2 / (1 + p.1)) Qd :=
    (((h2.mul hG).mul hφ).add (hG.mul hH)).sub hfrac
  have hmain : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.cut n p.1 * w2 p.1
      * (2 * G Ψ p.1 p.2 * Phi Ψ p.1 p.2 + G Ψ p.1 p.2 * H Ψ p.1 p.2
          - 4 * G Ψ p.1 p.2 * Phi Ψ p.1 p.2 / (1 + p.1))) Qd :=
    ((continuousOn_cut_Qd n).mul hw).mul hsum
  have hsec : ContinuousOn (fun p : ℝ × ℝ => w2 p.1 * (G Ψ p.1 p.2 * Phi Ψ p.1 p.2)
      * (p.1 * deriv (Work.FTS.EllipticEst.cut n) p.1)) Qd :=
    (hw.mul (hG.mul hφ)).mul (hz.mul (continuousOn_deriv_cut_Qd n))
  show ContinuousOn (fun p : ℝ × ℝ => nice n Ψ p.1 p.2) Qd
  simp only [nice]
  exact hmain.add hsec

/-! ## Integrability on the product, from compact support and a bound -/

theorem ae_mem_prod : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod
      (volume.restrict Work.Spaces.Iθ)), p.1 ∈ Work.Spaces.Iz ∧ p.2 ∈ Work.Spaces.Iθ := by
  have h : ∀ᵐ p ∂((volume : Measure ℝ).prod volume).restrict
      (Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2)),
      p ∈ Set.Ici (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    MeasureTheory.ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)
  simpa only [MeasureTheory.Measure.prod_restrict, Work.Spaces.Iz, Work.Spaces.Iθ,
    Set.mem_prod] using h

/-- A function on `Iz × Iθ` vanishing off the compact band `[a,b] × Iθ` and bounded there by
`C · |σ θ|` is integrable for the product of `volume.restrict Iz` and `volume.restrict Iθ`. -/
theorem integrable_uncurry_of_bound (F : ℝ → ℝ → ℝ) {C a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hCnn : 0 ≤ C)
    (hcont : ContinuousOn (Function.uncurry F) Qd)
    (hbound : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ, ‖F z θ‖ ≤ C * ‖sig θ‖)
    (hzero : ∀ z ∉ Set.Icc a b, ∀ θ, F z θ = 0) :
    Integrable (Function.uncurry F)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hfin : volume (Set.Icc a b) ≠ ⊤ := ne_of_lt isCompact_Icc.measure_lt_top
  have hdom1 : Integrable (fun z : ℝ => (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z)
      (volume.restrict Work.Spaces.Iz) :=
    ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (MeasureTheory.integrableOn_const (s := Set.Icc a b) (C := (1 : ℝ)) hfin (by simp))
      ).mono_measure Measure.restrict_le_self
  have hsig : Integrable sig (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.integrable_sig
  have hdom2 : Integrable (fun θ : ℝ => C * ‖sig θ‖) (volume.restrict Work.Spaces.Iθ) :=
    hsig.norm.const_mul C
  have hdom : Integrable (fun p : ℝ × ℝ =>
      (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * (C * ‖sig p.2‖))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    hdom1.mul_prod hdom2
  refine hdom.mono' (Work.Spaces.aesm_of_continuousOn_Qd _ hcont) ?_
  filter_upwards [ae_mem_prod] with p hp
  rcases hp with ⟨hp1, hp2⟩
  by_cases hmem : p.1 ∈ Set.Icc a b
  · simp only [Function.uncurry, Set.indicator_of_mem hmem, one_mul]
    exact hbound p.1 hmem p.2 hp2
  · simp only [Function.uncurry, Set.indicator_of_notMem hmem, zero_mul,
      hzero p.1 hmem p.2, norm_zero, le_refl]

/-- **Continuity on `Qd` of the `I₁`-integrand of the cut-off identity** (the pair-argument form
used by the `AngSecond` side; moved here when the two copies of this file were merged onto the
de-tainted one, 2026-10-08). -/
theorem continuousOn_IPF_Qd (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    ContinuousOn (fun p : ℝ × ℝ =>
        (p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2 * Work.FTS.EllipticEst.cut n p.1)
          * Work.Spaces.pthIter 2 Ψ p.1 p.2 * w2 p.1 * sig p.2) Qd :=
  (continuousOn_IPS_Qd n Ψ hΨ).mul continuousOn_sig_Qd

/-- **Continuity on `Qd` of `σ · nice n Ψ`** (the pair-argument form; see the note above). -/
theorem continuousOn_niceF_Qd (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    ContinuousOn (fun p : ℝ × ℝ => sig p.2 * nice n Ψ p.1 p.2) Qd :=
  continuousOn_sig_Qd.mul (continuousOn_uncurry_nice_Qd n Ψ hΨ)

/-- **Integrability on the product, for a pair-argument function vanishing off `[a,b] × Iθ` and
bounded there by `C · |σ θ|`** (the pair-argument form of `integrable_uncurry_of_bound`; see the
note above).  This is the version the `AngSecond`-side consumers use — the two statements differ
only in the shape of the argument, and the extra hypotheses `0 < a`, `a ≤ b` of
`integrable_uncurry_of_bound` are not needed here. -/
theorem integrable_prod_of_bound (g : ℝ × ℝ → ℝ) {C a b : ℝ} (hCnn : 0 ≤ C)
    (hcont : ContinuousOn g Qd)
    (hbound : ∀ p : ℝ × ℝ, p.1 ∈ Set.Icc a b → p.2 ∈ Work.Spaces.Iθ → ‖g p‖ ≤ C * ‖sig p.2‖)
    (hzero : ∀ p : ℝ × ℝ, p.1 ∉ Set.Icc a b → g p = 0) :
    Integrable g
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hfin : volume (Set.Icc a b) ≠ ⊤ := ne_of_lt isCompact_Icc.measure_lt_top
  have hdom1 : Integrable (fun z : ℝ => (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z)
      (volume.restrict Work.Spaces.Iz) :=
    ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (MeasureTheory.integrableOn_const (s := Set.Icc a b) (C := (1 : ℝ)) hfin (by simp))
      ).mono_measure Measure.restrict_le_self
  have hsig : Integrable sig (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.integrable_sig
  have hdom2 : Integrable (fun θ : ℝ => C * ‖sig θ‖) (volume.restrict Work.Spaces.Iθ) :=
    hsig.norm.const_mul C
  have hdom : Integrable (fun p : ℝ × ℝ =>
      (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * (C * ‖sig p.2‖))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    hdom1.mul_prod hdom2
  refine hdom.mono' (Work.Spaces.aesm_of_continuousOn_Qd g hcont) ?_
  filter_upwards [ae_mem_prod] with p hp
  rcases hp with ⟨hp1, hp2⟩
  by_cases hmem : p.1 ∈ Set.Icc a b
  · simp only [Set.indicator_of_mem hmem, one_mul]
    exact hbound p hmem hp2
  · simp only [Set.indicator_of_notMem hmem, zero_mul, hzero p hmem, norm_zero, le_refl]

/-! ## The one-dimensional integration by parts at a fixed angle -/

theorem slice_nice_ibp_alt (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (∫ z in Work.Spaces.Iz, nice n Ψ z θ)
      = -∫ z in Work.Spaces.Iz,
          Work.Spaces.pzIter 2 Ψ z θ
            * (z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z * w2 z) := by
  have hstep : (∫ z in Set.Ioi (0 : ℝ), nice n Ψ z θ)
      = -∫ z in Set.Ioi (0 : ℝ),
          Work.Spaces.pzIter 2 Ψ z θ
            * (z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z * w2 z) := by
    rw [show (∫ z in Set.Ioi (0 : ℝ), nice n Ψ z θ)
        = ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pz Ψ z θ * Dv n Ψ z θ from
        setIntegral_congr_fun measurableSet_Ioi
          (fun z hz => (pz_mul_Dv_eq_nice n Ψ hΨ hz hθ).symm)]
    exact slice_ibp_halfline n Ψ hΨ hθ
  have hIz1 : (∫ z in Work.Spaces.Iz, nice n Ψ z θ)
      = ∫ z in Set.Ioi (0 : ℝ), nice n Ψ z θ :=
    MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hIz2 : (∫ z in Work.Spaces.Iz,
        Work.Spaces.pzIter 2 Ψ z θ
          * (z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z * w2 z))
      = ∫ z in Set.Ioi (0 : ℝ),
        Work.Spaces.pzIter 2 Ψ z θ
          * (z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z * w2 z) :=
    MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  rw [hIz1, hIz2, hstep]

/-! ## Fubini for the two integrands -/

theorem swap_IP_cut_alt (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
            * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
      IsCompact (band n ×ˢ Work.Spaces.Iθ)).exists_bound_of_continuousOn
    (continuousOn_IPS_box n Ψ hΨ)
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC (zlo n, 0)
    ⟨⟨le_refl _, band_upper_le n⟩, by constructor <;> linarith [Real.pi_pos]⟩)
  have hzero : ∀ z ∉ band n, ∀ θ : ℝ,
      ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ) = 0 := by
    intro z hz θ
    have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    have hhalf : zlo n ≤ 1 / (n + 1 : ℝ) := by
      have h := one_div_le_one_div_of_le hn
        (show (n : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) by linarith)
      simpa only [zlo] using h
    simp only [band, Set.mem_Icc, not_and_or, not_le] at hz
    rcases hz with hzlt | hzgt
    · rw [Work.FTS.EllipticEst.cut_apply_zero_of_le n (show z ≤ 1 / (n + 1 : ℝ) by linarith)]
      ring
    · rw [Work.FTS.EllipticEst.cut_apply_zero_of_ge n (show 3 * (n + 1 : ℝ) ≤ z by linarith)]
      ring
  have hbound : ∀ z ∈ band n, ∀ θ ∈ Work.Spaces.Iθ,
      ‖(z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ‖ ≤ C * ‖sig θ‖ := by
    intro z hz θ hθ
    have h1 : ‖(z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z‖ ≤ C := hC (z, θ) ⟨hz, hθ⟩
    calc ‖(z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
            * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ‖
        = ‖(z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
            * Work.Spaces.pthIter 2 Ψ z θ * w2 z‖ * ‖sig θ‖ := norm_mul _ _
      _ ≤ C * ‖sig θ‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hf := integrable_uncurry_of_bound
    (F := fun z θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
      * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ)
    (band_lower_pos n) (band_upper_le n) hCnn
    (by
      show ContinuousOn (fun p : ℝ × ℝ =>
        (p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2 * Work.FTS.EllipticEst.cut n p.1)
          * Work.Spaces.pthIter 2 Ψ p.1 p.2 * w2 p.1 * sig p.2) Qd
      exact (continuousOn_IPS_Qd n Ψ hΨ).mul continuousOn_sig_Qd)
    hbound hzero
  exact MeasureTheory.integral_integral_swap hf

theorem swap_nice_alt (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, sig θ * nice n Ψ z θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, sig θ * nice n Ψ z θ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
      IsCompact (band n ×ˢ Work.Spaces.Iθ)).exists_bound_of_continuousOn
    (continuousOn_uncurry_nice n Ψ hΨ)
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC (zlo n, 0)
    ⟨⟨le_refl _, band_upper_le n⟩, by constructor <;> linarith [Real.pi_pos]⟩)
  have hzero : ∀ z ∉ band n, ∀ θ : ℝ, (sig θ * nice n Ψ z θ) = 0 := by
    intro z hz θ
    have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
    have hhalf : zlo n ≤ 1 / (n + 1 : ℝ) := by
      have h := one_div_le_one_div_of_le hn
        (show (n : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) by linarith)
      simpa only [zlo] using h
    simp only [band, Set.mem_Icc, not_and_or, not_le] at hz
    rcases hz with hzlt | hzgt
    · have h1 : z ≤ 1 / (n + 1 : ℝ) := by linarith
      have h2 : z < 1 / (n + 1 : ℝ) := by linarith
      rw [nice, Work.FTS.EllipticEst.cut_apply_zero_of_le n h1,
        deriv_cut_eq_zero_of_lt n h2]
      ring
    · have h1 : 3 * (n + 1 : ℝ) ≤ z := by linarith
      have h2 : 3 * (n + 1 : ℝ) < z := by linarith
      rw [nice, Work.FTS.EllipticEst.cut_apply_zero_of_ge n h1,
        deriv_cut_eq_zero_of_gt n h2]
      ring
  have hbound : ∀ z ∈ band n, ∀ θ ∈ Work.Spaces.Iθ,
      ‖sig θ * nice n Ψ z θ‖ ≤ C * ‖sig θ‖ := by
    intro z hz θ hθ
    have h1 : ‖nice n Ψ z θ‖ ≤ C := hC (z, θ) ⟨hz, hθ⟩
    calc ‖sig θ * nice n Ψ z θ‖ = ‖sig θ‖ * ‖nice n Ψ z θ‖ := norm_mul _ _
      _ ≤ ‖sig θ‖ * C := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = C * ‖sig θ‖ := by ring
  have hf := integrable_uncurry_of_bound (F := fun z θ => sig θ * nice n Ψ z θ)
    (band_lower_pos n) (band_upper_le n) hCnn
    (by
      show ContinuousOn (fun p : ℝ × ℝ => sig p.2 * nice n Ψ p.1 p.2) Qd
      exact continuousOn_sig_Qd.mul (continuousOn_uncurry_nice_Qd n Ψ hΨ)) hbound hzero
  exact MeasureTheory.integral_integral_swap hf

/-! ## The cut-off identity -/

theorem I1_cutoff_identity_alt (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ) :
    IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
        (Work.Spaces.pthIter 2 Ψ)
      = - ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, sig θ * nice n Ψ z θ := by
  rw [IP]
  calc ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
          * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
            * Work.Spaces.pthIter 2 Ψ z θ * w2 z * sig θ := swap_IP_cut_alt n Ψ hΨ
    _ = ∫ θ in Work.Spaces.Iθ,
          (∫ z in Work.Spaces.Iz,
            (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
              * Work.Spaces.pthIter 2 Ψ z θ * w2 z) * sig θ := by
        refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
        exact integral_mul_const (sig θ) _
    _ = ∫ θ in Work.Spaces.Iθ,
          -(∫ z in Work.Spaces.Iz, sig θ * nice n Ψ z θ) := by
        refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
        have h1 : (∫ z in Work.Spaces.Iz,
              (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ * Work.FTS.EllipticEst.cut n z)
                * Work.Spaces.pthIter 2 Ψ z θ * w2 z)
            = ∫ z in Work.Spaces.Iz,
                Work.Spaces.pzIter 2 Ψ z θ
                  * (z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ
                      * Work.FTS.EllipticEst.cut n z * w2 z) :=
          setIntegral_congr_fun measurableSet_Ici (fun z _ => by ring)
        have h2 : (∫ z in Work.Spaces.Iz,
              Work.Spaces.pzIter 2 Ψ z θ
                * (z ^ 2 * Work.Spaces.pthIter 2 Ψ z θ
                    * Work.FTS.EllipticEst.cut n z * w2 z))
            = -∫ z in Work.Spaces.Iz, nice n Ψ z θ := by
          rw [slice_nice_ibp_alt n Ψ hΨ hθ]
          ring
        rw [h1, h2, MeasureTheory.integral_const_mul]
        ring
    _ = -∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz, sig θ * nice n Ψ z θ := by
        rw [MeasureTheory.integral_neg]
    _ = - ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, sig θ * nice n Ψ z θ := by
        rw [swap_nice_alt n Ψ hΨ]

end Work.FTS.EllipticEst.AngSecond
