import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.integral_mul_pd_eq_neg
import Submission.Work.Diff.STE.GN.ibp_rpow
import Submission.Work.Diff.STE.fourierCoeff_iterate_pd
import Submission.Work.Diff.STE.GN.tendsto_integral_rpow_add_sq_clean

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Periodic integration by parts with a real power: the complex-valued form

For a `ℂ`-valued `C^∞` `1`-periodic function `g` on the unit torus `ι → ℝ` and a real exponent
`p ≥ 2`,

`∫_{cube} ‖∂ᵢ g‖^p ≤ (p-1) ∫_{cube} ‖g‖ · ‖∂ᵢ g‖^{p-2} · ‖∂ᵢ∂ᵢ g‖`,

where `∂ᵢ = pd i` is the directional derivative along `eᵢ`.

The proof uses the `ε`-regularisation `F_ε = (‖∂ᵢg‖² + ε²)^{(p-2)/2} • conj(∂ᵢg)` (which is smooth,
the base `‖∂ᵢg‖² + ε² ≥ ε²` being bounded away from `0`), the complex integration by parts
`integral_mul_pd_eq_neg`, the pointwise derivative bound
`‖∂ᵢ F_ε‖ ≤ (p-1) (‖∂ᵢg‖² + ε²)^{(p-2)/2} ‖∂ᵢ∂ᵢg‖`, and finally dominated convergence `ε → 0⁺`.

## Main statement

* `Work.Diff.STE.GN.ibpRpowComplexClean`
-/

namespace Work.Diff.STE.GN

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `(r^2)^s = r^(2s)` for `r ≥ 0`. -/
lemma rpow_sq_eq (r s : ℝ) (hr : 0 ≤ r) : (r ^ 2) ^ s = r ^ (2 * s) := by
  rw [← Real.rpow_natCast r 2, Nat.cast_ofNat]
  rw [← Real.rpow_mul hr (2 : ℝ) s]

/-- `(r^2)^((p-2)/2) = r^(p-2)` for `r ≥ 0`. -/
lemma rpow_sq_half (p r : ℝ) (hr : 0 ≤ r) : (r ^ 2) ^ ((p - 2) / 2) = r ^ (p - 2) := by
  rw [rpow_sq_eq r ((p - 2) / 2) hr]
  congr 1
  ring

/-- `r^(p-2) * r^2 = r^p` for `r ≥ 0` and `p ≠ 0`. -/
lemma rpow_sub_two_mul_sq (p r : ℝ) (hp : p ≠ 0) (hr : 0 ≤ r) : r ^ (p - 2) * r ^ 2 = r ^ p := by
  rw [← Real.rpow_natCast r 2, Nat.cast_ofNat]
  rw [← Real.rpow_add' hr (by intro h; exact hp (by linarith))]
  congr 1
  ring

/-- A continuous real-valued function is integrable on the unit cube. -/
lemma integrableOn_unitCube_of_continuous_real {F : (ι → ℝ) → ℝ} (hF : Continuous F) :
    Integrable F (volume.restrict (unitCube (ι := ι))) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : unitCube ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC hF.continuousOn).mono_set hsub

/-- The `ε`-regularised "conjugate derivative" `y ↦ (‖w y‖² + ε²)^s • conj(w y)` is `C^∞`. -/
lemma contDiff_rpow_normSq_smul_star (s ε : ℝ) (hε : 0 < ε) (w : (ι → ℝ) → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : ι → ℝ => ((‖w y‖ ^ 2 + ε ^ 2) ^ s) • (starRingEnd ℂ) (w y)) := by
  have hpos : ∀ y : ι → ℝ, (‖w y‖ ^ 2 + ε ^ 2) ≠ 0 := by intro y; positivity
  have hθ : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => ‖w y‖ ^ 2 + ε ^ 2) :=
    (hw.norm_sq (𝕜 := ℂ)).add contDiff_const
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => (starRingEnd ℂ) (w y)) := by
    have h := (Complex.conjCLE.contDiff (n := (⊤ : ℕ∞))).comp hw
    simpa only [Function.comp_def, Complex.conjCLE_apply] using h
  exact (hθ.rpow_const_of_ne hpos).smul hc

/-- The `ε`-regularised "conjugate derivative" inherits `1`-periodicity in the direction `i`. -/
lemma periodicIn_rpow_normSq_smul_star (i : ι) (s ε : ℝ) (w : (ι → ℝ) → ℂ)
    (hwper : PeriodicIn i w) :
    PeriodicIn i (fun y : ι → ℝ => ((‖w y‖ ^ 2 + ε ^ 2) ^ s) • (starRingEnd ℂ) (w y)) := by
  intro x
  show ((‖w (x + Pi.single i 1)‖ ^ 2 + ε ^ 2) ^ s) • (starRingEnd ℂ) (w (x + Pi.single i 1))
      = ((‖w x‖ ^ 2 + ε ^ 2) ^ s) • (starRingEnd ℂ) (w x)
  rw [hwper x]

/-- Scalar arithmetic for the derivative bound. -/
private lemma arith_bound (s ε p q r : ℝ) (hs : 0 ≤ s) (hε : 0 < ε)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : |r| ≤ p * q) :
    (p ^ 2 + ε ^ 2) ^ s * q + s * (p ^ 2 + ε ^ 2) ^ (s - 1) * |(2 : ℕ) • r| * p
      ≤ (2 * s + 1) * (p ^ 2 + ε ^ 2) ^ s * q := by
  have hC : 0 < p ^ 2 + ε ^ 2 := by positivity
  have hCsm : 0 ≤ (p ^ 2 + ε ^ 2) ^ (s - 1) := Real.rpow_nonneg (le_of_lt hC) _
  have hxsq : p ^ 2 ≤ p ^ 2 + ε ^ 2 := le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ ε ^ 2)
  have hpow : (p ^ 2 + ε ^ 2) ^ (s - 1) * (p ^ 2 + ε ^ 2) = (p ^ 2 + ε ^ 2) ^ s := by
    rw [Real.rpow_sub_one (ne_of_gt hC)]
    field_simp
  have hr' : |r| * p ≤ (p ^ 2 + ε ^ 2) * q := by
    calc |r| * p ≤ (p * q) * p := mul_le_mul_of_nonneg_right hr hp
      _ = q * p ^ 2 := by ring
      _ ≤ q * (p ^ 2 + ε ^ 2) := mul_le_mul_of_nonneg_left hxsq hq
      _ = (p ^ 2 + ε ^ 2) * q := by ring
  have h2r : |(2 : ℕ) • r| ≤ 2 * |r| := by
    have h : |(2 : ℕ) • r| = 2 * |r| := by
      rw [two_nsmul, ← two_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact le_of_eq h
  have hstep : |(2 : ℕ) • r| * p ≤ 2 * ((p ^ 2 + ε ^ 2) * q) := by
    calc |(2 : ℕ) • r| * p ≤ (2 * |r|) * p := mul_le_mul_of_nonneg_right h2r hp
      _ = 2 * (|r| * p) := by ring
      _ ≤ 2 * ((p ^ 2 + ε ^ 2) * q) := mul_le_mul_of_nonneg_left hr' (by norm_num)
  have hmain : s * (p ^ 2 + ε ^ 2) ^ (s - 1) * |(2 : ℕ) • r| * p
      ≤ 2 * s * (p ^ 2 + ε ^ 2) ^ s * q := by
    calc s * (p ^ 2 + ε ^ 2) ^ (s - 1) * |(2 : ℕ) • r| * p
        = (s * (p ^ 2 + ε ^ 2) ^ (s - 1)) * (|(2 : ℕ) • r| * p) := by ring
      _ ≤ (s * (p ^ 2 + ε ^ 2) ^ (s - 1)) * (2 * ((p ^ 2 + ε ^ 2) * q)) :=
          mul_le_mul_of_nonneg_left hstep (mul_nonneg hs hCsm)
      _ = 2 * s * ((p ^ 2 + ε ^ 2) ^ (s - 1) * (p ^ 2 + ε ^ 2)) * q := by ring
      _ = 2 * s * (p ^ 2 + ε ^ 2) ^ s * q := by rw [hpow]
  have hgoal : (2 * s + 1) * (p ^ 2 + ε ^ 2) ^ s * q
      = (p ^ 2 + ε ^ 2) ^ s * q + 2 * s * (p ^ 2 + ε ^ 2) ^ s * q := by ring
  rw [hgoal]
  exact add_le_add (le_refl _) hmain

/-- **Derivative bound for the `ε`-regularised conjugate derivative.**  For a smooth
`w : (ι → ℝ) → ℂ`, `s ≥ 0`, `ε > 0` and every `x`,

`‖∂ᵢ ((‖w‖² + ε²)^s • conj(w)) x‖ ≤ (2s+1) (‖w x‖² + ε²)^s ‖∂ᵢ w x‖`. -/
private theorem norm_pd_rpow_smul_star_bound (i : ι) (s ε : ℝ)
    (hs : 0 ≤ s) (hε : 0 < ε) (w : (ι → ℝ) → ℂ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : ι → ℝ) :
    ‖Work.Diff.STE.pd i
        (fun y : ι → ℝ => ((‖w y‖ ^ 2 + ε ^ 2) ^ s) • (starRingEnd ℂ) (w y)) x‖
      ≤ (2 * s + 1) * ((‖w x‖ ^ 2 + ε ^ 2) ^ s) * ‖Work.Diff.STE.pd i w x‖ := by
  have hC : 0 < ‖w x‖ ^ 2 + ε ^ 2 := by positivity
  have hCs : 0 ≤ (‖w x‖ ^ 2 + ε ^ 2) ^ s := Real.rpow_nonneg (le_of_lt hC) s
  have hCsm : 0 ≤ (‖w x‖ ^ 2 + ε ^ 2) ^ (s - 1) := Real.rpow_nonneg (le_of_lt hC) _
  have hwd : DifferentiableAt ℝ w x := (hw.differentiable (by simp)).differentiableAt
  have hwfd : HasFDerivAt w (fderiv ℝ w x) x := hwd.hasFDerivAt
  -- derivative of the star factor
  have hstar : HasFDerivAt (fun y : ι → ℝ => (starRingEnd ℂ) (w y))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ w x)) x := by
    have hclm : HasFDerivAt (fun z : ℂ => Complex.conjCLE z) (Complex.conjCLE : ℂ →L[ℝ] ℂ) (w x) :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt
    have h := hclm.comp x hwfd
    simpa only [Function.comp_def, Complex.conjCLE_apply] using h
  have hstar_norm : ∀ z : ℂ, ‖(Complex.conjCLE : ℂ →L[ℝ] ℂ) z‖ = ‖z‖ := by
    intro z
    change ‖(Complex.conjCLE : ℂ ≃L[ℝ] ℂ) z‖ = ‖z‖
    rw [Complex.conjCLE_apply, starRingEnd_apply, norm_star]
  -- derivative of the real weight
  have hns : HasFDerivAt (fun y : ι → ℝ => ‖w y‖ ^ 2)
      (2 • (innerSL ℝ (w x)).comp (fderiv ℝ w x)) x := hwfd.norm_sq
  have hbase : HasFDerivAt (fun y : ι → ℝ => ‖w y‖ ^ 2 + ε ^ 2)
      (2 • (innerSL ℝ (w x)).comp (fderiv ℝ w x)) x := hns.add_const (ε ^ 2)
  have hθ : HasFDerivAt (fun y : ι → ℝ => (‖w y‖ ^ 2 + ε ^ 2) ^ s)
      ((s * (‖w x‖ ^ 2 + ε ^ 2) ^ (s - 1))
        • (2 • (innerSL ℝ (w x)).comp (fderiv ℝ w x))) x :=
    hbase.rpow_const (Or.inl (ne_of_gt hC))
  have hFd : HasFDerivAt (fun y : ι → ℝ => ((‖w y‖ ^ 2 + ε ^ 2) ^ s) • (starRingEnd ℂ) (w y))
      (((‖w x‖ ^ 2 + ε ^ 2) ^ s) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ w x))
        + ((s * (‖w x‖ ^ 2 + ε ^ 2) ^ (s - 1))
            • (2 • (innerSL ℝ (w x)).comp (fderiv ℝ w x))).smulRight
              ((starRingEnd ℂ) (w x))) x :=
    hθ.smul hstar
  have hnorm : ‖(fderiv ℝ (fun y : ι → ℝ => ((‖w y‖ ^ 2 + ε ^ 2) ^ s) • (starRingEnd ℂ) (w y)) x)
        (Pi.single i 1)‖
      ≤ (2 * s + 1) * (‖w x‖ ^ 2 + ε ^ 2) ^ s * ‖(fderiv ℝ w x) (Pi.single i 1)‖ := by
    rw [hFd.fderiv, add_apply]
    refine le_trans (norm_add_le _ _) ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, norm_smul, norm_star,
      Real.norm_eq_abs, starRingEnd_apply, hstar_norm, abs_mul,
      abs_of_nonneg hCs, abs_of_nonneg hCsm, abs_of_nonneg hs]
    exact arith_bound s ε ‖w x‖ ‖(fderiv ℝ w x) (Pi.single i 1)‖
      (inner ℝ (w x) ((fderiv ℝ w x) (Pi.single i 1))) hs hε (norm_nonneg _) (norm_nonneg _)
      (abs_real_inner_le_norm _ _)
  simpa only [Work.Diff.STE.pd] using hnorm

/-- **Periodic integration by parts with a real power, complex-valued form.**  For a `ℂ`-valued
`C^∞` `1`-periodic `g` on the unit torus `ι → ℝ` and a real exponent `p ≥ 2`,

`∫_{cube} ‖∂ᵢ g‖^p ≤ (p-1) ∫_{cube} ‖g‖ · ‖∂ᵢ g‖^{p-2} · ‖∂ᵢ∂ᵢ g‖`. -/
theorem ibpRpowComplexClean {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (p : ℝ) (hp : 2 ≤ p)
    (g : (ι → ℝ) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hper : Work.Diff.STE.Periodic1 g) :
    ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i g x‖ ^ p
      ≤ (p - 1) * ∫ x in Work.Diff.STE.unitCube (ι := ι),
          ‖g x‖ * ‖Work.Diff.STE.pd i g x‖ ^ (p - 2)
            * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i g) x‖ := by
  set s : ℝ := (p - 2) / 2 with hs_def
  have hs : 0 ≤ s := by rw [hs_def]; linarith
  set w : (ι → ℝ) → ℂ := Work.Diff.STE.pd i g with hw_def
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := by
    rw [hw_def]; exact contDiff_pd_of_contDiff_top hg
  have hwper : PeriodicIn i w := by
    rw [hw_def]; exact periodicIn_pd (fun x => hper i x)
  have hw' : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd i w) := contDiff_pd_of_contDiff_top hw
  have hg1 : ContDiff ℝ 1 g := hg.of_le (WithTop.coe_le_coe.mpr le_top)
  have hgper : PeriodicIn i g := fun x => hper i x
  -- continuity / nonnegativity of the two weight families
  have hNc : Continuous (fun x : ι → ℝ => ‖w x‖ ^ 2) := (hw.continuous.norm).pow 2
  have hMc : Continuous (fun x : ι → ℝ => ‖g x‖ * ‖Work.Diff.STE.pd i w x‖) :=
    hg.continuous.norm.mul hw'.continuous.norm
  have hN0 : ∀ x : ι → ℝ, 0 ≤ ‖w x‖ ^ 2 := fun x => by positivity
  have hM0 : ∀ x : ι → ℝ, 0 ≤ ‖g x‖ * ‖Work.Diff.STE.pd i w x‖ := fun x => by positivity
  -- ## The key inequality, for each `ε > 0`
  have key : ∀ ε : ℝ, 0 < ε →
      ∫ x in Work.Diff.STE.unitCube, (‖w x‖ ^ 2 + ε ^ 2) ^ s * ‖w x‖ ^ 2
        ≤ (p - 1) * ∫ x in Work.Diff.STE.unitCube,
            (‖w x‖ ^ 2 + ε ^ 2) ^ s * (‖g x‖ * ‖Work.Diff.STE.pd i w x‖) := by
    intro ε hε
    set F : (ι → ℝ) → ℂ :=
      fun y => ((‖w y‖ ^ 2 + ε ^ 2) ^ s) • (starRingEnd ℂ) (w y) with hF_def
    have hFsm : ContDiff ℝ (⊤ : ℕ∞) F := by
      rw [hF_def]; exact contDiff_rpow_normSq_smul_star s ε hε w hw
    have hF1 : ContDiff ℝ 1 F := hFsm.of_le (WithTop.coe_le_coe.mpr le_top)
    have hFper : PeriodicIn i F := by
      rw [hF_def]; exact periodicIn_rpow_normSq_smul_star i s ε w hwper
    -- the pointwise value of `F x * ∂ᵢ g x`
    have hpt : ∀ x : ι → ℝ, F x * w x = ↑(((‖w x‖ ^ 2 + ε ^ 2) ^ s) * ‖w x‖ ^ 2) := by
      intro x
      rw [hF_def]
      simp only
      rw [Complex.real_smul, mul_assoc, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
    -- integration by parts
    have hIBP := integral_mul_pd_eq_neg i F g hF1 hg1 hFper hgper
    have hEq : (↑(∫ x in Work.Diff.STE.unitCube, (‖w x‖ ^ 2 + ε ^ 2) ^ s * ‖w x‖ ^ 2) : ℂ)
        = -∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.pd i F x * g x := by
      have h1 : (∫ x in Work.Diff.STE.unitCube,
            (↑((‖w x‖ ^ 2 + ε ^ 2) ^ s * ‖w x‖ ^ 2) : ℂ))
          = ↑(∫ x in Work.Diff.STE.unitCube,
              (‖w x‖ ^ 2 + ε ^ 2) ^ s * ‖w x‖ ^ 2) := integral_ofReal
      have h2 : (fun x : ι → ℝ => (↑((‖w x‖ ^ 2 + ε ^ 2) ^ s * ‖w x‖ ^ 2) : ℂ))
          =ᵐ[volume.restrict (Work.Diff.STE.unitCube (ι := ι))]
            (fun x => F x * Work.Diff.STE.pd i g x) :=
        Filter.Eventually.of_forall fun x => (hpt x).symm
      rw [← h1, ← hIBP]
      exact integral_congr_ae h2
    have hnn : 0 ≤ ∫ x in Work.Diff.STE.unitCube, (‖w x‖ ^ 2 + ε ^ 2) ^ s * ‖w x‖ ^ 2 :=
      integral_nonneg fun x => mul_nonneg (Real.rpow_nonneg (by positivity) s) (by positivity)
    have hle1 : ∫ x in Work.Diff.STE.unitCube, (‖w x‖ ^ 2 + ε ^ 2) ^ s * ‖w x‖ ^ 2
        ≤ ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i F x‖ * ‖g x‖ := by
      have hnorm : ‖(↑(∫ x in Work.Diff.STE.unitCube,
              (‖w x‖ ^ 2 + ε ^ 2) ^ s * ‖w x‖ ^ 2) : ℂ)‖
          = |∫ x in Work.Diff.STE.unitCube, (‖w x‖ ^ 2 + ε ^ 2) ^ s * ‖w x‖ ^ 2| :=
        RCLike.norm_ofReal (K := ℂ) _
      calc ∫ x in Work.Diff.STE.unitCube, (‖w x‖ ^ 2 + ε ^ 2) ^ s * ‖w x‖ ^ 2
          = ‖(↑(∫ x in Work.Diff.STE.unitCube,
                (‖w x‖ ^ 2 + ε ^ 2) ^ s * ‖w x‖ ^ 2) : ℂ)‖ :=
            (abs_of_nonneg hnn).symm.trans hnorm.symm
        _ = ‖∫ x in Work.Diff.STE.unitCube, Work.Diff.STE.pd i F x * g x‖ := by
            rw [hEq, norm_neg]
        _ ≤ ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i F x * g x‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i F x‖ * ‖g x‖ :=
            integral_congr_ae (Filter.Eventually.of_forall fun x => norm_mul _ _)
    have hle2 : ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i F x‖ * ‖g x‖
        ≤ (p - 1) * ∫ x in Work.Diff.STE.unitCube,
            (‖w x‖ ^ 2 + ε ^ 2) ^ s * (‖g x‖ * ‖Work.Diff.STE.pd i w x‖) := by
      have hpt2 : ∀ x : ι → ℝ, ‖Work.Diff.STE.pd i F x‖ * ‖g x‖
          ≤ (p - 1) * ((‖w x‖ ^ 2 + ε ^ 2) ^ s
              * (‖g x‖ * ‖Work.Diff.STE.pd i w x‖)) := by
        intro x
        have hb : ‖Work.Diff.STE.pd i F x‖
            ≤ (2 * s + 1) * ((‖w x‖ ^ 2 + ε ^ 2) ^ s) * ‖Work.Diff.STE.pd i w x‖ := by
          rw [hF_def]
          exact norm_pd_rpow_smul_star_bound i s ε hs hε w hw x
        have h2s : 2 * s + 1 = p - 1 := by rw [hs_def]; ring
        calc ‖Work.Diff.STE.pd i F x‖ * ‖g x‖
            ≤ ((2 * s + 1) * ((‖w x‖ ^ 2 + ε ^ 2) ^ s) * ‖Work.Diff.STE.pd i w x‖)
                * ‖g x‖ :=
              mul_le_mul_of_nonneg_right hb (norm_nonneg _)
          _ = (p - 1) * ((‖w x‖ ^ 2 + ε ^ 2) ^ s
                * (‖g x‖ * ‖Work.Diff.STE.pd i w x‖)) := by
              rw [h2s]; ring
      have hInt1 : Integrable (fun x : ι → ℝ => ‖Work.Diff.STE.pd i F x‖ * ‖g x‖)
          (volume.restrict Work.Diff.STE.unitCube) :=
        integrableOn_unitCube_of_continuous_real
          ((continuous_pd hF1 i).norm.mul hg.continuous.norm)
      have hInt2 : Integrable (fun x : ι → ℝ => (p - 1) * ((‖w x‖ ^ 2 + ε ^ 2) ^ s
            * (‖g x‖ * ‖Work.Diff.STE.pd i w x‖)))
          (volume.restrict Work.Diff.STE.unitCube) :=
        integrableOn_unitCube_of_continuous_real
          (continuous_const.mul (((Real.continuous_rpow_const hs).comp
            (hNc.add continuous_const)).mul hMc))
      have hmono := integral_mono_ae hInt1 hInt2 (Filter.Eventually.of_forall hpt2)
      rwa [integral_const_mul] at hmono
    calc ∫ x in Work.Diff.STE.unitCube, (‖w x‖ ^ 2 + ε ^ 2) ^ s * ‖w x‖ ^ 2
        ≤ ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pd i F x‖ * ‖g x‖ := hle1
      _ ≤ (p - 1) * ∫ x in Work.Diff.STE.unitCube,
            (‖w x‖ ^ 2 + ε ^ 2) ^ s * (‖g x‖ * ‖Work.Diff.STE.pd i w x‖) := hle2
  -- ## The limit `ε → 0⁺`
  have hlimN : Filter.Tendsto
      (fun n : ℕ => ∫ x in Work.Diff.STE.unitCube,
        (‖w x‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) ^ s * ‖w x‖ ^ 2)
      Filter.atTop
      (nhds (∫ x in Work.Diff.STE.unitCube, (‖w x‖ ^ 2) ^ s * ‖w x‖ ^ 2)) :=
    tendsto_integral_rpow_add_sq_clean s hs (fun x => ‖w x‖ ^ 2) (fun x => ‖w x‖ ^ 2)
      hNc hNc hN0 hN0
  have hlimM : Filter.Tendsto
      (fun n : ℕ => ∫ x in Work.Diff.STE.unitCube,
        (‖w x‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) ^ s * (‖g x‖ * ‖Work.Diff.STE.pd i w x‖))
      Filter.atTop
      (nhds (∫ x in Work.Diff.STE.unitCube,
        (‖w x‖ ^ 2) ^ s * (‖g x‖ * ‖Work.Diff.STE.pd i w x‖))) :=
    tendsto_integral_rpow_add_sq_clean s hs (fun x => ‖w x‖ ^ 2)
      (fun x => ‖g x‖ * ‖Work.Diff.STE.pd i w x‖) hNc hMc hN0 hM0
  have hIdL : (∫ x in Work.Diff.STE.unitCube, (‖w x‖ ^ 2) ^ s * ‖w x‖ ^ 2)
      = ∫ x in Work.Diff.STE.unitCube, ‖w x‖ ^ p := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hs_def, rpow_sq_half p ‖w x‖ (norm_nonneg _),
      rpow_sub_two_mul_sq p ‖w x‖ (by linarith) (norm_nonneg _)]
  have hIdR : (∫ x in Work.Diff.STE.unitCube,
        (‖w x‖ ^ 2) ^ s * (‖g x‖ * ‖Work.Diff.STE.pd i w x‖))
      = ∫ x in Work.Diff.STE.unitCube,
          ‖g x‖ * ‖w x‖ ^ (p - 2) * ‖Work.Diff.STE.pd i w x‖ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hs_def, rpow_sq_half p ‖w x‖ (norm_nonneg _)]
    ring
  have hlimN' : Filter.Tendsto
      (fun n : ℕ => ∫ x in Work.Diff.STE.unitCube,
        (‖w x‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) ^ s * ‖w x‖ ^ 2)
      Filter.atTop (nhds (∫ x in Work.Diff.STE.unitCube, ‖w x‖ ^ p)) := by
    rwa [hIdL] at hlimN
  have hlimM' : Filter.Tendsto
      (fun n : ℕ => (p - 1) * ∫ x in Work.Diff.STE.unitCube,
        (‖w x‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) ^ s * (‖g x‖ * ‖Work.Diff.STE.pd i w x‖))
      Filter.atTop
      (nhds ((p - 1) * ∫ x in Work.Diff.STE.unitCube,
        ‖g x‖ * ‖w x‖ ^ (p - 2) * ‖Work.Diff.STE.pd i w x‖)) := by
    have h := hlimM.const_mul (p - 1)
    rwa [hIdR] at h
  exact le_of_tendsto_of_tendsto' hlimN' hlimM' (fun n => key (1 / ((n : ℝ) + 1)) (by positivity))

end Work.Diff.STE.GN
