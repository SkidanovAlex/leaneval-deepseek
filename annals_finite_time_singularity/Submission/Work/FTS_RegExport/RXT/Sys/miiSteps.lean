import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS.CoercivityFix.Transfer.E2_blocks
import Submission.Work.FTS_RegExport.RXT.Sys.miiAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.mixed_integral_identity` — S5a of the RX-St1 leaf plan

The integrated identity for the six components `w_k = D_z^{j}D_θ^{i}(slice g τ)`, `(j,i) = idx k`:

  `w_k(τ₂) − w_k(τ₁) = ∫_{τ₁}^{τ₂} (D^β ∂_τ g)(σ) dσ`.

The proof is by induction on the total order `j + i ≤ 2`.  The slot `(0,0)` is the fundamental
theorem of calculus in `τ` (the dynamic equation gives the pointwise derivative
`∂_τg(σ) = deriv (fun s => g z θ s) σ`, `RegPkgMin.cont` the continuity, and `GdotLoc` the
integrability).  Each step `(j,i) → (j+1,i)` (resp. `(0,i) → (0,i+1)`) differentiates the identity
for `(j,i)` in the variable `z` (resp. `θ`) along the difference-quotient sequence `z/(n+1)`
(resp. `((π/2−θ)/2)/(n+1)`) and passes to the limit with the dominated convergence theorem; the
domination is the uniform sup bound of `GdotLoc` combined with the mean value theorem.  Only
`D_z`-outermost and `D_θ`-outermost steps occur, so no commutation of `D_z` with `D_θ` is needed.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.RegExportIface.RXT (idx GdotLoc)
open Work.FTS.Regularity (pExp)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The base case -/

/-- **The base case `(0,0)`**: the fundamental theorem of calculus in `τ`. -/
theorem mii_P_00 {S : ℝ} {g : Fam}
    (hcont : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ContinuousOn (fun τ => g z θ τ) (Set.Ici 0))
    (hderiv : ∀ z θ σ, 0 < σ → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s) (gdot g σ z θ) σ)
    (hR : mii_R S g 0 0) : mii_P S g 0 0 := by
  intro z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
  have hQd : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ, hθ'⟩
  have hder : ∀ σ ∈ Set.Ioo τ₁ τ₂, HasDerivAt (fun s : ℝ => g z θ s) (gdot g σ z θ) σ :=
    fun σ hσ => hderiv z θ σ (by linarith [hσ.1, h0]) hQd
  have hcont' : ContinuousOn (fun s : ℝ => g z θ s) (Set.Icc τ₁ τ₂) :=
    (hcont z θ hQd).mono fun s hs => h0.trans hs.1
  have hint : IntervalIntegrable (fun σ : ℝ => gdot g σ z θ) volume τ₁ τ₂ :=
    hR z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h12 hcont' hder hint
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
    Work.FTS.Galerkin.slice_apply]
  rw [hFTC]

/-! ## The step in `z` -/

/-- **The step `(j,i) → (j+1,i)`**: differentiation in `z` of the identity for `(j,i)`, along the
difference-quotient sequence `z/(n+1)`. -/
theorem mii_step_z {S : ℝ} {g : Fam} (hG : GdotLoc S g)
    (hc4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ 1) (hP : mii_P S g j i) (hR : mii_R S g j i) :
    mii_P S g (j + 1) i := by
  intro z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
  obtain ⟨C, hC0, hC⟩ := mii_abs_pz_mixed_gdot_le hG (j := j) (i := i) hji hz hθ hθ'
  have hmeas : ∀ y θ', 0 < y → 0 < θ' → θ' < Real.pi / 2 →
      AEStronglyMeasurable (fun σ => Work.Spaces.mixed j i (gdot g σ) y θ')
        (volume.restrict (Set.Ioc τ₁ τ₂)) :=
    mii_aesm_mixed_gdot_low hG h0 h2S j i hji
  -- the limit of the left-hand sides
  have hA : ∀ τ ∈ Set.Icc (0 : ℝ) S,
      Tendsto (fun n : ℕ => z * ((Work.Spaces.mixed j i (slice g τ) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (slice g τ) z θ) / (z / ((n : ℝ) + 1)))) atTop
        (𝓝 (Work.Spaces.mixed (j + 1) i (slice g τ) z θ)) := by
    intro τ hτ
    have hd : HasDerivAt (fun y : ℝ => Work.Spaces.mixed j i (slice g τ) y θ)
        (Work.Spaces.pz (Work.Spaces.mixed j i (slice g τ)) z θ) z :=
      mii_hasDerivAt_mixed_slice_z (n := 4) (hc4 τ hτ.1) (by omega) hz ⟨hθ, hθ'⟩
    have h1 := (mii_tendsto_slope_seq hz hd).const_mul z
    simpa only [mii_mixed_succ_apply] using h1
  -- the dominated convergence theorem
  have hHmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun σ : ℝ => z * ((Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (gdot g σ) z θ) / (z / ((n : ℝ) + 1))))
      (volume.restrict (Set.Ioc τ₁ τ₂)) := by
    intro n
    have h1 := hmeas (z + z / ((n : ℝ) + 1)) θ (by positivity) hθ hθ'
    have h2 := hmeas z θ hz hθ hθ'
    have h3 : AEStronglyMeasurable
        (fun σ : ℝ => (z / ((n : ℝ) + 1))⁻¹
          * (Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
            - Work.Spaces.mixed j i (gdot g σ) z θ)) (volume.restrict (Set.Ioc τ₁ τ₂)) :=
      (h1.sub h2).const_mul _
    refine (h3.const_mul z).congr (Filter.Eventually.of_forall fun σ => ?_)
    simp only [div_eq_mul_inv]
    ring
  have hHbound : ∀ n : ℕ, ∀ᵐ σ ∂(volume.restrict (Set.Ioc τ₁ τ₂)),
      ‖z * ((Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (gdot g σ) z θ) / (z / ((n : ℝ) + 1)))‖ ≤ z * C := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun σ hσ => ?_
    have hσmem : σ ∈ Set.Ioc (0 : ℝ) S := ⟨lt_of_le_of_lt h0 hσ.1, le_trans hσ.2 h2S⟩
    have ht : 0 < z / ((n : ℝ) + 1) := by positivity
    have htle : z / ((n : ℝ) + 1) ≤ z := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hcont : ContinuousOn (fun y : ℝ => Work.Spaces.mixed j i (gdot g σ) y θ)
        (Set.Icc z (z + z / ((n : ℝ) + 1))) :=
      mii_continuousOn_mixed_slice_z (n := 2) (hG.1 σ hσmem) (by omega) ⟨hθ, hθ'⟩ hz
    have hdiff : ∀ y ∈ Set.Ioo z (z + z / ((n : ℝ) + 1)),
        HasDerivAt (fun y' : ℝ => Work.Spaces.mixed j i (gdot g σ) y' θ)
          (deriv (fun y' : ℝ => Work.Spaces.mixed j i (gdot g σ) y' θ) y) y := by
      intro y hy
      exact (mii_hasDerivAt_mixed_slice_z (n := 2) (hG.1 σ hσmem) (by omega)
        (by linarith [hy.1]) ⟨hθ, hθ'⟩).differentiableAt.hasDerivAt
    have hb : ∀ y ∈ Set.Icc z (z + z / ((n : ℝ) + 1)),
        |deriv (fun y' : ℝ => Work.Spaces.mixed j i (gdot g σ) y' θ) y| ≤ C := by
      intro y hy
      have hy2 : y ≤ 2 * z := by linarith [hy.2, htle]
      have h1 : deriv (fun y' : ℝ => Work.Spaces.mixed j i (gdot g σ) y' θ) y
          = Work.Spaces.pz (Work.Spaces.mixed j i (gdot g σ)) y θ := rfl
      rw [h1]
      exact hC σ hσmem y ⟨by linarith [hy.1], hy2⟩
    have hMVT := mii_abs_sub_le_of_abs_deriv_le (a := z) (b := z + z / ((n : ℝ) + 1))
      (by linarith [ht]) hcont hdiff hb
    have hMVT' : |Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
        - Work.Spaces.mixed j i (gdot g σ) z θ| ≤ C * (z / ((n : ℝ) + 1)) := by
      have h := hMVT
      rwa [show z + z / ((n : ℝ) + 1) - z = z / ((n : ℝ) + 1) by ring] at h
    calc ‖z * ((Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (gdot g σ) z θ) / (z / ((n : ℝ) + 1)))‖
        = z * (|Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
            - Work.Spaces.mixed j i (gdot g σ) z θ| / (z / ((n : ℝ) + 1))) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos hz, abs_div, abs_of_pos ht]
      _ ≤ z * (C * (z / ((n : ℝ) + 1)) / (z / ((n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hMVT' (le_of_lt ht)) (le_of_lt hz)
      _ = z * C := by field_simp
  have hHlim : ∀ᵐ σ ∂(volume.restrict (Set.Ioc τ₁ τ₂)),
      Tendsto (fun n : ℕ => z * ((Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (gdot g σ) z θ) / (z / ((n : ℝ) + 1)))) atTop
        (𝓝 (Work.Spaces.mixed (j + 1) i (gdot g σ) z θ)) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun σ hσ => ?_
    have hσmem : σ ∈ Set.Ioc (0 : ℝ) S := ⟨lt_of_le_of_lt h0 hσ.1, le_trans hσ.2 h2S⟩
    have hd : HasDerivAt (fun y : ℝ => Work.Spaces.mixed j i (gdot g σ) y θ)
        (Work.Spaces.pz (Work.Spaces.mixed j i (gdot g σ)) z θ) z :=
      mii_hasDerivAt_mixed_slice_z (n := 2) (hG.1 σ hσmem) (by omega) hz ⟨hθ, hθ'⟩
    have h1 := (mii_tendsto_slope_seq hz hd).const_mul z
    simpa only [mii_mixed_succ_apply] using h1
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc τ₁ τ₂)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc τ₁ τ₂))
    (F := fun n σ => z * ((Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ
        - Work.Spaces.mixed j i (gdot g σ) z θ) / (z / ((n : ℝ) + 1))))
    (f := fun σ => Work.Spaces.mixed (j + 1) i (gdot g σ) z θ)
    (fun _ : ℝ => z * C) hHmeas (integrable_const _) hHbound hHlim
  -- the value of each integral
  have hCval : ∀ n : ℕ, (∫ σ in τ₁..τ₂, z * ((Work.Spaces.mixed j i (gdot g σ)
        (z + z / ((n : ℝ) + 1)) θ - Work.Spaces.mixed j i (gdot g σ) z θ) / (z / ((n : ℝ) + 1))))
      = z * ((Work.Spaces.mixed j i (slice g τ₂) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (slice g τ₂) z θ) / (z / ((n : ℝ) + 1)))
        - z * ((Work.Spaces.mixed j i (slice g τ₁) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (slice g τ₁) z θ) / (z / ((n : ℝ) + 1))) := by
    intro n
    have h1 : (∫ σ in τ₁..τ₂, Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ)
        = Work.Spaces.mixed j i (slice g τ₂) (z + z / ((n : ℝ) + 1)) θ
          - Work.Spaces.mixed j i (slice g τ₁) (z + z / ((n : ℝ) + 1)) θ :=
      (hP (z + z / ((n : ℝ) + 1)) θ (by positivity) hθ hθ' τ₁ τ₂ h0 h12 h2S).symm
    have h2 : (∫ σ in τ₁..τ₂, Work.Spaces.mixed j i (gdot g σ) z θ)
        = Work.Spaces.mixed j i (slice g τ₂) z θ - Work.Spaces.mixed j i (slice g τ₁) z θ :=
      (hP z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S).symm
    have hi1 : IntervalIntegrable
        (fun σ => Work.Spaces.mixed j i (gdot g σ) (z + z / ((n : ℝ) + 1)) θ) volume τ₁ τ₂ :=
      hR (z + z / ((n : ℝ) + 1)) θ (by positivity) hθ hθ' τ₁ τ₂ h0 h12 h2S
    have hi2 : IntervalIntegrable (fun σ => Work.Spaces.mixed j i (gdot g σ) z θ) volume τ₁ τ₂ :=
      hR z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_sub hi1 hi2, h1, h2]
    ring
  -- assemble
  have hlimSub : Tendsto (fun n : ℕ => z * ((Work.Spaces.mixed j i (slice g τ₂)
        (z + z / ((n : ℝ) + 1)) θ - Work.Spaces.mixed j i (slice g τ₂) z θ) / (z / ((n : ℝ) + 1)))
      - z * ((Work.Spaces.mixed j i (slice g τ₁) (z + z / ((n : ℝ) + 1)) θ
        - Work.Spaces.mixed j i (slice g τ₁) z θ) / (z / ((n : ℝ) + 1)))) atTop
      (𝓝 (Work.Spaces.mixed (j + 1) i (slice g τ₂) z θ
        - Work.Spaces.mixed (j + 1) i (slice g τ₁) z θ)) :=
    (hA τ₂ ⟨h0.trans h12, h2S⟩).sub (hA τ₁ ⟨h0, le_trans h12 h2S⟩)
  have hlimInt : Tendsto (fun n : ℕ => z * ((Work.Spaces.mixed j i (slice g τ₂)
        (z + z / ((n : ℝ) + 1)) θ - Work.Spaces.mixed j i (slice g τ₂) z θ) / (z / ((n : ℝ) + 1)))
      - z * ((Work.Spaces.mixed j i (slice g τ₁) (z + z / ((n : ℝ) + 1)) θ
        - Work.Spaces.mixed j i (slice g τ₁) z θ) / (z / ((n : ℝ) + 1)))) atTop
      (𝓝 (∫ σ in τ₁..τ₂, Work.Spaces.mixed (j + 1) i (gdot g σ) z θ)) := by
    have hDCT' := hDCT
    rw [show (∫ σ, Work.Spaces.mixed (j + 1) i (gdot g σ) z θ
          ∂(volume.restrict (Set.Ioc τ₁ τ₂)))
        = ∫ σ in τ₁..τ₂, Work.Spaces.mixed (j + 1) i (gdot g σ) z θ from
      (intervalIntegral.integral_of_le h12).symm] at hDCT'
    refine hDCT'.congr' (Filter.Eventually.of_forall fun n => ?_)
    rw [← intervalIntegral.integral_of_le h12]
    exact hCval n
  exact tendsto_nhds_unique hlimSub hlimInt

/-! ## The step in `θ` -/

/-- **The step `(0,i) → (0,i+1)`**: differentiation in `θ` of the identity for `(0,i)`, along the
difference-quotient sequence `((π/2−θ)/2)/(n+1)`. -/
theorem mii_step_theta {S : ℝ} {g : Fam} (hG : GdotLoc S g)
    (hc4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0)
    {i : ℕ} (hi : i ≤ 1) (hP : mii_P S g 0 i) (hR : mii_R S g 0 i) :
    mii_P S g 0 (i + 1) := by
  intro z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
  obtain ⟨C, hC0, hC⟩ := mii_abs_pth_mixed_gdot_le hG (j := 0) (i := i) (by omega) hz hθ hθ'
  have hmeas : ∀ y θ', 0 < y → 0 < θ' → θ' < Real.pi / 2 →
      AEStronglyMeasurable (fun σ => Work.Spaces.mixed 0 i (gdot g σ) y θ')
        (volume.restrict (Set.Ioc τ₁ τ₂)) :=
    mii_aesm_mixed_gdot_low hG h0 h2S 0 i (by omega)
  -- the limit of the left-hand sides
  have hA : ∀ τ ∈ Set.Icc (0 : ℝ) S,
      Tendsto (fun n : ℕ => Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (slice g τ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (slice g τ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
        atTop (𝓝 (Work.Spaces.mixed 0 (i + 1) (slice g τ) z θ)) := by
    intro τ hτ
    have hd : HasDerivAt (fun y : ℝ => Work.Spaces.mixed 0 i (slice g τ) z y)
        (Work.Spaces.pth (Work.Spaces.mixed 0 i (slice g τ)) z θ) θ :=
      mii_hasDerivAt_mixed_slice_theta (n := 4) (hc4 τ hτ.1) (by omega) hz ⟨hθ, hθ'⟩
    have h1 := (mii_tendsto_slope_seq (show (0 : ℝ) < (Real.pi / 2 - θ) / 2 by linarith) hd)
      |>.const_mul (Real.sin (2 * θ))
    simpa only [mii_mixed_zero_succ_apply] using h1
  -- the dominated convergence theorem
  have hHmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun σ : ℝ => Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (gdot g σ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
      (volume.restrict (Set.Ioc τ₁ τ₂)) := by
    intro n
    have h1 := hmeas z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)) hz (by
      have : 0 < ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) := by positivity
      linarith) (by
      have h2 : ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) ≤ (Real.pi / 2 - θ) / 2 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      linarith)
    have h2 := hmeas z θ hz hθ hθ'
    have h3 : AEStronglyMeasurable
        (fun σ : ℝ => (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))⁻¹
          * (Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
            - Work.Spaces.mixed 0 i (gdot g σ) z θ)) (volume.restrict (Set.Ioc τ₁ τ₂)) :=
      (h1.sub h2).const_mul _
    refine (h3.const_mul (Real.sin (2 * θ))).congr (Filter.Eventually.of_forall fun σ => ?_)
    simp only [div_eq_mul_inv]
    ring
  have hHbound : ∀ n : ℕ, ∀ᵐ σ ∂(volume.restrict (Set.Ioc τ₁ τ₂)),
      ‖Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (gdot g σ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)))‖
        ≤ |Real.sin (2 * θ)| * C := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun σ hσ => ?_
    have hσmem : σ ∈ Set.Ioc (0 : ℝ) S := ⟨lt_of_le_of_lt h0 hσ.1, le_trans hσ.2 h2S⟩
    have ht : 0 < ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) := by positivity
    have htle : ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) ≤ (Real.pi / 2 - θ) / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hcont : ContinuousOn (fun y : ℝ => Work.Spaces.mixed 0 i (gdot g σ) z y)
        (Set.Icc θ (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))) :=
      mii_continuousOn_mixed_slice_theta (n := 2) (hG.1 σ hσmem) (by omega) hz hθ
        (by linarith [htle])
    have hdiff : ∀ y ∈ Set.Ioo θ (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)),
        HasDerivAt (fun y' : ℝ => Work.Spaces.mixed 0 i (gdot g σ) z y')
          (deriv (fun y' : ℝ => Work.Spaces.mixed 0 i (gdot g σ) z y') y) y := by
      intro y hy
      exact (mii_hasDerivAt_mixed_slice_theta (n := 2) (hG.1 σ hσmem) (by omega) hz
        ⟨by linarith [hy.1], by linarith [hy.2, htle]⟩).differentiableAt.hasDerivAt
    have hb : ∀ y ∈ Set.Icc θ (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)),
        |deriv (fun y' : ℝ => Work.Spaces.mixed 0 i (gdot g σ) z y') y| ≤ C := by
      intro y hy
      have h1 : deriv (fun y' : ℝ => Work.Spaces.mixed 0 i (gdot g σ) z y') y
          = Work.Spaces.pth (Work.Spaces.mixed 0 i (gdot g σ)) z y := rfl
      rw [h1]
      exact hC σ hσmem y ⟨by linarith [hy.1], by linarith [hy.2, htle]⟩
    have hMVT := mii_abs_sub_le_of_abs_deriv_le (a := θ)
      (b := θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)) (by linarith [ht]) hcont hdiff hb
    have hMVT' : |Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
        - Work.Spaces.mixed 0 i (gdot g σ) z θ| ≤ C * (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)) := by
      have h := hMVT
      rwa [show θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) - θ
        = ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) by ring] at h
    calc ‖Real.sin (2 * θ)
          * ((Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
            - Work.Spaces.mixed 0 i (gdot g σ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)))‖
        = |Real.sin (2 * θ)| * (|Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
            - Work.Spaces.mixed 0 i (gdot g σ) z θ| / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))) := by
          rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos ht]
      _ ≤ |Real.sin (2 * θ)| * (C * (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
            / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hMVT' (le_of_lt ht)) (abs_nonneg _)
      _ = |Real.sin (2 * θ)| * C := by
          rw [mul_div_assoc, div_self (ne_of_gt ht), mul_one]
  have hHlim : ∀ᵐ σ ∂(volume.restrict (Set.Ioc τ₁ τ₂)),
      Tendsto (fun n : ℕ => Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (gdot g σ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
        atTop (𝓝 (Work.Spaces.mixed 0 (i + 1) (gdot g σ) z θ)) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun σ hσ => ?_
    have hσmem : σ ∈ Set.Ioc (0 : ℝ) S := ⟨lt_of_le_of_lt h0 hσ.1, le_trans hσ.2 h2S⟩
    have hd : HasDerivAt (fun y : ℝ => Work.Spaces.mixed 0 i (gdot g σ) z y)
        (Work.Spaces.pth (Work.Spaces.mixed 0 i (gdot g σ)) z θ) θ :=
      mii_hasDerivAt_mixed_slice_theta (n := 2) (hG.1 σ hσmem) (by omega) hz ⟨hθ, hθ'⟩
    have h1 := (mii_tendsto_slope_seq (show (0 : ℝ) < (Real.pi / 2 - θ) / 2 by linarith) hd)
      |>.const_mul (Real.sin (2 * θ))
    simpa only [mii_mixed_zero_succ_apply] using h1
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc τ₁ τ₂)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc τ₁ τ₂))
    (F := fun n σ => Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (gdot g σ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
    (f := fun σ => Work.Spaces.mixed 0 (i + 1) (gdot g σ) z θ)
    (fun _ : ℝ => |Real.sin (2 * θ)| * C) hHmeas
    ((integrable_const _).const_mul _) hHbound hHlim
  -- the value of each integral
  have hCval : ∀ n : ℕ, (∫ σ in τ₁..τ₂, Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (gdot g σ) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (gdot g σ) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
      = Real.sin (2 * θ)
          * ((Work.Spaces.mixed 0 i (slice g τ₂) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
            - Work.Spaces.mixed 0 i (slice g τ₂) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)))
        - Real.sin (2 * θ)
          * ((Work.Spaces.mixed 0 i (slice g τ₁) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
            - Work.Spaces.mixed 0 i (slice g τ₁) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))) := by
    intro n
    have h1 : (∫ σ in τ₁..τ₂, Work.Spaces.mixed 0 i (gdot g σ) z
          (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)))
        = Work.Spaces.mixed 0 i (slice g τ₂) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (slice g τ₁) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)) :=
      (hP z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)) hz (by
          have : 0 < ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) := by positivity
          linarith)
        (by
          have h2 : ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) ≤ (Real.pi / 2 - θ) / 2 := by
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
            nlinarith [Nat.cast_nonneg (α := ℝ) n]
          linarith)
        τ₁ τ₂ h0 h12 h2S).symm
    have h2 : (∫ σ in τ₁..τ₂, Work.Spaces.mixed 0 i (gdot g σ) z θ)
        = Work.Spaces.mixed 0 i (slice g τ₂) z θ - Work.Spaces.mixed 0 i (slice g τ₁) z θ :=
      (hP z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S).symm
    have hi1 : IntervalIntegrable
        (fun σ => Work.Spaces.mixed 0 i (gdot g σ) z
          (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))) volume τ₁ τ₂ :=
      hR z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)) hz (by
          have : 0 < ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) := by positivity
          linarith)
        (by
          have h2 : ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1) ≤ (Real.pi / 2 - θ) / 2 := by
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
            nlinarith [Nat.cast_nonneg (α := ℝ) n]
          linarith)
        τ₁ τ₂ h0 h12 h2S
    have hi2 : IntervalIntegrable (fun σ => Work.Spaces.mixed 0 i (gdot g σ) z θ) volume τ₁ τ₂ :=
      hR z θ hz hθ hθ' τ₁ τ₂ h0 h12 h2S
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_sub hi1 hi2, h1, h2]
    ring
  -- assemble
  have hlimSub : Tendsto (fun n : ℕ => Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (slice g τ₂) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (slice g τ₂) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)))
      - Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (slice g τ₁) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (slice g τ₁) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
      atTop (𝓝 (Work.Spaces.mixed 0 (i + 1) (slice g τ₂) z θ
        - Work.Spaces.mixed 0 (i + 1) (slice g τ₁) z θ)) :=
    (hA τ₂ ⟨h0.trans h12, h2S⟩).sub (hA τ₁ ⟨h0, le_trans h12 h2S⟩)
  have hlimInt : Tendsto (fun n : ℕ => Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (slice g τ₂) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (slice g τ₂) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1)))
      - Real.sin (2 * θ)
        * ((Work.Spaces.mixed 0 i (slice g τ₁) z (θ + ((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))
          - Work.Spaces.mixed 0 i (slice g τ₁) z θ) / (((Real.pi / 2 - θ) / 2) / ((n : ℝ) + 1))))
      atTop (𝓝 (∫ σ in τ₁..τ₂, Work.Spaces.mixed 0 (i + 1) (gdot g σ) z θ)) := by
    have hDCT' := hDCT
    rw [show (∫ σ, Work.Spaces.mixed 0 (i + 1) (gdot g σ) z θ
          ∂(volume.restrict (Set.Ioc τ₁ τ₂)))
        = ∫ σ in τ₁..τ₂, Work.Spaces.mixed 0 (i + 1) (gdot g σ) z θ from
      (intervalIntegral.integral_of_le h12).symm] at hDCT'
    refine hDCT'.congr' (Filter.Eventually.of_forall fun n => ?_)
    rw [← intervalIntegral.integral_of_le h12]
    exact hCval n
  exact tendsto_nhds_unique hlimSub hlimInt

end Work.FTS_RegExport.RXT.Sys
