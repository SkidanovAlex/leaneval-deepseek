import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.SysAux.FK_L12_aux
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.FK_L12_slice_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ### The main statement -/

/-- Facts about the angular moment `FK u (z) = ∫_θ K(θ) u(z,θ) dθ` and the radial transform
`L12 u (z) = ∫_{r>z} FK u (r)/r dr` of a slice `u` that is `C⁴` on the open quadrant with all
`mixed`-jets of order `≤ 2` bounded by `B·z^{3/2}/(1+z)²`, and with `L12 u 0 = 0`:
`j`-th `D_z`-jets for `j ≤ 2`, `C²`/`C³` regularity, and the deriv-identity `L12' = -FK/z`. -/
theorem FK_L12_slice_facts {B : ℝ} {u : ℝ → ℝ → ℝ}
    (hCd : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hb : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a u z θ| ≤ B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    (h0 : Work.Construction.L12 u 0 = 0) :
    ∃ C : ℝ, 0 < C ∧
      (∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter j (fun z _ => Work.Construction.FK u z) z 0|
          ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) ∧
      (∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 u z) z 0|
          ≤ C * z ^ ((3 : ℝ) / 2)) ∧
      ContDiffOn ℝ 2 (fun z => Work.Construction.FK u z) (Set.Ioi 0) ∧
      ContDiffOn ℝ 3 (fun z => Work.Construction.L12 u z) (Set.Ioi 0) ∧
      (∀ z : ℝ, 0 < z →
        HasDerivAt (fun z' => Work.Construction.L12 u z') (-(Work.Construction.FK u z) / z) z) := by
  ---------------------------------------------------------------------------------------------
  -- `B' = max B 0`, and the weighted hypothesis in the form used below
  ---------------------------------------------------------------------------------------------
  set B' : ℝ := max B 0 with hB'def
  have hB'0 : 0 ≤ B' := le_max_right B 0
  have hB'le : B ≤ B' := le_max_left B 0
  have hb' : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a u z θ| ≤ B' * L12Wt z := by
    intro b a hba z θ hz hθ hθ2
    have h1 := hb b a hba z θ hz hθ hθ2
    have h2 : B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) ≤ B' * L12Wt z := by
      rw [L12Wt]
      exact mul_le_mul_of_nonneg_right hB'le (by positivity)
    linarith [h1, h2]
  ---------------------------------------------------------------------------------------------
  -- the `z`-slices of `u` are `C²` on `(0,∞)`
  ---------------------------------------------------------------------------------------------
  have hslice : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContDiffOn ℝ 2 (fun z => u z θ) (Set.Ioi 0) := by
    intro θ hθ
    have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi 0) Work.FTS.EllipticEst.Q0 :=
      fun z hz => ⟨hz, hθ⟩
    have hcomp := (hCd.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 4)).comp
      ((contDiffOn_id : ContDiffOn ℝ 2 (fun z : ℝ => z) (Set.Ioi 0)).prodMk contDiffOn_const) hmap
    simpa only [Function.comp_def, Function.uncurry, id_eq] using hcomp
  have hG2u : ContDiffOn ℝ 2 (Function.uncurry u) Work.FTS.EllipticEst.Q0 :=
    hCd.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 4)
  have hpzu2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz u)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_two_uncurry_pz (hCd.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))
  have hpzu1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz u)) Work.FTS.EllipticEst.Q0 :=
    (Work.Spaces.uncurry_partial_c1 Work.FTS.EllipticEst.isOpen_Q0 hG2u).1
  have hpziter2cont : ContinuousOn (Function.uncurry (Work.Spaces.pzIter 2 u))
      Work.FTS.EllipticEst.Q0 := by
    have h := (Work.Spaces.uncurry_partial_c1 Work.FTS.EllipticEst.isOpen_Q0 hpzu2).1
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h.continuousOn
  ---------------------------------------------------------------------------------------------
  -- the pointwise bounds `|u| ≤ B'`, `|∂_z u| ≤ B'`, `|∂_z² u| ≤ 2 B' L12Wt z/z²`
  ---------------------------------------------------------------------------------------------
  have hmixed00 : ∀ z θ : ℝ, Work.Spaces.mixed 0 0 u z θ = u z θ := fun z θ => rfl
  have hmixed10 : ∀ z θ : ℝ, Work.Spaces.mixed 1 0 u z θ = z * Work.Spaces.pz u z θ :=
    fun z θ => rfl
  have hb0 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |u z θ| ≤ B' := by
    intro z θ hz hθ hθ2
    have h1 : |u z θ| ≤ B' * L12Wt z := by
      simpa only [hmixed00] using hb' 0 0 (by norm_num) z θ hz hθ hθ2
    exact le_trans h1 (by simpa using mul_le_of_le_one_right hB'0 (L12Wt_le_one hz))
  have hb1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pz u z θ| ≤ B' := by
    intro z θ hz hθ hθ2
    have h1 : |z * Work.Spaces.pz u z θ| ≤ B' * L12Wt z := by
      simpa only [hmixed10] using hb' 1 0 (by norm_num) z θ hz hθ hθ2
    rw [abs_mul, abs_of_pos hz] at h1
    have h2 : |Work.Spaces.pz u z θ| ≤ (B' * L12Wt z) / z := by
      rw [le_div_iff₀ hz]; linarith
    have h3 : (B' * L12Wt z) / z ≤ B' := by
      rw [mul_div_assoc]
      simpa using mul_le_mul_of_nonneg_left (L12Wt_div_le_one hz) hB'0
    exact le_trans h2 h3
  have hpz2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pzIter 2 u z θ| ≤ 2 * B' * (L12Wt z / z ^ 2) := by
    intro z θ hz hθ hθ2
    have h1 : |Work.Spaces.Dz u z θ| ≤ B' * L12Wt z := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_succ,
        Work.Spaces.DzIter_zero] using
        hb' 1 0 (by norm_num) z θ hz hθ hθ2
    have h2 : |Work.Spaces.DzIter 2 u z θ| ≤ B' * L12Wt z := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_zero] using
        hb' 2 0 (by norm_num) z θ hz hθ hθ2
    have hexp := DzIter_two_pt_open_aux (h := u) hslice hz ⟨hθ, hθ2⟩
    have hDz : Work.Spaces.Dz u z θ = z * Work.Spaces.pzIter 1 u z θ := rfl
    have hkey : z ^ 2 * Work.Spaces.pzIter 2 u z θ
        = Work.Spaces.DzIter 2 u z θ - Work.Spaces.Dz u z θ := by
      linarith [hexp, hDz]
    have h3 : z ^ 2 * |Work.Spaces.pzIter 2 u z θ| ≤ 2 * (B' * L12Wt z) := by
      rw [← abs_of_pos (by positivity : (0 : ℝ) < z ^ 2), ← abs_mul, hkey]
      have habs : |Work.Spaces.DzIter 2 u z θ - Work.Spaces.Dz u z θ|
          ≤ |Work.Spaces.DzIter 2 u z θ| + |Work.Spaces.Dz u z θ| := by
        rw [sub_eq_add_neg]
        simpa using abs_add_le (Work.Spaces.DzIter 2 u z θ) (-(Work.Spaces.Dz u z θ))
      calc |Work.Spaces.DzIter 2 u z θ - Work.Spaces.Dz u z θ|
          ≤ |Work.Spaces.DzIter 2 u z θ| + |Work.Spaces.Dz u z θ| := habs
        _ ≤ B' * L12Wt z + B' * L12Wt z := add_le_add h2 h1
        _ = 2 * (B' * L12Wt z) := by ring
    have hz2 : (0 : ℝ) < z ^ 2 := by positivity
    have h4 : |Work.Spaces.pzIter 2 u z θ| ≤ (2 * B' * L12Wt z) / z ^ 2 := by
      rw [le_div_iff₀ hz2]
      calc |Work.Spaces.pzIter 2 u z θ| * z ^ 2
            = z ^ 2 * |Work.Spaces.pzIter 2 u z θ| := by ring
        _ ≤ 2 * (B' * L12Wt z) := h3
        _ = 2 * B' * L12Wt z := by ring
    calc |Work.Spaces.pzIter 2 u z θ| ≤ (2 * B' * L12Wt z) / z ^ 2 := h4
      _ = 2 * B' * (L12Wt z / z ^ 2) := by ring
  ---------------------------------------------------------------------------------------------
  -- the two angular moments `I₁`, `I₂` and the derivative formulas for `FK u`
  ---------------------------------------------------------------------------------------------
  set I1 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz u z θ * Work.Spaces.K θ
    with hI1def
  set I2 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 u z θ * Work.Spaces.K θ
    with hI2def
  have hKcont : ContinuousOn Work.Spaces.K Work.Spaces.Iθ :=
    ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn
  have hFKd : ∀ z : ℝ, 0 < z → HasDerivAt (fun z => Work.Construction.FK u z) (I1 z) z := by
    intro z hz
    rw [hI1def]
    exact param_hasDerivAt (G := u) (φ := Work.Spaces.K) (C₀ := B') (C₁ := B')
      hB'0 hz hKcont hG2u hb0 (fun z' θ hz' hθ hθ2 _ _ => hb1 z' θ hz' hθ hθ2)
  have hFKd2 : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun w => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz u w θ * Work.Spaces.K θ)
        (I2 z) z := by
    intro z hz
    rw [hI2def]
    refine param_hasDerivAt (G := Work.Spaces.pz u) (φ := Work.Spaces.K) (C₀ := B')
      (C₁ := 2 * B' * (z / 2) ^ (-(1 : ℝ) / 2)) ?_ hz hKcont hpzu2 hb1 ?_
    · exact mul_nonneg (mul_nonneg (by norm_num) hB'0) (Real.rpow_nonneg (by linarith) _)
    · intro z' θ hz' hθ hθ2 hz1 _hz2
      have h := hpz2 z' θ hz' hθ hθ2
      have hle := L12Wt_div_sq_le hz hz1
      calc |Work.Spaces.pz (Work.Spaces.pz u) z' θ| ≤ 2 * B' * (L12Wt z' / z' ^ 2) := h
        _ ≤ 2 * B' * (z / 2) ^ (-(1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hle (mul_nonneg (by norm_num) hB'0)
  ---------------------------------------------------------------------------------------------
  -- the angular-integral bounds for `I₁` and `I₂`
  ---------------------------------------------------------------------------------------------
  have hI1b : ∀ z : ℝ, 0 < z → |I1 z| ≤ (B' * (L12Wt z / z)) * 3 * (Real.pi / 2) := by
    intro z hz
    rw [hI1def]
    refine abs_setIntegral_Itheta_mul_K_le_aux
      (G := fun θ => Work.Spaces.pz u z θ) (c := B' * (L12Wt z / z))
      (mul_nonneg hB'0 (div_nonneg (L12Wt_nonneg hz) hz.le)) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2) hpzu1.continuousOn hz
    · filter_upwards [ae_mem_Ioo_of_mem_Iθ] with θ hθ
      have h1 : |z * Work.Spaces.pz u z θ| ≤ B' * L12Wt z := by
        simpa only [hmixed10] using hb' 1 0 (by norm_num) z θ hz hθ.1 hθ.2
      rw [abs_mul, abs_of_pos hz] at h1
      have h2 : |Work.Spaces.pz u z θ| ≤ (B' * L12Wt z) / z := by
        rw [le_div_iff₀ hz]; linarith
      calc |Work.Spaces.pz u z θ| ≤ (B' * L12Wt z) / z := h2
        _ = B' * (L12Wt z / z) := by ring
  have hI2b : ∀ z : ℝ, 0 < z → |I2 z| ≤ (2 * B' * (L12Wt z / z ^ 2)) * 3 * (Real.pi / 2) := by
    intro z hz
    rw [hI2def]
    refine abs_setIntegral_Itheta_mul_K_le_aux
      (G := fun θ => Work.Spaces.pzIter 2 u z θ) (c := 2 * B' * (L12Wt z / z ^ 2))
      (mul_nonneg (mul_nonneg (by norm_num) hB'0) (div_nonneg (L12Wt_nonneg hz) (by positivity)))
      ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 u p.1 p.2) hpziter2cont hz
    · filter_upwards [ae_mem_Ioo_of_mem_Iθ] with θ hθ
      exact hpz2 z θ hz hθ.1 hθ.2
  ---------------------------------------------------------------------------------------------
  -- the pointwise bound on `FK u` and the bounds on its `D_z`-jets
  ---------------------------------------------------------------------------------------------
  have hFK0 : ∀ z : ℝ, 0 < z →
      |Work.Construction.FK u z| ≤ B' * (3 * (Real.pi / 2)) * L12Wt z := by
    intro z hz
    have h := abs_setIntegral_Itheta_mul_K_le_aux (G := fun θ => u z θ) (c := B' * L12Wt z)
      (mul_nonneg hB'0 (L12Wt_nonneg hz))
      (Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => u p.1 p.2)
        hG2u.continuousOn hz)
      (by
        filter_upwards [ae_mem_Ioo_of_mem_Iθ] with θ hθ
        simpa only [hmixed00] using hb' 0 0 (by norm_num) z θ hz hθ.1 hθ.2)
    calc |Work.Construction.FK u z| ≤ (B' * L12Wt z) * 3 * (Real.pi / 2) := h
      _ = B' * (3 * (Real.pi / 2)) * L12Wt z := by ring
  have hFKjet1 : ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK u z) z 0|
        ≤ B' * (3 * (Real.pi / 2)) * L12Wt z := by
    intro z hz
    have hval : Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK u z) z 0 = z * I1 z := by
      show z * deriv (fun z' => Work.Construction.FK u z') z = z * I1 z
      rw [(hFKd z hz).deriv]
    rw [hval, abs_mul, abs_of_pos hz]
    have h := hI1b z hz
    calc z * |I1 z| ≤ z * ((B' * (L12Wt z / z)) * 3 * (Real.pi / 2)) :=
          mul_le_mul_of_nonneg_left h hz.le
      _ = B' * (3 * (Real.pi / 2)) * L12Wt z := by
          field_simp
          try ring
  have hFKjet2 : ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter 2 (fun z _ => Work.Construction.FK u z) z 0|
        ≤ 3 * (B' * (3 * (Real.pi / 2)) * L12Wt z) := by
    intro z hz
    have hev : (fun w => Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK u z) w 0)
        =ᶠ[𝓝 z] fun w => w * I1 w := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      show w * deriv (fun z' => Work.Construction.FK u z') w = w * I1 w
      rw [(hFKd w hw).deriv]
    have hprod : HasDerivAt (fun w => w * I1 w) (1 * I1 z + z * I2 z) z :=
      (hasDerivAt_id z).mul (hFKd2 z hz)
    have hderiv : deriv (fun w => Work.Spaces.DzIter 1
        (fun z _ => Work.Construction.FK u z) w 0) z = 1 * I1 z + z * I2 z := by
      rw [hev.deriv_eq]; exact hprod.deriv
    have hval : Work.Spaces.DzIter 2 (fun z _ => Work.Construction.FK u z) z 0
        = z * (1 * I1 z + z * I2 z) := by
      show z * deriv (fun w => Work.Spaces.DzIter 1
        (fun z _ => Work.Construction.FK u z) w 0) z = z * (1 * I1 z + z * I2 z)
      rw [hderiv]
    rw [hval, abs_mul, abs_of_pos hz]
    have h1 := hI1b z hz
    have h2 := hI2b z hz
    have h3 : |1 * I1 z + z * I2 z| ≤ (B' * (L12Wt z / z)) * 3 * (Real.pi / 2)
        + z * ((2 * B' * (L12Wt z / z ^ 2)) * 3 * (Real.pi / 2)) := by
      calc |1 * I1 z + z * I2 z| ≤ |1 * I1 z| + |z * I2 z| := abs_add_le _ _
        _ = |I1 z| + z * |I2 z| := by rw [one_mul, abs_mul, abs_of_pos hz]
        _ ≤ (B' * (L12Wt z / z)) * 3 * (Real.pi / 2)
              + z * ((2 * B' * (L12Wt z / z ^ 2)) * 3 * (Real.pi / 2)) :=
            add_le_add h1 (mul_le_mul_of_nonneg_left h2 hz.le)
    calc z * |1 * I1 z + z * I2 z|
        ≤ z * ((B' * (L12Wt z / z)) * 3 * (Real.pi / 2)
            + z * ((2 * B' * (L12Wt z / z ^ 2)) * 3 * (Real.pi / 2))) :=
          mul_le_mul_of_nonneg_left h3 hz.le
      _ = 3 * (B' * (3 * (Real.pi / 2)) * L12Wt z) := by
          field_simp
          try ring

  ---------------------------------------------------------------------------------------------
  -- `FK u` is `C²` on `(0,∞)`
  ---------------------------------------------------------------------------------------------
  have hI2cont : ContinuousOn I2 (Set.Ioi 0) := by
    intro z₀ hz₀'
    have hz₀ : 0 < z₀ := hz₀'
    have hmem : z₀ ∈ Set.Ioo (z₀ / 2) (2 * z₀) := ⟨by linarith, by linarith⟩
    have hKc0 : 0 ≤ 2 * B' * (z₀ / 2) ^ (-(1 : ℝ) / 2) :=
      mul_nonneg (mul_nonneg (by norm_num) hB'0) (Real.rpow_nonneg (by linarith) _)
    have hG_meas : ∀ᶠ z in 𝓝 z₀,
        AEStronglyMeasurable (fun θ => Work.Spaces.pzIter 2 u z θ * Work.Spaces.K θ)
          (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
      filter_upwards [isOpen_Ioo.mem_nhds hmem] with z hz
      exact ((hpziter2cont.comp ((continuous_const.prodMk continuous_id).continuousOn)
        (fun θ hθ => ⟨lt_trans (by linarith) hz.1, hθ⟩)).mul
        (hKcont.mono (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))).aestronglyMeasurable
        measurableSet_Ioo
    have hbound : ∀ᶠ z in 𝓝 z₀,
        ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))),
          ‖Work.Spaces.pzIter 2 u z θ‖ ≤ 2 * B' * (z₀ / 2) ^ (-(1 : ℝ) / 2) := by
      filter_upwards [isOpen_Ioo.mem_nhds hmem] with z hz
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs]
      calc |Work.Spaces.pzIter 2 u z θ| ≤ 2 * B' * (L12Wt z / z ^ 2) :=
            hpz2 z θ (lt_trans (by linarith) hz.1) hθ.1 hθ.2
        _ ≤ 2 * B' * (z₀ / 2) ^ (-(1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left (L12Wt_div_sq_le hz₀ hz.1.le)
              (mul_nonneg (by norm_num) hB'0)
    have hcont : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))),
        ContinuousAt (fun z => Work.Spaces.pzIter 2 u z θ) z₀ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hslice : ContinuousOn (fun z : ℝ => Work.Spaces.pzIter 2 u z θ) (Set.Ioi 0) :=
        (hpziter2cont.comp ((continuous_id.prodMk continuous_const).continuousOn)
          (fun z hz => ⟨hz, hθ⟩)).congr (fun z _ => rfl)
      exact hslice.continuousAt (isOpen_Ioi.mem_nhds hz₀)
    have hmain := continuousAt_integral_Itheta_of_bound
      (G := fun z θ => Work.Spaces.pzIter 2 u z θ) (φ := Work.Spaces.K) (z₀ := z₀)
      (K := 2 * B' * (z₀ / 2) ^ (-(1 : ℝ) / 2)) hKc0 hKcont hG_meas hbound hcont
    have hEq : (fun z => ∫ θ, Work.Spaces.pzIter 2 u z θ * Work.Spaces.K θ
        ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))))
        = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 u z θ * Work.Spaces.K θ := by
      funext z
      rw [volume_restrict_Iθ_eq]
    rw [hEq] at hmain
    simpa only [← hI2def] using hmain.continuousWithinAt
  have hFKcont : ContDiffOn ℝ 2 (fun z => Work.Construction.FK u z) (Set.Ioi 0) := by
    have hderiv_eq : Set.EqOn (deriv (fun z => Work.Construction.FK u z)) I1 (Set.Ioi 0) :=
      fun z hz => (hFKd z hz).deriv
    have hderiv2_eq : Set.EqOn (deriv I1) I2 (Set.Ioi 0) := fun z hz => (hFKd2 z hz).deriv
    have hdiff_f : DifferentiableOn ℝ (fun z => Work.Construction.FK u z) (Set.Ioi 0) :=
      fun z hz => (hFKd z hz).differentiableAt.differentiableWithinAt
    have hdiff_g : DifferentiableOn ℝ I1 (Set.Ioi 0) :=
      fun z hz => (hFKd2 z hz).differentiableAt.differentiableWithinAt
    have hcont_dd : ContinuousOn (deriv (deriv (fun z => Work.Construction.FK u z)))
        (Set.Ioi 0) :=
      (hI2cont.congr hderiv2_eq).congr (deriv_congr_of_isOpen isOpen_Ioi hderiv_eq)
    have hdiff_deriv : DifferentiableOn ℝ (deriv (fun z => Work.Construction.FK u z))
        (Set.Ioi 0) :=
      hdiff_g.congr hderiv_eq
    have hcont1 : ContDiffOn ℝ 1 (deriv (fun z => Work.Construction.FK u z)) (Set.Ioi 0) := by
      rw [show (1 : WithTop ℕ∞) = 0 + 1 from by norm_num]
      refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
        (f := deriv (fun z => Work.Construction.FK u z)) (n := (0 : WithTop ℕ∞)) isOpen_Ioi).mpr
        ⟨hdiff_deriv, ?_, ?_⟩
      · intro h; exact absurd h (by norm_num)
      · rw [contDiffOn_zero]; exact hcont_dd
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from by norm_num]
    refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
      (f := fun z => Work.Construction.FK u z) (n := (1 : WithTop ℕ∞)) isOpen_Ioi).mpr
      ⟨hdiff_f, ?_, hcont1⟩
    intro h; exact absurd h (by norm_num)
  ---------------------------------------------------------------------------------------------
  -- the derivative of `L₁₂ u`, and bounds on its `D_z`-jets
  ---------------------------------------------------------------------------------------------
  have hFK2cont : ContinuousOn (fun r : ℝ => Work.Construction.FK u r / r) (Set.Ioi 0) :=
    hFKcont.continuousOn.div continuousOn_id (fun r hr => ne_of_gt hr)
  have hgint : IntegrableOn (fun r : ℝ => Work.Construction.FK u r / r) (Set.Ioi 0) := by
    have haesm : AEStronglyMeasurable (fun r : ℝ => Work.Construction.FK u r / r)
        (volume.restrict (Set.Ioi 0)) :=
      hFK2cont.aestronglyMeasurable measurableSet_Ioi
    refine Integrable.mono' (sqrt_div_sq_integrableOn_aux.const_mul (B' * (3 * (Real.pi / 2))))
      haesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have h1 : |Work.Construction.FK u r| ≤ B' * (3 * (Real.pi / 2)) * L12Wt r := hFK0 r hr0
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0]
    calc |Work.Construction.FK u r| / r ≤ B' * (3 * (Real.pi / 2)) * L12Wt r / r :=
          div_le_div_of_nonneg_right h1 hr0.le
      _ = B' * (3 * (Real.pi / 2)) * (Real.sqrt r / (1 + r) ^ 2) := by
          rw [mul_div_assoc, L12Wt_div_eq hr0]
  have hL12hasDeriv : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z' => Work.Construction.L12 u z') (-(Work.Construction.FK u z) / z) z := by
    intro z hz
    have hz2 : 0 < z / 2 := by linarith
    have hcont : ContinuousOn (fun r : ℝ => Work.Construction.FK u r / r) (Set.Ioi (z / 2)) :=
      hFK2cont.mono (fun r hr => lt_trans hz2 hr)
    have hint : IntegrableOn (fun r : ℝ => Work.Construction.FK u r / r) (Set.Ioi (z / 2)) :=
      hgint.mono_set (Set.Ioi_subset_Ioi (by linarith))
    have h := Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi (a := z / 2) (z := z)
      (by linarith) hcont hint
    have hfun : (fun z' => ∫ r in Set.Ioi z', Work.Construction.FK u r / r)
        = fun z' => Work.Construction.L12 u z' :=
      funext fun z' => (Work.FTS_RegExport.RXT.L12_eq_integral_FK u z').symm
    rw [hfun] at h
    simpa only [neg_div] using h
  have hL12jet0 : ∀ z : ℝ, 0 < z →
      |Work.Construction.L12 u z| ≤ B' * (3 * (Real.pi / 2)) * z ^ ((3 : ℝ) / 2) := by
    intro z hz
    rw [Work.FTS_RegExport.RXT.L12_eq_integral_FK u z]
    refine abs_setIntegral_Ioi_le_of_integral_zero_aux
      (g := fun r => Work.Construction.FK u r / r) (B := B' * (3 * (Real.pi / 2)))
      (mul_nonneg hB'0 (by positivity)) hz hgint ?_ ?_
    · intro r hr
      have h1 : |Work.Construction.FK u r| ≤ B' * (3 * (Real.pi / 2)) * L12Wt r := hFK0 r hr
      rw [abs_div, abs_of_pos hr]
      calc |Work.Construction.FK u r| / r ≤ B' * (3 * (Real.pi / 2)) * L12Wt r / r :=
            div_le_div_of_nonneg_right h1 hr.le
        _ = B' * (3 * (Real.pi / 2)) * (Real.sqrt r / (1 + r) ^ 2) := by
            rw [mul_div_assoc, L12Wt_div_eq hr]
    · rw [← Work.FTS_RegExport.RXT.L12_eq_integral_FK u 0]
      exact h0
  have hL12jet1 : ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12 u z) z 0|
        ≤ B' * (3 * (Real.pi / 2)) * z ^ ((3 : ℝ) / 2) := by
    intro z hz
    have hval : Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12 u z) z 0
        = -(Work.Construction.FK u z) := by
      show z * deriv (fun z' => Work.Construction.L12 u z') z = -(Work.Construction.FK u z)
      rw [(hL12hasDeriv z hz).deriv]
      field_simp
    rw [hval, abs_neg]
    calc |Work.Construction.FK u z| ≤ B' * (3 * (Real.pi / 2)) * L12Wt z := hFK0 z hz
      _ ≤ B' * (3 * (Real.pi / 2)) * z ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left (L12Wt_le_rpow hz) (mul_nonneg hB'0 (by positivity))
  have hL12jet2 : ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter 2 (fun z _ => Work.Construction.L12 u z) z 0|
        ≤ B' * (3 * (Real.pi / 2)) * z ^ ((3 : ℝ) / 2) := by
    intro z hz
    have hev : (fun w => Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12 u z) w 0)
        =ᶠ[𝓝 z] fun w => -(Work.Construction.FK u w) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      have hwpos : 0 < w := hw
      show w * deriv (fun z' => Work.Construction.L12 u z') w = -(Work.Construction.FK u w)
      rw [(hL12hasDeriv w hw).deriv]
      field_simp
    have hderiv : deriv (fun w => Work.Spaces.DzIter 1
        (fun z _ => Work.Construction.L12 u z) w 0) z = -(I1 z) := by
      rw [hev.deriv_eq]
      exact ((hFKd z hz).neg).deriv
    have hval : Work.Spaces.DzIter 2 (fun z _ => Work.Construction.L12 u z) z 0
        = -Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK u z) z 0 := by
      show z * deriv (fun w => Work.Spaces.DzIter 1
          (fun z _ => Work.Construction.L12 u z) w 0) z
        = -(z * deriv (fun w => Work.Construction.FK u w) z)
      rw [hderiv, (hFKd z hz).deriv]
      ring
    rw [hval, abs_neg]
    calc |Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK u z) z 0|
        ≤ B' * (3 * (Real.pi / 2)) * L12Wt z := hFKjet1 z hz
      _ ≤ B' * (3 * (Real.pi / 2)) * z ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left (L12Wt_le_rpow hz) (mul_nonneg hB'0 (by positivity))
  ---------------------------------------------------------------------------------------------
  -- assembly
  ---------------------------------------------------------------------------------------------
  have hCpos : 0 < 3 * B' * (3 * (Real.pi / 2)) + 1 := by
    nlinarith [hB'0, Real.pi_pos]
  refine ⟨3 * B' * (3 * (Real.pi / 2)) + 1, hCpos, ?_, ?_, hFKcont,
    contDiffOn_three_L12 hFKcont, hL12hasDeriv⟩
  · intro j hj z hz
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    have hnn : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 := by positivity
    rcases hj' with rfl | rfl | rfl
    · have h : |Work.Spaces.DzIter 0 (fun z _ => Work.Construction.FK u z) z 0|
          ≤ B' * (3 * (Real.pi / 2)) * L12Wt z := by
        simpa only [Work.Spaces.DzIter_zero] using hFK0 z hz
      rw [L12Wt] at h
      calc |Work.Spaces.DzIter 0 (fun z _ => Work.Construction.FK u z) z 0|
          ≤ B' * (3 * (Real.pi / 2)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := h
        _ ≤ (3 * B' * (3 * (Real.pi / 2)) + 1) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_right (by nlinarith [hB'0, Real.pi_pos]) hnn
    · have h : |Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK u z) z 0|
          ≤ B' * (3 * (Real.pi / 2)) * L12Wt z := hFKjet1 z hz
      rw [L12Wt] at h
      calc |Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK u z) z 0|
          ≤ B' * (3 * (Real.pi / 2)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := h
        _ ≤ (3 * B' * (3 * (Real.pi / 2)) + 1) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_right (by nlinarith [hB'0, Real.pi_pos]) hnn
    · have h : |Work.Spaces.DzIter 2 (fun z _ => Work.Construction.FK u z) z 0|
          ≤ 3 * (B' * (3 * (Real.pi / 2)) * L12Wt z) := hFKjet2 z hz
      rw [L12Wt] at h
      calc |Work.Spaces.DzIter 2 (fun z _ => Work.Construction.FK u z) z 0|
          ≤ 3 * (B' * (3 * (Real.pi / 2)) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) := h
        _ = (3 * (B' * (3 * (Real.pi / 2)))) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by ring
        _ ≤ (3 * B' * (3 * (Real.pi / 2)) + 1) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_right (by nlinarith [hB'0, Real.pi_pos]) hnn
  · intro j hj z hz
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    have hnn : 0 ≤ z ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hz.le _
    rcases hj' with rfl | rfl | rfl
    · have h : |Work.Spaces.DzIter 0 (fun z _ => Work.Construction.L12 u z) z 0|
          ≤ B' * (3 * (Real.pi / 2)) * z ^ ((3 : ℝ) / 2) := by
        simpa only [Work.Spaces.DzIter_zero] using hL12jet0 z hz
      calc |Work.Spaces.DzIter 0 (fun z _ => Work.Construction.L12 u z) z 0|
          ≤ B' * (3 * (Real.pi / 2)) * z ^ ((3 : ℝ) / 2) := h
        _ ≤ (3 * B' * (3 * (Real.pi / 2)) + 1) * z ^ ((3 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (by nlinarith [hB'0, Real.pi_pos]) hnn
    · calc |Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12 u z) z 0|
          ≤ B' * (3 * (Real.pi / 2)) * z ^ ((3 : ℝ) / 2) := hL12jet1 z hz
        _ ≤ (3 * B' * (3 * (Real.pi / 2)) + 1) * z ^ ((3 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (by nlinarith [hB'0, Real.pi_pos]) hnn
    · calc |Work.Spaces.DzIter 2 (fun z _ => Work.Construction.L12 u z) z 0|
          ≤ B' * (3 * (Real.pi / 2)) * z ^ ((3 : ℝ) / 2) := hL12jet2 z hz
        _ ≤ (3 * B' * (3 * (Real.pi / 2)) + 1) * z ^ ((3 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (by nlinarith [hB'0, Real.pi_pos]) hnn

end

end Work.FTS_RegExport.RXT.SysAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.L12_tail_weight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

open MeasureTheory Set

/-!
# Tail bound for the `L12` weight

If `g` is integrable on `(0,∞)`, has *vanishing total integral* `∫_{(0,∞)} g = 0`, and obeys the
pointwise bound `|g r| ≤ B √r / (1+r)²`, then the tail integral over `(z,∞)` satisfies

  `|∫_{(z,∞)} g| ≤ 8 B z^{3/2} / (1+z)²`.

This is the sharp form of the crude bound `|∫_{(z,∞)} g| ≤ B z^{3/2}` (which one gets from
`∫_{(z,∞)} g = -∫_{(0,z]} g` together with the pointwise bound `|g r| ≤ B √z` on `(0,z]`):
the crude bound is useless for large `z`, where the weight `√r/(1+r)² ≍ r^{-3/2}` actually makes
the tail decay like `z^{-1/2}`.

The proof therefore splits into two regimes.

* **`z ≤ 1`**: use the head integral `∫_{(0,z]} g = -∫_{(z,∞)} g` and the crude bound
  `B z^{3/2}` (this is `abs_setIntegral_Ioi_le_of_integral_zero_aux`); since `(1+z)² ≤ 4` here,
  `B z^{3/2} ≤ 8 B z^{3/2}/(1+z)²`.
* **`z ≥ 1`**: bound the tail directly,
  `|∫_{(z,∞)} g| ≤ ∫_{(z,∞)} B√r/(1+r)² ≤ B ∫_{(z,∞)} r^{-3/2} = 2 B z^{-1/2}`,
  and `2 z^{-1/2} ≤ 8 z^{3/2}/(1+z)²` because `(1+z)² ≤ 4 z²` for `z ≥ 1`.
-/

/-- The tail bound, in the regime `z ≤ 1`, obtained from the head integral. -/
private lemma L12_tail_small {g : ℝ → ℝ} {B z : ℝ}
    (hB : 0 ≤ B) (hz : 0 < z) (hz1 : z ≤ 1)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0))
    (hbd : ∀ r : ℝ, 0 < r → |g r| ≤ B * (Real.sqrt r / (1 + r) ^ 2))
    (h0 : ∫ r in Set.Ioi 0, g r = 0) :
    |∫ r in Set.Ioi z, g r| ≤ 8 * B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
  have hden : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  have hr : (0 : ℝ) < z ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hz _
  -- `(1+z)^2 ≤ 4 ≤ 8`, so `1 ≤ 8/(1+z)^2`
  have hle : (1 : ℝ) ≤ 8 / (1 + z) ^ 2 := by
    rw [le_div_iff₀ hden]
    nlinarith
  calc |∫ r in Set.Ioi z, g r| ≤ B * z ^ ((3 : ℝ) / 2) :=
        abs_setIntegral_Ioi_le_of_integral_zero_aux hB hz hint hbd h0
    _ ≤ B * ((8 / (1 + z) ^ 2) * z ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hr.le hle) hB
    _ = 8 * B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by ring

/-- The tail bound, in the regime `z ≥ 1`, obtained by bounding the tail integral directly
against `∫_{(z,∞)} r^{-3/2} = 2 z^{-1/2}`. -/
private lemma L12_tail_large {g : ℝ → ℝ} {B z : ℝ}
    (hB : 0 ≤ B) (hz : 0 < z) (hz1 : 1 ≤ z)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0))
    (hbd : ∀ r : ℝ, 0 < r → |g r| ≤ B * (Real.sqrt r / (1 + r) ^ 2)) :
    |∫ r in Set.Ioi z, g r| ≤ 8 * B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
  have hzle : (0 : ℝ) ≤ z := le_of_lt hz
  have hInt_z : MeasureTheory.IntegrableOn g (Set.Ioi z) :=
    hint.mono_set (Set.Ioi_subset_Ioi hzle)
  have hAbs : MeasureTheory.IntegrableOn (fun r : ℝ => |g r|) (Set.Ioi z) :=
    MeasureTheory.Integrable.abs hInt_z
  -- the comparison function `√r/(1+r)²` is integrable on `(z,∞)`
  have hPhi_int : MeasureTheory.IntegrableOn (fun r : ℝ => Real.sqrt r / (1 + r) ^ 2)
      (Set.Ioi z) := by
    refine MeasureTheory.Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ) / 2) (c := z) (by norm_num) hz) ?_ ?_
    · exact (Real.continuous_sqrt.measurable.div (by fun_prop)).aestronglyMeasurable.restrict
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : (0 : ℝ) < r := lt_trans hz hr
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hstep : Real.sqrt r / (1 + r) ^ 2 ≤ Real.sqrt r / r ^ 2 :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg r) (by positivity) (by nlinarith)
      have heq : Real.sqrt r / r ^ 2 = r ^ (-(3 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast r 2, ← Real.rpow_sub hr0]
        norm_num
      linarith [hstep, heq.le]
  have hIntB : MeasureTheory.IntegrableOn (fun r : ℝ => B * (Real.sqrt r / (1 + r) ^ 2))
      (Set.Ioi z) := MeasureTheory.Integrable.const_mul hPhi_int B
  have hRpow_int : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ (-(3 : ℝ) / 2)) (Set.Ioi z) :=
    integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ) / 2) (c := z) (by norm_num) hz
  have hstep2 : ∫ r in Set.Ioi z, |g r|
      ≤ ∫ r in Set.Ioi z, B * (Real.sqrt r / (1 + r) ^ 2) :=
    MeasureTheory.setIntegral_mono_on hAbs hIntB measurableSet_Ioi
      (fun r hr => hbd r (lt_trans hz hr))
  have hstep4 : ∫ r in Set.Ioi z, (Real.sqrt r / (1 + r) ^ 2)
      ≤ ∫ r in Set.Ioi z, r ^ (-(3 : ℝ) / 2) := by
    refine MeasureTheory.setIntegral_mono_on hPhi_int hRpow_int measurableSet_Ioi
      (fun r hr => ?_)
    have hr0 : (0 : ℝ) < r := lt_trans hz hr
    have hstep : Real.sqrt r / (1 + r) ^ 2 ≤ Real.sqrt r / r ^ 2 :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg r) (by positivity) (by nlinarith)
    have heq : Real.sqrt r / r ^ 2 = r ^ (-(3 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast r 2, ← Real.rpow_sub hr0]
      norm_num
    linarith [hstep, heq.le]
  have hstep5 : ∫ r in Set.Ioi z, r ^ (-(3 : ℝ) / 2) = 2 * z ^ (-(1 : ℝ) / 2) := by
    rw [integral_Ioi_rpow_of_lt (a := -(3 : ℝ) / 2) (c := z) (by norm_num) hz]
    have h : (-(3 : ℝ) / 2 + 1) = (-(1 : ℝ) / 2) := by norm_num
    rw [h]
    ring
  have hard : 2 * z ^ (-(1 : ℝ) / 2) ≤ 8 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    have hs : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz
    have hsq : Real.sqrt z * Real.sqrt z = z := Real.mul_self_sqrt hz.le
    have h32 : z ^ ((3 : ℝ) / 2) = Real.sqrt z * z := by
      rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = (1 : ℝ) / 2 + 1 by norm_num,
        Real.rpow_add hz, Real.rpow_one]
    have hm : z ^ (-(1 : ℝ) / 2) = (Real.sqrt z)⁻¹ := by
      rw [Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
        Real.rpow_neg hz.le, one_div]
    rw [h32, hm]
    have hcomb : 8 * (√z * z / (1 + z) ^ 2) = 8 * (√z * z) / (1 + z) ^ 2 := by ring
    rw [hcomb, le_div_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
    have hre : 2 * (√z)⁻¹ * (1 + z) ^ 2 = (√z)⁻¹ * (2 * (1 + z) ^ 2) := by ring
    rw [hre, inv_mul_le_iff₀ hs]
    nlinarith [hsq, hz1, sq_nonneg (1 + z), sq_nonneg z]
  calc |∫ r in Set.Ioi z, g r| ≤ ∫ r in Set.Ioi z, |g r| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ r in Set.Ioi z, B * (Real.sqrt r / (1 + r) ^ 2) := hstep2
    _ = B * ∫ r in Set.Ioi z, (Real.sqrt r / (1 + r) ^ 2) :=
        MeasureTheory.integral_const_mul B _
    _ ≤ B * ∫ r in Set.Ioi z, r ^ (-(3 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hstep4 hB
    _ = B * (2 * z ^ (-(1 : ℝ) / 2)) := by rw [hstep5]
    _ ≤ 8 * B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
        have := mul_le_mul_of_nonneg_left hard hB
        nlinarith [this]

theorem L12_tail_weight {g : ℝ → ℝ} {B z : ℝ}
    (hB : 0 ≤ B) (hz : 0 < z)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0))
    (hbd : ∀ r : ℝ, 0 < r → |g r| ≤ B * (Real.sqrt r / (1 + r) ^ 2))
    (h0 : ∫ r in Set.Ioi 0, g r = 0) :
    |∫ r in Set.Ioi z, g r| ≤ 8 * B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
  rcases le_or_gt z 1 with hz1 | hz1
  · exact L12_tail_small hB hz hz1 hint hbd h0
  · exact L12_tail_large hB hz (le_of_lt hz1) hint hbd

end Work.FTS_RegExport.RXT.SysAux
end
