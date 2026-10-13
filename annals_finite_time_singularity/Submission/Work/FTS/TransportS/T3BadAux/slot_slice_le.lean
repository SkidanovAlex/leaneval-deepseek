import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T3BadAux

set_option autoImplicit false

theorem slot_slice_le {α Mf θ : ℝ} {f g : ℝ → ℝ → ℝ} (k : Fin 5) (hMf : 0 ≤ Mf)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hφcd : ContDiffOn ℝ 1 (fun z => f z θ) (Set.Ioi (0 : ℝ)))
    (hucd : ContDiffOn ℝ 1 (fun z => Work.FTS.H2.Thard g k z θ) (Set.Ioi (0 : ℝ)))
    (hfb : ∀ z ∈ Work.Spaces.Iz, |f z θ| ≤ Mf)
    (hDfb : ∀ z ∈ Work.Spaces.Iz, |Work.Spaces.Dz f z θ| ≤ Mf)
    (htr0 : Filter.Tendsto
      (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htrT : Filter.Tendsto
      (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
      Filter.atTop (nhds 0))
    (hint1 : MeasureTheory.IntegrableOn (fun z => f z θ * z * (Work.Spaces.w z) ^ 2
        * Work.FTS.H2.Thard g k z θ * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
        (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn
        (fun z => Work.FTS.TransportS.gK' α f g k z θ) (Set.Ioi 0))
    (hint3 : MeasureTheory.IntegrableOn
        (fun z => (Work.FTS.TransportS.Xz α g k z θ) ^ 2) (Set.Ioi 0)) :
    |∫ z in Set.Ioi (0 : ℝ), Work.FTS.TransportS.gK α f g k z θ|
      ≤ 2 * Mf * ∫ z in Set.Ioi (0 : ℝ), (Work.FTS.TransportS.Xz α g k z θ) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  set S : ℝ := Work.FTS.H2.sghard α k θ with hS
  set V : ℝ → ℝ := fun z => Work.FTS.H2.Thard g k z θ with hV
  set V' : ℝ → ℝ := fun z => Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ with hV'
  set φ : ℝ → ℝ := fun z => f z θ * (z * (Work.Spaces.w z) ^ 2) with hφ
  set φ' : ℝ → ℝ := fun z => Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
      + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) with hφ'
  have hSpos : 0 < S := by
    rw [hS]
    rcases eq_or_ne k.val 0 with hk | hk
    · rw [show k = 0 from Fin.ext hk, Work.FTS.H2.sghard_apply_zero]
      exact Real.rpow_pos_of_pos hsin _
    · rw [Work.FTS.H2.sghard_apply_ne α k hk θ]
      exact Real.rpow_pos_of_pos hsin _
  have hSne : S ≠ 0 := ne_of_gt hSpos
  -- ## The pointwise identities
  have hgK_pt : ∀ z : ℝ, gK α f g k z θ = S * (φ z * V z * V' z) := by
    intro z
    simp only [gK, hS, hφ, hV, hV'] <;> ring
  have hgK'_pt : ∀ z : ℝ, gK' α f g k z θ = φ' z * V z ^ 2 := by
    intro z
    simp only [gK', hφ', hV]
  have hXz_pt : ∀ z : ℝ, (Xz α g k z θ) ^ 2 = S * ((Work.Spaces.w z) ^ 2 * (V z) ^ 2) := by
    intro z
    simp only [hS, hV, Xz_sq (α := α) g k z θ hθI] <;> ring
  -- ## The derivative hypotheses
  have hderivV : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt V (V' z) z := by
    intro z hz
    have hd := ((hucd.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
    simp only [hV, hV', Work.Spaces.pz] at hd ⊢
    exact hd
  have hderivφ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (φ' z) z := by
    intro z hz
    have hf : HasDerivAt (fun z' => f z' θ) (Work.Spaces.pz f z θ) z := by
      have hd := ((hφcd.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hz)).hasDerivAt
      simpa only [Work.Spaces.pz] using hd
    have hzw := Work.FTS.H2.hasDerivAt_zw2 hz
    have h := hf.mul hzw
    simp only [hφ, hφ'] at h ⊢
    convert h using 1
    ring
  -- ## The transfer of the integrability and boundary hypotheses
  have hlim0 : Filter.Tendsto (fun z => z * (V z * Work.Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa only [hV] using htr0
  have hlimTop : Filter.Tendsto (fun z => z * (V z * Work.Spaces.w z) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa only [hV] using htrT
  have hint1' : MeasureTheory.IntegrableOn (fun z => φ z * V z * V' z)
      (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun hint1 ?_ measurableSet_Ioi
    intro z _
    simp only [hφ, hV, hV'] <;> ring
  have hint2' : MeasureTheory.IntegrableOn (fun z => φ' z * V z ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun hint2 ?_ measurableSet_Ioi
    intro z _
    simp only [gK', hφ', hV]
  have hφbnd : ∀ z ∈ Set.Ici (0 : ℝ), |φ z| ≤ Mf * (z * (Work.Spaces.w z) ^ 2) := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := hz
    have hzw : 0 ≤ z * (Work.Spaces.w z) ^ 2 := mul_nonneg hz (sq_nonneg _)
    simp only [hφ]
    rw [abs_mul, abs_of_nonneg hzw]
    exact mul_le_mul_of_nonneg_right (hfb z hzIz) hzw
  -- ## The pointwise bound for the integration-by-parts integrand
  have hgK'_le : ∀ z : ℝ, 0 < z →
      |gK' α f g k z θ| ≤ 4 * Mf * ((Work.Spaces.w z) ^ 2 * (V z) ^ 2) := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hratio : |(z - 3) / (1 + z)| ≤ 3 := Work.FTS.H2.abs_ratio_le_three z hz
    have h2 : |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2|
        ≤ Mf * (Work.Spaces.w z) ^ 2 := by
      rw [show Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
            = (Work.Spaces.pz f z θ * z) * (Work.Spaces.w z) ^ 2 from by ring,
        abs_mul, abs_of_nonneg hw2,
        show |Work.Spaces.pz f z θ * z| = |Work.Spaces.Dz f z θ| from by
          rw [Work.Spaces.Dz, mul_comm]]
      exact mul_le_mul_of_nonneg_right (hDfb z hzIz) hw2
    have h3 : |f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
        ≤ 3 * Mf * (Work.Spaces.w z) ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw2]
      calc |f z θ| * ((Work.Spaces.w z) ^ 2 * |(z - 3) / (1 + z)|)
          ≤ Mf * ((Work.Spaces.w z) ^ 2 * 3) :=
            mul_le_mul (hfb z hzIz) (mul_le_mul_of_nonneg_left hratio hw2)
              (mul_nonneg hw2 (abs_nonneg _)) hMf
        _ = 3 * Mf * (Work.Spaces.w z) ^ 2 := by ring
    have h1 : |φ' z| ≤ 4 * Mf * (Work.Spaces.w z) ^ 2 := by
      simp only [hφ']
      calc |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
              + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
          ≤ |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2|
            + |f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))| := abs_add_le _ _
        _ ≤ Mf * (Work.Spaces.w z) ^ 2 + 3 * Mf * (Work.Spaces.w z) ^ 2 := add_le_add h2 h3
        _ = 4 * Mf * (Work.Spaces.w z) ^ 2 := by ring
    rw [hgK'_pt z, abs_mul, abs_of_nonneg (sq_nonneg (V z))]
    calc |φ' z| * V z ^ 2 ≤ (4 * Mf * (Work.Spaces.w z) ^ 2) * V z ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = 4 * Mf * ((Work.Spaces.w z) ^ 2 * V z ^ 2) := by ring
  -- ## The monotonicity step against the `Xz²`-majorant
  have hMle : (∫ z in Set.Ioi (0 : ℝ), |gK' α f g k z θ|)
      ≤ (4 * Mf / S) * ∫ z in Set.Ioi (0 : ℝ), (Xz α g k z θ) ^ 2 := by
    have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        |gK' α f g k z θ| ≤ (4 * Mf / S) * (Xz α g k z θ) ^ 2 := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      calc |gK' α f g k z θ| ≤ 4 * Mf * ((Work.Spaces.w z) ^ 2 * (V z) ^ 2) := hgK'_le z hz
        _ = (4 * Mf / S) * (Xz α g k z θ) ^ 2 := by
            rw [hXz_pt z]
            field_simp
    calc (∫ z in Set.Ioi (0 : ℝ), |gK' α f g k z θ|)
        ≤ ∫ z in Set.Ioi (0 : ℝ), (4 * Mf / S) * (Xz α g k z θ) ^ 2 :=
          MeasureTheory.integral_mono_ae hint2.abs
            (MeasureTheory.Integrable.const_mul hint3 (4 * Mf / S)) hpt
      _ = (4 * Mf / S) * ∫ z in Set.Ioi (0 : ℝ), (Xz α g k z θ) ^ 2 :=
          MeasureTheory.integral_const_mul (4 * Mf / S) _
  -- ## The integration by parts identity
  have hIntgK : (∫ z in Set.Ioi (0 : ℝ), gK α f g k z θ)
      = -(S / 2) * ∫ z in Set.Ioi (0 : ℝ), gK' α f g k z θ := by
    have hzibp := zibp_Ioi (Mf := Mf) hMf hderivφ hderivV hint1' hint2' hφbnd hlim0 hlimTop
    have hIntK' : (∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2)
        = ∫ z in Set.Ioi (0 : ℝ), gK' α f g k z θ :=
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun z => (hgK'_pt z).symm))
    have h1 : (∫ z in Set.Ioi (0 : ℝ), gK α f g k z θ)
        = S * ∫ z in Set.Ioi (0 : ℝ), φ z * V z * V' z := by
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hgK_pt)]
      exact MeasureTheory.integral_const_mul S (fun z => φ z * V z * V' z)
    rw [h1, hzibp, hIntK']
    ring
  -- ## Conclusion
  have habs : |∫ z in Set.Ioi (0 : ℝ), gK α f g k z θ|
      = (S / 2) * |∫ z in Set.Ioi (0 : ℝ), gK' α f g k z θ| := by
    rw [hIntgK, abs_mul, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ S / 2)]
  calc |∫ z in Set.Ioi (0 : ℝ), gK α f g k z θ|
      = (S / 2) * |∫ z in Set.Ioi (0 : ℝ), gK' α f g k z θ| := habs
    _ ≤ (S / 2) * (∫ z in Set.Ioi (0 : ℝ), |gK' α f g k z θ|) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        simpa only [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm (fun z => gK' α f g k z θ)
    _ ≤ (S / 2) * ((4 * Mf / S) * ∫ z in Set.Ioi (0 : ℝ), (Xz α g k z θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hMle (by linarith)
    _ = 2 * Mf * ∫ z in Set.Ioi (0 : ℝ), (Xz α g k z θ) ^ 2 := by
        field_simp
        ring

end Work.FTS.TransportS.T3BadAux
