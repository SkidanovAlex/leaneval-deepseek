import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Uop_PhiTs_bounds
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Uop_PhiTs_slice_zero
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_FstarRadial
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_SmoothQuadPthFstar
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_PthFstarMixed
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_bookkeeping
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_bad
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_bad_hi
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_notGood
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_pzIter_tendsto
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS.LocData.DzIter_FM_Fstar_abs_le
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 3200000

noncomputable section

/-! ## Unconditional linearity of the `D`-operators over constant multiples

`mixed j i (fun z θ => c * f z θ) = c * mixed j i f z θ` holds for **every** constant `c` and
every `f`, with no regularity hypothesis: if `f` is not differentiable at a point then neither
is `c * f` (for `c ≠ 0`) and both sides are `0`.  This is the same observation as
`Work.FTS.LocData.deriv_const_mul_uncond`; it is needed here to pull the factor `-2` of
`N₂^{ss} = -2 U(Φ̃_*) ∂_θF_*` out of the Leibniz expansion. -/

private theorem deriv_cmul (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

private theorem pz_cmul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_cmul]

private theorem Dz_cmul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Spaces.Dz]
  rw [pz_cmul]
  ring

private theorem pth_cmul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_cmul]

private theorem Dth_cmul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.Spaces.Dth]
  rw [pth_cmul]
  ring

private theorem DthIter_cmul (n : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter n (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter n f z θ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih, Dth_cmul]

private theorem DzIter_cmul (n : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter n (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter n f z θ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih, Dz_cmul]

private theorem mixed_cmul (j i : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  rw [Work.Spaces.mixed, Work.Spaces.mixed, DthIter_cmul, DzIter_cmul]

/-! ## Smoothness of `U(Φ̃_*)` on the open quadrant -/

theorem smoothQuad_Uop_PhiTs {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    Work.FTS.LocData.SmoothQuad
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) := by
  have hψ : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) :=
    row15aux.smoothQuad_PhiTs_cc hα hS
  have hdz : Work.FTS.LocData.SmoothQuad
      (Work.Spaces.Dz (Work.FTS.Nonlin.PhiTs α Φs)) := by
    simpa using Work.FTS.LocData.SmoothQuad.DzIter hψ 1
  have h1 : Work.FTS.LocData.SmoothQuad
      (fun z θ => -3 * Work.FTS.Nonlin.PhiTs α Φs z θ) :=
    Work.FTS.LocData.smoothQuad_const_mul (-3) hψ
  have h2 : Work.FTS.LocData.SmoothQuad
      (fun z θ => -α * (Work.Spaces.Dz (Work.FTS.Nonlin.PhiTs α Φs)) z θ) :=
    Work.FTS.LocData.smoothQuad_const_mul (-α) hdz
  have hsum : Work.FTS.LocData.SmoothQuad (fun z θ =>
      -3 * Work.FTS.Nonlin.PhiTs α Φs z θ
        + -α * (Work.Spaces.Dz (Work.FTS.Nonlin.PhiTs α Φs)) z θ) :=
    Work.FTS.LocData.smoothQuad_add h1 h2
  have heq : Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) = fun z θ =>
      -3 * Work.FTS.Nonlin.PhiTs α Φs z θ
        + -α * (Work.Spaces.Dz (Work.FTS.Nonlin.PhiTs α Φs)) z θ := by
    funext z θ
    simp only [Work.Construction.Uop, Work.Spaces.Dz]
    ring
  rwa [heq]

/-! ## The row-15 pointwise estimate on a "good" angular slice

Everything is proved here from the delivered U-side bounds (`Uop_PhiTs_bounds`), leaving the two
`F_*`-side inputs (`row15_SmoothQuadPthFstar`, `row15_PthFstarMixed`) as explicit hypotheses so
that the argument can be checked independently of them. -/

theorem row15_slot_bound_aux
    (hWq : ∀ α : ℝ,
      Work.FTS.LocData.SmoothQuad (Work.Spaces.pth (Work.Construction.Fstar α)))
    (hWb : ∃ Cw : ℝ, 0 < Cw ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (z : ℝ), 0 < z →
      ∀ (θ : ℝ), 0 < θ → θ < Real.pi / 2 → ∀ (m l : ℕ), m + l ≤ 4 →
        |Work.Spaces.mixed l m (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
          ≤ Cw * α ^ 2 * Work.Spaces.Gam α θ * (Real.sin (2 * θ))⁻¹
              * |(Work.Spaces.OpZ^[l]) Work.FM.Fstar z|) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α Cs z : ℝ} {Φs : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.Nonlin.StarPkg α Cs Φs → 0 < z →
      (∀ θ ∈ Work.Spaces.Iθ,
        Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) 0 θ = 0) →
      (∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun θ => Work.Spaces.DzIter b
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ i j : ℕ, i + j ≤ 4 →
        |Work.Spaces.mixed j i (Work.FTS.Nonlin.N2ss α Φs) z θ * Work.Spaces.w z|
          ≤ K * α ^ 3 * (Cs + 1) * Work.Spaces.Gam α θ * row15aux.rlog z := by
  obtain ⟨Cw, hCwpos, hWb⟩ := hWb
  obtain ⟨Cu, hCupos, hUop⟩ := row15aux.Uop_PhiTs_bounds
  obtain ⟨Cr, hCrpos, hRadF⟩ := row15aux.row15_FstarRadial
  have hCun : 0 ≤ Cu := le_of_lt hCupos
  have hCwn : 0 ≤ Cw := le_of_lt hCwpos
  have hCrn : 0 ≤ Cr := le_of_lt hCrpos
  refine ⟨30000 * Cu * Cw * Cr + 1, by positivity, ?_⟩
  intro α Cs z Φs hα hα1 hS hz hU0 hgood θ hθ i j hij
  have hCs : 0 ≤ Cs := row15aux.Cs_nonneg_of_starPkg hα hS
  have hαn : 0 ≤ α := le_of_lt hα
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hwnn : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]; positivity
  have hrlog : 0 ≤ row15aux.rlog z := row15aux.rlog_nonneg (le_of_lt hz)
  have hlognn : 0 ≤ Real.log (1 + z) := Real.log_nonneg (by linarith)
  have hlog1 : Real.log (1 + z) ≤ z := by
    have h := Real.log_le_sub_one_of_pos hz1
    linarith
  -- `log(1+z)/z ≤ rlog z` and `1/(1+z) ≤ rlog z`
  have hlogdiv : Real.log (1 + z) / z ≤ row15aux.rlog z := by
    have hkey : Real.log (1 + z) * (1 + z) ≤ z * (1 + Real.log (1 + z)) := by
      nlinarith [hlog1]
    rw [row15aux.rlog_def, div_le_div_iff₀ hz hz1]
    linarith [hkey]
  have hone_div : 1 / (1 + z) ≤ row15aux.rlog z := by
    have hkey : (1 : ℝ) * (1 + z) ≤ (1 + Real.log (1 + z)) * (1 + z) := by
      nlinarith [hlognn, hz1]
    rw [row15aux.rlog_def, div_le_div_iff₀ hz1 hz1]
    exact hkey
  -- the angular vanishing of `N₂^{ss}` at the two endpoints
  have hN2eq : Work.FTS.Nonlin.N2ss α Φs = fun z θ =>
      -2 * ((Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
        * Work.Spaces.pth (Work.Construction.Fstar α) z θ) := by
    funext z' θ'
    simp only [Work.FTS.Nonlin.N2ss]
    ring
  have hUθ0 : ∀ z' : ℝ,
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z' 0 = 0 :=
    fun z' => hS.vanishU.1 z'
  have hUθπ : ∀ z' : ℝ,
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z' (π / 2) = 0 :=
    fun z' => hS.vanishU.2 z'
  have hsinπ : Real.sin (2 * (π / 2)) = 0 := by
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
  have hN2_0 : ∀ z' : ℝ, Work.FTS.Nonlin.N2ss α Φs z' 0 = 0 := by
    intro z'
    rw [hN2eq]
    simp [hUθ0 z']
  have hN2_π : ∀ z' : ℝ, Work.FTS.Nonlin.N2ss α Φs z' (π / 2) = 0 := by
    intro z'
    rw [hN2eq]
    simp [hUθπ z']
  -- the vanishing of `Γ` at the two endpoints
  have hGam0 : Work.Spaces.Gam α 0 = 0 := by
    rw [Work.Spaces.Gam, show Real.sin (0 : ℝ) * Real.cos (0 : ℝ) ^ 2 = 0 by norm_num]
    exact Real.zero_rpow (by positivity : α / 3 ≠ 0)
  have hGamπ : Work.Spaces.Gam α (π / 2) = 0 := by
    rw [Work.Spaces.Gam]
    have h : Real.sin (π / 2) * Real.cos (π / 2) ^ 2 = 0 := by
      rw [Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
    rw [h]
    exact Real.zero_rpow (by positivity : α / 3 ≠ 0)
  rcases eq_or_lt_of_le hθ.1 with hθz0 | hθz
  · -- ## `θ = 0`
    rw [← hθz0]
    have hleft : Work.Spaces.mixed j i (Work.FTS.Nonlin.N2ss α Φs) z 0 = 0 := by
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        change (fun z' => Work.Spaces.DzIter j (Work.FTS.Nonlin.N2ss α Φs) z' 0) z = 0
        have h1 : (fun z' => Work.Spaces.DzIter j (Work.FTS.Nonlin.N2ss α Φs) z' 0)
            = (Work.Spaces.OpZ^[j]) (fun z' => Work.FTS.Nonlin.N2ss α Φs z' 0) :=
          Work.Spaces.sliceZ_DzIter j (Work.FTS.Nonlin.N2ss α Φs) 0
        have h2 : (fun z' => Work.FTS.Nonlin.N2ss α Φs z' 0) = fun _ => (0 : ℝ) :=
          funext hN2_0
        rw [h1, h2, Work.Spaces.OpZ_iterate_zero]
      · exact Work.Spaces.mixed_eq_zero_of_sin_eq_zero (θ := 0) (by simp) hipos
    rw [hleft, zero_mul, abs_zero, hGam0]
    simp
  rcases eq_or_lt_of_le hθ.2 with hθπ | hθπ
  · -- ## `θ = π/2`
    rw [hθπ]
    have hleft : Work.Spaces.mixed j i (Work.FTS.Nonlin.N2ss α Φs) z (π / 2) = 0 := by
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        change (fun z' => Work.Spaces.DzIter j (Work.FTS.Nonlin.N2ss α Φs) z' (π / 2)) z = 0
        have h1 : (fun z' => Work.Spaces.DzIter j (Work.FTS.Nonlin.N2ss α Φs) z' (π / 2))
            = (Work.Spaces.OpZ^[j]) (fun z' => Work.FTS.Nonlin.N2ss α Φs z' (π / 2)) :=
          Work.Spaces.sliceZ_DzIter j (Work.FTS.Nonlin.N2ss α Φs) (π / 2)
        have h2 : (fun z' => Work.FTS.Nonlin.N2ss α Φs z' (π / 2)) = fun _ => (0 : ℝ) :=
          funext hN2_π
        rw [h1, h2, Work.Spaces.OpZ_iterate_zero]
      · exact Work.Spaces.mixed_eq_zero_of_sin_eq_zero (θ := π / 2) hsinπ hipos
    rw [hleft, zero_mul, abs_zero, hGamπ]
    simp
  -- ## the interior case `0 < θ < π/2`
  have hθi : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθz, hθπ⟩
  have hs2pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs2le : 0 ≤ Real.sin (2 * θ) := le_of_lt hs2pos
  have hΓnn : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  obtain ⟨hUb0, hUb1, hUb2⟩ := hUop hα hα1 hS hz hU0 hgood
  -- the `F_*`-side inputs
  have hWbd : ∀ m l : ℕ, m + l ≤ 4 →
      |Work.Spaces.mixed l m (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
        ≤ Cw * α ^ 2 * Work.Spaces.Gam α θ * (Real.sin (2 * θ))⁻¹
            * |(Work.Spaces.OpZ^[l]) Work.FM.Fstar z| :=
    fun m l hml => hWb α hα hα1 z hz θ hθz hθπ m l hml
  have hT1 : Work.FTS.LocData.T1F = Work.Spaces.OpZ := rfl
  have hRadl : ∀ l : ℕ, l ≤ 4 →
      |(Work.Spaces.OpZ^[l]) Work.FM.Fstar z| ≤ Cr * z / (1 + z) ^ 2 := by
    intro l hl
    have h := hRadF l hl z θ hz
    rw [Work.FTS.LocData.DzIter_Fstar_eq_T1, hT1] at h
    exact h
  have hradw : ∀ l : ℕ, l ≤ 4 →
      |(Work.Spaces.OpZ^[l]) Work.FM.Fstar z| * Work.Spaces.w z ≤ Cr / z := by
    intro l hl
    have h1 := hRadl l hl
    have h2 : (0 : ℝ) ≤ (1 + z) ^ 2 / z ^ 2 := by positivity
    have h3 : |(Work.Spaces.OpZ^[l]) Work.FM.Fstar z| * ((1 + z) ^ 2 / z ^ 2) ≤ Cr / z := by
      refine le_trans (mul_le_mul_of_nonneg_right h1 h2) ?_
      rw [show Cr * z / (1 + z) ^ 2 * ((1 + z) ^ 2 / z ^ 2) = Cr / z from by
        field_simp]
    simpa only [Work.Spaces.w] using h3
  -- the `sin 2θ`-weighted `F_*`-side bound
  have hWs2 : ∀ m l : ℕ, m + l ≤ 4 →
      Real.sin (2 * θ)
          * |Work.Spaces.mixed l m (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
        ≤ Cw * α ^ 2 * Work.Spaces.Gam α θ * |(Work.Spaces.OpZ^[l]) Work.FM.Fstar z| := by
    intro m l hml
    have h1 := mul_le_mul_of_nonneg_left (hWbd m l hml) hs2le
    have h2 : Real.sin (2 * θ) * (Cw * α ^ 2 * Work.Spaces.Gam α θ
        * (Real.sin (2 * θ))⁻¹ * |(Work.Spaces.OpZ^[l]) Work.FM.Fstar z|)
        = Cw * α ^ 2 * Work.Spaces.Gam α θ * |(Work.Spaces.OpZ^[l]) Work.FM.Fstar z| := by
      rw [show Real.sin (2 * θ) * (Cw * α ^ 2 * Work.Spaces.Gam α θ
            * (Real.sin (2 * θ))⁻¹ * |(Work.Spaces.OpZ^[l]) Work.FM.Fstar z|)
          = (Cw * α ^ 2 * Work.Spaces.Gam α θ
              * |(Work.Spaces.OpZ^[l]) Work.FM.Fstar z|)
            * (Real.sin (2 * θ) * (Real.sin (2 * θ))⁻¹) from by ring,
        mul_inv_cancel₀ (ne_of_gt hs2pos), mul_one]
    rwa [h2] at h1
  -- ## the Leibniz expansion of `N₂^{ss}`
  have hU_sm : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) := smoothQuad_Uop_PhiTs hα hS
  have hW_sm : Work.FTS.LocData.SmoothQuad
      (Work.Spaces.pth (Work.Construction.Fstar α)) := hWq α
  have hleib := Work.FTS.H2.HQ.mixed_mul_eq_quad j i
    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))
    (Work.Spaces.pth (Work.Construction.Fstar α)) hU_sm hW_sm z (le_of_lt hz) θ hθi
  have hLHS : |-2 * Work.Spaces.mixed j i (fun z θ =>
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ) z θ
        * Work.Spaces.w z|
      = 2 * (|Work.Spaces.mixed j i (fun z θ =>
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
            * Work.Spaces.pth (Work.Construction.Fstar α) z θ) z θ| * Work.Spaces.w z) := by
    rw [abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hwnn]
    ring
  -- nonnegativity of the collecting constants
  have hABs : (0 : ℝ) ≤ Cu * Cw * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ := by
    have h1 : (0 : ℝ) ≤ Cu * Cw * (Cs + 1) * α ^ 3 := by positivity
    exact mul_nonneg h1 hΓnn
  have hMnn : 0 ≤ 2 * Cu * Cw * Cr * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
      * row15aux.rlog z := by
    have h1 : (0 : ℝ) ≤ Cu * Cw * Cr * (Cs + 1) * α ^ 3 := by positivity
    exact mul_nonneg (mul_nonneg (by linarith) hΓnn) hrlog
  -- ## the per-summand bound
  have hpair : ∀ a b : ℕ, a ≤ i → b ≤ j →
      |Work.Spaces.mixed b a (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        * |Work.Spaces.mixed (j - b) (i - a)
            (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
        * Work.Spaces.w z
        ≤ 2 * Cu * Cw * Cr * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ * row15aux.rlog z := by
    intro a b hai hbj
    have hml : (i - a) + (j - b) ≤ 4 := by omega
    have hab4 : a + b ≤ 4 := by omega
    have hj4 : j ≤ 4 := by omega
    have hb4 : b ≤ 4 := by omega
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · subst ha0
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos
      · -- ### `a = 0`, `b = 0`
        subst hb0
        have hXb : |Work.Spaces.mixed 0 0
            (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
            ≤ Cu * (Cs + 1) * α * Real.sin (2 * θ) * Real.log (1 + z) := by
          simpa using hUb0 θ hθ
        have hYb : Real.sin (2 * θ) * |Work.Spaces.mixed (j - 0) (i - 0)
            (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
            ≤ Cw * α ^ 2 * Work.Spaces.Gam α θ * |(Work.Spaces.OpZ^[j]) Work.FM.Fstar z| := by
          simpa using hWs2 i j (by omega)
        have hXb0 : 0 ≤ Cu * (Cs + 1) * α * Real.sin (2 * θ) * Real.log (1 + z) := by
          positivity
        have hFw : Real.log (1 + z)
            * (|(Work.Spaces.OpZ^[j]) Work.FM.Fstar z| * Work.Spaces.w z)
            ≤ 2 * Cr * row15aux.rlog z := by
          have h1 : |(Work.Spaces.OpZ^[j]) Work.FM.Fstar z| * Work.Spaces.w z ≤ Cr / z :=
            hradw j hj4
          have h2 : Real.log (1 + z) * (Cr / z) ≤ 2 * Cr * row15aux.rlog z := by
            rw [show Real.log (1 + z) * (Cr / z) = Cr * (Real.log (1 + z) / z) from by ring]
            nlinarith [hlogdiv, hCrn, hrlog]
          exact le_trans (mul_le_mul_of_nonneg_left h1 hlognn) h2
        calc |Work.Spaces.mixed 0 0
              (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
              * |Work.Spaces.mixed (j - 0) (i - 0)
                  (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
              * Work.Spaces.w z
            ≤ (Cu * (Cs + 1) * α * Real.sin (2 * θ) * Real.log (1 + z))
              * |Work.Spaces.mixed (j - 0) (i - 0)
                  (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
              * Work.Spaces.w z :=
                mul_le_mul_of_nonneg_right (mul_le_mul hXb le_rfl (abs_nonneg _) hXb0) hwnn
          _ = Cu * (Cs + 1) * α * Real.log (1 + z)
              * (Real.sin (2 * θ) * |Work.Spaces.mixed (j - 0) (i - 0)
                  (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|) * Work.Spaces.w z := by
                ring
          _ ≤ Cu * (Cs + 1) * α * Real.log (1 + z)
              * (Cw * α ^ 2 * Work.Spaces.Gam α θ
                  * |(Work.Spaces.OpZ^[j]) Work.FM.Fstar z|) * Work.Spaces.w z :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYb (by positivity)) hwnn
          _ = Cu * Cw * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
              * (Real.log (1 + z)
                  * (|(Work.Spaces.OpZ^[j]) Work.FM.Fstar z| * Work.Spaces.w z)) := by ring
          _ ≤ Cu * Cw * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
              * (2 * Cr * row15aux.rlog z) := mul_le_mul_of_nonneg_left hFw hABs
          _ = 2 * Cu * Cw * Cr * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
              * row15aux.rlog z := by ring
      · -- ### `a = 0`, `b ≥ 1`
        have hXb : |Work.Spaces.mixed b 0
            (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
            ≤ Cu * (Cs + 1) * α * Real.sin (2 * θ) * (z / (1 + z)) := by
          simpa using hUb1 b hbpos hb4 θ hθ
        have hYb : Real.sin (2 * θ) * |Work.Spaces.mixed (j - b) (i - 0)
            (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
            ≤ Cw * α ^ 2 * Work.Spaces.Gam α θ
                * |(Work.Spaces.OpZ^[j - b]) Work.FM.Fstar z| := by
          simpa using hWs2 i (j - b) hml
        have hXb0 : 0 ≤ Cu * (Cs + 1) * α * Real.sin (2 * θ) * (z / (1 + z)) := by
          positivity
        have hFw : (z / (1 + z))
            * (|(Work.Spaces.OpZ^[j - b]) Work.FM.Fstar z| * Work.Spaces.w z)
            ≤ 2 * Cr * row15aux.rlog z := by
          have h1 : |(Work.Spaces.OpZ^[j - b]) Work.FM.Fstar z| * Work.Spaces.w z ≤ Cr / z :=
            hradw (j - b) (by omega)
          have h2 : (z / (1 + z)) * (Cr / z) ≤ 2 * Cr * row15aux.rlog z := by
            rw [show (z / (1 + z)) * (Cr / z) = Cr * (1 / (1 + z)) from by
              field_simp]
            nlinarith [hone_div, hCrn, hrlog]
          exact le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
        calc |Work.Spaces.mixed b 0
              (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
              * |Work.Spaces.mixed (j - b) (i - 0)
                  (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
              * Work.Spaces.w z
            ≤ (Cu * (Cs + 1) * α * Real.sin (2 * θ) * (z / (1 + z)))
              * |Work.Spaces.mixed (j - b) (i - 0)
                  (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
              * Work.Spaces.w z :=
                mul_le_mul_of_nonneg_right (mul_le_mul hXb le_rfl (abs_nonneg _) hXb0) hwnn
          _ = Cu * (Cs + 1) * α * (z / (1 + z))
              * (Real.sin (2 * θ) * |Work.Spaces.mixed (j - b) (i - 0)
                  (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|) * Work.Spaces.w z := by
                ring
          _ ≤ Cu * (Cs + 1) * α * (z / (1 + z))
              * (Cw * α ^ 2 * Work.Spaces.Gam α θ
                  * |(Work.Spaces.OpZ^[j - b]) Work.FM.Fstar z|) * Work.Spaces.w z :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYb (by positivity)) hwnn
          _ = Cu * Cw * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
              * ((z / (1 + z))
                  * (|(Work.Spaces.OpZ^[j - b]) Work.FM.Fstar z| * Work.Spaces.w z)) := by ring
          _ ≤ Cu * Cw * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
              * (2 * Cr * row15aux.rlog z) := mul_le_mul_of_nonneg_left hFw hABs
          _ = 2 * Cu * Cw * Cr * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
              * row15aux.rlog z := by ring
    · -- ### `a ≥ 1`
        have hXb : |Work.Spaces.mixed b a
            (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
            ≤ Cu * (Cs + 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))
                * (z / (1 + z)) := by
          simpa only [Work.Spaces.mixed] using hUb2 a b hapos hab4 θ hθ
        have hYb : Real.sin (2 * θ) * |Work.Spaces.mixed (j - b) (i - a)
            (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
            ≤ Cw * α ^ 2 * Work.Spaces.Gam α θ
                * |(Work.Spaces.OpZ^[j - b]) Work.FM.Fstar z| := hWs2 (i - a) (j - b) hml
        have hXb0 : 0 ≤ Cu * (Cs + 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))
            * (z / (1 + z)) := by
          have h1 : 0 ≤ 1 + Real.sin (2 * θ) := by linarith
          positivity
        have h1s : 1 + Real.sin (2 * θ) ≤ 2 := by
          have := Real.sin_le_one (2 * θ)
          linarith
        have hFw : ((1 + Real.sin (2 * θ)) * (z / (1 + z)))
            * (|(Work.Spaces.OpZ^[j - b]) Work.FM.Fstar z| * Work.Spaces.w z)
            ≤ 2 * Cr * row15aux.rlog z := by
          have h1 : |(Work.Spaces.OpZ^[j - b]) Work.FM.Fstar z| * Work.Spaces.w z ≤ Cr / z :=
            hradw (j - b) (by omega)
          have h2 : ((1 + Real.sin (2 * θ)) * (z / (1 + z))) * (Cr / z)
              ≤ 2 * Cr * row15aux.rlog z := by
            rw [show ((1 + Real.sin (2 * θ)) * (z / (1 + z))) * (Cr / z)
                = (1 + Real.sin (2 * θ)) * (Cr * (1 / (1 + z))) from by
              field_simp]
            have h3 : (1 + Real.sin (2 * θ)) * (Cr * (1 / (1 + z)))
                ≤ 2 * (Cr * (1 / (1 + z))) := by
              have hc : 0 ≤ Cr * (1 / (1 + z)) := by positivity
              nlinarith [h1s, hc]
            have h4 : 2 * (Cr * (1 / (1 + z))) ≤ 2 * Cr * row15aux.rlog z := by
              have h5 : 1 / (1 + z) ≤ row15aux.rlog z := hone_div
              nlinarith [h5, hCrn, hrlog]
            linarith
          exact le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
        calc |Work.Spaces.mixed b a
              (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
              * |Work.Spaces.mixed (j - b) (i - a)
                  (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
              * Work.Spaces.w z
            ≤ (Cu * (Cs + 1) * α * Real.sin (2 * θ) * (1 + Real.sin (2 * θ))
                * (z / (1 + z)))
              * |Work.Spaces.mixed (j - b) (i - a)
                  (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
              * Work.Spaces.w z :=
                mul_le_mul_of_nonneg_right (mul_le_mul hXb le_rfl (abs_nonneg _) hXb0) hwnn
          _ = Cu * (Cs + 1) * α * ((1 + Real.sin (2 * θ)) * (z / (1 + z)))
              * (Real.sin (2 * θ) * |Work.Spaces.mixed (j - b) (i - a)
                  (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|) * Work.Spaces.w z := by
                ring
          _ ≤ Cu * (Cs + 1) * α * ((1 + Real.sin (2 * θ)) * (z / (1 + z)))
              * (Cw * α ^ 2 * Work.Spaces.Gam α θ
                  * |(Work.Spaces.OpZ^[j - b]) Work.FM.Fstar z|) * Work.Spaces.w z :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYb (by positivity)) hwnn
          _ = Cu * Cw * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
              * (((1 + Real.sin (2 * θ)) * (z / (1 + z)))
                  * (|(Work.Spaces.OpZ^[j - b]) Work.FM.Fstar z| * Work.Spaces.w z)) := by ring
          _ ≤ Cu * Cw * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
              * (2 * Cr * row15aux.rlog z) := mul_le_mul_of_nonneg_left hFw hABs
          _ = 2 * Cu * Cw * Cr * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
              * row15aux.rlog z := by ring
  -- ## the summation
  have hmainUW : |Work.Spaces.mixed j i (fun z θ =>
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ) z θ| * Work.Spaces.w z
      ≤ 6400 * (2 * Cu * Cw * Cr * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
          * row15aux.rlog z) := by
    rw [hleib]
    have hsumabs : |∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a
                  (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
              * Work.Spaces.mixed (j - b) (i - a)
                  (Work.Spaces.pth (Work.Construction.Fstar α)) z θ)|
        ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (|Work.Spaces.mixed b a
                    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
                * |Work.Spaces.mixed (j - b) (i - a)
                    (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|) := by
      calc |∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              ((i.choose a : ℝ) * (j.choose b : ℝ))
                * (Work.Spaces.mixed b a
                      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
                  * Work.Spaces.mixed (j - b) (i - a)
                      (Work.Spaces.pth (Work.Construction.Fstar α)) z θ)|
          ≤ ∑ a ∈ Finset.range (i + 1),
              |∑ b ∈ Finset.range (j + 1),
                ((i.choose a : ℝ) * (j.choose b : ℝ))
                  * (Work.Spaces.mixed b a
                        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
                    * Work.Spaces.mixed (j - b) (i - a)
                        (Work.Spaces.pth (Work.Construction.Fstar α)) z θ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              |((i.choose a : ℝ) * (j.choose b : ℝ))
                * (Work.Spaces.mixed b a
                      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
                  * Work.Spaces.mixed (j - b) (i - a)
                      (Work.Spaces.pth (Work.Construction.Fstar α)) z θ)| :=
            Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
        _ = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              ((i.choose a : ℝ) * (j.choose b : ℝ))
                * (|Work.Spaces.mixed b a
                      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
                  * |Work.Spaces.mixed (j - b) (i - a)
                      (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|) := by
            refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
            have hc0 : (0 : ℝ) ≤ (i.choose a : ℝ) := Nat.cast_nonneg _
            have hc1 : (0 : ℝ) ≤ (j.choose b : ℝ) := Nat.cast_nonneg _
            simp only [abs_mul]
            rw [abs_of_nonneg hc0, abs_of_nonneg hc1]
    calc |∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a
                    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
                * Work.Spaces.mixed (j - b) (i - a)
                    (Work.Spaces.pth (Work.Construction.Fstar α)) z θ)| * Work.Spaces.w z
        ≤ (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (|Work.Spaces.mixed b a
                    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
                * |Work.Spaces.mixed (j - b) (i - a)
                    (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|)) * Work.Spaces.w z :=
          mul_le_mul_of_nonneg_right hsumabs hwnn
      _ = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (|Work.Spaces.mixed b a
                    (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
                * |Work.Spaces.mixed (j - b) (i - a)
                    (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|)
              * Work.Spaces.w z := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_mul]
      _ ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (2 * Cu * Cw * Cr * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
                  * row15aux.rlog z) := by
          refine Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => ?_))
          have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
          have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
          have hc : (0 : ℝ) ≤ (i.choose a : ℝ) * (j.choose b : ℝ) :=
            mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          have h := hpair a b hai hbj
          calc ((i.choose a : ℝ) * (j.choose b : ℝ))
                * (|Work.Spaces.mixed b a
                      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
                  * |Work.Spaces.mixed (j - b) (i - a)
                      (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|)
                * Work.Spaces.w z
              = ((i.choose a : ℝ) * (j.choose b : ℝ))
                * (|Work.Spaces.mixed b a
                      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
                  * |Work.Spaces.mixed (j - b) (i - a)
                      (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
                  * Work.Spaces.w z) := by ring
            _ ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
                * (2 * Cu * Cw * Cr * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
                    * row15aux.rlog z) := mul_le_mul_of_nonneg_left h hc
      _ = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ)))
          * (2 * Cu * Cw * Cr * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
              * row15aux.rlog z) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_mul]
      _ ≤ 6400 * (2 * Cu * Cw * Cr * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
              * row15aux.rlog z) := by
          refine mul_le_mul_of_nonneg_right (le_trans ?_ (le_refl 6400)) hMnn
          -- the binomial weight
          have hi4 : i ≤ 4 := by omega
          have hj4 : j ≤ 4 := by omega
          have h16 : ∀ (n a : ℕ), a ≤ n → n ≤ 4 → (n.choose a : ℝ) ≤ 16 := by
            intro n a han hn
            have h1 : n.choose a ≤ 2 ^ n := Nat.choose_le_two_pow n a
            have h2 : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn
            have h3 : ((2 : ℕ) ^ 4) = 16 := by norm_num
            exact_mod_cast le_trans h1 (le_trans h2 (le_of_eq h3))
          have hbnd : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
              ((i.choose a : ℝ) * (j.choose b : ℝ)) ≤ 256 := by
            intro a ha b hb'
            have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
            have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb')
            have h1 := h16 i a hai hi4
            have h2 := h16 j b hbj hj4
            have h3 : (0 : ℝ) ≤ (j.choose b : ℝ) := Nat.cast_nonneg _
            nlinarith
          calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                ((i.choose a : ℝ) * (j.choose b : ℝ)))
              ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (256 : ℝ) :=
                Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb' => hbnd a ha b hb'))
            _ = ((i : ℝ) + 1) * (((j : ℝ) + 1) * 256) := by
                simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
                  Nat.cast_one]
            _ ≤ 6400 := by
                have hi : (i : ℝ) ≤ 4 := by exact_mod_cast hi4
                have hj : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
                nlinarith
  -- ## conclusion
  have hY : 0 ≤ α ^ 3 * (Cs + 1) * Work.Spaces.Gam α θ * row15aux.rlog z :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hαn 3) (by linarith)) hΓnn) hrlog
  have hX : 0 ≤ Cu * Cw * Cr
      * (α ^ 3 * (Cs + 1) * Work.Spaces.Gam α θ * row15aux.rlog z) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCun hCwn) hCrn) hY
  rw [hN2eq]
  have hcmpt : ∀ z θ : ℝ, Work.Spaces.mixed j i (fun z θ =>
        -2 * ((Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ)) z θ
      = -2 * Work.Spaces.mixed j i (fun z θ =>
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
            * Work.Spaces.pth (Work.Construction.Fstar α) z θ) z θ :=
    fun z θ => congrFun (congrFun (mixed_cmul j i (-2) (fun z θ =>
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
        * Work.Spaces.pth (Work.Construction.Fstar α) z θ)) z) θ
  rw [hcmpt, hLHS]
  calc 2 * (|Work.Spaces.mixed j i (fun z θ =>
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ
            * Work.Spaces.pth (Work.Construction.Fstar α) z θ) z θ| * Work.Spaces.w z)
      ≤ 2 * (6400 * (2 * Cu * Cw * Cr * (Cs + 1) * α ^ 3 * Work.Spaces.Gam α θ
          * row15aux.rlog z)) := mul_le_mul_of_nonneg_left hmainUW (by norm_num)
    _ = 25600 * (Cu * Cw * Cr * (α ^ 3 * (Cs + 1) * Work.Spaces.Gam α θ
          * row15aux.rlog z)) := by ring
    _ ≤ 30000 * (Cu * Cw * Cr * (α ^ 3 * (Cs + 1) * Work.Spaces.Gam α θ
          * row15aux.rlog z)) + α ^ 3 * (Cs + 1) * Work.Spaces.Gam α θ
          * row15aux.rlog z := by linarith
    _ = (30000 * Cu * Cw * Cr + 1) * α ^ 3 * (Cs + 1) * Work.Spaces.Gam α θ
          * row15aux.rlog z := by ring

/-- **Row 15, pointwise form.**

`|D_z^j D_θ^i N₂^{ss}(z,θ)·w(z)| ≤ K·α³·(Cs+1)·Γ(θ)·rlog(z)` for `i+j ≤ 4`, on the slices
`z > 0` whose angular derivatives of `𝒰(Φ̃_*)` vanish at `θ = 0⁺`.  This is
`row15_slot_bound_aux` with its two `F_*`-side inputs supplied by the sibling modules. -/
theorem row15_slot_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {α Cs z : ℝ} {Φs : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.Nonlin.StarPkg α Cs Φs → 0 < z →
      (∀ θ ∈ Work.Spaces.Iθ,
        Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) 0 θ = 0) →
      (∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun θ => Work.Spaces.DzIter b
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ i j : ℕ, i + j ≤ 4 →
        |Work.Spaces.mixed j i (Work.FTS.Nonlin.N2ss α Φs) z θ * Work.Spaces.w z|
          ≤ K * α ^ 3 * (Cs + 1) * Work.Spaces.Gam α θ * row15aux.rlog z :=
  row15_slot_bound_aux row15aux.row15_SmoothQuadPthFstar row15aux.row15_PthFstarMixed

theorem row15 {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs)
        ≤ K * α ^ 2 := by
  obtain ⟨Ks, hKspos, hslot⟩ := row15_slot_bound
  refine ⟨10 ^ 6 * Ks * (|Cs| + 1) + 1, by positivity, ?_⟩
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
  have hCs : 0 ≤ Cs := row15aux.Cs_nonneg_of_starPkg hα hstar
  have hU0 : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) 0 θ = 0 :=
    row15aux.Uop_PhiTs_slice_zero hα hα1 hstar
  have hU : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun θ => Work.Spaces.DzIter b
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ i j : ℕ, i + j ≤ 4 →
        |Work.Spaces.mixed j i (Work.FTS.Nonlin.N2ss α Φs) z θ * Work.Spaces.w z|
          ≤ Ks * α ^ 3 * (Cs + 1) * Work.Spaces.Gam α θ * row15aux.rlog z := by
    intro z hz hgood θ hθ i j hij
    exact hslot hα hα1 hstar hz hU0 hgood θ hθ i j hij
  have hbad : ∀ z ∈ Set.Ioi (0 : ℝ),
      ¬(∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun θ => Work.Spaces.DzIter b
          (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
      ¬MeasureTheory.IntegrableOn
        (fun θ => Work.Spaces.HkIntegrand α 4 (Work.FTS.Nonlin.N2ss α Φs) z θ)
        Work.Spaces.Iθ := by
    intro z hz hnotgood hInt
    obtain ⟨k, hk4, hlow, δ, hδpos, hbig⟩ :=
      row15aux.row15_notGood hα hα1 hstar hz
        (fun k hk => row15aux.row15_pzIter_tendsto hα hα1 hstar hz k hk) hnotgood
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      exact row15aux.row15_bad hα hα1 hstar hz ⟨δ, hδpos, hbig⟩ hInt
    · exact row15aux.row15_bad_hi hα hα1 hstar hz k hkpos hk4 hlow
        ⟨δ, hδpos, hbig⟩ hInt
  have hbook := row15aux.row15_bookkeeping hα hα1 hKspos hCs hU hbad
  have hXn : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs)
      ≤ 10 ^ 6 * Ks * (|Cs| + 1) * α ^ 2 := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hbook) ?_
    have hsq : (1000000 * Ks * (Cs + 1)) ^ 2 * α ^ 4
        = (1000000 * Ks * (Cs + 1) * α ^ 2) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1000000),
      abs_of_nonneg (le_of_lt hKspos), abs_of_nonneg (sq_nonneg α)]
    have habs : |Cs + 1| ≤ |Cs| + 1 := by
      have h := abs_add_le Cs (1 : ℝ)
      simpa using h
    have h3 : 1000000 * Ks * |Cs + 1| ≤ 1000000 * Ks * (|Cs| + 1) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    calc 1000000 * Ks * |Cs + 1| * α ^ 2
        = (1000000 * Ks * |Cs + 1|) * α ^ 2 := by ring
      _ ≤ (1000000 * Ks * (|Cs| + 1)) * α ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (sq_nonneg α)
      _ = 1000000 * Ks * (|Cs| + 1) * α ^ 2 := by ring
      _ = 10 ^ 6 * Ks * (|Cs| + 1) * α ^ 2 := by norm_num
  have hfin : 10 ^ 6 * Ks * (|Cs| + 1) * α ^ 2
      ≤ (10 ^ 6 * Ks * (|Cs| + 1) + 1) * α ^ 2 := by
    have h1 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
    nlinarith [h1]
  exact le_trans hXn hfin

end

end Work.FTS.Nonlinear.Pieces.RNP
