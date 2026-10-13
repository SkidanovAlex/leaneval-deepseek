/-
# `H6Pair6Aux/RowMuAux/sg_open` — the three `sg`-rows in the open-quadrant class

`Work.FTS.NonlinRows.Rl1.sgBounds` proves the three `sg`-rows (`Rop·g`, `Uop·∂_θg`, `Vop·D_zg`)
of the `rl¹` block for a datum `g` in the **closed**-quadrant class `GalClass α g`
(`SmoothQuad g ∧ HkMem α 4 g`).  The level-six consumers of this route only ever have the
*honest* open-quadrant class

  `SmoothOpen f`  (`C^∞` on the open quadrant `(0,∞) × (0,π/2)`) `∧ HkMem α 4 f`,

which is exactly what `H6Adm α f` supplies.  This file re-proves the three rows in that class and
packages them in the `Fa`-envelope

  `K · (1 + max Cs 0) · α^{-2} · (1 + Xn α f)²`

consumed by the row bookkeeping of `H6Pair6Aux`.

The analytic content is identical to `sgBounds`: the coefficient bounds of `StarPkgo`
(`star_Rop_le`, `star_Vop_le`, `starUopBound`), the angular Cauchy–Schwarz engine
`PsgAux.rl1_slot_le`, and the slot comparisons `PsgAux.slot_g/slot_dth/slot_dz`.  The only
change is that the smoothness hypothesis is `SmoothOpen` (open quadrant) instead of `SmoothQuad`
(closed quadrant) — which is all the engine actually uses, since it only needs continuity of the
uncurried slot on `(0,∞) × (0,π/2)`.

Every declaration in this file is complete, with no gaps.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.SlotDataOpen
import Submission.Work.FTS.NonlinRows.Rl1.sgBounds
import Submission.Work.FTS.NonlinRows.Rl1.tools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)
open Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Row `N₁^{sg} = 2ℛ(Φ̃_*)·f` -/

theorem row1sg_open {α Cs : ℝ} {f Φs : Fn} (hα : 0 < α)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Fa (Work.FTS.Nonlin.N1sg α Φs f)
      ≤ ENNReal.ofReal (6 * max Cs 0 * α * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α f) := by
  have hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hso.continuousOn
  have hCs0 : 0 ≤ max Cs 0 := le_max_right _ _
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) r θ|
        ≤ 6 * max Cs 0 * α := by
    intro r hr
    refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hb1 := Work.FTS.Nonlinear.Pieces.rl1Pieces.abs_K_le_three θ
    have hb2 := Work.FTS.NonlinRows.Rl1.star_Rop_le hα hs r hr θ hθ
    calc |Work.Spaces.K θ
          * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ)|
        = 2 * |Work.Spaces.K θ|
            * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          ring
      _ ≤ 2 * 3 * (max Cs 0 * α) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hb1 (by norm_num)) hb2
            (abs_nonneg _) (by positivity)
      _ = 6 * max Cs 0 * α := by ring
  have hBmeas : ∀ r, 0 < r → AEMeasurable (fun θ => ENNReal.ofReal ((f r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => slice_sq_aemeasurable hcont hr
  have hΦmeas := slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (f r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ :=
    fun r hr => ae_Iθ_of_forall_Ioo (fun θ hθ => slot_g hα hr hθ f)
  have hE := rl1_slot_le (α := α) (C := 6 * max Cs 0 * α)
    (A := fun z θ => 2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    (B := f) (g := f) (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le)
    hmem hA hBmeas hΦmeas hBw
  rw [Fa]
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs f r θ|
      = |Work.Spaces.K θ
          * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ) * f r θ| := by
    intro r θ
    rw [Work.FTS.Nonlin.N1sg]
    congr 1
    ring
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  exact MeasureTheory.lintegral_congr fun θ => by rw [hid r θ]

/-! ## Row `N₂^{sg} = -2𝒰(Φ̃_*)·∂_θf` -/

/-- Row 2 with the pointwise bound on `𝒰(Φ̃_*)` exposed. -/
theorem row2sg_open {α MU : ℝ} {f Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hMU : 0 ≤ MU)
    (hU : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ MU)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    Fa (Work.FTS.Nonlin.N2sg α Φs f)
      ≤ ENNReal.ofReal (3 * MU * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f) := by
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.Dth f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hso.Dth.continuousOn
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
            / Real.sin (2 * θ)) r θ| ≤ 3 * MU := by
    intro r hr
    refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hs2 : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sin_two_pos hθ)
    have hU0 := hU r θ hr hθI
    have hK : Work.Spaces.K θ = (3 / 2) * Real.cos θ * Real.sin (2 * θ) := by
      rw [Work.Spaces.K, Real.sin_two_mul]
      ring
    have hratio : Work.Spaces.K θ / Real.sin (2 * θ) = (3 / 2) * Real.cos θ := by
      rw [hK]
      field_simp
    have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have habs : |Work.Spaces.K θ
          * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
              / Real.sin (2 * θ))|
        = 2 * ((3 / 2) * |Real.cos θ|)
          * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
      have hsplit : Work.Spaces.K θ
            * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
                / Real.sin (2 * θ))
          = (Work.Spaces.K θ / Real.sin (2 * θ))
            * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ) := by ring
      rw [hsplit, hratio]
      rw [show (3 / 2 : ℝ) * Real.cos θ
            * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ)
          = (-3) * (Real.cos θ
            * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ) from by ring,
        abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_mul]
      ring
    rw [habs]
    have h1 : (3 / 2) * |Real.cos θ| ≤ (3 / 2) * 1 :=
      mul_le_mul_of_nonneg_left hcos (by norm_num)
    calc 2 * ((3 / 2) * |Real.cos θ|)
          * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
        ≤ 2 * ((3 / 2) * 1) * MU := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hU0
            (abs_nonneg _) ?_
          positivity
      _ = 3 * MU := by ring
  have hBmeas : ∀ r, 0 < r → AEMeasurable
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dth f r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => slice_sq_aemeasurable hcont hr
  have hΦmeas := slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (Work.Spaces.Dth f r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ :=
    fun r hr => ae_Iθ_of_forall_Ioo (fun θ hθ => slot_dth hα hr hθ f)
  have hE := rl1_slot_le (α := α) (C := 3 * MU)
    (A := fun z θ => -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      / Real.sin (2 * θ))
    (B := Work.Spaces.Dth f) (g := f) (mul_nonneg (by norm_num) hMU)
    hmem hA hBmeas hΦmeas hBw
  rw [Fa]
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs f r θ|
        = |Work.Spaces.K θ * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
              / Real.sin (2 * θ)) * Work.Spaces.Dth f r θ| := by
    intro r θ hθ
    have hs2 : Real.sin (2 * θ) ≠ 0 := ne_of_gt (sin_two_pos hθ)
    rw [Work.FTS.Nonlin.N2sg]
    congr 1
    simp only [Work.Spaces.Dth]
    field_simp
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  refine MeasureTheory.lintegral_congr_ae ?_
  filter_upwards [ae_Iθ_of_forall_Ioo
    (p := fun θ => θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (fun θ hθ => hθ)] with θ hθ
  rw [hid r θ hθ]

/-! ## Row `N₃^{sg} = -2α𝒱(Φ̃_*)·D_zf` -/

theorem row3sg_open {α Cs : ℝ} {f Φs : Fn} (hα : 0 < α)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Fa (Work.FTS.Nonlin.N3sg α Φs f)
      ≤ ENNReal.ofReal (6 * max Cs 0 * α ^ 2 * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α f) := by
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.Dz f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hso.Dz.continuousOn
  have hCs0 : 0 ≤ max Cs 0 := le_max_right _ _
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) r θ|
        ≤ 6 * max Cs 0 * α ^ 2 := by
    intro r hr
    refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hb1 := Work.FTS.Nonlinear.Pieces.rl1Pieces.abs_K_le_three θ
    have hb2 := Work.FTS.NonlinRows.Rl1.star_Vop_le hα hs r hr θ hθ
    calc |Work.Spaces.K θ
          * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)|
        = 2 * α * |Work.Spaces.K θ|
            * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
          rw [show Work.Spaces.K θ
                * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)
              = (-(2 * α)) * (Work.Spaces.K θ
                * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ) from by ring,
            abs_mul, abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) hα.le), abs_mul]
          ring
      _ ≤ 2 * α * 3 * (max Cs 0 * α) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hb1
            (mul_nonneg (by norm_num) hα.le)) hb2 (abs_nonneg _) (by positivity)
      _ = 6 * max Cs 0 * α ^ 2 := by ring
  have hBmeas : ∀ r, 0 < r → AEMeasurable
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dz f r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => slice_sq_aemeasurable hcont hr
  have hΦmeas := slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (Work.Spaces.Dz f r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f r θ :=
    fun r hr => ae_Iθ_of_forall_Ioo (fun θ hθ => slot_dz hα hr hθ f)
  have hE := rl1_slot_le (α := α) (C := 6 * max Cs 0 * α ^ 2)
    (A := fun z θ => -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    (B := Work.Spaces.Dz f) (g := f)
    (mul_nonneg (mul_nonneg (by norm_num) hCs0) (sq_nonneg α))
    hmem hA hBmeas hΦmeas hBw
  rw [Fa]
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs f r θ|
      = |Work.Spaces.K θ
          * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)
          * Work.Spaces.Dz f r θ| := by
    intro r θ
    rw [Work.FTS.Nonlin.N3sg]
    congr 1
    ring
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  exact MeasureTheory.lintegral_congr fun θ => by rw [hid r θ]

/-! ## Elementary arithmetic -/

/-- `√(π/2) ≤ 2`. -/
theorem sqrt_pi_div_two_le_two : Real.sqrt (Real.pi / 2) ≤ 2 := by
  have h : Real.sqrt (Real.pi / 2) ≤ Real.sqrt 4 :=
    Real.sqrt_le_sqrt (by linarith [Real.pi_le_four])
  rwa [show Real.sqrt (4 : ℝ) = 2 from by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h

/-- `1 ≤ α^{-2}` for `0 < α ≤ 1`. -/
theorem one_le_rpow_neg_two {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) ≤ α ^ (-(2 : ℝ)) := by
  rw [Real.rpow_neg hα.le]
  rw [one_le_inv₀ (Real.rpow_pos_of_pos hα 2)]
  exact Real.rpow_le_one hα.le hα1 (by norm_num)

/-- The arithmetic core of the three row estimates: an `α`-linear constant `c` bounded by
`12·A` gives a bound by the envelope `K·M·α^{-2}·(1+X)²`. -/
theorem row_le_envelope {c A α s X K M : ℝ} (hcle : c ≤ 12 * A) (hA0 : 0 ≤ A) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hs : s ≤ 2) (hs0 : 0 ≤ s) (hX0 : 0 ≤ X)
    (hrpow : (1 : ℝ) ≤ α ^ (-(2 : ℝ))) (hKM : 24 * A ≤ K * M) :
    c * α * s * X ≤ K * M * α ^ (-(2 : ℝ)) * (1 + X) ^ 2 := by
  have h12A : (0 : ℝ) ≤ 12 * A := by linarith
  have h24A : (0 : ℝ) ≤ 24 * A := by linarith
  have h1 : c * α * s * X ≤ (12 * A) * α * s * X := by
    have h : c * α ≤ 12 * A * α := mul_le_mul_of_nonneg_right hcle hα0.le
    have h2 : c * α * s ≤ 12 * A * α * s := mul_le_mul_of_nonneg_right h hs0
    exact mul_le_mul_of_nonneg_right h2 hX0
  have h2 : (12 * A) * α * s * X ≤ (12 * A) * s * X := by
    have hb : (12 * A) * α * s ≤ ((12 * A) * 1) * s :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα1 h12A) hs0
    have hc : (12 * A) * α * s * X ≤ ((12 * A) * 1) * s * X :=
      mul_le_mul_of_nonneg_right hb hX0
    simpa only [mul_one] using hc
  have h3 : (12 * A) * s * X ≤ (24 * A) * X := by
    have hb : (12 * A) * s ≤ 24 * A := by
      have := mul_le_mul_of_nonneg_left hs h12A
      linarith
    simpa using mul_le_mul_of_nonneg_right hb hX0
  have h4 : (24 * A) * X ≤ (24 * A) * (1 + X) ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ h24A
    nlinarith [hX0]
  have h5 : (24 * A) * (1 + X) ^ 2 ≤ (24 * A) * (α ^ (-(2 : ℝ)) * (1 + X) ^ 2) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (sq_nonneg _) hrpow) h24A
  have h6 : (24 * A) * (α ^ (-(2 : ℝ)) * (1 + X) ^ 2)
      ≤ K * M * (α ^ (-(2 : ℝ)) * (1 + X) ^ 2) :=
    mul_le_mul_of_nonneg_right hKM (by positivity)
  have h7 : K * M * (α ^ (-(2 : ℝ)) * (1 + X) ^ 2)
      = K * M * α ^ (-(2 : ℝ)) * (1 + X) ^ 2 := by ring
  calc c * α * s * X ≤ (12 * A) * α * s * X := h1
    _ ≤ (12 * A) * s * X := h2
    _ ≤ (24 * A) * X := h3
    _ ≤ (24 * A) * (1 + X) ^ 2 := h4
    _ ≤ (24 * A) * (α ^ (-(2 : ℝ)) * (1 + X) ^ 2) := h5
    _ ≤ K * M * (α ^ (-(2 : ℝ)) * (1 + X) ^ 2) := h6
    _ = K * M * α ^ (-(2 : ℝ)) * (1 + X) ^ 2 := h7

/-! ## Assembly -/

theorem sg_open (Cs : ℝ) : ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f Φs : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.VocabO.StarPkgo α Cs Φs →
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1sg α Φs f)
        ≤ ENNReal.ofReal (K * (1 + max Cs 0) * α ^ (-(2 : ℝ))
            * (1 + Work.FTS.Nonlin.Xn α f) ^ 2) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2sg α Φs f)
        ≤ ENNReal.ofReal (K * (1 + max Cs 0) * α ^ (-(2 : ℝ))
            * (1 + Work.FTS.Nonlin.Xn α f) ^ 2) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3sg α Φs f)
        ≤ ENNReal.ofReal (K * (1 + max Cs 0) * α ^ (-(2 : ℝ))
            * (1 + Work.FTS.Nonlin.Xn α f) ^ 2) := by
  obtain ⟨CU, hCUpos, hCUb⟩ := Work.FTS.NonlinRows.Rl1.starUopBound
  have hCU0 : 0 ≤ CU := hCUpos.le
  have hM0 : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hA0 : 0 ≤ 1 + max Cs 0 + max Cs 0 * CU := by
    have := mul_nonneg hM0 hCU0
    linarith
  have hM1 : (1 : ℝ) ≤ 1 + max Cs 0 := by linarith
  refine ⟨1 + 24 * (1 + max Cs 0 + max Cs 0 * CU), by linarith, ?_⟩
  intro α f Φs hα hα1 hso hmem hs
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hrpow : (1 : ℝ) ≤ α ^ (-(2 : ℝ)) := one_le_rpow_neg_two hα hα1
  have hsv : Real.sqrt (Real.pi / 2) ≤ 2 := sqrt_pi_div_two_le_two
  have hsv0 : (0 : ℝ) ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  have hKM : 24 * (1 + max Cs 0 + max Cs 0 * CU)
      ≤ (1 + 24 * (1 + max Cs 0 + max Cs 0 * CU)) * (1 + max Cs 0) := by
    nlinarith [hA0, hM1]
  have key : ∀ c : ℝ, 0 ≤ c → c ≤ 12 * (1 + max Cs 0 + max Cs 0 * CU) →
      c * α * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f
        ≤ (1 + 24 * (1 + max Cs 0 + max Cs 0 * CU)) * (1 + max Cs 0)
            * α ^ (-(2 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 2 :=
    fun c _ hc => row_le_envelope hc hA0 hα hα1 hsv hsv0 hXn0 hrpow hKM
  have hc1 : 6 * max Cs 0 ≤ 12 * (1 + max Cs 0 + max Cs 0 * CU) := by
    nlinarith [hM0, hA0]
  have hc2 : 3 * CU * max Cs 0 ≤ 12 * (1 + max Cs 0 + max Cs 0 * CU) := by
    nlinarith [hM0, hCU0, mul_nonneg hM0 hCU0]
  have hc3 : 6 * max Cs 0 * α ≤ 12 * (1 + max Cs 0 + max Cs 0 * CU) := by
    nlinarith [hM0, hA0, hα.le, hα1]
  have hrow3 : (6 * max Cs 0) * α ^ 2 * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f
      = ((6 * max Cs 0 * α) * α) * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f := by
    ring
  refine ⟨(row1sg_open hα hso hmem hs).trans
      (ENNReal.ofReal_le_ofReal (key (6 * max Cs 0) (by positivity) hc1)), ?_, ?_⟩
  · refine (row2sg_open (α := α) (MU := CU * max Cs 0 * α) hα hα1
        (mul_nonneg (mul_nonneg hCU0 hM0) hα.le)
        (fun z θ hz hθ => hCUb hα hα1 hs z hz θ hθ) hso hmem).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have h2rew : 3 * (CU * max Cs 0 * α) * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f
        = (3 * CU * max Cs 0) * α * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α f := by
      ring
    rw [h2rew]
    exact key (3 * CU * max Cs 0)
      (mul_nonneg (mul_nonneg (by norm_num) hCU0) hM0) hc2
  · refine (row3sg_open hα hso hmem hs).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hrow3]
    exact key (6 * max Cs 0 * α)
      (mul_nonneg (mul_nonneg (by norm_num) hM0) hα.le) hc3

end

end Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux
