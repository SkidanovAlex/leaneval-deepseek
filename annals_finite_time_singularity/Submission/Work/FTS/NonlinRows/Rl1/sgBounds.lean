import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.starUopBound
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Psg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.Rl1

/-
The three `sg`-rows (coefficient a star coefficient, slot the datum's `g`, `∂_θg`, `D_zg`).
All coefficient bounds needed are *pointwise* and already in `Rl1/tools.lean`:
`star_Rop_le : |Rop(Φ̃_*)| ≤ max Cs 0·α`, `star_Vop_le : |Vop(Φ̃_*)| ≤ max Cs 0·α`,
`star_KUop_le : |K θ·Uop(Φ̃_*)| ≤ 6 max Cs 0·α` (via `K_mul_Uop`), and
`Work.FTS.NonlinRows.Rl1.starUopBound : |Uop(Φ̃_*)| ≤ C·max Cs 0·α`.

Route: pull the constant out of the `∫⁻_θ` (`lintegral_const_mul'`) after the pointwise bound
`|K θ·N| ≤ (const)·K θ·|slot|` and estimate the slot against its energy `Phi0 g`/`Phi1 g`/`Phi2 g`
with `Work.FTS.NonlinRows.Rl1.lintegral_abs_le_sqrt` (for the `D_θg`-slot of `N2sg`, where the
`K`-weight cannot be kept) together with `inner_lintegral_le`, then the `r`-step
`Work.FTS.Nonlinear.Pieces.outer_of_inner` with `∫ w·Phi_j ≤ HkSq α 4 g` (from
`Work.FTS.NonlinRows.Rl1.slot0/1/2`).  For `N2sg` one may also use `starUopBound` and
`|K θ·∂_θg| = 3cos²θ·|D_θg| ≤ 3|D_θg|`.
Rates: `C·max Cs 0·α·Xn α g` for rows 1,2 and `C·max Cs 0·α²·Xn α g` for row 3; both fit
`K·Env α g` since `α ≤ √α`.
CAUTION: do NOT try to prove an `Xn`-level bound (`HkMem α 4 (N1sg) ∧ Xn α (N1sg) ≤ …`);
`NonlinRows/NRow10.lean` documents that this is impossible from `StarPkgo`.  The `Fa`-level
statement above is the correct, provable one (the coefficient estimate is pointwise).

## The route implemented here

`Fa` *is* the `rl¹`-density `∫⁻_r r⁻¹ (∫⁻_θ |K θ·N r θ|)`, and for a pointwise *factorisation*
`K θ·N = (K θ·A)·B` with `|K θ·A| ≤ C` the whole estimate is already available as the generic
engine `Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.rl1_slot_le` (proved, sorry-free):

  `∫⁻_r r⁻¹ (∫⁻_θ |K θ·A·B|) ≤ ofReal (C·√(π/2)·Xn α g)`,

which performs the angular Cauchy–Schwarz against `(∫⁻_θ B²)^{1/2}` and the radial one against
the weighted energy `∫_r w(r)·∫⁻_θ HkIntegrand α 4 g`.  The three slots `B = g, D_θg, D_zg` are
compared with the `ℋ⁴`-integrand by `PsgAux.slot_g/slot_dth/slot_dz`, and `|K θ·A| ≤ C` comes
from `star_Rop_le`, `starUopBound` and `star_Vop_le` together with `|K θ| ≤ 3` and the exact
identities `K θ / sin 2θ = (3/2)cos θ`, `pth g = D_θg / sin 2θ`.

The only primed ingredient beyond that engine is the pointwise bound on `𝒰(Φ̃_*)`
(`Work.FTS.NonlinRows.Rl1.starUopBound`).
-/
noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)
open Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Row `N₁^{sg} = 2ℛ(Φ̃_*)·g` -/

theorem row1sg_primed {α Cs : ℝ} {g Φs : Fn} (hα : 0 < α)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) (hgal : Work.FTS.Nonlin.GalClass α g) :
    Fa (Work.FTS.Nonlin.N1sg α Φs g)
      ≤ ENNReal.ofReal (6 * max Cs 0 * α * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α g) := by
  have hreg := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hcont : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    contOn_of_smoothQuad hreg.1
  have hCs0 : 0 ≤ max Cs 0 := le_max_right _ _
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) r θ|
        ≤ 6 * max Cs 0 * α := by
    intro r hr
    refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hb1 := Work.FTS.Nonlinear.Pieces.rl1Pieces.abs_K_le_three θ
    have hb2 := star_Rop_le hα hs r hr θ hθ
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
  have hBmeas : ∀ r, 0 < r → AEMeasurable (fun θ => ENNReal.ofReal ((g r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => slice_sq_aemeasurable hcont hr
  have hΦmeas := slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
    fun r hr => ae_Iθ_of_forall_Ioo (fun θ hθ => slot_g hα hr hθ g)
  have hE := rl1_slot_le (α := α) (C := 6 * max Cs 0 * α)
    (A := fun z θ => 2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    (B := g) (g := g) (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le)
    hmem hA hBmeas hΦmeas hBw
  rw [Fa]
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ|
      = |Work.Spaces.K θ
          * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ) * g r θ| := by
    intro r θ
    rw [Work.FTS.Nonlin.N1sg]
    congr 1
    ring
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  exact MeasureTheory.lintegral_congr fun θ => by rw [hid r θ]

/-! ## Row `N₂^{sg} = -2𝒰(Φ̃_*)·∂_θg` -/

/-- Row 2 with the pointwise bound on `𝒰(Φ̃_*)` exposed. -/
theorem row2sg_primed {α MU : ℝ} {g Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hMU : 0 ≤ MU)
    (hU : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ MU)
    (hgal : Work.FTS.Nonlin.GalClass α g) :
    Fa (Work.FTS.Nonlin.N2sg α Φs g)
      ≤ ENNReal.ofReal (3 * MU * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g) := by
  have hreg := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.Dth g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    contOn_of_smoothQuad
      (show Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth g) from
        Work.FTS.LocData.SmoothQuad.DthIter hreg.1 1)
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
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dth g r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => slice_sq_aemeasurable hcont hr
  have hΦmeas := slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (Work.Spaces.Dth g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
    fun r hr => ae_Iθ_of_forall_Ioo (fun θ hθ => slot_dth hα hr hθ g)
  have hE := rl1_slot_le (α := α) (C := 3 * MU)
    (A := fun z θ => -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      / Real.sin (2 * θ))
    (B := Work.Spaces.Dth g) (g := g) (mul_nonneg (by norm_num) hMU)
    hmem hA hBmeas hΦmeas hBw
  rw [Fa]
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ|
        = |Work.Spaces.K θ * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
              / Real.sin (2 * θ)) * Work.Spaces.Dth g r θ| := by
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

/-! ## Row `N₃^{sg} = -2α𝒱(Φ̃_*)·D_zg` -/

theorem row3sg_primed {α Cs : ℝ} {g Φs : Fn} (hα : 0 < α)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) (hgal : Work.FTS.Nonlin.GalClass α g) :
    Fa (Work.FTS.Nonlin.N3sg α Φs g)
      ≤ ENNReal.ofReal (6 * max Cs 0 * α ^ 2 * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α g) := by
  have hreg := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.Dz g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    contOn_of_smoothQuad
      (show Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz g) from
        Work.FTS.LocData.SmoothQuad.DzIter hreg.1 1)
  have hCs0 : 0 ≤ max Cs 0 := le_max_right _ _
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) r θ|
        ≤ 6 * max Cs 0 * α ^ 2 := by
    intro r hr
    refine ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hb1 := Work.FTS.Nonlinear.Pieces.rl1Pieces.abs_K_le_three θ
    have hb2 := star_Vop_le hα hs r hr θ hθ
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
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dz g r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => slice_sq_aemeasurable hcont hr
  have hΦmeas := slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (Work.Spaces.Dz g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
    fun r hr => ae_Iθ_of_forall_Ioo (fun θ hθ => slot_dz hα hr hθ g)
  have hE := rl1_slot_le (α := α) (C := 6 * max Cs 0 * α ^ 2)
    (A := fun z θ => -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    (B := Work.Spaces.Dz g) (g := g)
    (mul_nonneg (mul_nonneg (by norm_num) hCs0) (sq_nonneg α))
    hmem hA hBmeas hΦmeas hBw
  rw [Fa]
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ|
      = |Work.Spaces.K θ
          * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)
          * Work.Spaces.Dz g r θ| := by
    intro r θ
    rw [Work.FTS.Nonlin.N3sg]
    congr 1
    ring
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  exact MeasureTheory.lintegral_congr fun θ => by rw [hid r θ]

/-! ## Assembly -/

/-- `α ≤ √α` for `0 < α ≤ 1`. -/
theorem alpha_le_sqrt_primed {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ≤ Real.sqrt α := by
  have h : α ^ 2 ≤ α := by nlinarith
  calc α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα.le).symm
    _ ≤ Real.sqrt α := Real.sqrt_le_sqrt h

theorem sgBounds {Cs : ℝ} : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g → Work.FTS.VocabO.StarPkgo α Cs Φs →
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1sg α Φs g)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2sg α Φs g)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3sg α Φs g)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) := by
  obtain ⟨CU, hCUpos, hCUb⟩ := starUopBound
  have hCU0 : 0 ≤ CU := hCUpos.le
  have hP0 : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  have hM0 : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hMC0 : 0 ≤ max Cs 0 + max Cs 0 * CU := by
    have := mul_nonneg hM0 hCU0
    linarith
  set Kc : ℝ := 1 + 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU) with hKcdef
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    nlinarith [hP0, hMC0]
  have hKc0 : 0 ≤ Kc := hKcpos.le
  have hbig : 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU) ≤ Kc := by
    rw [hKcdef]; linarith
  have hcoef : ∀ c : ℝ, 0 ≤ c → c ≤ 12 * (max Cs 0 + max Cs 0 * CU) →
      c * Real.sqrt (Real.pi / 2) ≤ 12 * Real.sqrt (Real.pi / 2)
        * (max Cs 0 + max Cs 0 * CU) := by
    intro c _hc0 hcle
    calc c * Real.sqrt (Real.pi / 2)
        ≤ 12 * (max Cs 0 + max Cs 0 * CU) * Real.sqrt (Real.pi / 2) :=
          mul_le_mul_of_nonneg_right hcle hP0
      _ = 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU) := by ring
  have h6 : (6 : ℝ) * max Cs 0 ≤ 12 * (max Cs 0 + max Cs 0 * CU) := by
    nlinarith [hM0, hCU0, mul_nonneg hM0 hCU0]
  have h3 : 3 * CU * max Cs 0 ≤ 12 * (max Cs 0 + max Cs 0 * CU) := by
    nlinarith [hM0, hCU0, mul_nonneg hM0 hCU0]
  refine ⟨Kc, hKcpos, ?_⟩
  intro α g Φs hα hα1 hGal hStar
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hEnv0 : 0 ≤ Env α g := Env_nonneg g hα.le
  have hαX : α * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
    have h1 : α * Work.FTS.Nonlin.Xn α g ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_le_mul_of_nonneg_right (alpha_le_sqrt_primed hα hα1) hX0
    have h2 : Real.sqrt α * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
      rw [Env]
      have h3 : 0 ≤ α ^ 2 := sq_nonneg α
      have h4 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
      linarith
    exact h1.trans h2
  have hα2X : α ^ 2 * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
    have h1 : α ^ 2 * Work.FTS.Nonlin.Xn α g ≤ α * Work.FTS.Nonlin.Xn α g := by
      refine mul_le_mul_of_nonneg_right ?_ hX0
      nlinarith [hα.le, hα1]
    exact h1.trans hαX
  have keyA : ∀ c : ℝ, 0 ≤ c → c ≤ 12 * (max Cs 0 + max Cs 0 * CU) →
      c * α * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g ≤ Kc * Env α g := by
    intro c hc0 hcle
    have h1 := hcoef c hc0 hcle
    calc c * α * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g
        = (c * Real.sqrt (Real.pi / 2)) * (α * Work.FTS.Nonlin.Xn α g) := by ring
      _ ≤ (12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU))
            * (α * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul h1 le_rfl (mul_nonneg hα.le hX0) (by positivity)
      _ ≤ Kc * Env α g := mul_le_mul hbig hαX (mul_nonneg hα.le hX0) hKc0
  have keyB : ∀ c : ℝ, 0 ≤ c → c ≤ 12 * (max Cs 0 + max Cs 0 * CU) →
      c * α ^ 2 * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g ≤ Kc * Env α g := by
    intro c hc0 hcle
    have h1 := hcoef c hc0 hcle
    calc c * α ^ 2 * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g
        = (c * Real.sqrt (Real.pi / 2)) * (α ^ 2 * Work.FTS.Nonlin.Xn α g) := by ring
      _ ≤ (12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + max Cs 0 * CU))
            * (α ^ 2 * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul h1 le_rfl (mul_nonneg (sq_nonneg α) hX0) (by positivity)
      _ ≤ Kc * Env α g := mul_le_mul hbig hα2X (mul_nonneg (sq_nonneg α) hX0) hKc0
  refine ⟨?_, ?_, ?_⟩
  · have h1 := row1sg_primed hα hStar hGal
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    exact keyA (6 * max Cs 0) (mul_nonneg (by norm_num) hM0) h6
  · have hMU : 0 ≤ CU * max Cs 0 * α := mul_nonneg (mul_nonneg hCU0 hM0) hα.le
    have hU : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
        |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
          ≤ CU * max Cs 0 * α :=
      fun z θ hz hθ => hCUb hα hα1 hStar z hz θ hθ
    have h1 := row2sg_primed hα hα1 hMU hU hGal
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [show 3 * (CU * max Cs 0 * α) * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g
        = (3 * CU * max Cs 0) * α * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α g from by ring]
    exact keyA (3 * CU * max Cs 0) (mul_nonneg (mul_nonneg (by norm_num) hCU0) hM0) h3
  · have h1 := row3sg_primed hα hStar hGal
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    exact keyB (6 * max Cs 0) (mul_nonneg (by norm_num) hM0) h6

end

end Work.FTS.NonlinRows.Rl1
