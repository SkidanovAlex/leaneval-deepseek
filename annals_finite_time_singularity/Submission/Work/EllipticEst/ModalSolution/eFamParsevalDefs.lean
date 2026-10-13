/-
# `ModalSolution/eFamParsevalDefs`: the modal Hilbert space `L²(Iθ, cos θ dθ)` for `eFam`

This module sets up the `L²`-picture in which Parseval's identity for the Gegenbauer
(angular) modes `eFam m` of `Lzero` is proved:

* `Work.FTS.EllipticEst.LevelOneAsm.angMeasure = (volume.restrict Iθ).withDensity (ofReal ∘ cos)` and the Hilbert space
  `Lp ℝ 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure` come from
  `Submission/Work/FTS/EllipticEst/LevelOneAsm/EigParsevalDefs.lean`, where they were built
  for the sibling angular eigenbasis `eigFun`;
* `eM m := Gegenbauer.eFam m` (a reducible alias), `eFamD m = ∫ θ in Iθ, eM m θ ^ 2 * cos θ`
  is the squared norm of the `m`-th mode — computed exactly by `eFam_norm_fts` as
  `((2m+2)(2m+3))/(4m+5)`, hence positive (`eFamD_eq`, `eFamD_pos`);
* `eFam_memLp m : MemLp (eM m) 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure` (the modes are bounded on `Iθ`);
* `eFamLp m` is the class of `eM m` and `eFamE m = (√(eFamD m))⁻¹ • eFamLp m` is the
  normalised class, together with the inner-product computations
  `inner_toLp_eFamE`, `inner_eFamE_toLp`, `inner_eFamLp_any`.

The two structural facts about the family `eFamE` — it is orthonormal, and its span has trivial
orthogonal complement (completeness of the modes, from
`FTS/PhiStar/Gegenbauer/eFam_complete`) — are proved in the sibling modules
`ModalSolution/eFamE_orthonormal` and `ModalSolution/eFamE_span_orthogonal_eq_bot`; the Parseval
identity `Work.EllipticEst.ModalSolution.eFam_parseval` is assembled from them in
`ModalSolution/eFam_parseval`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.LevelOneAsm.EigParsevalDefs
import Submission.Work.EllipticEst.ModalSolution.eFamBasisFts_FALSE

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

local notation "Iθ" => Work.Spaces.Iθ

/-- The `m`-th Gegenbauer mode of `Lzero`, as a (reducible) alias for
`Work.FTS.PhiStar.Gegenbauer.eFam m`. -/
abbrev eM (m : ℕ) : ℝ → ℝ := Work.FTS.PhiStar.Gegenbauer.eFam m

/-- The squared `L²(Iθ, cos θ dθ)`-norm of the `m`-th mode. -/
def eFamD (m : ℕ) : ℝ := ∫ θ in Iθ, eM m θ ^ 2 * Real.cos θ

/-- `eFam_norm_fts`, restated for `eFamD`. -/
theorem eFamD_eq (m : ℕ) :
    eFamD m = ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) :=
  Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m

theorem eFamD_pos (m : ℕ) : 0 < eFamD m := by
  rw [eFamD_eq]
  positivity

/-- The modes are bounded on `Iθ` (they are `cos θ` times a polynomial in `sin θ`, and
`sin θ` stays in `[-1,1]`). -/
theorem eFam_abs_le (m : ℕ) : ∃ C : ℝ, ∀ θ ∈ Iθ, ‖eM m θ‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.continuousOn)
  refine ⟨C, fun θ hθ => ?_⟩
  have hsin : Real.sin θ ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [Real.neg_one_le_sin θ], Real.sin_le_one θ⟩
  have h2 := hC (Real.sin θ) hsin
  have h1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
  calc ‖eM m θ‖
      = |Real.cos θ| * |Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)| := by
        rw [Real.norm_eq_abs, eM, Work.FTS.PhiStar.Gegenbauer.eFam, abs_mul]
    _ ≤ 1 * C := by
        refine mul_le_mul h1 ?_ (abs_nonneg _) zero_le_one
        rwa [Real.norm_eq_abs] at h2
    _ = C := one_mul C

theorem eFam_memLp (m : ℕ) : MemLp (eM m) 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure := by
  obtain ⟨C, hC⟩ := eFam_abs_le m
  refine MemLp.of_bound ?_ C ?_
  · exact ((Real.continuous_cos.mul
      (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
        Real.continuous_sin))).aestronglyMeasurable
  · filter_upwards [Work.FTS.EllipticEst.LevelOneAsm.ae_mem_Iθ_angMeasure] with θ hθ
    exact hC θ hθ

/-- The class of the `m`-th mode in `L²(Iθ, cos θ dθ)`. -/
def eFamLp (m : ℕ) : Lp ℝ 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure := MemLp.toLp (eM m) (eFam_memLp m)

theorem eFamLp_coe (m : ℕ) : (eFamLp m : ℝ → ℝ) =ᵐ[Work.FTS.EllipticEst.LevelOneAsm.angMeasure] eM m :=
  MemLp.coeFn_toLp (eFam_memLp m)

/-- The normalised modes `eFamE m = (√(eFamD m))⁻¹ • eFamLp m`. -/
def eFamE (m : ℕ) : Lp ℝ 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure := (Real.sqrt (eFamD m))⁻¹ • eFamLp m

theorem eFamE_coe (m : ℕ) :
    (eFamE m : ℝ → ℝ) =ᵐ[Work.FTS.EllipticEst.LevelOneAsm.angMeasure]
      fun θ => (Real.sqrt (eFamD m))⁻¹ * eM m θ := by
  simp only [eFamE]
  filter_upwards [Lp.coeFn_smul (c := (Real.sqrt (eFamD m))⁻¹) (eFamLp m),
    eFamLp_coe m] with θ h1 h2
  rw [h1]
  simp only [Pi.smul_apply, smul_eq_mul, h2]

/-- The inner product of an `L²`-class with the `m`-th mode class is the weighted integral on
`Iθ`. -/
theorem inner_toLp_eFamLp {f : ℝ → ℝ} (hf : MemLp f 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure) (m : ℕ) :
    inner ℝ (MemLp.toLp f hf) (eFamLp m) = ∫ θ in Iθ, f θ * eM m θ * Real.cos θ :=
  Work.FTS.EllipticEst.LevelOneAsm.inner_toLp_toLp hf (eFam_memLp m)

theorem inner_toLp_eFamE {f : ℝ → ℝ} (hf : MemLp f 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure) (m : ℕ) :
    inner ℝ (MemLp.toLp f hf) (eFamE m)
      = (Real.sqrt (eFamD m))⁻¹ * ∫ θ in Iθ, f θ * eM m θ * Real.cos θ := by
  rw [eFamE, inner_smul_right, inner_toLp_eFamLp]

theorem inner_eFamE_toLp {g : ℝ → ℝ} (hg : MemLp g 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure) (m : ℕ) :
    inner ℝ (eFamE m) (MemLp.toLp g hg)
      = (Real.sqrt (eFamD m))⁻¹ * ∫ θ in Iθ, eM m θ * g θ * Real.cos θ := by
  have hcomm : (∫ θ in Iθ, g θ * eM m θ * Real.cos θ)
      = ∫ θ in Iθ, eM m θ * g θ * Real.cos θ :=
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [real_inner_comm, inner_toLp_eFamE, hcomm]

/-- The inner product of the `m`-th mode with an arbitrary `L²`-class is the weighted integral
against that class's representative. -/
theorem inner_eFamLp_any (m : ℕ) (y : Lp ℝ 2 Work.FTS.EllipticEst.LevelOneAsm.angMeasure) :
    inner ℝ (eFamLp m) y = ∫ θ in Iθ, eM m θ * (y : ℝ → ℝ) θ * Real.cos θ := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun a => inner ℝ ((eFamLp m : ℝ → ℝ) a) ((y : ℝ → ℝ) a))
      =ᵐ[Work.FTS.EllipticEst.LevelOneAsm.angMeasure] fun a => eM m a * (y : ℝ → ℝ) a := by
    filter_upwards [eFamLp_coe m] with a ha
    rw [ha, Real.inner_apply]
  rw [integral_congr_ae h1, Work.FTS.EllipticEst.LevelOneAsm.integral_angMeasure]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-- **The weighted integral of a mode on `Iθ` equals its interval integral on `(0, π/2)`** (the
two differ only at `θ = 0`, which is a null set); needed to compare `cmode` (interval form) with
the inner product (set-integral form). -/
theorem integral_Iθ_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ θ in Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le
    (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)).symm

end Work.EllipticEst.ModalSolution
