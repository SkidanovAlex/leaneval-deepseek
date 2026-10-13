import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.Pieces.L12FK_add_ge0
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.n3split
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.densNormCS
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.L12densN1Sum
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.SliceSlot
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.starPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.LintEngine
import Submission.Work.FTS.H2.InvOneAddSq
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Coercivity.slice_cs_K
import Submission.Work.Coercivity.K_facts
import Submission.Work.Coercivity.integral_Itheta_K
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.Rl1

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 3200000

/-!
# `n3Bound` — the `N₃`-row of the `L₁₂(N)(0)` estimate

The goal is
`∫_{s>0} ‖L₁₂dens(N₃ α (F_*+g) (Φ_s+Φ_g)) s‖ ≤ K(α² + √α·X + α^{-3/2}X²)`, `X = |g|_{ℋ⁴}`.

`N₃ = -2α·𝒱(Φ̃)·D_zF` with `Φ̃ = Φ̃_* + Φ̃_g` and `F = F_* + g`, so on the open quadrant
(`n3split`)

  `N₃ = -2α·(𝒱(Φ̃_g) + 𝒱(Φ̃_*))·(D_zg + D_zF_*)`,

and the two coefficients are bounded *pointwise* — `|𝒱(Φ̃_g)| ≤ 10√(10/α)·max Ce 0·X`
(`gPt`) and `|𝒱(Φ̃_*)| ≤ max Cs 0·α` (`starPt`).  Hence

  `‖L₁₂dens(N₃) s‖ ≤ (c₀/s)·∫_θ K(θ)(|D_zg| + |D_zF_*|)`,  `c₀ = 2α(cg + cs)`,

and Cauchy–Schwarz against the weight `K` (`Coercivity.slice_cs_K`) followed by `√(w s) =
(1+s)/s` turns the right-hand side into

  `A s · B s`,  `A s = 3·c₀·√(w s·Φ(s))`,  `B s = 1/(1+s)`,
  `Φ(s) = ∫_θ ((D_zg)² + (D_zF_*)²)`.

`w·Φ` is integrable with `∫ w·Φ ≤ HkSq α 4 g + 1600πα²` (the `i = 1` slot for the `g`-part,
`FstarPt` for the `F_*`-part), and `densNormCS` (Cauchy–Schwarz in `s`) gives
`≤ √(∫A²)·√(∫B²) ≤ 3√2·c₀·(X + 40√π·α)`, whence the stated bound.
-/

/-! ## Elementary `θ`-calculus -/

/-- `K θ = 3 sin θ cos²θ ≥ 0` on `Iθ = [0,π/2]`. -/
theorem K_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ :=
  Work.Coercivity.K_facts_nonneg θ hθ

/-- `K θ ≤ 3` on `Iθ`. -/
theorem K_le_three_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.K θ ≤ 3 :=
  Work.Coercivity.K_facts_le_three θ hθ

/-- The Lebesgue measure of `Iθ` is `π/2`. -/
theorem real_volume_Iθ :
    (MeasureTheory.volume : MeasureTheory.Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
  rw [Work.Spaces.Iθ, MeasureTheory.Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- The integral of a constant over `Iθ`. -/
theorem setIntegral_const_Iθ (c : ℝ) :
    (∫ _θ in Work.Spaces.Iθ, c) = c * (Real.pi / 2) := by
  rw [MeasureTheory.setIntegral_const, real_volume_Iθ, smul_eq_mul]
  ring

/-- The open angular interval and `Iθ` carry the same measure. -/
theorem restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  MeasureTheory.Measure.restrict_congr_set
    (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- The radial weight is nonnegative everywhere (the value at `0` is junk). -/
theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The radial weight is `≥ 1` on `z > 0`. -/
theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [sq_nonneg z]

/-- The radial weight is positive on `z > 0`. -/
theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z :=
  lt_of_lt_of_le zero_lt_one (one_le_w_of_pos hz)

/-- The trivial pointwise bound on the `L₁₂`-density: the norm of the `θ`-integral is at most
the integral of the norm. -/
theorem dens_le_theta (f : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    ‖Work.Construction.L12dens f s‖
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f s θ| / s := by
  rw [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ]
  refine (norm_integral_le_integral_norm
    (f := fun θ : ℝ => Work.Spaces.K θ * f s θ / s)).trans ?_
  refine le_of_eq ?_
  exact MeasureTheory.setIntegral_congr_fun (s := Set.Icc (0 : ℝ) (π / 2))
    measurableSet_Icc (fun θ hθ => by
      have hK : 0 ≤ Work.Spaces.K θ := K_nonneg_of_mem (by rw [Work.Spaces.Iθ]; exact hθ)
      have hkey : Work.Spaces.K θ * f s θ / s = (Work.Spaces.K θ / s) * f s θ := by ring
      rw [hkey, norm_mul, Real.norm_of_nonneg (div_nonneg hK hs.le), Real.norm_eq_abs]
      ring)

/-- A bounded slice has an `L²`-norm bounded by the constant. -/
theorem int_slice_sq_le_of_bound {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ C) :
    (∫ θ in Work.Spaces.Iθ, f θ ^ 2) ≤ (π / 2) * C ^ 2 := by
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => C ^ 2) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; simp)
  have hle := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => sq_nonneg (f θ)) hconst
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f θ)) (h θ hθ) 2))
  rw [setIntegral_const_Iθ] at hle
  simpa only [mul_comm] using hle

/-- The `θ`-Cauchy–Schwarz against the weight `K` of a nonnegative slice. -/
theorem slice_cs_K_nonneg {J : ℝ → ℝ} (s : ℝ)
    (hL2 : MeasureTheory.IntegrableOn (fun θ => J θ ^ 2) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * J θ) ≤ Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, J θ ^ 2) := by
  have hcs := Work.Coercivity.slice_cs_K (fun _ θ => J θ) s
    Work.Coercivity.K_facts_nonneg Work.Coercivity.K_facts_sq_integrableOn
    Work.Coercivity.K_facts.2.2.2 (by simpa using hL2)
  exact Real.le_sqrt_of_sq_le hcs

/-- Four-term triangle inequality. -/
theorem abs_add_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-- `α·√(10/α) ≤ 4` for `0 < α ≤ 1`. -/
theorem alpha_mul_sqrt_div_le_four {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α * Real.sqrt (10 / α) ≤ 4 := by
  have h1 : α * Real.sqrt (10 / α) = Real.sqrt (10 * α) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 10) α,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10) α]
    have hs : Real.sqrt α ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hα)
    field_simp
    rw [Real.sq_sqrt hα.le]
  rw [h1]
  calc Real.sqrt (10 * α) ≤ Real.sqrt 10 := Real.sqrt_le_sqrt (by nlinarith)
    _ ≤ 4 := by
        rw [Real.sqrt_le_iff]
        exact ⟨by norm_num, by norm_num⟩

/-- `√(w s·φ)·(1+s)⁻¹ = √φ·s⁻¹` for `s > 0` and `φ ≥ 0`. -/
theorem sqrt_w_mul_mul_inv {s φ : ℝ} (hs : 0 < s) (hφ : 0 ≤ φ) :
    Real.sqrt (Work.Spaces.w s * φ) * (1 / (1 + s)) = Real.sqrt φ * (1 / s) := by
  have hw : Work.Spaces.w s = ((1 + s) / s) ^ 2 := by rw [Work.Spaces.w, div_pow]
  rw [hw, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  field_simp

/-! ## The `θ`-slice of `D_z g` and its slot -/

/-- `SmoothQuad` is preserved by `D_z`. -/
theorem smoothQuad_Dz {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz g) :=
  Work.FTS.LocData.contDiffOn_Dz (isOpen_Ioi.prod isOpen_Ioo) hsm

/-- The `i = 1` slot of `HkIntegrand` dominates `(D_zg)²` on the open quadrant. -/
theorem slice_sq_le_HkIntegrand {α : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    (Work.Spaces.Dz g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hw1 : 1 ≤ Work.Spaces.w z := one_le_w_of_pos hz
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  set S : ℝ := (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hSdef
  have hSpos : 0 < S := by rw [hSdef]; exact Real.rpow_pos_of_pos hs _
  have hS1 : S ≤ 1 := by
    rw [hSdef]
    exact Real.rpow_le_one hs.le (Real.sin_le_one _) (by rw [Work.Spaces.eta]; norm_num)
  have hle : 1 ≤ Work.Spaces.w z / S := by
    rw [le_div_iff₀ hSpos]
    nlinarith [hw1, hS1]
  have h1 : (Work.Spaces.Dz g z θ) ^ 2
      ≤ (Work.Spaces.Dz g z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    have h2 : (1 : ℝ) ≤ (Work.Spaces.w z / S) ^ 2 := by nlinarith [hle]
    calc (Work.Spaces.Dz g z θ) ^ 2 = (Work.Spaces.Dz g z θ) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.Dz g z θ) ^ 2 * (Work.Spaces.w z / S) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = (Work.Spaces.Dz g z θ * (Work.Spaces.w z / S)) ^ 2 := by ring
  have hslot := Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 1 (by norm_num)
  have hDz : Work.Spaces.DzIter 1 g z θ = Work.Spaces.Dz g z θ := rfl
  rw [hDz] at hslot
  exact le_trans h1 hslot

/-- The `θ`-slice square of `D_zg` is integrable on `Iθ`. -/
theorem integrableOn_slice_Dz_sq {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.Dz g z θ) ^ 2) Work.Spaces.Iθ := by
  refine (hmem.1 z (by rw [Work.Spaces.Iz, Set.mem_Ici]; exact hz.le)).mono'
    (AEStronglyMeasurable.pow
      (Work.FTS.Nonlinear.Pieces.Rl1.aesm_slice_of_smoothQuad (smoothQuad_Dz hsm) hz) 2) ?_
  rw [← restrict_Ioo_eq_restrict_Iθ]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact slice_sq_le_HkIntegrand hz hθ.1 hθ.2)

/-! ## The function `Φ` and its weighted energy -/

/-- `Φ(s) = ∫_θ ((D_zg)² + (D_zF_*)²)`, the angular energy driving the estimate. -/
def PhiF (α : ℝ) (g : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.Dz g s θ) ^ 2
    + (Work.Spaces.Dz (Work.Construction.Fstar α) s θ) ^ 2)

theorem PhiF_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (s : ℝ) : 0 ≤ PhiF α g s :=
  integral_nonneg fun θ => add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- `D_z` of the profile is `SmoothQuad`. -/
theorem smoothQuad_Dz_Fstar (α : ℝ) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
  smoothQuad_Dz (Work.FTS.LocData.Fstar_smoothQuad α)

/-- The `D_zF_*`-slice square is integrable on `Iθ`. -/
theorem integrableOn_slice_DzFstar_sq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ^ 2) Work.Spaces.Iθ := by
  have hb : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 40 * α * (z / (1 + z) ^ 2) :=
    fun θ hθ => (Work.FTS.Nonlinear.Pieces.rl1Tools.FstarPt hα hα1 hz.le hθ).2
  refine (MeasureTheory.integrableOn_const (C := (40 * α * (z / (1 + z) ^ 2)) ^ 2)
    (by rw [Work.Spaces.Iθ, Real.volume_Icc]; simp)).mono'
    (AEStronglyMeasurable.pow
      (Work.FTS.Nonlinear.Pieces.Rl1.aesm_slice_of_smoothQuad (smoothQuad_Dz_Fstar α) hz) 2) ?_
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb θ hθ) 2)

/-- The two factors of `Φ` split (both slices are integrable). -/
theorem PhiF_eq_add {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ}
    (hs : 0 < s) :
    PhiF α g s = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz g s θ) ^ 2)
      + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Construction.Fstar α) s θ) ^ 2) := by
  rw [PhiF]
  exact MeasureTheory.integral_add (integrableOn_slice_Dz_sq hsm hmem hs)
    (integrableOn_slice_DzFstar_sq hα hα1 hs)

/-- The weighted angular energy of `Φ`. -/
theorem w_PhiF_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) {s : ℝ}
    (hs : 0 < s) :
    Work.Spaces.w s * PhiF α g s
      ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
        + 800 * π * α ^ 2 / (1 + s) ^ 2 := by
  have h1 : Work.Spaces.w s * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz g s θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ := by
    have h := (Work.FTS.Nonlinear.Pieces.Rl1.SliceSlot α 4 g hα hmem).2 1 (by norm_num) s hs
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h
  have h2 : Work.Spaces.w s
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Construction.Fstar α) s θ) ^ 2)
      ≤ 800 * π * α ^ 2 / (1 + s) ^ 2 := by
    have hb : ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.Dz (Work.Construction.Fstar α) s θ| ≤ 40 * α * (s / (1 + s) ^ 2) :=
      fun θ hθ => (Work.FTS.Nonlinear.Pieces.rl1Tools.FstarPt hα hα1 hs.le hθ).2
    have hle := int_slice_sq_le_of_bound (C := 40 * α * (s / (1 + s) ^ 2))
      (by positivity) hb
    have hw1 : 0 < Work.Spaces.w s := lt_of_lt_of_le zero_lt_one (one_le_w_of_pos hs)
    calc Work.Spaces.w s
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Construction.Fstar α) s θ) ^ 2)
        ≤ Work.Spaces.w s * ((π / 2) * (40 * α * (s / (1 + s) ^ 2)) ^ 2) :=
          mul_le_mul_of_nonneg_left hle hw1.le
      _ = 800 * π * α ^ 2 / (1 + s) ^ 2 := by
          rw [Work.Spaces.w]
          field_simp
          ring
  rw [PhiF_eq_add hα hα1 hsm hmem hs, mul_add]
  linarith

/-- `s ↦ w s·Φ(s)` is a.e. strongly measurable. -/
theorem aesm_w_PhiF {α : ℝ} {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) :
    AEStronglyMeasurable (fun s => Work.Spaces.w s * PhiF α g s)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hcont1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Work.FTS.LocData.contDiffOn_Dz (V := Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2))
      (isOpen_Ioi.prod isOpen_Ioo) hsm).continuousOn.mono (fun p hp => by
        simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
        exact ⟨by linarith [hp.1], hp.2⟩)
  have hcont2 : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Work.FTS.LocData.contDiffOn_Dz (V := Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2))
      (isOpen_Ioi.prod isOpen_Ioo)
      (Work.FTS.LocData.Fstar_smoothQuad α)).continuousOn.mono (fun p hp => by
        simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
        exact ⟨by linarith [hp.1], hp.2⟩)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.Dz g p.1 p.2) ^ 2
      + (Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (hcont1.pow 2).add (hcont2.pow 2)
  have hquad := Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => (Work.Spaces.Dz g p.1 p.2) ^ 2
      + (Work.Spaces.Dz (Work.Construction.Fstar α) p.1 p.2) ^ 2) hcont
  have hslice : AEStronglyMeasurable (fun s => PhiF α g s) (volume.restrict Work.Spaces.Iz) := by
    simpa only [PhiF, Work.Spaces.Iz] using hquad.integral_prod_right'
  have h1 : AEStronglyMeasurable (fun s => PhiF α g s)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hslice.mono_measure (MeasureTheory.Measure.restrict_mono_set volume Set.Ioi_subset_Ici_self)
  have h2 : AEStronglyMeasurable (fun s : ℝ => Work.Spaces.w s)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hwmeas : Measurable (fun s : ℝ => (1 + s) ^ 2 / s ^ 2) := by fun_prop
    simpa only [Work.Spaces.w] using hwmeas.aestronglyMeasurable
  exact h2.mul h1

/-- Integrability and the integral bound for `w·Φ`. -/
theorem integrableOn_w_PhiF {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.IntegrableOn (fun s => Work.Spaces.w s * PhiF α g s) (Set.Ioi (0 : ℝ)) ∧
      (∫ s in Set.Ioi (0 : ℝ), Work.Spaces.w s * PhiF α g s)
        ≤ Work.Spaces.HkSq α 4 g + 1600 * π * α ^ 2 := by
  have hH : MeasureTheory.Integrable
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hmem.2.mono_set Set.Ioi_subset_Ici_self
  have haesmI : MeasureTheory.AEStronglyMeasurable
      (fun s => 800 * π * α ^ 2 / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (by
      have hwmeas : Measurable (fun s : ℝ => 800 * π * α ^ 2 / (1 + s) ^ 2) := by fun_prop
      exact hwmeas.aestronglyMeasurable)
  have hI : MeasureTheory.Integrable (fun s => 800 * π * α ^ 2 / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine (Work.FTS.H2.InvOneAddSq.1.const_mul (800 * π * α ^ 2)).congr
      (Filter.Eventually.of_forall (fun s => ?_))
    show 800 * π * α ^ 2 * (1 / (1 + s)) ^ 2 = 800 * π * α ^ 2 / (1 + s) ^ 2
    rw [div_pow, one_pow, mul_one_div]
  have hmaj : MeasureTheory.Integrable
      (fun s => (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
        + 800 * π * α ^ 2 / (1 + s) ^ 2) (volume.restrict (Set.Ioi (0 : ℝ))) := hH.add hI
  have hbd : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Work.Spaces.w s * PhiF α g s
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          + 800 * π * α ^ 2 / (1 + s) ^ 2 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun s hs => w_PhiF_le hα hα1 hsm hmem hs)
  have hbd' : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖Work.Spaces.w s * PhiF α g s‖
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
          + 800 * π * α ^ 2 / (1 + s) ^ 2 :=
    hbd.mono fun s hs => by
      rw [Real.norm_of_nonneg (mul_nonneg (w_nonneg s) (PhiF_nonneg α g s))]
      exact hs
  have hw0 : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun s => Work.Spaces.w s * PhiF α g s) :=
    Filter.Eventually.of_forall fun s =>
      mul_nonneg (w_nonneg s) (PhiF_nonneg α g s)
  have hHval : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 g s θ) = Work.Spaces.HkSq α 4 g := by
    rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    rfl
  have hIval : (∫ s in Set.Ioi (0 : ℝ), 800 * π * α ^ 2 / (1 + s) ^ 2)
      = 800 * π * α ^ 2 * (∫ s in Set.Ioi (0 : ℝ), (1 / (1 + s)) ^ 2) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => by
      show 800 * π * α ^ 2 / (1 + s) ^ 2 = 800 * π * α ^ 2 * (1 / (1 + s)) ^ 2
      rw [div_pow, one_pow, mul_one_div]))
  constructor
  · exact hmaj.mono' (aesm_w_PhiF hsm) hbd'
  · refine (MeasureTheory.integral_mono_of_nonneg hw0 hmaj hbd).trans ?_
    rw [MeasureTheory.integral_add hH hI, hHval, hIval]
    have h2 : (∫ s in Set.Ioi (0 : ℝ), (1 / (1 + s)) ^ 2) ≤ 2 := Work.FTS.H2.InvOneAddSq.2
    have h3 : 800 * π * α ^ 2 * (∫ s in Set.Ioi (0 : ℝ), (1 / (1 + s)) ^ 2) ≤ 2 * (800 * π * α ^ 2) := by
      calc 800 * π * α ^ 2 * (∫ s in Set.Ioi (0 : ℝ), (1 / (1 + s)) ^ 2)
          ≤ 800 * π * α ^ 2 * 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2 * (800 * π * α ^ 2) := by ring
    linarith

/-! ## The estimate -/

/-- `|(-2)·α·A·B| ≤ 2α·cA·|B|` when `|A| ≤ cA`. -/
theorem abs_neg_two_mul_abs_le {α cA A B : ℝ} (hα : 0 ≤ α) (hA : |A| ≤ cA) :
    |-2 * α * A * B| ≤ 2 * α * cA * |B| := by
  have h2 : |-2 * α * A * B| = 2 * α * |A| * |B| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hα]
    norm_num
  rw [h2]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by positivity)) (abs_nonneg B)

/-- `α² ≤ α^{-3/2}` for `0 < α ≤ 1`. -/
theorem sq_le_rpow_neg_three_halves {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ 2 ≤ α ^ (-(3 / 2 : ℝ)) := by
  have h3 : α ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
  have h7 : (0 : ℝ) < α ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hα _
  have h8 : α ^ (-(3 / 2 : ℝ)) = (α ^ (3 / 2 : ℝ))⁻¹ := by
    rw [show (-(3 / 2 : ℝ)) = -(3 / 2) by ring, Real.rpow_neg hα.le]
  have h9 : 1 ≤ α ^ (-(3 / 2 : ℝ)) := by
    rw [h8]
    exact (one_le_inv₀ h7).mpr h3
  have h10 : α ^ 2 ≤ 1 := by nlinarith [hα1, hα.le]
  linarith

/-- `α²·X ≤ α² + α^{-3/2}X²` for `0 < α ≤ 1`, `0 ≤ X`. -/
theorem sq_mul_le_self_add {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    α ^ 2 * X ≤ α ^ 2 + α ^ (-(3 / 2 : ℝ)) * X ^ 2 := by
  have h4 := sq_le_rpow_neg_three_halves hα hα1
  by_cases h : X ≤ 1
  · have h1 : α ^ 2 * X ≤ α ^ 2 * 1 := mul_le_mul_of_nonneg_left h (sq_nonneg α)
    have h2 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg X)
    linarith
  · push_neg at h
    have hX2 : X ≤ X ^ 2 := by nlinarith
    have h5 : α ^ 2 * X ≤ α ^ 2 * X ^ 2 := mul_le_mul_of_nonneg_left hX2 (sq_nonneg α)
    have h6 : α ^ 2 * X ^ 2 ≤ α ^ (-(3 / 2 : ℝ)) * X ^ 2 :=
      mul_le_mul_of_nonneg_right h4 (sq_nonneg X)
    linarith [h5, h6, sq_nonneg α]

/-- `√α ≤ 1` and `α ≤ √α` for `0 < α ≤ 1`. -/
theorem alpha_le_sqrt_alpha {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ≤ Real.sqrt α ∧ Real.sqrt α ≤ 1 := by
  have h1 : Real.sqrt α ≤ 1 := Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using hα1⟩
  refine ⟨?_, h1⟩
  nlinarith [Real.sq_sqrt hα.le, Real.sqrt_nonneg α]

/-- The `N₃` pointwise bound on the open quadrant. -/
theorem n3_pt {α cg cs c₀ : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hsmg : Work.FTS.LocData.SmoothQuad g) (hφss : Work.FTS.LocData.SmoothQuad Φs)
    (hφgg : Work.FTS.LocData.SmoothQuad Φg)
    (hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z)
    (hL12 : ∀ z : ℝ, 0 < z →
        DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z)
    (hVg : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < π / 2 →
        |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ| ≤ cg)
    (hVs : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ cs)
    (hc₀ : c₀ = 2 * α * (cg + cs)) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |Work.Construction.N3 α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) s θ|
        ≤ c₀ * (|Work.Spaces.Dz g s θ| + |Work.Spaces.Dz (Work.Construction.Fstar α) s θ|) := by
  rw [← restrict_Ioo_eq_restrict_Iθ]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hsplit := n3split hα hα1 hsmg hφss hφgg hL hL12 s θ ⟨hs, hθ0, hθ1⟩
  have hA1 : |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) s θ| ≤ cg :=
    hVg s hs θ hθ0 hθ1
  have hA2 : |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) s θ| ≤ cs :=
    hVs s (by rw [Work.Spaces.Iz, Set.mem_Ici]; exact hs.le) θ
      (by rw [Work.Spaces.Iθ]; exact ⟨hθ0.le, hθ1.le⟩)
  set V1 : ℝ := Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) s θ with hV1def
  set V2 : ℝ := Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) s θ with hV2def
  set D1 : ℝ := Work.Spaces.Dz g s θ with hD1def
  set D2 : ℝ := Work.Spaces.Dz (Work.Construction.Fstar α) s θ with hD2def
  have hsplit' : Work.Construction.N3 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) s θ
      = -2 * α * V1 * D1 + (-2 * α * V1 * D2) + (-2 * α * V2 * D1)
        + (-2 * α * V2 * D2) := by
    rw [hsplit]
    simp only [Work.FTS.Nonlin.N3gg, Work.FTS.Nonlin.N3gs, Work.FTS.Nonlin.N3sg,
      Work.FTS.Nonlin.N3ss]
    ring
  rw [hsplit']
  have e1 : |-2 * α * V1 * D1| ≤ 2 * α * cg * |D1| := abs_neg_two_mul_abs_le hα.le hA1
  have e2 : |-2 * α * V1 * D2| ≤ 2 * α * cg * |D2| := abs_neg_two_mul_abs_le hα.le hA1
  have e3 : |-2 * α * V2 * D1| ≤ 2 * α * cs * |D1| := abs_neg_two_mul_abs_le hα.le hA2
  have e4 : |-2 * α * V2 * D2| ≤ 2 * α * cs * |D2| := abs_neg_two_mul_abs_le hα.le hA2
  calc |-2 * α * V1 * D1 + (-2 * α * V1 * D2) + (-2 * α * V2 * D1) + (-2 * α * V2 * D2)|
      ≤ |-2 * α * V1 * D1| + |-2 * α * V1 * D2| + |-2 * α * V2 * D1| + |-2 * α * V2 * D2| :=
        abs_add_four_le _ _ _ _
    _ ≤ 2 * α * cg * |D1| + 2 * α * cg * |D2| + 2 * α * cs * |D1| + 2 * α * cs * |D2| := by
        linarith [e1, e2, e3, e4]
    _ = c₀ * (|D1| + |D2|) := by
        rw [hc₀]
        ring

/-- The pointwise-in-`s` bound for the `L₁₂`-density of `N₃`. -/
theorem n3_dens_le {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn} {c₀ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc₀ : 0 ≤ c₀)
    (hsmg : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (hpt : ∀ s : ℝ, 0 < s → ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |Work.Construction.N3 α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) s θ|
        ≤ c₀ * (|Work.Spaces.Dz g s θ| + |Work.Spaces.Dz (Work.Construction.Fstar α) s θ|))
    {s : ℝ} (hs : 0 < s) :
    ‖Work.Construction.L12dens (Work.Construction.N3 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) s‖
      ≤ (3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s)) * (1 / (1 + s)) := by
  set J : ℝ → ℝ := fun θ => |Work.Spaces.Dz g s θ|
    + |Work.Spaces.Dz (Work.Construction.Fstar α) s θ| with hJ
  have hJ0 : ∀ θ, 0 ≤ J θ := fun θ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have haesmJ : MeasureTheory.AEStronglyMeasurable J (volume.restrict Work.Spaces.Iθ) := by
    rw [hJ]
    exact ((Work.FTS.Nonlinear.Pieces.Rl1.aesm_slice_of_smoothQuad
        (smoothQuad_Dz hsmg) hs).norm).add
      ((Work.FTS.Nonlinear.Pieces.Rl1.aesm_slice_of_smoothQuad (smoothQuad_Dz_Fstar α) hs).norm)
  have hJ2 : MeasureTheory.IntegrableOn (fun θ => J θ ^ 2) Work.Spaces.Iθ := by
    refine ((integrableOn_slice_Dz_sq hsmg hmem hs).add
      (integrableOn_slice_DzFstar_sq hα hα1 hs)).const_mul 2 |>.mono'
      (haesmJ.pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    show (|Work.Spaces.Dz g s θ| + |Work.Spaces.Dz (Work.Construction.Fstar α) s θ|) ^ 2
      ≤ 2 * ((Work.Spaces.Dz g s θ) ^ 2 + (Work.Spaces.Dz (Work.Construction.Fstar α) s θ) ^ 2)
    nlinarith [sq_nonneg (|Work.Spaces.Dz g s θ|
        - |Work.Spaces.Dz (Work.Construction.Fstar α) s θ|),
      sq_abs (Work.Spaces.Dz g s θ), sq_abs (Work.Spaces.Dz (Work.Construction.Fstar α) s θ)]
  have hKJ : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * J θ) Work.Spaces.Iθ := by
    refine (Work.Coercivity.K_facts_sq_integrableOn.add hJ2).const_mul (1 / 2) |>.mono'
      ((Work.Coercivity.K_facts_continuous.aestronglyMeasurable).mul haesmJ) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (K_nonneg_of_mem hθ) (hJ0 θ))]
    show Work.Spaces.K θ * J θ ≤ 1 / 2 * (Work.Spaces.K θ ^ 2 + (J θ) ^ 2)
    nlinarith [sq_nonneg (Work.Spaces.K θ - J θ)]
  -- (1) the density bound
  have h1 := dens_le_theta (Work.Construction.N3 α (Work.Construction.Ftot α g)
    (fun z θ => Φs z θ + Φg z θ)) hs
  -- (2) the monotone step
  have h2 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
        * |Work.Construction.N3 α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + Φg z θ) s θ| / s)
      ≤ ∫ θ in Work.Spaces.Iθ, (c₀ / s) * (Work.Spaces.K θ * J θ) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
        div_nonneg (mul_nonneg (K_nonneg_of_mem hθ) (abs_nonneg _)) hs.le))
      (hKJ.const_mul (c₀ / s)) ?_
    filter_upwards [hpt s hs, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ hmem
    rw [div_le_iff₀ hs]
    have hK0 : 0 ≤ Work.Spaces.K θ := K_nonneg_of_mem hmem
    have hstep : Work.Spaces.K θ * |Work.Construction.N3 α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ) s θ|
        ≤ Work.Spaces.K θ * (c₀ * J θ) := by
      refine mul_le_mul_of_nonneg_left ?_ hK0
      simpa only [hJ] using hθ
    have h3 : ((c₀ / s) * (Work.Spaces.K θ * J θ)) * s = c₀ * (Work.Spaces.K θ * J θ) := by
      field_simp
    have h4 : Work.Spaces.K θ * (c₀ * J θ) = c₀ * (Work.Spaces.K θ * J θ) := by ring
    rw [h3, ← h4]
    exact hstep
  -- (3) pull the constant out
  have h3 : (∫ θ in Work.Spaces.Iθ, (c₀ / s) * (Work.Spaces.K θ * J θ))
      = (c₀ / s) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * J θ :=
    MeasureTheory.integral_const_mul _ _
  -- (4) the `θ`-Cauchy–Schwarz
  have h4 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * J θ)
      ≤ Real.sqrt (3 * ∫ θ in Work.Spaces.Iθ, J θ ^ 2) :=
    slice_cs_K_nonneg s hJ2
  -- (5) the slice energy
  have h5 : (∫ θ in Work.Spaces.Iθ, J θ ^ 2) ≤ 2 * PhiF α g s := by
    have hpt2 : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        J θ ^ 2 ≤ 2 * ((Work.Spaces.Dz g s θ) ^ 2
          + (Work.Spaces.Dz (Work.Construction.Fstar α) s θ) ^ 2) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
      show (|Work.Spaces.Dz g s θ| + |Work.Spaces.Dz (Work.Construction.Fstar α) s θ|) ^ 2
        ≤ 2 * ((Work.Spaces.Dz g s θ) ^ 2 + (Work.Spaces.Dz (Work.Construction.Fstar α) s θ) ^ 2)
      nlinarith [sq_nonneg (|Work.Spaces.Dz g s θ|
          - |Work.Spaces.Dz (Work.Construction.Fstar α) s θ|),
        sq_abs (Work.Spaces.Dz g s θ), sq_abs (Work.Spaces.Dz (Work.Construction.Fstar α) s θ)]
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => sq_nonneg (J θ)))
      ((integrableOn_slice_Dz_sq hsmg hmem hs).add
        (integrableOn_slice_DzFstar_sq hα hα1 hs) |>.const_mul 2) hpt2
    have hmono2 : (∫ a in Work.Spaces.Iθ, J a ^ 2)
        ≤ ∫ a in Work.Spaces.Iθ, 2 * ((Work.Spaces.Dz g s a) ^ 2
          + (Work.Spaces.Dz (Work.Construction.Fstar α) s a) ^ 2) := hmono
    have hEq : (∫ a in Work.Spaces.Iθ, 2 * ((Work.Spaces.Dz g s a) ^ 2
          + (Work.Spaces.Dz (Work.Construction.Fstar α) s a) ^ 2)) = 2 * PhiF α g s := by
      rw [MeasureTheory.integral_const_mul]
      rfl
    linarith [hmono2, hEq.le, hEq.ge]
  -- assembly
  have hA : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * J θ)
      ≤ Real.sqrt (6 * PhiF α g s) := by
    refine h4.trans (Real.sqrt_le_sqrt ?_)
    linarith [h5]
  have hfin : (c₀ / s) * Real.sqrt (6 * PhiF α g s)
      ≤ 3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s) * (1 / (1 + s)) := by
    have h6le : Real.sqrt 6 ≤ 3 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by norm_num, by norm_num⟩
    have h6 : Real.sqrt (6 * PhiF α g s) ≤ 3 * Real.sqrt (PhiF α g s) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
      exact mul_le_mul_of_nonneg_right h6le (Real.sqrt_nonneg _)
    have hstep : (c₀ / s) * Real.sqrt (6 * PhiF α g s)
        ≤ (c₀ / s) * (3 * Real.sqrt (PhiF α g s)) :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    have hrw : (c₀ / s) * (3 * Real.sqrt (PhiF α g s))
        = 3 * c₀ * (Real.sqrt (PhiF α g s) * (1 / s)) := by ring
    have hrw2 : 3 * c₀ * (Real.sqrt (PhiF α g s) * (1 / s))
        = (3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s)) * (1 / (1 + s)) := by
      rw [← sqrt_w_mul_mul_inv hs (PhiF_nonneg α g s)]
      ring
    exact le_trans hstep (le_trans (le_of_eq hrw) (le_of_eq hrw2))
  refine le_trans h1 ?_
  refine le_trans h2 ?_
  rw [h3]
  refine le_trans (mul_le_mul_of_nonneg_left hA (by positivity)) ?_
  exact hfin

theorem n3Bound {α₂ Ci Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      (∫ s in Set.Ioi (0 : ℝ), ‖Work.Construction.L12dens (Work.Construction.N3 α
          (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) s‖)
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  refine ⟨3000000 * (max Ce 0 + max Cs 0) + 1, ?_, ?_⟩
  · have h1 : 0 ≤ max Ce 0 := le_max_right _ _
    have h2 : 0 ≤ max Cs 0 := le_max_right _ _
    linarith
  · intro α g Φs Φg hg hsp hep hα hα1 hαα₂
    have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hg
    have hsmg : Work.FTS.LocData.SmoothQuad g := hreg4.1
    have hmem : Work.Spaces.HkMem α 4 g := hreg4.2.1
    have hφss : Work.FTS.LocData.SmoothQuad Φs := hsp.smooth
    have hφgg : Work.FTS.LocData.SmoothQuad Φg := hep.smooth
    have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hadd := Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hg
    have hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z :=
      fun z hz => hadd.1 z hz.le
    have hL12 : ∀ z : ℝ, 0 < z →
        DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z :=
      fun z hz => hN.l12diff α ⟨hα, hαα₂⟩ g hsmg hmem z hz
    obtain ⟨_, _, hVg⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.gPt hα hα1 hep
    obtain ⟨_, hVs, _⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hsp
    obtain ⟨hPhi_int, hPhi_le⟩ := integrableOn_w_PhiF hα hα1 hsmg hmem
    -- the coefficient
    set c₀ : ℝ := 2 * α * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g
      + max Cs 0 * α) with hc₀def
    have hc₀0 : 0 ≤ c₀ := by
      rw [hc₀def]
      refine mul_nonneg (by positivity) (add_nonneg ?_ ?_)
      · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (le_max_right _ _)) hX
      · exact mul_nonneg (le_max_right _ _) hα.le
    -- the pointwise bound in θ
    have hpt : ∀ s : ℝ, 0 < s → ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |Work.Construction.N3 α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + Φg z θ) s θ|
          ≤ c₀ * (|Work.Spaces.Dz g s θ|
            + |Work.Spaces.Dz (Work.Construction.Fstar α) s θ|) := by
      intro s hs
      rw [hc₀def]
      exact n3_pt hα hα1 hsmg hφss hφgg hL hL12 hVg hVs rfl hs
    -- the pointwise bound in s
    have hdens : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ‖Work.Construction.L12dens (Work.Construction.N3 α (Work.Construction.Ftot α g)
            (fun z θ => Φs z θ + Φg z θ)) s‖
          ≤ (3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s)) * (1 / (1 + s)) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun s hs => n3_dens_le hα hα1 hc₀0 hsmg hmem hpt hs)
    -- the two Cauchy–Schwarz factors
    have hA_mem : MeasureTheory.MemLp
        (fun s => 3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s)) 2
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have hsqrt : MeasureTheory.AEStronglyMeasurable
          (fun s => Real.sqrt (Work.Spaces.w s * PhiF α g s))
          (volume.restrict (Set.Ioi (0 : ℝ))) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (aesm_w_PhiF hsmg)
      have haesm : MeasureTheory.AEStronglyMeasurable
          (fun s => 3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s))
          (volume.restrict (Set.Ioi (0 : ℝ))) :=
        hsqrt.const_mul (3 * c₀)
      rw [MeasureTheory.memLp_two_iff_integrable_sq haesm]
      refine (hPhi_int.const_mul (9 * c₀ ^ 2)).congr
        (Filter.Eventually.of_forall (fun s => ?_))
      show 9 * c₀ ^ 2 * (Work.Spaces.w s * PhiF α g s)
        = (3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s)) ^ 2
      have hsq := Real.sq_sqrt (mul_nonneg (w_nonneg s) (PhiF_nonneg α g s))
      nlinarith [hsq]
    have hB_mem : MeasureTheory.MemLp (fun s : ℝ => 1 / (1 + s)) 2
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      rw [MeasureTheory.memLp_two_iff_integrable_sq
        ((by fun_prop : Measurable (fun s : ℝ => 1 / (1 + s))).aestronglyMeasurable)]
      exact Work.FTS.H2.InvOneAddSq.1
    have hA0 : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun s => 3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s)) :=
      Filter.Eventually.of_forall fun s =>
        mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    have hB0 : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (fun s : ℝ => 1 / (1 + s)) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun s hs => div_nonneg zero_le_one (by
          have hs' : (0 : ℝ) < s := hs
          linarith))
    have hres := densNormCS (h := Work.Construction.N3 α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) hA_mem hB_mem hA0 hB0 hdens
    -- evaluate the two integrals
    have hA2le : (∫ s in Set.Ioi (0 : ℝ),
          (3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s)) ^ 2)
        ≤ 9 * c₀ ^ 2 * (Work.Spaces.HkSq α 4 g + 1600 * π * α ^ 2) := by
      have hEq : (∫ s in Set.Ioi (0 : ℝ),
            (3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s)) ^ 2)
          = 9 * c₀ ^ 2 * (∫ s in Set.Ioi (0 : ℝ), Work.Spaces.w s * PhiF α g s) := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
        show (3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s)) ^ 2
          = 9 * c₀ ^ 2 * (Work.Spaces.w s * PhiF α g s)
        have hsq := Real.sq_sqrt (mul_nonneg (w_nonneg s) (PhiF_nonneg α g s))
        nlinarith [hsq]
      rw [hEq]
      exact mul_le_mul_of_nonneg_left hPhi_le (by positivity)
    have hB2le : (∫ s in Set.Ioi (0 : ℝ), (1 / (1 + s)) ^ 2) ≤ 2 :=
      Work.FTS.H2.InvOneAddSq.2
    -- the square root of the `HkSq`-plus-term
    have hXsq : (Work.FTS.Nonlin.Xn α g) ^ 2 = Work.Spaces.HkSq α 4 g := by
      rw [show Work.FTS.Nonlin.Xn α g = Real.sqrt (Work.Spaces.HkSq α 4 g) from rfl,
        Real.sq_sqrt]
      exact integral_nonneg fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
    have hsqrt_le : Real.sqrt (Work.Spaces.HkSq α 4 g + 1600 * π * α ^ 2)
        ≤ Work.FTS.Nonlin.Xn α g + 40 * Real.sqrt π * α := by
      have hy : (40 * Real.sqrt π * α) ^ 2 = 1600 * π * α ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
        ring
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      rw [← hXsq, ← hy]
      nlinarith [mul_nonneg hX (show (0 : ℝ) ≤ 40 * Real.sqrt π * α by positivity)]
    -- the coefficient bound
    have hterm : 20 * α * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g
        ≤ 80 * max Ce 0 * Work.FTS.Nonlin.Xn α g := by
      have h4 := alpha_mul_sqrt_div_le_four hα hα1
      have h1 : 20 * (α * Real.sqrt (10 / α)) ≤ 20 * 4 := by linarith
      calc 20 * α * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g
          = (20 * (α * Real.sqrt (10 / α))) * max Ce 0 * Work.FTS.Nonlin.Xn α g := by ring
        _ ≤ (20 * 4) * max Ce 0 * Work.FTS.Nonlin.Xn α g :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right h1 (le_max_right _ _)) hX
        _ = 80 * max Ce 0 * Work.FTS.Nonlin.Xn α g := by ring
    have hc₀le : c₀ ≤ 80 * max Ce 0 * Work.FTS.Nonlin.Xn α g + 2 * max Cs 0 * α ^ 2 := by
      rw [hc₀def]
      have h1 : 2 * α * (10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g
          + max Cs 0 * α)
          = 20 * α * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g
            + 2 * max Cs 0 * α ^ 2 := by ring
      rw [h1]
      linarith [hterm]
    -- final arithmetic
    have hX2 : Work.FTS.Nonlin.Xn α g ^ 2 = Work.Spaces.HkSq α 4 g := hXsq
    have h1 : 3 * Real.sqrt 2 ≤ 5 := by
      have h2 : Real.sqrt 2 ≤ 5 / 3 := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    have h2 : 40 * Real.sqrt π ≤ 80 := by
      have h3 : Real.sqrt π ≤ 2 := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by linarith [Real.pi_lt_four]⟩
      linarith
    have h3 : α ^ 3 ≤ α ^ 2 := by nlinarith [hα1, hα.le]
    have h4 : α ≤ Real.sqrt α := (alpha_le_sqrt_alpha hα hα1).1
    have h5 : α ^ 2 ≤ α ^ (-(3 / 2 : ℝ)) := sq_le_rpow_neg_three_halves hα hα1
    have h6 : α ^ 2 * Work.FTS.Nonlin.Xn α g
        ≤ α ^ 2 + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
      sq_mul_le_self_add hα hα1 hX
    have h7 : 0 ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have h8 : 0 ≤ Work.FTS.Nonlin.Xn α g ^ 2 := sq_nonneg _
    have h9 : 0 ≤ α ^ 2 := sq_nonneg α
    have h10 : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g := mul_nonneg (Real.sqrt_nonneg _) hX
    have h11 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := mul_nonneg h7 h8
    have hP0 : 0 ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
        + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := by linarith [h9, h10, h11]
    have h12 : 1 ≤ α ^ (-(3 / 2 : ℝ)) := by
      have h13 : α ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
      have h14 : α ^ (-(3 / 2 : ℝ)) = (α ^ (3 / 2 : ℝ))⁻¹ := by
        rw [show (-(3 / 2 : ℝ)) = -(3 / 2) by ring, Real.rpow_neg hα.le]
      rw [h14]
      exact (one_le_inv₀ (Real.rpow_pos_of_pos hα _)).mpr h13
    have hfin : 3 * Real.sqrt 2 * c₀
          * (Work.FTS.Nonlin.Xn α g + 40 * Real.sqrt π * α)
        ≤ (3000000 * (max Ce 0 + max Cs 0) + 1)
            * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
              + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
      have hmc : 0 ≤ max Ce 0 := le_max_right _ _
      have hms : 0 ≤ max Cs 0 := le_max_right _ _
      have hL1 : 0 ≤ 80 * max Ce 0 * Work.FTS.Nonlin.Xn α g + 2 * max Cs 0 * α ^ 2 := by
        have ha : (0 : ℝ) ≤ 80 * max Ce 0 * Work.FTS.Nonlin.Xn α g :=
          mul_nonneg (mul_nonneg (by norm_num) hmc) hX
        have hb : (0 : ℝ) ≤ 2 * max Cs 0 * α ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hms) h9
        linarith
      have hL2 : 0 ≤ Work.FTS.Nonlin.Xn α g + 80 * α := by linarith [hα.le]
      have hstep1 : 3 * Real.sqrt 2 * c₀ * (Work.FTS.Nonlin.Xn α g + 40 * Real.sqrt π * α)
          ≤ 5 * c₀ * (Work.FTS.Nonlin.Xn α g + 80 * α) := by
        have hb : Work.FTS.Nonlin.Xn α g + 40 * Real.sqrt π * α
            ≤ Work.FTS.Nonlin.Xn α g + 80 * α := by
          have hb' : 40 * Real.sqrt π * α ≤ 80 * α := mul_le_mul_of_nonneg_right h2 hα.le
          linarith
        have hbase : 0 ≤ Work.FTS.Nonlin.Xn α g + 40 * Real.sqrt π * α := by
          have := mul_nonneg (Real.sqrt_nonneg π) hα.le
          linarith
        have hL : 3 * Real.sqrt 2 * c₀ ≤ 5 * c₀ := mul_le_mul_of_nonneg_right h1 hc₀0
        calc 3 * Real.sqrt 2 * c₀ * (Work.FTS.Nonlin.Xn α g + 40 * Real.sqrt π * α)
            ≤ 5 * c₀ * (Work.FTS.Nonlin.Xn α g + 40 * Real.sqrt π * α) :=
              mul_le_mul_of_nonneg_right hL hbase
          _ ≤ 5 * c₀ * (Work.FTS.Nonlin.Xn α g + 80 * α) :=
              mul_le_mul_of_nonneg_left hb (by linarith [hc₀0])
      have hstep2 : 5 * c₀ * (Work.FTS.Nonlin.Xn α g + 80 * α)
          ≤ 5 * (80 * max Ce 0 * Work.FTS.Nonlin.Xn α g + 2 * max Cs 0 * α ^ 2)
              * (Work.FTS.Nonlin.Xn α g + 80 * α) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc₀le (by norm_num)) hL2
      have k1 : 400 * max Ce 0 * Work.FTS.Nonlin.Xn α g ^ 2
          ≤ 1000000 * (max Ce 0 + max Cs 0)
              * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
        have h1a : Work.FTS.Nonlin.Xn α g ^ 2
            ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := by nlinarith [h12, h8]
        have hcoef : 400 * max Ce 0 ≤ 1000000 * (max Ce 0 + max Cs 0) := by linarith [hmc, hms]
        calc 400 * max Ce 0 * Work.FTS.Nonlin.Xn α g ^ 2
            ≤ 400 * max Ce 0 * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) :=
              mul_le_mul_of_nonneg_left h1a (by linarith [hmc])
          _ ≤ 1000000 * (max Ce 0 + max Cs 0)
                * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) :=
              mul_le_mul_of_nonneg_right hcoef h11
      have k2 : 32000 * max Ce 0 * α * Work.FTS.Nonlin.Xn α g
          ≤ 1000000 * (max Ce 0 + max Cs 0) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) := by
        have h2a : α * Work.FTS.Nonlin.Xn α g ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
          mul_le_mul_of_nonneg_right h4 hX
        have hcoef : 32000 * max Ce 0 ≤ 1000000 * (max Ce 0 + max Cs 0) := by linarith [hmc, hms]
        calc 32000 * max Ce 0 * α * Work.FTS.Nonlin.Xn α g
            = 32000 * max Ce 0 * (α * Work.FTS.Nonlin.Xn α g) := by ring
          _ ≤ 32000 * max Ce 0 * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) :=
              mul_le_mul_of_nonneg_left h2a (by linarith [hmc])
          _ ≤ 1000000 * (max Ce 0 + max Cs 0) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) :=
              mul_le_mul_of_nonneg_right hcoef h10
      have k3 : 10 * max Cs 0 * α ^ 2 * Work.FTS.Nonlin.Xn α g
          ≤ 1000000 * (max Ce 0 + max Cs 0)
              * (α ^ 2 + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
        have h3a : 10 * max Cs 0 * (α ^ 2 * Work.FTS.Nonlin.Xn α g)
            ≤ 10 * max Cs 0 * (α ^ 2 + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) :=
          mul_le_mul_of_nonneg_left h6 (by linarith [hms])
        have hcoef : 10 * max Cs 0 ≤ 1000000 * (max Ce 0 + max Cs 0) := by linarith [hmc, hms]
        calc 10 * max Cs 0 * α ^ 2 * Work.FTS.Nonlin.Xn α g
            = 10 * max Cs 0 * (α ^ 2 * Work.FTS.Nonlin.Xn α g) := by ring
          _ ≤ 10 * max Cs 0 * (α ^ 2 + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := h3a
          _ ≤ 1000000 * (max Ce 0 + max Cs 0)
                * (α ^ 2 + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) :=
              mul_le_mul_of_nonneg_right hcoef (by linarith [h9, h11])
      have k4 : 800 * max Cs 0 * α ^ 3
          ≤ 1000000 * (max Ce 0 + max Cs 0) * α ^ 2 := by
        have h4a : 800 * max Cs 0 * α ^ 3 ≤ 800 * max Cs 0 * α ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (by linarith [hms])
        have hcoef : 800 * max Cs 0 ≤ 1000000 * (max Ce 0 + max Cs 0) := by linarith [hmc, hms]
        calc 800 * max Cs 0 * α ^ 3 ≤ 800 * max Cs 0 * α ^ 2 := h4a
          _ ≤ 1000000 * (max Ce 0 + max Cs 0) * α ^ 2 :=
              mul_le_mul_of_nonneg_right hcoef h9
      have hexp : 5 * (80 * max Ce 0 * Work.FTS.Nonlin.Xn α g + 2 * max Cs 0 * α ^ 2)
            * (Work.FTS.Nonlin.Xn α g + 80 * α)
          = 400 * max Ce 0 * Work.FTS.Nonlin.Xn α g ^ 2
            + 32000 * max Ce 0 * α * Work.FTS.Nonlin.Xn α g
            + 10 * max Cs 0 * α ^ 2 * Work.FTS.Nonlin.Xn α g
            + 800 * max Cs 0 * α ^ 3 := by ring
      rw [hexp] at hstep2
      refine hstep1.trans (hstep2.trans ?_)
      nlinarith [k1, k2, k3, k4, hmc, hms, hX, hα.le, hα1, h7, h8, h9, h10, h11, hP0]
    refine hres.trans ?_
    have hstep : Real.sqrt (∫ s in Set.Ioi (0 : ℝ),
          (3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s)) ^ 2)
        * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), (1 / (1 + s)) ^ 2)
        ≤ 3 * Real.sqrt 2 * c₀ * (Work.FTS.Nonlin.Xn α g + 40 * Real.sqrt π * α) := by
      have h1 : Real.sqrt (∫ s in Set.Ioi (0 : ℝ),
            (3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s)) ^ 2)
          ≤ 3 * c₀ * Real.sqrt (Work.Spaces.HkSq α 4 g + 1600 * π * α ^ 2) := by
        refine (Real.sqrt_le_sqrt hA2le).trans (le_of_eq ?_)
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 9 * c₀ ^ 2),
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9), Real.sqrt_sq hc₀0]
        norm_num
      have h2 : Real.sqrt (∫ s in Set.Ioi (0 : ℝ), (1 / (1 + s)) ^ 2) ≤ Real.sqrt 2 :=
        Real.sqrt_le_sqrt hB2le
      calc Real.sqrt (∫ s in Set.Ioi (0 : ℝ),
              (3 * c₀ * Real.sqrt (Work.Spaces.w s * PhiF α g s)) ^ 2)
            * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), (1 / (1 + s)) ^ 2)
          ≤ (3 * c₀ * Real.sqrt (Work.Spaces.HkSq α 4 g + 1600 * π * α ^ 2)) * Real.sqrt 2 :=
            mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
        _ ≤ (3 * c₀ * (Work.FTS.Nonlin.Xn α g + 40 * Real.sqrt π * α)) * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsqrt_le (by linarith [hc₀0])) (Real.sqrt_nonneg _)
        _ = 3 * Real.sqrt 2 * c₀ * (Work.FTS.Nonlin.Xn α g + 40 * Real.sqrt π * α) := by ring
    exact hstep.trans hfin

end

end Work.FTS.Nonlinear.Pieces.Rl1
