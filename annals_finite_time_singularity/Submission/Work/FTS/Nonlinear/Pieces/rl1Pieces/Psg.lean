import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.starPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gSlots
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FKgFacts
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.LintEngine
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.StarUBound
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.H2.InvOneAddSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-!
# `Psg` — the five `sg`-rows of `N` in the `rl¹`-norm

The target is `Work.FTS.Nonlinear.Pieces.rl1Pieces.Psg`: there is `K > 0` such that for every
admissible datum the five `sg`-pieces of `N` obey

  `∫⁻_r r⁻¹ (∫⁻_θ |K θ · Nᵢ^{sg}(r,θ)|) ≤ ofReal (K · α^{1/2} · |g|_{ℋ⁴})`,   `i = 1..5`.

The five pieces are

  `N₁^{sg} = 2ℛ(Φ̃_*)·g`,  `N₂^{sg} = -2𝒰(Φ̃_*)·∂_θg`,  `N₃^{sg} = -2α𝒱(Φ̃_*)·D_zg`,
  `N₄^{sg} = -(1/2)FK(F_*)·D_θg`,  `N₅^{sg} = -sin²θ·FK(F_*)·g`,

so the coefficient factors (`ℛ(Φ̃_*)`, `𝒰(Φ̃_*)`, `𝒱(Φ̃_*)`, `FK(F_*)`) are *bounded pointwise*
by `C·α` (`StarPkg`/`starPt`/`StarUBound`, `FK_Fstar`) while the second factor is `g` or one of
its three first `D`-derivatives, which is *not* bounded pointwise without losing a power of `α`.
Hence the estimate is done with two Cauchy–Schwarz steps:

* angular: `∫⁻_θ |K θ·A·B| ≤ ofReal C √(π/2) · (∫⁻_θ B²)^{1/2}` (`inner_le`, using only the
  pointwise bound `|K θ A| ≤ C` and the a.e.-measurability of the `B`-slot);
* radial: `∫⁻_r r⁻¹ (∫⁻_θ B²)^{1/2} ≤ (∫⁻_r w(r)·∫⁻_θ B²)^{1/2}` (`outer_le`, the weight
  identity `r⁻¹ = √(w r)/(1+r)` and `∫_r (1+r)^{-2} = 1`);

and the surviving weighted energy is bounded by the `ℋ⁴`-norm of `g`: `w·B² ≤ HkIntegrand`
pointwise (`slot_g`, `slot_dth`, `slot_dz`), whence
`∫⁻_r w(r)·∫⁻_θ B² ≤ ∫⁻_r ∫⁻_θ HkIntegrand α 4 g = |g|_{ℋ⁴}²` (`hkSq_lintegral`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace PsgAux

/-! ## 1. Almost-everywhere statements on the angular interval -/

/-- An almost-everywhere statement on `Iθ = [0,π/2]` follows from the corresponding statement
on the open interval `(0,π/2)`. -/
theorem ae_Iθ_of_forall_Ioo {p : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), p θ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), p θ := by
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)).symm
  rw [hmeas]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h

/-! ## 2. Elementary arithmetic -/

/-- `α ≤ √α` for `0 < α ≤ 1`. -/
theorem alpha_le_sqrt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : α ≤ Real.sqrt α := by
  have h : α ^ 2 ≤ α := by nlinarith
  calc α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα.le).symm
    _ ≤ Real.sqrt α := Real.sqrt_le_sqrt h

/-- `α² ≤ √α` for `0 < α ≤ 1`. -/
theorem alpha_sq_le_sqrt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : α ^ 2 ≤ Real.sqrt α :=
  le_trans (by nlinarith) (alpha_le_sqrt hα hα1)

/-! ## 3. The pointwise slot comparisons -/

/-- `1 ≤ w z` for `z > 0`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [sq_nonneg z]

/-- `0 < w z` for `z > 0`. -/
theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

/-- For `0 < y ≤ 1` and `0 ≤ r` one has `1 ≤ y ^ (-r)`. -/
theorem one_le_rpow_neg {y r : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hr : 0 ≤ r) :
    1 ≤ y ^ (-r) := by
  rw [Real.rpow_neg hy.le, one_le_inv₀ (Real.rpow_pos_of_pos hy r)]
  exact Real.rpow_le_one hy.le hy1 hr

/-- `sin(2θ) > 0` on the open angular interval. -/
theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The squared angular weight of the pure `D_z` slots: `(w/sin(2θ)^{η/2})² = w²·sin(2θ)^{-η}`. -/
theorem w_div_sin_two_sq {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have h2 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) 2,
      ← Real.rpow_mul hs.le (Work.Spaces.eta / 2) ((2 : ℕ) : ℝ)]
    norm_num
  rw [div_pow, h2, div_eq_mul_inv, Real.rpow_neg hs.le]

/-- The squared mixed weight: `(Wt)² = w²·sin(2θ)^{-γ}`. -/
theorem Wt_sq' {α z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have h2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2,
      ← Real.rpow_mul hs.le (-(Work.Spaces.gam α / 2)) ((2 : ℕ) : ℝ)]
    ring_nf
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, h2]

/-- The weighted square of a `D_z`-slot dominates `w z·a²` on the open quadrant. -/
theorem w_mul_sq_le_rad {z θ a : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.w z * a ^ 2
      ≤ (a * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hw1 : 1 ≤ Work.Spaces.w z := one_le_w hz
  have hw0 : 0 ≤ Work.Spaces.w z := le_trans zero_le_one hw1
  have hse : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    one_le_rpow_neg (sin_two_pos hθ) (Real.sin_le_one _) Work.Spaces.eta_pos.le
  have hprod : 1 ≤ Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have h := mul_le_mul hw1 hse zero_le_one hw0
    simpa using h
  calc Work.Spaces.w z * a ^ 2 = a ^ 2 * Work.Spaces.w z * 1 := by ring
    _ ≤ a ^ 2 * Work.Spaces.w z * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg a) hw0)
    _ = (a * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_pow, w_div_sin_two_sq hθ]
        ring

/-- The weighted square of a mixed slot dominates `w z·a²` on the open quadrant. -/
theorem w_mul_sq_le_mixed {α z θ a : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Work.Spaces.w z * a ^ 2 ≤ (a * Work.Spaces.Wt α z θ) ^ 2 := by
  have hw1 : 1 ≤ Work.Spaces.w z := one_le_w hz
  have hw0 : 0 ≤ Work.Spaces.w z := le_trans zero_le_one hw1
  have hsg : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    one_le_rpow_neg (sin_two_pos hθ) (Real.sin_le_one _) (by
      have := Work.Spaces.gam_pos hα
      linarith)
  have hprod : 1 ≤ Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    have h := mul_le_mul hw1 hsg zero_le_one hw0
    simpa using h
  calc Work.Spaces.w z * a ^ 2 = a ^ 2 * Work.Spaces.w z * 1 := by ring
    _ ≤ a ^ 2 * Work.Spaces.w z * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg a) hw0)
    _ = (a * Work.Spaces.Wt α z θ) ^ 2 := by
        rw [mul_pow, Wt_sq' hθ]
        ring

/-- `w z·g(z,θ)² ≤ HkIntegrand α 4 g z θ` on the open quadrant. -/
theorem slot_g {α z θ : ℝ} (hα : 0 < α) (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (g : ℝ → ℝ → ℝ) :
    Work.Spaces.w z * (g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
  le_trans (w_mul_sq_le_rad (a := g z θ) hz hθ)
    (Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 0 (by norm_num))

/-- `w z·(D_θg(z,θ))² ≤ HkIntegrand α 4 g z θ` on the open quadrant. -/
theorem slot_dth {α z θ : ℝ} (hα : 0 < α) (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (g : ℝ → ℝ → ℝ) :
    Work.Spaces.w z * (Work.Spaces.Dth g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
  le_trans (w_mul_sq_le_mixed (a := Work.Spaces.Dth g z θ) hα hz hθ)
    (Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 0 (by norm_num) (by norm_num))

/-- `w z·(D_zg(z,θ))² ≤ HkIntegrand α 4 g z θ` on the open quadrant. -/
theorem slot_dz {α z θ : ℝ} (hα : 0 < α) (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (g : ℝ → ℝ → ℝ) :
    Work.Spaces.w z * (Work.Spaces.Dz g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
  le_trans (w_mul_sq_le_rad (a := Work.Spaces.Dz g z θ) hz hθ)
    (Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 1 (by norm_num))

/-! ## 4. Continuity on the open quadrant -/

/-- A `SmoothQuad` function is continuous on the open quadrant `(0,∞) × (0,π/2)`. -/
theorem contOn_of_smoothQuad {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have h : Work.FTS.LocData.SmoothQuad f := hf
  rw [Work.FTS.LocData.SmoothQuad] at h
  have hsub : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2))
      ⊆ (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := by
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := hp.1
    have hp2 : p.2 ∈ Set.Ioo (0 : ℝ) (π / 2) := hp.2
    exact ⟨by show (-1 : ℝ) < p.1; linarith, hp2⟩
  exact (h.mono hsub).continuousOn

/-! ## 5. Measurability and the two Cauchy–Schwarz engines -/

/-- The squared `θ`-slice of a function continuous on the open quadrant is a.e.-measurable. -/
theorem slice_sq_aemeasurable {B : ℝ → ℝ → ℝ}
    (hB : ContinuousOn (Function.uncurry B) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) {z : ℝ}
    (hz : 0 < z) :
    AEMeasurable (fun θ => ENNReal.ofReal ((B z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have h1 : MeasureTheory.AEStronglyMeasurable (fun θ => B z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry B) hB hz
  have h2 : AEMeasurable (fun θ => B z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (aestronglyMeasurable_iff_aemeasurable).mp h1
  have hg : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ 2)) := by fun_prop
  simpa only [Function.comp_def] using hg.comp_aemeasurable h2

/-- The parametrised `θ`-integral of the squared slice is measurable in `r`. -/
theorem slot_aemeasurable {B : ℝ → ℝ → ℝ}
    (hB : ContinuousOn (Function.uncurry B) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    AEMeasurable (fun r => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have h1 : MeasureTheory.AEStronglyMeasurable (Function.uncurry B)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry B) hB
  have hz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm
  have hmeas_eq : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set hz
  rw [hmeas_eq] at h1
  have h2 : AEMeasurable (Function.uncurry B)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (aestronglyMeasurable_iff_aemeasurable).mp h1
  have hg : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ 2)) := by fun_prop
  have h3 : AEMeasurable (Function.uncurry (fun r θ => ENNReal.ofReal ((B r θ) ^ 2)))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    exact hg.comp_aemeasurable h2
  exact h3.lintegral_prod_right

/-- The `z`-integral of the `ℋ⁴`-integrand against `r⁻¹` is `ofReal` of the `ℋ⁴`-square. -/
theorem hkSq_lintegral {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k g) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g r θ)) = ENNReal.ofReal (Work.Spaces.HkSq α k g) := by
  have hint : MeasureTheory.IntegrableOn
      (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g r θ) (Set.Ioi (0 : ℝ)) :=
    hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hkey := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun r =>
      integral_nonneg fun _ => Work.Spaces.HkIntegrand_nonneg α k g r _)
  rw [← hkey]
  congr 1
  rw [MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))]
  rfl

/-- **The angular Cauchy–Schwarz step.**  If `|K θ·A(z,θ)|` is bounded by the constant `c`
a.e. on `Iθ`, then the angular integral of `|K θ·A·B|` is bounded by
`ofReal (c √(π/2)) · (∫⁻_θ B²)^{1/2}`. -/
theorem inner_le {A B : ℝ → ℝ → ℝ} {c z : ℝ} (hc : 0 ≤ c)
    (hBmeas : AEMeasurable (fun θ => ENNReal.ofReal ((B z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hA : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * A z θ| ≤ c) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * A z θ * B z θ|)
      ≤ ENNReal.ofReal (c * Real.sqrt (Real.pi / 2))
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B z θ) ^ 2)) ^ (1 / 2 : ℝ) := by
  -- the pointwise bound `|K·A·B| ≤ c·|B|`
  have h1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * A z θ * B z θ|)
      ≤ ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal c * ENNReal.ofReal |B z θ| := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [hA] with θ hθ
    have h2 : |Work.Spaces.K θ * A z θ * B z θ| ≤ c * |B z θ| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hθ (abs_nonneg _)
    calc ENNReal.ofReal |Work.Spaces.K θ * A z θ * B z θ|
        ≤ ENNReal.ofReal (c * |B z θ|) := ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal c * ENNReal.ofReal |B z θ| := ENNReal.ofReal_mul hc
  -- Cauchy–Schwarz for `∫_θ |B|`
  have hBsqrt : AEMeasurable (fun θ => (ENNReal.ofReal ((B z θ) ^ 2)) ^ (1 / 2 : ℝ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hBmeas.pow_const (1 / 2 : ℝ)
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    hpq
    (aemeasurable_const : AEMeasurable (fun _ : ℝ => (1 : ENNReal))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) hBsqrt
  have hBabs : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B z θ|)
      = ∫⁻ θ in Work.Spaces.Iθ, (ENNReal.ofReal ((B z θ) ^ 2)) ^ (1 / 2 : ℝ) := by
    refine MeasureTheory.lintegral_congr fun θ => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]
  have hone : (∫⁻ θ in Work.Spaces.Iθ, ((1 : ENNReal) ^ (2 : ℝ)))
      = ENNReal.ofReal (Real.pi / 2) := by
    rw [ENNReal.one_rpow, MeasureTheory.setLIntegral_const, one_mul, Work.Spaces.Iθ,
      Real.volume_Icc, show (π / 2 - 0 : ℝ) = π / 2 from by ring]
  have hsq : (∫⁻ θ in Work.Spaces.Iθ,
        ((ENNReal.ofReal ((B z θ) ^ 2)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ))
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B z θ) ^ 2) := by
    refine MeasureTheory.lintegral_congr fun θ => ?_
    rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  have h3 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B z θ|)
      ≤ ENNReal.ofReal (Real.sqrt (Real.pi / 2))
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B z θ) ^ 2)) ^ (1 / 2 : ℝ) := by
    have hcs' : (∫⁻ θ in Work.Spaces.Iθ, (ENNReal.ofReal ((B z θ) ^ 2)) ^ (1 / 2 : ℝ))
        ≤ (∫⁻ θ in Work.Spaces.Iθ, ((1 : ENNReal) ^ (2 : ℝ))) ^ (1 / 2 : ℝ)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ((ENNReal.ofReal ((B z θ) ^ 2)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      simpa only [Pi.mul_apply, one_mul] using hcs
    rw [hBabs]
    refine hcs'.trans ?_
    rw [hone, hsq]
    refine mul_le_mul_of_nonneg_right (le_of_eq ?_) bot_le
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.sqrt_eq_rpow]
  -- assemble
  have h2 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal c * ENNReal.ofReal |B z θ|)
      = ENNReal.ofReal c * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B z θ|) :=
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [h2] at h1
  refine h1.trans ?_
  calc ENNReal.ofReal c * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B z θ|)
      ≤ ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt (Real.pi / 2))
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B z θ) ^ 2)) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 bot_le
    _ = ENNReal.ofReal (c * Real.sqrt (Real.pi / 2))
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B z θ) ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc]

/-- `∫_r (1/(1+r))² = 1` on `(0,∞)`. -/
theorem integral_one_div_sq :
    (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2) = 1 := by
  have hval : (∫ r in Set.Ioi (0 : ℝ), (1 + r) ^ (-2 : ℝ)) = 1 := by
    have hd : ∀ x ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun t : ℝ => (t + 1) ^ (-1 : ℝ) / (-1)) ((x + 1) ^ (-2 : ℝ)) x := by
      intro x hx
      have hx1 : x + 1 ≠ 0 := by
        have : (0 : ℝ) ≤ x := hx
        linarith
      have h2 := (((hasDerivAt_id x).add_const (1 : ℝ)).rpow_const (p := (-1 : ℝ))
        (Or.inl hx1)).div_const (-1)
      simp only [id_eq] at h2
      have hnum : (1 * (-1 : ℝ) * (x + 1) ^ ((-1 : ℝ) - 1)) / (-1) = (x + 1) ^ (-2 : ℝ) := by
        rw [show ((-1 : ℝ) - 1) = -2 by norm_num]
        field_simp
      rwa [hnum] at h2
    have hInt : MeasureTheory.IntegrableOn (fun x : ℝ => (x + 1) ^ (-2 : ℝ)) (Set.Ioi (0 : ℝ)) :=
      integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := 0) (m := 1) (by norm_num) (by norm_num)
    have ht : Filter.Tendsto (fun t : ℝ => (t + 1) ^ (-1 : ℝ) / (-1)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun t : ℝ => (t + 1) ^ (-1 : ℝ)) Filter.atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (y := 1) (by norm_num)).comp
          (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
      simpa using h1.div_const (-1)
    have hmain : (∫ x in Set.Ioi (0 : ℝ), (x + 1) ^ (-2 : ℝ)) = 1 := by
      have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
        (a := (0 : ℝ)) (m := (0 : ℝ)) hd hInt ht
      rw [h] at *
      norm_num
    have hmain' : (∫ x in Set.Ioi (0 : ℝ), (1 + x) ^ (-2 : ℝ)) = 1 := by
      rw [show (∫ x in Set.Ioi (0 : ℝ), (1 + x) ^ (-2 : ℝ))
          = ∫ x in Set.Ioi (0 : ℝ), (x + 1) ^ (-2 : ℝ) from
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          (fun x _ => by rw [add_comm])]
      exact hmain
    exact hmain'
  calc (∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2)
      = ∫ r in Set.Ioi (0 : ℝ), (1 + r) ^ (-2 : ℝ) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
        have hx0 : 0 < x := hx
        have h1 : (1 : ℝ) / (1 + x) = (1 + x) ^ (-1 : ℝ) := by
          rw [one_div, Real.rpow_neg_one]
        rw [h1, ← Real.rpow_natCast ((1 + x) ^ (-1 : ℝ)) 2,
          ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ 1 + x) (-1 : ℝ) ((2 : ℕ) : ℝ)]
        norm_num
    _ = 1 := hval

/-- **The radial Cauchy–Schwarz step.**  `∫⁻_r r⁻¹ Φ(r)^{1/2}` is bounded by
`(∫⁻_r w(r)·Φ(r))^{1/2}` (the weight identity `r⁻¹ = √(w r)/(1+r)` and `∫_r (1+r)^{-2} = 1`). -/
theorem outer_le {Φ : ℝ → ENNReal}
    (hΦmeas : AEMeasurable Φ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (Φ r) ^ (1 / 2 : ℝ))
      ≤ (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Work.Spaces.w r) * Φ r) ^ (1 / 2 : ℝ) := by
  have hcongr : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (Φ r) ^ (1 / 2 : ℝ))
      = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (1 / (1 + r))
          * (ENNReal.ofReal (Work.Spaces.w r) * Φ r) ^ (1 / 2 : ℝ) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hw0 : 0 < Work.Spaces.w r := by
      rw [Work.Spaces.w]
      positivity
    have hsq : Real.sqrt (Work.Spaces.w r) = (1 + r) / r := by
      rw [Work.Spaces.w, show (1 + r) ^ 2 / r ^ 2 = ((1 + r) / r) ^ 2 from by ring,
        Real.sqrt_sq (by positivity)]
    have hrw : r⁻¹ = 1 / (1 + r) * Real.sqrt (Work.Spaces.w r) := by
      rw [hsq]
      field_simp
    have hsplit : (ENNReal.ofReal (Work.Spaces.w r) * Φ r) ^ (1 / 2 : ℝ)
        = ENNReal.ofReal (Real.sqrt (Work.Spaces.w r)) * (Φ r) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (le_of_lt hw0) (by norm_num), Real.sqrt_eq_rpow]
    calc ENNReal.ofReal r⁻¹ * (Φ r) ^ (1 / 2 : ℝ)
        = ENNReal.ofReal (1 / (1 + r)) * ENNReal.ofReal (Real.sqrt (Work.Spaces.w r))
            * (Φ r) ^ (1 / 2 : ℝ) := by
          rw [hrw, ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (1 / (1 + r))
            * (ENNReal.ofReal (Real.sqrt (Work.Spaces.w r)) * (Φ r) ^ (1 / 2 : ℝ)) := by ring
      _ = ENNReal.ofReal (1 / (1 + r))
            * (ENNReal.ofReal (Work.Spaces.w r) * Φ r) ^ (1 / 2 : ℝ) := by rw [hsplit]
  rw [hcongr]
  have hf_meas : AEMeasurable (fun r => ENNReal.ofReal (1 / (1 + r)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (by fun_prop : Measurable (fun r : ℝ => ENNReal.ofReal (1 / (1 + r)))).aemeasurable
  have hg_meas : AEMeasurable
      (fun r => (ENNReal.ofReal (Work.Spaces.w r) * Φ r) ^ (1 / 2 : ℝ))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : AEMeasurable (fun r => ENNReal.ofReal (Work.Spaces.w r) * Φ r)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (ENNReal.measurable_ofReal.comp (by unfold Work.Spaces.w; fun_prop)).aemeasurable.mul
        hΦmeas
    exact h1.pow_const (1 / 2 : ℝ)
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    hpq hf_meas hg_meas
  have hA : (∫⁻ r in Set.Ioi (0 : ℝ), (ENNReal.ofReal (1 / (1 + r))) ^ (2 : ℝ)) = 1 := by
    have h1 : (∫⁻ r in Set.Ioi (0 : ℝ), (ENNReal.ofReal (1 / (1 + r))) ^ (2 : ℝ))
        = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal ((1 / (1 + r)) ^ 2) := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := hr
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two]
    rw [h1]
    have hint : MeasureTheory.IntegrableOn (fun r : ℝ => (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
      Work.FTS.H2.InvOneAddSq.1
    have hkey := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun r => by positivity)
    rw [← hkey, integral_one_div_sq, ENNReal.ofReal_one]
  have hB : (∫⁻ r in Set.Ioi (0 : ℝ),
        ((ENNReal.ofReal (Work.Spaces.w r) * Φ r) ^ (1 / 2 : ℝ)) ^ (2 : ℝ))
      = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Work.Spaces.w r) * Φ r := by
    refine MeasureTheory.lintegral_congr fun r => ?_
    rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (1 / (1 + r))
        * (ENNReal.ofReal (Work.Spaces.w r) * Φ r) ^ (1 / 2 : ℝ))
      ≤ (∫⁻ r in Set.Ioi (0 : ℝ), (ENNReal.ofReal (1 / (1 + r))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          * (∫⁻ r in Set.Ioi (0 : ℝ),
              ((ENNReal.ofReal (Work.Spaces.w r) * Φ r) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^
            (1 / 2 : ℝ) := hhold
    _ = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Work.Spaces.w r) * Φ r) ^ (1 / 2 : ℝ) := by
        rw [hA, hB, ENNReal.one_rpow, one_mul]

/-- **The `rl¹`-engine.**  A pointwise bound `|K θ·A(r,θ)| ≤ C` combined with the slot facts
`w(r)·B(r,θ)² ≤ HkIntegrand α 4 g` gives the `rl¹`-bound of the product `A·B`. -/
theorem rl1_slot_le {α C : ℝ} {A B g : ℝ → ℝ → ℝ}
    (hC : 0 ≤ C) (hmem : Work.Spaces.HkMem α 4 g)
    (hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * A r θ| ≤ C)
    (hBmeas : ∀ r, 0 < r → AEMeasurable (fun θ => ENNReal.ofReal ((B r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hΦmeas : AEMeasurable (fun r => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (B r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * A r θ * B r θ|))
      ≤ ENNReal.ofReal (C * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g) := by
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * A r θ * B r θ|)
        ≤ ENNReal.ofReal (C * Real.sqrt (Real.pi / 2))
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2)) ^ (1 / 2 : ℝ) :=
    fun r hr => inner_le hC (hBmeas r hr) (hA r hr)
  have hweight : (∫⁻ r in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Work.Spaces.w r)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2)))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 4 g) := by
    have hstep : (∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Work.Spaces.w r)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2)))
        ≤ ∫⁻ r in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := hr
      have hkey : (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 g r θ))
          = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (hmem.1 r (by simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith))
          (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g r θ)).symm
      calc ENNReal.ofReal (Work.Spaces.w r)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2))
          = ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.w r) * ENNReal.ofReal ((B r θ) ^ 2) :=
            (MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
        _ ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Work.Spaces.HkIntegrand α 4 g r θ) := by
            refine MeasureTheory.lintegral_mono_ae ?_
            filter_upwards [hBw r hr0] with θ hθ
            rw [← ENNReal.ofReal_mul (le_of_lt (w_pos hr0))]
            exact ENNReal.ofReal_le_ofReal hθ
        _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ) := hkey
    exact hstep.trans (le_of_eq (hkSq_lintegral hmem))
  have hX : (ENNReal.ofReal (Work.Spaces.HkSq α 4 g)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Work.FTS.Nonlin.Xn α g) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Work.Spaces.HkSq_nonneg α 4 g) (by norm_num)]
    congr 1
    simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, Real.sqrt_eq_rpow]
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * A r θ * B r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * (ENNReal.ofReal (C * Real.sqrt (Real.pi / 2))
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2)) ^ (1 / 2 : ℝ)) := by
        refine MeasureTheory.lintegral_mono_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
        exact mul_le_mul_of_nonneg_left (hinner r hr) bot_le
    _ = ENNReal.ofReal (C * Real.sqrt (Real.pi / 2))
          * (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2)) ^ (1 / 2 : ℝ)) := by
        rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine MeasureTheory.lintegral_congr fun r => ?_
        ring
    _ ≤ ENNReal.ofReal (C * Real.sqrt (Real.pi / 2))
          * (∫⁻ r in Set.Ioi (0 : ℝ),
              ENNReal.ofReal (Work.Spaces.w r)
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2))) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (outer_le hΦmeas) bot_le
    _ ≤ ENNReal.ofReal (C * Real.sqrt (Real.pi / 2))
          * (ENNReal.ofReal (Work.Spaces.HkSq α 4 g)) ^ (1 / 2 : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        exact ENNReal.rpow_le_rpow hweight (by norm_num)
    _ = ENNReal.ofReal (C * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g) := by
        rw [hX, ← ENNReal.ofReal_mul (by positivity)]

end PsgAux

/-! ## The pointwise bounds of the two `Φ̃_*`-coefficient factors -/

/-- The pointwise bound on `𝒰(Φ̃_*)`, with the explicit constant `4` (the existential constant
of `Work.FTS.Nonlinear.Pieces.Rl1.StarUBound` exposed). -/
theorem abs_Uop_PhiTs_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ 4 * max Cs 0 * α := by
  intro z hz θ hθ
  change |Work.Construction.Uop α
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ| ≤ 4 * max Cs 0 * α
  let Ψ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs
  obtain ⟨hR, hV, hdU⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs
  have hR' : ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Rop α Ψ z θ| ≤ max Cs 0 * α := hR
  have hV' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Vop Ψ z θ| ≤ max Cs 0 * α := hV
  have hdU' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pth (Work.Construction.Uop α Ψ) z θ| ≤ max Cs 0 * α := hdU
  have hvU : Work.Spaces.VanishTheta (Work.Construction.Uop α Ψ) := hs.vanishU
  have hMnn : 0 ≤ max Cs 0 := le_max_right Cs 0
  have hMα : 0 ≤ max Cs 0 * α := mul_nonneg hMnn hα.le
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hpi4Iθ : (π / 4) ∈ Work.Spaces.Iθ := ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hpi4Ioo : (π / 4) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hanchor : |Work.Construction.Uop α Ψ z (π / 4)| ≤ 2 * (max Cs 0 * α) := by
    rw [Work.FTS.Nonlinear.Pieces.Rl1.Uop_pi_div_four α Ψ z, abs_neg]
    have h1 := hR' z hz (π / 4) hpi4Iθ
    have h2 := hV' z hzI (π / 4) hpi4Iθ
    have htri : |Work.Construction.Rop α Ψ z (π / 4) - Work.Construction.Vop Ψ z (π / 4)|
        ≤ |Work.Construction.Rop α Ψ z (π / 4)| + |Work.Construction.Vop Ψ z (π / 4)| := by
      have h := abs_add_le (Work.Construction.Rop α Ψ z (π / 4))
        (-(Work.Construction.Vop Ψ z (π / 4)))
      rw [abs_neg] at h
      simpa only [sub_eq_add_neg] using h
    linarith
  rcases eq_or_ne θ 0 with hθ0 | hθ0
  · subst hθ0
    rw [hvU.1 z, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hMnn) hα.le
  rcases eq_or_ne θ (π / 2) with hθ2 | hθ2
  · subst hθ2
    rw [hvU.2 z, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hMnn) hα.le
  have hθint : θ ∈ Set.Ioo (0 : ℝ) (π / 2) :=
    ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hθ2⟩
  have hsq : Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α Ψ) := by
    show Work.FTS.LocData.SmoothQuad (Work.Construction.Uop α
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))
    exact Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_Uop
      (Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_PhiTs hα hα1 hs.smooth)
  have hslice : ∀ n : ℕ, ContDiffOn ℝ n (fun θ' => Work.Construction.Uop α Ψ z θ')
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    fun n => Work.FTS.Nonlinear.Pieces.Rl1.contDiffOn_thSlice_Uop (by linarith) hsq n
  have hK : ∀ ξ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |deriv (fun θ' => Work.Construction.Uop α Ψ z θ') ξ| ≤ max Cs 0 * α := by
    intro ξ hξ
    have hξI : ξ ∈ Work.Spaces.Iθ := ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
    have h := hdU' z hzI ξ hξI
    simpa only [Work.Spaces.pth] using h
  have hmvt := Work.FTS.EllipticEst.SgamBound.abs_sub_le_mul_abs_sub_of_deriv_bound
    (u := fun θ' => Work.Construction.Uop α Ψ z θ') hslice hθint hpi4Ioo hK
  have hdist : |θ - π / 4| ≤ π / 4 := by
    rw [abs_le]
    exact ⟨by linarith [hθint.1], by linarith [hθint.2]⟩
  have hb1 : |Work.Construction.Uop α Ψ z θ - Work.Construction.Uop α Ψ z (π / 4)|
      ≤ (max Cs 0 * α) * (π / 4) :=
    le_trans hmvt (mul_le_mul_of_nonneg_left hdist hMα)
  have htri : |Work.Construction.Uop α Ψ z θ|
      ≤ |Work.Construction.Uop α Ψ z θ - Work.Construction.Uop α Ψ z (π / 4)|
        + |Work.Construction.Uop α Ψ z (π / 4)| := by
    have h := abs_add_le (Work.Construction.Uop α Ψ z θ - Work.Construction.Uop α Ψ z (π / 4))
      (Work.Construction.Uop α Ψ z (π / 4))
    rwa [sub_add_cancel] at h
  have hpi : (π / 4 : ℝ) ≤ 2 := by linarith [Real.pi_lt_four]
  have hstep : (max Cs 0 * α) * (π / 4) ≤ (max Cs 0 * α) * 2 :=
    mul_le_mul_of_nonneg_left hpi hMα
  linarith [hb1, hanchor, htri, hstep]

/-- The angular moment of `F_*` is at most `α` on `z ≥ 0`. -/
theorem abs_FK_Fstar_le {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z) :
    |Work.Construction.FK (Work.Construction.Fstar α) z| ≤ α := by
  rw [Work.FTS.Nonlin.FK_Fstar hα hα1, abs_mul, abs_of_pos hα]
  have h2 : |2 * z / (1 + z) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (by linarith) (by positivity)), div_le_one (by positivity)]
    nlinarith [sq_nonneg (1 - z)]
  calc α * |2 * z / (1 + z) ^ 2| ≤ α * 1 := mul_le_mul_of_nonneg_left h2 hα.le
    _ = α := by ring

/-! ## The five rows -/

/-- Row `N₁^{sg}`: `2ℛ(Φ̃_*)·g`. -/
theorem row1sg {α Cs : ℝ} {g Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hgal : Work.FTS.Nonlin.GalClass α g) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ|))
      ≤ ENNReal.ofReal (6 * max Cs 0 * α * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α g) := by
  have hreg := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hcont : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    PsgAux.contOn_of_smoothQuad hreg.1
  obtain ⟨hR, -, -⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs
  have hCs0 : 0 ≤ max Cs 0 := le_max_right _ _
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) r θ|
        ≤ 6 * max Cs 0 * α := by
    intro r hr
    refine PsgAux.ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hb1 := Work.FTS.Nonlinear.Pieces.rl1Tools.abs_K_le_three θ
    have hb2 := hR r hr θ hθI
    calc |Work.Spaces.K θ * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ)|
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
    fun r hr => PsgAux.slice_sq_aemeasurable hcont hr
  have hΦmeas := PsgAux.slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
    fun r hr => PsgAux.ae_Iθ_of_forall_Ioo (fun θ hθ => PsgAux.slot_g hα hr hθ g)
  have hE := PsgAux.rl1_slot_le (α := α) (C := 6 * max Cs 0 * α)
    (A := fun z θ => 2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    (B := g) (g := g) (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le)
    hmem hA hBmeas hΦmeas hBw
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

/-- Row `N₂^{sg}`: `-2𝒰(Φ̃_*)·∂_θg`. -/
theorem row2sg {α Cs : ℝ} {g Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hgal : Work.FTS.Nonlin.GalClass α g) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ|))
      ≤ ENNReal.ofReal (12 * max Cs 0 * α * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α g) := by
  have hreg := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.Dth g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    PsgAux.contOn_of_smoothQuad
      (show Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth g) from
        Work.FTS.LocData.SmoothQuad.DthIter hreg.1 1)
  have hCs0 : 0 ≤ max Cs 0 := le_max_right _ _
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
            / Real.sin (2 * θ)) r θ| ≤ 12 * max Cs 0 * α := by
    intro r hr
    refine PsgAux.ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hs2 : Real.sin (2 * θ) ≠ 0 := ne_of_gt (PsgAux.sin_two_pos hθ)
    have hU := abs_Uop_PhiTs_le hα hα1 hs r hr θ hθI
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
      have hmm : |(3 / 2 : ℝ) * Real.cos θ
            * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ)|
          = 2 * ((3 / 2) * |Real.cos θ|)
            * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| := by
        rw [show (3 / 2 : ℝ) * Real.cos θ
              * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ)
            = (-3) * (Real.cos θ
              * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ) from by ring,
          abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_mul]
        ring
      exact hmm
    rw [habs]
    have h1 : (3 / 2) * |Real.cos θ| ≤ (3 / 2) * 1 :=
      mul_le_mul_of_nonneg_left hcos (by norm_num)
    calc 2 * ((3 / 2) * |Real.cos θ|)
          * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
        ≤ 2 * ((3 / 2) * 1) * (4 * max Cs 0 * α) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hU (abs_nonneg _) ?_
          positivity
      _ = 12 * max Cs 0 * α := by ring
  have hBmeas : ∀ r, 0 < r → AEMeasurable
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dth g r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => PsgAux.slice_sq_aemeasurable hcont hr
  have hΦmeas := PsgAux.slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (Work.Spaces.Dth g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
    fun r hr => PsgAux.ae_Iθ_of_forall_Ioo (fun θ hθ => PsgAux.slot_dth hα hr hθ g)
  have hE := PsgAux.rl1_slot_le (α := α) (C := 12 * max Cs 0 * α)
    (A := fun z θ => -2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
      / Real.sin (2 * θ))
    (B := Work.Spaces.Dth g) (g := g) (mul_nonneg (mul_nonneg (by norm_num) hCs0) hα.le)
    hmem hA hBmeas hΦmeas hBw
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ|
        = |Work.Spaces.K θ * (-2 * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ
              / Real.sin (2 * θ)) * Work.Spaces.Dth g r θ| := by
    intro r θ hθ
    have hs2 : Real.sin (2 * θ) ≠ 0 := ne_of_gt (PsgAux.sin_two_pos hθ)
    rw [Work.FTS.Nonlin.N2sg]
    congr 1
    simp only [Work.Spaces.Dth]
    field_simp
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  refine MeasureTheory.lintegral_congr_ae ?_
  filter_upwards [PsgAux.ae_Iθ_of_forall_Ioo
    (p := fun θ => θ ∈ Set.Ioo (0 : ℝ) (π / 2)) (fun θ hθ => hθ)] with θ hθ
  rw [hid r θ hθ]

/-- Row `N₃^{sg}`: `-2α𝒱(Φ̃_*)·D_zg`. -/
theorem row3sg {α Cs : ℝ} {g Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hgal : Work.FTS.Nonlin.GalClass α g) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ|))
      ≤ ENNReal.ofReal (6 * max Cs 0 * α ^ 2 * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α g) := by
  have hreg := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.Dz g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    PsgAux.contOn_of_smoothQuad
      (show Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz g) from
        Work.FTS.LocData.SmoothQuad.DzIter hreg.1 1)
  obtain ⟨-, hV, -⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs
  have hCs0 : 0 ≤ max Cs 0 := le_max_right _ _
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z θ =>
          -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) r θ|
        ≤ 6 * max Cs 0 * α ^ 2 := by
    intro r hr
    refine PsgAux.ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hb1 := Work.FTS.Nonlinear.Pieces.rl1Tools.abs_K_le_three θ
    have hb2 := hV r hr.le θ hθI
    calc |Work.Spaces.K θ * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)|
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
    fun r hr => PsgAux.slice_sq_aemeasurable hcont hr
  have hΦmeas := PsgAux.slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (Work.Spaces.Dz g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
    fun r hr => PsgAux.ae_Iθ_of_forall_Ioo (fun θ hθ => PsgAux.slot_dz hα hr hθ g)
  have hE := PsgAux.rl1_slot_le (α := α) (C := 6 * max Cs 0 * α ^ 2)
    (A := fun z θ => -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ)
    (B := Work.Spaces.Dz g) (g := g)
    (mul_nonneg (mul_nonneg (by norm_num) hCs0) (sq_nonneg α))
    hmem hA hBmeas hΦmeas hBw
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

/-- Row `N₄^{sg}`: `-(1/2)FK(F_*)·D_θg`. -/
theorem row4sg {α Cs : ℝ} {g Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hgal : Work.FTS.Nonlin.GalClass α g) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ|))
      ≤ ENNReal.ofReal (3 / 2 * α * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α g) := by
  have hreg := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hcont : ContinuousOn (Function.uncurry (Work.Spaces.Dth g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    PsgAux.contOn_of_smoothQuad
      (show Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth g) from
        Work.FTS.LocData.SmoothQuad.DthIter hreg.1 1)
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun z _ =>
          -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z) r θ|
        ≤ 3 / 2 * α := by
    intro r hr
    refine PsgAux.ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hb1 := Work.FTS.Nonlinear.Pieces.rl1Tools.abs_K_le_three θ
    have hb2 := abs_FK_Fstar_le hα hα1 hr.le
    calc |Work.Spaces.K θ
          * (-(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) r)|
        = (1 / 2) * |Work.Spaces.K θ| * |Work.Construction.FK (Work.Construction.Fstar α) r| := by
          rw [show Work.Spaces.K θ
                * (-(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) r)
              = (-(1 / 2)) * (Work.Spaces.K θ
                * Work.Construction.FK (Work.Construction.Fstar α) r) from by ring,
            abs_mul, abs_neg,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2), abs_mul]
          ring
      _ ≤ (1 / 2) * 3 * α := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hb1 (by norm_num)) hb2
            (abs_nonneg _) (by norm_num)
      _ = 3 / 2 * α := by ring
  have hBmeas : ∀ r, 0 < r → AEMeasurable
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dth g r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => PsgAux.slice_sq_aemeasurable hcont hr
  have hΦmeas := PsgAux.slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (Work.Spaces.Dth g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
    fun r hr => PsgAux.ae_Iθ_of_forall_Ioo (fun θ hθ => PsgAux.slot_dth hα hr hθ g)
  have hE := PsgAux.rl1_slot_le (α := α) (C := 3 / 2 * α)
    (A := fun z _ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z)
    (B := Work.Spaces.Dth g) (g := g) (mul_nonneg (by norm_num) hα.le)
    hmem hA hBmeas hΦmeas hBw
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ|
      = |Work.Spaces.K θ
          * (-(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) r)
          * Work.Spaces.Dth g r θ| := by
    intro r θ
    rw [Work.FTS.Nonlin.N4sg]
    congr 1
    ring
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  exact MeasureTheory.lintegral_congr fun θ => by rw [hid r θ]

/-- Row `N₅^{sg}`: `-sin²θ·FK(F_*)·g`. -/
theorem row5sg {α Cs : ℝ} {g Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (hgal : Work.FTS.Nonlin.GalClass α g) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ|))
      ≤ ENNReal.ofReal (3 * α * Real.sqrt (Real.pi / 2)
          * Work.FTS.Nonlin.Xn α g) := by
  have hreg := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hcont : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    PsgAux.contOn_of_smoothQuad hreg.1
  have hA : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * (fun _ θ =>
          -(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) r) r θ|
        ≤ 3 * α := by
    intro r hr
    refine PsgAux.ae_Iθ_of_forall_Ioo (fun θ hθ => ?_)
    have hb1 := Work.FTS.Nonlinear.Pieces.rl1Tools.abs_K_le_three θ
    have hb2 := abs_FK_Fstar_le hα hα1 hr.le
    have hs2 : |(Real.sin θ) ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
    calc |Work.Spaces.K θ * (-(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) r)|
        = |Work.Spaces.K θ| * |(Real.sin θ) ^ 2|
            * |Work.Construction.FK (Work.Construction.Fstar α) r| := by
          rw [abs_mul, abs_mul, abs_neg]
          ring
      _ ≤ 3 * 1 * α := by
          refine mul_le_mul (mul_le_mul hb1 hs2 (abs_nonneg _) (by norm_num)) hb2
            (abs_nonneg _) (by norm_num)
      _ = 3 * α := by ring
  have hBmeas : ∀ r, 0 < r → AEMeasurable (fun θ => ENNReal.ofReal ((g r θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => PsgAux.slice_sq_aemeasurable hcont hr
  have hΦmeas := PsgAux.slot_aemeasurable hcont
  have hBw : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w r * (g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ :=
    fun r hr => PsgAux.ae_Iθ_of_forall_Ioo (fun θ hθ => PsgAux.slot_g hα hr hθ g)
  have hE := PsgAux.rl1_slot_le (α := α) (C := 3 * α)
    (A := fun _ θ => -(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) _)
    (B := g) (g := g) (mul_nonneg (by norm_num) hα.le)
    hmem hA hBmeas hΦmeas hBw
  refine le_trans (le_of_eq ?_) hE
  have hid : ∀ r θ, |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ|
      = |Work.Spaces.K θ * (-(Real.sin θ) ^ 2
          * Work.Construction.FK (Work.Construction.Fstar α) r) * g r θ| := by
    intro r θ
    rw [Work.FTS.Nonlin.N5sg]
    congr 1
    ring
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  exact MeasureTheory.lintegral_congr fun θ => by rw [hid r θ]

theorem Psg {α₂ Ci Ce Cs : ℝ} :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.N4Norm Ci α₂ →
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg →
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ|))
        ≤ ENNReal.ofReal (K * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ|))
        ≤ ENNReal.ofReal (K * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ|))
        ≤ ENNReal.ofReal (K * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ|))
        ≤ ENNReal.ofReal (K * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ|))
        ≤ ENNReal.ofReal (K * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  refine ⟨1 + 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + 1), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ max Cs 0 + 1 := by have := le_max_right Cs 0; linarith
    have h2 : (0 : ℝ) ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
    nlinarith
  · intro α g Φs Φg hα hα1 hαα₂ hN hgal hstar hell
    have hCs0 : 0 ≤ max Cs 0 := le_max_right _ _
    have hsp : 0 ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
    have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
    have hK0 : 0 ≤ 1 + 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + 1) := by
      have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hsp
      nlinarith
    have key : ∀ c : ℝ, 0 ≤ c → c ≤ 12 * (max Cs 0 + 1) →
        c * α * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g
          ≤ (1 + 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + 1))
            * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := by
      intro c _hc hcle
      have h1 : c * Real.sqrt (Real.pi / 2)
          ≤ 12 * (max Cs 0 + 1) * Real.sqrt (Real.pi / 2) :=
        mul_le_mul_of_nonneg_right hcle hsp
      have h2 : 12 * (max Cs 0 + 1) * Real.sqrt (Real.pi / 2)
          ≤ 1 + 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + 1) := by
        have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hsp
        nlinarith
      have h3a : α ≤ α ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        exact PsgAux.alpha_le_sqrt hα hα1
      have h3 : α * Work.FTS.Nonlin.Xn α g
          ≤ α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g :=
        mul_le_mul_of_nonneg_right h3a hX0
      calc c * α * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g
          = (c * Real.sqrt (Real.pi / 2)) * (α * Work.FTS.Nonlin.Xn α g) := by ring
        _ ≤ (1 + 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + 1))
              * (α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) :=
            mul_le_mul (le_trans h1 h2) h3 (mul_nonneg hα.le hX0) hK0
        _ = (1 + 12 * Real.sqrt (Real.pi / 2) * (max Cs 0 + 1)) * α ^ (1 / 2 : ℝ)
              * Work.FTS.Nonlin.Xn α g := by ring
    have h6 : 6 * max Cs 0 ≤ 12 * (max Cs 0 + 1) := by linarith
    have h12 : 12 * max Cs 0 ≤ 12 * (max Cs 0 + 1) := by linarith
    have h32 : (3 / 2 : ℝ) ≤ 12 * (max Cs 0 + 1) := by linarith
    have h3' : (3 : ℝ) ≤ 12 * (max Cs 0 + 1) := by linarith
    have hrow3 : 6 * max Cs 0 * α ^ 2 * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g
        ≤ 6 * max Cs 0 * α * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g := by
      have h1 : α ^ 2 ≤ α := by nlinarith
      have h2 : 0 ≤ 6 * max Cs 0 * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g := by
        have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hCs0
        have := mul_nonneg this hsp
        exact mul_nonneg this hX0
      nlinarith [h1, h2]
    exact ⟨(row1sg hα hstar hgal).trans
        (ENNReal.ofReal_le_ofReal (key (6 * max Cs 0)
          (mul_nonneg (by norm_num) hCs0) h6)),
      (row2sg hα hα1 hstar hgal).trans
        (ENNReal.ofReal_le_ofReal (key (12 * max Cs 0)
          (mul_nonneg (by norm_num) hCs0) h12)),
      ((row3sg hα hstar hgal).trans (ENNReal.ofReal_le_ofReal hrow3)).trans
        (ENNReal.ofReal_le_ofReal (key (6 * max Cs 0)
          (mul_nonneg (by norm_num) hCs0) h6)),
      (row4sg hα hα1 hstar hgal).trans
        (ENNReal.ofReal_le_ofReal (key (3 / 2) (by norm_num) h32)),
      (row5sg hα hα1 hstar hgal).trans
        (ENNReal.ofReal_le_ofReal (key 3 (by norm_num) h3'))⟩

end

end Work.FTS.Nonlinear.Pieces.rl1Pieces
