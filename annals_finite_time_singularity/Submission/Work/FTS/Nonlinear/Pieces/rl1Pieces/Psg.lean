import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.VocabO
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq

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







end

end Work.FTS.Nonlinear.Pieces.rl1Pieces
