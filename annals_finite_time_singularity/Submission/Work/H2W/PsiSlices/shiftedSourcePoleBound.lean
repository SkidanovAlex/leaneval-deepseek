import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.lzeroSlicePoleBound
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.eigenPoleHalves
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.eigenFTCPoleDefs
import Submission.Work.FTS.EllipticEst.H2W.SliceA.lzero1SliceGrowthQuant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.H2W.PsiSlices

open Work.FTS.EllipticEst.H2W
open Work.FTS.EllipticEst.H2W.WeakPureAux
open Work.FTS.EllipticEst.H2W.LzeroGrowth

set_option autoImplicit false

noncomputable section

/-! ## The shifted source mass, and the pointwise splitting of the `Dfun` density

The whole proof runs the `(Dfun, Rfun)`-Wronskian system of `Lzero1` with the *shifted* source
`g = Lzero1 u - c·u`.  The only structural change with respect to the eigen case is that the
source integral `∫ sinθcos²θ |g|` is a fixed (finite) number `shiftedMass c u` rather than a
multiple of the running `Rfun`-mass, which only shifts the constant of the resulting Grönwall
inequality. -/

/-- The weighted `L¹` mass `2 ∫_{Iθ} sinθcos²θ · |Lzero1 u - c·u|` of the shifted source. -/
def shiftedMass (c : ℝ) (u : ℝ → ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ,
    2 * (Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|)

theorem shiftedMass_nonneg (c : ℝ) (u : ℝ → ℝ) : 0 ≤ shiftedMass c u := by
  rw [shiftedMass]
  refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
  exact mul_nonneg (by norm_num) (mul_nonneg (sinCos2_nonneg hθ) (abs_nonneg _))

/-- The density of `shiftedMass` is integrable as soon as the source hypothesis holds. -/
theorem integrableOn_shiftedMass (c : ℝ) (u : ℝ → ℝ)
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2
        * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => 2 * (Work.Elliptic.sinCos2 θ
        * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|)) Work.Spaces.Iθ := by
  exact h.const_mul 2

/-- An interval integral of the source density is dominated by the full mass. -/
theorem intervalIntegral_shiftedMass_le (c : ℝ) (u : ℝ → ℝ)
    (hc : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 2 * (Work.Elliptic.sinCos2 θ
        * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|)) Work.Spaces.Iθ)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2) :
    (∫ t in a..b, 2 * (Work.Elliptic.sinCos2 t
        * |Work.FTS.EllipticEst.Lzero1 u t - c * u t|)) ≤ shiftedMass c u := by
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ :=
    fun t ht => ⟨le_trans ha ht.1.le, le_trans ht.2 hb⟩
  calc (∫ t in a..b, 2 * (Work.Elliptic.sinCos2 t
        * |Work.FTS.EllipticEst.Lzero1 u t - c * u t|))
      = ∫ t in Set.Ioc a b, 2 * (Work.Elliptic.sinCos2 t
          * |Work.FTS.EllipticEst.Lzero1 u t - c * u t|) :=
        intervalIntegral.integral_of_le hab
    _ ≤ ∫ t in Work.Spaces.Iθ, 2 * (Work.Elliptic.sinCos2 t
          * |Work.FTS.EllipticEst.Lzero1 u t - c * u t|) := by
        refine MeasureTheory.setIntegral_mono_set hc ?_ ?_
        · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          exact mul_nonneg (by norm_num) (mul_nonneg (sinCos2_nonneg ht) (abs_nonneg _))
        · filter_upwards with t ht using hsub ht
    _ = shiftedMass c u := by rw [shiftedMass]

/-- Pointwise splitting of the density in the `Dfun`-FTC identity:
`|2 Lzero1 u · sinθcos²θ| ≤ 2 sinθcos²θ |Lzero1 u - c·u| + 2|c| (|Rfun u| · ew)`. -/
theorem abs_two_mul_sinCos2_le (c : ℝ) {u : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |2 * Work.FTS.EllipticEst.Lzero1 u θ * Work.Elliptic.sinCos2 θ|
      ≤ 2 * (Work.Elliptic.sinCos2 θ
          * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|)
        + 2 * |c| * (|Rfun u θ| * ew θ) := by
  have hσ : 0 ≤ Work.Elliptic.sinCos2 θ := LzeroGrowth.sinCos2_nonneg_of_mem hθ
  have hsin2 : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hsplit : |Work.FTS.EllipticEst.Lzero1 u θ|
      ≤ |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ| + |c| * |u θ| := by
    have h := abs_add_le (Work.FTS.EllipticEst.Lzero1 u θ - c * u θ) (c * u θ)
    have h4 : (Work.FTS.EllipticEst.Lzero1 u θ - c * u θ) + c * u θ
        = Work.FTS.EllipticEst.Lzero1 u θ := by ring
    rw [h4, abs_mul] at h
    exact h
  have hu_eq : u θ = Rfun u θ * Real.sin (2 * θ) :=
    (Lzero1Growth.Rfun_mul_sin (u := u) hθ).symm
  have huabs : |u θ| = |Rfun u θ| * Real.sin (2 * θ) := by
    rw [hu_eq, abs_mul, abs_of_pos hsin2]
  have hmain : 2 * Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|
      ≤ 2 * (Work.Elliptic.sinCos2 θ
          * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|)
        + 2 * |c| * (|Rfun u θ| * ew θ) := by
    have h1 : 2 * Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ|
        ≤ 2 * Work.Elliptic.sinCos2 θ
          * (|Work.FTS.EllipticEst.Lzero1 u θ - c * u θ| + |c| * |u θ|) :=
      mul_le_mul_of_nonneg_left hsplit (by linarith [hσ])
    rw [huabs] at h1
    have h2 : 2 * Work.Elliptic.sinCos2 θ
          * (|Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|
            + |c| * (|Rfun u θ| * Real.sin (2 * θ)))
        = 2 * (Work.Elliptic.sinCos2 θ
            * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|)
          + 2 * |c| * (|Rfun u θ| * ew θ) := by
      rw [ew]; ring
    linarith [h1, h2]
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hσ]
  convert hmain using 1 <;> ring

/-! ## The two halves of the running bounds -/

/-- **The shifted `Dfun` running bound on the right half.**  For `θ ∈ [π/4, π/2)`,
`|Dfun u θ| ≤ |Dfun u (π/4)| + shiftedMass c u + 2|c|·Gd u θ`. -/
theorem shiftedDfunRunBound (c : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2
        * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|) Work.Spaces.Iθ)
    {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    |Dfun u θ| ≤ |Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ := by
  have hq : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc : MeasureTheory.IntegrableOn
      (fun t : ℝ => 2 * (Work.Elliptic.sinCos2 t
        * |Work.FTS.EllipticEst.Lzero1 u t - c * u t|)) Work.Spaces.Iθ :=
    integrableOn_shiftedMass c u h
  have hftc : Dfun u θ - Dfun u (Real.pi / 4)
      = ∫ s in (Real.pi / 4)..θ,
          2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s :=
    Dfun_ftc hu hq hθ' hθ.1
  have h1 : |Dfun u θ - Dfun u (Real.pi / 4)|
      ≤ ∫ s in (Real.pi / 4)..θ,
          |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s| := by
    rw [hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hθ.1
  have hsub : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun s hs => ⟨by linarith [hs.1, Real.pi_pos], by linarith [hθ.2, hs.2]⟩
  have hpt : ∀ s ∈ Set.Icc (Real.pi / 4) θ,
      |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|
        ≤ 2 * (Work.Elliptic.sinCos2 s
            * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|)
          + 2 * |c| * (|Rfun u s| * ew s) :=
    fun s hs => abs_two_mul_sinCos2_le c (hsub hs)
  have hcs : ContinuousOn (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s)
      (Set.Icc (Real.pi / 4) θ) :=
    ((Lzero1Growth.continuousOn_Lzero1 hu).const_mul 2).mono hsub
  have hLint : IntervalIntegrable
      (fun s : ℝ => |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|)
      volume (Real.pi / 4) θ :=
    ((hcs.mul WeakPureAux.continuous_sinCos2.continuousOn).abs).intervalIntegrable_of_Icc hθ.1
  have hsrcCont : ContinuousOn
      (fun s : ℝ => Work.FTS.EllipticEst.Lzero1 u s - c * u s)
      (Set.Icc (Real.pi / 4) θ) :=
    ((Lzero1Growth.continuousOn_Lzero1 hu).mono hsub).sub
      ((hu.continuousOn.const_mul c).mono hsub)
  have hAint : IntervalIntegrable
      (fun s : ℝ => 2 * (Work.Elliptic.sinCos2 s
        * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|))
      volume (Real.pi / 4) θ :=
    ((WeakPureAux.continuous_sinCos2.continuousOn.mul hsrcCont.abs).const_mul 2)
      |>.intervalIntegrable_of_Icc hθ.1
  have hBint : IntervalIntegrable
      (fun s : ℝ => 2 * |c| * (|Rfun u s| * ew s)) volume (Real.pi / 4) θ :=
    ((continuousOn_absRfun_mul_ew hu
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).const_mul (2 * |c|))
      |>.intervalIntegrable_of_Icc hθ.1
  have hRint : IntervalIntegrable
      (fun s : ℝ => 2 * (Work.Elliptic.sinCos2 s
            * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|)
          + 2 * |c| * (|Rfun u s| * ew s)) volume (Real.pi / 4) θ :=
    hAint.add hBint
  have h3 : (∫ s in (Real.pi / 4)..θ,
        |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|)
      ≤ ∫ s in (Real.pi / 4)..θ,
          (2 * (Work.Elliptic.sinCos2 s
              * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|)
            + 2 * |c| * (|Rfun u s| * ew s)) :=
    intervalIntegral.integral_mono_on hθ.1 hLint hRint hpt
  have h4a : (∫ s in (Real.pi / 4)..θ, 2 * (Work.Elliptic.sinCos2 s
        * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|))
      = 2 * ∫ s in (Real.pi / 4)..θ, (Work.Elliptic.sinCos2 s
        * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|) :=
    intervalIntegral.integral_const_mul 2 _
  have h4b : (∫ s in (Real.pi / 4)..θ, 2 * |c| * (|Rfun u s| * ew s))
      = 2 * |c| * ∫ s in (Real.pi / 4)..θ, |Rfun u s| * ew s :=
    intervalIntegral.integral_const_mul (2 * |c|) _
  have h4 : (∫ s in (Real.pi / 4)..θ,
          (2 * (Work.Elliptic.sinCos2 s
              * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|)
            + 2 * |c| * (|Rfun u s| * ew s)))
      = (2 * ∫ s in (Real.pi / 4)..θ, (Work.Elliptic.sinCos2 s
              * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|))
        + 2 * |c| * (∫ s in (Real.pi / 4)..θ, |Rfun u s| * ew s) := by
    rw [intervalIntegral.integral_add hAint hBint, h4a, h4b]
  have h5 : (2 * ∫ s in (Real.pi / 4)..θ, (Work.Elliptic.sinCos2 s
        * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|)) ≤ shiftedMass c u := by
    have hh := intervalIntegral_shiftedMass_le c u hc hθ.1 (by linarith [Real.pi_pos])
      (le_of_lt hθ.2)
    rwa [h4a] at hh
  have h6 : (∫ s in (Real.pi / 4)..θ, |Rfun u s| * ew s) = Gd u θ := rfl
  have h7 : |Dfun u θ - Dfun u (Real.pi / 4)| ≤ shiftedMass c u + 2 * |c| * Gd u θ := by
    rw [h6] at h4
    linarith [h1, h3, h4, h5]
  calc |Dfun u θ| = |Dfun u (Real.pi / 4) + (Dfun u θ - Dfun u (Real.pi / 4))| := by
        congr 1; ring
    _ ≤ |Dfun u (Real.pi / 4)| + |Dfun u θ - Dfun u (Real.pi / 4)| := abs_add_le _ _
    _ ≤ |Dfun u (Real.pi / 4)| + (shiftedMass c u + 2 * |c| * Gd u θ) :=
        add_le_add le_rfl h7
    _ = |Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ := by ring

/-- **The shifted `Rfun` running bound on the right half.**  For `θ ∈ [π/4, π/2)`,
`|Rfun u θ| ≤ |Rfun u (π/4)| + (|Dfun u (π/4)| + shiftedMass c u + 2|c|·Gd u θ)·Ki θ`. -/
theorem shiftedRfunRunBound (c : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2
        * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|) Work.Spaces.Iθ)
    {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    |Rfun u θ| ≤ |Rfun u (Real.pi / 4)|
      + (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ) * Ki θ := by
  have hq : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hq0 : (0 : ℝ) < Real.pi / 4 := hq.1
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hftc := Rfun_ftc_ek hu hq hθ' hθ.1
  have h2 : ∀ s ∈ Set.Icc (Real.pi / 4) θ,
      |ek s * (-(Dfun u s))|
        ≤ (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ) * ek s := by
    intro s hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hs.1, Real.pi_pos], by linarith [hθ.2, hs.2]⟩
    have hk : 0 ≤ ek s := ek_nonneg hs'
    have hD := shiftedDfunRunBound c u hu h (θ := s) ⟨hs.1, by linarith [hθ.2, hs.2]⟩
    have hG : Gd u s ≤ Gd u θ := Gd_mono hu hs.1 hθ.2 hs.2
    have h2c : (0 : ℝ) ≤ 2 * |c| := by positivity
    rw [abs_mul, abs_neg, abs_of_nonneg hk]
    calc ek s * |Dfun u s|
        ≤ ek s * (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u s) :=
          mul_le_mul_of_nonneg_left hD hk
      _ ≤ ek s * (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hG h2c)) hk
      _ = (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ) * ek s := by ring
  have h1 : |Rfun u θ - Rfun u (Real.pi / 4)|
      ≤ ∫ s in (Real.pi / 4)..θ, |ek s * (-(Dfun u s))| := by
    rw [hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hθ.1
  have hcont1 : ContinuousOn (fun s : ℝ => |ek s * (-(Dfun u s))|)
      (Set.Icc (Real.pi / 4) θ) :=
    (ContinuousOn.mul (continuousOn_ek hq0 hθ.2)
      (((Lzero1Growth.continuousOn_Dfun hu).mono (fun s hs =>
        ⟨by linarith [hs.1, Real.pi_pos], by linarith [hθ.2, hs.2]⟩)).neg)).abs
  have hcont2 : ContinuousOn
      (fun s : ℝ => (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ) * ek s)
      (Set.Icc (Real.pi / 4) θ) :=
    continuousOn_const.mul (continuousOn_ek hq0 hθ.2)
  have hint1 : IntervalIntegrable (fun s : ℝ => |ek s * (-(Dfun u s))|)
      volume (Real.pi / 4) θ := hcont1.intervalIntegrable_of_Icc hθ.1
  have hint2 : IntervalIntegrable
      (fun s : ℝ => (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ) * ek s)
      volume (Real.pi / 4) θ := hcont2.intervalIntegrable_of_Icc hθ.1
  have h3 := intervalIntegral.integral_mono_on hθ.1 hint1 hint2 h2
  have h4 : (∫ s in (Real.pi / 4)..θ,
        (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ) * ek s)
      = (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ) * Ki θ := by
    rw [Ki]
    exact intervalIntegral.integral_const_mul
      (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ) ek
  have hkey : |Rfun u θ - Rfun u (Real.pi / 4)|
      ≤ (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ) * Ki θ :=
    le_trans (le_trans h1 h3) (le_of_eq h4)
  calc |Rfun u θ| = |Rfun u (Real.pi / 4) + (Rfun u θ - Rfun u (Real.pi / 4))| := by
        congr 1; ring
    _ ≤ |Rfun u (Real.pi / 4)| + |Rfun u θ - Rfun u (Real.pi / 4)| := abs_add_le _ _
    _ ≤ |Rfun u (Real.pi / 4)|
          + (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ) * Ki θ :=
        add_le_add le_rfl hkey

/-- **The Grönwall step on the right half.**  The running mass `Gd u` is bounded. -/
theorem shiftedGdBound (c : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2
        * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|) Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2), Gd u θ ≤ C := by
  set P : ℝ := 2 * |c| * (Real.pi ^ 4 / 128) with hPdef
  set Q : ℝ := |Rfun u (Real.pi / 4)|
    + (|Dfun u (Real.pi / 4)| + shiftedMass c u) * (Real.pi ^ 4 / 128) with hQdef
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg (add_nonneg (abs_nonneg _) (shiftedMass_nonneg c u)) (by positivity))
  have hmass : ∀ y ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      |Rfun u y| * ew y ≤ P * Gd u y + Q := by
    intro y hy
    have hy2 : y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos, hy.1], hy.2⟩
    have hew0 : 0 ≤ ew y := ew_nonneg hy2
    have hR := shiftedRfunRunBound c u hu h hy
    have h1 := mul_le_mul_of_nonneg_right hR hew0
    have hKiw : Ki y * ew y ≤ Real.pi ^ 4 / 128 := by
      rw [mul_comm]; exact ew_mul_Ki_le hy
    have hA1 : |Rfun u (Real.pi / 4)| * ew y ≤ |Rfun u (Real.pi / 4)| * 1 :=
      mul_le_mul_of_nonneg_left (ew_le_one y) (abs_nonneg _)
    have hD1 : (|Dfun u (Real.pi / 4)| + shiftedMass c u) * (Ki y * ew y)
        ≤ (|Dfun u (Real.pi / 4)| + shiftedMass c u) * (Real.pi ^ 4 / 128) :=
      mul_le_mul_of_nonneg_left hKiw
        (by linarith [abs_nonneg (Dfun u (Real.pi / 4)), shiftedMass_nonneg c u])
    have hG0 : 0 ≤ Gd u y := Gd_nonneg hu hy.1 hy.2
    have hP1 : 2 * |c| * Gd u y * (Ki y * ew y) ≤ P * Gd u y := by
      have hh := mul_le_mul_of_nonneg_left hKiw
        (by positivity : (0 : ℝ) ≤ 2 * |c| * Gd u y)
      rw [hPdef]
      nlinarith [hh]
    have hexp : (|Rfun u (Real.pi / 4)|
          + (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u y) * Ki y) * ew y
        = |Rfun u (Real.pi / 4)| * ew y
          + (|Dfun u (Real.pi / 4)| + shiftedMass c u) * (Ki y * ew y)
          + 2 * |c| * Gd u y * (Ki y * ew y) := by ring
    have hsum : (|Rfun u (Real.pi / 4)|
          + (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u y) * Ki y) * ew y
        ≤ P * Gd u y + Q := by
      rw [hexp, hQdef]
      linarith [hA1, hD1, hP1]
    linarith [h1, hsum]
  have hprim : ∀ T ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      Gd u T ≤ gronwallBound 0 P Q (T - Real.pi / 4) := by
    intro T hT
    have hle : (Real.pi / 4 : ℝ) ≤ T := hT.1.le
    set F : ℝ → ℝ := fun s => |Rfun u s| * ew s with hFdef
    have hFat : ∀ y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ContinuousAt F y := by
      intro y hy
      have hR : ContinuousAt (Rfun u) y := by
        have h1 : ContinuousAt u y :=
          (Lzero1Growth.hasDerivAt_u hu hy).continuousAt
        have h2 : ContinuousAt (fun s : ℝ => Real.sin (2 * s)) y := by fun_prop
        exact h1.div h2 (ne_of_gt (sin_two_pos hy))
      rw [hFdef]
      exact (hR.abs).mul ew_continuous.continuousAt
    have hFcont : ContinuousOn F (Set.Icc (Real.pi / 4) T) := fun y hy =>
      (hFat y ⟨by linarith [Real.pi_pos, hy.1], lt_of_le_of_lt hy.2 hT.2⟩).continuousWithinAt
    have hFint : IntegrableOn F (Set.Icc (Real.pi / 4) T) := hFcont.integrableOn_Icc
    have hcontIoc : ContinuousOn (fun x : ℝ => ∫ t in Set.Ioc (Real.pi / 4) x, F t)
        (Set.Icc (Real.pi / 4) T) := intervalIntegral.continuousOn_primitive hFint
    have hcont : ContinuousOn (Gd u) (Set.Icc (Real.pi / 4) T) := by
      refine hcontIoc.congr (fun x hx => ?_)
      rw [Gd, hFdef]
      exact intervalIntegral.integral_of_le hx.1
    have hderiv : ∀ x ∈ Set.Ico (Real.pi / 4) T,
        HasDerivWithinAt (Gd u) (F x) (Set.Ici x) x := by
      intro x hx
      have hx2 : x ∈ Set.Ico (Real.pi / 4) (Real.pi / 2) :=
        ⟨hx.1, lt_of_lt_of_le hx.2 hT.2.le⟩
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [Real.pi_pos, hx.1], hx2.2⟩
      have hint : IntervalIntegrable F volume (Real.pi / 4) x :=
        (hFcont.mono (fun y hy => ⟨hy.1, le_trans hy.2 hx.2.le⟩)).intervalIntegrable_of_Icc hx.1
      have hmeas : StronglyMeasurableAtFilter F (𝓝 x) volume :=
        ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo (0 : ℝ) (Real.pi / 2))
          isOpen_Ioo hFat x hx'
      exact (intervalIntegral.integral_hasDerivAt_right hint hmeas (hFat x hx')).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Ico (Real.pi / 4) T, ‖F x‖ ≤ P * ‖Gd u x‖ + Q := by
      intro x hx
      have hx2 : x ∈ Set.Ico (Real.pi / 4) (Real.pi / 2) :=
        ⟨hx.1, lt_of_lt_of_le hx.2 hT.2.le⟩
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [Real.pi_pos, hx.1], hx2.2⟩
      have hFnn : 0 ≤ F x := by
        rw [hFdef]; exact mul_nonneg (abs_nonneg _) (ew_nonneg hx')
      have hval := hmass x hx2
      have hnorm : ‖F x‖ = |Rfun u x| * ew x := by
        rw [hFdef, Real.norm_eq_abs, abs_of_nonneg hFnn]
      rw [hnorm]
      have hle2 : P * Gd u x + Q ≤ P * ‖Gd u x‖ + Q :=
        add_le_add (mul_le_mul_of_nonneg_left (le_abs_self _) hP0) le_rfl
      linarith [hval, hle2]
    have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := Gd u) (f' := F) (a := (Real.pi / 4 : ℝ)) (b := T) (δ := (0 : ℝ)) (K := P)
      (ε := Q) hcont hderiv
      (by simp only [Gd, intervalIntegral.integral_same, norm_zero, le_refl]) hbound
    have hT' := hmain T ⟨hle, le_rfl⟩
    have hGnn : 0 ≤ Gd u T := Gd_nonneg hu hT.1.le hT.2
    rw [Real.norm_eq_abs, abs_of_nonneg hGnn] at hT'
    exact hT'
  have hCnn : 0 ≤ gronwallBound 0 P Q (Real.pi / 4) := by
    have h := gronwallBound_mono (δ := (0 : ℝ)) (K := P) (ε := Q) le_rfl hQ0 hP0
      (show (0 : ℝ) ≤ Real.pi / 4 by linarith [Real.pi_pos])
    rw [gronwallBound_x0] at h
    exact h
  refine ⟨gronwallBound 0 P Q (Real.pi / 4), hCnn, fun θ hθ => ?_⟩
  rcases eq_or_lt_of_le hθ.1 with heq | hlt
  · rw [← heq]
    simp only [Gd, intervalIntegral.integral_same]
    exact hCnn
  · have hh := hprim θ ⟨hlt, hθ.2⟩
    have hmono := gronwallBound_mono (δ := (0 : ℝ)) (K := P) (ε := Q) le_rfl hQ0 hP0
      (show θ - Real.pi / 4 ≤ Real.pi / 4 by linarith [hθ.2])
    exact le_trans hh hmono

/-- **The right-half constant for the shifted operator.** -/
theorem shiftedRfunRightConst (c : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2
        * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|) Work.Spaces.Iθ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      |Rfun u θ| ≤ |Rfun u (Real.pi / 4)| + B * Ki θ := by
  obtain ⟨C, hC, hbound⟩ := shiftedGdBound c u hu h
  have hS0 : 0 ≤ shiftedMass c u := shiftedMass_nonneg c u
  have h2c0 : (0 : ℝ) ≤ 2 * |c| := by positivity
  refine ⟨|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * C,
    add_nonneg (add_nonneg (abs_nonneg _) hS0) (mul_nonneg h2c0 hC), fun θ hθ => ?_⟩
  have h1 := shiftedRfunRunBound c u hu h hθ
  have hKi : 0 ≤ Ki θ := Ki_nonneg hθ.1 hθ.2
  have hcoef : |Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ
      ≤ |Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * C := by
    have hh := hbound θ hθ
    have h2c : (0 : ℝ) ≤ 2 * |c| := by positivity
    linarith [mul_le_mul_of_nonneg_left hh h2c]
  calc |Rfun u θ|
      ≤ |Rfun u (Real.pi / 4)|
          + (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * Gd u θ) * Ki θ := h1
    _ ≤ |Rfun u (Real.pi / 4)|
          + (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * C) * Ki θ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef hKi)

/-! ## The left half -/

/-- **The shifted `Dfun` running bound on the left half.**  For `θ ∈ (0, π/4]`,
`|Dfun u θ| ≤ |Dfun u (π/4)| + shiftedMass c u + 2|c|·GdL u θ`. -/
theorem shiftedDfunRunBoundL (c : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2
        * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|) Work.Spaces.Iθ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4)) :
    |Dfun u θ| ≤ |Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ := by
  have hq : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc : MeasureTheory.IntegrableOn
      (fun t : ℝ => 2 * (Work.Elliptic.sinCos2 t
        * |Work.FTS.EllipticEst.Lzero1 u t - c * u t|)) Work.Spaces.Iθ :=
    integrableOn_shiftedMass c u h
  have hftc : Dfun u (Real.pi / 4) - Dfun u θ
      = ∫ s in θ..(Real.pi / 4),
          2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s := by
    have hh := Dfun_ftc hu hθ' hq hθ.2
    linarith [hh]
  have h1 : |Dfun u (Real.pi / 4) - Dfun u θ|
      ≤ ∫ s in θ..(Real.pi / 4),
          |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s| := by
    rw [hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hθ.2
  have hsub : Set.Icc θ (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun s hs => ⟨by linarith [hθ.1, hs.1], by linarith [hs.2, Real.pi_pos]⟩
  have hpt : ∀ s ∈ Set.Icc θ (Real.pi / 4),
      |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|
        ≤ 2 * (Work.Elliptic.sinCos2 s
            * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|)
          + 2 * |c| * (|Rfun u s| * ew s) :=
    fun s hs => abs_two_mul_sinCos2_le c (hsub hs)
  have hcs : ContinuousOn (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s)
      (Set.Icc θ (Real.pi / 4)) :=
    ((Lzero1Growth.continuousOn_Lzero1 hu).const_mul 2).mono hsub
  have hLint : IntervalIntegrable
      (fun s : ℝ => |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|)
      volume θ (Real.pi / 4) :=
    ((hcs.mul WeakPureAux.continuous_sinCos2.continuousOn).abs).intervalIntegrable_of_Icc hθ.2
  have hsrcCont : ContinuousOn
      (fun s : ℝ => Work.FTS.EllipticEst.Lzero1 u s - c * u s)
      (Set.Icc θ (Real.pi / 4)) :=
    ((Lzero1Growth.continuousOn_Lzero1 hu).mono hsub).sub
      ((hu.continuousOn.const_mul c).mono hsub)
  have hAint : IntervalIntegrable
      (fun s : ℝ => 2 * (Work.Elliptic.sinCos2 s
        * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|))
      volume θ (Real.pi / 4) :=
    ((WeakPureAux.continuous_sinCos2.continuousOn.mul hsrcCont.abs).const_mul 2)
      |>.intervalIntegrable_of_Icc hθ.2
  have hBint : IntervalIntegrable
      (fun s : ℝ => 2 * |c| * (|Rfun u s| * ew s)) volume θ (Real.pi / 4) :=
    ((continuousOn_absRfun_mul_ew hu
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).const_mul (2 * |c|))
      |>.intervalIntegrable_of_Icc hθ.2
  have hRint : IntervalIntegrable
      (fun s : ℝ => 2 * (Work.Elliptic.sinCos2 s
            * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|)
          + 2 * |c| * (|Rfun u s| * ew s)) volume θ (Real.pi / 4) :=
    hAint.add hBint
  have h3 : (∫ s in θ..(Real.pi / 4),
        |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|)
      ≤ ∫ s in θ..(Real.pi / 4),
          (2 * (Work.Elliptic.sinCos2 s
              * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|)
            + 2 * |c| * (|Rfun u s| * ew s)) :=
    intervalIntegral.integral_mono_on hθ.2 hLint hRint hpt
  have h4a : (∫ s in θ..(Real.pi / 4), 2 * (Work.Elliptic.sinCos2 s
        * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|))
      = 2 * ∫ s in θ..(Real.pi / 4), (Work.Elliptic.sinCos2 s
        * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|) :=
    intervalIntegral.integral_const_mul 2 _
  have h4b : (∫ s in θ..(Real.pi / 4), 2 * |c| * (|Rfun u s| * ew s))
      = 2 * |c| * ∫ s in θ..(Real.pi / 4), |Rfun u s| * ew s :=
    intervalIntegral.integral_const_mul (2 * |c|) _
  have h4 : (∫ s in θ..(Real.pi / 4),
          (2 * (Work.Elliptic.sinCos2 s
              * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|)
            + 2 * |c| * (|Rfun u s| * ew s)))
      = (2 * ∫ s in θ..(Real.pi / 4), (Work.Elliptic.sinCos2 s
              * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|))
        + 2 * |c| * (∫ s in θ..(Real.pi / 4), |Rfun u s| * ew s) := by
    rw [intervalIntegral.integral_add hAint hBint, h4a, h4b]
  have h5 : (2 * ∫ s in θ..(Real.pi / 4), (Work.Elliptic.sinCos2 s
        * |Work.FTS.EllipticEst.Lzero1 u s - c * u s|)) ≤ shiftedMass c u := by
    have hh := intervalIntegral_shiftedMass_le c u hc hθ.2 hθ.1.le (by linarith [Real.pi_pos])
    rwa [h4a] at hh
  have h6 : (∫ s in θ..(Real.pi / 4), |Rfun u s| * ew s) = GdL u θ := rfl
  have h7 : |Dfun u (Real.pi / 4) - Dfun u θ| ≤ shiftedMass c u + 2 * |c| * GdL u θ := by
    rw [h6] at h4
    linarith [h1, h3, h4, h5]
  have habs : |Dfun u θ - Dfun u (Real.pi / 4)| = |Dfun u (Real.pi / 4) - Dfun u θ| :=
    abs_sub_comm _ _
  calc |Dfun u θ| = |Dfun u (Real.pi / 4) + (Dfun u θ - Dfun u (Real.pi / 4))| := by
        congr 1; ring
    _ ≤ |Dfun u (Real.pi / 4)| + |Dfun u θ - Dfun u (Real.pi / 4)| := abs_add_le _ _
    _ = |Dfun u (Real.pi / 4)| + |Dfun u (Real.pi / 4) - Dfun u θ| := by rw [habs]
    _ ≤ |Dfun u (Real.pi / 4)| + (shiftedMass c u + 2 * |c| * GdL u θ) :=
        add_le_add le_rfl h7
    _ = |Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ := by ring

/-- **The shifted `Rfun` running bound on the left half.** -/
theorem shiftedRfunRunBoundL (c : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2
        * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|) Work.Spaces.Iθ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4)) :
    |Rfun u θ| ≤ |Rfun u (Real.pi / 4)|
      + (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ) * Kl θ := by
  have hq : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hq0 : (0 : ℝ) < Real.pi / 4 := hq.1
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hftc := Rfun_ftc_ek hu hθ' hq hθ.2
  have h2 : ∀ s ∈ Set.Icc θ (Real.pi / 4),
      |ek s * (-(Dfun u s))|
        ≤ (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ) * ek s := by
    intro s hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, hs.1, Real.pi_pos], by linarith [hθ.2, hs.2, Real.pi_pos]⟩
    have hk : 0 ≤ ek s := ek_nonneg hs'
    have hD := shiftedDfunRunBoundL c u hu h (θ := s)
      ⟨by linarith [hθ.1, hs.1], by linarith [hs.2, hθ.2]⟩
    have hG : GdL u s ≤ GdL u θ := GdL_mono hu hθ.1 hs.1 hs.2
    have h2c : (0 : ℝ) ≤ 2 * |c| := by positivity
    rw [abs_mul, abs_neg, abs_of_nonneg hk]
    calc ek s * |Dfun u s|
        ≤ ek s * (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u s) :=
          mul_le_mul_of_nonneg_left hD hk
      _ ≤ ek s * (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hG h2c)) hk
      _ = (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ) * ek s := by ring
  have h1 : |Rfun u (Real.pi / 4) - Rfun u θ|
      ≤ ∫ s in θ..(Real.pi / 4), |ek s * (-(Dfun u s))| := by
    rw [hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hθ.2
  have hcont1 : ContinuousOn
      (fun s : ℝ => |ek s * (-(Dfun u s))|) (Set.Icc θ (Real.pi / 4)) :=
    (ContinuousOn.mul (continuousOn_ek hθ.1 (by linarith [hθ.2, Real.pi_pos]))
      (((Lzero1Growth.continuousOn_Dfun hu).mono (fun s hs =>
        ⟨by linarith [hθ.1, hs.1], by linarith [hθ.2, hs.2, Real.pi_pos]⟩)).neg)).abs
  have hcont2 : ContinuousOn
      (fun s : ℝ => (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ) * ek s)
      (Set.Icc θ (Real.pi / 4)) :=
    continuousOn_const.mul (continuousOn_ek hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  have hint1 : IntervalIntegrable (fun s : ℝ => |ek s * (-(Dfun u s))|)
      volume θ (Real.pi / 4) := hcont1.intervalIntegrable_of_Icc hθ.2
  have hint2 : IntervalIntegrable
      (fun s : ℝ => (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ) * ek s)
      volume θ (Real.pi / 4) := hcont2.intervalIntegrable_of_Icc hθ.2
  have h3 := intervalIntegral.integral_mono_on hθ.2 hint1 hint2 h2
  have h4 : (∫ s in θ..(Real.pi / 4),
        (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ) * ek s)
      = (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ) * Kl θ := by
    rw [Kl]
    exact intervalIntegral.integral_const_mul
      (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ) ek
  have hkey : |Rfun u (Real.pi / 4) - Rfun u θ|
      ≤ (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ) * Kl θ :=
    le_trans (le_trans h1 h3) (le_of_eq h4)
  have habs : |Rfun u θ - Rfun u (Real.pi / 4)|
      = |Rfun u (Real.pi / 4) - Rfun u θ| := abs_sub_comm _ _
  calc |Rfun u θ| = |Rfun u (Real.pi / 4) + (Rfun u θ - Rfun u (Real.pi / 4))| := by
        congr 1; ring
    _ ≤ |Rfun u (Real.pi / 4)| + |Rfun u θ - Rfun u (Real.pi / 4)| := abs_add_le _ _
    _ = |Rfun u (Real.pi / 4)| + |Rfun u (Real.pi / 4) - Rfun u θ| := by rw [habs]
    _ ≤ |Rfun u (Real.pi / 4)|
          + (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ) * Kl θ :=
        add_le_add le_rfl hkey

/-- **The Grönwall step on the left half.**  The running mass `GdL u` is bounded. -/
theorem shiftedGdLBound (c : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2
        * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|) Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4), GdL u θ ≤ C := by
  set P : ℝ := 2 * |c| * (Real.pi ^ 3 / 16) with hPdef
  set Q : ℝ := |Rfun u (Real.pi / 4)|
    + (|Dfun u (Real.pi / 4)| + shiftedMass c u) * (Real.pi ^ 3 / 16) with hQdef
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg (add_nonneg (abs_nonneg _) (shiftedMass_nonneg c u)) (by positivity))
  have hmass : ∀ y ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
      |Rfun u y| * ew y ≤ P * GdL u y + Q := by
    intro y hy
    have hy2 : y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
    have hew0 : 0 ≤ ew y := ew_nonneg hy2
    have hR := shiftedRfunRunBoundL c u hu h hy
    have h1 := mul_le_mul_of_nonneg_right hR hew0
    have hKlw : Kl y * ew y ≤ Real.pi ^ 3 / 16 := by
      rw [mul_comm]; exact ew_mul_Kl_le hy
    have hA1 : |Rfun u (Real.pi / 4)| * ew y ≤ |Rfun u (Real.pi / 4)| * 1 :=
      mul_le_mul_of_nonneg_left (ew_le_one y) (abs_nonneg _)
    have hD1 : (|Dfun u (Real.pi / 4)| + shiftedMass c u) * (Kl y * ew y)
        ≤ (|Dfun u (Real.pi / 4)| + shiftedMass c u) * (Real.pi ^ 3 / 16) :=
      mul_le_mul_of_nonneg_left hKlw
        (by linarith [abs_nonneg (Dfun u (Real.pi / 4)), shiftedMass_nonneg c u])
    have hG0 : 0 ≤ GdL u y := GdL_nonneg hu hy
    have hP1 : 2 * |c| * GdL u y * (Kl y * ew y) ≤ P * GdL u y := by
      have hh := mul_le_mul_of_nonneg_left hKlw
        (by positivity : (0 : ℝ) ≤ 2 * |c| * GdL u y)
      rw [hPdef]
      nlinarith [hh]
    have hexp : (|Rfun u (Real.pi / 4)|
          + (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u y) * Kl y) * ew y
        = |Rfun u (Real.pi / 4)| * ew y
          + (|Dfun u (Real.pi / 4)| + shiftedMass c u) * (Kl y * ew y)
          + 2 * |c| * GdL u y * (Kl y * ew y) := by ring
    have hsum : (|Rfun u (Real.pi / 4)|
          + (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u y) * Kl y) * ew y
        ≤ P * GdL u y + Q := by
      rw [hexp, hQdef]
      linarith [hA1, hD1, hP1]
    linarith [h1, hsum]
  set g : ℝ → ℝ := fun t => |Rfun u (Real.pi / 4 - t)| * ew (Real.pi / 4 - t) with hgdef
  have hgopen : ∀ t ∈ Set.Ioo (-(1 : ℝ) / 4) (Real.pi / 4), ContinuousAt g t := by
    intro t ht
    have hy : Real.pi / 4 - t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [ht.2], by linarith [ht.1, Real.pi_gt_three]⟩
    have hRfun : ContinuousAt (Rfun u) (Real.pi / 4 - t) := by
      have h1 : ContinuousAt u (Real.pi / 4 - t) :=
        (Lzero1Growth.hasDerivAt_u hu hy).continuousAt
      have h2 : ContinuousAt (fun s : ℝ => Real.sin (2 * s)) (Real.pi / 4 - t) := by
        fun_prop
      have h3 : Real.sin (2 * (Real.pi / 4 - t)) ≠ 0 := ne_of_gt (sin_two_pos hy)
      exact h1.div h2 h3
    have hf : ContinuousAt (fun s : ℝ => |Rfun u s| * ew s) (Real.pi / 4 - t) :=
      (hRfun.abs).mul ew_continuous.continuousAt
    have hlin : ContinuousAt (fun t : ℝ => Real.pi / 4 - t) t :=
      continuousAt_const.sub continuousAt_id
    have hcomp := hf.comp hlin
    rw [hgdef]
    exact hcomp
  have hprim : ∀ b ∈ Set.Ico (0 : ℝ) (Real.pi / 4),
      (∫ t in (0 : ℝ)..b, g t) ≤ gronwallBound 0 P Q b := by
    intro b hb
    have hb0 : 0 ≤ b := hb.1
    have hblt : b < Real.pi / 4 := hb.2
    have hgcont : ContinuousOn g (Set.Icc 0 b) := fun x hx =>
      (hgopen x ⟨by linarith [hx.1, hx.2, hblt], by linarith [hx.2, hblt]⟩).continuousWithinAt
    have hgint : IntegrableOn g (Set.Icc 0 b) := hgcont.integrableOn_Icc
    have hcontIoc : ContinuousOn (fun x : ℝ => ∫ t in Set.Ioc (0 : ℝ) x, g t)
        (Set.Icc 0 b) := intervalIntegral.continuousOn_primitive hgint
    have hcont : ContinuousOn (fun x : ℝ => ∫ t in (0 : ℝ)..x, g t) (Set.Icc 0 b) :=
      hcontIoc.congr (fun x hx => intervalIntegral.integral_of_le hx.1)
    have hderiv : ∀ x ∈ Set.Ico (0 : ℝ) b,
        HasDerivWithinAt (fun x : ℝ => ∫ t in (0 : ℝ)..x, g t) (g x) (Set.Ici x) x := by
      intro x hx
      have hxlt : x < Real.pi / 4 := lt_of_lt_of_le hx.2 hblt.le
      have hint : IntervalIntegrable g volume (0 : ℝ) x :=
        (hgcont.mono (fun y hy => ⟨hy.1, by linarith [hy.2, hx.2]⟩)).intervalIntegrable_of_Icc hx.1
      have hcontAt : ContinuousAt g x := hgopen x ⟨by linarith [hx.1], hxlt⟩
      have hmeas : StronglyMeasurableAtFilter g (𝓝 x) volume :=
        ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo (-(1 : ℝ) / 4) (Real.pi / 4))
          isOpen_Ioo hgopen x ⟨by linarith [hx.1], hxlt⟩
      exact (intervalIntegral.integral_hasDerivAt_right hint hmeas hcontAt).hasDerivWithinAt
    have hbound : ∀ x ∈ Set.Ico (0 : ℝ) b, ‖g x‖
        ≤ P * ‖∫ t in (0 : ℝ)..x, g t‖ + Q := by
      intro x hx
      have hxlt : x < Real.pi / 4 := lt_of_lt_of_le hx.2 hblt.le
      have hy : Real.pi / 4 - x ∈ Set.Ioc (0 : ℝ) (Real.pi / 4) :=
        ⟨by linarith [hxlt], by linarith [hx.1]⟩
      have hy2 : Real.pi / 4 - x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
      have hgnn : 0 ≤ g x := mul_nonneg (abs_nonneg _) (ew_nonneg hy2)
      have hval := hmass (Real.pi / 4 - x) hy
      have hnorm : ‖g x‖ = |Rfun u (Real.pi / 4 - x)| * ew (Real.pi / 4 - x) := by
        rw [hgdef, Real.norm_eq_abs, abs_of_nonneg hgnn]
      rw [hnorm]
      have hchange : (∫ t in (0 : ℝ)..x, g t) = GdL u (Real.pi / 4 - x) := by
        have h2 := intervalIntegral.integral_comp_sub_left
          (f := fun s : ℝ => |Rfun u s| * ew s) (a := (0 : ℝ)) (b := x) (Real.pi / 4)
        rw [hgdef]
        refine h2.trans ?_
        rw [GdL]
        congr 1 <;> ring
      have hle : P * GdL u (Real.pi / 4 - x) + Q ≤ P * ‖∫ t in (0 : ℝ)..x, g t‖ + Q := by
        rw [hchange]
        exact add_le_add (mul_le_mul_of_nonneg_left (le_abs_self _) hP0) le_rfl
      linarith [hval, hle]
    have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := fun x : ℝ => ∫ t in (0 : ℝ)..x, g t)
      (f' := g) (a := (0 : ℝ)) (b := b) (δ := (0 : ℝ)) (K := P) (ε := Q)
      hcont hderiv (by simp) hbound
    have hb' := hmain b ⟨hb0, le_rfl⟩
    rw [sub_zero] at hb'
    exact le_trans (le_abs_self _) hb'
  refine ⟨gronwallBound 0 P Q (Real.pi / 4), ?_, ?_⟩
  · have h := gronwallBound_mono (δ := (0 : ℝ)) (K := P) (ε := Q) le_rfl hQ0 hP0
      (show (0 : ℝ) ≤ Real.pi / 4 by linarith [Real.pi_pos])
    rw [gronwallBound_x0] at h
    exact h
  · intro θ hθ
    have hb : Real.pi / 4 - θ ∈ Set.Ico (0 : ℝ) (Real.pi / 4) :=
      ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
    have hh := hprim (Real.pi / 4 - θ) hb
    have hchange : (∫ t in (0 : ℝ)..(Real.pi / 4 - θ), g t) = GdL u θ := by
      have h2 := intervalIntegral.integral_comp_sub_left
        (f := fun s : ℝ => |Rfun u s| * ew s) (a := (0 : ℝ))
        (b := Real.pi / 4 - θ) (Real.pi / 4)
      rw [hgdef]
      refine h2.trans ?_
      rw [GdL]
      congr 1 <;> ring
    rw [hchange] at hh
    refine le_trans hh ?_
    have hmono := gronwallBound_mono (δ := (0 : ℝ)) (K := P) (ε := Q) le_rfl hQ0 hP0
    exact hmono (show Real.pi / 4 - θ ≤ Real.pi / 4 by linarith [hθ.1])

/-- **The left-half constant for the shifted operator.** -/
theorem shiftedRfunLeftConst (c : ℝ) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2
        * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|) Work.Spaces.Iθ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
      |Rfun u θ| ≤ |Rfun u (Real.pi / 4)|
        + B * (∫ s in θ..(Real.pi / 4),
            1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) := by
  obtain ⟨C, hC, hbound⟩ := shiftedGdLBound c u hu h
  have hS0 : 0 ≤ shiftedMass c u := shiftedMass_nonneg c u
  have h2c0 : (0 : ℝ) ≤ 2 * |c| := by positivity
  refine ⟨|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * C,
    add_nonneg (add_nonneg (abs_nonneg _) hS0) (mul_nonneg h2c0 hC),
    fun θ hθ => ?_⟩
  have h1 := shiftedRfunRunBoundL c u hu h hθ
  have hKl : 0 ≤ Kl θ := Kl_nonneg hθ
  have hcoef : |Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ
      ≤ |Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * C := by
    have hh := hbound θ hθ
    have h2c : (0 : ℝ) ≤ 2 * |c| := by positivity
    linarith [mul_le_mul_of_nonneg_left hh h2c]
  calc |Rfun u θ|
      ≤ |Rfun u (Real.pi / 4)|
          + (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * GdL u θ) * Kl θ := h1
    _ ≤ |Rfun u (Real.pi / 4)|
          + (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * C) * Kl θ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef hKl)
    _ = |Rfun u (Real.pi / 4)|
        + (|Dfun u (Real.pi / 4)| + shiftedMass c u + 2 * |c| * C)
          * (∫ s in θ..(Real.pi / 4),
              1 / (Real.cos s * (Real.sin (2 * s)) ^ 2)) := by
        simp only [Kl, ek]

/-- The one-variable endpoint (indicial) bound for the *shifted* angular operator `Lzero1 - c`:
for any real `c` and `u ∈ C^∞(0, π/2)`, if `θ ↦ sinθcos²θ·|Lzero1 u θ - c·u θ|` is
integrable on `Iθ = [0, π/2]`, then `u` obeys the pole bound.  The added term `-c·u` is lower
order at `θ = π/2` (the indicial equation `1 - s² = 0` is unchanged, exponents `±1`), so the same
growth `O(θ⁻¹ + (π/2-θ)⁻¹)` holds; the case `c = 0` is `WeakPureAux.lzeroSlicePoleBound`.
This is what makes the `z`-level propagation available at *every* level (the level-`m` identity has
the `γ_m·∂_z^mΨ` term, which is exactly `c = γ_m`).

Note for the proof: the existing `lzero1SliceGrowth` proof uses the *explicit* solution `sin 2θ` of
`Lzero1 y = 0`, which is not a solution of `Lzero1 y - c·y = 0` for `c ≠ 0`; the reduction-of-order
argument must be redone with the shifted operator's own regular solution near `θ = π/2`
(Frobenius: exponents `±1`, no resonant `t⁻¹·log t` term — the reduction of order gives Bessel
order 1, `w'' = (1/t)w' - c·w`), and `θ = 0` handled separately (ordinary point). -/
theorem shiftedSourcePoleBound (c : ℝ) (u : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2
        * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|) Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ C * (1 / θ + 1 / (Real.pi / 2 - θ)) := by
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hu 2
  obtain ⟨Bl, hBl0, hl⟩ := shiftedRfunLeftConst c u hu2 h
  obtain ⟨Br, hBr0, hr⟩ := shiftedRfunRightConst c u hu2 h
  set A : ℝ := |Rfun u (Real.pi / 4)| with hAdef
  set B : ℝ := max Bl Br with hBdef
  have hA0 : 0 ≤ A := abs_nonneg _
  have hB0 : 0 ≤ B := le_trans hBl0 (le_max_left Bl Br)
  have hleft : ∀ θ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
      |Rfun u θ| ≤ A + B * ∫ s in θ..(Real.pi / 4),
        1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) := by
    intro θ hθ
    have h1 := hl θ hθ
    have hKl : 0 ≤ Kl θ := Kl_nonneg hθ
    have h2 : Bl * Kl θ ≤ B * Kl θ := mul_le_mul_of_nonneg_right (le_max_left Bl Br) hKl
    calc |Rfun u θ| ≤ |Rfun u (Real.pi / 4)| + Bl * Kl θ := h1
      _ ≤ |Rfun u (Real.pi / 4)| + B * Kl θ := by linarith
      _ = A + B * ∫ s in θ..(Real.pi / 4),
            1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) := by
          simp only [hAdef, Kl, ek]
  have hright : ∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
      |Rfun u θ| ≤ A + B * ∫ s in (Real.pi / 4)..θ,
        1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) := by
    intro θ hθ
    have h1 := hr θ hθ
    have hKi : 0 ≤ Ki θ := Ki_nonneg hθ.1 hθ.2
    have h2 : Br * Ki θ ≤ B * Ki θ := mul_le_mul_of_nonneg_right (le_max_right Bl Br) hKi
    calc |Rfun u θ| ≤ |Rfun u (Real.pi / 4)| + Br * Ki θ := h1
      _ ≤ |Rfun u (Real.pi / 4)| + B * Ki θ := by linarith
      _ = A + B * ∫ s in (Real.pi / 4)..θ,
            1 / (Real.cos s * (Real.sin (2 * s)) ^ 2) := by
          simp only [hAdef, Ki, ek]
  have hbound := SliceA.growthQuant (u := u) hA0 hB0 hleft hright
  refine ⟨10 * (A + B), by positivity, fun θ hθ => ?_⟩
  have hfin := hbound θ hθ
  simpa only [one_div] using hfin

end

end Work.H2W.PsiSlices
