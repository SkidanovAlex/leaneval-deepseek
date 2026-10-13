import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.lzero1SliceGrowth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `WeakPureAux/eigenFTCAux` — the `(Dfun, Rfun)` FTC system for `Lzero1 u = mu * u`

Stage 1 (and the first half of stage 2) of the plan in
`WeakPureAux/NOTES_eigenSlicePoleBound.md`: the two exact integral identities carried by

* `Dfun u θ = cos θ · (u θ · (sin 2θ)' - u' θ · sin 2θ)`, with `Dfun u' = 2·Lzero1 u·sinθcos²θ`,
* `Rfun u θ = u θ / sin 2θ`, with `Rfun u' = -Dfun u θ/(cos θ · sin(2θ)²)`,

and the *running* bound for `Dfun` obtained from them under the eigenrelation
`Lzero1 u = mu * u`.  The bounds are deliberately stated with the running weight
`Gd u θ = ∫_{π/4}^{θ} |Rfun u s|·w s ds` (`w = sin(2θ)·sinθcos²θ`) instead of the total
`Mfun u = ∫_{Iθ} sinθcos²θ·|Lzero1 u|`, which is *not* known to be finite before the theorem is
proved.  All ingredients come from the already-proved `C²`-level lemmas of
`Submission/Work/FTS/EllipticEst/H2W/lzero1SliceGrowth.lean`.
-/

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-- The weight `w θ = sin(2θ)·sinθcos²θ`, so that `sinθcos²θ·|u θ| = |Rfun u θ|·w θ`. -/
def ew (θ : ℝ) : ℝ := Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ

/-- The kernel `k θ = 1/(cos θ · sin(2θ)²)` of the `Rfun` equation. -/
def ek (θ : ℝ) : ℝ := 1 / (Real.cos θ * Real.sin (2 * θ) ^ 2)

/-- The elementary form of `w`: `sin(2θ)·sinθcos²θ = 2 sin²θ cos³θ`. -/
theorem ew_eq (θ : ℝ) : ew θ = 2 * Real.sin θ ^ 2 * Real.cos θ ^ 3 := by
  rw [ew, Work.Elliptic.sinCos2, Real.sin_two_mul]
  ring

/-- The elementary form of `k`: `1/(cos θ sin(2θ)²) = 1/(4 sin²θ cos³θ)`. -/
theorem ek_eq (θ : ℝ) : ek θ = 1 / (4 * Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
  rw [ek, Real.sin_two_mul]
  ring

/-- `sinθcos²θ` is continuous. -/
theorem continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop

/-- `w` is continuous. -/
theorem ew_continuous : Continuous ew := by
  have h : Continuous fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ :=
    (by fun_prop : Continuous fun θ : ℝ => Real.sin (2 * θ)).mul continuous_sinCos2
  exact h

/-- `sinθcos²θ ≥ 0` on the open angular interval. -/
theorem sinCos2_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])).le (sq_nonneg _)

/-- `w` is nonnegative on the open angular interval. -/
theorem ew_nonneg {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 ≤ ew θ := by
  rw [ew]
  exact mul_nonneg (Work.FTS.EllipticEst.H2W.LzeroGrowth.sin_two_pos hθ).le
    (sinCos2_nonneg_of_mem hθ)

/-- `k` is nonnegative on the open angular interval. -/
theorem ek_nonneg {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 0 ≤ ek θ := by
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  have hs2 : 0 < Real.sin (2 * θ) := Work.FTS.EllipticEst.H2W.LzeroGrowth.sin_two_pos hθ
  rw [ek]
  positivity

/-- `Rfun u = u/sin(2θ)` is continuous on the open angular interval for `C²` data. -/
theorem continuousOn_Rfun {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u) (Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn
  have h2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (by fun_prop : Continuous fun θ : ℝ => Real.sin (2 * θ)).continuousOn
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 :=
    fun θ hθ => ne_of_gt (Work.FTS.EllipticEst.H2W.LzeroGrowth.sin_two_pos hθ)
  show ContinuousOn (fun θ : ℝ => u θ / Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2))
  exact h1.div h2 hne

/-- **FTC for `Dfun`.** -/
theorem Dfun_ftc {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hb : b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hab : a ≤ b) :
    Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u b
        - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u a
      = ∫ s in a..b, 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s := by
  have hderiv : ∀ s ∈ Set.uIcc a b,
      HasDerivAt (Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u)
        (2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s) s := by
    intro s hs
    rw [Set.uIcc_of_le hab] at hs
    exact Work.FTS.EllipticEst.H2W.Lzero1Growth.Dfun_hasDerivAt hu
      ⟨by linarith [ha.1, hs.1], by linarith [hb.2, hs.2]⟩
  have hint : IntervalIntegrable
      (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s)
      volume a b := by
    have hcont : ContinuousOn
        (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s)
        (Set.Icc a b) := by
      have h1 : ContinuousOn (fun s : ℝ => 2 * Work.FTS.EllipticEst.Lzero1 u s)
          (Set.Icc a b) :=
        (Work.FTS.EllipticEst.H2W.Lzero1Growth.continuousOn_Lzero1 hu).const_mul 2 |>.mono
          (fun s hs => ⟨by linarith [ha.1, hs.1], by linarith [hb.2, hs.2]⟩)
      exact h1.mul continuous_sinCos2.continuousOn
    exact hcont.intervalIntegrable_of_Icc hab
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b) hderiv hint
  linarith [h]

/-- **FTC for `Rfun`.** -/
theorem Rfun_ftc {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hb : b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hab : a ≤ b) :
    Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u b
        - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u a
      = ∫ s in a..b,
          -(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s)
            / (Real.cos s * Real.sin (2 * s) ^ 2) := by
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun s hs => ⟨by linarith [ha.1, hs.1], by linarith [hb.2, hs.2]⟩
  have hderiv : ∀ s ∈ Set.uIcc a b,
      HasDerivAt (Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u)
        (-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s)
          / (Real.cos s * Real.sin (2 * s) ^ 2)) s := by
    intro s hs
    rw [Set.uIcc_of_le hab] at hs
    exact Work.FTS.EllipticEst.H2W.Lzero1Growth.Rfun_hasDerivAt hu (hsub hs)
  have hint : IntervalIntegrable
      (fun s : ℝ => -(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s)
        / (Real.cos s * Real.sin (2 * s) ^ 2)) volume a b :=
    ((Work.FTS.EllipticEst.H2W.Lzero1Growth.continuousOn_Rderiv hu).mono hsub)
      |>.intervalIntegrable_of_Icc hab
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b) hderiv hint
  linarith [h]

/-- The `ek`-form of the `Rfun` FTC identity. -/
theorem Rfun_ftc_ek {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {a b : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hb : b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hab : a ≤ b) :
    Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u b
        - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u a
      = ∫ s in a..b, ek s * (-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s)) := by
  rw [Rfun_ftc hu ha hb hab]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [ek]
  ring

/-- The integrand `s ↦ |Rfun u s|·w s` of `Gd` is continuous on subintervals of `(0,π/2)`. -/
theorem continuousOn_absRfun_mul_ew {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hb : b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ContinuousOn (fun s : ℝ => |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u s| * ew s)
      (Set.Icc a b) :=
  (((continuousOn_Rfun hu).mono (fun s hs =>
      ⟨by linarith [ha.1, hs.1], by linarith [hb.2, hs.2]⟩)).abs).mul
    (ew_continuous.continuousOn)

/-- The running radial weight `Gd u θ = ∫_{π/4}^{θ} |Rfun u s|·w s ds`. -/
def Gd (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ s in (Real.pi / 4)..θ, |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u s| * ew s

/-- The kernel integral `K θ = ∫_{π/4}^{θ} k s ds`. -/
def Ki (θ : ℝ) : ℝ := ∫ s in (Real.pi / 4)..θ, ek s

/-- **The running bound for `Dfun`** under the eigenrelation: for `θ ∈ [π/4, π/2)`,
`|Dfun u θ| ≤ |Dfun u (π/4)| + 2|mu|·Gd u θ`. -/
theorem Dfun_run_bound {u : ℝ → ℝ} {mu : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (heig : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ = mu * u θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u θ|
      ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ := by
  have hq : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hpt : ∀ s ∈ Set.Icc (Real.pi / 4) θ,
      |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|
        = 2 * |mu| * (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u s| * ew s) := by
    intro s hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hs.1, Real.pi_pos], by linarith [hθ.2, hs.2]⟩
    have hsin : 0 < Real.sin (2 * s) := Work.FTS.EllipticEst.H2W.LzeroGrowth.sin_two_pos hs'
    have hσ : 0 ≤ Work.Elliptic.sinCos2 s := sinCos2_nonneg_of_mem hs'
    have hsinθ : 0 ≤ Real.sin s :=
      (Real.sin_pos_of_pos_of_lt_pi hs'.1 (by linarith [hs'.2, Real.pi_pos])).le
    have hu_eq : u s = Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u s * Real.sin (2 * s) :=
      (Work.FTS.EllipticEst.H2W.Lzero1Growth.Rfun_mul_sin (u := u) hs').symm
    have hL : Work.FTS.EllipticEst.Lzero1 u s = mu * u s := heig s hs'
    rw [hL, hu_eq, ew, Work.Elliptic.sinCos2]
    rw [abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (mul_nonneg hsinθ (sq_nonneg (Real.cos s))),
      abs_of_pos hsin]
    ring
  have hftc := Dfun_ftc hu hq hθ' hθ.1
  have h1 : |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u θ
        - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)|
      ≤ ∫ s in (Real.pi / 4)..θ,
          |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s| := by
    rw [hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hθ.1
  have hcontL : ContinuousOn
      (fun s : ℝ => |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|)
      (Set.Icc (Real.pi / 4) θ) :=
    (((Work.FTS.EllipticEst.H2W.Lzero1Growth.continuousOn_Lzero1 hu).const_mul 2 |>.mono
        (fun s hs => ⟨by linarith [hs.1, Real.pi_pos], by linarith [hθ.2, hs.2]⟩)).mul
      continuous_sinCos2.continuousOn).abs
  have hcontR : ContinuousOn (Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u)
      (Set.Icc (Real.pi / 4) θ) :=
    (continuousOn_Rfun hu).mono (fun s hs =>
      ⟨by linarith [hs.1, Real.pi_pos], by linarith [hθ.2, hs.2]⟩)
  have h3 : (∫ s in (Real.pi / 4)..θ,
        |2 * Work.FTS.EllipticEst.Lzero1 u s * Work.Elliptic.sinCos2 s|)
      ≤ ∫ s in (Real.pi / 4)..θ,
          2 * |mu| * (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u s| * ew s) :=
    intervalIntegral.integral_mono_on hθ.1 (hcontL.intervalIntegrable_of_Icc hθ.1)
      (((hcontR.abs).mul ew_continuous.continuousOn).const_mul (2 * |mu|)
        |>.intervalIntegrable_of_Icc hθ.1)
      (fun s hs => (hpt s hs).le)
  have h4 : (∫ s in (Real.pi / 4)..θ,
        2 * |mu| * (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u s| * ew s))
      = 2 * |mu| * Gd u θ := by
    rw [Gd, intervalIntegral.integral_const_mul]
  calc |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u θ|
      = |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)
          + (Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u θ
            - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4))| := by
        congr 1
        ring
    _ ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)|
          + |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u θ
            - Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| := abs_add_le _ _
    _ ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ := by
        refine add_le_add le_rfl (le_trans h1 (le_trans h3 (le_of_eq h4)))

/-- `ek` is continuous on `[a,b] ⊆ (0,π/2)`. -/
theorem continuousOn_ek {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2) :
    ContinuousOn ek (Set.Icc a b) := by
  show ContinuousOn (fun s : ℝ => 1 / (Real.cos s * Real.sin (2 * s) ^ 2)) (Set.Icc a b)
  refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
  intro s hs
  exact mul_ne_zero
    (ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ha, hs.1], by linarith [hb, hs.2]⟩))
    (pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.H2W.LzeroGrowth.sin_two_pos
      ⟨by linarith [ha, hs.1], by linarith [hb, hs.2]⟩)))

/-- `Gd` is monotone in its upper endpoint on `[π/4, π/2)`. -/
theorem Gd_mono {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {a b : ℝ}
    (ha : (Real.pi / 4 : ℝ) ≤ a) (hb : b < Real.pi / 2) (hab : a ≤ b) : Gd u a ≤ Gd u b := by
  have hq0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hia : IntervalIntegrable
      (fun s : ℝ => |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u s| * ew s)
      volume (Real.pi / 4) a :=
    ((continuousOn_absRfun_mul_ew hu ⟨hq0, by linarith [Real.pi_pos]⟩
      ⟨by linarith [ha, hq0], by linarith [hab, hb]⟩).mono
        (fun s hs => ⟨hs.1, by linarith [hs.2, hab]⟩)).intervalIntegrable_of_Icc ha
  have hib : IntervalIntegrable
      (fun s : ℝ => |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u s| * ew s) volume a b :=
    (continuousOn_absRfun_mul_ew hu ⟨by linarith [ha, hq0], by linarith [hab, hb]⟩
      ⟨by linarith [ha, hq0], hb⟩).intervalIntegrable_of_Icc hab
  have hsplit : Gd u a + (∫ s in a..b,
      |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u s| * ew s) = Gd u b := by
    rw [Gd, Gd]
    exact intervalIntegral.integral_add_adjacent_intervals hia hib
  have hnn : 0 ≤ ∫ s in a..b, |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u s| * ew s := by
    have h := intervalIntegral.integral_mono_on hab
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b) hib
      (fun s hs => mul_nonneg (abs_nonneg _) (ew_nonneg ⟨by linarith [ha, hs.1, Real.pi_pos],
        by linarith [hb, hs.2]⟩))
    simpa using h
  linarith [hsplit, hnn]

/-- `Gd u θ ≥ 0` on `[π/4, π/2)`. -/
theorem Gd_nonneg {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : (Real.pi / 4 : ℝ) ≤ θ) (hθ2 : θ < Real.pi / 2) : 0 ≤ Gd u θ := by
  have hq0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hint : IntervalIntegrable
      (fun s : ℝ => |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u s| * ew s)
      volume (Real.pi / 4) θ :=
    (continuousOn_absRfun_mul_ew hu ⟨hq0, by linarith [Real.pi_pos]⟩
      ⟨by linarith [hθ, hq0], hθ2⟩).intervalIntegrable_of_Icc hθ
  have h := intervalIntegral.integral_mono_on hθ
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (Real.pi / 4) θ) hint
    (fun s hs => mul_nonneg (abs_nonneg _) (ew_nonneg ⟨by linarith [hθ, hs.1, Real.pi_pos],
      by linarith [hθ2, hs.2]⟩))
  simpa [Gd] using h

/-- `Ki θ ≥ 0` on `[π/4, π/2)`. -/
theorem Ki_nonneg {θ : ℝ} (hθ : (Real.pi / 4 : ℝ) ≤ θ) (hθ2 : θ < Real.pi / 2) :
    0 ≤ Ki θ := by
  have hq0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have h := intervalIntegral.integral_mono_on hθ
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (Real.pi / 4) θ)
    ((continuousOn_ek hq0 hθ2).intervalIntegrable_of_Icc hθ)
    (fun s hs => ek_nonneg ⟨by linarith [hθ, hs.1, Real.pi_pos], by linarith [hθ2, hs.2]⟩)
  simpa [Ki] using h

/-- `Ki` is monotone on `[π/4, π/2)`. -/
theorem Ki_mono {a b : ℝ} (ha : (Real.pi / 4 : ℝ) ≤ a) (hb : b < Real.pi / 2) (hab : a ≤ b) :
    Ki a ≤ Ki b := by
  have hq0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hia : IntervalIntegrable ek volume (Real.pi / 4) a :=
    (continuousOn_ek hq0 (by linarith [hab, hb])).intervalIntegrable_of_Icc ha
  have hib : IntervalIntegrable ek volume a b :=
    (continuousOn_ek (by linarith [ha, hq0]) hb).intervalIntegrable_of_Icc hab
  have hsplit : Ki a + (∫ s in a..b, ek s) = Ki b := by
    rw [Ki, Ki]
    exact intervalIntegral.integral_add_adjacent_intervals hia hib
  have hnn : 0 ≤ ∫ s in a..b, ek s := by
    have h := intervalIntegral.integral_mono_on hab
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b)
      ((continuousOn_ek (by linarith [ha, hq0]) hb).intervalIntegrable_of_Icc hab)
      (fun s hs => ek_nonneg ⟨by linarith [ha, hs.1, Real.pi_pos], by linarith [hb, hs.2]⟩)
    simpa using h
  linarith [hsplit, hnn]

/-- **The running bound for `Rfun`** under the eigenrelation: for `θ ∈ [π/4, π/2)`,
`|Rfun u θ| ≤ |Rfun u (π/4)| + (|Dfun u (π/4)| + 2|mu|·Gd u θ)·Ki θ`. -/
theorem Rfun_run_bound {u : ℝ → ℝ} {mu : ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (heig : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ = mu * u θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2)) :
    |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ|
      ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi / 4)|
        + (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ)
          * Ki θ := by
  have hq : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hq0 : (0 : ℝ) < Real.pi / 4 := hq.1
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hftc := Rfun_ftc_ek hu hq hθ' hθ.1
  have h2 : ∀ s ∈ Set.Icc (Real.pi / 4) θ,
      |ek s * (-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s))|
        ≤ (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ)
          * ek s := by
    intro s hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hs.1, Real.pi_pos], by linarith [hθ.2, hs.2]⟩
    have hk : 0 ≤ ek s := ek_nonneg hs'
    have hD := Dfun_run_bound hu heig ⟨hs.1, by linarith [hθ.2, hs.2]⟩
    have hG : Gd u s ≤ Gd u θ := Gd_mono hu hs.1 hθ.2 hs.2
    have h2m : (0 : ℝ) ≤ 2 * |mu| := by positivity
    rw [abs_mul, abs_neg, abs_of_nonneg hk]
    calc ek s * |Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s|
        ≤ ek s * (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u s) :=
          mul_le_mul_of_nonneg_left hD hk
      _ ≤ ek s * (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ) :=
          mul_le_mul_of_nonneg_left
            (by linarith [mul_le_mul_of_nonneg_left hG h2m]) hk
      _ = (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ)
            * ek s := by ring
  have h1 : |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ
        - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi / 4)|
      ≤ ∫ s in (Real.pi / 4)..θ, |ek s * (-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s))| := by
    rw [hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hθ.1
  have hcont1 : ContinuousOn
      (fun s : ℝ => |ek s * (-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s))|)
      (Set.Icc (Real.pi / 4) θ) :=
    (ContinuousOn.mul (continuousOn_ek hq0 hθ.2)
      (((Work.FTS.EllipticEst.H2W.Lzero1Growth.continuousOn_Dfun hu).mono (fun s hs =>
        ⟨by linarith [hs.1, Real.pi_pos], by linarith [hθ.2, hs.2]⟩)).neg)).abs
  have hcont2 : ContinuousOn
      (fun s : ℝ => (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ)
        * ek s) (Set.Icc (Real.pi / 4) θ) :=
    continuousOn_const.mul (continuousOn_ek hq0 hθ.2)
  have hint1 : IntervalIntegrable
      (fun s : ℝ => |ek s * (-(Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u s))|)
      volume (Real.pi / 4) θ :=
    hcont1.intervalIntegrable_of_Icc hθ.1
  have hint2 : IntervalIntegrable
      (fun s : ℝ => (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ)
        * ek s) volume (Real.pi / 4) θ :=
    hcont2.intervalIntegrable_of_Icc hθ.1
  have h3 := intervalIntegral.integral_mono_on hθ.1 hint1 hint2 h2
  have h4 : (∫ s in (Real.pi / 4)..θ,
        (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ) * ek s)
      = (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ) * Ki θ := by
    rw [Ki]
    exact intervalIntegral.integral_const_mul
      (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ) ek
  have hkey : |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ
        - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi / 4)|
      ≤ (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ) * Ki θ :=
    le_trans (le_trans h1 h3) (le_of_eq h4)
  calc |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ|
      = |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi / 4)
          + (Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ
            - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi / 4))| := by
        congr 1
        ring
    _ ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi / 4)|
          + |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u θ
            - Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi / 4)| := abs_add_le _ _
    _ ≤ |Work.FTS.EllipticEst.H2W.LzeroGrowth.Rfun u (Real.pi / 4)|
          + (|Work.FTS.EllipticEst.H2W.LzeroGrowth.Dfun u (Real.pi / 4)| + 2 * |mu| * Gd u θ)
            * Ki θ := add_le_add le_rfl hkey

end

end Work.FTS.EllipticEst.H2W.WeakPureAux
