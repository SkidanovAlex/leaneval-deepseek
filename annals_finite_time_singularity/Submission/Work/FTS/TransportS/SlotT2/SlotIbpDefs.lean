/-
Copyright: work module for the Elgindi finite-time singularity project.

# The per-slot radial integration by parts of the `D_z`-transport hard part

For a single slot `k : Fin 5` the top (order-`5`) term of the `D_z`-transport pairing is

`∫_z ∫_θ w(z)² · sghard α k θ · f z θ · D_z (Thard g k) z θ · Thard g k z θ`

(`ps` below).  Because `D_z = z ∂_z` and `∂_z (V²) = 2 V ∂_z V`, the integrand is a total
`z`-derivative:

`ps α f g k z θ = ∂_z (ZG α f g k · θ) z - ZE α f g k z θ`,

with `ZG` the primitive and `ZE` the correction (`∂_z (f z w²) = D_z f · w² + f · w² · (z-3)/(1+z)`).
Integrating over `z ∈ (0,∞)` (the two boundary terms die because the primitive `z ↦ ∫_θ ZG` has
limit `0` at both ends, which follows from the finiteness of `∫_z w² ∫_θ (Thard g k)² sghard α k`
— this is the content of `Work.FTS.H2.ZibpLimit`) gives

`∫_z ∫_θ ps = - ∫_z ∫_θ ZE`,

and the correction obeys the pointwise bound `|ZE| ≤ 2 Mf · (Xz α g k)²`, where
`(Xz α g k)² = (Thard g k)² w² sghard α k` is a single summand of `HkIntegrand α 4 g`
(`Work.FTS.TransportS.Xz_sq`).  Hence `|∫ ps| ≤ 2 Mf · HkSq α 4 g`.

This module contains the definitions (`ZG`, `ZE`, `ps`) together with the *elementary*
infrastructure (the pointwise bounds, the continuity of the uncurried blocks on the open
quadrant, the a.e. strong measurability of the blocks and of their slices, and the slice
integrability coming from `HkMem α 4 g`/`HkMem α 5 g`) on which the four deferred pieces
(`slot_ZG_deriv`, `slot_data`, `slot_zibp_funeq`, `ZGLimitZero`) are stated.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.SlotT2

set_option autoImplicit false

/-! ## The three blocks -/

/-- The primitive of the `k`-th hard slot: `½ f z w² (Thard g k)² sghard α k`. -/
def ZG (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) : ℝ :=
  (1 / 2) * f z θ * z * (Work.Spaces.w z) ^ 2
    * (Work.FTS.H2.Thard g k z θ) ^ 2 * Work.FTS.H2.sghard α k θ

/-- The correction term of the `k`-th hard slot:
`½ (D_z f · w² + f · w² (z-3)/(1+z)) (Thard g k)² sghard α k`. -/
def ZE (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) : ℝ :=
  (1 / 2) * (Work.Spaces.Dz f z θ * (Work.Spaces.w z) ^ 2
      + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))
    * (Work.FTS.H2.Thard g k z θ) ^ 2 * Work.FTS.H2.sghard α k θ

/-- The integrand of the `k`-th hard-slot pairing (the integrand of the target statement). -/
def ps (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ * f z θ
    * Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ * Work.FTS.H2.Thard g k z θ

/-- The angular energy of the `k`-th slot as a function of `z`:
`∫_θ (Xz α g k z θ)² = ∫_θ (Thard g k z θ)² w(z)² sghard α k θ`. -/
def angE (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Xz α g k z θ) ^ 2

/-! ## Elementary pointwise identities -/

/-- `ps` is the coefficient `f` times the product of the two weighted slot factors. -/
theorem ps_eq_mul {α : ℝ} (f g : ℝ → ℝ → ℝ) (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    ps α f g k z θ = f z θ * (Xz α g k z θ * Yz α g k z θ) := by
  have h : Xz α g k z θ * Yz α g k z θ
      = Work.FTS.H2.Thard g k z θ * Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ
        * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ := Xz_mul_Yz (α := α) g k z θ hθ
  rw [ps, h]
  ring

/-- `ZG` is `½ f z` times the square of the order-`4` weighted slot factor. -/
theorem ZG_eq {α : ℝ} (f g : ℝ → ℝ → ℝ) (k : Fin 5) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    ZG α f g k z θ = (1 / 2) * f z θ * z * (Xz α g k z θ) ^ 2 := by
  rw [ZG, Xz_sq (α := α) g k z θ hθ]
  ring

/-- `ZE` is `½ (D_z f · w² + f w² (z-3)/(1+z))` times the square of the order-`4` weighted
slot factor, divided by `w²`. -/
theorem ZE_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) :
    ZE α f g k z θ
      = (1 / 2) * (Work.Spaces.Dz f z θ * (Work.Spaces.w z) ^ 2
          + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))
        * (Work.FTS.H2.Thard g k z θ) ^ 2 * Work.FTS.H2.sghard α k θ := rfl

theorem w_sq_nonneg (z : ℝ) : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _

/-- The pointwise bound on the primitive. -/
theorem abs_ZG_le {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (k : Fin 5) (hMf : 0 ≤ Mf) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) (hf : |f z θ| ≤ Mf) :
    |ZG α f g k z θ| ≤ (Mf / 2) * z * (Xz α g k z θ) ^ 2 := by
  have hnn : 0 ≤ (Xz α g k z θ) ^ 2 := sq_nonneg _
  rw [ZG_eq f g k hθ, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_of_pos hz, abs_of_nonneg hnn]
  have h1 : (1 / 2) * |f z θ| ≤ Mf / 2 := by linarith
  calc (1 / 2) * |f z θ| * z * (Xz α g k z θ) ^ 2
      = ((1 / 2) * |f z θ|) * (z * (Xz α g k z θ) ^ 2) := by ring
    _ ≤ (Mf / 2) * (z * (Xz α g k z θ) ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg hz.le hnn)
    _ = (Mf / 2) * z * (Xz α g k z θ) ^ 2 := by ring

/-- The `if`-form of `Xz`, unfolded at a point. -/
theorem Xz_apply_ite (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) :
    Xz α g k z θ = if k.val = 0 then Work.Spaces.DzIter 4 g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      else Work.Spaces.mixed (4 - k.val) k.val g z θ * Work.Spaces.Wt α z θ := by
  by_cases hk : k.val = 0
  · simp only [Xz, if_pos hk, Work.Spaces.mixed_zero_right, if_pos hk]
  · simp only [Xz, if_neg hk, if_neg hk]

/-- The `if`-form of `Yz`, unfolded at a point. -/
theorem Yz_apply_ite (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) :
    Yz α g k z θ = if k.val = 0 then Work.Spaces.DzIter 5 g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      else Work.Spaces.mixed (5 - k.val) k.val g z θ * Work.Spaces.Wt α z θ := by
  by_cases hk : k.val = 0
  · simp only [Yz, if_pos hk, Work.Spaces.mixed_zero_right, if_pos hk]
  · simp only [Yz, if_neg hk, if_neg hk]

/-- The pointwise bound on the correction term.  Note the *strong* hypothesis `|D_z f| ≤ Mf`,
which makes the term `z ∂_z f · w²` bounded: this is why the statement of the target lemma
carries a bound on `D_z f` and not only on `f`. -/
theorem abs_ZE_le {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (k : Fin 5) (hMf : 0 ≤ Mf) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) (hf : |f z θ| ≤ Mf)
    (hDf : |Work.Spaces.Dz f z θ| ≤ Mf) :
    |ZE α f g k z θ| ≤ 2 * Mf * (Xz α g k z θ) ^ 2 := by
  have hsgh : 0 ≤ Work.FTS.H2.sghard α k θ := Work.FTS.H2.sghard_nonneg α k hθ
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hV2 : 0 ≤ (Work.FTS.H2.Thard g k z θ) ^ 2 := sq_nonneg _
  have hVE : (Work.FTS.H2.Thard g k z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      * Work.FTS.H2.sghard α k θ = (Xz α g k z θ) ^ 2 := by
    rw [Xz_sq (α := α) g k z θ hθ]
  have hratio : |(z - 3) / (1 + z)| ≤ 3 := by
    have hz1 : (0 : ℝ) < 1 + z := by linarith
    rw [abs_div, abs_of_pos hz1, div_le_iff₀ hz1, abs_le]
    constructor <;> linarith
  have h2 : |Work.Spaces.Dz f z θ * (Work.Spaces.w z) ^ 2| ≤ Mf * (Work.Spaces.w z) ^ 2 := by
    rw [abs_mul, abs_of_nonneg hw2]
    exact mul_le_mul_of_nonneg_right hDf hw2
  have h3 : |f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
      ≤ 3 * Mf * (Work.Spaces.w z) ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw2]
    calc |f z θ| * ((Work.Spaces.w z) ^ 2 * |(z - 3) / (1 + z)|)
        ≤ Mf * ((Work.Spaces.w z) ^ 2 * 3) := by
          refine mul_le_mul hf (mul_le_mul_of_nonneg_left hratio hw2)
            (mul_nonneg hw2 (abs_nonneg _)) hMf
      _ = 3 * Mf * (Work.Spaces.w z) ^ 2 := by ring
  have h1 : |Work.Spaces.Dz f z θ * (Work.Spaces.w z) ^ 2
      + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
      ≤ 4 * Mf * (Work.Spaces.w z) ^ 2 := by
    calc _ ≤ |Work.Spaces.Dz f z θ * (Work.Spaces.w z) ^ 2|
          + |f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))| := abs_add_le _ _
      _ ≤ Mf * (Work.Spaces.w z) ^ 2 + 3 * Mf * (Work.Spaces.w z) ^ 2 := add_le_add h2 h3
      _ = 4 * Mf * (Work.Spaces.w z) ^ 2 := by ring
  have hmain : |ZE α f g k z θ|
      = (1 / 2) * |Work.Spaces.Dz f z θ * (Work.Spaces.w z) ^ 2
          + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
        * (Work.FTS.H2.Thard g k z θ) ^ 2 * Work.FTS.H2.sghard α k θ := by
    rw [ZE_eq, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      abs_of_nonneg hV2, abs_of_nonneg hsgh]
  rw [hmain]
  calc (1 / 2) * |Work.Spaces.Dz f z θ * (Work.Spaces.w z) ^ 2
        + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
        * (Work.FTS.H2.Thard g k z θ) ^ 2 * Work.FTS.H2.sghard α k θ
      ≤ (1 / 2) * (4 * Mf * (Work.Spaces.w z) ^ 2)
          * (Work.FTS.H2.Thard g k z θ) ^ 2 * Work.FTS.H2.sghard α k θ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1 (by norm_num)) hV2) hsgh
    _ = 2 * Mf * (Xz α g k z θ) ^ 2 := by
        rw [← hVE]
        ring

/-! ## Continuity of the uncurried blocks on the open quadrant -/

theorem continuousOn_sghard_Qd' (α : ℝ) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.sghard α k p.2) Work.FTS.LocData.Qd :=
  continuousOn_sghard_Qd α k

theorem continuousOn_Thard_Qd' {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.Thard g k p.1 p.2) Work.FTS.LocData.Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.FTS.H2.Thard g k p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.mixed (4 - k.val) k.val g p.1 p.2 := by
    funext p
    simp only [Work.FTS.H2.Thard_eq_mixed]
  rw [hfun]
  exact (hg.mixed (4 - k.val) k.val).continuousOn

theorem continuousOn_Xz_Qd' {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Xz α g k p.1 p.2) Work.FTS.LocData.Qd := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hfun : (fun p : ℝ × ℝ => Xz α g k p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.DzIter 4 g p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) := by
      funext p
      simp only [Xz_apply_ite, if_pos hk, Work.Spaces.mixed_zero_right]
    rw [hfun]
    exact ((hg.mixed 4 0).continuousOn).mul continuousOn_wdivsin_Qd
  · have hfun : (fun p : ℝ × ℝ => Xz α g k p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.mixed (4 - k.val) k.val g p.1 p.2
            * Work.Spaces.Wt α p.1 p.2 := by
      funext p
      simp only [Xz_apply_ite, if_neg hk]
    rw [hfun]
    exact ((hg.mixed (4 - k.val) k.val).continuousOn).mul (continuousOn_Wt_Qd α)

theorem continuousOn_Yz_Qd' {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Yz α g k p.1 p.2) Work.FTS.LocData.Qd := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hfun : (fun p : ℝ × ℝ => Yz α g k p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.DzIter 5 g p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) := by
      funext p
      simp only [Yz_apply_ite, if_pos hk, Work.Spaces.mixed_zero_right]
    rw [hfun]
    exact ((hg.mixed 5 0).continuousOn).mul continuousOn_wdivsin_Qd
  · have hfun : (fun p : ℝ × ℝ => Yz α g k p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.mixed (5 - k.val) k.val g p.1 p.2
            * Work.Spaces.Wt α p.1 p.2 := by
      funext p
      simp only [Yz_apply_ite, if_neg hk]
    rw [hfun]
    exact ((hg.mixed (5 - k.val) k.val).continuousOn).mul (continuousOn_Wt_Qd α)

theorem continuousOn_ps_Qd {α : ℝ} {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => ps α f g k p.1 p.2) Work.FTS.LocData.Qd := by
  have hfun : (fun p : ℝ × ℝ => ps α f g k p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2 * Work.FTS.H2.sghard α k p.2 * f p.1 p.2
          * Work.Spaces.mixed (5 - k.val) k.val g p.1 p.2
          * Work.FTS.H2.Thard g k p.1 p.2 := by
    funext p
    simp only [ps, Dz_Thard_apply]
  rw [hfun]
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2
      * Work.FTS.H2.sghard α k p.2) Work.FTS.LocData.Qd :=
    continuousOn_w_sq_Qd.mul (continuousOn_sghard_Qd α k)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed (5 - k.val) k.val g p.1 p.2)
      Work.FTS.LocData.Qd := (hg.mixed (5 - k.val) k.val).continuousOn
  exact (((h1.mul hf.continuousOn).mul h2)).mul (continuousOn_Thard_Qd' hg k)

theorem continuousOn_ZE_Qd {α : ℝ} {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => ZE α f g k p.1 p.2) Work.FTS.LocData.Qd := by
  have hratio : ContinuousOn (fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1)) Work.FTS.LocData.Qd :=
    ContinuousOn.div (continuousOn_fst.sub continuousOn_const)
      (continuousOn_const.add continuousOn_fst) (fun p hp => by
        have h1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp).1
        linarith)
  have hfun : (fun p : ℝ × ℝ => ZE α f g k p.1 p.2)
      = fun p : ℝ × ℝ => (1 / 2) * (Work.Spaces.Dz f p.1 p.2 * Work.Spaces.w p.1 ^ 2
          + f p.1 p.2 * (Work.Spaces.w p.1 ^ 2 * ((p.1 - 3) / (1 + p.1))))
          * (Work.FTS.H2.Thard g k p.1 p.2) ^ 2 * Work.FTS.H2.sghard α k p.2 := by
    funext p
    simp only [ZE_eq]
  rw [hfun]
  have h1 : ContinuousOn (fun p : ℝ × ℝ => (1 / 2) * (Work.Spaces.Dz f p.1 p.2
      * Work.Spaces.w p.1 ^ 2
      + f p.1 p.2 * (Work.Spaces.w p.1 ^ 2 * ((p.1 - 3) / (1 + p.1))))) Work.FTS.LocData.Qd :=
    (continuousOn_const (c := (1 / 2 : ℝ))).mul
      (((hf.Dz.continuousOn).mul continuousOn_w_sq_Qd).add
        (hf.continuousOn.mul (continuousOn_w_sq_Qd.mul hratio)))
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (Work.FTS.H2.Thard g k p.1 p.2) ^ 2)
      Work.FTS.LocData.Qd := (continuousOn_Thard_Qd' hg k).pow 2
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.sghard α k p.2) Work.FTS.LocData.Qd :=
    continuousOn_sghard_Qd α k
  exact (h1.mul h2).mul h3

theorem continuousOn_ZG_Qd {α : ℝ} {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => ZG α f g k p.1 p.2) Work.FTS.LocData.Qd := by
  have hfun : (fun p : ℝ × ℝ => ZG α f g k p.1 p.2)
      = fun p : ℝ × ℝ => (1 / 2) * f p.1 p.2 * p.1 * Work.Spaces.w p.1 ^ 2
          * (Work.FTS.H2.Thard g k p.1 p.2) ^ 2 * Work.FTS.H2.sghard α k p.2 := by
    funext p
    simp only [ZG]
  rw [hfun]
  have h1 : ContinuousOn (fun p : ℝ × ℝ => (1 / 2) * f p.1 p.2) Work.FTS.LocData.Qd :=
    (continuousOn_const (c := (1 / 2 : ℝ))).mul hf.continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => p.1) Work.FTS.LocData.Qd := continuousOn_fst
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2) Work.FTS.LocData.Qd :=
    continuousOn_w_sq_Qd
  have h4 : ContinuousOn (fun p : ℝ × ℝ => (Work.FTS.H2.Thard g k p.1 p.2) ^ 2)
      Work.FTS.LocData.Qd := (continuousOn_Thard_Qd' hg k).pow 2
  have h5 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.sghard α k p.2) Work.FTS.LocData.Qd :=
    continuousOn_sghard_Qd α k
  exact (((h1.mul h2).mul h3).mul h4).mul h5

/-! ## A.e. strong measurability of the blocks and of their slices -/

theorem aesm_Xz_sq_prod {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (k : Fin 5) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => (Xz α g k p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ ((continuousOn_Xz_Qd' hg k).pow 2)

theorem aesm_Yz_sq_prod {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (k : Fin 5) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => (Yz α g k p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ ((continuousOn_Yz_Qd' hg k).pow 2)

theorem aesm_ps_prod {α : ℝ} {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => ps α f g k p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_ps_Qd hf hg k)

theorem aesm_ZE_prod {α : ℝ} {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => ZE α f g k p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_ZE_Qd hf hg k)

theorem aesm_slice_Xz_sq {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (k : Fin 5) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => (Xz α g k z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
  (Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_Xz_Qd' hg k) hz).pow 2

theorem aesm_slice_Yz_sq {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (k : Fin 5) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => (Yz α g k z θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
  (Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_Yz_Qd' hg k) hz).pow 2

theorem aesm_slice_ZE {α : ℝ} {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => ZE α f g k z θ) (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_ZE_Qd hf hg k) hz

theorem aesm_slice_ps {α : ℝ} {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => ps α f g k z θ) (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_ps_Qd hf hg k) hz

theorem aesm_slice_ZG {α : ℝ} {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (k : Fin 5) {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ : ℝ => ZG α f g k z θ) (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_ZG_Qd hf hg k) hz

/-! ## The vanishing of the blocks at `z = 0` -/

theorem Xz_zero_z (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) (θ : ℝ) :
    Xz α g k 0 θ = 0 := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    rw [Xz_apply_zero]
    simp [Work.Spaces.w]
  · rw [Xz_apply_ne hk]
    simp [Work.Spaces.w, Work.Spaces.Wt]

theorem Yz_zero_z (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) (θ : ℝ) :
    Yz α g k 0 θ = 0 := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    rw [Yz_apply_zero]
    simp [Work.Spaces.w]
  · rw [Yz_apply_ne hk]
    simp [Work.Spaces.w, Work.Spaces.Wt]

theorem ZG_zero_z (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) (θ : ℝ) :
    ZG α f g k 0 θ = 0 := by
  rw [ZG]
  ring

/-! ## Slice integrability coming from `HkMem` -/

/-- The θ-slice of the square of the order-`4` weighted slot factor is integrable, for every
`z ∈ Iz`, as soon as `g ∈ ℋ⁴`. -/
theorem integrableOn_Xz_sq_slice {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hg4 : Work.Spaces.HkMem α 4 g) (k : Fin 5) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ : ℝ => (Xz α g k z θ) ^ 2) Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hz0' : z = 0 := hz0.symm
    subst hz0'
    rw [show (fun θ : ℝ => (Xz α g k 0 θ) ^ 2) = fun _ : ℝ => (0 : ℝ) from by
      funext θ; rw [Xz_zero_z, sq]; ring]
    exact integrableOn_zero
  · refine Integrable.mono' (hg4.1 z hz) (aesm_slice_Xz_sq hg k hzpos) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
      measurableSet_Icc)] with θ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Xz_sq_le_HkIntegrand4 α g k z θ

/-- The θ-slice of the square of the order-`5` weighted slot factor is integrable, for every
`z ∈ Iz`, as soon as `g ∈ ℋ⁵`. -/
theorem integrableOn_Yz_sq_slice {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hg5 : Work.Spaces.HkMem α 5 g) (k : Fin 5) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ : ℝ => (Yz α g k z θ) ^ 2) Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hz0' : z = 0 := hz0.symm
    subst hz0'
    rw [show (fun θ : ℝ => (Yz α g k 0 θ) ^ 2) = fun _ : ℝ => (0 : ℝ) from by
      funext θ; rw [Yz_zero_z, sq]; ring]
    exact integrableOn_zero
  · refine Integrable.mono' (hg5.1 z hz) (aesm_slice_Yz_sq hg k hzpos) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
      measurableSet_Icc)] with θ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Yz_sq_le_HkIntegrand α g k z θ

/-- The θ-slice of the primitive `ZG` is integrable for every `z ∈ Iz`, from `g ∈ ℋ⁴` and the
bound on `f`. -/
theorem integrableOn_ZG_slice {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (k : Fin 5) (hMf : 0 ≤ Mf)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hg4 : Work.Spaces.HkMem α 4 g)
    (hfb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ : ℝ => ZG α f g k z θ) Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hz0' : z = 0 := hz0.symm
    subst hz0'
    rw [show (fun θ : ℝ => ZG α f g k 0 θ) = fun _ : ℝ => (0 : ℝ) from by
      funext θ; exact ZG_zero_z α f g k θ]
    exact integrableOn_zero
  · refine Integrable.mono'
      ((integrableOn_Xz_sq_slice hg hg4 k hz).const_mul ((Mf / 2) * z))
      (aesm_slice_ZG hf hg k hzpos) ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    rw [Real.norm_eq_abs]
    exact abs_ZG_le k hMf hzpos ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ (hfb z θ hzpos hθ.1 hθ.2)

/-- The bound on the θ-integral of the primitive. -/
theorem abs_int_ZG_le {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (k : Fin 5) (hMf : 0 ≤ Mf)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hg4 : Work.Spaces.HkMem α 4 g)
    (hfb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    {z : ℝ} (hz : 0 < z) :
    |∫ θ in Work.Spaces.Iθ, ZG α f g k z θ|
      ≤ (Mf / 2) * z * ∫ θ in Work.Spaces.Iθ, (Xz α g k z θ) ^ 2 := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hb : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      |ZG α f g k z θ| ≤ (Mf / 2) * z * (Xz α g k z θ) ^ 2 := by
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    exact abs_ZG_le k hMf hz ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ (hfb z θ hz hθ.1 hθ.2)
  calc |∫ θ in Work.Spaces.Iθ, ZG α f g k z θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |ZG α f g k z θ| := abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ, (Mf / 2) * z * (Xz α g k z θ) ^ 2 :=
        MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => abs_nonneg _)
          ((integrableOn_Xz_sq_slice hg hg4 k hzI).const_mul _) hb
    _ = (Mf / 2) * z * ∫ θ in Work.Spaces.Iθ, (Xz α g k z θ) ^ 2 :=
        MeasureTheory.integral_const_mul _ _

end Work.FTS.TransportS.SlotT2
