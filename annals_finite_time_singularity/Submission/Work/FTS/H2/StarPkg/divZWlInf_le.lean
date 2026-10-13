/-
Copyright: work module for the Elgindi finite-time singularity project.

# `(z+1)/z · f` gains one derivative in the `𝒲^{4,∞}`-scale, for the honest data class

`Work.Elliptic.division_by_z` proves `|(z+1)/z · f|_{𝒲^{4,∞}} ≤ 100 |f|_{𝒲^{5,∞}}` under
`Work.Spaces.SmoothNbhd f` (analyticity on a neighbourhood of the closed quadrant) and
`∀ θ, f 0 θ = 0`.  This module proves the same statement for the honest class used by the star
package (`Work.FTS.Nonlin.StarPkg`, see `Submission/Work/FTS/H2/StarPkg/Subst.lean`):

* `Work.FTS.LocData.SmoothQuad f` — genuine `C^∞` on the open quadrant (not `⊤`);
* `Work.FTS.H2.SliceSmooth f` — the `z`-slices are `C^∞` at every `θ ∈ Iθ`, including the two
  boundary lines;
* `f 0 θ = 0` only for `θ ∈ Iθ`.

The one-variable core is the Taylor quotient of `h` at `z = 0`, realised by the parameter
integral `DivExtN h k z = ∫_0^1 t^k h^{(k+1)}(t z) dt`; the proofs of `DivExtN_hasDerivAt`,
`DivExtN_zero_eq_div`, `DivExtN_iteratedDeriv`, `DivExtN_contDiffOn` and `slice_div_z` are the
proofs of `Work.Elliptic.division_by_z` with the analytic order `⊤` replaced by the genuine
smooth order `Work.Stability.smoothOrder = ∞` (which is what a merely `C^∞` datum has).

The angular half of the estimate is `DthIter j g = ((z+1)/z) · DthIter j f` (`D_θ^j` commutes
with a multiplication by a function of `z` alone, `Work.Elliptic.DthIter_mul_zfun`) plus the two
extra facts about the `z`-slices of `DthIter j f` for `j ≥ 1`: they are `C^∞` on `(-1,∞)`
(`sliceSmooth_DthIter`, from `SmoothQuad` on the open quadrant and the vanishing of the `sin 2θ`
factor at the two boundary angles) and they vanish at `z = 0` (`dthIter_zero_apply`, from
`f 0 θ = 0` for `θ ∈ Iθ`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.H2.SliceSmooth
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Elliptic.division_by_z
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.HkAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.H2.StarPkg

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The genuine smooth order `∞` versus the analytic order `⊤` -/

theorem smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]

theorem smoothOrder_add_one :
    Work.Stability.smoothOrder + 1 = Work.Stability.smoothOrder := rfl

theorem natCast_le_smoothOrder (k : ℕ) :
    ((k : ℕ∞) : ℕ∞ω) ≤ Work.Stability.smoothOrder := by
  rw [Work.Stability.smoothOrder]
  exact WithTop.coe_le_coe.mpr le_top

/-! ## The Taylor quotient of a function of one variable, at the genuine smooth order -/

/-- The Taylor quotient of `h` written as a parameter integral:
`DivExtN h k z = ∫_0^1 t^k h^{(k+1)}(t z) dt`.  For `k = 0` this equals `h z / z` for
`z ≠ 0` and gives a smooth extension of the quotient to `z = 0`.  (Identical to
`Work.Elliptic.DivExtN`; duplicated here so that the ported lemmas below refer to it in the
local namespace.) -/
noncomputable def DivExtN (h : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun z => ∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) h (t * z)

/-- Iterated derivatives of a function smooth on `(-1,∞)` are smooth there. -/
theorem iteratedDeriv_contDiffOn_Ioi {h : ℝ → ℝ}
    (hh : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (-1))) (m : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (iteratedDeriv m h) (Set.Ioi (-1)) := by
  induction m with
  | zero => simpa using hh
  | succ m ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen isOpen_Ioi (le_of_eq smoothOrder_add_one)

theorem DivExtN_hasDerivAt (h : ℝ → ℝ) (hh : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (-1))) (k : ℕ)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    HasDerivAt (DivExtN h k) (DivExtN h (k + 1) z) z := by
  have hz' : (-1 : ℝ) < z := hz
  set a : ℝ := min 0 ((z - 1) / 2) with ha
  set b : ℝ := z + 1 with hb
  have ha_le : a ≤ 0 := by rw [ha]; exact min_le_left _ _
  have ha_le' : a ≤ (z - 1) / 2 := by rw [ha]; exact min_le_right _ _
  have ha_gt : -1 < a := by
    rw [ha]; exact lt_min (by norm_num) (by linarith)
  have hb_pos : 0 < b := by rw [hb]; linarith
  have haz : a < z := by linarith
  have hzb : z < b := by rw [hb]; linarith
  have hsub : Set.Icc a b ⊆ Set.Ioi (-1 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1]
  have hcont : ContinuousOn (iteratedDeriv (k + 2) h) (Set.Icc a b) :=
    (iteratedDeriv_contDiffOn_Ioi hh (k + 2)).continuousOn.mono hsub
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hmem : ∀ x ∈ Set.Ioo a b, ∀ t ∈ Set.Icc (0 : ℝ) 1, t * x ∈ Set.Icc a b := by
    intro x hx t ht
    obtain ⟨ht0, ht1⟩ := ht
    obtain ⟨hxa, hxb⟩ := hx
    constructor
    · rcases lt_or_ge 0 x with hx0 | hx0
      · exact le_trans ha_le (mul_nonneg ht0 (le_of_lt hx0))
      · have h1 : x ≤ t * x := by
          nlinarith [mul_nonneg_of_nonpos_of_nonpos hx0
            (show t - 1 ≤ 0 by linarith)]
        linarith
    · rcases lt_or_ge 0 x with hx0 | hx0
      · have h2 : t * x ≤ x := by nlinarith
        linarith
      · have : t * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hx0
        linarith
  have hs_nhds : Set.Ioo a b ∈ 𝓝 z := isOpen_Ioo.mem_nhds ⟨haz, hzb⟩
  have hcontF : ∀ x ∈ Set.Ioo a b,
      ContinuousOn (fun t : ℝ => t ^ k * iteratedDeriv (k + 1) h (t * x))
        (Set.uIcc (0 : ℝ) 1) := by
    intro x hx
    refine ContinuousOn.mul (continuous_pow k).continuousOn ?_
    refine (iteratedDeriv_contDiffOn_Ioi hh (k + 1)).continuousOn.comp
      (continuousOn_id.mul_const x) ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hsub (hmem x hx t ht)
  have hcontG : ContinuousOn
      (fun t : ℝ => t ^ (k + 1) * iteratedDeriv (k + 2) h (t * z)) (Set.uIcc (0 : ℝ) 1) := by
    refine ContinuousOn.mul (continuous_pow (k + 1)).continuousOn ?_
    refine (iteratedDeriv_contDiffOn_Ioi hh (k + 2)).continuousOn.comp
      (continuousOn_id.mul_const z) ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hsub (hmem z ⟨haz, hzb⟩ t ht)
  have huIoc_sub : Set.uIoc (0 : ℝ) 1 ⊆ Set.uIcc (0 : ℝ) 1 := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hIt : ∀ t ∈ Set.uIoc (0 : ℝ) 1, t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun t : ℝ => t ^ k * iteratedDeriv (k + 1) h (t * x))
      ((volume : Measure ℝ).restrict (Set.uIoc 0 1)) := by
    filter_upwards [hs_nhds] with x hx
    exact ((hcontF x hx).mono huIoc_sub).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable
      (fun t : ℝ => t ^ k * iteratedDeriv (k + 1) h (t * z)) volume 0 1 :=
    (hcontF z ⟨haz, hzb⟩).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => t ^ (k + 1) * iteratedDeriv (k + 2) h (t * z))
      ((volume : Measure ℝ).restrict (Set.uIoc 0 1)) :=
    (hcontG.mono huIoc_sub).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ x ∈ Set.Ioo a b, ‖t ^ (k + 1) * iteratedDeriv (k + 2) h (t * x)‖ ≤ C := by
    filter_upwards with t ht x hx
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := hIt t ht
    rw [Real.norm_eq_abs, abs_mul]
    have hpow : |t ^ (k + 1)| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg ht'.1 _)]
      exact pow_le_one₀ ht'.1 ht'.2
    have hg2 : |iteratedDeriv (k + 2) h (t * x)| ≤ C := by
      simpa [Real.norm_eq_abs] using hC (t * x) (hmem x hx t ht')
    calc |t ^ (k + 1)| * |iteratedDeriv (k + 2) h (t * x)| ≤ 1 * C :=
          mul_le_mul hpow hg2 (abs_nonneg _) (by positivity)
      _ = C := one_mul C
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ x ∈ Set.Ioo a b,
        HasDerivAt (fun x : ℝ => t ^ k * iteratedDeriv (k + 1) h (t * x))
          (t ^ (k + 1) * iteratedDeriv (k + 2) h (t * x)) x := by
    filter_upwards with t ht x hx
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := hIt t ht
    have hd : HasDerivAt (iteratedDeriv (k + 1) h)
        (iteratedDeriv (k + 2) h (t * x)) (t * x) := by
      have hdAt : DifferentiableAt ℝ (iteratedDeriv (k + 1) h) (t * x) :=
        ((iteratedDeriv_contDiffOn_Ioi hh (k + 1)).differentiableOn (n := Work.Stability.smoothOrder) smoothOrder_ne_zero).differentiableAt
          (isOpen_Ioi.mem_nhds (hsub (hmem x hx t ht')))
      have h2 : iteratedDeriv (k + 2) h = deriv (iteratedDeriv (k + 1) h) := iteratedDeriv_succ
      rw [h2]
      exact hdAt.hasDerivAt
    have hg : HasDerivAt (fun y : ℝ => t * y) t x := by
      simpa using (hasDerivAt_id x).const_mul t
    have hcomp : HasDerivAt (fun y : ℝ => iteratedDeriv (k + 1) h (t * y))
        (iteratedDeriv (k + 2) h (t * x) * t) x := HasDerivAt.comp x hd hg
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hcomp.const_mul (t ^ k)
  have hkey := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t => t ^ k * iteratedDeriv (k + 1) h (t * x))
    (F' := fun x t => t ^ (k + 1) * iteratedDeriv (k + 2) h (t * x))
    (x₀ := z) (s := Set.Ioo a b) (a := (0 : ℝ)) (b := (1 : ℝ))
    (μ := (volume : Measure ℝ)) (bound := fun _ => C)
    hs_nhds hF_meas hF_int hF'_meas h_bound intervalIntegrable_const hdiff
  exact hkey.2


theorem DivExtN_zero_eq_div (h : ℝ → ℝ) (hh : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (-1))) (hh0 : h 0 = 0)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) (hz0 : z ≠ 0) :
    DivExtN h 0 z = h z / z := by
  have hsubu : Set.uIcc (0 : ℝ) z ⊆ Set.Ioi (-1) := by
    intro x hx
    have hx' : x ∈ Set.Icc (min (0 : ℝ) z) (max (0 : ℝ) z) := hx
    have h1 : -1 < min (0 : ℝ) z := lt_min (by norm_num) hz
    exact lt_of_lt_of_le h1 hx'.1
  have hftc : ∫ x in (0 : ℝ)..z, deriv h x = h z - h 0 := by
    refine intervalIntegral.integral_deriv_eq_sub ?_ ?_
    · intro x hx
      exact (hh.differentiableOn (n := Work.Stability.smoothOrder) smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioi.mem_nhds (hsubu hx))
    · have h1 : IntervalIntegrable (iteratedDeriv 1 h) volume 0 z :=
        ((iteratedDeriv_contDiffOn_Ioi hh 1).continuousOn.mono hsubu).intervalIntegrable
      simpa [iteratedDeriv_one] using h1
  have hsubst : ∫ t in (0 : ℝ)..1, deriv h (t * z) = z⁻¹ * ∫ x in (0 : ℝ)..z, deriv h x := by
    have h1 := intervalIntegral.integral_comp_mul_right (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := deriv h) (c := z) hz0
    simpa using h1
  rw [DivExtN]
  simp only [Nat.zero_add, pow_zero, one_mul, iteratedDeriv_one]
  rw [hsubst, hftc, hh0, sub_zero, div_eq_inv_mul]

/-- The `m`-th derivative of `DivExtN h n` is `DivExtN h (n + m)`. -/
theorem DivExtN_iteratedDeriv (h : ℝ → ℝ) (hh : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (-1))) (m n : ℕ) :
    Set.EqOn (iteratedDeriv m (DivExtN h n)) (DivExtN h (n + m)) (Set.Ioi (-1)) := by
  induction m with
  | zero => intro z hz; simp [DivExtN]
  | succ m ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have hev : (iteratedDeriv m (DivExtN h n)) =ᶠ[𝓝 z] (DivExtN h (n + m)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact ih hw
    rw [hev.deriv_eq, (DivExtN_hasDerivAt h hh (n + m) hz).deriv]
    rw [show n + m + 1 = n + (m + 1) from by omega]

/-- Every `DivExtN h n` is smooth on `(-1,∞)`. -/
theorem DivExtN_contDiffOn (h : ℝ → ℝ) (hh : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (-1))) (n k : ℕ) :
    ContDiffOn ℝ k (DivExtN h n) (Set.Ioi (-1)) := by
  refine contDiffOn_of_differentiableOn_deriv (n := (k : ℕ∞)) ?_
  intro m _
  have h1 : DifferentiableOn ℝ (iteratedDeriv m (DivExtN h n)) (Set.Ioi (-1)) := by
    have h2 : DifferentiableOn ℝ (DivExtN h (n + m)) (Set.Ioi (-1)) := fun z hz =>
      (DivExtN_hasDerivAt h hh (n + m) hz).differentiableAt.differentiableWithinAt
    refine h2.congr ?_
    intro x hx
    exact (DivExtN_iteratedDeriv h hh m n) hx
  refine h1.congr ?_
  intro x hx
  exact iteratedDerivWithin_of_isOpen isOpen_Ioi hx


/-- **The slice estimate.**  If `H` vanishes at `0` and `(u+1)^j H^{(j)}(u) W` is bounded by `M`
for `j = k` and `j = k+1`, then the same bound (with constant `2`) holds for the quotient
`(z+1)/z H` at level `k`. -/
theorem slice_div_z (k : ℕ) (H : ℝ → ℝ) (W M : ℝ) (hW : 0 ≤ W)
    (hH : ContDiffOn ℝ Work.Stability.smoothOrder H (Set.Ioi (-1))) (hH0 : H 0 = 0)
    (hb1 : ∀ z ∈ Set.Ici (0 : ℝ), |(z + 1) ^ k * iteratedDeriv k H z| * W ≤ M)
    (hb2 : ∀ z ∈ Set.Ici (0 : ℝ), |(z + 1) ^ (k + 1) * iteratedDeriv (k + 1) H z| * W ≤ M) :
    ∀ z ∈ Set.Ici (0 : ℝ),
      |(z + 1) ^ k * iteratedDeriv k (fun z => (z + 1) / z * H z) z * W| ≤ 2 * M := by
  have hMnn : 0 ≤ M := by
    have h := hb1 0 (by simp)
    nlinarith [abs_nonneg ((0 + 1) ^ k * iteratedDeriv k H 0), hW, h]
  intro z hz
  rcases lt_or_ge 0 z with hzpos | hzle
  · have hzIoi : z ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
    have hmem : Set.Ioo (z / 2) (3 * z / 2) ∈ 𝓝 z :=
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have hHc : ContDiffAt ℝ k H z :=
      (hH.contDiffAt (isOpen_Ioi.mem_nhds hzIoi)).of_le (natCast_le_smoothOrder k)
    have hqc : ContDiffAt ℝ k (fun w => H w / w) z :=
      hHc.div contDiffAt_id (by simpa using hzpos.ne')
    have hev1 : (fun w : ℝ => (w + 1) / w * H w) =ᶠ[𝓝 z] (fun w => H w + H w / w) := by
      filter_upwards [hmem] with w hw
      have hw0 : w ≠ 0 := ne_of_gt (by linarith [hw.1])
      field_simp
    have hqeq : iteratedDeriv k (fun w => H w / w) z = DivExtN H k z := by
      have hev2 : (fun w : ℝ => H w / w) =ᶠ[𝓝 z] DivExtN H 0 := by
        filter_upwards [hmem] with w hw
        have hw0 : w ≠ 0 := ne_of_gt (by linarith [hw.1])
        have hwIoi : w ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith [hw.1]
        exact (DivExtN_zero_eq_div H hH hH0 hwIoi hw0).symm
      rw [Filter.EventuallyEq.iteratedDeriv_eq k hev2]
      simpa using (DivExtN_iteratedDeriv H hH k 0) hzIoi
    have hsum : iteratedDeriv k (fun w : ℝ => (w + 1) / w * H w) z
        = iteratedDeriv k H z + DivExtN H k z := by
      rw [Filter.EventuallyEq.iteratedDeriv_eq k hev1]
      rw [show (fun w : ℝ => H w + H w / w) = H + (fun w => H w / w) from rfl]
      rw [iteratedDeriv_add hHc hqc]
      rw [hqeq]
    rw [hsum]
    have hDiv : DivExtN H k z = ∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) H (t * z) := rfl
    rw [hDiv]
    have hb1' : |(z + 1) ^ k * iteratedDeriv k H z| * W ≤ M := hb1 z hz
    have hb2' : |(z + 1) ^ k * (∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) H (t * z)) * W|
        ≤ M := Work.Elliptic.divz_integral_bound k H hW hb2 hzpos
    calc |(z + 1) ^ k * (iteratedDeriv k H z
            + ∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) H (t * z)) * W|
        = |(z + 1) ^ k * iteratedDeriv k H z * W
            + (z + 1) ^ k * (∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) H (t * z)) * W| := by
          congr 1; ring
      _ ≤ |(z + 1) ^ k * iteratedDeriv k H z * W|
            + |(z + 1) ^ k * (∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) H (t * z)) * W| :=
          abs_add_le _ _
      _ = |(z + 1) ^ k * iteratedDeriv k H z| * W
            + |(z + 1) ^ k * (∫ t in (0 : ℝ)..1, t ^ k * iteratedDeriv (k + 1) H (t * z)) * W| := by
          rw [abs_mul, abs_of_nonneg hW]
      _ ≤ M + M := add_le_add hb1' hb2'
      _ = 2 * M := by ring
  · have hz0 : z = 0 := le_antisymm hzle hz
    subst hz0
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [iteratedDeriv_zero]
      have hzero : |(0 + 1) ^ 0 * ((0 + 1) / 0 * H 0) * W| = 0 := by simp
      rw [hzero]
      linarith
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      set A : ℝ → ℝ := fun w => H w + DivExtN H 0 w with hA
      have hAc : ContDiffAt ℝ (k' + 1) H 0 :=
        (hH.contDiffAt (isOpen_Ioi.mem_nhds (by norm_num))).of_le (natCast_le_smoothOrder (k' + 1))
      have hDc : ContDiffAt ℝ (k' + 1) (DivExtN H 0) 0 :=
        (DivExtN_contDiffOn H hH 0 (k' + 1)).contDiffAt (isOpen_Ioi.mem_nhds (by norm_num))
      have hFA : ∀ w ∈ Set.Ioo (0 : ℝ) 1, (fun w => (w + 1) / w * H w) w = A w := by
        intro w hw
        have hw0 : w ≠ 0 := ne_of_gt hw.1
        have hwIoi : w ∈ Set.Ioi (-1 : ℝ) := by simp only [Set.mem_Ioi]; linarith [hw.1]
        have hdiv := DivExtN_zero_eq_div H hH hH0 hwIoi hw0
        rw [hA]
        simp only []
        rw [hdiv]
        field_simp
      have hAcd : ContDiffAt ℝ (k' + 1) A 0 := by
        rw [hA]
        exact ContDiffAt.add hAc hDc
      rcases Work.Elliptic.iteratedDeriv_jump (ε := 1) (by norm_num) hFA (show 1 ≤ k' + 1 from by omega) hAcd with hJ | hJ
      · rw [hJ]
        simp only [mul_zero, zero_mul, abs_zero]
        linarith
      · rw [hJ]
        have hAeq : iteratedDeriv (k' + 1) A 0
            = iteratedDeriv (k' + 1) H 0 + DivExtN H (k' + 1) 0 := by
          rw [hA]
          rw [show (fun w : ℝ => H w + DivExtN H 0 w) = H + DivExtN H 0 from rfl]
          rw [iteratedDeriv_add hAc hDc]
          rw [show iteratedDeriv (k' + 1) (DivExtN H 0) 0 = DivExtN H (k' + 1) 0 from by
            simpa using (DivExtN_iteratedDeriv H hH (k' + 1) 0)
              (show (0 : ℝ) ∈ Set.Ioi (-1) from by simp)]
        rw [hAeq]
        have hb1'' : |iteratedDeriv (k' + 1) H 0| * W ≤ M := by
          have h := hb1 0 (by simp)
          simpa using h
        have hb2'' : |DivExtN H (k' + 1) 0| * W ≤ M := by
          have hc : |iteratedDeriv (k' + 2) H 0| * W ≤ M := by
            have h := hb2 0 (by simp)
            simpa using h
          have hintegral : DivExtN H (k' + 1) 0
              = ∫ t in (0 : ℝ)..1, t ^ (k' + 1) * iteratedDeriv (k' + 2) H 0 := by
            simp [DivExtN]
          rw [hintegral]
          have hbd : |∫ t in (0 : ℝ)..1, t ^ (k' + 1) * iteratedDeriv (k' + 2) H 0|
              ≤ |iteratedDeriv (k' + 2) H 0| := by
            have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
              (C := |iteratedDeriv (k' + 2) H 0|)
              (f := fun t : ℝ => t ^ (k' + 1) * iteratedDeriv (k' + 2) H 0) (fun t ht => by
                rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
                rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt ht.1) _)]
                calc t ^ (k' + 1) * |iteratedDeriv (k' + 2) H 0|
                    ≤ 1 * |iteratedDeriv (k' + 2) H 0| :=
                      mul_le_mul_of_nonneg_right (pow_le_one₀ (le_of_lt ht.1) ht.2)
                        (abs_nonneg _)
                  _ = |iteratedDeriv (k' + 2) H 0| := one_mul _)
            simpa using h
          exact le_trans (mul_le_mul_of_nonneg_right hbd hW) hc
        calc |(0 + 1) ^ (k' + 1) * (iteratedDeriv (k' + 1) H 0 + DivExtN H (k' + 1) 0) * W|
            = |iteratedDeriv (k' + 1) H 0 * W + DivExtN H (k' + 1) 0 * W| := by
              congr 1
              norm_num
              ring
          _ ≤ |iteratedDeriv (k' + 1) H 0 * W| + |DivExtN H (k' + 1) 0 * W| := abs_add_le _ _
          _ = |iteratedDeriv (k' + 1) H 0| * W + |DivExtN H (k' + 1) 0| * W := by
              rw [abs_mul, abs_mul, abs_of_nonneg hW]
          _ ≤ M + M := add_le_add hb1'' hb2''
          _ = 2 * M := by ring

/-! ## The `z`-slices of `DthIter j f`, `j ≥ 1` -/

/-- A `z`-slice at an **interior** angle of a function which vanishes on the line `z = 0` for
every `θ ∈ Iθ` has vanishing derivative at that angle: the slice is locally zero. -/
theorem deriv_zslice_zero {F : ℝ → ℝ → ℝ} (hF : ∀ θ ∈ Work.Spaces.Iθ, F 0 θ = 0)
    {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    deriv (fun θ' => F 0 θ') θ = 0 := by
  set d : ℝ := min θ (π / 2 - θ) with hd
  have hdpos : 0 < d := by
    rw [hd]; exact lt_min h0 (by linarith [Real.pi_pos])
  have hsub : Set.Ioo (θ - d) (θ + d) ⊆ Work.Spaces.Iθ := by
    intro t ht
    have hdl : d ≤ θ := by rw [hd]; exact min_le_left _ _
    have hdr : d ≤ π / 2 - θ := by rw [hd]; exact min_le_right _ _
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmem : Set.Ioo (θ - d) (θ + d) ∈ 𝓝 θ :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hev : (fun θ' => F 0 θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmem] with t ht
    exact hF t (hsub ht)
  rw [hev.deriv_eq]
  simp

/-- The `z`-slices of `D_θ^j f` (`j ≥ 1`) are `C^∞` on `(-1,∞)`, at every `θ ∈ Iθ`.  At an
interior angle this is joint smoothness on the open quadrant; at the two boundary angles the
slice vanishes identically because of the factor `sin(2θ)` in `D_θ`. -/
theorem sliceSmooth_DthIter {f : ℝ → ℝ → ℝ} (hQ : Work.FTS.LocData.SmoothQuad f) {j : ℕ}
    (hj : 1 ≤ j) : Work.FTS.H2.SliceSmooth (Work.Spaces.DthIter j f) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | hpos
  · subst h0
    have hfun : (fun z : ℝ => Work.Spaces.DthIter (j' + 1) f z 0) = fun _ => (0 : ℝ) := by
      funext z
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      simp
    rw [hfun]
    exact contDiffOn_const
  · rcases eq_or_lt_of_le hθ.2 with hpi | hlt
    · subst hpi
      have hfun : (fun z : ℝ => Work.Spaces.DthIter (j' + 1) f z (π / 2)) = fun _ => (0 : ℝ) := by
        funext z
        rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
        rw [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi, zero_mul]
      rw [hfun]
      exact contDiffOn_const
    · have hc : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter (j' + 1) f)) Work.Spaces.quadU :=
        Work.FTS.LocData.contDiffOn_DthIter (V := Work.Spaces.quadU)
          Work.Spaces.isOpen_quadU (by simpa [Work.FTS.LocData.SmoothQuad,
            Work.Spaces.quadU] using hQ) (j' + 1)
      have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (-1)) Work.Spaces.quadU :=
        fun z hz => ⟨hz, hpos, hlt⟩
      have hι : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (z, θ))
          (Set.Ioi (-1)) := contDiffOn_id.prodMk contDiffOn_const
      have hcomp := hc.comp hι hmap
      simpa [Function.comp_def, Function.uncurry] using hcomp

/-- `D_θ^j f` vanishes on the line `z = 0` (`j ≥ 1`), for every `θ ∈ Iθ`, when `f` itself does.
The two boundary angles are immediate (the factor `sin(2θ)` of `D_θ` vanishes there); at an
interior angle the slice `θ' ↦ D_θ^j f 0 θ'` is locally zero. -/
theorem dthIter_zero_apply {f : ℝ → ℝ → ℝ} (hf0 : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0) :
    ∀ j : ℕ, 1 ≤ j → ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.DthIter j f 0 θ = 0 := by
  intro j
  induction j with
  | zero => intro hj; omega
  | succ j ih =>
    intro _ θ hθ
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero, Work.Spaces.Dth,
        Work.Spaces.pth]
      rcases eq_or_lt_of_le hθ.1 with h0 | hpos
      · subst h0
        rw [show Real.sin (2 * 0) = 0 from by simp, zero_mul]
      · rcases eq_or_lt_of_le hθ.2 with hpi | hlt
        · subst hpi
          rw [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi, zero_mul]
        · rw [deriv_zslice_zero hf0 hpos hlt, mul_zero]
    · have hih := ih hjpos
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rcases eq_or_lt_of_le hθ.1 with h0 | hpos
      · subst h0
        rw [show Real.sin (2 * 0) = 0 from by simp, zero_mul]
      · rcases eq_or_lt_of_le hθ.2 with hpi | hlt
        · subst hpi
          rw [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi, zero_mul]
        · rw [deriv_zslice_zero hih hpos hlt, mul_zero]

/-! ## The main theorem -/

theorem divZWlInf_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 →
    Work.FTS.LocData.SmoothQuad f →
    Work.FTS.H2.SliceSmooth f →
    (∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0) →
    Work.Spaces.WlInfMem α 5 f →
    Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z * f z θ) ∧
      Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z * f z θ)
        ≤ C * Work.Spaces.WlInf α 5 f := by
  refine ⟨100, by norm_num, ?_⟩
  intro α f hα hα1 hsq hsl hf0 hmem
  set g : ℝ → ℝ → ℝ := fun z θ => (z + 1) / z * f z θ with hg
  set W5 : ℝ := Work.Spaces.WlInf α 5 f with hW5
  have hW5nn : 0 ≤ W5 := by
    rw [hW5, Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 5 f hmem)
      (Work.Spaces.wlThSum_nonneg α 5 f hmem)
  have hZ : ∀ k ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k g z θ| ≤ 2 * W5 := by
    intro k hk z hz θ hθ
    have h1 : Work.Spaces.pzIter k g z θ
        = iteratedDeriv k (fun w => (w + 1) / w * f w θ) z := by
      simp only [Work.Elliptic.pzIter_eq_iteratedDeriv, hg]
    rw [h1]
    have hb1 : ∀ u ∈ Set.Ici (0 : ℝ),
        |(u + 1) ^ k * iteratedDeriv k (fun w => f w θ) u| * 1 ≤ W5 := by
      intro u hu
      have h := Work.Spaces.WlInf_z_bound α 5 f hmem k (by omega) u θ hu hθ
      rw [Work.Elliptic.pzIter_eq_iteratedDeriv] at h
      simpa using h
    have hb2 : ∀ u ∈ Set.Ici (0 : ℝ),
        |(u + 1) ^ (k + 1) * iteratedDeriv (k + 1) (fun w => f w θ) u| * 1 ≤ W5 := by
      intro u hu
      have h := Work.Spaces.WlInf_z_bound α 5 f hmem (k + 1) (by omega) u θ hu hθ
      rw [Work.Elliptic.pzIter_eq_iteratedDeriv] at h
      simpa using h
    simpa using slice_div_z k (fun w => f w θ) 1 W5 (by norm_num)
      (hsl θ hθ) (hf0 θ hθ) hb1 hb2 z hz
  have hW : ∀ (j k : ℕ), 1 ≤ j → k + j ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ 2 * W5 := by
    intro j k hj hjk z hz θ hθ
    have hDj : Work.Spaces.DthIter j g
        = fun z θ => (z + 1) / z * Work.Spaces.DthIter j f z θ := by
      simp only [hg]
      exact Work.Elliptic.DthIter_mul_zfun j (fun z => (z + 1) / z) f
    have h1 : Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
        = iteratedDeriv k (fun w => (w + 1) / w * Work.Spaces.DthIter j f w θ) z := by
      simp only [hDj, Work.Elliptic.pzIter_eq_iteratedDeriv]
    rw [h1]
    have hs : 0 ≤ Real.sin (2 * θ) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hθ.1, hθ.2, Real.pi_pos]
    have hd : 0 < α + Real.sin (2 * θ) := by linarith
    have hb1 : ∀ u ∈ Set.Ici (0 : ℝ),
        |(u + 1) ^ k * iteratedDeriv k (fun w => Work.Spaces.DthIter j f w θ) u|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ W5 := by
      intro u hu
      have h := Work.Spaces.WlInf_mixed_bound α 5 f hmem j k hj (by omega) u θ hu hθ
      rw [Work.Elliptic.pzIter_eq_iteratedDeriv] at h
      have habs : |(u + 1) ^ k * iteratedDeriv k (fun w => Work.Spaces.DthIter j f w θ) u
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          = |(u + 1) ^ k * iteratedDeriv k (fun w => Work.Spaces.DthIter j f w θ) u|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
        rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs _), abs_of_pos hd]
        ring
      rw [← habs]
      exact h
    have hb2 : ∀ u ∈ Set.Ici (0 : ℝ),
        |(u + 1) ^ (k + 1) * iteratedDeriv (k + 1) (fun w => Work.Spaces.DthIter j f w θ) u|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ W5 := by
      intro u hu
      have h := Work.Spaces.WlInf_mixed_bound α 5 f hmem j (k + 1) hj (by omega) u θ hu hθ
      rw [Work.Elliptic.pzIter_eq_iteratedDeriv] at h
      have habs : |(u + 1) ^ (k + 1)
            * iteratedDeriv (k + 1) (fun w => Work.Spaces.DthIter j f w θ) u
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          = |(u + 1) ^ (k + 1) * iteratedDeriv (k + 1) (fun w => Work.Spaces.DthIter j f w θ) u|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
        rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs _), abs_of_pos hd]
        ring
      rw [← habs]
      exact h
    simpa [mul_div_assoc] using slice_div_z k (fun w => Work.Spaces.DthIter j f w θ)
      ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) W5
      (Work.Elliptic.sin_weight_nonneg hα hθ)
      (sliceSmooth_DthIter hsq hj θ hθ)
      (dthIter_zero_apply hf0 j hj θ hθ) hb1 hb2 z hz
  have hmemg : Work.Spaces.WlInfMem α 4 g := by
    refine ⟨fun k hk => Work.Spaces.supFinite_of_pointwise (hZ k hk), ?_⟩
    intro j hj k hk hj1 hjk
    exact Work.Spaces.supFinite_of_pointwise (hW j k hj1 hjk)
  have hbound : Work.Spaces.WlInf α 4 g ≤ 100 * W5 := by
    have h1 : (∑ k ∈ Finset.range (4 + 1),
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k g z θ)) ≤ 50 * W5 := by
      calc (∑ k ∈ Finset.range (4 + 1),
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k g z θ))
          ≤ ∑ k ∈ Finset.range (4 + 1), (2 * W5) :=
            Finset.sum_le_sum fun k hk =>
              Work.Spaces.supAbs_le (hZ k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
        _ = 5 * (2 * W5) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
        _ ≤ 50 * W5 := by linarith
    have h2 : (∑ j ∈ Finset.range (4 + 1), ∑ k ∈ Finset.range (4 + 1),
            if 1 ≤ j ∧ k + j ≤ 4 then
              Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
                * Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            else 0) ≤ 50 * W5 := by
      calc (∑ j ∈ Finset.range (4 + 1), ∑ k ∈ Finset.range (4 + 1),
            if 1 ≤ j ∧ k + j ≤ 4 then
              Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
                * Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
            else 0)
          ≤ ∑ j ∈ Finset.range (4 + 1), ∑ k ∈ Finset.range (4 + 1), (2 * W5) := by
            refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
            by_cases h : 1 ≤ j ∧ k + j ≤ 4
            · rw [if_pos h]
              exact Work.Spaces.supAbs_le (hW j k h.1 h.2)
            · rw [if_neg h]
              linarith
        _ = 25 * (2 * W5) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
              Finset.card_range, nsmul_eq_mul]
            ring
        _ ≤ 50 * W5 := by linarith
    rw [Work.Spaces.WlInf]
    linarith
  exact ⟨hmemg, hbound⟩

end Work.FTS.H2.StarPkg
