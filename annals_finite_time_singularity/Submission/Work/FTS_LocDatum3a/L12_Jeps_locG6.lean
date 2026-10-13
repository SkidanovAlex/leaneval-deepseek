/-
# `L₁₂(J_ε (locG6))(0) = 0` for the localised order-`6` datum

This file proves clause `l12` of the interface for the mollified datum
(`Work.FTS_LocDatum3a.LEAD_LocDatum3a_stmts.lean.txt`, second theorem):

  `L₁₂(locG6 α L β)(0) = 0`  ⟹  `L₁₂(J_ε(locG6 α L β))(0) = 0`.

The datum is *separable* (`Work.FTS.LocDataExt.locG_eq_locR_Gam`):

  `locG6 α L β = locR α L β(z) · Γ(θ)`,

and `L₁₂` of a separable datum factorises:

  `L₁₂(R·G)(0) = (∫_0^{π/2} K(θ)G(θ) dθ) · (∫_0^{∞} R(s)/s ds)`

(`L12_sep_mul` below), with `∫_0^{π/2} K Γ = c(α) > 0`.  Hence the hypothesis
`L₁₂(locG6)(0) = 0` is exactly the statement `∫_0^{∞} locR(s)/s ds = 0`
(`locR_Lambda_zero`).

The mollifier `J_ε` is a convolution in the log-coordinates `(log z, log tan θ)`; the
`z`-part of the convolution is the *translation* of the measure `ds/s` on `(0,∞)`, so it
leaves `∫ R(s)/s ds` invariant and the angular part factors out.  The resulting identity
is `Work.FTS_LocDatum3a.L12_Jeps_interchange_meas` (proved in the sibling module):

  `L₁₂(J_ε F)(0) = ∫_p Jker ρ ε p · L₁₂(shift_p F)(0)`,

`shift_p F (z,θ) = F(z e^{-p₁}, arctan(tan θ e^{-p₂}))`, and the shifted function of a
separable datum is again separable, so its `L₁₂(·)(0)` is
`(∫ R(s)/s ds)·(∫_0^{π/2} K(θ)G(thShift θ p₂) dθ)` (`L12_sep_mul_shift`, using the scaling
invariance `∫ R(c s)/s ds = ∫ R(s)/s ds` of `Work.FTS_LocDatum3a.integral_comp_mul_Ioi`).
The result is `(∫ R(s)/s ds) · ∫_p Jker ρ ε p (…)`, which vanishes as soon as `∫ R(s)/s ds = 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.LocData6.Main
import Submission.Work.FTS_LocDatum3a.integral_comp_mul_Ioi
import Submission.Work.FTS_LocDatum3a.L12_Jeps_interchange_mine

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false

/-! ## `L₁₂` of a separable datum -/

/-- The angular density of a separable datum: `L₁₂dens(K)(R·G)(s) = (R(s)/s)·∫_θ K(θ)G(θ)`. -/
lemma L12dens_sep_mul (R G : ℝ → ℝ) (s : ℝ) :
    Work.FM.L12dens Work.Spaces.K (fun z θ => R z * G θ) s
      = (R s / s) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ) := by
  simp only [Work.FM.L12dens, Work.Spaces.Iθ]
  rw [show (∫ θ in Set.Icc (0 : ℝ) (π / 2), Work.Spaces.K θ * (R s * G θ) / s)
      = ∫ θ in Set.Icc (0 : ℝ) (π / 2), (R s / s) * (Work.Spaces.K θ * G θ) from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]

/-- **`L₁₂` of a separable datum**: `L₁₂(R·G)(0) = (∫_θ K G)·(∫_s R(s)/s)`. -/
lemma L12_sep_mul (R G : ℝ → ℝ) :
    Work.FM.L12 Work.Spaces.K (fun z θ => R z * G θ) 0
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ) * (∫ s in Set.Ioi (0 : ℝ), R s / s) := by
  simp only [Work.FM.L12]
  rw [show (∫ s in Set.Ioi (0 : ℝ), Work.FM.L12dens Work.Spaces.K (fun z θ => R z * G θ) s)
      = ∫ s in Set.Ioi (0 : ℝ), (R s / s) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ) from
    setIntegral_congr_fun measurableSet_Ioi (fun s _ => L12dens_sep_mul R G s)]
  rw [MeasureTheory.integral_mul_const]
  exact mul_comm _ _

/-- The same computation for a datum already *shifted* in the log-coordinates:
`L₁₂ (z ↦ R(z e^{-p₁}) · G(thShift · p₂))(0) = (∫_s R(s)/s)·(∫_θ K(θ)G(thShift θ p₂))`.
The `z`-integral is invariant under `s ↦ c s` for `ds/s`
(`Work.FTS_LocDatum3a.integral_comp_mul_Ioi`). -/
lemma L12_sep_mul_shift (R G : ℝ → ℝ) (p₁ p₂ : ℝ) :
    Work.FM.L12 Work.Spaces.K
        (fun z θ => R (Work.FTS.StrongEps.zShift z p₁) * G (Work.FTS.StrongEps.thShift θ p₂)) 0
      = (∫ s in Set.Ioi (0 : ℝ), R s / s)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G (Work.FTS.StrongEps.thShift θ p₂)) := by
  have hc : (0 : ℝ) < Real.exp (-p₁) := Real.exp_pos _
  have hswap : (∫ s in Set.Ioi (0 : ℝ), R (Work.FTS.StrongEps.zShift s p₁) / s)
      = ∫ s in Set.Ioi (0 : ℝ), R s / s := by
    rw [show (∫ s in Set.Ioi (0 : ℝ), R (Work.FTS.StrongEps.zShift s p₁) / s)
        = ∫ s in Set.Ioi (0 : ℝ), R (Real.exp (-p₁) * s) / s from
      setIntegral_congr_fun measurableSet_Ioi
        (fun s _ => by rw [Work.FTS.StrongEps.zShift, mul_comm])]
    exact integral_comp_mul_Ioi hc R
  rw [L12_sep_mul (fun z => R (Work.FTS.StrongEps.zShift z p₁))
      (fun θ => G (Work.FTS.StrongEps.thShift θ p₂)), hswap]
  ring

/-- The normalisation constant `c(α)` with the factors in the order used by `L₁₂dens`. -/
lemma c_eq_int (α : ℝ) :
    Work.Spaces.c α = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ := by
  rw [Work.Spaces.c]
  exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-! ## The angular factor `Γ(α)` -/

/-- `Γ(α)` is continuous (the exponent `α/3` is nonnegative). -/
lemma continuous_Gam (α : ℝ) (hα : 0 < α) : Continuous (Work.Spaces.Gam α) := by
  have h : Continuous fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 := by fun_prop
  exact h.rpow_const (fun θ => Or.inr (by positivity))

/-- `Γ(α)` is measurable. -/
lemma measurable_Gam (α : ℝ) (hα : 0 ≤ α) : Measurable (Work.Spaces.Gam α) := by
  have hbase : Measurable fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 :=
    Real.continuous_sin.measurable.mul
      (by fun_prop : Continuous fun θ : ℝ => Real.cos θ ^ 2).measurable
  have hrp : Measurable fun x : ℝ => x ^ (α / 3) :=
    (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ α / 3)).measurable
  rw [show Work.Spaces.Gam α = fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl]
  exact hrp.comp hbase

/-- `|Γ(α)| ≤ 1` everywhere. -/
lemma abs_Gam_le_one (α : ℝ) (hα : 0 < α) (θ : ℝ) : |Work.Spaces.Gam α θ| ≤ 1 := by
  have hy : (0 : ℝ) ≤ α / 3 := by positivity
  have habs : |Real.sin θ * Real.cos θ ^ 2| ≤ 1 := by
    have hs : |Real.sin θ| ≤ 1 := abs_le.mpr (Real.sin_mem_Icc θ)
    have hc : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have hc0 : 0 ≤ |Real.cos θ| := abs_nonneg _
    calc |Real.sin θ * Real.cos θ ^ 2| = |Real.sin θ| * |Real.cos θ| ^ 2 := by
          rw [abs_mul, abs_pow]
      _ ≤ 1 * 1 ^ 2 := by
          exact mul_le_mul hs (pow_le_pow_left₀ hc0 hc 2) (by positivity) (by norm_num)
      _ = 1 := by norm_num
  calc |Work.Spaces.Gam α θ| = |(Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)| := rfl
    _ ≤ |Real.sin θ * Real.cos θ ^ 2| ^ (α / 3) := Real.abs_rpow_le_abs_rpow _ _
    _ ≤ 1 ^ (α / 3) := Real.rpow_le_rpow (abs_nonneg _) habs hy
    _ = 1 := Real.one_rpow _

/-! ## The hypothesis `L₁₂(locG6)(0) = 0` is `∫ R(s)/s ds = 0` -/

/-- **The normalisation hypothesis in radial form**: if `L₁₂(locG6 α L β)(0) = 0` then the
radial factor satisfies `∫_0^∞ locR(s)/s ds = 0`. -/
lemma locR_Lambda_zero (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (h12 : Work.Construction.L12 (Work.FTS.LocData6.locG6 α L β) 0 = 0) :
    (∫ s in Set.Ioi (0 : ℝ), Work.FTS.LocDataExt.locR α L β s / s) = 0 := by
  have hfact : Work.FTS.LocData6.locG6 α L β
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ :=
    Work.FTS.LocDataExt.locG_eq_locR_Gam α L β
  have h1 : Work.Construction.L12 (Work.FTS.LocData6.locG6 α L β) 0
      = Work.Spaces.c α * (∫ s in Set.Ioi (0 : ℝ), Work.FTS.LocDataExt.locR α L β s / s) := by
    rw [show Work.Construction.L12 (Work.FTS.LocData6.locG6 α L β) 0
        = Work.FM.L12 Work.Spaces.K
            (fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ) 0 from by
      rw [hfact]
      rfl]
    rw [L12_sep_mul, c_eq_int]
  have hz : Work.Spaces.c α * (∫ s in Set.Ioi (0 : ℝ), Work.FTS.LocDataExt.locR α L β s / s)
      = 0 := by rw [← h1, h12]
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  exact (mul_eq_zero.mp hz).resolve_left hc

/-! ## The radial factor `locR`: measurability, vanishing near `0` and decay -/

/-- `|F_{*,rad}(z)| ≤ 2/(1+z)` for `z > 0`. -/
lemma abs_Fstar_le (z : ℝ) (hz : 0 < z) : |Work.FM.Fstar z| ≤ 2 / (1 + z) := by
  have hz1 : 0 < 1 + z := by linarith
  have hzle : z / (1 + z) ≤ 1 := by rw [div_le_one hz1]; linarith
  rw [Work.FM.Fstar, abs_div, abs_of_nonneg (sq_nonneg (1 + z)), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hz,
    show 2 * z / (1 + z) ^ 2 = (2 / (1 + z)) * (z / (1 + z)) from by field_simp]
  exact mul_le_of_le_one_right (by positivity) hzle

/-- `|zfarR L z| ≤ 2/(1+z)` for `z > 0`. -/
lemma abs_zfarR_le (L : ℝ) (z : ℝ) (hz : 0 < z) :
    |Work.FTS.LocDataExt.zfarR L z| ≤ 2 / (1 + z) := by
  rw [Work.FTS.LocDataExt.zfarR_apply, abs_mul]
  refine (mul_le_of_le_one_left (abs_nonneg _) ?_).trans (abs_Fstar_le z hz)
  rw [abs_le]
  exact ⟨by linarith [Work.Stability.chi_le_one (z / L)],
    by linarith [Work.Stability.chi_nonneg (z / L)]⟩

/-- `zfarR L` is measurable. -/
lemma measurable_zfarR (L : ℝ) : Measurable (Work.FTS.LocDataExt.zfarR L) := by
  have hchi : Measurable fun z : ℝ => Work.Stability.chi (z / L) :=
    Work.Stability.chi_continuous.measurable.comp (by fun_prop)
  have hF : Measurable fun z : ℝ => (2 * z) / (1 + z) ^ 2 := by measurability
  rw [show Work.FTS.LocDataExt.zfarR L
      = fun z : ℝ => (1 - Work.Stability.chi (z / L)) * ((2 * z) / (1 + z) ^ 2) from rfl]
  exact (measurable_const.sub hchi).mul hF

/-- `bumpZ` is measurable. -/
lemma measurable_bumpZ : Measurable Work.FTS.LocData.bumpZ := by
  rw [show Work.FTS.LocData.bumpZ
      = fun z : ℝ => Work.Stability.chi (4 * z - 5) from rfl]
  exact Work.Stability.chi_continuous.measurable.comp (by fun_prop)

/-- `locR α L β` is measurable. -/
lemma measurable_locR (α L β : ℝ) : Measurable (Work.FTS.LocDataExt.locR α L β) := by
  have hz := measurable_zfarR L
  have hb := measurable_bumpZ
  rw [show Work.FTS.LocDataExt.locR α L β
      = fun z : ℝ => -(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z
          + β * Work.FTS.LocData.bumpZ z from rfl]
  exact (measurable_const.mul hz).add (measurable_const.mul hb)

/-- `locR α L β` vanishes on `(0, 3/4]` (the cut-off factors of both summands are `0` there). -/
lemma locR_vanish (α L β : ℝ) (hL : 1 ≤ L) :
    ∀ z, 0 < z → z ≤ 3 / 4 → Work.FTS.LocDataExt.locR α L β z = 0 := by
  intro z hz hz34
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [Work.FTS.LocDataExt.locR_apply,
    Work.FTS.LocDataExt.zfarR_eq_zero_of_le hLpos hz.le (by linarith),
    Work.FTS.LocDataExt.bumpZ_eq_zero_of_le hz34]
  ring

/-- The decay `|locR α L β z| ≤ C/(1+z)` for `z > 0`. -/
lemma locR_decay (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, 0 < z →
      |Work.FTS.LocDataExt.locR α L β z| ≤ C / (1 + z) := by
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hbump1 : ∀ z : ℝ, |Work.FTS.LocData.bumpZ z| ≤ 1 := by
    intro z
    rw [Work.FTS.LocData.bumpZ_apply]
    exact abs_le.mpr ⟨by linarith [Work.Stability.chi_nonneg (4 * z - 5)],
      Work.Stability.chi_le_one (4 * z - 5)⟩
  refine ⟨20 * α + 3 * |β| + 1, by positivity, fun z hz => ?_⟩
  have hz1 : 0 < 1 + z := by linarith
  have h1 : |-(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z| ≤ 20 * α / (1 + z) := by
    rw [abs_mul, abs_neg, abs_div, abs_of_pos hcpos, abs_of_pos hα]
    have h2 : α / Work.Spaces.c α ≤ 10 * α := by
      rw [div_le_iff₀ hcpos]
      have := mul_le_mul_of_nonneg_left hc hα.le
      nlinarith
    calc α / Work.Spaces.c α * |Work.FTS.LocDataExt.zfarR L z|
        ≤ 10 * α * (2 / (1 + z)) :=
          mul_le_mul h2 (abs_zfarR_le L z hz) (abs_nonneg _) (by positivity)
      _ = 20 * α / (1 + z) := by ring
  have h3 : |β * Work.FTS.LocData.bumpZ z| ≤ 3 * |β| / (1 + z) := by
    rw [abs_mul]
    by_cases hle : z ≤ 7 / 4
    · have h4 : (1 : ℝ) ≤ 3 / (1 + z) := by
        rw [le_div_iff₀ hz1]
        linarith
      calc |β| * |Work.FTS.LocData.bumpZ z| ≤ |β| * 1 :=
            mul_le_mul_of_nonneg_left (hbump1 z) (abs_nonneg β)
        _ = |β| := by ring
        _ ≤ |β| * (3 / (1 + z)) := le_mul_of_one_le_right (abs_nonneg β) h4
        _ = 3 * |β| / (1 + z) := by ring
    · have hz0 : Work.FTS.LocData.bumpZ z = 0 := by
        refine Work.FTS.LocData.bumpZ_eq_zero_of_notMem ?_
        simp only [Set.mem_Icc, not_and_or, not_le]
        exact Or.inr (by linarith)
      rw [hz0, abs_zero, mul_zero]
      positivity
  rw [Work.FTS.LocDataExt.locR_apply]
  calc |-(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z
          + β * Work.FTS.LocData.bumpZ z|
      ≤ |-(α / Work.Spaces.c α) * Work.FTS.LocDataExt.zfarR L z|
        + |β * Work.FTS.LocData.bumpZ z| := abs_add_le _ _
    _ ≤ 20 * α / (1 + z) + 3 * |β| / (1 + z) := add_le_add h1 h3
    _ ≤ (20 * α + 3 * |β| + 1) / (1 + z) := by
        rw [← add_div, div_le_div_iff_of_pos_right hz1]
        linarith

/-- Measurability of the separable datum `(z,θ) ↦ locR z · Γ(α)(θ)`. -/
lemma measurable_uncurry_locR_Gam (α L β : ℝ) (hα : 0 < α) :
    Measurable (Function.uncurry (fun z θ => Work.FTS.LocDataExt.locR α L β z
      * Work.Spaces.Gam α θ)) := by
  have hlocR := measurable_locR α L β
  have hGam := measurable_Gam α hα.le
  rw [show Function.uncurry (fun z θ => Work.FTS.LocDataExt.locR α L β z
      * Work.Spaces.Gam α θ)
      = fun x : ℝ × ℝ => Work.FTS.LocDataExt.locR α L β x.1 * Work.Spaces.Gam α x.2 from rfl]
  exact (hlocR.comp measurable_fst).mul (hGam.comp measurable_snd)

/-! ## The target -/

theorem L12_Jeps_locG6 (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (h12 : Work.Construction.L12 (Work.FTS.LocData6.locG6 α L β) 0 = 0) :
    Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.LocData6.locG6 α L β)) 0 = 0 := by
  obtain ⟨C, hCpos, hCb⟩ := locR_decay α L β hα hα1
  have hΛ : (∫ s in Set.Ioi (0 : ℝ), Work.FTS.LocDataExt.locR α L β s / s) = 0 :=
    locR_Lambda_zero α L β hα hα1 h12
  have hFm : Measurable (Function.uncurry (fun z θ => Work.FTS.LocDataExt.locR α L β z
      * Work.Spaces.Gam α θ)) := measurable_uncurry_locR_Gam α L β hα
  have hF0 : ∀ z θ, 0 < z → z ≤ 3 / 4 →
      (fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ) z θ = 0 := by
    intro z θ hz hza
    show Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ = 0
    rw [locR_vanish α L β hL z hz hza, zero_mul]
  have hFg : ∀ z θ, 0 < z →
      |(fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ) z θ|
        ≤ C / (1 + z) := by
    intro z θ hz
    show |Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ| ≤ C / (1 + z)
    rw [abs_mul]
    calc |Work.FTS.LocDataExt.locR α L β z| * |Work.Spaces.Gam α θ|
        ≤ (C / (1 + z)) * 1 :=
          mul_le_mul (hCb z hz) (abs_Gam_le_one α hα θ) (abs_nonneg _) (by positivity)
      _ = C / (1 + z) := by ring
  have hkey := L12_Jeps_interchange_mine (ρ := ρ) hρ.moll hε
      (F := fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ)
      (a := 3 / 4) (C := C) (by norm_num) hFm hF0 hFg
  have hfact : Work.FTS.LocData6.locG6 α L β
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ :=
    Work.FTS.LocDataExt.locG_eq_locR_Gam α L β
  rw [show Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.LocData6.locG6 α L β)) 0
      = Work.FM.L12 Work.Spaces.K (Work.FTS.StrongEps.Jeps ρ ε
          (fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ)) 0 from by
    rw [hfact]
    rfl]
  rw [hkey]
  have hshift : ∀ p : ℝ × ℝ, Work.FM.L12 Work.Spaces.K
      (fun z θ => (fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ)
        (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) 0
      = (∫ s in Set.Ioi (0 : ℝ), Work.FTS.LocDataExt.locR α L β s / s)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
            * Work.Spaces.Gam α (Work.FTS.StrongEps.thShift θ p.2)) :=
    fun p => L12_sep_mul_shift (Work.FTS.LocDataExt.locR α L β) (Work.Spaces.Gam α) p.1 p.2
  simp only [hshift]
  rw [hΛ]
  simp

end Work.FTS_LocDatum3a
