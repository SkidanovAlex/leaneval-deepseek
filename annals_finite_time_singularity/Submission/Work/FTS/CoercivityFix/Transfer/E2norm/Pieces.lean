/-
# `Transfer/E2norm/Pieces.lean` — the pieces of the `ℋⁿ`-norm bound for the `D_z`-defect

This module collects the four facts about the `D_z`-transfer defect

  `E2 α f = Ê₂ f + Γ(θ)·radS α f z`

that the `ℋⁿ`-norm bound `E2_norm` needs, and that are independent of the (large) radial
bookkeeping over the expansion of `D_z^j (radS α f)`:

* `ampA_dzdIter_bound_uniform` — the multiplier `ampA α = 2z/(c(α)(1+z)²)` has all its
  `(z∂_z)`-iterates up to order `4` bounded on `(0,∞)` by a constant **independent of `α`**
  (this is `E2pkg.ampA_dzdIter_bound` with the `α`-quantifier moved inside, which is what the
  final `∃ κ, ∀ α ≤ 1` statement requires);
* `qang_sq_w_sq_le` — the angular moment bound `∫_z (Qang f i z)² w(z)² dz ≤ (∫_θ K_θ²)·|f|²_{ℋⁿ}`
  at the level `n` (rather than the level `4` of `N4Fields.Qang_sq_w_sq_integral`);
* `L12f_DzdIter_sq_w_sq_le` — the same for the `(z∂_z)`-iterates of `L₁₂ f`
  (`D_z^c(L₁₂ f) = −Qang f (c−1)` for `c ≥ 1`, and the weighted Hardy inequality
  `Coercivity.L12f_w_hardy` with constant `107` for `c = 0`);
* `HkSq_add_le` — the two-term additivity of `HkSq` used to split `E2 α f` into its two
  structurally different summands.

All constants below are independent of `α ∈ (0,1]`, which is what makes the final constant
of `E2_norm` uniform.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadL12
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.HardyOne
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.dzdIter_coeff_bound
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadSAux
import Submission.Work.FTS.H2.Qang_sq_leQ
import Submission.Work.FTS.H2.QangAux
import Submission.Work.FTS.Nonlinear.N4Fields.Qang_sq_w_sq_integral
import Submission.Work.Coercivity.L12f_w_hardy
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS.CoercivityFix.Coer1T.HardyBasic
import Submission.Work.FTS.LocDataExt.Monotone

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2norm

set_option autoImplicit false

open Work.FTS.Galerkin (Fn)

/-! ## The `α`-uniform bound on the multiplier `ampA` -/

/-- **The multiplier `ampA α = 2z/(c(α)(1+z)²)` has uniformly bounded `(z∂_z)`-iterates.**
There is a single `K`, valid for every `α ∈ (0,1]`, such that `|D_z^j (ampA α) z| ≤ K` for
`j ≤ 4` and `z > 0`.

This is `E2pkg.ampA_dzdIter_bound` with the constant made explicit (`20·K₀`, where `K₀` is the
chart bound of `E2Bound.zop_phi_bound`): the only `α`-dependence of the estimate is the factor
`2/c(α) ≤ 20`, from `1/10 ≤ c(α)` (`Spaces.c_bounds`). -/
theorem ampA_dzdIter_bound_uniform :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ j ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ K := by
  obtain ⟨K₀, hK₀, hbd⟩ := Work.FTS.CoercivityFix.E2Bound.zop_phi_bound 4
  refine ⟨20 * K₀, by positivity, ?_⟩
  intro α hα hα1 j hj z hz
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have h2c : 2 / Work.Spaces.c α ≤ 20 := by
    rw [div_le_iff₀ hcpos]
    linarith
  have hb : |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K₀ := hbd j hj z hz
  calc |Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampA α) z|
      = |Work.Spaces.Zop^[j] (Work.FTS.CoercivityFix.Transfer.ampA α) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
    _ = |Work.Spaces.Zop^[j]
          (fun z => (2 / Work.Spaces.c α) * (z / (1 + z) ^ 2)) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.ampA_eq_const_mul_fA]
    _ = |(2 / Work.Spaces.c α) * Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]
    _ = |2 / Work.Spaces.c α|
          * |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := abs_mul _ _
    _ = (2 / Work.Spaces.c α)
          * |Work.Spaces.Zop^[j] (fun z : ℝ => z / (1 + z) ^ 2) z| := by
        rw [abs_of_nonneg (by positivity)]
    _ ≤ (2 / Work.Spaces.c α) * K₀ := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ 20 * K₀ := mul_le_mul_of_nonneg_right h2c hK₀

/-! ## The angular-moment bound at level `n` -/

/-- The two angular endpoints of `Iθ = [0,π/2]` are null. -/
private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- `Iz = [0,∞)` and `(0,∞)` differ by the null set `{0}`. -/
private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

/-- **The angular moment at level `n`.**  For `f ∈ CoerAdm α`, `0 < α ≤ 1` and `i ≤ n ≤ 3`,

  `∫_z (Qang f i z)² w(z)² dz ≤ (∫_θ K_θ(θ)² dθ) · |f|²_{ℋⁿ}`,

with the *α-independent* Cauchy–Schwarz constant `∫_θ K_θ²`.  (`Work.FTS.H2.Qang_sq_leQ` is
the Cauchy–Schwarz step in `θ`, and the surviving `∫_θ (D_z^i f)²` is dominated by a single
pure `D_z`-slot of the level-`n` integrand.) -/
theorem qang_sq_w_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {n : ℕ} (hn : n ≤ 3)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.Nonlin.CoerAdm α f) (i : ℕ) (hi : i ≤ n) :
    MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f := by
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem5 : Work.Spaces.HkMem α 5 f := hf.reg.2.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hsm hmem5
  have hmemn : Work.Spaces.HkMem α n f :=
    Work.FTS.LocDataExt.HkMem_mono (by omega) hsm hmem5
  have hi4 : i ≤ 4 := by omega
  -- integrability (from the `Ioi 0` version, transported along the null set `{0}`)
  have hintIoi : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    Work.FTS.CoercivityFix.Transfer.E1Parts.Qang_sq_w_sq_integrable_Ioi α hα hα1 hsm hmem4 hi4
  have hint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    hintIoi.congr_set_ae Iz_ae_eq_Ioi
  refine ⟨hint, ?_⟩
  -- the pointwise (in `z > 0`) bound
  have hpt : ∀ z : ℝ, 0 < z →
      (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ) := by
    intro z hz
    have hCS := Work.FTS.H2.Qang_sq_leQ α f hsm hmem4 i hi4 hz
    have hslice : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ) ^ 2)
          * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ := by
      have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
          (Work.Spaces.DzIter i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α n f z θ := by
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => by
            have h := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α n f i hi hz hθ
            have hw : 0 < (Work.Spaces.w z) ^ 2 := pow_pos (Work.FTS.H2.w_pos hz) 2
            rw [le_div_iff₀ hw] at h
            exact h)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmemn.1 z (le_of_lt hz)) hae
      simpa only [MeasureTheory.integral_mul_const] using hmono
    calc (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ) ^ 2))
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hCS (sq_nonneg _)
      _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
      _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ) :=
          mul_le_mul_of_nonneg_left hslice
            (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
  -- integrate the pointwise bound over `z ∈ (0,∞)`
  have hbase : MeasureTheory.IntegrableOn
      (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.congr_set_ae (hmemn.2.const_mul _) Iz_ae_eq_Ioi.symm
  have hcomp : ∫ z in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
      = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f := by
    rw [MeasureTheory.integral_const_mul, Work.Spaces.HkSq,
      MeasureTheory.setIntegral_congr_set Iz_ae_eq_Ioi]
  rw [MeasureTheory.setIntegral_congr_set Iz_ae_eq_Ioi, ← hcomp]
  exact MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    hbase (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt)

/-! ## The `(z∂_z)`-iterates of `L₁₂ f` -/

/-- **Weighted `L²`-bound for the `(z∂_z)`-iterates of `L₁₂ f`.**  For `f ∈ CoerAdm α`,
`0 < α ≤ 1` and `c ≤ n ≤ 3`,

  `∫_z (D_z^c (L₁₂ f)(z))² w(z)² dz ≤ 107·(∫_θ K_θ²)·|f|²_{ℋⁿ}`.

For `c = 0` this is the weighted Hardy inequality `Coercivity.L12f_w_hardy`
(`107`), with the right-hand side bounded by `qang_sq_w_sq_le`; for `c ≥ 1` it is
`D_z^c(L₁₂ f) = −Qang f (c−1)` (`E1Parts.DzdIter_L12f_eq_neg_Qang`) together with
`qang_sq_w_sq_le`. -/
theorem L12f_DzdIter_sq_w_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {n : ℕ} (hn : n ≤ 3)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.Nonlin.CoerAdm α f) (c : ℕ) (hc : c ≤ n) :
    MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz, (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2
        ≤ 107 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f := by
  have hint : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    Work.FTS.CoercivityFix.Transfer.E1Parts.L12f_DzdIter_sq_w_sq_integrable α hα hα1 hf
      c (by omega)
  rcases Nat.eq_zero_or_pos c with h | h
  · -- `c = 0`: the weighted Hardy inequality for `L₁₂ f`
    subst h
    have hH : Work.Coercivity.HardyHyp f :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.hardyHyp_of_coerAdm_le_one α hα hα1 hf
    have hq0 := qang_sq_w_sq_le α hα hα1 hn hf 0 (by omega)
    have hgint : MeasureTheory.IntegrableOn
        (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f z θ) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
      MeasureTheory.IntegrableOn.congr_fun hq0.1
        (fun z _ => by
          show (Work.Elliptic.Qang f 0 z) ^ 2 * (Work.Spaces.w z) ^ 2
            = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          rw [Work.FTS.CoercivityFix.Transfer.E1Parts.Qang_zero_eq_integral f z])
        measurableSet_Ici
    obtain ⟨_hint2, hle⟩ := Work.Coercivity.L12f_w_hardy f hH hgint
    have hQ : ∫ z in Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        = ∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang f 0 z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => by
        show (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          = (Work.Elliptic.Qang f 0 z) ^ 2 * (Work.Spaces.w z) ^ 2
        rw [Work.FTS.CoercivityFix.Transfer.E1Parts.Qang_zero_eq_integral f z])
    have hLHS : ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 0 (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2
        = ∫ z in Work.Spaces.Iz, (Work.Coercivity.L12f f z * Work.Spaces.w z) ^ 2 :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => by
        show (Work.Elliptic.DzdIter 0 (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2 = (Work.Coercivity.L12f f z * Work.Spaces.w z) ^ 2
        rw [Work.Elliptic.DzdIter_zero, mul_pow])
    refine ⟨hint, ?_⟩
    rw [hLHS]
    calc ∫ z in Work.Spaces.Iz, (Work.Coercivity.L12f f z * Work.Spaces.w z) ^ 2
        ≤ 107 * ∫ z in Work.Spaces.Iz,
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := hle
      _ = 107 * ∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang f 0 z) ^ 2 * (Work.Spaces.w z) ^ 2 := by rw [hQ]
      _ ≤ 107 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f) :=
          mul_le_mul_of_nonneg_left hq0.2 (by norm_num)
      _ = 107 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f := by
          ring
  · -- `c ≥ 1`: `D_z^c(L₁₂ f) = −Qang f (c−1)`
    have hc4 : c ≤ 4 := by omega
    have hid := Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_L12f_eq_neg_Qang α hα hα1 hf
      c h hc4
    have hq := qang_sq_w_sq_le α hα hα1 hn hf (c - 1) (by omega)
    have hcongr : ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2
        = ∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang f (c - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      MeasureTheory.setIntegral_congr_ae measurableSet_Ici
        (Filter.Eventually.of_forall fun z hz => by
          rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
          · subst h0
            have hw0 : (Work.Spaces.w (0 : ℝ)) ^ 2 = 0 := by simp [Work.Spaces.w]
            rw [hw0]
            ring
          · rw [hid z hpos]
            ring)
    refine ⟨hint, ?_⟩
    rw [hcongr]
    calc ∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang f (c - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f := hq.2
      _ ≤ 107 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f := by
          have h1 : (0 : ℝ) ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) :=
            MeasureTheory.integral_nonneg fun θ => sq_nonneg _
          have h2 : (0 : ℝ) ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
          nlinarith

/-! ## Two-term additivity of `HkSq` -/

/-- **`HkSq` is two-term subadditive** for a pair whose blocks add up pointwise and whose
`HkIntegrand` is pointwise dominated by twice the sum of the two integrands. -/
theorem HkSq_add_le (α : ℝ) (n : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α n f) (hg : Work.Spaces.HkMem α n g)
    (hfg : Work.Spaces.HkMem α n (f + g))
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n (f + g) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α n f z θ
          + 2 * Work.Spaces.HkIntegrand α n g z θ) :
    Work.Spaces.HkSq α n (f + g) ≤ 2 * Work.Spaces.HkSq α n f + 2 * Work.Spaces.HkSq α n g := by
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (f + g) z θ)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ) := by
    intro z hz
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α n (f + g) z θ
          ≤ 2 * Work.Spaces.HkIntegrand α n f z θ
            + 2 * Work.Spaces.HkIntegrand α n g z θ :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ)
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α n (f + g) z θ)
      (((hf.1 z hz).const_mul 2).add ((hg.1 z hz).const_mul 2)) hae
    have hEq : (∫ a in Work.Spaces.Iθ,
          ((fun x => 2 * Work.Spaces.HkIntegrand α n f z x)
            + fun x => 2 * Work.Spaces.HkIntegrand α n g z x) a)
        = 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ) := by
      simp only [Pi.add_apply]
      rw [MeasureTheory.integral_add ((hf.1 z hz).const_mul 2) ((hg.1 z hz).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact le_trans hmono (le_of_eq hEq)
  have hmain : (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (f + g) z θ)
      ≤ ∫ z in Work.Spaces.Iz, (2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ)) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α n (f + g) z θ)
      ((hf.2.const_mul 2).add (hg.2.const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hslice)
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n (f + g) z θ)
      ≤ ∫ z in Work.Spaces.Iz, (2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ)) := hmain
    _ = 2 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)
        + 2 * (∫ z in Work.Spaces.Iz,
            ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ) := by
        rw [MeasureTheory.integral_add (hf.2.const_mul 2) (hg.2.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

end Work.FTS.CoercivityFix.Transfer.E2norm
