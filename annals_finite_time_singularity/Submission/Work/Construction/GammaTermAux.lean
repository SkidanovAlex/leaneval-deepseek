/-
# Auxiliary definitions for the `ℋ⁴` bound on the first two terms of `N₀`

The target of `H4N_GammaTerm_le` is

`|8α² c2m(θ) z²Γ(θ)/(c(α)(1+z)⁴)|_{ℋ⁴} ≤ C α²`  (`0 < α ≤ 1`, `C` universal),

the "direct calculation" of tex 1398–1402 (the two `F_*`-quadratic terms of `\eqref{N0}`,
which only vanish linearly at `z = 0` individually but quadratically in combination).

The function is **separated**: it is `ρ(z)·ψ(θ)` times the `α`-constant `8α²/c(α)`, with

* `ρ(z) = z²/(1+z)⁴` (`rhoR`), whose `D_z`-iterates are bounded by `M/(1+z)²` after
  multiplication by the weight `w(z)` (the `z`-calculation of the "direct calculation");
* `ψ(θ) = c2m(θ)Γ(θ)` (`psiA α`), whose `D_θ`-iterates are controlled by `C·Γ(θ)` (the
  `θ`-calculation).

This file collects the definitions, the *separability* lemmas (the `D_z`- and `D_θ`-iterates
of a separated function are separated), the elementary bound `Γ ≤ sin(2θ)^{α/3}`, the
generic angular integral `∫ sin(2θ)^{-p} ≤ 100/(1-p)`, and the measure identifications
`[0,π/2] ~ (0,π/2)`, `[0,∞) ~ (0,∞)` (so that pointwise bounds proved on the open
quadrant may be used inside the integrals over the closed sets).

The two computational cores are stated as the lemmas

* `Work.Construction.H4N_GammaTerm_rho_bound`  (`∃ M > 0, ∀ j ≤ 4, ∀ z ≥ 0,
   |(D_z^j ρ)(z)·w(z)| ≤ M/(1+z)²`), and
* `Work.Construction.H4N_GammaTerm_Lop_bound`  (`∃ D > 0, ∀ 0 < α ≤ 1, ∀ 1 ≤ i ≤ 4,
   ∀ θ ∈ (0,π/2), |(D_θ^i ψ)(θ)| ≤ D·Γ(θ)·(sin(2θ)² + α)`)

of the companion modules `Submission/Work/Construction/H4N_GammaTerm_rho_bound.lean` and
`Submission/Work/Construction/H4N_GammaTerm_Lop_bound.lean`; the module
`Submission/Work/Construction/H4N_GammaTerm_le.lean` assembles them.

## Notes for the `θ`-calculation

`D_θ = sin(2θ)∂_θ` acts on functions of `θ` alone as `Work.Spaces.Lop`
(`Work.Spaces.Lop φ = fun θ => sin(2θ)·φ'(θ)`, definitionally equal to the `dthU` of
`Submission/Work/Spaces/GammaW_Prelim.lean`), and on the pair `(z,θ)` as
`Work.Spaces.DthIter`.  Similarly `D_z` acts on functions of `z` alone as
`Work.Spaces.Zop` (`Zop φ = fun z => z·φ'(z)`).  The bridge between the two is
`Work.Spaces.DthIter_eq_iterate_Lop` / `Work.Spaces.Zop_slice`.

The useful rewriting of the angular coefficient is `c2m_eq`: on all of `ℝ`,
`c2m_eq_half`: `c2m θ = (3cos(2θ) - 1)/2`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Spaces.sin_rpow_le_majorant
import Submission.Work.Spaces.integrableOn_majorant_rpow
import Submission.Work.Spaces.integral_majorant_rpow
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-! ## The separated shape of the term -/

/-- The radial factor `ρ(z) = z²/(1+z)⁴` of the `Γ`-term. -/
def rhoR (z : ℝ) : ℝ := z ^ 2 / (1 + z) ^ 4

/-- The angular factor `ψ(θ) = c2m(θ)·Γ(θ)` of the `Γ`-term. -/
def psiA (α : ℝ) (θ : ℝ) : ℝ := c2m θ * Work.Spaces.Gam α θ

/-- The `α`-dependent constant `8α²/c(α)` multiplying `ρ·ψ`. -/
def Kfac (α : ℝ) : ℝ := 8 * α ^ 2 / Work.Spaces.c α

/-- A separated function `(z,θ) ↦ a z · b θ`. -/
def sepF (a b : ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => a z * b θ

/-! ## Separability of the iterated derivatives -/

theorem Zop_apply (u : ℝ → ℝ) (z : ℝ) :
    Work.Spaces.Zop u z = z * deriv u z := rfl

theorem Lop_apply (u : ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.Lop u θ = Real.sin (2 * θ) * deriv u θ := rfl

theorem Zop_const_mul (c : ℝ) (u : ℝ → ℝ) :
    Work.Spaces.Zop (fun z => c * u z) = fun z => c * Work.Spaces.Zop u z := by
  funext z
  rw [Zop_apply, Zop_apply, deriv_const_mul_fun (a := c) (b := u) z]
  ring

theorem Zop_iter_const_mul (j : ℕ) (c : ℝ) (u : ℝ → ℝ) :
    Work.Spaces.Zop^[j] (fun z => c * u z) = fun z => c * (Work.Spaces.Zop^[j] u) z := by
  induction j with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Zop_const_mul]
      funext z
      rw [Function.iterate_succ_apply']

theorem sepF_DzIter (i : ℕ) (a b : ℝ → ℝ) :
    Work.Spaces.DzIter i (sepF a b) = sepF (Work.Spaces.Zop^[i] a) b := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      show z * deriv (fun z' => (Work.Spaces.Zop^[n] a) z' * b θ) z
          = (Work.Spaces.Zop^[n + 1] a) z * b θ
      rw [Function.iterate_succ_apply', Zop_apply,
          deriv_mul_const_fun (a := b θ) (b := Work.Spaces.Zop^[n] a) z]
      ring

theorem sepF_DthIter (i : ℕ) (a b : ℝ → ℝ) :
    Work.Spaces.DthIter i (sepF a b) = sepF a (Work.Spaces.Lop^[i] b) := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => a z * (Work.Spaces.Lop^[n] b) θ') θ
          = a z * (Work.Spaces.Lop^[n + 1] b) θ
      rw [Function.iterate_succ_apply', Lop_apply,
          deriv_const_mul_fun (a := a z) (b := Work.Spaces.Lop^[n] b) θ]
      ring

theorem sepF_mixed (j i : ℕ) (a b : ℝ → ℝ) :
    Work.Spaces.mixed j i (sepF a b)
      = sepF (Work.Spaces.Zop^[j] a) (Work.Spaces.Lop^[i] b) := by
  rw [Work.Spaces.mixed, sepF_DthIter, sepF_DzIter]

/-! ## The angular coefficient `c2m` -/

/-- `c2m θ = (3cos(2θ) - 1)/2`: the form used for the angular derivatives. -/
theorem c2m_eq_half (θ : ℝ) : c2m θ = (3 * Real.cos (2 * θ) - 1) / 2 := by
  rw [c2m, Real.cos_two_mul]
  have h := Real.sin_sq_add_cos_sq θ
  ring_nf at h ⊢
  linarith

/-! ## The measure of the closed intervals is the measure of the open ones -/

theorem restrict_Iθ_eq_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (π / 2)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl,
      Set.Icc_sdiff_Ioo_same (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)]
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton 0) (measure_singleton _)
  · rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]

theorem restrict_Iz_eq_Ioi :
    volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl, Set.Ici_sdiff_Ioi, Set.Icc_self]
    exact measure_singleton 0
  · rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioi_subset_Ici_self, measure_empty]

/-! ## Elementary angular bounds -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem Gam_nonneg_of_Iθ {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1

theorem Gam_le_one_of_Iθ {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2

/-- `Γ(θ) ≤ sin(2θ)^{α/3}`: since `sin θ cos²θ ≤ sin θ cos θ = sin(2θ)/2 ≤ sin(2θ)` and
both sides are obtained by raising to the nonnegative power `α/3`. -/
theorem Gam_le_sin_two_rpow {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 3) := by
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hbase : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]
    nlinarith [mul_nonneg hs0 hc0, hc0, hc1, sq_nonneg (Real.cos θ),
      Real.cos_sq_le_one θ]
  rw [Work.Spaces.Gam]
  exact Real.rpow_le_rpow (mul_nonneg hs0 (sq_nonneg _)) hbase (by linarith)

/-- `∫_0^{π/2} sin(2θ)^{-p} ≤ 100/(1-p)` for `0 < p < 1`, uniformly in `p`. -/
theorem integral_sin_two_rpow_neg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-p) ≤ 100 / (1 - p) := by
  have hGint : Integrable
      (fun θ : ℝ => (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)))
      (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.integrableOn_majorant_rpow p hp0 hp1
  have hGval : ∫ θ in Work.Spaces.Iθ,
        ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)))
      = Real.pi * (1 / 2) ^ p / (1 - p) := Work.Spaces.integral_majorant_rpow p hp0 hp1
  have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-p)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _
  have hle : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-p))
      ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Work.Spaces.sin_rpow_le_majorant p θ hp0 hθ
  have hmono := MeasureTheory.integral_mono_of_nonneg hnonneg hGint hle
  calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-p)
      ≤ ∫ θ in Work.Spaces.Iθ,
          ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) := hmono
    _ = Real.pi * (1 / 2) ^ p / (1 - p) := hGval
    _ ≤ 100 / (1 - p) := by
        refine div_le_div_of_nonneg_right ?_ (by linarith)
        calc Real.pi * (1 / 2) ^ p
            ≤ 4 * 1 := mul_le_mul (le_of_lt Real.pi_lt_four)
                (Real.rpow_le_one (by norm_num) (by norm_num) (le_of_lt hp0))
                (by positivity) (by norm_num)
          _ ≤ 100 := by norm_num

end Work.Construction
