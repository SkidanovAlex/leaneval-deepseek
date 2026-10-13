/-
# `|L₁₂ h 0| ≤ C · |h|_{ℋ⁴_α}` with `C` independent of `α` (Cauchy–Schwarz route)

`L₁₂ h 0 = ∫_{s>0} ∫_θ K(θ)·h(s,θ)/s dθ ds`.  Writing `g = h·w/Sw` with
`Sw θ = sin(2θ)^{η/2}` (so that `g²` is the `D_z^0`-summand of `HkIntegrand`), the density
integrand factorises as

  `K(θ)·h s θ/s = Wlam s · (K(θ)·Sw θ·g(s,θ))`,   `Wlam s = s/(1+s)² = 1/(s·w s)`,

and two Cauchy–Schwarz steps finish the job:

* in `θ`: `|∫_θ K·Sw·g| ≤ √(∫_θ (K·Sw)²)·√(∫_θ HkIntegrand α 4 h s θ)` (using
  `g² ≤ HkIntegrand`, i.e. the `D_z^0`-term);
* in `s`: against `Wlam ∈ L²((0,∞))`, using `∫_{(0,∞)} ∫_θ HkIntegrand = HkSq α 4 h`
  (the sets `Ioi 0` and `Iz = Ici 0` differ by the null set `{0}`).

Every integrability issue on the way is handled by `MeasureTheory.integral_undef` (a
non-integrable integral is `0`, which satisfies the bound, the right hand side being
nonnegative), so the only hypothesis needed is `HkMem α 4 h` itself — no smoothness, no
measurability of the slices.

The constants are `BK = √(∫_θ (K·Sw)²)` and `W2 = ∫_{(0,∞)} Wlam²`; the final constant is
`BK·√W2 + 1` (both terms are finite and independent of `α`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.GalBasis.cc.abs_integral_K_S_Gaz_le
import Submission.Work.FTS.GalBasis.cc.integral_abs_L12dens_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The pointwise identity -/

/-- For `s > 0` and `θ ∈ Iθ`, the integrand of the `L₁₂`-density is the radial weight
`Wlam s = 1/(s·w s)` times the weighted datum `Gaz h = h·w/Sw` against the angular profile
`K·Sw`.  (At the endpoints `θ = 0, π/2`, where `Sw` vanishes, both sides vanish because so
does `K`.) -/
lemma K_mul_h_div_s_eq (h : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.K θ * h s θ / s
        = Wlam s * (Work.Spaces.K θ * Sw θ * Gaz h s θ) := by
  intro θ hθ
  rw [Gaz, Wlam, Work.Spaces.w]
  by_cases hS : Sw θ = 0
  · have hK : Work.Spaces.K θ = 0 := sw_eq_zero_imp_K_eq_zero hθ hS
    rw [hS, hK]
    simp
  · have hS' : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≠ 0 := by
      simpa only [Sw] using hS
    have h1s : (1 : ℝ) + s ≠ 0 := by linarith
    field_simp

/-- The `L₁₂`-density as a constant multiple of the angular integral of the weighted datum. -/
lemma L12dens_eq_weighted (h : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    Work.Construction.L12dens h s
      = Wlam s * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Sw θ * Gaz h s θ := by
  have hI : Work.Spaces.Iθ = Set.Icc 0 (π / 2) := rfl
  calc Work.Construction.L12dens h s
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h s θ / s := by
        rw [Work.Construction.L12dens, Work.FM.L12dens, hI]
    _ = ∫ θ in Work.Spaces.Iθ, Wlam s * (Work.Spaces.K θ * Sw θ * Gaz h s θ) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => K_mul_h_div_s_eq h hs θ (by simpa only [hI] using hθ))] with θ hθ
        exact hθ
    _ = Wlam s * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Sw θ * Gaz h s θ :=
        integral_const_mul _ _

/-! ## The pointwise bound on the density -/

lemma abs_L12dens_le (α : ℝ) (h : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 h)
    {s : ℝ} (hs : 0 < s) :
    |Work.Construction.L12dens h s|
      ≤ Wlam s * (BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h s θ)) := by
  rw [L12dens_eq_weighted h hs, abs_mul, abs_of_nonneg (Wlam_nonneg hs.le)]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_K_S_Gaz_le α h (hmem.1 s hs.le)) (Wlam_nonneg hs.le)

/-! ## The main theorem -/

/-- Route (Cauchy–Schwarz, `α`-free).  `L12 h 0 = ∫_{s>0} ∫_θ K θ · h s θ / s`.  Put
`g := h · w / sin(2θ)^{η/2}`; then `K θ h/s = g · (K θ sin(2θ)^{η/2} s/(1+s)²)`, and the second
factor has finite `L²(dz dθ)`-norm (constant in `α`).  Hence
`|L12 h 0| ≤ (∫∫ g²)^{1/2} · (∫_θ K² sin^η)^{1/2} · (∫_s s²/(1+s)⁴)^{1/2}`,
and `∫∫ g² ≤ HkSq α 4 h` since `(DzIter 0 h · w/sin(2θ)^{η/2})² = g²` is the `i = 0` summand of
`HkIntegrand α 4 h` (all summands are squares).  Finally `HkNorm α 4 h = sqrt (HkSq α 4 h)`.
The only care needed is the integrability bookkeeping: `HkMem α 4 h` gives `IntegrableOn`
of the θ-slice for every `z ∈ Iz` and integrability of the marginal in `z`, and if the
`θ`-integral of `K θ h/s` is not integrable, `MeasureTheory.integral_undef` makes it `0`, which
is even better. -/
theorem abs_L12_le_HkNorm : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : Work.FTS.Galerkin.Fn),
    Work.Spaces.HkMem α 4 h → |Work.Construction.L12 h 0| ≤ C * Work.Spaces.HkNorm α 4 h := by
  refine ⟨BK * Real.sqrt W2 + 1, by nlinarith [BK_nonneg, Real.sqrt_nonneg W2], ?_⟩
  intro α h hmem
  have hbd : ∀ s ∈ Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s|
      ≤ Wlam s * (BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 h s θ)) :=
    fun s hs => abs_L12dens_le α h hmem hs
  have hL12 : Work.Construction.L12 h 0
      = ∫ s in Set.Ioi (0 : ℝ), Work.Construction.L12dens h s := rfl
  calc |Work.Construction.L12 h 0|
      = |∫ s in Set.Ioi (0 : ℝ), Work.Construction.L12dens h s| := by rw [hL12]
    _ ≤ ∫ s in Set.Ioi (0 : ℝ), |Work.Construction.L12dens h s| := by
        simpa only [Real.norm_eq_abs] using
          (MeasureTheory.norm_integral_le_integral_norm
            (μ := volume.restrict (Set.Ioi (0 : ℝ)))
            (f := fun s => Work.Construction.L12dens h s))
    _ ≤ BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α 4 h) :=
        integral_abs_L12dens_le α h hmem hbd
    _ = (BK * Real.sqrt W2) * Work.Spaces.HkNorm α 4 h := by
        rw [Work.Spaces.HkNorm]
    _ ≤ (BK * Real.sqrt W2 + 1) * Work.Spaces.HkNorm α 4 h := by
        have hx := Work.Spaces.HkNorm_nonneg α 4 h
        nlinarith

end Work.FTS.GalBasis.cc
