/-
# `Work.FTS.PhiStar.FlatWAux.PsiExpansion` — the eigenfunction expansion of the angular model

The angular model `ψ` (`Work.FTS.PhiStar.AngModel α ψ`) solves `Lzero1 ψ = Γ̄` with Dirichlet
data; the eigenfunctions of `Lzero1` are `eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)`
(`lam m = 2m(2m+5)`), which are orthogonal and *complete* in `L²(Iθ, cos θ dθ)`
(`eFam_complete`).  This file proves that the eigenfunction series of `ψ` converges to `ψ`
pointwise on `(0, π/2)`:

  `∑' m, cmode m (fun _ θ => ψ θ) 0 · eFam m θ = ψ θ`.

## The argument

The mode coefficients `b_m := cmode m (fun _ θ => ψ θ) 0` decay like `λ_m^{-1} (2m+1)^{-1/2}`
(`CmodeDecay`, from the self-adjointness of `Lzero1` in the weight `cos θ`) while
`|eFam m θ| ≤ √((2m+2)(2m+3))` on `Iθ` (`psiAngBounds` plus the vanishing at the endpoints);
hence `|b_m e_m(θ)| ≤ K (m+1)^{-3/2}` uniformly on `Iθ`, a summable majorant.  By the
Weierstrass M-test the series `S(θ) := ∑' m, b_m e_m(θ)` is continuous on `Iθ`, and termwise
integration against `e_n cos θ` (dominated convergence with the majorant) together with
orthogonality gives

  `∫_{Iθ} S · e_n · cos θ = b_n ∫_{Iθ} e_n² · cos θ = ∫_{Iθ} ψ · e_n · cos θ`,

the last identity being the definition of `b_n`.  So `S - ψ` is continuous, square-integrable
against the weight and orthogonal to every `e_n`: `eFam_complete` makes it vanish a.e., and
continuity upgrades this to everywhere on the open interval.

The two analysis steps (termwise integration and the a.e.-to-pointwise upgrade) are provided by
the companion modules `PsiExpAux/TsumMoment` and `PsiExpAux/MomentEqOn`; the arithmetic of the
majorant and the assembly are proved here.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.CmodeDecay
import Submission.Work.FTS.PhiStar.Series.SummableModes
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Series.Deleg.psiAngBounds
import Submission.Work.FTS.PhiStar.FlatWAux.PsiExpAux.MomentEqOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-! ## Elementary facts about the modes and the weight -/

/-- The set integral over `Iθ = [0, π/2]` is the interval integral over `0..π/2`. -/
private lemma iota_eq_interval (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-- The normalisation `∫_{Iθ} eFam m ^ 2 cos θ` of the `m`-th mode is positive. -/
private lemma eFam_norm_pos (m : ℕ) :
    0 < ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ := by
  rw [iota_eq_interval, Work.FTS.PhiStar.Gegenbauer.FamNormValue]
  positivity

/-- Every mode is a continuous function. -/
private lemma continuous_eFam (m : ℕ) : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  change Continuous (fun θ : ℝ =>
    Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
  exact Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
      Real.continuous_sin)

/-- The uniform bound `|eFam m θ| ≤ √((2m+2)(2m+3))` on the whole closed interval `Iθ`
(the sharp bound on the closed quadrant; the endpoints vanish). -/
private lemma abs_eFam_le_sqrt (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) := by
  obtain ⟨h0, h1⟩ := hθ
  rcases lt_or_eq_of_le h0 with h0' | h0'
  · rcases lt_or_eq_of_le h1 with h1' | h1'
    · exact (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).1 m θ ⟨h0', h1'⟩
    · rw [h1', Work.FTS.PhiStar.Series.eFam_zero_left, abs_zero]
      exact Real.sqrt_nonneg _
  · rw [← h0', Work.FTS.PhiStar.Series.eFam_zero_right, abs_zero]
    exact Real.sqrt_nonneg _

/-! ## The arithmetic of the majorant `(m+1)^{-3/2}` -/

/-- `√((2m+2)(2m+3)) ≤ √6 · √(m+1) · √(2m+1)`. -/
private lemma sqrt_factor (m : ℕ) :
    Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
      ≤ Real.sqrt 6 * Real.sqrt ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1) := by
  have hb : (2 * (m : ℝ) + 3) ≤ 3 * (2 * (m : ℝ) + 1) := by
    have h : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  calc Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
      = Real.sqrt ((2 * ((m : ℝ) + 1)) * (2 * (m : ℝ) + 3)) := by ring_nf
    _ = Real.sqrt (2 * ((m : ℝ) + 1)) * Real.sqrt (2 * (m : ℝ) + 3) :=
        Real.sqrt_mul (by positivity) _
    _ = (Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1)) * Real.sqrt (2 * (m : ℝ) + 3) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1))
          * (Real.sqrt 3 * Real.sqrt (2 * (m : ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
        exact Real.sqrt_le_sqrt hb
    _ = Real.sqrt 6 * Real.sqrt ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1) := by
        have h6 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
          rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        calc (Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1))
              * (Real.sqrt 3 * Real.sqrt (2 * (m : ℝ) + 1))
            = (Real.sqrt 2 * Real.sqrt 3)
                * (Real.sqrt ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)) := by ring
          _ = Real.sqrt 6 * Real.sqrt ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1) := by
              rw [h6]; ring

/-- The cross-multiplied form of the majorant inequality:
`√((2m+2)(2m+3)) · (m+1)√(m+1) ≤ 300 λ_m √(2m+1)` for `m ≥ 1`. -/
private lemma prod_bound (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
        * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
      ≤ 300 * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hsx : Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 := by
    rw [← sq, Real.sq_sqrt (le_of_lt hx)]
  have hs6 : Real.sqrt 6 ≤ 3 := by
    have h : Real.sqrt 6 ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by norm_num)
    rwa [show Real.sqrt 9 = (3 : ℝ) from by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hlamdef : Work.FTS.PhiStar.Gegenbauer.lam m
      = 2 * (m : ℝ) * (2 * (m : ℝ) + 5) := rfl
  have hcore : Real.sqrt 6 * ((m : ℝ) + 1) ^ 2
      ≤ 300 * Work.FTS.PhiStar.Gegenbauer.lam m := by
    have hsq : ((m : ℝ) + 1) ^ 2 ≤ 2 * (m : ℝ) * (2 * (m : ℝ) + 5) := by nlinarith
    have h2 : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by positivity
    calc Real.sqrt 6 * ((m : ℝ) + 1) ^ 2 ≤ 3 * ((m : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_right hs6 h2
      _ ≤ 3 * (2 * (m : ℝ) * (2 * (m : ℝ) + 5)) :=
          mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 6 * (m : ℝ) * (2 * (m : ℝ) + 5) := by ring
      _ ≤ 300 * Work.FTS.PhiStar.Gegenbauer.lam m := by
          rw [hlamdef]
          nlinarith [show (0 : ℝ) ≤ (m : ℝ) by positivity]
  calc Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
        * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
      ≤ (Real.sqrt 6 * Real.sqrt ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1))
          * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (sqrt_factor m) (by positivity)
    _ = (Real.sqrt 6 * ((m : ℝ) + 1) ^ 2) * Real.sqrt (2 * (m : ℝ) + 1) := by
        calc (Real.sqrt 6 * Real.sqrt ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1))
              * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
            = Real.sqrt 6 * (Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
                * ((m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1) := by ring
          _ = Real.sqrt 6 * ((m : ℝ) + 1) * ((m : ℝ) + 1)
                * Real.sqrt (2 * (m : ℝ) + 1) := by rw [hsx]
          _ = (Real.sqrt 6 * ((m : ℝ) + 1) ^ 2) * Real.sqrt (2 * (m : ℝ) + 1) := by ring
    _ ≤ (300 * Work.FTS.PhiStar.Gegenbauer.lam m) * Real.sqrt (2 * (m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hcore (Real.sqrt_nonneg _)
    _ = 300 * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by ring

/-- The divided form: `√((2m+2)(2m+3)) / (λ_m √(2m+1)) ≤ 300 / ((m+1)√(m+1))`. -/
private lemma expr_le (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
        / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ 300 * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hD : 0 < ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) :=
    mul_pos hx (Real.sqrt_pos.2 hx)
  have hlam : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
    rw [show Work.FTS.PhiStar.Gegenbauer.lam m = 2 * (m : ℝ) * (2 * (m : ℝ) + 5) from rfl]
    nlinarith
  have hN : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
    mul_pos hlam (Real.sqrt_pos.2 (by linarith))
  have hDinv : (300 : ℝ) * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹
      = 300 / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) := by
    rw [inv_eq_one_div, mul_one_div]
  rw [hDinv, div_le_iff₀ hN]
  rw [show (300 : ℝ) / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))
        * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      = 300 * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
        / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) from by ring]
  rw [le_div_iff₀ hD]
  exact prod_bound m hm

/-! ## The pointwise domination by a summable majorant -/

/-- If the coefficients decay like `λ_m^{-1}(2m+1)^{-1/2}` and vanish at `m = 0`, then the
products `c_m e_m(θ)` are dominated on `Iθ` by the summable sequence
`max 1 (300C) · ((m+1)√(m+1))^{-1}`. -/
private lemma pointwise_bound {c : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |c m| ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hzero : c 0 = 0) (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ max 1 (300 * C) * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ := by
  have hDnn : ∀ k : ℕ, 0 ≤ (((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1))⁻¹ := fun k =>
    inv_nonneg.mpr (by positivity)
  by_cases hm : m = 0
  · subst hm
    rw [hzero, zero_mul, abs_zero]
    exact mul_nonneg (le_trans zero_le_one (le_max_left 1 (300 * C))) (hDnn 0)
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hm1R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hlam : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
      rw [show Work.FTS.PhiStar.Gegenbauer.lam m = 2 * (m : ℝ) * (2 * (m : ℝ) + 5) from rfl]
      nlinarith [hm1R]
    have hN : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos hlam (Real.sqrt_pos.2 (by linarith))
    rw [abs_mul]
    calc |c m| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ (C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
            * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) :=
          mul_le_mul (hdec m hm1) (abs_eFam_le_sqrt m hθ) (abs_nonneg _)
            (le_of_lt (div_pos hC hN))
      _ = C * (Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
            / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by ring
      _ ≤ C * (300 * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹) :=
          mul_le_mul_of_nonneg_left (expr_le m hm1) (le_of_lt hC)
      _ = (300 * C) * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ := by ring
      _ ≤ max 1 (300 * C) * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right 1 (300 * C)) (hDnn m)

/-! ## Termwise integration -/

/-- **Termwise integration of the mode series.**  If the modes are dominated by a summable
majorant `u`, the series can be integrated term by term against `eFam n · cos θ`: the `m ≠ n`
terms drop out by orthogonality and only the diagonal survives.  (Dominated convergence with
the uniform majorant; the dominated function is the constant `∑ u_m · √((2n+2)(2n+3))`.) -/
private lemma tsum_moment (b : ℕ → ℝ) (u : ℕ → ℝ) (hu : Summable u)
    (hb : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ u m) (n : ℕ) :
    (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = b n * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
  have hunn : ∀ m : ℕ, 0 ≤ u m := fun m =>
    le_trans (abs_nonneg _) (hb m 0 Work.Spaces.zero_mem_Iθ)
  set K : ℝ := Real.sqrt ((2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 3)) with hK
  have hKnn : 0 ≤ K := Real.sqrt_nonneg _
  have hprod : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)| ≤ u m * K := by
    intro m θ hθ
    have h1 := hb m θ hθ
    have h2 : |Work.FTS.PhiStar.Gegenbauer.eFam n θ| ≤ K := abs_eFam_le_sqrt n hθ
    have h3 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have h4 : |Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ| ≤ K := by
      rw [abs_mul]
      calc |Work.FTS.PhiStar.Gegenbauer.eFam n θ| * |Real.cos θ| ≤ K * 1 :=
            mul_le_mul h2 h3 (abs_nonneg _) hKnn
        _ = K := by ring
    rw [abs_mul]
    exact mul_le_mul h1 h4 (abs_nonneg _) (hunn m)
  haveI hfin : MeasureTheory.IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply_univ]
    exact measure_Icc_lt_top
  have hsumK : Summable (fun m : ℕ => u m * K) := hu.mul_right K
  have hmain := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iθ)
    (F := fun (m : ℕ) (θ : ℝ) => b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
    (f := fun θ : ℝ => (∑' m : ℕ, b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
    (fun (m : ℕ) (_ : ℝ) => u m * K)
    (fun m => ((continuous_const.mul (continuous_eFam m)).mul
      ((continuous_eFam n).mul Real.continuous_cos)).continuousOn.aestronglyMeasurable
        measurableSet_Icc)
    (fun m => by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
      exact Filter.Eventually.of_forall (fun θ hθ => by
        simpa only [Real.norm_eq_abs] using hprod m θ hθ))
    (Filter.Eventually.of_forall (fun _ => hsumK))
    (MeasureTheory.integrable_const _)
    (by
      rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun θ hθ => ?_)
      have hs : Summable (fun m : ℕ => b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
        Summable.of_norm_bounded hu (fun m => by rw [Real.norm_eq_abs]; exact hb m θ hθ)
      exact (hs.hasSum).mul_right (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
  have hFint : ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      = b m * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ
            * Real.cos θ) := by
    intro m
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  have horth : ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ
          * Real.cos θ)
      = if m = n then (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) else 0 := by
    intro m
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    · rw [if_neg hmn, iota_eq_interval]
      exact Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m n hmn
  have hfun : (fun m : ℕ => if m = n then b n * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) else 0)
      = fun m : ℕ => ∫ θ in Work.Spaces.Iθ,
          b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := by
    funext m
    rw [hFint m, horth m]
    by_cases hmn : m = n
    · subst hmn; simp
    · simp [hmn]
  have h2 : HasSum (fun m : ℕ => if m = n then b n * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) else 0)
      (b n * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ)) := hasSum_ite_eq n _
  rw [hfun] at h2
  have huniq := hmain.unique h2
  rw [← huniq]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-! ## The main auxiliary statement -/

/-- **The eigenfunction expansion of a function whose coefficients decay like
`λ_m^{-1}(2m+1)^{-1/2}`.**  For a coefficient family `c` with those two properties (decay, and
`c 0 = 0`) which are the Fourier coefficients of `ψ`, the series `∑_m c_m e_m` converges to
`ψ` pointwise on `(0, π/2)`.  The two analysis inputs are the termwise integration
(`hTsum`) and the a.e.-to-pointwise upgrade (`hMom`). -/
private theorem psiExpansionAux (c : ℕ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |c m| ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hzero : c 0 = 0)
    (hTsum : ∀ (b : ℕ → ℝ) (u : ℕ → ℝ), Summable u →
      (∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
        |b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ u m) →
      ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ,
          (∑' m : ℕ, b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        = b n * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ))
    (hMom : ∀ (v w : ℝ → ℝ), ContinuousOn v (Set.Icc 0 (Real.pi / 2)) →
      ContinuousOn w (Set.Icc 0 (Real.pi / 2)) →
      (∀ n : ℕ, (∫ θ in Work.Spaces.Iθ,
          w θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ, v θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), w θ = v θ)
    (ψ : ℝ → ℝ) (hcontψ : ContinuousOn ψ (Set.Icc 0 (Real.pi / 2)))
    (hcoeff : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ,
        ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = c n * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (∑' m : ℕ, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ := by
  obtain ⟨C, hC, hdec⟩ := hdec
  set K : ℝ := max 1 (300 * C) with hKdef
  set u : ℕ → ℝ := fun m => K * (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹ with hudef
  have hDinv : ∀ m : ℕ, (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹
      = (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹ := by
    intro m
    congr 1
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by positivity : (0 : ℝ) < (m : ℝ) + 1), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hu : Summable u := by
    have hbase : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
      have h0 : Summable (fun n : ℕ => (((n : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
        Real.summable_nat_rpow_inv.mpr (by norm_num)
      have h1 := (summable_nat_add_iff
        (f := fun n : ℕ => (((n : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹) 1).mpr h0
      simpa only [Nat.cast_add, Nat.cast_one] using h1
    have h2 : Summable (fun m : ℕ => (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1))⁻¹) :=
      hbase.congr (fun m => (hDinv m).symm)
    simpa only [hudef, hKdef] using h2.mul_left K
  have hb : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ u m :=
    fun m θ hθ => pointwise_bound hC hdec hzero m hθ
  have hcont : ContinuousOn
      (fun θ => ∑' m, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) Work.Spaces.Iθ :=
    continuousOn_tsum (s := Work.Spaces.Iθ) (u := u)
      (fun m => ((continuous_eFam m).const_mul (c m)).continuousOn) hu
      (fun m x hx => by rw [Real.norm_eq_abs]; exact hb m x hx)
  have hmom : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ,
      ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ,
          (∑' m, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ := by
    intro n
    rw [hcoeff n, hTsum c u hu hb n]
  intro θ hθ
  exact hMom ψ (fun θ => ∑' m, c m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
    hcontψ hcont (fun n => (hmom n).symm) θ hθ

/-! ## The target -/

theorem PsiExpansion : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (ψ : ℝ → ℝ), 0 < α → α ≤ 1 / 5 →
    Work.FTS.PhiStar.AngModel α ψ → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ := by
  refine ⟨1, one_pos, fun α ψ hα hα5 hψ θ hθ => ?_⟩
  -- the coefficient decay of `CmodeDecay`
  obtain ⟨C, hC, hdec0⟩ := Work.FTS.PhiStar.Series.CmodeDecay
  have hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
    ⟨C, hC, fun m hm => hdec0 α ψ hα hα5 hψ m hm⟩
  -- the `m = 0` coefficient vanishes by the moment condition
  have hzero : Work.FTS.PhiStar.Series.cmode 0 (fun _ θ' => ψ θ') 0 = 0 := by
    refine Work.FTS.PhiStar.Series.eFam_zero_moment (fun _ θ' => ψ θ') ?_
    simpa only [Work.Elliptic.Fstar] using hψ.moment
  -- the coefficients are the Fourier coefficients of `ψ`
  have hcoeff : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ,
        ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = Work.FTS.PhiStar.Series.cmode n (fun _ θ' => ψ θ') 0
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
    intro n
    have hnum := iota_eq_interval
      (fun θ => ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
    have hden := iota_eq_interval
      (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ)
    have hne : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) ≠ 0 := by
      rw [← hden]
      exact ne_of_gt (eFam_norm_pos n)
    have hcm : Work.FTS.PhiStar.Series.cmode n (fun _ θ' => ψ θ') 0
        = (∫ θ in (0 : ℝ)..(Real.pi / 2),
              ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
          / (∫ θ in (0 : ℝ)..(Real.pi / 2),
              Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
      simp only [Work.FTS.PhiStar.Series.cmode]
    rw [hnum, hden, hcm, div_mul_cancel₀ _ hne]
  exact psiExpansionAux (fun m => Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0)
    hdec hzero tsum_moment
    Work.FTS.PhiStar.FlatWAux.PsiExpAux.MomentEqOn
    ψ hψ.cont hcoeff θ hθ

end Work.FTS.PhiStar.FlatWAux
