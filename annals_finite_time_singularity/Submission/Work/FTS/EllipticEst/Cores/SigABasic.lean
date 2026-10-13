/-
Copyright: work module for the Elgindi finite-time singularity project.

# The endpoint rate of a slice, in the light weight `σ_a = sin(2θ)^{2-γ}`

The target `sliceRateSigA` is the endpoint rate used by the `Step 5` / interpolation chain:
for a `C¹` slice `Φ` on `(0,π/2)` whose weighted derivative square is `σ_a`-integrable,

* `Φ` has a limit `c` at `0⁺` (and `c'` at `(π/2)⁻`), and
* `(Φ θ - c)² ≤ K θ^{γ-1} ∫_0^θ (Φ')² σ_a`,   `(Φ θ - c')² ≤ K (π/2-θ)^{γ-1} ∫_θ^{π/2} (Φ')² σ_a`

with a constant `K = K(α)` uniform in `Φ`.

## Mathematics

Write `γ = gam α = 1 + α/10` and `p = 2 - γ ∈ (0,1)`, so `σ_a = sin(2θ)^p` and the exponent
`γ - 1 = 1 - p` is the "rate".  The ingredients are

* the Cauchy–Schwarz step `(∫_s Φ')² ≤ (∫_s (Φ')²σ_a)·(∫_s σ_a^{-1})` (`cs_step`),
* the *weight bound* `∫_0^θ σ_a^{-1} ≤ K θ^{γ-1}` (`integral_sigA_inv_le`), which near `0` is
  the Jordan bound `sin(2θ) ≥ 4θ/π` integrated against a power, and for `θ ≥ π/4` is the
  global finiteness `∫_0^{π/2} σ_a^{-1} < ∞`; the mirror statement at `π/2` follows by the
  reflection `θ ↦ π/2 - θ` (`integral_reflect`),
* the fundamental theorem of calculus in its *interior* form (`ftc_interior`), which avoids
  needing a limit hypothesis: instead of integrating from the singular endpoint we normalise
  at `θ₀ = π/4`, `c := Φ(π/4) - ∫_0^{π/4} Φ'`, and split the integrals at `π/4`.

The limit at the endpoint is then a *consequence* of the estimate: `(Φθ - c)² ≤ K θ^{γ-1} M`
with `M = ∫_0^{π/2}(Φ')²σ_a < ∞` forces `Φ θ → c` as `θ → 0⁺`.

Everything in this file is `sorry`-free.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.Spaces.cs_integral
import Submission.Work.Spaces.sin_rpow_le_majorant
import Submission.Work.Spaces.integrableOn_majorant_rpow
import Submission.Work.Spaces.integral_majorant_rpow
import Submission.Work.Spaces.integral_sin_rpow
import Submission.Work.FTS.H2.STBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. The weight `σ_a` and elementary exponent facts -/

/-- The light angular weight `σ_a α θ = sin(2θ)^{2-γ(α)}` (the abbreviation `TT.sigA`). -/
def sigA (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)

/-- `2 - γ(α) > 0` for `α ≤ 1`: the weight vanishes at both endpoints. -/
lemma sub_gam_pos {α : ℝ} (hα1 : α ≤ 1) : 0 < 2 - Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

/-- `2 - γ(α) < 1` for `α > 0`. -/
lemma sub_gam_lt_one {α : ℝ} (hα : 0 < α) : 2 - Work.Spaces.gam α < 1 := by
  rw [Work.Spaces.gam]; linarith

lemma sigA_pos' {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < sigA α θ :=
  Work.FTS.EllipticEst.TT.sigA_pos α θ hθ

/-- `σ_a` is continuous on `ℝ` (the exponent `2-γ` is positive). -/
lemma sigA_continuous (α : ℝ) (hα1 : α ≤ 1) : Continuous (fun t : ℝ => sigA α t) := by
  change Continuous (fun t : ℝ => (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α))
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
    (fun t => Or.inr (le_of_lt (sub_gam_pos hα1)))

/-- **`σ_a` is invariant under `θ ↦ π/2 - θ`.** -/
lemma sigA_reflect {α y : ℝ} : sigA α (Real.pi / 2 - y) = sigA α y := by
  change (Real.sin (2 * (Real.pi / 2 - y))) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α)
  rw [show 2 * (Real.pi / 2 - y) = Real.pi - 2 * y by ring, Real.sin_pi_sub]

/-- `σ_a θ^{-1} = sin(2θ)^{-(2-γ)}` on the open interval. -/
lemma sigA_inv_eq_partial {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (sigA α θ)⁻¹ = (Real.sin (2 * θ)) ^ (-(2 - Work.Spaces.gam α)) := by
  have hpos : 0 < Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hθ
  change ((Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))⁻¹ = _
  exact (Real.rpow_neg hpos.le (2 - Work.Spaces.gam α)).symm

/-- **Integrability of `σ_a^{-1}`** on `[0,π/2]`, by domination with the Jordan majorant
`(π/4)^p (θ^{-p} + (π/2-θ)^{-p})`. -/
lemma integrableOn_sigA_inv {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun t : ℝ => (sigA α t)⁻¹) (Set.Icc 0 (Real.pi / 2)) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := sub_gam_pos hα1
  have hp1 : 2 - Work.Spaces.gam α < 1 := sub_gam_lt_one hα
  refine MeasureTheory.Integrable.mono'
    (Work.Spaces.integrableOn_majorant_rpow (2 - Work.Spaces.gam α) hp0 hp1) ?_ ?_
  · exact (sigA_continuous α hα1).measurable.inv.aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ?_)
    have hsin : 0 ≤ Real.sin (2 * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
    have hmaj := Work.Spaces.sin_rpow_le_majorant (2 - Work.Spaces.gam α) t hp0 ht
    rcases eq_or_lt_of_le hsin with h0 | hpos
    · have hz : sigA α t = 0 := by
        change (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α) = 0
        rw [← h0, Real.zero_rpow (ne_of_gt hp0)]
      rw [hz, inv_zero, norm_zero]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (add_nonneg (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (by linarith [ht.2]) _))
    · have hval : (sigA α t)⁻¹ = (Real.sin (2 * t)) ^ (-(2 - Work.Spaces.gam α)) := by
        change ((Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α))⁻¹ = _
        exact (Real.rpow_neg hpos.le (2 - Work.Spaces.gam α)).symm
      rw [hval, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)]
      exact hmaj

/-! ## 2. The pointwise AM–GM bound and integrability of `Φ'` -/

/-- `2|x| ≤ x²σ + σ^{-1}` for `σ > 0` (`(x√σ - 1/√σ)² ≥ 0`). -/
lemma two_abs_le_sq_mul_add_inv {σ x : ℝ} (hσ : 0 < σ) : 2 * |x| ≤ x ^ 2 * σ + σ⁻¹ := by
  have hu2 : (Real.sqrt σ) ^ 2 = σ := Real.sq_sqrt hσ.le
  have hu0 : 0 < Real.sqrt σ := Real.sqrt_pos_of_pos hσ
  have h1 : (|x| * Real.sqrt σ) ^ 2 = x ^ 2 * σ := by rw [mul_pow, sq_abs, hu2]
  have h2 : ((Real.sqrt σ)⁻¹) ^ 2 = σ⁻¹ := by rw [inv_pow, hu2]
  have h3 : (|x| * Real.sqrt σ) * (Real.sqrt σ)⁻¹ = |x| := by
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hu0), mul_one]
  have h4 := two_mul_le_add_sq (|x| * Real.sqrt σ) ((Real.sqrt σ)⁻¹)
  rw [h1, h2] at h4
  rw [mul_assoc, h3] at h4
  exact h4

/-- **Integrability of `Φ'`** on any `s ⊆ (0,π/2)` where both `(Φ')²σ_a` and `σ_a^{-1}` are
integrable (AM–GM). -/
lemma integrableOn_deriv {α : ℝ} {Φ : ℝ → ℝ} {s : Set ℝ}
    (hsm : MeasurableSet s) (hs : s ⊆ Set.Ioo 0 (Real.pi / 2))
    (hA : IntegrableOn (fun t => (deriv Φ t) ^ 2 * sigA α t) s)
    (hB : IntegrableOn (fun t => (sigA α t)⁻¹) s) :
    IntegrableOn (deriv Φ) s := by
  have hdom : Integrable (fun t => (deriv Φ t) ^ 2 * sigA α t + (sigA α t)⁻¹)
      (volume.restrict s) := hA.add hB
  refine MeasureTheory.Integrable.mono' hdom (measurable_deriv Φ).aestronglyMeasurable ?_
  refine MeasureTheory.ae_restrict_of_forall_mem hsm (fun t ht => ?_)
  have hσ : 0 < sigA α t := sigA_pos' (hs ht)
  have h := two_abs_le_sq_mul_add_inv (σ := sigA α t) (x := deriv Φ t) hσ
  rw [Real.norm_eq_abs]
  linarith [h, abs_nonneg (deriv Φ t)]

/-- **Cauchy–Schwarz for the slice**: `(∫_s Φ')² ≤ (∫_s (Φ')²σ_a)(∫_s σ_a^{-1})`. -/
lemma cs_step {α : ℝ} (hα1 : α ≤ 1) {Φ : ℝ → ℝ} {s : Set ℝ}
    (hsm : MeasurableSet s) (hs : s ⊆ Set.Ioo 0 (Real.pi / 2))
    (hA : IntegrableOn (fun t => (deriv Φ t) ^ 2 * sigA α t) s)
    (hB : IntegrableOn (fun t => (sigA α t)⁻¹) s) :
    (∫ t in s, deriv Φ t) ^ 2
      ≤ (∫ t in s, (deriv Φ t) ^ 2 * sigA α t) * (∫ t in s, (sigA α t)⁻¹) := by
  set u : ℝ → ℝ := fun t => deriv Φ t * Real.sqrt (sigA α t) with hu
  set v : ℝ → ℝ := fun t => (Real.sqrt (sigA α t))⁻¹ with hv
  have hsig : ∀ t ∈ s, 0 < sigA α t := fun t ht => sigA_pos' (hs ht)
  have haesm_u : AEStronglyMeasurable u (volume.restrict s) := by
    rw [hu]
    exact (measurable_deriv Φ).aestronglyMeasurable.mul
      ((sigA_continuous α hα1).sqrt.aestronglyMeasurable)
  have haesm_v : AEStronglyMeasurable v (volume.restrict s) := by
    rw [hv]
    exact ((Continuous.sqrt (sigA_continuous α hα1)).continuousOn.inv₀
      (fun t ht => ne_of_gt (Real.sqrt_pos_of_pos (hsig t ht)))).aestronglyMeasurable hsm
  have huM : MemLp u 2 (volume.restrict s) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq haesm_u]
    refine hA.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hsm (fun t ht => ?_)
    rw [hu]; simp only []
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hsig t ht))]
  have hvM : MemLp v 2 (volume.restrict s) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq haesm_v]
    refine hB.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hsm (fun t ht => ?_)
    rw [hv]; simp only []
    rw [inv_pow, Real.sq_sqrt (le_of_lt (hsig t ht))]
  have hcs := Work.Spaces.cs_integral huM hvM
  have h1 : ∫ x in s, u x * v x = ∫ x in s, deriv Φ x := by
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hsm (fun t ht => ?_)
    rw [hu, hv]; simp only []
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos_of_pos (hsig t ht))), mul_one]
  have h2 : ∫ x in s, u x ^ 2 = ∫ x in s, (deriv Φ x) ^ 2 * sigA α x := by
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hsm (fun t ht => ?_)
    rw [hu]; simp only []
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hsig t ht))]
  have h3 : ∫ x in s, v x ^ 2 = ∫ x in s, (sigA α x)⁻¹ := by
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem hsm (fun t ht => ?_)
    rw [hv]; simp only []
    rw [inv_pow, Real.sq_sqrt (le_of_lt (hsig t ht))]
  rw [h1, h2, h3] at hcs
  exact hcs

/-! ## 3. The weight bound `∫_0^θ σ_a^{-1} ≤ K θ^{γ-1}` -/

/-- `(π/2 - t)^{-p} ≤ (4/π)^p` for `t ∈ (0,θ)`, `θ ≤ π/4` (`p > 0`). -/
lemma shift_le_const {p t θ : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) θ) (hsmall : θ ≤ Real.pi / 4)
    (hp0 : 0 < p) : (Real.pi / 2 - t) ^ (-p) ≤ (4 / Real.pi) ^ p := by
  have hge : Real.pi / 4 ≤ Real.pi / 2 - t := by linarith [ht.2, hsmall]
  have h1 : (Real.pi / 2 - t) ^ (-p) ≤ (Real.pi / 4) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [Real.pi_pos]) hge (by linarith)
  have h2 : (Real.pi / 4) ^ (-p) = (4 / Real.pi) ^ p := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ Real.pi / 4) p,
      show (4 : ℝ) / Real.pi = (Real.pi / 4)⁻¹ from by rw [inv_div π 4],
      Real.inv_rpow (by positivity : (0 : ℝ) ≤ Real.pi / 4) p]
  rw [← h2]
  exact h1

/-- Continuity on `(0,θ)` of `t ↦ (π/2-t)^{-p}`, for `θ ≤ π/4`. -/
lemma shift_cont {p θ : ℝ} (hsmall : θ ≤ Real.pi / 4) :
    ContinuousOn (fun t : ℝ => (Real.pi / 2 - t) ^ (-p)) (Set.Ioo (0 : ℝ) θ) :=
  ((continuous_const.sub continuous_id).continuousOn).rpow_const
    (fun t ht => Or.inl (show Real.pi / 2 - t ≠ 0 from by linarith [ht.2, hsmall, Real.pi_pos]))

/-- **The partial weight bound for the singular power weight**: for `0 < p < 1` and
`0 < θ ≤ π/2`,
`∫_{(0,θ)} sin(2t)^{-p} ≤ ((π/4)^p/(1-p) + 1 + (100/(1-p))(π/4)^{p-1}) θ^{1-p}`.

For `θ ≤ π/4` this is the Jordan majorant `sin(2t) ≥ 4t/π` integrated against the power
`t^{-p}`; for `θ ≥ π/4` it is the global bound `∫_0^{π/2} sin(2t)^{-p} ≤ 100/(1-p)`
scaled by `θ^{1-p} ≥ (π/4)^{1-p}`. -/
lemma integral_sin_rpow_neg_partial {p θ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hθ0 : 0 < θ) (hθ : θ ≤ Real.pi / 2) :
    ∫ t in Set.Ioo 0 θ, (Real.sin (2 * t)) ^ (-p)
      ≤ ((Real.pi / 4) ^ p / (1 - p) + 1 + (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1))
          * θ ^ (1 - p) := by
  have hIntIcc : MeasureTheory.IntegrableOn (fun t : ℝ => (Real.sin (2 * t)) ^ (-p))
      (Set.Icc 0 (Real.pi / 2)) :=
    (Work.Spaces.sin_two_rpow (-p) (by linarith) (by linarith)).1
  have hTotal : ∫ t in Set.Icc 0 (Real.pi / 2), (Real.sin (2 * t)) ^ (-p) ≤ 100 / (1 - p) := by
    have h := (Work.Spaces.sin_two_rpow (-p) (by linarith) (by linarith)).2
    have he : (-p : ℝ) + 1 = 1 - p := by ring
    rwa [he] at h
  have hsub : Set.Ioo (0 : ℝ) θ ⊆ Set.Icc 0 (Real.pi / 2) :=
    fun t ht => ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) hθ⟩
  rcases le_or_gt θ (Real.pi / 4) with hsmall | hbig
  · -- ===== Case `θ ≤ π/4` =====
    have hθle1 : θ ≤ 1 := by linarith [hsmall, Real.pi_lt_four]
    have hmajInt : MeasureTheory.IntegrableOn
        (fun t : ℝ => (Real.pi / 4) ^ p * (t ^ (-p) + (Real.pi / 2 - t) ^ (-p)))
        (Set.Ioo 0 θ) :=
      (Work.Spaces.integrableOn_majorant_rpow p hp0 hp1).mono_set hsub
    have hIntθ : MeasureTheory.IntegrableOn (fun t : ℝ => (Real.sin (2 * t)) ^ (-p))
        (Set.Ioo 0 θ) := hIntIcc.mono_set hsub
    have hmono : ∫ t in Set.Ioo 0 θ, (Real.sin (2 * t)) ^ (-p)
        ≤ ∫ t in Set.Ioo 0 θ, (Real.pi / 4) ^ p * (t ^ (-p) + (Real.pi / 2 - t) ^ (-p)) := by
      refine MeasureTheory.integral_mono_ae hIntθ hmajInt ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun t ht => Work.Spaces.sin_rpow_le_majorant p t hp0 (hsub ht))
    have hpowInt : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-p)) (Set.Ioo 0 θ) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hθ0).mpr (by linarith)
    have hshiftInt : MeasureTheory.IntegrableOn (fun t : ℝ => (Real.pi / 2 - t) ^ (-p))
        (Set.Ioo 0 θ) := by
      have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (4 / Real.pi) ^ p) (Set.Ioo 0 θ) :=
        MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      refine MeasureTheory.Integrable.mono' hconst ?_ ?_
      · exact (shift_cont hsmall).aestronglyMeasurable measurableSet_Ioo
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => ?_)
        rw [Real.norm_of_nonneg (Real.rpow_nonneg
          (by linarith [ht.2, hsmall, Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2 - t) _)]
        exact shift_le_const ht hsmall hp0
    have hsplit : ∫ t in Set.Ioo 0 θ, ((Real.pi / 4) ^ p * (t ^ (-p) + (Real.pi / 2 - t) ^ (-p)))
        = (Real.pi / 4) ^ p * ((∫ t in Set.Ioo 0 θ, t ^ (-p))
            + ∫ t in Set.Ioo 0 θ, (Real.pi / 2 - t) ^ (-p)) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hpowInt hshiftInt]
    have hI1 : ∫ t in Set.Ioo 0 θ, t ^ (-p) = θ ^ (1 - p) / (1 - p) := by
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hθ0.le]
      rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -p))]
      rw [show (-p + 1 : ℝ) = 1 - p by ring, Real.zero_rpow (by linarith : (1 - p) ≠ 0)]
      ring
    have hI2 : ∫ t in Set.Ioo 0 θ, (Real.pi / 2 - t) ^ (-p) ≤ θ * (4 / Real.pi) ^ p := by
      have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (4 / Real.pi) ^ p) (Set.Ioo 0 θ) :=
        MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      have hcmp : ∫ t in Set.Ioo 0 θ, (Real.pi / 2 - t) ^ (-p)
          ≤ ∫ t in Set.Ioo 0 θ, ((4 / Real.pi) ^ p) := by
        refine MeasureTheory.integral_mono_ae hshiftInt hconst ?_
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun t ht => shift_le_const ht hsmall hp0)
      have hval : ∫ t in Set.Ioo 0 θ, ((4 / Real.pi) ^ p) = θ * (4 / Real.pi) ^ p := by
        rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hθ0.le,
          intervalIntegral.integral_const, sub_zero]
        simp [smul_eq_mul]
      linarith [hcmp, hval.le, hval.ge]
    have hcancel : (Real.pi / 4) ^ p * (4 / Real.pi) ^ p = 1 := by
      rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ Real.pi / 4)
          (by positivity : (0 : ℝ) ≤ 4 / Real.pi),
        show Real.pi / 4 * (4 / Real.pi) = 1 from by field_simp, Real.one_rpow]
    have hθpow : θ ≤ θ ^ (1 - p) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hθ0 hθle1 (show (1 : ℝ) - p ≤ 1 by linarith)
      simpa using h
    have hcoef1 : (0 : ℝ) ≤ (Real.pi / 4) ^ p / (1 - p) :=
      div_nonneg (Real.rpow_nonneg (by positivity) _) (by linarith)
    have hstep : (Real.pi / 4) ^ p * (θ ^ (1 - p) / (1 - p) + θ * (4 / Real.pi) ^ p)
        ≤ ((Real.pi / 4) ^ p / (1 - p) + 1) * θ ^ (1 - p) := by
      have h1 : (Real.pi / 4) ^ p * (θ * (4 / Real.pi) ^ p) = θ := by
        rw [mul_comm θ (((4 : ℝ) / Real.pi) ^ p), ← mul_assoc, hcancel, one_mul]
      have hkey : (Real.pi / 4) ^ p * (θ ^ (1 - p) / (1 - p))
          = ((Real.pi / 4) ^ p / (1 - p)) * θ ^ (1 - p) := by ring
      rw [mul_add, h1, hkey]
      have hB : (0 : ℝ) ≤ θ ^ (1 - p) := Real.rpow_nonneg hθ0.le _
      nlinarith [hcoef1, hθpow, hB]
    have hfin : ((Real.pi / 4) ^ p / (1 - p) + 1) * θ ^ (1 - p)
        ≤ ((Real.pi / 4) ^ p / (1 - p) + 1 + (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1))
            * θ ^ (1 - p) := by
      have hnn : (0 : ℝ) ≤ (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1) :=
        mul_nonneg (div_nonneg (by norm_num) (by linarith)) (Real.rpow_nonneg (by positivity) _)
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hθ0.le _)
    calc ∫ t in Set.Ioo 0 θ, (Real.sin (2 * t)) ^ (-p)
        ≤ ∫ t in Set.Ioo 0 θ, (Real.pi / 4) ^ p
            * (t ^ (-p) + (Real.pi / 2 - t) ^ (-p)) := hmono
      _ = (Real.pi / 4) ^ p * ((∫ t in Set.Ioo 0 θ, t ^ (-p))
            + ∫ t in Set.Ioo 0 θ, (Real.pi / 2 - t) ^ (-p)) := hsplit
      _ ≤ (Real.pi / 4) ^ p * (θ ^ (1 - p) / (1 - p) + θ * (4 / Real.pi) ^ p) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
          exact add_le_add hI1.le hI2
      _ ≤ ((Real.pi / 4) ^ p / (1 - p) + 1) * θ ^ (1 - p) := hstep
      _ ≤ _ := hfin
  · -- ===== Case `θ ≥ π/4` =====
    have hmono : ∫ t in Set.Ioo 0 θ, (Real.sin (2 * t)) ^ (-p)
        ≤ ∫ t in Set.Icc 0 (Real.pi / 2), (Real.sin (2 * t)) ^ (-p) := by
      refine MeasureTheory.setIntegral_mono_set hIntIcc ?_ ?_
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun t ht => Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
            (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])) _)
      · exact MeasureTheory.ae_le_set.mpr (by rw [Set.sdiff_eq_empty.mpr hsub, measure_empty])
    have h1 : (Real.pi / 4) ^ (p - 1) * θ ^ (1 - p) = (θ / (Real.pi / 4)) ^ (1 - p) := by
      rw [Real.div_rpow hθ0.le (by positivity : (0 : ℝ) ≤ Real.pi / 4) (1 - p)]
      have hL : (Real.pi / 4) ^ (p - 1) = ((Real.pi / 4) ^ (1 - p))⁻¹ := by
        rw [show p - 1 = -(1 - p) by ring,
          Real.rpow_neg (by positivity : (0 : ℝ) ≤ Real.pi / 4) (1 - p)]
      rw [hL]
      ring
    have hge1 : (1 : ℝ) ≤ (θ / (Real.pi / 4)) ^ (1 - p) :=
      Real.one_le_rpow (by rw [le_div_iff₀ (by linarith [Real.pi_pos])]; linarith) (by linarith)
    have hmain : 100 / (1 - p) ≤ (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1) * θ ^ (1 - p) := by
      rw [mul_assoc, h1]
      exact le_mul_of_one_le_right (div_nonneg (by norm_num) (by linarith)) hge1
    have hbig2 : (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1)
        ≤ (Real.pi / 4) ^ p / (1 - p) + 1 + (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1) := by
      have h2 : (0 : ℝ) ≤ (Real.pi / 4) ^ p / (1 - p) + 1 := by
        have h3 := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) p
        have h4 := div_nonneg h3 (by linarith : (0 : ℝ) ≤ 1 - p)
        linarith
      linarith
    have h2 : 100 / (1 - p) ≤ ((Real.pi / 4) ^ p / (1 - p) + 1
        + (100 / (1 - p)) * (Real.pi / 4) ^ (p - 1)) * θ ^ (1 - p) :=
      hmain.trans (mul_le_mul_of_nonneg_right hbig2 (Real.rpow_nonneg hθ0.le _))
    linarith [hmono, hTotal, h2]

/-- **The weight bound in the form needed downstream**: for `α ∈ (0,1]` and `θ ∈ (0,π/2)`,
`∫_{(0,θ)} σ_a^{-1} ≤ K θ^{γ-1}`. -/
lemma integral_sigA_inv_le_partial (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∫ t in Set.Ioo 0 θ, (sigA α t)⁻¹
      ≤ ((Real.pi / 4) ^ (2 - Work.Spaces.gam α) / (1 - (2 - Work.Spaces.gam α)) + 1
          + (100 / (1 - (2 - Work.Spaces.gam α)))
              * (Real.pi / 4) ^ ((2 - Work.Spaces.gam α) - 1))
        * θ ^ (Work.Spaces.gam α - 1) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := sub_gam_pos hα1
  have hp1 : 2 - Work.Spaces.gam α < 1 := sub_gam_lt_one hα
  have hcongr : ∫ t in Set.Ioo 0 θ, (sigA α t)⁻¹
      = ∫ t in Set.Ioo 0 θ, (Real.sin (2 * t)) ^ (-(2 - Work.Spaces.gam α)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun t ht => sigA_inv_eq_partial ⟨ht.1, by linarith [ht.2, hθ.2]⟩)
  rw [hcongr]
  have h := integral_sin_rpow_neg_partial (p := 2 - Work.Spaces.gam α) hp0 hp1 hθ.1 hθ.2.le
  have hgam : Work.Spaces.gam α - 1 = 1 - (2 - Work.Spaces.gam α) := by ring
  rwa [hgam]

/-- The same with an existential constant, for a compact statement. -/
lemma integral_sigA_inv_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ KW : ℝ, 0 < KW ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ∫ t in Set.Ioo 0 θ, (sigA α t)⁻¹ ≤ KW * θ ^ (Work.Spaces.gam α - 1) := by
  refine ⟨_, ?_, fun θ hθ => integral_sigA_inv_le_partial α hα hα1 hθ⟩
  have hp0 : 0 < 2 - Work.Spaces.gam α := sub_gam_pos hα1
  have hp1 : 2 - Work.Spaces.gam α < 1 := sub_gam_lt_one hα
  have h1 : (0 : ℝ) < (Real.pi / 4) ^ (2 - Work.Spaces.gam α) / (1 - (2 - Work.Spaces.gam α)) :=
    div_pos (Real.rpow_pos_of_pos (by linarith [Real.pi_pos]) _) (by linarith)
  have h2 : (0 : ℝ) < (100 / (1 - (2 - Work.Spaces.gam α)))
      * (Real.pi / 4) ^ ((2 - Work.Spaces.gam α) - 1) :=
    mul_pos (div_pos (by norm_num) (by linarith))
      (Real.rpow_pos_of_pos (by linarith [Real.pi_pos]) _)
  linarith

/-! ## 4. The reflection `θ ↦ π/2 - θ` -/

/-- **Change of variables** `y ↦ π/2 - y` on the intervals `(0,t)` and `(π/2-t, π/2)`. -/
lemma integral_reflect {g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    ∫ y in Set.Ioo 0 t, g (Real.pi / 2 - y)
      = ∫ x in Set.Ioo (Real.pi / 2 - t) (Real.pi / 2), g x := by
  calc ∫ y in Set.Ioo 0 t, g (Real.pi / 2 - y)
      = ∫ y in (0 : ℝ)..t, g (Real.pi / 2 - y) := by
        rw [intervalIntegral.integral_of_le ht, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    _ = ∫ x in (Real.pi / 2 - t)..(Real.pi / 2), g x := by
        rw [intervalIntegral.integral_comp_sub_left g (Real.pi / 2)]
        simp
    _ = ∫ x in Set.Ioo (Real.pi / 2 - t) (Real.pi / 2), g x := by
        rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
          MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **The mirror weight bound**: `∫_{(θ,π/2)} σ_a^{-1} ≤ K (π/2-θ)^{γ-1}`. -/
lemma integral_sigA_inv_le_right (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ KW : ℝ, 0 < KW ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      ∫ t in Set.Ioo θ (Real.pi / 2), (sigA α t)⁻¹
        ≤ KW * (Real.pi / 2 - θ) ^ (Work.Spaces.gam α - 1) := by
  obtain ⟨KW, hKW, hKWb⟩ := integral_sigA_inv_le α hα hα1
  refine ⟨KW, hKW, fun θ hθ => ?_⟩
  have h1 : ∫ y in Set.Ioo 0 (Real.pi / 2 - θ), (sigA α (Real.pi / 2 - y))⁻¹
      = ∫ y in Set.Ioo 0 (Real.pi / 2 - θ), (sigA α y)⁻¹ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun y _ => by rw [sigA_reflect])
  have h2 := integral_reflect (g := fun t => (sigA α t)⁻¹) (t := Real.pi / 2 - θ)
    (by linarith [hθ.2])
  rw [show Real.pi / 2 - (Real.pi / 2 - θ) = θ from by ring] at h2
  rw [← h2, h1]
  exact hKWb (Real.pi / 2 - θ) ⟨by linarith [hθ.2], by linarith [hθ.1, Real.pi_pos]⟩

/-- The reflection of the filters: `y ↦ π/2 - y` maps `0⁺` to `(π/2)⁻`. -/
lemma tendsto_reflect_iff {Φ : ℝ → ℝ} {c : ℝ} :
    Tendsto (fun y => Φ (Real.pi / 2 - y)) (nhdsWithin 0 (Set.Ioi 0)) (nhds c)
      ↔ Tendsto Φ (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) := by
  have hbase : Continuous (fun y : ℝ => Real.pi / 2 - y) := continuous_const.sub continuous_id
  constructor
  · intro h
    have hmap : Tendsto (fun x : ℝ => Real.pi / 2 - x)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h1 := (hbase.continuousAt (x := Real.pi / 2)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Set.Iio (Real.pi / 2)) (a := Real.pi / 2))
        simpa using h1
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [Set.mem_Iio] at hx
        simp only [Set.mem_Ioi]
        linarith
    have h2 := h.comp hmap
    have hcomp : ((fun y : ℝ => Φ (Real.pi / 2 - y)) ∘ (fun x : ℝ => Real.pi / 2 - x)) = Φ := by
      funext x
      simp only [Function.comp_apply]
      congr 1
      ring
    rwa [hcomp] at h2
  · intro h
    have hmap : Tendsto (fun y : ℝ => Real.pi / 2 - y) (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h1 := (hbase.continuousAt (x := 0)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi 0) (a := 0))
        simpa using h1
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [Set.mem_Ioi] at hx
        simp only [Set.mem_Iio]
        linarith
    have h2 := h.comp hmap
    have hcomp : (Φ ∘ (fun y : ℝ => Real.pi / 2 - y)) = fun y => Φ (Real.pi / 2 - y) := rfl
    rwa [hcomp] at h2

/-- `A y^e → 0` as `y → 0⁺` (for `e > 0`). -/
lemma tendsto_const_mul_rpow_zero {A e : ℝ} (he : 0 < e) :
    Tendsto (fun y : ℝ => A * y ^ e) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h : ContinuousAt (fun y : ℝ => A * y ^ e) 0 :=
    continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr he.le))
  have h0 : (0 : ℝ) ^ e = 0 := Real.zero_rpow (ne_of_gt he)
  simpa [h0] using h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0) (a := 0))

/-- Squeeze: a function dominated by `A y^e` off `0` tends to `0` at `0⁺`. -/
lemma tendsto_zero_of_abs_le {F : ℝ → ℝ} {A e : ℝ} (he : 0 < e)
    (h : ∀ y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |F y| ≤ A * y ^ e) :
    Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (f := fun y => ‖F y‖) (g := fun y => A * y ^ e) ?_ ?_
      (tendsto_const_mul_rpow_zero (A := A) he))
  · filter_upwards with y
    exact norm_nonneg (F y)
  · filter_upwards [Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)] with y hy
    simpa [Real.norm_eq_abs] using h y hy

/-! ## 5. The fundamental theorem of calculus in the interior -/

/-- **Interior FTC.**  For `u < v` both in `(0,π/2)` and `Φ` of class `C¹` there,
`Φ v - Φ u = ∫_{(u,v)} Φ'`. -/
lemma ftc_interior {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 1 Φ (Set.Ioo 0 (Real.pi / 2)))
    {u v : ℝ} (hu : u ∈ Set.Ioo 0 (Real.pi / 2)) (hv : v ∈ Set.Ioo 0 (Real.pi / 2)) (huv : u < v)
    (hint : IntervalIntegrable (deriv Φ) volume u v) :
    Φ v - Φ u = ∫ t in Set.Ioo u v, deriv Φ t := by
  have hderiv : ∀ x ∈ Set.Ioo u v, HasDerivAt Φ (deriv Φ x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := ⟨by linarith [hu.1, hx.1], by linarith [hv.2, hx.2]⟩
    exact ((hΦ.differentiableOn_one.differentiableAt (Ioo_mem_nhds hx'.1 hx'.2))).hasDerivAt
  have hcu : Tendsto Φ (nhdsWithin u (Set.Ioi u)) (nhds (Φ u)) :=
    (hΦ.continuousOn.continuousAt (Ioo_mem_nhds hu.1 hu.2)).tendsto.mono_left nhdsWithin_le_nhds
  have hcv : Tendsto Φ (nhdsWithin v (Set.Iio v)) (nhds (Φ v)) :=
    (hΦ.continuousOn.continuousAt (Ioo_mem_nhds hv.1 hv.2)).tendsto.mono_left nhdsWithin_le_nhds
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto huv hderiv hint hcu hcv
  rw [← h, intervalIntegral.integral_of_le huv.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **Additivity of the slice integral at an interior point** (a single point is negligible, so
this is the interval-integral splitting rule). -/
lemma setIntegral_Ioo_add_adjacent {a b c : ℝ} {f : ℝ → ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : IntegrableOn f (Set.Ioo a b)) (h2 : IntegrableOn f (Set.Ioo b c)) :
    (∫ t in Set.Ioo a b, f t) + (∫ t in Set.Ioo b c, f t) = ∫ t in Set.Ioo a c, f t := by
  have h1' : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab (by simp) (by simp)).mpr h1
  have h2' : IntervalIntegrable f volume b c :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hbc (by simp) (by simp)).mpr h2
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hbc,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (le_trans hab hbc)]
  exact intervalIntegral.integral_add_adjacent_intervals h1' h2'

/-! ## 6. The FTC normalised at `θ₀ = π/4`, and the squeeze for the endpoint limits -/

/-- **The FTC identity at the left endpoint.**  With the normalisation
`c := Φ(π/4) - ∫_0^{π/4} Φ'` one has `Φ θ - c = ∫_0^θ Φ'` for every `θ ∈ (0,π/2)`.
(The splitting of the integral at `π/4` is `setIntegral_Ioo_add_adjacent`; the missing point
`π/4` is irrelevant.) -/
lemma ftc_at_quarter {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 1 Φ (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (deriv Φ) (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Φ θ - (Φ (Real.pi / 4) - ∫ t in Set.Ioo 0 (Real.pi / 4), deriv Φ t)
        = ∫ t in Set.Ioo 0 θ, deriv Φ t := by
  intro θ hθ
  have hπ4 : (Real.pi / 4) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hfour : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hintm : IntegrableOn (deriv Φ) (Set.Ioo 0 (Real.pi / 4)) :=
    hint.mono_set (fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)
  rcases lt_trichotomy θ (Real.pi / 4) with hlt | heq | hgt
  · have hIntθ : IntegrableOn (deriv Φ) (Set.Ioo 0 θ) :=
      hint.mono_set (fun x hx => ⟨hx.1, by linarith [hx.2, hlt, Real.pi_pos]⟩)
    have hIntmid : IntegrableOn (deriv Φ) (Set.Ioo θ (Real.pi / 4)) :=
      hint.mono_set (fun x hx => ⟨by linarith [hθ.1, hx.1], by linarith [hx.2, Real.pi_pos]⟩)
    have hftc : Φ (Real.pi / 4) - Φ θ = ∫ t in Set.Ioo θ (Real.pi / 4), deriv Φ t :=
      ftc_interior hΦ hθ hπ4 hlt
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le hlt.le (by simp) (by simp)).mpr hIntmid)
    have hsplit := setIntegral_Ioo_add_adjacent hθ.1.le hlt.le hIntθ hIntmid
    linarith [hftc, hsplit]
  · subst heq
    ring
  · have hIntmid : IntegrableOn (deriv Φ) (Set.Ioo (Real.pi / 4) θ) :=
      hint.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩)
    have hftc : Φ θ - Φ (Real.pi / 4) = ∫ t in Set.Ioo (Real.pi / 4) θ, deriv Φ t :=
      ftc_interior hΦ hπ4 hθ hgt
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le hgt.le (by simp) (by simp)).mpr hIntmid)
    have hsplit := setIntegral_Ioo_add_adjacent hfour.le hgt.le hintm hIntmid
    linarith [hftc, hsplit]

/-- **The FTC identity at the right endpoint.**  With the normalisation
`c := Φ(π/4) + ∫_{π/4}^{π/2} Φ'` one has `Φ θ - c = -∫_θ^{π/2} Φ'` for every `θ ∈ (0,π/2)`. -/
lemma ftc_at_quarter_right {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 1 Φ (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (deriv Φ) (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Φ θ - (Φ (Real.pi / 4) + ∫ t in Set.Ioo (Real.pi / 4) (Real.pi / 2), deriv Φ t)
        = -(∫ t in Set.Ioo θ (Real.pi / 2), deriv Φ t) := by
  intro θ hθ
  have hπ4 : (Real.pi / 4) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hfour : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hintm : IntegrableOn (deriv Φ) (Set.Ioo (Real.pi / 4) (Real.pi / 2)) :=
    hint.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  rcases lt_trichotomy θ (Real.pi / 4) with hlt | heq | hgt
  · have hIntθ : IntegrableOn (deriv Φ) (Set.Ioo θ (Real.pi / 4)) :=
      hint.mono_set (fun x hx => ⟨by linarith [hθ.1, hx.1], by linarith [hx.2, Real.pi_pos]⟩)
    have hftc : Φ (Real.pi / 4) - Φ θ = ∫ t in Set.Ioo θ (Real.pi / 4), deriv Φ t :=
      ftc_interior hΦ hθ hπ4 hlt
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le hlt.le (by simp) (by simp)).mpr hIntθ)
    have hsplit := setIntegral_Ioo_add_adjacent hlt.le
      (by linarith [Real.pi_pos] : Real.pi / 4 ≤ Real.pi / 2) hIntθ hintm
    linarith [hftc, hsplit]
  · subst heq
    ring
  · have hIntmid : IntegrableOn (deriv Φ) (Set.Ioo (Real.pi / 4) θ) :=
      hint.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, hθ.2]⟩)
    have hIntθ2 : IntegrableOn (deriv Φ) (Set.Ioo θ (Real.pi / 2)) :=
      hint.mono_set (fun x hx => ⟨by linarith [hgt.le, hx.1], hx.2⟩)
    have hftc : Φ θ - Φ (Real.pi / 4) = ∫ t in Set.Ioo (Real.pi / 4) θ, deriv Φ t :=
      ftc_interior hΦ hπ4 hθ hgt
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le hgt.le (by simp) (by simp)).mpr hIntmid)
    have hsplit := setIntegral_Ioo_add_adjacent hgt.le hθ.2.le hIntmid hIntθ2
    linarith [hftc, hsplit]

/-- From a bound on the square, the corresponding bound on the absolute value with the
`e/2`-power. -/
lemma abs_le_sqrt_mul_rpow {x K M e θ : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hθ : 0 ≤ θ)
    (h : x ^ 2 ≤ K * M * θ ^ e) :
    |x| ≤ Real.sqrt (K * M) * θ ^ (e / 2) := by
  have h2 : (θ ^ (e / 2)) ^ 2 = θ ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hθ]
    congr 1
    push_cast
    ring
  have hsq : (Real.sqrt (K * M) * θ ^ (e / 2)) ^ 2 = K * M * θ ^ e := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hK hM), h2]
  have h1 : Real.sqrt (x ^ 2) ≤ Real.sqrt ((Real.sqrt (K * M) * θ ^ (e / 2)) ^ 2) :=
    Real.sqrt_le_sqrt (by rw [hsq]; exact h)
  rw [Real.sqrt_sq_eq_abs,
    Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hθ _))] at h1
  exact h1

/-- The reflected squeeze: a function whose reflected version is dominated by `A y^e` at `0⁺`
has limit `0` at `(π/2)⁻`. -/
lemma tendsto_zero_of_abs_le_reflect {F : ℝ → ℝ} {A e : ℝ} (he : 0 < e)
    (h : ∀ y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |F (Real.pi / 2 - y)| ≤ A * y ^ e) :
    Tendsto F (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
  (tendsto_reflect_iff (Φ := F)).mp (tendsto_zero_of_abs_le he h)

/-! ## 7. Elementary nonnegativity helpers -/

lemma sigA_nonneg' {α θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) : 0 ≤ sigA α θ :=
  Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ

lemma inv_sigA_nonneg {α x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) : 0 ≤ (sigA α x)⁻¹ :=
  le_of_lt (inv_pos.mpr (sigA_pos' hx))

lemma sq_mul_sigA_nonneg {α x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (y : ℝ) :
    0 ≤ y ^ 2 * sigA α x :=
  mul_nonneg (sq_nonneg y) (sigA_nonneg' ⟨hx.1.le, hx.2.le⟩)

/-- Monotonicity of the slice integral in the right endpoint (nonnegative integrand). -/
lemma setIntegral_mono_Ioo {f : ℝ → ℝ} {a b c : ℝ} (hbc : b ≤ c)
    (hint : IntegrableOn f (Set.Ioo a c)) (hnn : ∀ x ∈ Set.Ioo a c, 0 ≤ f x) :
    ∫ x in Set.Ioo a b, f x ≤ ∫ x in Set.Ioo a c, f x := by
  have hsub : Set.Ioo a b ⊆ Set.Ioo a c := fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hbc⟩
  have hae : (Set.Ioo a b : Set ℝ) ≤ᵐ[volume] (Set.Ioo a c : Set ℝ) := by
    rw [MeasureTheory.ae_le_set, Set.sdiff_eq_empty.mpr hsub, measure_empty]
  exact MeasureTheory.setIntegral_mono_set hint
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hnn) hae

/-- Monotonicity of the slice integral in the left endpoint (nonnegative integrand). -/
lemma setIntegral_mono_Ioo_left {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hint : IntegrableOn f (Set.Ioo a c)) (hnn : ∀ x ∈ Set.Ioo a c, 0 ≤ f x) :
    ∫ x in Set.Ioo b c, f x ≤ ∫ x in Set.Ioo a c, f x := by
  have hsub : Set.Ioo b c ⊆ Set.Ioo a c := fun x hx => ⟨lt_of_le_of_lt hab hx.1, hx.2⟩
  have hae : (Set.Ioo b c : Set ℝ) ≤ᵐ[volume] (Set.Ioo a c : Set ℝ) := by
    rw [MeasureTheory.ae_le_set, Set.sdiff_eq_empty.mpr hsub, measure_empty]
  exact MeasureTheory.setIntegral_mono_set hint
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hnn) hae

end Work.FTS.EllipticEst.Cores
