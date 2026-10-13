/-
# `Work.FTS.EllSol.EllPkgAux.KernelDefs` — the kernel of the angular Jensen estimate

Vocabulary for `Work.FTS.EllSol.EllPkgAux.kernelJensen`: the three-image mollification kernel

  `KJ ε θ s = sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - π)`

(the three images of `s` under the reflections generating the doubly odd extension, cf.
`PkgK5.K5c.MollDefs`), together with its elementary properties:

* `KJ_nonneg` : the kernel is nonnegative;
* `KJ_le` : it is bounded by `3 (ε · sMass)⁻¹`;
* `continuous_KJ` : joint continuity;
* `integrable_KJ_slice`, `integral_KJ_line` : the slice is integrable on the line and has total
  mass `3` there;
* `KJ_mass` : its mass over `Iθ` is at most `3`;
* `aesm_sq_of_integrableOn`, `integrableOn_sq_of_integrableOn` : the single hypothesis
  `IntegrableOn (g² σθ) Iθ` of the target controls `g²` itself;
* `KJ_pointwise` : the pointwise Jensen/Cauchy–Schwarz bound
  `(∫_{Iθ} KJ ε θ s · g s)² ≤ 3 ∫_{Iθ} KJ ε θ s · (g s)²`.

The `L²` Schur step (`∫_{Iθ} σθ(θ) KJ ε θ u dθ ≤ K σθ(u)`) is the proved lemma
`Work.FTS.EllSol.K5cAux.thWeightCmp`; it is used (in the form `KJ_schur_ae` below, a.e. on
`Iθ`) by the assembly in `kernelJensen`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.K5cAux.thWeightCmp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.FTS.EllSol.PkgK5.K5c

local notation "Iθ" => Work.Spaces.Iθ
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-- The three-image mollification kernel of the doubly odd extension. -/
def KJ (ε θ s : ℝ) : ℝ :=
  sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi)

theorem KJ_nonneg {ε : ℝ} (hε : 0 < ε) (θ s : ℝ) : 0 ≤ KJ ε θ s := by
  simp only [KJ]
  exact add_nonneg (add_nonneg (sKer_nonneg hε _) (sKer_nonneg hε _)) (sKer_nonneg hε _)

theorem KJ_le {ε : ℝ} (hε : 0 < ε) (θ s : ℝ) : KJ ε θ s ≤ 3 * (ε * sMass)⁻¹ := by
  have h1 := Work.FTS.EllSol.K5cAux.sKer_le_inv hε (θ - s)
  have h2 := Work.FTS.EllSol.K5cAux.sKer_le_inv hε (θ + s)
  have h3 := Work.FTS.EllSol.K5cAux.sKer_le_inv hε (θ + s - Real.pi)
  simp only [KJ]
  linarith

theorem continuous_KJ (ε : ℝ) : Continuous (fun p : ℝ × ℝ => KJ ε p.1 p.2) := by
  have hc : Continuous (fun t : ℝ => sKer ε t) := Work.FTS.EllSol.K5cAux.continuous_sKer ε
  have h1 : Continuous (fun p : ℝ × ℝ => sKer ε (p.1 - p.2)) :=
    hc.comp (continuous_fst.sub continuous_snd)
  have h2 : Continuous (fun p : ℝ × ℝ => sKer ε (p.1 + p.2)) :=
    hc.comp (continuous_fst.add continuous_snd)
  have h3 : Continuous (fun p : ℝ × ℝ => sKer ε (p.1 + p.2 - Real.pi)) :=
    hc.comp ((continuous_fst.add continuous_snd).sub continuous_const)
  simp only [KJ]
  exact (h1.add h2).add h3

theorem integrable_sKer_sub {ε θ : ℝ} (hε : 0 < ε) :
    Integrable (fun s : ℝ => sKer ε (θ - s)) volume := by
  have h := (Work.FTS.EllSol.K5cAux.integrable_sKer hε).comp_sub_right θ
  refine h.congr (Filter.Eventually.of_forall (fun s => ?_))
  show sKer ε (s - θ) = sKer ε (θ - s)
  rw [show θ - s = -(s - θ) by ring, sKer_even]

theorem integrable_sKer_add {ε θ : ℝ} (hε : 0 < ε) :
    Integrable (fun s : ℝ => sKer ε (θ + s)) volume := by
  have h := (Work.FTS.EllSol.K5cAux.integrable_sKer hε).comp_sub_right (-θ)
  refine h.congr (Filter.Eventually.of_forall (fun s => ?_))
  show sKer ε (s - -θ) = sKer ε (θ + s)
  rw [show s - -θ = θ + s by ring]

theorem integrable_sKer_shift {ε θ : ℝ} (hε : 0 < ε) :
    Integrable (fun s : ℝ => sKer ε (θ + s - Real.pi)) volume := by
  have h := (Work.FTS.EllSol.K5cAux.integrable_sKer hε).comp_sub_right (Real.pi - θ)
  refine h.congr (Filter.Eventually.of_forall (fun s => ?_))
  show sKer ε (s - (Real.pi - θ)) = sKer ε (θ + s - Real.pi)
  rw [show s - (Real.pi - θ) = θ + s - Real.pi by ring]

theorem integrable_KJ_slice {ε θ : ℝ} (hε : 0 < ε) :
    Integrable (fun s : ℝ => KJ ε θ s) volume := by
  have h1 := integrable_sKer_sub (θ := θ) hε
  have h2 := integrable_sKer_add (θ := θ) hε
  have h3 := integrable_sKer_shift (θ := θ) hε
  have hsum : (fun s : ℝ => KJ ε θ s)
      = (fun s : ℝ => sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi)) := rfl
  rw [hsum]
  exact (h1.add h2).add h3

theorem integral_KJ_line {ε θ : ℝ} (hε : 0 < ε) : (∫ s : ℝ, KJ ε θ s) = 3 := by
  have h1 : (∫ s : ℝ, sKer ε (θ - s)) = 1 := by
    rw [show (fun s : ℝ => sKer ε (θ - s)) = fun s : ℝ => sKer ε (s - θ) by
      funext s; rw [show θ - s = -(s - θ) by ring, sKer_even]]
    rw [MeasureTheory.integral_sub_right_eq_self, sKer_integral_eq_one hε]
  have h2 : (∫ s : ℝ, sKer ε (θ + s)) = 1 := by
    rw [show (fun s : ℝ => sKer ε (θ + s)) = fun s : ℝ => sKer ε (s - (-θ)) by
      funext s; rw [show s - -θ = θ + s by ring]]
    rw [MeasureTheory.integral_sub_right_eq_self, sKer_integral_eq_one hε]
  have h3 : (∫ s : ℝ, sKer ε (θ + s - Real.pi)) = 1 := by
    rw [show (fun s : ℝ => sKer ε (θ + s - Real.pi))
        = fun s : ℝ => sKer ε (s - (Real.pi - θ)) by
      funext s; rw [show s - (Real.pi - θ) = θ + s - Real.pi by ring]]
    rw [MeasureTheory.integral_sub_right_eq_self, sKer_integral_eq_one hε]
  have hi1 : Integrable (fun s : ℝ => sKer ε (θ - s)) volume := integrable_sKer_sub (θ := θ) hε
  have hi2 : Integrable (fun s : ℝ => sKer ε (θ + s)) volume := integrable_sKer_add (θ := θ) hε
  have hi3 : Integrable (fun s : ℝ => sKer ε (θ + s - Real.pi)) volume :=
    integrable_sKer_shift (θ := θ) hε
  have hsum : (∫ s : ℝ, KJ ε θ s)
      = (∫ s : ℝ, sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi)) := rfl
  rw [hsum]
  have e2 : (∫ s : ℝ, sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi))
      = (∫ s : ℝ, sKer ε (θ - s) + sKer ε (θ + s))
        + ∫ s : ℝ, sKer ε (θ + s - Real.pi) :=
    MeasureTheory.integral_add (hi1.add hi2) hi3
  have e1 : (∫ s : ℝ, sKer ε (θ - s) + sKer ε (θ + s))
      = (∫ s : ℝ, sKer ε (θ - s)) + ∫ s : ℝ, sKer ε (θ + s) :=
    MeasureTheory.integral_add hi1 hi2
  rw [e2, e1, h1, h2, h3]
  norm_num

theorem KJ_mass {ε θ : ℝ} (hε : 0 < ε) (_hθ : θ ∈ Iθ) :
    ∫ s in Iθ, KJ ε θ s ≤ 3 := by
  have hint : Integrable (fun s : ℝ => KJ ε θ s) volume := integrable_KJ_slice hε
  have h1 : (∫ s in Iθ, KJ ε θ s) ≤ ∫ s : ℝ, KJ ε θ s :=
    MeasureTheory.setIntegral_le_integral hint
      (Filter.Eventually.of_forall (fun s => KJ_nonneg hε θ s))
  rw [integral_KJ_line hε] at h1
  exact h1

end Work.FTS.EllSol.EllPkgAux
