import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.EllipticEst.TanTheta.Basic
import Submission.Work.FTS.EllipticEst.TanTheta.psi_contdiff
import Submission.Work.FTS.EllipticEst.TanTheta.psi_deriv_formula
import Submission.Work.FTS.EllipticEst.TanTheta.psi_second_deriv
import Submission.Work.FTS.EllipticEst.TanTheta.psi_bounds_sc
import Submission.Work.FTS.EllipticEst.TanTheta.integrable_deriv_psi_sq
import Submission.Work.FTS.EllipticEst.TanTheta.integrable_wrho_products
import Submission.Work.FTS.EllipticEst.TanTheta.wrho_mul_sq_tendsto
import Submission.Work.FTS.EllipticEst.TanTheta.wrho_deriv
import Submission.Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TanTheta

set_option autoImplicit false

/-! ## General helpers: the fundamental theorem of calculus on an open interval,
and integration by parts against a weight vanishing at both endpoints. -/

/-- **FTC-2 on an open interval.**  If `G` is differentiable on `(a,b)` with derivative `G'`,
`G'` is integrable there, and `G` has limits `m` at `a⁺` and `l` at `b⁻`, then
`∫_{a}^{b} G' = l - m`. -/
theorem integral_Ioo_eq_sub_of_tendsto {a b m l : ℝ} (hab : a < b) {G G' : ℝ → ℝ}
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt G (G' x) x)
    (hint : IntegrableOn G' (Set.Ioo a b))
    (hbot : Tendsto G (𝓝[>] a) (𝓝 m)) (htop : Tendsto G (𝓝[<] b) (𝓝 l)) :
    ∫ x in Set.Ioo a b, G' x = l - m := by
  have hle : a ≤ b := le_of_lt hab
  have hI : IntervalIntegrable G' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mpr hint
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab hderiv hI hbot htop
  rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  exact h

/-- **Integration by parts against a weight vanishing at both endpoints.**  If
`(ρ f²) → 0` at `a⁺` and at `b⁻`, then `∫ ρ f f' = -(1/2) ∫ ρ' f²` on `(a,b)`. -/
theorem integral_Ioo_mul_deriv_eq_neg_half {a b : ℝ} (hab : a < b) {ρ ρ' f f' : ℝ → ℝ}
    (hρ : ∀ x ∈ Set.Ioo a b, HasDerivAt ρ (ρ' x) x)
    (hf : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint1 : IntegrableOn (fun x => ρ' x * f x ^ 2) (Set.Ioo a b))
    (hint2 : IntegrableOn (fun x => ρ x * f x * f' x) (Set.Ioo a b))
    (hbot : Tendsto (fun x => ρ x * f x ^ 2) (𝓝[>] a) (𝓝 0))
    (htop : Tendsto (fun x => ρ x * f x ^ 2) (𝓝[<] b) (𝓝 0)) :
    ∫ x in Set.Ioo a b, ρ x * f x * f' x = -(1 / 2) * ∫ x in Set.Ioo a b, ρ' x * f x ^ 2 := by
  have hderivG : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun y => (1 / 2) * (ρ y * f y ^ 2))
        (ρ x * f x * f' x + (1 / 2) * (ρ' x * f x ^ 2)) x := by
    intro x hx
    have h := ((hρ x hx).mul ((hf x hx).pow 2)).const_mul (1 / 2)
    have h2 : (2 : ℕ) - 1 = 1 := rfl
    rw [h2, pow_one] at h
    convert h using 1
    simp only [Pi.pow_apply]
    ring
  have hInt : IntegrableOn
      (fun x => ρ x * f x * f' x + (1 / 2) * (ρ' x * f x ^ 2)) (Set.Ioo a b) :=
    hint2.add (hint1.const_mul (1 / 2))
  have hlim1 : Tendsto (fun y => (1 / 2) * (ρ y * f y ^ 2)) (𝓝[>] a) (𝓝 0) := by
    simpa using hbot.const_mul (1 / 2 : ℝ)
  have hlim2 : Tendsto (fun y => (1 / 2) * (ρ y * f y ^ 2)) (𝓝[<] b) (𝓝 0) := by
    simpa using htop.const_mul (1 / 2 : ℝ)
  have hFTC := integral_Ioo_eq_sub_of_tendsto hab hderivG hInt hlim1 hlim2
  simp only [sub_zero] at hFTC
  have hsplit : ∫ x in Set.Ioo a b, (ρ x * f x * f' x + (1 / 2) * (ρ' x * f x ^ 2))
      = (∫ x in Set.Ioo a b, ρ x * f x * f' x)
        + (1 / 2) * ∫ x in Set.Ioo a b, ρ' x * f x ^ 2 := by
    rw [integral_add hint2 (hint1.const_mul (1 / 2)), integral_const_mul]
  rw [hsplit] at hFTC
  linarith [hFTC]

/-- An integrable function on `(0, π/2)` times a bounded measurable function is integrable. -/
theorem integrableOn_mul_of_bound {f g : ℝ → ℝ} {c : ℝ}
    (hf : IntegrableOn f (Set.Ioo 0 (Real.pi / 2)))
    (hg : AEStronglyMeasurable g (volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖g θ‖ ≤ c) :
    IntegrableOn (fun θ => f θ * g θ) (Set.Ioo 0 (Real.pi / 2)) :=
  hf.mul_bdd hg (ae_restrict_of_forall_mem measurableSet_Ioo hb)

/-- **The slice identity behind the paper's `I₄`.**

Let `η ∈ [0,1)`, let `u : ℝ → ℝ` be `C²` on a neighbourhood of `[0, π/2]` with `u (π/2) = 0`,
and write `ψ θ = u θ / Real.cos θ` on `(0, π/2)`.  If the three weighted integrals
`∫ (u')² sin(2θ)^{-η}`, `∫ (u'')² sin(2θ)^{-η}` and `∫ ψ² sin(2θ)^{-η}` over `(0, π/2)` are
honest (integrable), then

  `∫_0^{π/2} [((1-η)/2)·cos(2θ) + 2·sin²θ]·(ψ')²·sin(2θ)^{-η}`
     `= -∫_0^{π/2} (sin θ · ψ')·(u'')·sin(2θ)^{-η}`
       `+ ((1-η)/2)·∫_0^{π/2} cos(2θ)·ψ²·sin(2θ)^{-η}`.

This is the exact rearrangement of the two integrations by parts in `θ` used in
Elgindi, Annals 194 (3) 2021, Step 2 of the proof of Proposition `prop:H2` (`I₄`): writing
`u = cos θ · ψ` (so `u'' = -cosθ·ψ - 2 sinθ·ψ' + cosθ·ψ''`) and putting it into
`I₄ = -∫ (∂_θ(tan θ · u))·u''·s^{-η}` gives, after the two integrations by parts with the weight
`ρ = sin(2θ)^{1-η}/2 = sin θ cos θ · sin(2θ)^{-η}` (whose boundary values vanish at `θ = 0, π/2`),
the identity above; equivalently it is the pair of identities
`∫ sinθ cosθ · ψ ψ' s^{-η} = -((1-η)/2)∫ cos 2θ ψ² s^{-η}` and
`∫ sinθ cosθ · ψ' ψ'' s^{-η} = -((1-η)/2)∫ cos 2θ (ψ')² s^{-η}`.
(The absolute integrability of `sinθ cosθ ψ' ψ'' s^{-η}`, needed for the second integration by
parts, follows from the three hypotheses: near the endpoints `u = cos θ · ψ` gives
`ψ'' = (u'' + cos θ ψ + 2 sin θ ψ')/cos θ` and `sin(2θ)^{1-η}/(2 cos θ) ≤ sin(2θ)^{-η}`, while
away from them `sin θ cos θ ≤ sin(2θ)^{-η}` up to a constant; the boundary terms of the two
integrations by parts vanish because `ρ → 0` at `θ = 0, π/2` and `ψ`, `ψ'` are bounded near the
endpoints — `|ψ| ≤ C` and `|ψ'| ≤ C` follow from `u ∈ C²`, `u(π/2) = 0`.)
The right-hand side is what Cauchy–Schwarz bounds by `‖sin θ ψ' s^{-η/2}‖·‖u'' s^{-η/2}‖`, and the
coefficient on the left satisfies `((1-η)/2)cos2θ + 2 sin²θ ≥ (1-η)/2 > 0`. -/
theorem slice_ident (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hu0 : u 0 = 0) (hu1 : u (Real.pi / 2) = 0)
    (hi1 : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)))
    (hi2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)))
    (hi3 : MeasureTheory.IntegrableOn
      (fun θ => (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (((1 - η) / 2) * Real.cos (2 * θ) + 2 * (Real.sin θ) ^ 2)
          * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      = - (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ) * (deriv (deriv u) θ)
              * (Real.sin (2 * θ)) ^ (-η))
        + ((1 - η) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
  have hmain : (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (((1 - η) / 2) * Real.cos (2 * θ) + 2 * (Real.sin θ) ^ 2)
          * (deriv (psi u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      = - (∫ θ in Set.Ioo 0 (Real.pi / 2),
            (Real.sin θ * deriv (psi u) θ) * (deriv (deriv u) θ)
              * (Real.sin (2 * θ)) ^ (-η))
        + ((1 - η) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Real.cos (2 * θ) * (psi u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
    -- ## 0.  elementary facts
    have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
    have hs_int : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) := by
      have h : IntervalIntegrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-η)) volume 0
          (Real.pi / 2) := Work.FTS.H2.intervalIntegrable_sin_rpow (-η) (by linarith)
      rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le hpi2.le] at h
    -- ## 1.  `ψ` is `C²` on the interval and its derivatives exist there
    have hψcd : ContDiffOn ℝ 2 (psi u) (Set.Ioo 0 (Real.pi / 2)) := psi_contdiff u hu
    have hψdiff : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (psi u) (deriv (psi u) θ) θ := by
      intro θ hθ
      have hcd : ContDiffAt ℝ 2 (psi u) θ := hψcd.contDiffAt (isOpen_Ioo.mem_nhds hθ)
      exact (hcd.differentiableAt (by norm_num)).hasDerivAt
    have hψ'diff : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (deriv (psi u)) (deriv (deriv (psi u)) θ) θ := by
      intro θ hθ
      have hcd : ContDiffAt ℝ 2 (psi u) θ := hψcd.contDiffAt (isOpen_Ioo.mem_nhds hθ)
      have hd1 : ContDiffAt ℝ 1 (deriv (psi u)) θ := hcd.derivWithin (by norm_num)
      exact (hd1.differentiableAt (by norm_num)).hasDerivAt
    -- ## 2.  the bounds on `ψ` and `ψ'`
    obtain ⟨C, hC0, hCb⟩ := psi_bounds_sc u hu hu1
    have hCψ : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ‖psi u θ‖ ≤ C :=
      fun θ hθ => (hCb θ hθ).1
    have hCψ' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ‖deriv (psi u) θ‖ ≤ C :=
      fun θ hθ => (hCb θ hθ).2
    -- ## 3.  the integrability inputs
    have hψ'sq : IntegrableOn
        (fun θ => (deriv (psi u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) := integrable_deriv_psi_sq η hη1 u C hCψ'
    have hi3' : IntegrableOn (fun θ => (psi u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) := by simpa only [psi] using hi3
    have halg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Real.cos θ * deriv (deriv (psi u)) θ
          = deriv (deriv u) θ + Real.cos θ * psi u θ
            + 2 * Real.sin θ * deriv (psi u) θ :=
      fun θ hθ => psi_second_deriv u hu hθ
    -- ## 4.  the products and the vanishing of the boundary terms
    obtain ⟨hρψψ', hρψ'ψ''⟩ :=
      integrable_wrho_products η hη0 hη1 u C C hCψ hCψ' halg hi2 hi3'
    obtain ⟨hbd1, hbd2, hbd3, hbd4⟩ := wrho_mul_sq_tendsto η hη0 hη1 u C C hCψ hCψ'
    -- ## 5.  bounded multipliers
    have hcos2_meas : AEStronglyMeasurable (fun θ : ℝ => Real.cos (2 * θ))
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      ((Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).measurable).aestronglyMeasurable
    have hcos2_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ‖Real.cos (2 * θ)‖ ≤ 1 := by
      intro θ hθ
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hsin2_meas : AEStronglyMeasurable (fun θ : ℝ => (Real.sin θ) ^ 2)
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      ((Real.continuous_sin.pow 2).measurable).aestronglyMeasurable
    have hsin2_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ‖(Real.sin θ) ^ 2‖ ≤ 1 := by
      intro θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
    have hfac_meas : AEStronglyMeasurable (fun θ : ℝ => (1 - η) * Real.cos (2 * θ))
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      ((continuous_const.mul (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))).measurable).aestronglyMeasurable
    have hfac_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        ‖(1 - η) * Real.cos (2 * θ)‖ ≤ |1 - η| := by
      intro θ hθ
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
    -- ## 6.  integrability of the four derived integrands
    have hintJ1 : IntegrableOn
        (fun θ => Real.cos (2 * θ) * (deriv (psi u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) :=
      (integrableOn_mul_of_bound hψ'sq hcos2_meas hcos2_le).congr_fun
        (fun θ _ => by ring) measurableSet_Ioo
    have hintJ2 : IntegrableOn
        (fun θ => (Real.sin θ) ^ 2 * (deriv (psi u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) :=
      (integrableOn_mul_of_bound hψ'sq hsin2_meas hsin2_le).congr_fun
        (fun θ _ => by ring) measurableSet_Ioo
    have hintw1 : IntegrableOn (fun θ => wrhoD η θ * (psi u θ) ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (integrableOn_mul_of_bound hi3' hfac_meas hfac_le).congr_fun
        (fun θ _ => by simp only [wrhoD]; ring) measurableSet_Ioo
    have hintw2 : IntegrableOn (fun θ => wrhoD η θ * (deriv (psi u) θ) ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (integrableOn_mul_of_bound hψ'sq hfac_meas hfac_le).congr_fun
        (fun θ _ => by simp only [wrhoD]; ring) measurableSet_Ioo
    -- ## 7.  the two integrations by parts
    have hP1 := integral_Ioo_mul_deriv_eq_neg_half hpi2 (fun θ hθ => wrho_deriv η hθ)
      hψdiff hintw1 hρψψ' hbd1 hbd2
    have hP2 := integral_Ioo_mul_deriv_eq_neg_half hpi2 (fun θ hθ => wrho_deriv η hθ)
      hψ'diff hintw2 hρψ'ψ'' hbd3 hbd4
    -- ## 8.  rewriting the right-hand integrals of the two identities
    have hpt8a : ∀ θ : ℝ, wrhoD η θ * (psi u θ) ^ 2
        = (1 - η) * (Real.cos (2 * θ) * (psi u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
      intro θ
      simp only [wrhoD]
      ring
    have hpt8b : ∀ θ : ℝ, wrhoD η θ * (deriv (psi u) θ) ^ 2
        = (1 - η) * (Real.cos (2 * θ) * (deriv (psi u) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-η)) := by
      intro θ
      simp only [wrhoD]
      ring
    have hP1c : (∫ θ in Set.Ioo 0 (Real.pi / 2), wrhoD η θ * (psi u θ) ^ 2)
        = (1 - η) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Real.cos (2 * θ) * (psi u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
      rw [setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hpt8a θ), integral_const_mul]
    have hP2c : (∫ θ in Set.Ioo 0 (Real.pi / 2), wrhoD η θ * (deriv (psi u) θ) ^ 2)
        = (1 - η) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Real.cos (2 * θ) * (deriv (psi u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
      rw [setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hpt8b θ), integral_const_mul]
    have hK1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), wrho η θ * psi u θ * deriv (psi u) θ)
        = -((1 - η) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Real.cos (2 * θ) * (psi u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
      rw [hP1, hP1c]
      ring
    have hK2 : (∫ θ in Set.Ioo 0 (Real.pi / 2),
          wrho η θ * deriv (psi u) θ * deriv (deriv (psi u)) θ)
        = -((1 - η) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Real.cos (2 * θ) * (deriv (psi u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
      rw [hP2, hP2c]
      ring
    -- ## 9.  the left-hand side, split
    have hptA : ∀ θ : ℝ,
        (((1 - η) / 2) * Real.cos (2 * θ) + 2 * (Real.sin θ) ^ 2)
            * (deriv (psi u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)
        = ((1 - η) / 2) * (Real.cos (2 * θ) * (deriv (psi u) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-η))
          + 2 * ((Real.sin θ) ^ 2 * (deriv (psi u) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-η)) := by
      intro θ
      ring
    have hA : (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (((1 - η) / 2) * Real.cos (2 * θ) + 2 * (Real.sin θ) ^ 2)
            * (deriv (psi u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        = ((1 - η) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              Real.cos (2 * θ) * (deriv (psi u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
          + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin θ) ^ 2 * (deriv (psi u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
      rw [setIntegral_congr_fun measurableSet_Ioo (fun θ _ => hptA θ),
        integral_add (hintJ1.const_mul ((1 - η) / 2)) (hintJ2.const_mul 2),
        integral_const_mul, integral_const_mul]
      try ring
    -- ## 10.  the middle term, split
    have hB : (∫ θ in Set.Ioo 0 (Real.pi / 2),
          (Real.sin θ * deriv (psi u) θ) * (deriv (deriv u) θ) * (Real.sin (2 * θ)) ^ (-η))
        = -(∫ θ in Set.Ioo 0 (Real.pi / 2), wrho η θ * psi u θ * deriv (psi u) θ)
          + (-2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin θ) ^ 2 * (deriv (psi u) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
          + (∫ θ in Set.Ioo 0 (Real.pi / 2),
              wrho η θ * deriv (psi u) θ * deriv (deriv (psi u)) θ) := by
      have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          (Real.sin θ * deriv (psi u) θ) * (deriv (deriv u) θ) * (Real.sin (2 * θ)) ^ (-η)
          = -(wrho η θ * psi u θ * deriv (psi u) θ)
            + (-2) * ((Real.sin θ) ^ 2 * (deriv (psi u) θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-η))
            + wrho η θ * deriv (psi u) θ * deriv (deriv (psi u)) θ := by
        intro θ hθ
        have h := halg θ hθ
        have hsub : deriv (deriv u) θ
            = Real.cos θ * deriv (deriv (psi u)) θ - Real.cos θ * psi u θ
              - 2 * Real.sin θ * deriv (psi u) θ := by linarith
        rw [hsub]
        simp only [wrho]
        ring
      rw [setIntegral_congr_fun measurableSet_Ioo hpt]
      have hm1 : IntegrableOn
          (fun θ => -(wrho η θ * psi u θ * deriv (psi u) θ)) (Set.Ioo 0 (Real.pi / 2)) :=
        hρψψ'.neg
      have hm2 : IntegrableOn
          (fun θ => (-2) * ((Real.sin θ) ^ 2 * (deriv (psi u) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-η))) (Set.Ioo 0 (Real.pi / 2)) :=
        hintJ2.const_mul (-2)
      have hm12 : IntegrableOn
          (fun θ => -(wrho η θ * psi u θ * deriv (psi u) θ)
            + (-2) * ((Real.sin θ) ^ 2 * (deriv (psi u) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-η))) (Set.Ioo 0 (Real.pi / 2)) :=
        hm1.add hm2
      rw [integral_add hm12 hρψ'ψ'', integral_add hm1 hm2, integral_neg,
        integral_const_mul]
      try ring
    -- ## 11.  assemble
    rw [hA, hB, hK1, hK2]
    ring
  exact hmain

end Work.FTS.EllipticEst.TanTheta
