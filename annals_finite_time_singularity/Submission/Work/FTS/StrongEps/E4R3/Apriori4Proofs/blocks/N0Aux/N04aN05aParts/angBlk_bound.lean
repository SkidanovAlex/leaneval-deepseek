/-
Copyright: work module for the Elgindi finite-time singularity project.

# The uniform bound `α² ∫_{Iθ} angBlk(α,a) ≤ Aang·a²`

`Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α a` is the angular integrand

  `θ ↦ (a·Γ(θ)·q(θ))² sin(2θ)^{-η} + ∑_{1 ≤ i ≤ 6} (D_θ^i (a·Γ·q)(θ))² sin(2θ)^{-γ(α)}`

whose integrability on `Iθ = [0,π/2]` is `H6N0Aux.gamQfun_angBlk`.  Here we prove the
*quantitative* statement: there is an `α`-independent constant `Aang` with

  `α² ∫_{Iθ} angBlk α a ≤ Aang · a²`   for `α ∈ (0,1]`, `|a| ≤ 20`.

## Route

* **Exact `a`-scaling.**  `D_θ` is linear over constants (`Spaces.dthU_iter_const_mul`), so
  every summand of `angBlk α a` is `a²` times the corresponding summand with `a` replaced by
  `1`: the `a`-dependence is exactly quadratic.
* **The jet bound `Kf`.**  `H6N0Aux.GQjet_bound` (the constant of `H6N0Aux.Kf`) gives
  `|D_θ^i (Γ·q)| ≤ Kf·Γ` on `Iθ` for `i ≤ 6`; combined with `Γ ≤ 1` this bounds the `η`-slot
  by `Kf² sin(2θ)^{-η}`, and combined with `Γ² ≤ sin(2θ)^{2α/3}`
  (`Coercivity.Gam_sq_le_sin_two`) it bounds each `γ`-slot by
  `Kf² sin(2θ)^{2α/3-γ} = Kf² sin(2θ)^{-q}`, `q = 1 - 17α/30 ∈ (0,1)`.
* **Integrating the majorant.**  `Coercivity.integral_sin_two_neg_rpow_le` gives
  `∫_{Iθ} sin(2θ)^{-q} ≤ 4/(1-q)` for `q ∈ (0,1)`, so the majorant has integral at most
  `Kf²·400 + 7Kf²·(120/(17α))`; the factor `α²` of the statement then kills the `1/α`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.gamQfun_angBlk
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.StrongPersist.H6Rows.FstarI12H6
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux (angBlk Kf GQjet_bound gamQfun_angBlk Kf_pos)

set_option maxHeartbeats 800000

/-! ## The auxiliary exponent `q` and the majorant -/

/-- The exponent `q(α) = 1 - 17α/30` of the angular majorant: `Γ(θ)² sin(2θ)^{-γ(α)}`
is dominated by `sin(2θ)^{-q(α)}` because `2α/3 - γ(α) = -q(α)`. -/
noncomputable def qang (α : ℝ) : ℝ := 1 - 17 * α / 30

lemma qang_pos {α : ℝ} (hα : α ≤ 1) : 0 < qang α := by rw [qang]; linarith

lemma qang_lt_one {α : ℝ} (hα : 0 < α) : qang α < 1 := by rw [qang]; linarith

/-- The angular majorant of `angBlk α a / a²`. -/
noncomputable def majBlk (α : ℝ) : ℝ → ℝ := fun θ =>
  Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + (7 * Kf ^ 2) * (Real.sin (2 * θ)) ^ (-(qang α))

lemma eta_pos : 0 < Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num

lemma eta_lt_one : Work.Spaces.eta < 1 := by rw [Work.Spaces.eta]; norm_num

lemma sin_two_nonneg_of_mem_Iθ (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-! ## Nonnegativity -/

lemma angBlk_nonneg (α a : ℝ) : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ angBlk α a θ := by
  intro θ hθ
  have hs0 := sin_two_nonneg_of_mem_Iθ θ hθ
  simp only [angBlk]
  refine add_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)) ?_
  refine Finset.sum_nonneg (fun i _ => ?_)
  by_cases h1 : 1 ≤ i
  · rw [if_pos h1]; exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  · rw [if_neg h1]

/-! ## The two pointwise block bounds -/

/-- The `η`-slot: `(a·Γ·q)² sin(2θ)^{-η} ≤ a² Kf² sin(2θ)^{-η}`. -/
lemma eta_term_le {α a : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hs0 := sin_two_nonneg_of_mem_Iθ θ hθ
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hjet := GQjet_bound (i := 0) hα hα1 (by norm_num : |(1 : ℝ)| ≤ 20) (Nat.zero_le 6) hθ
  have hjet' : |Work.Spaces.Gam α θ * Work.Spaces.qfun θ| ≤ Kf * Work.Spaces.Gam α θ := by
    simpa using hjet
  have hsq : (Work.Spaces.Gam α θ * Work.Spaces.qfun θ) ^ 2 ≤ Kf ^ 2 := by
    have h1 : (Work.Spaces.Gam α θ * Work.Spaces.qfun θ) ^ 2
        ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := by
      calc (Work.Spaces.Gam α θ * Work.Spaces.qfun θ) ^ 2
          = |Work.Spaces.Gam α θ * Work.Spaces.qfun θ| ^ 2 := by rw [sq_abs]
        _ ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hjet' 2
    calc (Work.Spaces.Gam α θ * Work.Spaces.qfun θ) ^ 2
        ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := h1
      _ = Kf ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := by ring
      _ ≤ Kf ^ 2 * 1 ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith [hG.1, hG.2]) (sq_nonneg Kf)
      _ = Kf ^ 2 := by ring
  have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs0 _
  calc (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = a ^ 2 * ((Work.Spaces.Gam α θ * Work.Spaces.qfun θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
    _ ≤ a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hw) (sq_nonneg a)

/-- The `γ`-slots: for `i ≤ 6`, `(D_θ^i (a·Γ·q))² sin(2θ)^{-γ} ≤ a² Kf² sin(2θ)^{-q(α)}`. -/
lemma jet_term_le {α a : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) {i : ℕ} (hi : i ≤ 6) :
    (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(qang α))) := by
  have hs0 := sin_two_nonneg_of_mem_Iθ θ hθ
  have hexp : 2 * α / 3 + -(Work.Spaces.gam α) = -(qang α) := by
    rw [Work.Spaces.gam, qang]; ring
  have hne : 2 * α / 3 + -(Work.Spaces.gam α) ≠ 0 := by
    rw [hexp]; have := qang_pos hα1; linarith
  have hjet := GQjet_bound (i := i) hα hα1 (by norm_num : |(1 : ℝ)| ≤ 20) hi hθ
  rw [Work.Spaces.dthU_iter_const_mul] at hjet
  have hjet' : |Work.Spaces.dthU^[i]
      (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ| ≤ Kf * Work.Spaces.Gam α θ := by
    simpa using hjet
  have hsq : (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ) ^ 2
      ≤ Kf ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3) := by
    have h1 : (Work.Spaces.dthU^[i]
        (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ) ^ 2
        ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := by
      calc (Work.Spaces.dthU^[i]
            (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ) ^ 2
          = |Work.Spaces.dthU^[i]
              (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ| ^ 2 := by rw [sq_abs]
        _ ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hjet' 2
    calc (Work.Spaces.dthU^[i]
            (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ) ^ 2
        ≤ (Kf * Work.Spaces.Gam α θ) ^ 2 := h1
      _ = Kf ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := by ring
      _ ≤ Kf ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3) :=
          mul_le_mul_of_nonneg_left (Work.Coercivity.Gam_sq_le_sin_two α hα θ hθ) (sq_nonneg _)
  have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs0 _
  have hprod : (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (-(qang α)) := by
    rw [← Real.rpow_add' hs0 hne, hexp]
  calc (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = a ^ 2 * ((Work.Spaces.dthU^[i]
          (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        rw [Work.Spaces.dthU_iter_const_mul]; ring
    _ ≤ a ^ 2 * ((Kf ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3))
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hw) (sq_nonneg a)
    _ = a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(qang α))) := by
        rw [mul_assoc, hprod]

/-- **The pointwise majorant.**  `angBlk α a θ ≤ a² · majBlk α θ` on `Iθ`. -/
lemma angBlk_le_maj {α a : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ θ ∈ Work.Spaces.Iθ, angBlk α a θ ≤ a ^ 2 * majBlk α θ := by
  intro θ hθ
  have hs0 := sin_two_nonneg_of_mem_Iθ θ hθ
  simp only [angBlk, majBlk]
  have hsum : (∑ i ∈ Finset.range 7,
        (if 1 ≤ i then
          (Work.Spaces.dthU^[i] (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
         else 0))
      ≤ ∑ _i ∈ Finset.range 7, a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(qang α))) := by
    refine Finset.sum_le_sum (fun i hi => ?_)
    by_cases h1 : 1 ≤ i
    · rw [if_pos h1]
      exact jet_term_le hα hα1 hθ (by have := Finset.mem_range.mp hi; omega)
    · rw [if_neg h1]
      exact mul_nonneg (sq_nonneg a) (mul_nonneg (sq_nonneg Kf) (Real.rpow_nonneg hs0 _))
  calc (a * (Work.Spaces.Gam α θ * Work.Spaces.qfun θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range 7,
            (if 1 ≤ i then
              (Work.Spaces.dthU^[i]
                (fun t => a * (Work.Spaces.Gam α t * Work.Spaces.qfun t)) θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
             else 0)
      ≤ a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (∑ _i ∈ Finset.range 7, a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(qang α)))) :=
        add_le_add (eta_term_le hα hα1 hθ) hsum
    _ = a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + 7 * (a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(qang α)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = a ^ 2 * (Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          + (7 * Kf ^ 2) * (Real.sin (2 * θ)) ^ (-(qang α))) := by ring

/-! ## Integration of the majorant -/

lemma majBlk_integrable {α a : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ => a ^ 2 * majBlk α θ) Work.Spaces.Iθ := by
  have hEta := Work.Coercivity.integral_sin_two_neg_rpow_le Work.Spaces.eta eta_pos eta_lt_one
  have hQ := Work.Coercivity.integral_sin_two_neg_rpow_le (qang α)
    (qang_pos hα1) (qang_lt_one hα)
  have h1 : IntegrableOn (fun θ => Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := hEta.1.const_mul _
  have h2 : IntegrableOn (fun θ => (7 * Kf ^ 2) * (Real.sin (2 * θ)) ^ (-(qang α)))
      Work.Spaces.Iθ := hQ.1.const_mul _
  have h3 := h1.add h2
  exact h3.const_mul (a ^ 2)

lemma majBlk_integral_le {α a : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ θ in Work.Spaces.Iθ, a ^ 2 * majBlk α θ
      ≤ a ^ 2 * (Kf ^ 2 * (400 : ℝ) + (7 * Kf ^ 2) * (120 / (17 * α))) := by
  have hEta := Work.Coercivity.integral_sin_two_neg_rpow_le Work.Spaces.eta eta_pos eta_lt_one
  have hQ := Work.Coercivity.integral_sin_two_neg_rpow_le (qang α)
    (qang_pos hα1) (qang_lt_one hα)
  have h1 : IntegrableOn (fun θ => Kf ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := hEta.1.const_mul _
  have h2 : IntegrableOn (fun θ => (7 * Kf ^ 2) * (Real.sin (2 * θ)) ^ (-(qang α)))
      Work.Spaces.Iθ := hQ.1.const_mul _
  have hval : ∫ θ in Work.Spaces.Iθ, a ^ 2 * majBlk α θ
      = a ^ 2 * (Kf ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (7 * Kf ^ 2) * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ (-(qang α)))) := by
    simp only [majBlk]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add h1 h2,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have heta : Kf ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ Kf ^ 2 * 400 := by
    have h4 : (4 : ℝ) / (1 - Work.Spaces.eta) = 400 := by
      rw [Work.Spaces.eta]; norm_num
    simpa only [h4] using mul_le_mul_of_nonneg_left hEta.2 (sq_nonneg Kf)
  have hq : (7 * Kf ^ 2) * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(qang α)))
      ≤ (7 * Kf ^ 2) * (120 / (17 * α)) := by
    have h17 : (1 : ℝ) - qang α = 17 * α / 30 := by rw [qang]; ring
    have h4 : (4 : ℝ) / (1 - qang α) = 120 / (17 * α) := by
      rw [h17]
      have hαne : α ≠ 0 := ne_of_gt hα
      field_simp
      ring
    simpa only [h4] using mul_le_mul_of_nonneg_left hQ.2 (by positivity)
  rw [hval]
  exact mul_le_mul_of_nonneg_left (add_le_add heta hq) (sq_nonneg a)

/-! ## The main theorem -/

theorem angBlk_bound : ∃ Aang : ℝ, 0 < Aang ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ a : ℝ, |a| ≤ 20 →
    MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α a)
        Work.Spaces.Iθ ∧
      α ^ 2 * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α a θ) ≤ Aang * a ^ 2 := by
  obtain ⟨_, _, hang⟩ := gamQfun_angBlk
  refine ⟨500 * Kf ^ 2 + 1, by positivity, fun α hαIoc a ha => ?_⟩
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hint : MeasureTheory.IntegrableOn (angBlk α a) Work.Spaces.Iθ :=
    hang α hαIoc a ha
  refine ⟨hint, ?_⟩
  -- the integral is dominated by the integral of the majorant
  have hmono : ∫ θ in Work.Spaces.Iθ, angBlk α a θ
      ≤ ∫ θ in Work.Spaces.Iθ, a ^ 2 * majBlk α θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ (majBlk_integrable hα hα1) ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact angBlk_nonneg α a θ hθ
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact angBlk_le_maj hα hα1 θ hθ
  have hInt : ∫ θ in Work.Spaces.Iθ, angBlk α a θ
      ≤ a ^ 2 * (Kf ^ 2 * (400 : ℝ) + (7 * Kf ^ 2) * (120 / (17 * α))) :=
    le_trans hmono (majBlk_integral_le hα hα1)
  -- arithmetic
  have hαsq1 : α ^ 2 ≤ 1 := by nlinarith [hα, hα1]
  have hkey : α ^ 2 * (120 / (17 * α)) ≤ 120 / 17 := by
    have hαne : α ≠ 0 := ne_of_gt hα
    have he : α ^ 2 * (120 / (17 * α)) = 120 * α / 17 := by
      field_simp
    rw [he, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 17) (by norm_num : (0 : ℝ) < 17)]
    nlinarith [hα1]
  have hnum : Kf ^ 2 * (400 : ℝ) * 1 + (7 * Kf ^ 2) * (120 / 17) ≤ 500 * Kf ^ 2 + 1 := by
    nlinarith [sq_nonneg Kf]
  calc α ^ 2 * (∫ θ in Work.Spaces.Iθ, angBlk α a θ)
      ≤ α ^ 2 * (a ^ 2 * (Kf ^ 2 * (400 : ℝ) + (7 * Kf ^ 2) * (120 / (17 * α)))) :=
        mul_le_mul_of_nonneg_left hInt (sq_nonneg α)
    _ = a ^ 2 * (Kf ^ 2 * (400 : ℝ) * α ^ 2 + (7 * Kf ^ 2) * (α ^ 2 * (120 / (17 * α)))) := by
        ring
    _ ≤ a ^ 2 * (Kf ^ 2 * (400 : ℝ) * 1 + (7 * Kf ^ 2) * (120 / 17)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (sq_nonneg a)
        · exact mul_le_mul_of_nonneg_left hαsq1 (by positivity)
        · exact mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ (500 * Kf ^ 2 + 1) * a ^ 2 := by
        calc a ^ 2 * (Kf ^ 2 * (400 : ℝ) * 1 + (7 * Kf ^ 2) * (120 / 17))
            ≤ a ^ 2 * (500 * Kf ^ 2 + 1) := mul_le_mul_of_nonneg_left hnum (sq_nonneg a)
          _ = (500 * Kf ^ 2 + 1) * a ^ 2 := by ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts
