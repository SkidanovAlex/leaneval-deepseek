import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.dict13Aux3
import Submission.Work.BoseFixB1S.integrableOn_cont_mul_pairComp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13Aux4` — support facts and the right-hand-side functionals

Two groups of elementary facts used by the `L¹` dictionary:

* the `rowProd` integrand vanishes off `abox n ℓ × acube ℓ × acube ℓ` (pointwise, no measurability),
  because the state factors force the configuration into the box; together with the a.e. linearity
  of `qmqKernelR` (delegated) this turns the box identity into an ambient a.e. identity;
* the right-hand side `rhsFun` of the dictionary: a.e. invariance in the pair kernel, integrability
  of its integrand, and its `L¹(Λ×Λ)` bound (`lintegral_pair_abox`).

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "abx" => Submission.BoseGases.abox
local notation "acb" => Submission.BoseGases.acube

set_option autoImplicit false

/-- The box `L¹`-norm of a pair kernel: the iterated `∫⁻` of `‖e‖` over `acube ℓ × acube ℓ`. -/
noncomputable def boxL1 (ℓ : ℝ) (e : E3 → E3 → ℝ) : ENNReal :=
  ∫⁻ a, ∫⁻ b, ‖e a b‖ₑ
    ∂((volume : Measure E3).restrict (acb ℓ)) ∂((volume : Measure E3).restrict (acb ℓ))

/-! ## 1. The support of the `rowProd` integrand -/

/-- `rowProd` vanishes when the configuration lies outside the box. -/
theorem rowProd_eq_zero_of_notMem_abox {n : ℕ} {ℓ : ℝ} {Θ : Xn n → ℂ} {A B : E3 → ℂ}
    {K : E3 → E3 → ℂ} {p : Fin n × Fin n}
    (hΘs : Function.support Θ ⊆ abx n ℓ) {z : Xn n × (E3 × E3)} (hz : z.1 ∉ abx n ℓ) :
    rowProd Θ A B K p z = 0 := by
  have h0 : Θ z.1 = 0 := by
    by_contra h
    exact hz (hΘs (Function.mem_support.mpr h))
  simp only [rowProd, rowInt, h0, star_zero, zero_mul, mul_zero]

/-- `rowProd` vanishes when the `u`-variable (the second updated slot) lies outside the cube. -/
theorem rowProd_eq_zero_of_notMem_acube_snd {n : ℕ} {ℓ : ℝ} {Θ : Xn n → ℂ} {A B : E3 → ℂ}
    {K : E3 → E3 → ℂ} {p : Fin n × Fin n}
    (hΘs : Function.support Θ ⊆ abx n ℓ) {z : Xn n × (E3 × E3)} (hz : z.2.2 ∉ acb ℓ) :
    rowProd Θ A B K p z = 0 := by
  have hmem : Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2 ∉ abx n ℓ := by
    intro h
    have h2 := (Submission.BoseGases.mem_abox_iff n ℓ _).mp h p.2
    rw [Function.update_self] at h2
    exact hz h2
  have h0 : Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2) = 0 := by
    by_contra h
    exact hmem (hΘs (Function.mem_support.mpr h))
  simp only [rowProd, rowInt, h0, mul_zero]

/-- `rowProd` vanishes when the `y`-variable (the first updated slot) lies outside the cube. -/
theorem rowProd_eq_zero_of_notMem_acube_fst {n : ℕ} {ℓ : ℝ} {Θ : Xn n → ℂ} {A B : E3 → ℂ}
    {K : E3 → E3 → ℂ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    (hΘs : Function.support Θ ⊆ abx n ℓ) {z : Xn n × (E3 × E3)} (hz : z.2.1 ∉ acb ℓ) :
    rowProd Θ A B K p z = 0 := by
  have hmem : Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2 ∉ abx n ℓ := by
    intro h
    have h2 := (Submission.BoseGases.mem_abox_iff n ℓ _).mp h p.1
    rw [show (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2) p.1 = z.2.1 by
      simp [hp]] at h2
    exact hz h2
  have h0 : Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2) = 0 := by
    by_contra h
    exact hmem (hΘs (Function.mem_support.mpr h))
  simp only [rowProd, rowInt, h0, mul_zero]

/-- The `(p.1, p.2)`-pullback of a pair kernel is a.e.-strongly-measurable on the box. -/
theorem aestronglyMeasurable_pairEval {n : ℕ} {ℓ : ℝ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {e : E3 → E3 → ℝ}
    (he : AEStronglyMeasurable (Function.uncurry e)
      ((volume : Measure E3).prod (volume : Measure E3))) :
    AEStronglyMeasurable (fun x : Xn n => e (x p.1) (x p.2))
      ((volume : Measure (Xn n)).restrict (abx n ℓ)) := by
  have : SigmaFinite ((volume : Measure E3).restrict (acb ℓ)) := inferInstance
  have hq : Measure.QuasiMeasurePreserving (fun x : Xn n => (x p.1, x p.2))
      ((volume : Measure (Xn n)).restrict (abx n ℓ))
      ((volume : Measure E3).prod (volume : Measure E3)) := by
    have h0 := Work.BoseFixB2.Pot.quasiMeasurePreserving_pair_eval_aux
      ((volume : Measure E3).restrict (acb ℓ)) hp
    rw [show (volume : Measure (Xn n)).restrict (abx n ℓ)
      = Measure.pi (fun _ : Fin n => (volume : Measure E3).restrict (acb ℓ)) from
        Submission.BoseGases.restrict_abox_eq_pi n ℓ]
    refine h0.mono_right ?_
    have ha : ((volume : Measure E3).restrict (acb ℓ)) ≪ (volume : Measure E3) :=
      Measure.absolutelyContinuous_of_le Measure.restrict_le_self
    simpa using Measure.AbsolutelyContinuous.prod ha ha
  rw [show (fun x : Xn n => e (x p.1) (x p.2))
      = Function.uncurry e ∘ fun x : Xn n => (x p.1, x p.2) from rfl]
  exact he.comp_quasiMeasurePreserving hq

/-! ## 2. The right-hand side: a.e. invariance -/

/-- `rhsFun` depends only on the a.e. class of the pair kernel. -/
theorem rhsFun_congr_ae {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℝ} {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) {e₁ e₂ : E3 → E3 → ℝ}
    (h : Function.uncurry e₁ =ᵐ[(volume : Measure E3).prod (volume : Measure E3)]
      Function.uncurry e₂) :
    rhsFun ℓ Ψ p e₁ = rhsFun ℓ Ψ p e₂ := by
  have hqmp : Measure.QuasiMeasurePreserving (fun x : Xn n => (x p.1, x p.2))
      ((volume : Measure (Xn n)).restrict (abx n ℓ))
      ((volume : Measure E3).prod (volume : Measure E3)) := by
    have : SigmaFinite ((volume : Measure E3).restrict (acb ℓ)) := inferInstance
    have h1 := Work.BoseFixB2.Pot.quasiMeasurePreserving_pair_eval_aux
      ((volume : Measure E3).restrict (acb ℓ)) hp
    rw [show (volume : Measure (Xn n)).restrict (abx n ℓ)
      = Measure.pi (fun _ : Fin n => (volume : Measure E3).restrict (acb ℓ)) from
        Submission.BoseGases.restrict_abox_eq_pi n ℓ]
    refine h1.mono_right ?_
    have ha : ((volume : Measure E3).restrict (acb ℓ)) ≪ (volume : Measure E3) :=
      Measure.absolutelyContinuous_of_le Measure.restrict_le_self
    simpa using Measure.AbsolutelyContinuous.prod ha ha
  have hae : (fun x : Xn n => Function.uncurry e₁ (x p.1, x p.2))
      =ᵐ[(volume : Measure (Xn n)).restrict (abx n ℓ)]
      (fun x : Xn n => Function.uncurry e₂ (x p.1, x p.2)) := hqmp.ae_eq h
  rw [rhsFun, rhsFun]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  simp only [Function.uncurry] at hx ⊢
  rw [hx]

/-! ## 3. The right-hand side: integrability and `L¹` bound -/

/-- The `abox`-integrand of the right-hand side is integrable for a merely integrable pair kernel
(a continuous weight times the `(p.1, p.2)`-pullback of the kernel). -/
theorem rhs_integrableOn {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {G : Xn n → ℝ} (hG : Continuous G)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) {e : E3 → E3 → ℝ}
    (he : AEStronglyMeasurable (Function.uncurry e)
      ((volume : Measure E3).prod (volume : Measure E3)))
    (hfin : boxL1 ℓ e < ⊤) :
    IntegrableOn (fun x : Xn n => G x * e (x p.1) (x p.2)) (abx n ℓ) volume := by
  have : SigmaFinite ((volume : Measure E3).restrict (acb ℓ)) := inferInstance
  have ha : ((volume : Measure E3).restrict (acb ℓ)) ≪ (volume : Measure E3) :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hm : AEMeasurable (Function.uncurry e)
      (((volume : Measure E3).restrict (acb ℓ)).prod ((volume : Measure E3).restrict (acb ℓ))) :=
    he.aemeasurable.mono' (by simpa using Measure.AbsolutelyContinuous.prod ha ha)
  have hI : Integrable (Function.uncurry e) (volume.restrict (acb ℓ ×ˢ acb ℓ)) := by
    refine ⟨he.restrict, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm,
      show volume.restrict (acb ℓ ×ˢ acb ℓ)
        = ((volume : Measure E3).restrict (acb ℓ)).prod
            ((volume : Measure E3).restrict (acb ℓ)) from
        (Measure.prod_restrict (acb ℓ) (acb ℓ)).symm,
      lintegral_prod _ (by simpa only [Function.uncurry] using hm.enorm)]
    exact hfin
  exact Work.BoseFixB1S.integrableOn_cont_mul_pairComp hℓ hp hG hI

/-- **The `L¹` bound of the right-hand side** (`ℝ≥0∞` form).  On the box `|G| ≤ B`, the
`(p.1, p.2)`-pullback integral factors through the box `L¹` norm of the kernel
(`lintegral_pair_abox`). -/
theorem rhs_enorm_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {G : Xn n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hGb : ∀ x ∈ abx n ℓ, ‖G x‖ ≤ B) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {e : E3 → E3 → ℝ}
    (he : AEStronglyMeasurable (Function.uncurry e)
      ((volume : Measure E3).prod (volume : Measure E3))) :
    ‖∫ x in abx n ℓ, G x * e (x p.1) (x p.2)‖ₑ
      ≤ ENNReal.ofReal B * (volume : Measure E3) (acb ℓ) ^ (n - 2) * boxL1 ℓ e := by
  have hm : AEStronglyMeasurable (fun x : Xn n => e (x p.1) (x p.2))
      ((volume : Measure (Xn n)).restrict (abx n ℓ)) := aestronglyMeasurable_pairEval hp he
  have hpeel : (∫⁻ x, ‖e (x p.1) (x p.2)‖ₑ ∂((volume : Measure (Xn n)).restrict (abx n ℓ)))
      = (volume : Measure E3) (acb ℓ) ^ (n - 2) * boxL1 ℓ e := by
    have h := Work.BoseFixB2.Pot.lintegral_pair_abox (n := n) (ℓ := ℓ) hℓ hp
      (φ := fun a b => ‖e a b‖ₑ) (by
        rw [show Function.uncurry (fun a b => ‖e a b‖ₑ)
            = fun p : E3 × E3 => ‖Function.uncurry e p‖ₑ from rfl]
        exact (he.enorm).aestronglyMeasurable)
    simpa only [boxL1] using h
  have hpt : ∀ᵐ x ∂((volume : Measure (Xn n)).restrict (abx n ℓ)),
      ‖G x * e (x p.1) (x p.2)‖ₑ ≤ ENNReal.ofReal B * ‖e (x p.1) (x p.2)‖ₑ := by
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
    refine ae_of_all _ (fun x hx => ?_)
    rw [enorm_mul]
    refine mul_le_mul' ?_ le_rfl
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hGb x hx)
  calc ‖∫ x in abx n ℓ, G x * e (x p.1) (x p.2)‖ₑ
      ≤ ∫⁻ x, ‖G x * e (x p.1) (x p.2)‖ₑ
          ∂((volume : Measure (Xn n)).restrict (abx n ℓ)) :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, ENNReal.ofReal B * ‖e (x p.1) (x p.2)‖ₑ
          ∂((volume : Measure (Xn n)).restrict (abx n ℓ)) := lintegral_mono_ae hpt
    _ = ENNReal.ofReal B
          * ∫⁻ x, ‖e (x p.1) (x p.2)‖ₑ ∂((volume : Measure (Xn n)).restrict (abx n ℓ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal B * ((volume : Measure E3) (acb ℓ) ^ (n - 2) * boxL1 ℓ e) := by
        rw [hpeel]
    _ = ENNReal.ofReal B * (volume : Measure E3) (acb ℓ) ^ (n - 2) * boxL1 ℓ e := by
        rw [mul_assoc]

end Work.BoseBoxFock
