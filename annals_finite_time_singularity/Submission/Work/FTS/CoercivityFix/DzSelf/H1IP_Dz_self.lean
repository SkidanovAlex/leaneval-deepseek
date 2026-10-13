/-
# `|(D_z f, f)_{ℋ¹}| ≤ 10²² |f|²_{ℋ⁴}` on the coercivity class `CoerAdm`

The frozen vocabulary `Work.FTS.Nonlin.UnifIP` (see `Submission/Work/FTS/Vocab.lean`) asks
for the self-adjointness clause

  `Dz_self : |IP α (D_z f) f| ≤ Ccs · |f|_{ℋ⁴}²`   for `f ∈ CoerAdm α`.

This file proves that clause for the paper's concrete first inner product
`H1IP α = IP₁` (`Work.Coercivity.H1IP`), with the constant `Ccs = 10²²`, i.e.

  `|H1IP α (D_z f) f| ≤ 10²² · HkSq α 4 f`   for every `CoerAdm α f`.

## Why it is true, and why it is *not* a formality

`H1IP α (D_z f) f` is the sum of four weighted `L²`-pairings

* `10 (D_z²f, D_zf)_{w²/sin^η}`,
* `10¹⁰ (D_zf, f)_{w²/sin^η}`,
* `10¹⁷ (D_zf, f)_{w²}`,
* `10²¹ (D_θD_zf, D_θf)_{w²/sin^γ}`,

and each pairing is a *cross* term, so it is genuinely (not vacuously) bounded: the four
quantities `D_z²f`, `D_zf`, `f`, `D_θf` all occur, with the *same* weights, among the
summands of the `ℋ⁴`-integrand `HkIntegrand α 4 f`; the only exception is the fourth
pairing, where `D_θ D_z f` has to be recognised as the mixed derivative `D_z D_θ f`, which
holds almost everywhere (the two operators commute on the open quadrant, and the two
angular endpoints `θ = 0, π/2` form a null set).

The estimates are the weighted AM–GM inequality `2|uv| ρ ≤ u²ρ + v²ρ` integrated against
the quadrant, i.e. the sharp form of Cauchy–Schwarz
`|(u,v)_ρ| ≤ (|u|²_ρ + |v|²_ρ)/2`; the division by `2` costs nothing because the
coefficients `10 + 10¹⁰ + 10¹⁷ + 10²¹ < 10²²` leave a factor-two slack in the constant.
Every pairing is weighted by a weight `ρ` with `0 ≤ ρ ≤ ρ'` (`ρ' = w²sin^{-η}` resp.
the same weight), so the two quadratic forms on the right are `En`-energies, which are
summands of `HkSq α 4 f`.

## The regularity input

`CoerAdm α f` gives `RegQ α 5 f = SmoothQuad f ∧ HkMem α 5 f ∧ BdryTraces α 5 f`
(`Submission/Work/FTS/Vocab.lean`).  `HkMem α 4 f` and `HkMem α 2 f` follow by
monotonicity in the order (`Work.FTS.LocDataExt.HkMem_mono`), and `HkMem α 2 f` is what
supplies the joint integrability of the four weighted squares
(`Work.FTS.CoercivityFix.Coer1.sq_DzEta`, `_sq_MixedGam`, `_sq_DzOne`, which are stated at
order `2` but only ever need the orders `0,1,2` that occur inside the order-`4` bounds here).

## Contents

* `wip_abs_le_half` — the weighted AM–GM/Cauchy–Schwarz bound for `wip`;
* `En_eq_prodIntegral` — `En β u` as a product-measure integral, given the integrability
  of `u²ρ_β`;
* `En_eta_eq_L2Sq`, `En_gam_eq_L2Sq`, `En_eta_DzIter_le_HkSq`, `En_gam_mixed_le_HkSq` —
  the comparison of the `En`-energies with the `ℋ⁴`-norm square;
* `H1IP_Dz_self` — the assembly.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.LocDataExt.Monotone
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Coercivity.wip_eq_integral_prod
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.DzSelf

open Work.FTS.Galerkin (Fn)
open Work.FTS.CoercivityFix.Coer1 (En Rho wip_Rho_self)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The product of the two restricted measures on the quadrant
`[0,∞) × [0,π/2]`, i.e. Lebesgue measure restricted to `Iz ×ˢ Iθ`. -/
abbrev PM : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-! ## Two elementary tools -/

/-- The triangle inequality for four real terms. -/
theorem abs_add_four (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-! ## The weighted AM–GM bound for `wip` -/

/-- **Weighted AM–GM (Cauchy–Schwarz) for `wip`.**  If `0 ≤ ρ ≤ ρ'` almost everywhere on
the quadrant, and the three products `u²ρ'`, `v²ρ'`, `uvρ` are integrable, then

  `|wip ρ u v| ≤ (wip ρ' u u + wip ρ' v v) / 2 = (|u|²_{ρ'} + |v|²_{ρ'}) / 2`.

The proof is the pointwise bound `|uv|ρ ≤ (u² + v²)ρ/2 ≤ (u² + v²)ρ'/2`, integrated with
Fubini (`Work.Coercivity.wip_eq_integral_prod`). -/
theorem wip_abs_le_half {ρ ρ' u v : Fn}
    (hρnn : ∀ᵐ p ∂PM, 0 ≤ ρ p.1 p.2)
    (hle : ∀ᵐ p ∂PM, ρ p.1 p.2 ≤ ρ' p.1 p.2)
    (hu : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * ρ' z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hv : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => v z θ * v z θ * ρ' z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (huv : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * v z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    |Work.Coercivity.wip ρ u v|
      ≤ (Work.Coercivity.wip ρ' u u + Work.Coercivity.wip ρ' v v) / 2 := by
  -- Move the three integrability certificates to the product measure.
  have huP : Integrable (fun p : ℝ × ℝ => u p.1 p.2 * u p.1 p.2 * ρ' p.1 p.2) PM := by
    rw [MeasureTheory.IntegrableOn, ← Coer1.iz_prod_restrict] at hu
    exact hu
  have hvP : Integrable (fun p : ℝ × ℝ => v p.1 p.2 * v p.1 p.2 * ρ' p.1 p.2) PM := by
    rw [MeasureTheory.IntegrableOn, ← Coer1.iz_prod_restrict] at hv
    exact hv
  have huvP : Integrable (fun p : ℝ × ℝ => u p.1 p.2 * v p.1 p.2 * ρ p.1 p.2) PM := by
    rw [MeasureTheory.IntegrableOn, ← Coer1.iz_prod_restrict] at huv
    exact huv
  -- The majorant `(u²ρ' + v²ρ')/2` is integrable.
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      (u p.1 p.2 * u p.1 p.2 * ρ' p.1 p.2 + v p.1 p.2 * v p.1 p.2 * ρ' p.1 p.2) / 2) PM :=
    (huP.add hvP).div_const 2
  -- The pointwise bound (a.e.).
  have hbound : ∀ᵐ p ∂PM, |u p.1 p.2 * v p.1 p.2 * ρ p.1 p.2|
      ≤ (u p.1 p.2 * u p.1 p.2 * ρ' p.1 p.2 + v p.1 p.2 * v p.1 p.2 * ρ' p.1 p.2) / 2 := by
    filter_upwards [hρnn, hle] with p hρ hρle
    have hρ' : 0 ≤ ρ' p.1 p.2 := le_trans hρ hρle
    calc |u p.1 p.2 * v p.1 p.2 * ρ p.1 p.2|
        = |u p.1 p.2 * v p.1 p.2| * ρ p.1 p.2 := by
          rw [abs_mul, abs_of_nonneg hρ]
      _ ≤ |u p.1 p.2 * v p.1 p.2| * ρ' p.1 p.2 :=
          mul_le_mul_of_nonneg_left hρle (abs_nonneg _)
      _ ≤ (u p.1 p.2 ^ 2 * ρ' p.1 p.2 + v p.1 p.2 ^ 2 * ρ' p.1 p.2) / 2 := by
          have h := Coer1.two_abs_mul_le (u p.1 p.2) (v p.1 p.2) (ρ' p.1 p.2) hρ'
          linarith
      _ = (u p.1 p.2 * u p.1 p.2 * ρ' p.1 p.2 + v p.1 p.2 * v p.1 p.2 * ρ' p.1 p.2) / 2 := by
          ring
  rw [Work.Coercivity.wip_eq_integral_prod ρ u v huv,
    Work.Coercivity.wip_eq_integral_prod ρ' u u hu,
    Work.Coercivity.wip_eq_integral_prod ρ' v v hv]
  calc |∫ p, u p.1 p.2 * v p.1 p.2 * ρ p.1 p.2 ∂PM|
      ≤ ∫ p, |u p.1 p.2 * v p.1 p.2 * ρ p.1 p.2| ∂PM :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ p, (u p.1 p.2 * u p.1 p.2 * ρ' p.1 p.2
          + v p.1 p.2 * v p.1 p.2 * ρ' p.1 p.2) / 2 ∂PM :=
        MeasureTheory.integral_mono_ae huvP.abs hmaj hbound
    _ = (∫ p, u p.1 p.2 * u p.1 p.2 * ρ' p.1 p.2 ∂PM
          + ∫ p, v p.1 p.2 * v p.1 p.2 * ρ' p.1 p.2 ∂PM) / 2 := by
        rw [MeasureTheory.integral_div, MeasureTheory.integral_add huP hvP]

/-! ## The `En`-energies as product-measure integrals -/

/-- `En β u` is the product-measure integral of `u²ρ_β`, as soon as the latter is
integrable. -/
theorem En_eq_prodIntegral {β : ℝ} {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * Rho β z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    En β u = ∫ p : ℝ × ℝ, u p.1 p.2 * u p.1 p.2 * Rho β p.1 p.2 ∂PM := by
  rw [← wip_Rho_self β u]
  exact Work.Coercivity.wip_eq_integral_prod (Rho β) u u h

/-! ## The `En`-energies against the `ℋ⁴`-norm square -/

/-- The `η`-weighted energy of the pure `D_z`-blocks is the corresponding summand of
`L2Sq`, written with the half-weight `w/sin(2θ)^{η/2}`. -/
theorem En_eta_eq_L2Sq (u : Fn) :
    En Work.Spaces.eta u
      = Work.Spaces.L2Sq (fun z θ =>
          u z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) := by
  rw [Coer1.En, Work.Spaces.L2Sq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rw [mul_pow, Coer1.sig_div_sq_Iθ Work.Spaces.eta (by rw [Work.Spaces.eta]; norm_num) z θ hθ]
  ring

/-- The `γ`-weighted energy of the mixed blocks is the corresponding summand of `L2Sq`,
written with the full weight `Wt α = w·sin(2θ)^{-γ/2}`. -/
theorem En_gam_eq_L2Sq (α : ℝ) (hα : 0 < α) (u : Fn) :
    En (Work.Spaces.gam α) u = Work.Spaces.L2Sq (fun z θ => u z θ * Work.Spaces.Wt α z θ) := by
  rw [Coer1.En, Work.Spaces.L2Sq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
  rw [mul_pow, Coer1.Wt_sq_self_Iθ α z θ hα hθ]
  ring

/-- Every pure `D_z`-block energy of order `≤ 4` is dominated by `HkSq α 4 f`. -/
theorem En_eta_DzIter_le_HkSq (α : ℝ) {f : Fn} (hm : Work.Spaces.HkMem α 4 f)
    (i : ℕ) (hi : i ≤ 4) :
    En Work.Spaces.eta (Work.Spaces.DzIter i f) ≤ Work.Spaces.HkSq α 4 f := by
  rw [En_eta_eq_L2Sq]
  exact Work.Spaces.L2Sq_DzIter_le_HkSq α 4 f hm i hi

/-- Every mixed-block energy `En (gam α) (D_z^j D_θ^i f)`, `i ≥ 1`, `i + j ≤ 4`, is
dominated by `HkSq α 4 f`. -/
theorem En_gam_mixed_le_HkSq (α : ℝ) (hα : 0 < α) {f : Fn} (hm : Work.Spaces.HkMem α 4 f)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    En (Work.Spaces.gam α) (Work.Spaces.mixed j i f) ≤ Work.Spaces.HkSq α 4 f := by
  rw [En_gam_eq_L2Sq α hα]
  exact Work.Spaces.L2Sq_mixed_le_HkSq α 4 f hm i j hi hij

/-! ## The main estimate -/

theorem H1IP_Dz_self (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) :
    |Work.Coercivity.H1IP α (Work.Spaces.Dz f) f| ≤ (10:ℝ) ^ 22 * Work.Spaces.HkSq α 4 f := by
  obtain ⟨hreg, _hvanish, _haxis, _hl12⟩ := hf
  obtain ⟨hsq, hm5, _hb⟩ := hreg
  have hm4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.LocDataExt.HkMem_mono (by norm_num) hsq hm5
  have hm2 : Work.Spaces.HkMem α 2 f :=
    Work.FTS.LocDataExt.HkMem_mono (by norm_num) hsq hm5
  have hHnn : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  -- a.e. nonnegativity of the weights `Rho β`
  have hRhoNN : ∀ β : ℝ, ∀ᵐ p ∂PM, 0 ≤ Rho β p.1 p.2 := fun β =>
    (Coer1.ae_prod_snd_mem measurableSet_Icc
      (MeasureTheory.ae_restrict_mem measurableSet_Icc)).mono
      (fun p hp => Coer1.Rho_nonneg β p.1 p.2 hp)
  -- the `η`-weighted squares of the pure `D_z`-blocks
  have hsqE : ∀ i, i ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.DzIter i f z θ ^ 2 * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    fun i hi => Coer1.sq_DzEta α hsq hm2 i hi
  have hsqEmul : ∀ i, i ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        Work.Spaces.DzIter i f z θ * Work.Spaces.DzIter i f z θ * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    fun i hi => (hsqE i hi).congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => by
        rcases p with ⟨z, θ⟩
        simp only [Function.uncurry_apply_pair]
        ring))
  -- the `γ`-weighted squares of the mixed blocks
  have hsqMG : ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        Work.Spaces.mixed j i f z θ ^ 2 * Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    fun i j hi hij => Coer1.sq_MixedGam α hα hsq hm2 i j hi hij
  have hsqMGmul : ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        Work.Spaces.mixed j i f z θ * Work.Spaces.mixed j i f z θ
          * Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    fun i j hi hij => (hsqMG i j hi hij).congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => by
        rcases p with ⟨z, θ⟩
        simp only [Function.uncurry_apply_pair]
        ring))
  -- the plain radial weight
  have hsqO : ∀ i, i ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.DzIter i f z θ ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    fun i hi => Coer1.sq_DzOne α hsq hm2 i hi
  -- ## The four cross terms
  have hT1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.DzIter 2 f z θ * Work.Spaces.DzIter 1 f z θ * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Coer1.integrableOn_mul_of_sq_Q
      (((Coer1.continuousOn_DzIter_Q hsq 2).mul (Coer1.continuousOn_DzIter_Q hsq 1)).mul
        (Coer1.continuousOn_Rho Work.Spaces.eta))
      (Coer1.Rho_nonneg Work.Spaces.eta) (hsqE 2 (by norm_num)) (hsqE 1 (by norm_num))
  have hT2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.DzIter 1 f z θ * f z θ * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Coer1.integrableOn_mul_of_sq_Q
      (((Coer1.continuousOn_DzIter_Q hsq 1).mul (Coer1.continuousOn_f_Q hsq)).mul
        (Coer1.continuousOn_Rho Work.Spaces.eta))
      (Coer1.Rho_nonneg Work.Spaces.eta) (hsqE 1 (by norm_num)) (hsqE 0 (by norm_num))
  have hT3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.DzIter 1 f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Coer1.integrableOn_mul_of_sq_Q
      (((Coer1.continuousOn_DzIter_Q hsq 1).mul (Coer1.continuousOn_f_Q hsq)).mul
        Coer1.continuousOn_w2)
      Coer1.w2_nonneg (hsqO 1 (by norm_num)) (hsqO 0 (by norm_num))
  have hM11 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.mixed 1 1 f z θ * Work.Spaces.mixed 1 1 f z θ
        * Rho (Work.Spaces.gam α) z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    hsqMGmul 1 1 (by norm_num) (by norm_num)
  have hM01 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.mixed 0 1 f z θ * Work.Spaces.mixed 0 1 f z θ
        * Rho (Work.Spaces.gam α) z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    hsqMGmul 1 0 (by norm_num) (by norm_num)
  have hM11x : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.mixed 1 1 f z θ * Work.Spaces.Dth f z θ
        * Rho (Work.Spaces.gam α) z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Coer1.integrableOn_mul_of_sq_Q
      (((Coer1.continuousOn_mixed_Q hsq 1 1).mul (Coer1.continuousOn_mixed_Q hsq 0 1)).mul
        (Coer1.continuousOn_Rho (Work.Spaces.gam α)))
      (Coer1.Rho_nonneg _) (hsqMG 1 1 (by norm_num) (by norm_num))
      (hsqMG 1 0 (by norm_num) (by norm_num))
  -- ## `D_θ D_z f = D_z D_θ f` almost everywhere
  have hae4 : ∀ᵐ p ∂PM,
      Work.Spaces.Dth (Work.Spaces.Dz f) p.1 p.2 = Work.Spaces.mixed 1 1 f p.1 p.2 :=
    (Coer1.ae_Dz_Dth_comm hsq).mono (fun p hp => by
      rw [← hp]
      simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
        Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero])
  have haeEqPM : (Function.uncurry (fun z θ =>
        Work.Spaces.mixed 1 1 f z θ * Work.Spaces.mixed 1 1 f z θ
          * Rho (Work.Spaces.gam α) z θ))
      =ᵐ[PM] (Function.uncurry (fun z θ =>
        Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dth (Work.Spaces.Dz f) z θ
          * Rho (Work.Spaces.gam α) z θ)) := by
    filter_upwards [hae4] with p hp
    simp only [Function.uncurry]
    rw [← hp]
  have haeEq : (Function.uncurry (fun z θ =>
        Work.Spaces.mixed 1 1 f z θ * Work.Spaces.mixed 1 1 f z θ
          * Rho (Work.Spaces.gam α) z θ))
      =ᵐ[MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)]
      (Function.uncurry (fun z θ =>
        Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dth (Work.Spaces.Dz f) z θ
          * Rho (Work.Spaces.gam α) z θ)) := by
    rw [← Coer1.iz_prod_restrict]
    exact haeEqPM
  have hae4' : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
      Work.Spaces.Dth (Work.Spaces.Dz f) p.1 p.2 = Work.Spaces.mixed 1 1 f p.1 p.2 := by
    rw [← Coer1.iz_prod_restrict]
    exact hae4
  have haeEq2 : (Function.uncurry (fun z θ =>
        Work.Spaces.mixed 1 1 f z θ * Work.Spaces.Dth f z θ
          * Rho (Work.Spaces.gam α) z θ))
      =ᵐ[MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)]
      (Function.uncurry (fun z θ =>
        Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dth f z θ
          * Rho (Work.Spaces.gam α) z θ)) := by
    filter_upwards [hae4'] with p hp
    simp only [Function.uncurry]
    rw [← hp]
  -- the integrability certificates for the fourth pairing
  have hu4 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dth (Work.Spaces.Dz f) z θ
        * Rho (Work.Spaces.gam α) z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    hM11.congr haeEq
  have hv4 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Rho (Work.Spaces.gam α) z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    hM01
  have huv4 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dth f z θ
        * Rho (Work.Spaces.gam α) z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    hM11x.congr haeEq2
  -- ## The four pairings are bounded by `HkSq α 4 f`
  have hs1 : |Work.Coercivity.wip (Rho Work.Spaces.eta)
      (Work.Spaces.DzIter 2 f) (Work.Spaces.DzIter 1 f)| ≤ Work.Spaces.HkSq α 4 f := by
    have h := wip_abs_le_half (ρ := Rho Work.Spaces.eta) (ρ' := Rho Work.Spaces.eta)
      (u := Work.Spaces.DzIter 2 f) (v := Work.Spaces.DzIter 1 f)
      (hRhoNN Work.Spaces.eta) (Filter.Eventually.of_forall (fun _ => le_refl _))
      (hsqEmul 2 (by norm_num)) (hsqEmul 1 (by norm_num)) hT1
    rw [wip_Rho_self Work.Spaces.eta (Work.Spaces.DzIter 2 f),
      wip_Rho_self Work.Spaces.eta (Work.Spaces.DzIter 1 f)] at h
    have h1 := En_eta_DzIter_le_HkSq α hm4 2 (by norm_num)
    have h2 := En_eta_DzIter_le_HkSq α hm4 1 (by norm_num)
    linarith
  have hs2 : |Work.Coercivity.wip (Rho Work.Spaces.eta)
      (Work.Spaces.DzIter 1 f) f| ≤ Work.Spaces.HkSq α 4 f := by
    have h := wip_abs_le_half (ρ := Rho Work.Spaces.eta) (ρ' := Rho Work.Spaces.eta)
      (u := Work.Spaces.DzIter 1 f) (v := f)
      (hRhoNN Work.Spaces.eta) (Filter.Eventually.of_forall (fun _ => le_refl _))
      (hsqEmul 1 (by norm_num))
      (by simpa only [Work.Spaces.DzIter_zero] using hsqEmul 0 (by norm_num)) hT2
    rw [wip_Rho_self Work.Spaces.eta (Work.Spaces.DzIter 1 f),
      wip_Rho_self Work.Spaces.eta f] at h
    have h1 := En_eta_DzIter_le_HkSq α hm4 1 (by norm_num)
    have h2 : En Work.Spaces.eta f ≤ Work.Spaces.HkSq α 4 f := by
      simpa only [Work.Spaces.DzIter_zero] using En_eta_DzIter_le_HkSq α hm4 0 (by norm_num)
    linarith
  have hs3 : |Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Spaces.DzIter 1 f) f| ≤ Work.Spaces.HkSq α 4 f := by
    have hle3 : ∀ᵐ p ∂PM, (fun z _ => Work.Spaces.w z ^ 2) p.1 p.2 ≤ Rho Work.Spaces.eta p.1 p.2 :=
      (Coer1.ae_prod_snd_mem measurableSet_Ioo Coer1.ae_restrict_Iθ_mem_Ioo).mono
        (fun p hp => Coer1.w2_le_Rho_eta p.1 p.2 hp)
    have h := wip_abs_le_half (ρ := fun z _ => Work.Spaces.w z ^ 2) (ρ' := Rho Work.Spaces.eta)
      (u := Work.Spaces.DzIter 1 f) (v := f)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hle3
      (hsqEmul 1 (by norm_num))
      (by simpa only [Work.Spaces.DzIter_zero] using hsqEmul 0 (by norm_num)) hT3
    rw [wip_Rho_self Work.Spaces.eta (Work.Spaces.DzIter 1 f),
      wip_Rho_self Work.Spaces.eta f] at h
    have h1 := En_eta_DzIter_le_HkSq α hm4 1 (by norm_num)
    have h2 : En Work.Spaces.eta f ≤ Work.Spaces.HkSq α 4 f := by
      simpa only [Work.Spaces.DzIter_zero] using En_eta_DzIter_le_HkSq α hm4 0 (by norm_num)
    linarith
  have hs4 : |Work.Coercivity.wip (Rho (Work.Spaces.gam α))
      (Work.Spaces.Dth (Work.Spaces.Dz f)) (Work.Spaces.Dth f)| ≤ Work.Spaces.HkSq α 4 f := by
    have h := wip_abs_le_half (ρ := Rho (Work.Spaces.gam α)) (ρ' := Rho (Work.Spaces.gam α))
      (u := Work.Spaces.Dth (Work.Spaces.Dz f)) (v := Work.Spaces.Dth f)
      (hRhoNN (Work.Spaces.gam α)) (Filter.Eventually.of_forall (fun _ => le_refl _))
      hu4 hv4 huv4
    rw [wip_Rho_self (Work.Spaces.gam α) (Work.Spaces.Dth (Work.Spaces.Dz f)),
      wip_Rho_self (Work.Spaces.gam α) (Work.Spaces.Dth f)] at h
    have h1 : En (Work.Spaces.gam α) (Work.Spaces.Dth (Work.Spaces.Dz f))
        ≤ Work.Spaces.HkSq α 4 f := by
      have hEn : En (Work.Spaces.gam α) (Work.Spaces.Dth (Work.Spaces.Dz f))
          = En (Work.Spaces.gam α) (Work.Spaces.mixed 1 1 f) := by
        rw [En_eq_prodIntegral hu4, En_eq_prodIntegral hM11]
        exact MeasureTheory.integral_congr_ae haeEqPM.symm
      rw [hEn]
      exact En_gam_mixed_le_HkSq α hα hm4 1 1 (by norm_num) (by norm_num)
    have h2 : En (Work.Spaces.gam α) (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α 4 f := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero,
        Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using
        En_gam_mixed_le_HkSq α hα hm4 1 0 (by norm_num) (by norm_num)
    linarith
  -- ## Assembly
  have hIP : Work.Coercivity.H1IP α (Work.Spaces.Dz f) f
      = 10 * Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz (Work.Spaces.Dz f))
          (Work.Spaces.Dz f)
        + 10 ^ 10 * Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz f) f
        + 10 ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
            (Work.Spaces.Dz f) f
        + 10 ^ 21 * Work.Coercivity.wip (Rho (Work.Spaces.gam α))
            (Work.Spaces.Dth (Work.Spaces.Dz f)) (Work.Spaces.Dth f) := rfl
  have hdz2 : Work.Spaces.DzIter 2 f = Work.Spaces.Dz (Work.Spaces.Dz f) := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  have hdz1 : Work.Spaces.DzIter 1 f = Work.Spaces.Dz f := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  have hA : |Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz (Work.Spaces.Dz f))
      (Work.Spaces.Dz f)| ≤ Work.Spaces.HkSq α 4 f := by
    simpa only [hdz2, hdz1] using hs1
  have hB : |Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz f) f|
      ≤ Work.Spaces.HkSq α 4 f := by
    simpa only [hdz1] using hs2
  have hC : |Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Spaces.Dz f) f|
      ≤ Work.Spaces.HkSq α 4 f := by
    simpa only [hdz1] using hs3
  have htri : |10 * Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz (Work.Spaces.Dz f))
          (Work.Spaces.Dz f)
        + 10 ^ 10 * Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz f) f
        + 10 ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Spaces.Dz f) f
        + 10 ^ 21 * Work.Coercivity.wip (Rho (Work.Spaces.gam α))
            (Work.Spaces.Dth (Work.Spaces.Dz f)) (Work.Spaces.Dth f)|
      ≤ 10 * Work.Spaces.HkSq α 4 f + 10 ^ 10 * Work.Spaces.HkSq α 4 f
        + 10 ^ 17 * Work.Spaces.HkSq α 4 f + 10 ^ 21 * Work.Spaces.HkSq α 4 f := by
    have h1 : |10 * Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz (Work.Spaces.Dz f))
        (Work.Spaces.Dz f)| ≤ 10 * Work.Spaces.HkSq α 4 f := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 10)]
      exact mul_le_mul_of_nonneg_left hA (by norm_num)
    have h2 : |10 ^ 10 * Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz f) f|
        ≤ 10 ^ 10 * Work.Spaces.HkSq α 4 f := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 10 ^ 10)]
      exact mul_le_mul_of_nonneg_left hB (by positivity)
    have h3 : |10 ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
        (Work.Spaces.Dz f) f| ≤ 10 ^ 17 * Work.Spaces.HkSq α 4 f := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 10 ^ 17)]
      exact mul_le_mul_of_nonneg_left hC (by positivity)
    have h4 : |10 ^ 21 * Work.Coercivity.wip (Rho (Work.Spaces.gam α))
        (Work.Spaces.Dth (Work.Spaces.Dz f)) (Work.Spaces.Dth f)|
        ≤ 10 ^ 21 * Work.Spaces.HkSq α 4 f := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 10 ^ 21)]
      exact mul_le_mul_of_nonneg_left hs4 (by positivity)
    have h5 := abs_add_four
      (10 * Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz (Work.Spaces.Dz f))
        (Work.Spaces.Dz f))
      (10 ^ 10 * Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz f) f)
      (10 ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Spaces.Dz f) f)
      (10 ^ 21 * Work.Coercivity.wip (Rho (Work.Spaces.gam α))
        (Work.Spaces.Dth (Work.Spaces.Dz f)) (Work.Spaces.Dth f))
    linarith [h1, h2, h3, h4, h5]
  calc |Work.Coercivity.H1IP α (Work.Spaces.Dz f) f|
      = |10 * Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz (Work.Spaces.Dz f))
            (Work.Spaces.Dz f)
          + 10 ^ 10 * Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz f) f
          + 10 ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Spaces.Dz f) f
          + 10 ^ 21 * Work.Coercivity.wip (Rho (Work.Spaces.gam α))
              (Work.Spaces.Dth (Work.Spaces.Dz f)) (Work.Spaces.Dth f)| := by rw [hIP]
    _ ≤ 10 * Work.Spaces.HkSq α 4 f + 10 ^ 10 * Work.Spaces.HkSq α 4 f
          + 10 ^ 17 * Work.Spaces.HkSq α 4 f + 10 ^ 21 * Work.Spaces.HkSq α 4 f := htri
    _ = ((10 : ℝ) + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * Work.Spaces.HkSq α 4 f := by ring
    _ ≤ (10 : ℝ) ^ 22 * Work.Spaces.HkSq α 4 f :=
        mul_le_mul_of_nonneg_right (by norm_num) hHnn

end Work.FTS.CoercivityFix.DzSelf
