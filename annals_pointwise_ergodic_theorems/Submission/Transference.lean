import ChallengeDeps
import Mathlib.Tactic
import Submission.Reduction
import Submission.VarClamp
import Submission.PolyGrowth

/-!
# Calderón transference (Krause--Mirek--Tao, Proposition 3.1 (ii))

The Calderón transference principle allows one to deduce the variational estimate for an
arbitrary measure-preserving system `(X, μ, T)` from the corresponding estimate for the integer
shift model `(ℤ, μ_ℤ, T_ℤ)`, `T_ℤ(n) = n - 1`.

This file develops that reduction for the bilinear polynomial averages
`A T N X P f g x`.  The situation is analysed in two steps.

* *Product systems.*  For a measure space `(X, μ)`, the product system
  `(X × ℤ, μ × μ_ℤ, id × T_ℤ)` has no interaction between its fibres `{x} × ℤ`.  Writing
  `F_x := fun n => F (x,n)`, the averages on the product system are the averages on `ℤ` of the
  slices, `A_{X×ℤ,N}(F,G)(x,n) = A_{ℤ,N}(F_x,G_x)(n)`, so the `ℤ`-shift estimate may be applied
  fibre by fibre, and the resulting estimate for the product system follows from Tonelli's
  theorem and Hölder's inequality.

* *Testing functions on the product system.*  Given the estimate for every product system, one
  takes the test functions `f_{i,M}(x,n) = 1_{[1,3CM^D]}(n) f_i(T^{-n}x)`; the fibre identity
  `A_{X×ℤ,N}(f_{1,M},f_{2,M})(x,n) = A_{X,N}(f_1,f_2)(T^{-n}x)` holds for `CM^D ≤ n ≤ 2CM^D`
  and `N ≤ M`, and the normalisations `(3CM^D)^{1/p_i}` of the test functions cancel against the
  factor `(CM^D)^{1/p}` obtained by integrating over the fibre, thanks to the Hölder exponent
  relation `1/p = 1/p₁ + 1/p₂`.
-/

set_option maxHeartbeats 4000000

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

/-! ## The integer shift -/

/-- The integer shift `T_ℤ(n) = n - 1`, as a measurable equivalence of `ℤ`. -/
noncomputable def TZ : ℤ ≃ᵐ ℤ where
  toEquiv := { toFun := fun n => n - 1, invFun := fun n => n + 1,
               left_inv := fun n => by simp, right_inv := fun n => by simp }
  measurable_toFun := measurable_id.sub measurable_const
  measurable_invFun := measurable_id.add measurable_const

lemma TZ_apply (n : ℤ) : TZ n = n - 1 := rfl

lemma TZ_symm_apply (n : ℤ) : (TZ.symm : ℤ ≃ᵐ ℤ) n = n + 1 := rfl

lemma TZ_nat (m : ℕ) : ∀ n : ℤ, (((TZ : ℤ ≃ ℤ) ^ m) n) = n - m := by
  induction m with
  | zero => intro n; simp
  | succ m ih =>
      intro n
      rw [pow_succ, Equiv.Perm.coe_mul]
      show (((TZ : ℤ ≃ ℤ) ^ m) (TZ n)) = n - (m + 1)
      rw [ih, TZ_apply]
      ring

lemma TZ_nat_zpow (m : ℕ) (n : ℤ) : (((TZ : ℤ ≃ ℤ) ^ (m : ℤ)) n) = n - m := by
  rw [zpow_natCast]
  exact TZ_nat m n

lemma TZ_neg_zpow (m : ℕ) (n : ℤ) : (((TZ : ℤ ≃ ℤ) ^ (-(m : ℤ))) n) = n + m := by
  rw [zpow_neg, zpow_natCast]
  have hnm : (((TZ : ℤ ≃ ℤ) ^ m)) (n + m) = n := by rw [TZ_nat m]; ring
  have h2 : ((((TZ : ℤ ≃ ℤ) ^ m)⁻¹) n) = ((((TZ : ℤ ≃ ℤ) ^ m)⁻¹)) ((((TZ : ℤ ≃ ℤ) ^ m)) (n + m)) := by
    rw [hnm]
  rw [h2]
  simpa using Equiv.left_inv (((TZ : ℤ ≃ ℤ) ^ m)) (n + m)

lemma TZ_zpow (k : ℤ) (n : ℤ) : (((TZ : ℤ ≃ ℤ) ^ k) n) = n - k := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm, TZ_nat_zpow]
  · rw [hm, TZ_neg_zpow]
    ring

/-- The shift `T_ℤ` preserves counting measure. -/
lemma measurePreserving_TZ :
    MeasurePreserving (TZ : ℤ ≃ᵐ ℤ) (Measure.count : Measure ℤ) Measure.count := by
  refine ⟨TZ.measurable, le_antisymm ?_ ?_⟩
  · exact Function.Injective.map_count_le TZ.injective TZ.measurable
  · have h : (Measure.count : Measure ℤ).map (TZ.symm : ℤ ≃ᵐ ℤ) ≤ Measure.count :=
      Function.Injective.map_count_le TZ.symm.injective TZ.symm.measurable
    have h2 := Measure.map_mono (f := (TZ : ℤ ≃ᵐ ℤ)) h TZ.measurable
    simpa using h2

/-! ## The product system -/

/-- The product system `id × T_ℤ` on `𝓧 × ℤ`, where `𝓧` is the phase space of the original
system.  It acts by `(x,n) ↦ (x, n-1)` and preserves the product measure `μ × μ_ℤ`. -/
noncomputable def prodSys (𝓧 : Type*) [MeasurableSpace 𝓧] : 𝓧 × ℤ ≃ᵐ 𝓧 × ℤ :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl 𝓧) TZ

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

@[simp] lemma prodSys_apply (x : 𝓧) (j : ℤ) : prodSys 𝓧 (x, j) = (x, j - 1) := rfl

lemma prodSys_measurePreserving (μ : Measure 𝓧) [SFinite μ] :
    MeasurePreserving (prodSys 𝓧) (μ.prod (Measure.count : Measure ℤ))
      (μ.prod (Measure.count : Measure ℤ)) :=
  MeasurePreserving.prod (MeasurePreserving.id μ) measurePreserving_TZ

lemma prodSys_pow_apply (m : ℕ) : ∀ (x : 𝓧) (j : ℤ),
    (((prodSys 𝓧 : (𝓧 × ℤ) ≃ (𝓧 × ℤ)) ^ m) (x, j)) = (x, j - m) := by
  induction m with
  | zero => intro x j; simp
  | succ m ih =>
      intro x j
      rw [pow_succ, Equiv.Perm.coe_mul]
      show (((prodSys 𝓧 : (𝓧 × ℤ) ≃ (𝓧 × ℤ)) ^ m) (prodSys 𝓧 (x, j))) = (x, j - (m + 1))
      rw [show prodSys 𝓧 (x, j) = (x, j - 1) from rfl, ih]
      simp only [Prod.mk.injEq, true_and]
      ring

lemma prodSys_neg_zpow (m : ℕ) (x : 𝓧) (j : ℤ) :
    (((prodSys 𝓧 : (𝓧 × ℤ) ≃ (𝓧 × ℤ)) ^ (-(m : ℤ))) (x, j)) = (x, j + m) := by
  rw [zpow_neg, zpow_natCast]
  have hnm : (((prodSys 𝓧 : (𝓧 × ℤ) ≃ (𝓧 × ℤ)) ^ m) (x, j + m)) = (x, j) := by
    rw [prodSys_pow_apply]
    simp only [Prod.mk.injEq, true_and]
    ring
  have h2 : ((((prodSys 𝓧 : (𝓧 × ℤ) ≃ (𝓧 × ℤ)) ^ m)⁻¹) (x, j))
      = ((((prodSys 𝓧 : (𝓧 × ℤ) ≃ (𝓧 × ℤ)) ^ m)⁻¹))
          ((((prodSys 𝓧 : (𝓧 × ℤ) ≃ (𝓧 × ℤ)) ^ m)) (x, j + m)) := by
    rw [hnm]
  rw [h2]
  simpa using Equiv.left_inv (((prodSys 𝓧 : (𝓧 × ℤ) ≃ (𝓧 × ℤ)) ^ m)) (x, j + m)

lemma prodSys_zpow (k : ℤ) (x : 𝓧) (j : ℤ) :
    (((prodSys 𝓧 : (𝓧 × ℤ) ≃ (𝓧 × ℤ)) ^ k) (x, j)) = (x, j - k) := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm, zpow_natCast, prodSys_pow_apply]
  · rw [hm, prodSys_neg_zpow]
    simp only [Prod.mk.injEq, true_and]
    ring

/-! ## The fibre identity -/

/-- On the product system, the average of `F, G` at the point `(x,j)` is the average on the
integer shift of the slices `F_x = fun n => F (x,n)`, `G_x`. -/
lemma A_prodSys_eq (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (F G : 𝓧 × ℤ → ℂ) (x : 𝓧) (j : ℤ) :
    A (prodSys 𝓧) N P₁ P₂ F G (x, j)
      = A TZ N P₁ P₂ (fun k => F (x, k)) (fun k => G (x, k)) j := by
  simp only [A]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [prodSys_zpow, TZ_zpow]


/-! ## The variational estimate for the integer shift -/

/-- The variational norm of the averages `A_{a n}(f,g)` on the integer shift, as a function of
the point of `ℤ`.  Bundling it keeps the statements below small. -/
noncomputable def shiftVar (r : ℝ≥0) (P : ℤ[X]) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (j : ℤ) : ℝ≥0∞ :=
  variationalNorm r (fun n => A TZ (a n) X P f g j)

/-- The variational norm of the averages on the product system `𝓧 × ℤ`, bundled. -/
noncomputable def prodVar (r : ℝ≥0) (P : ℤ[X]) (a : ℕ → ℝ≥0) (F G : 𝓧 × ℤ → ℂ)
    (y : 𝓧 × ℤ) : ℝ≥0∞ :=
  variationalNorm r (fun n => A (prodSys 𝓧) (a n) X P F G y)

/-- The variational estimate for the integer shift model `(ℤ, μ_ℤ, T_ℤ)`: for every
`Λ`-lacunary sequence `a` of scales and all `f, g : ℤ → ℂ`,
`‖ (A_{a n}(f,g))_n ‖_{ℓᵖ(ℤ;Vʳ)} ≤ C(Λ) ‖f‖_{ℓᵖ₁} ‖g‖_{ℓᵖ₂}`.

The estimate is stated in terms of `eLpNorm` on both sides (rather than the norms of the `Lᵖ`
elements), which is the form needed for the fibre-by-fibre application in the product system:
the estimate remains meaningful (and true, being `≤ ∞`) when one of the norms on the right is
infinite. -/
def VarEstZ (P : ℤ[X]) (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0) (Cv : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ (Λ : ℝ≥0) (a : ℕ → ℝ≥0), 1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → ∀ f g : ℤ → ℂ,
    eLpNorm (shiftVar r P a f g) p Measure.count
      ≤ (Cv Λ : ℝ≥0∞) * eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count

/-- On the product system, the variational norm of the averages at the point `(x,j)` only sees
the slice `fun k => F (x,k)`, and equals the variational norm of the averages on the integer
shift of that slice. -/
lemma prodVar_fibre (r : ℝ≥0) (P : ℤ[X]) (a : ℕ → ℝ≥0) (F G : 𝓧 × ℤ → ℂ) (x : 𝓧) :
    (fun j => prodVar r P a F G (x, j))
      = shiftVar r P a (fun k => F (x, k)) (fun k => G (x, k)) := by
  funext j
  have hseq : (fun n => A (prodSys 𝓧) (a n) X P F G (x, j))
      = (fun n => A TZ (a n) X P (fun k => F (x, k)) (fun k => G (x, k)) j) := by
    funext n
    exact A_prodSys_eq (a n) X P F G x j
  simp only [prodVar, shiftVar]
  rw [hseq]

/-- The variational norm of the averages on the product system is a.e. measurable. -/
lemma aemeasurable_prodVar {r : ℝ≥0} (hr : 0 < r) {μ : Measure 𝓧} [SigmaFinite μ]
    {P : ℤ[X]} {a : ℕ → ℝ≥0} {F G : 𝓧 × ℤ → ℂ}
    (hF : AEMeasurable F (μ.prod (Measure.count : Measure ℤ)))
    (hG : AEMeasurable G (μ.prod (Measure.count : Measure ℤ))) :
    AEMeasurable (prodVar r P a F G) (μ.prod (Measure.count : Measure ℤ)) :=
  aemeasurable_variationalNorm hr (fun n =>
    aemeasurable_A (prodSys_measurePreserving μ) (a n) X P hF hG)

/-! ## `eLpNorm` of `ℝ≥0∞`-valued functions

The variational norm is `ℝ≥0∞`-valued, so we record the two forms of the `Lᵖ` seminorm that we
need for such functions: the integral formula and the "raise to the `p`-th power" identity. -/

/-! ## `eLpNorm` of `ℝ≥0∞`-valued functions

The variational norm is `ℝ≥0∞`-valued, so we record the form of the `Lᵖ` seminorm that we need
for such functions: raising it to the `p`-th power returns the integral of the `p`-th powers of
the pointwise norms. -/

section EnnrealLp

variable {ε : Type*} [ENorm ε] {μ : Measure 𝓧} {ν : Measure ℤ}

/-- Tonelli's theorem for the `p`-th power of the `Lᵖ` seminorm on a product space. -/
lemma eLpNorm_prod_rpow_toReal [SFinite ν] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    {W : 𝓧 × ℤ → ℝ≥0∞} (hW : AEMeasurable W (μ.prod ν)) :
    (eLpNorm W p (μ.prod ν)) ^ p.toReal
      = ∫⁻ x, (eLpNorm (fun j => W (x, j)) p ν) ^ p.toReal ∂μ := by
  rw [eLpNorm_rpow_toReal hp0 hptop _ hW.aestronglyMeasurable]
  have hid : (∫⁻ z : 𝓧 × ℤ, ‖W z‖ₑ ^ p.toReal ∂(μ.prod ν))
      = ∫⁻ z : 𝓧 × ℤ, W z ^ p.toReal ∂(μ.prod ν) :=
    lintegral_congr fun z => by simp only [enorm_eq_self]
  rw [hid, lintegral_prod (fun z : 𝓧 × ℤ => W z ^ p.toReal) (hW.pow_const _)]
  refine lintegral_congr fun x => ?_
  rw [eLpNorm_rpow_toReal hp0 hptop _ AEStronglyMeasurable.of_discrete]
  simp only [enorm_eq_self]

end EnnrealLp

/-! ## The Hölder/fibre inequality

Applying Tonelli's theorem to the product of the fibre norms and then Hölder's inequality in the
first variable bounds the integral of a product of two fibre norms on the product space by the
product of the global norms, as soon as `1/p = 1/p₁ + 1/p₂`. -/

section FibreHolder

variable {μ : Measure 𝓧}

lemma intCast_toReal_inv_sum {p₁ p₂ p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (h1p₁ : 1 < p₁) (htp₁ : p₁ ≠ ∞) (h1p₂ : 1 < p₂) (htp₂ : p₂ ≠ ∞)
    (hpq : p₁⁻¹ + p₂⁻¹ = p⁻¹) :
    (p₁.toReal)⁻¹ + (p₂.toReal)⁻¹ = (p.toReal)⁻¹ := by
  have h1 : p₁ ≠ 0 := (lt_trans one_pos h1p₁).ne'
  have h2 : p₂ ≠ 0 := (lt_trans one_pos h1p₂).ne'
  have h3 : p ≠ 0 := hp0
  have e1 : (p₁⁻¹ : ℝ≥0∞) ≠ ∞ := ENNReal.inv_ne_top.mpr h1
  have e2 : (p₂⁻¹ : ℝ≥0∞) ≠ ∞ := ENNReal.inv_ne_top.mpr h2
  have h := congrArg ENNReal.toReal hpq
  rw [ENNReal.toReal_add e1 e2, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_inv] at h
  exact h

/-- Fibre Hölder inequality: for the product measure `μ × μ_ℤ`,
`∫_X (‖F_x‖_{p₁} ‖G_x‖_{p₂})^p ≤ ‖F‖_{p₁}^p ‖G‖_{p₂}^p` provided `1/p = 1/p₁ + 1/p₂`. -/
lemma lintegral_fibre_mul_le {p₁ p₂ p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (h1p₁ : 1 < p₁) (htp₁ : p₁ ≠ ∞) (h1p₂ : 1 < p₂) (htp₂ : p₂ ≠ ∞)
    (hpq : p₁⁻¹ + p₂⁻¹ = p⁻¹) [SFinite μ]
    {F G : 𝓧 × ℤ → ℂ} (hF : AEMeasurable F (μ.prod (Measure.count : Measure ℤ)))
    (hG : AEMeasurable G (μ.prod (Measure.count : Measure ℤ))) :
    (∫⁻ x, (eLpNorm (fun j => F (x, j)) p₁ (Measure.count : Measure ℤ)) ^ p.toReal
        * (eLpNorm (fun j => G (x, j)) p₂ (Measure.count : Measure ℤ)) ^ p.toReal ∂μ)
      ≤ (eLpNorm F p₁ (μ.prod (Measure.count : Measure ℤ))) ^ p.toReal
        * (eLpNorm G p₂ (μ.prod (Measure.count : Measure ℤ))) ^ p.toReal := by
  have h1 : p₁ ≠ 0 := (lt_trans one_pos h1p₁).ne'
  have h2 : p₂ ≠ 0 := (lt_trans one_pos h1p₂).ne'
  have hq : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp0, hptop⟩
  have hqpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hq₁ : 0 < p₁.toReal := ENNReal.toReal_pos h1 htp₁
  have hq₂ : 0 < p₂.toReal := ENNReal.toReal_pos h2 htp₂
  have hqe := intCast_toReal_inv_sum hp0 hptop h1p₁ htp₁ h1p₂ htp₂ hpq
  set Ax : 𝓧 → ℝ≥0∞ := fun x => ∫⁻ j, ‖F (x, j)‖ₑ ^ p₁.toReal ∂(Measure.count : Measure ℤ) with hAxdef
  set Bx : 𝓧 → ℝ≥0∞ := fun x => ∫⁻ j, ‖G (x, j)‖ₑ ^ p₂.toReal ∂(Measure.count : Measure ℤ) with hBxdef
  have hAx : AEMeasurable Ax μ := (hF.enorm.pow_const _).lintegral_prod_right'
  have hBx : AEMeasurable Bx μ := (hG.enorm.pow_const _).lintegral_prod_right'
  have hAxnorm : ∀ x, Ax x = (eLpNorm (fun j => F (x, j)) p₁ (Measure.count : Measure ℤ)) ^ p₁.toReal :=
    fun x => (eLpNorm_rpow_toReal h1 htp₁ (fun j => F (x, j))).symm
  have hBxnorm : ∀ x, Bx x = (eLpNorm (fun j => G (x, j)) p₂ (Measure.count : Measure ℤ)) ^ p₂.toReal :=
    fun x => (eLpNorm_rpow_toReal h2 htp₂ (fun j => G (x, j))).symm
  -- the two integrands agree
  have hcongr :
      (∫⁻ x, (eLpNorm (fun j => F (x, j)) p₁ (Measure.count : Measure ℤ)) ^ p.toReal
          * (eLpNorm (fun j => G (x, j)) p₂ (Measure.count : Measure ℤ)) ^ p.toReal ∂μ)
        = ∫⁻ x, (Ax x) ^ ((p.toReal) / p₁.toReal) * (Bx x) ^ ((p.toReal) / p₂.toReal) ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [hAxnorm x, hBxnorm x]
    congr 1
    · rw [← ENNReal.rpow_mul]
      congr 1
      field_simp
    · rw [← ENNReal.rpow_mul]
      congr 1
      field_simp
  rw [hcongr]
  -- Hölder
  have hHolderConj : Real.HolderConjugate (p₁.toReal / p.toReal) (p₂.toReal / p.toReal) := by
    refine ⟨?_, div_pos hq₁ hqpos, div_pos hq₂ hqpos⟩
    rw [inv_div, inv_div, inv_one, div_eq_mul_inv, div_eq_mul_inv, ← mul_add, hqe]
    exact mul_inv_cancel₀ hq
  have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hHolderConj
    (f := fun x => Ax x ^ (p.toReal / p₁.toReal))
    (g := fun x => Bx x ^ (p.toReal / p₂.toReal))
    (hAx.pow_const (p.toReal / p₁.toReal)) (hBx.pow_const (p.toReal / p₂.toReal))
  -- identify the pieces
  have hAxr : ∀ x, ((Ax x) ^ ((p.toReal) / p₁.toReal)) ^ (p₁.toReal / p.toReal) = Ax x := by
    intro x
    rw [← ENNReal.rpow_mul,
      show (p.toReal / p₁.toReal) * (p₁.toReal / p.toReal) = 1 by field_simp,
      ENNReal.rpow_one]
  have hBxr : ∀ x, ((Bx x) ^ ((p.toReal) / p₂.toReal)) ^ (p₂.toReal / p.toReal) = Bx x := by
    intro x
    rw [← ENNReal.rpow_mul,
      show (p.toReal / p₂.toReal) * (p₂.toReal / p.toReal) = 1 by field_simp,
      ENNReal.rpow_one]
  have hIntA : ∫⁻ x, Ax x ∂μ = (eLpNorm F p₁ (μ.prod (Measure.count : Measure ℤ))) ^ p₁.toReal := by
    rw [← lintegral_prod (fun z : 𝓧 × ℤ => ‖F z‖ₑ ^ p₁.toReal) ((hF.enorm.pow_const _))]
    exact (eLpNorm_rpow_toReal h1 htp₁ F).symm
  have hIntB : ∫⁻ x, Bx x ∂μ = (eLpNorm G p₂ (μ.prod (Measure.count : Measure ℤ))) ^ p₂.toReal := by
    rw [← lintegral_prod (fun z : 𝓧 × ℤ => ‖G z‖ₑ ^ p₂.toReal) ((hG.enorm.pow_const _))]
    exact (eLpNorm_rpow_toReal h2 htp₂ G).symm
  have hfP : (∫⁻ x, ((Ax x) ^ ((p.toReal) / p₁.toReal)) ^ (p₁.toReal / p.toReal) ∂μ)
        ^ (1 / (p₁.toReal / p.toReal))
      = (eLpNorm F p₁ (μ.prod (Measure.count : Measure ℤ))) ^ p.toReal := by
    have h1' : ∫⁻ x, ((Ax x) ^ ((p.toReal) / p₁.toReal)) ^ (p₁.toReal / p.toReal) ∂μ
        = ∫⁻ x, Ax x ∂μ := lintegral_congr fun x => hAxr x
    rw [h1', hIntA, one_div, inv_div, ← ENNReal.rpow_mul,
      show p₁.toReal * (p.toReal / p₁.toReal) = p.toReal from
        by rw [mul_comm, div_mul_cancel₀ _ hq₁.ne']]
  have hgP : (∫⁻ x, ((Bx x) ^ ((p.toReal) / p₂.toReal)) ^ (p₂.toReal / p.toReal) ∂μ)
        ^ (1 / (p₂.toReal / p.toReal))
      = (eLpNorm G p₂ (μ.prod (Measure.count : Measure ℤ))) ^ p.toReal := by
    have h1' : ∫⁻ x, ((Bx x) ^ ((p.toReal) / p₂.toReal)) ^ (p₂.toReal / p.toReal) ∂μ
        = ∫⁻ x, Bx x ∂μ := lintegral_congr fun x => hBxr x
    rw [h1', hIntB, one_div, inv_div, ← ENNReal.rpow_mul,
      show p₂.toReal * (p.toReal / p₂.toReal) = p.toReal from
        by rw [mul_comm, div_mul_cancel₀ _ hq₂.ne']]
  calc ∫⁻ x, (Ax x) ^ ((p.toReal) / p₁.toReal) * (Bx x) ^ ((p.toReal) / p₂.toReal) ∂μ
      ≤ (∫⁻ x, ((Ax x) ^ ((p.toReal) / p₁.toReal)) ^ (p₁.toReal / p.toReal) ∂μ)
            ^ (1 / (p₁.toReal / p.toReal))
          * (∫⁻ x, ((Bx x) ^ ((p.toReal) / p₂.toReal)) ^ (p₂.toReal / p.toReal) ∂μ)
            ^ (1 / (p₂.toReal / p.toReal)) := hHold
    _ = (eLpNorm F p₁ (μ.prod (Measure.count : Measure ℤ))) ^ p.toReal
          * (eLpNorm G p₂ (μ.prod (Measure.count : Measure ℤ))) ^ p.toReal := by
        rw [hfP, hgP]

end FibreHolder

/-! ## The variational estimate for a product system -/

/-- **Calderón transference, product systems.**  If the variational estimate holds for the
integer shift model, then it holds for every product system `(𝓧 × ℤ, μ × μ_ℤ, id × T_ℤ)`:
on such a system the averages do not mix the fibres `{x} × ℤ`, so the estimate may be applied to
each slice `F_x = fun n => F (x,n)` and the result integrated with Tonelli's theorem and
Hölder's inequality. -/
theorem eLpNorm_prodSys_le {r : ℝ≥0} (hr : 0 < r) {P : ℤ[X]} {p₁ p₂ p : ℝ≥0∞}
    {Cv : ℝ≥0 → ℝ≥0} (hZ : VarEstZ P p₁ p₂ p r Cv)
    {μ : Measure 𝓧} [SigmaFinite μ] {Λ : ℝ≥0} {a : ℕ → ℝ≥0}
    (hΛ : 1 < Λ) (ha : Lacunary Λ a) (ha' : ∀ n, 1 ≤ a n)
    {F G : 𝓧 × ℤ → ℂ}
    (hF : AEMeasurable F (μ.prod (Measure.count : Measure ℤ)))
    (hG : AEMeasurable G (μ.prod (Measure.count : Measure ℤ)))
    (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (h1p₁ : 1 < p₁) (htp₁ : p₁ ≠ ∞) (h1p₂ : 1 < p₂) (htp₂ : p₂ ≠ ∞)
    (hpq : p₁⁻¹ + p₂⁻¹ = p⁻¹) :
    eLpNorm (prodVar r P a F G) p (μ.prod (Measure.count : Measure ℤ))
      ≤ (Cv Λ : ℝ≥0∞) * eLpNorm F p₁ (μ.prod (Measure.count : Measure ℤ))
          * eLpNorm G p₂ (μ.prod (Measure.count : Measure ℤ)) := by
  set ν : Measure (𝓧 × ℤ) := μ.prod (Measure.count : Measure ℤ) with hν
  set W : 𝓧 × ℤ → ℝ≥0∞ := prodVar r P a F G with hW
  have hWmeas : AEMeasurable W ν := by
    rw [hW, hν]
    exact aemeasurable_prodVar hr hF hG
  have hqpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hq : p.toReal ≠ 0 := hqpos.ne'
  have hfib : ∀ x : 𝓧, eLpNorm (fun j => W (x, j)) p (Measure.count : Measure ℤ)
      ≤ (Cv Λ : ℝ≥0∞) * eLpNorm (fun j => F (x, j)) p₁ (Measure.count : Measure ℤ)
          * eLpNorm (fun j => G (x, j)) p₂ (Measure.count : Measure ℤ) := by
    intro x
    rw [hW, prodVar_fibre r P a F G x]
    exact hZ Λ a hΛ ha ha' (fun k => F (x, k)) (fun k => G (x, k))
  have key : (eLpNorm W p ν) ^ p.toReal
      = ∫⁻ x, (eLpNorm (fun j => W (x, j)) p (Measure.count : Measure ℤ)) ^ p.toReal ∂μ := by
    rw [hν]
    exact eLpNorm_prod_rpow_toReal hp0 hptop hWmeas
  have hstep : (eLpNorm W p ν) ^ p.toReal
      ≤ ((Cv Λ : ℝ≥0∞) * eLpNorm F p₁ ν * eLpNorm G p₂ ν) ^ p.toReal := by
    rw [key]
    calc ∫⁻ x, (eLpNorm (fun j => W (x, j)) p (Measure.count : Measure ℤ)) ^ p.toReal ∂μ
        ≤ ∫⁻ x, ((Cv Λ : ℝ≥0∞) * eLpNorm (fun j => F (x, j)) p₁ (Measure.count : Measure ℤ)
              * eLpNorm (fun j => G (x, j)) p₂ (Measure.count : Measure ℤ)) ^ p.toReal ∂μ :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (hfib x) hqpos.le
      _ = (Cv Λ : ℝ≥0∞) ^ p.toReal
            * ∫⁻ x, (eLpNorm (fun j => F (x, j)) p₁ (Measure.count : Measure ℤ)) ^ p.toReal
                * (eLpNorm (fun j => G (x, j)) p₂ (Measure.count : Measure ℤ)) ^ p.toReal ∂μ := by
          rw [lintegral_congr (fun x => by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hqpos.le,
              ENNReal.mul_rpow_of_nonneg _ _ hqpos.le, mul_assoc])]
          rw [lintegral_const_mul' _ _
            (ENNReal.rpow_ne_top_of_nonneg hqpos.le (ENNReal.coe_ne_top))]
      _ ≤ (Cv Λ : ℝ≥0∞) ^ p.toReal
            * ((eLpNorm F p₁ ν) ^ p.toReal * (eLpNorm G p₂ ν) ^ p.toReal) := by
          refine mul_le_mul' le_rfl ?_
          rw [hν]
          exact lintegral_fibre_mul_le hp0 hptop h1p₁ htp₁ h1p₂ htp₂ hpq hF hG
      _ = ((Cv Λ : ℝ≥0∞) * eLpNorm F p₁ ν * eLpNorm G p₂ ν) ^ p.toReal := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hqpos.le, ENNReal.mul_rpow_of_nonneg _ _ hqpos.le,
            mul_assoc]
  calc eLpNorm W p ν
      = ((eLpNorm W p ν) ^ p.toReal) ^ (p.toReal)⁻¹ := (ENNReal.rpow_rpow_inv hq _).symm
    _ ≤ (((Cv Λ : ℝ≥0∞) * eLpNorm F p₁ ν * eLpNorm G p₂ ν) ^ p.toReal) ^ (p.toReal)⁻¹ :=
        ENNReal.rpow_le_rpow hstep (by positivity)
    _ = (Cv Λ : ℝ≥0∞) * eLpNorm F p₁ ν * eLpNorm G p₂ ν := ENNReal.rpow_rpow_inv hq _

/-! ## The test functions on the product system

For the testing-function step of the Calderón transference we use, on the product system
`(𝓧 × ℤ, μ × μ_ℤ, id × T_ℤ)`, the functions
`f_M(x,n) = 1_{[1,B]}(n) f(T^{-n} x)`.
They are written as finite sums, which makes their measurability immediate, and they satisfy the
fibre identity `A_{𝓧×ℤ,N}(f_M,g_M)(x,n) = A_{𝓧,N}(f,g)(T^{-n}x)` for `n` in the middle range
`[CM^D,2CM^D]` and all scales `N` with `⌊N⌋ ≤ M`. -/

/-- The test function `f_M(x,n) = 1_{[1,B]}(n) f (T^{-n} x)`, written as a finite sum so that
measurability is immediate. -/
noncomputable def testFun (T : 𝓧 ≃ᵐ 𝓧) (f : 𝓧 → ℂ) (B : ℕ) (y : 𝓧 × ℤ) : ℂ :=
  ∑ k ∈ Finset.Icc (1 : ℤ) (B : ℤ),
    (if y.2 = k then f ((T ^ (-k) : 𝓧 ≃ 𝓧) y.1) else 0)

lemma testFun_apply (T : 𝓧 ≃ᵐ 𝓧) (f : 𝓧 → ℂ) (B : ℕ) (x : 𝓧) (j : ℤ) :
    testFun T f B (x, j)
      = if (1 : ℤ) ≤ j ∧ j ≤ (B : ℤ) then f ((T ^ (-j) : 𝓧 ≃ 𝓧) x) else 0 := by
  simp only [testFun, Finset.sum_ite_eq, Finset.mem_Icc]

lemma measurable_testFun {T : 𝓧 ≃ᵐ 𝓧} {f : 𝓧 → ℂ} (hf : Measurable f) (B : ℕ) :
    Measurable (testFun T f B) := by
  refine Finset.measurable_sum _ fun k _ => ?_
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurable_snd (measurableSet_singleton k)
  · exact hf.comp ((measurable_zpow_apply T (-k)).comp measurable_fst)

lemma aemeasurable_testFun {μ : Measure 𝓧} {T : 𝓧 ≃ᵐ 𝓧} {f : 𝓧 → ℂ}
    (hf : Measurable f) (B : ℕ) :
    AEMeasurable (testFun T f B) (μ.prod (Measure.count : Measure ℤ)) :=
  (measurable_testFun hf B).aemeasurable

/-- The iterate of a measurable equivalence behaves well under `zpow`. -/
lemma zpow_mul_apply (T : 𝓧 ≃ᵐ 𝓧) (m n : ℤ) (x : 𝓧) :
    ((T ^ (m + n) : 𝓧 ≃ 𝓧)) x = ((T ^ m : 𝓧 ≃ 𝓧)) (((T ^ n : 𝓧 ≃ 𝓧)) x) := by
  rw [zpow_add]
  exact Equiv.Perm.mul_apply _ _ _

/-- **The fibre identity for the test functions.**  For the product system, the average of the
test functions `f_M, g_M` at `(x,j)` is the average of `f, g` at `T^{-j}x`, provided the shifts
`j - P_i(n)` all land in the support `[1,B]` of the test functions. -/
lemma A_prodSys_testFun_eq (N : ℝ≥0) (T : 𝓧 ≃ᵐ 𝓧) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (B : ℕ)
    (x : 𝓧) (j : ℤ)
    (h1 : ∀ n : ℤ, 1 ≤ n → n ≤ (Nat.floor N : ℤ) →
      1 ≤ j - P₁.eval n ∧ j - P₁.eval n ≤ (B : ℤ))
    (h2 : ∀ n : ℤ, 1 ≤ n → n ≤ (Nat.floor N : ℤ) →
      1 ≤ j - P₂.eval n ∧ j - P₂.eval n ≤ (B : ℤ)) :
    A (prodSys 𝓧) N P₁ P₂ (testFun T f B) (testFun T g B) (x, j)
      = A T N P₁ P₂ f g (((T : 𝓧 ≃ 𝓧) ^ (-j)) x) := by
  simp only [A]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn'' : 1 ≤ n ∧ n ≤ Nat.floor N := Finset.mem_Icc.mp hn
  have hn' : (1 : ℤ) ≤ (n : ℤ) ∧ (n : ℤ) ≤ (Nat.floor N : ℤ) :=
    ⟨by exact_mod_cast hn''.1, by exact_mod_cast hn''.2⟩
  have hP₁ : testFun T f B (((prodSys 𝓧 : (𝓧 × ℤ) ≃ᵐ (𝓧 × ℤ)) ^ (P₁.eval (n : ℤ)) :
        (𝓧 × ℤ) ≃ (𝓧 × ℤ)) (x, j))
      = f (((T : 𝓧 ≃ 𝓧) ^ (P₁.eval (n : ℤ) + (-j))) x) := by
    rw [prodSys_zpow, testFun_apply, if_pos (h1 (n : ℤ) hn'.1 hn'.2)]
    congr 1
    ring_nf
  have hP₂ : testFun T g B (((prodSys 𝓧 : (𝓧 × ℤ) ≃ᵐ (𝓧 × ℤ)) ^ (P₂.eval (n : ℤ)) :
        (𝓧 × ℤ) ≃ (𝓧 × ℤ)) (x, j))
      = g (((T : 𝓧 ≃ 𝓧) ^ (P₂.eval (n : ℤ) + (-j))) x) := by
    rw [prodSys_zpow, testFun_apply, if_pos (h2 (n : ℤ) hn'.1 hn'.2)]
    congr 1
    ring_nf
  rw [hP₁, hP₂, zpow_mul_apply, zpow_mul_apply]

/-! ## The `Lᵖ` norm of the test functions -/

/-- A positive power of a measure-preserving equivalence is measure preserving. -/
lemma measurePreserving_zpow_apply {μ : Measure 𝓧} {T : 𝓧 ≃ᵐ 𝓧}
    (hT : MeasurePreserving (T : 𝓧 ≃ᵐ 𝓧) μ μ) (k : ℤ) :
    MeasurePreserving (fun x => (T ^ k : 𝓧 ≃ 𝓧) x) μ μ := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · subst hm
    have h1 : (fun x => (T ^ (m : ℤ) : 𝓧 ≃ 𝓧) x) = (T : 𝓧 → 𝓧)^[m] := by
      funext x
      rw [show (T ^ (m : ℤ) : 𝓧 ≃ 𝓧) = (T : 𝓧 ≃ 𝓧) ^ m from by simp [zpow_natCast]]
      exact congrFun (Equiv.Perm.coe_pow (T : 𝓧 ≃ 𝓧) m) x
    rw [h1]
    exact hT.iterate m
  · subst hm
    have h1 : (fun x => (T ^ (-(m : ℤ)) : 𝓧 ≃ 𝓧) x) = (T.symm : 𝓧 → 𝓧)^[m] := by
      funext x
      rw [show (T ^ (-(m : ℤ)) : 𝓧 ≃ 𝓧) = (T.symm : 𝓧 ≃ 𝓧) ^ m from by
        rw [zpow_neg, zpow_natCast, ← inv_pow]
        rfl]
      exact congrFun (Equiv.Perm.coe_pow (T.symm : 𝓧 ≃ 𝓧) m) x
    rw [h1]
    exact (MeasurePreserving.symm T hT).iterate m

/-- The `p₁`-th power of the `Lᵖ` norm of the test function `f_M` is `B` times that of `f`,
because the `B` translates of `f` along the orbit of `T` are disjoint (as the measure is
preserved). -/
lemma eLpNorm_testFun {μ : Measure 𝓧} [SigmaFinite μ] {T : 𝓧 ≃ᵐ 𝓧}
    (hT : MeasurePreserving (T : 𝓧 ≃ᵐ 𝓧) μ μ) {f : 𝓧 → ℂ} (hf : Measurable f) {B : ℕ}
    {p₁ : ℝ≥0∞} (hp₁0 : p₁ ≠ 0) (hp₁top : p₁ ≠ ∞) :
    (eLpNorm (testFun T f B) p₁ (μ.prod (Measure.count : Measure ℤ))) ^ p₁.toReal
      = (B : ℝ≥0∞) * (eLpNorm f p₁ μ) ^ p₁.toReal := by
  have hq : 0 < p₁.toReal := ENNReal.toReal_pos hp₁0 hp₁top
  have hval : ∀ (x : 𝓧) (j : ℤ), ‖testFun T f B (x, j)‖ₑ ^ p₁.toReal
      = if j ∈ Finset.Icc (1 : ℤ) (B : ℤ) then
          ‖f ((T ^ (-j) : 𝓧 ≃ 𝓧) x)‖ₑ ^ p₁.toReal else 0 := by
    intro x j
    rw [testFun_apply]
    by_cases hj : (1 : ℤ) ≤ j ∧ j ≤ (B : ℤ)
    · rw [if_pos hj, if_pos (Finset.mem_Icc.mpr hj)]
    · rw [if_neg hj, if_neg (fun hc => hj (Finset.mem_Icc.mp hc))]
      rw [enorm_zero, ENNReal.zero_rpow_of_pos hq]
  rw [eLpNorm_rpow_toReal hp₁0 hp₁top _ (measurable_testFun hf B).aestronglyMeasurable]
  rw [lintegral_prod _ (((measurable_testFun hf B).enorm.pow_const _).aemeasurable)]
  have hstep1 : (fun x : 𝓧 =>
        ∫⁻ j, ‖testFun T f B (x, j)‖ₑ ^ p₁.toReal ∂(Measure.count : Measure ℤ))
      = fun x => ∑ j ∈ Finset.Icc (1 : ℤ) (B : ℤ),
          ‖f ((T ^ (-j) : 𝓧 ≃ 𝓧) x)‖ₑ ^ p₁.toReal := by
    funext x
    rw [lintegral_count]
    rw [tsum_eq_sum (s := Finset.Icc (1 : ℤ) (B : ℤ))
      (f := fun j => ‖testFun T f B (x, j)‖ₑ ^ p₁.toReal) (fun j hj => by
        rw [hval]; simp [hj])]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hval, if_pos hj]
  rw [hstep1]
  rw [lintegral_finsetSum (Finset.Icc (1 : ℤ) (B : ℤ))
      (f := fun j (x : 𝓧) => ‖f ((T ^ (-j) : 𝓧 ≃ 𝓧) x)‖ₑ ^ p₁.toReal)
      (fun j _ => ((hf.comp (measurable_zpow_apply T (-j))).enorm).pow_const _)]
  have hterm : ∀ j ∈ Finset.Icc (1 : ℤ) (B : ℤ),
      ∫⁻ x, ‖f ((T ^ (-j) : 𝓧 ≃ 𝓧) x)‖ₑ ^ p₁.toReal ∂μ
        = ∫⁻ y, ‖f y‖ₑ ^ p₁.toReal ∂μ :=
    fun j _ => MeasurePreserving.lintegral_comp (measurePreserving_zpow_apply hT (-j))
      ((hf.enorm).pow_const _)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Int.card_Icc]
  have hcard : ((((B : ℤ) + 1 - 1).toNat : ℕ) : ℝ≥0∞) = (B : ℝ≥0∞) := by
    rw [show (B : ℤ) + 1 - 1 = (B : ℤ) by ring, Int.toNat_natCast]
  rw [nsmul_eq_mul, hcard, eLpNorm_rpow_toReal hp₁0 hp₁top f]



/-! ## The lower bound for the testing-function step -/

/-- Pointwise lower bound: on the middle range of the `ℤ`-coordinate, the variational norm of
the averages of the test functions on the product system dominates the variational norm of the
averages of `f, g` on the original system, restricted to the scales `a 0, …, a K`. -/
lemma prodVar_testFun_lower {r : ℝ≥0} {P : ℤ[X]} {a : ℕ → ℝ≥0} {K M B : ℕ} {T : 𝓧 ≃ᵐ 𝓧}
    {f g : 𝓧 → ℂ} (x : 𝓧) (j : ℤ)
    (hMK : ∀ n : ℕ, n ≤ K → Nat.floor (a n) ≤ M)
    (hcond : ∀ n : ℤ, 1 ≤ n → n ≤ (M : ℤ) →
      (1 ≤ j - n ∧ j - n ≤ (B : ℤ)) ∧ (1 ≤ j - P.eval n ∧ j - P.eval n ≤ (B : ℤ))) :
    variationalNorm r (fun n => A T (a (min n K)) X P f g (((T : 𝓧 ≃ 𝓧) ^ (-j)) x))
      ≤ prodVar r P a (testFun T f B) (testFun T g B) (x, j) := by
  refine le_trans (le_of_eq ?_) (variationalNorm_comp_min_le r
    (fun n => A (prodSys 𝓧) (a n) X P (testFun T f B) (testFun T g B) (x, j)) K)
  congr 1
  funext n
  have hn : Nat.floor (a (min n K)) ≤ M := hMK (min n K) (min_le_right n K)
  refine (A_prodSys_testFun_eq (a (min n K)) T X P f g B x j ?_ ?_).symm
  · intro m hm1 hm2
    have hm2' : m ≤ (M : ℤ) := le_trans hm2 (by exact_mod_cast hn)
    simpa [Polynomial.eval_X] using (hcond m hm1 hm2').1
  · intro m hm1 hm2
    exact (hcond m hm1 (le_trans hm2 (by exact_mod_cast hn))).2

/-- Integrated lower bound: the `Lᵖ` norm of the variational norm of the test-function averages on
the product system dominates `card J` times the `p`-th power of the `Lᵖ` norm of the variational
norm of the averages of `f, g` restricted to the scales `a 0, …, a K`. -/
lemma prodVar_testFun_lower_lp {r : ℝ≥0} (hr : 0 < r) {P : ℤ[X]} {a : ℕ → ℝ≥0}
    {D Cfan K M B : ℕ} {T : 𝓧 ≃ᵐ 𝓧} {f g : 𝓧 → ℂ} (hf : Measurable f) (hg : Measurable g)
    {μ : Measure 𝓧} [SigmaFinite μ] (hT : MeasurePreserving (T : 𝓧 ≃ᵐ 𝓧) μ μ)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (hMK : ∀ n : ℕ, n ≤ K → Nat.floor (a n) ≤ M)
    (hcond : ∀ j ∈ Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ), ∀ n : ℤ, 1 ≤ n →
      n ≤ (M : ℤ) →
      (1 ≤ j - n ∧ j - n ≤ (B : ℤ)) ∧ (1 ≤ j - P.eval n ∧ j - P.eval n ≤ (B : ℤ))) :
    ((Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card : ℝ≥0∞) *
      (eLpNorm (fun y => variationalNorm r (fun n => A T (a (min n K)) X P f g y)) p μ)
        ^ p.toReal
      ≤ (eLpNorm (prodVar r P a (testFun T f B) (testFun T g B)) p
          (μ.prod (Measure.count : Measure ℤ))) ^ p.toReal := by
  set J : Finset ℤ := Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ) with hJdef
  have hJmem : ∀ j ∈ J, j ∈ Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ) :=
    fun j hj => hj
  set VK : 𝓧 → ℝ≥0∞ := fun y => variationalNorm r (fun n => A T (a (min n K)) X P f g y)
    with hVK
  set W : 𝓧 × ℤ → ℝ≥0∞ := prodVar r P a (testFun T f B) (testFun T g B) with hW
  have hWmeas : AEMeasurable W (μ.prod (Measure.count : Measure ℤ)) := by
    rw [hW]
    exact aemeasurable_prodVar hr (aemeasurable_testFun hf B) (aemeasurable_testFun hg B)
  have hVKmeas : Measurable VK := by
    rw [hVK]
    exact measurable_variationalNorm hr (fun n => measurable_A T (a (min n K)) X P hf hg)
  have hL : (eLpNorm W p (μ.prod (Measure.count : Measure ℤ))) ^ p.toReal
      = ∫⁻ z : 𝓧 × ℤ, W z ^ p.toReal ∂(μ.prod (Measure.count : Measure ℤ)) := by
    rw [eLpNorm_rpow_toReal hp0 hptop _ hWmeas.aestronglyMeasurable]
    exact lintegral_congr fun z => by simp only [enorm_eq_self]
  have hR : (eLpNorm VK p μ) ^ p.toReal = ∫⁻ y, VK y ^ p.toReal ∂μ := by
    rw [eLpNorm_rpow_toReal hp0 hptop _ hVKmeas.aestronglyMeasurable]
    exact lintegral_congr fun y => by simp only [enorm_eq_self]
  rw [hL, hR]
  have hpt : ∀ x : 𝓧, ∑ j ∈ J, VK (((T : 𝓧 ≃ 𝓧) ^ (-j)) x) ^ p.toReal
      ≤ ∑ j ∈ J, W (x, j) ^ p.toReal := by
    intro x
    refine Finset.sum_le_sum fun j hj => ?_
    refine ENNReal.rpow_le_rpow ?_ (ENNReal.toReal_pos hp0 hptop).le
    rw [hVK, hW]
    exact prodVar_testFun_lower x j hMK (hcond j (hJmem j hj))
  have hcard : (∑ _j ∈ J, ∫⁻ y, VK y ^ p.toReal ∂μ)
      = (J.card : ℝ≥0∞) * ∫⁻ y, VK y ^ p.toReal ∂μ := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hfirst : (J.card : ℝ≥0∞) * ∫⁻ y, VK y ^ p.toReal ∂μ
      = ∫⁻ x, ∑ j ∈ J, VK (((T : 𝓧 ≃ 𝓧) ^ (-j)) x) ^ p.toReal ∂μ := by
    have hswap : (∑ j ∈ J, ∫⁻ y, VK y ^ p.toReal ∂μ)
        = ∑ j ∈ J, ∫⁻ x, VK (((T : 𝓧 ≃ 𝓧) ^ (-j)) x) ^ p.toReal ∂μ :=
      Finset.sum_congr rfl fun j _ =>
        (MeasurePreserving.lintegral_comp (measurePreserving_zpow_apply hT (-j))
          (f := fun b => VK b ^ p.toReal) (hVKmeas.pow_const _)).symm
    rw [← hcard, hswap]
    exact (lintegral_finsetSum J (f := fun j (x : 𝓧) =>
      VK (((T : 𝓧 ≃ 𝓧) ^ (-j)) x) ^ p.toReal)
      (fun j _ => (hVKmeas.comp (measurable_zpow_apply T (-j))).pow_const _)).symm
  calc (J.card : ℝ≥0∞) * ∫⁻ y, VK y ^ p.toReal ∂μ
      = ∫⁻ x, ∑ j ∈ J, VK (((T : 𝓧 ≃ 𝓧) ^ (-j)) x) ^ p.toReal ∂μ := hfirst
    _ ≤ ∫⁻ x, ∑ j ∈ J, W (x, j) ^ p.toReal ∂μ := lintegral_mono fun x => hpt x
    _ ≤ ∫⁻ x, ∫⁻ j, W (x, j) ^ p.toReal ∂(Measure.count : Measure ℤ) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [lintegral_count, ENNReal.tsum_eq_iSup_sum]
        exact le_iSup (fun s : Finset ℤ => ∑ j ∈ s, W (x, j) ^ p.toReal) J
    _ = ∫⁻ z : 𝓧 × ℤ, W z ^ p.toReal ∂(μ.prod (Measure.count : Measure ℤ)) :=
        (lintegral_prod _ (hWmeas.pow_const _)).symm

/-! ## Calderón transference: the ℤ-shift estimate implies the ergodic estimate -/

open scoped Classical in
/-- **Calderón transference (Krause--Mirek--Tao, Proposition 3.1 (ii)).**  The variational
estimate for the integer shift model implies the variational estimate for an arbitrary
measure-preserving system `(𝓧, μ, T)`, in the Hölder exponent case `1/p = 1/p₁ + 1/p₂`. -/
theorem varEst_of_varEstZ {r : ℝ≥0} (hr : 1 ≤ r) {P : ℤ[X]}
    {p₁ p₂ p : ℝ≥0∞} {Cv : ℝ≥0 → ℝ≥0} (hZ : VarEstZ P p₁ p₂ p r Cv)
    {μ : Measure 𝓧} [SigmaFinite μ] {T : 𝓧 ≃ᵐ 𝓧}
    (hT : MeasurePreserving (T : 𝓧 ≃ᵐ 𝓧) μ μ)
    {Λ : ℝ≥0} {a : ℕ → ℝ≥0} (hΛ : 1 < Λ) (ha : Lacunary Λ a) (ha' : ∀ n, 1 ≤ a n)
    {f g : 𝓧 → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) (hp1 : 1 ≤ p)
    (h1p₁ : 1 < p₁) (htp₁ : p₁ ≠ ∞) (h1p₂ : 1 < p₂) (htp₂ : p₂ ≠ ∞)
    (hpq : p₁⁻¹ + p₂⁻¹ = p⁻¹) :
    eLpNorm (fun x => variationalNorm r (fun n => A T (a n) X P f g x)) p μ
      ≤ (10 * Cv Λ : ℝ≥0) * eLpNorm f p₁ μ * eLpNorm g p₂ μ := by
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr
  have hqne : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp0, hptop⟩
  have hqpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hp1pos : 0 < p.toReal := hqpos
  have hq1ne : p₁.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨(lt_trans one_pos h1p₁).ne', htp₁⟩
  have hq2ne : p₂.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨(lt_trans one_pos h1p₂).ne', htp₂⟩
  have hrel : p.toReal / p₁.toReal + p.toReal / p₂.toReal = 1 := by
    have h := intCast_toReal_inv_sum hp0 hptop h1p₁ htp₁ h1p₂ htp₂ hpq
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_add, h]
    exact mul_inv_cancel₀ hqne
  have hqq : 0 < p.toReal / p₁.toReal := div_pos hqpos
    (ENNReal.toReal_pos (lt_trans one_pos h1p₁).ne' htp₁)
  have hqq₂ : 0 < p.toReal / p₂.toReal := div_pos hqpos
    (ENNReal.toReal_pos (lt_trans one_pos h1p₂).ne' htp₂)
  have hmono_a : Monotone a := Commons.Analysis.Real.monotone_of_lacunary hΛ (lacunary_mul_le ha ha')
  -- the pointwise bound for each clamped sequence
  have hpoint : ∀ K : ℕ, eLpNorm
      (fun x => variationalNorm r (fun n => A T (a (min n K)) X P f g x)) p μ
      ≤ (10 * Cv Λ : ℝ≥0) * eLpNorm f p₁ μ * eLpNorm g p₂ μ := by
    intro K
    obtain ⟨C₁, hC₁nn, hC₁⟩ := exists_abs_intCast_eval_le P
    set Cfan : ℕ := max 2 (⌈C₁⌉₊ + 1) with hCfan
    have hCfan2 : 2 ≤ Cfan := le_max_left _ _
    have hCfan1 : 1 ≤ Cfan := le_trans (by norm_num) hCfan2
    have hCfanC₁ : C₁ ≤ (Cfan : ℝ) := by
      refine le_trans (Nat.le_ceil C₁) ?_
      exact_mod_cast (le_trans (Nat.le_succ _) (le_max_right 2 (⌈C₁⌉₊ + 1)))
    set D : ℕ := max 1 P.natDegree with hD
    have hD1 : 1 ≤ D := le_max_left _ _
    have hDdeg : P.natDegree ≤ D := le_max_right _ _
    set M : ℕ := max ⌈a K⌉₊ 1 with hM
    have hM1 : 1 ≤ M := le_max_right _ _
    have haKM : a K ≤ (M : ℝ≥0) := le_trans (Nat.le_ceil (a K)) (by exact_mod_cast le_max_left _ _)
    set B : ℕ := 5 * Cfan * M ^ D with hB
    -- the growth bound for `P`
    have hPbound : ∀ n : ℤ, 1 ≤ n → n ≤ (M : ℤ) →
        |((P.eval n : ℤ) : ℝ)| ≤ (Cfan * M ^ D : ℕ) := by
      intro n hn1 hnM
      have hnpos : (0 : ℝ) ≤ (n : ℝ) := by
        have : (0 : ℤ) ≤ n := le_trans (by norm_num) hn1
        exact_mod_cast this
      have hnabs : |(n : ℝ)| ≤ (M : ℝ) := by
        rw [abs_of_nonneg hnpos]; exact_mod_cast hnM
      have hmax : max |(n : ℝ)| 1 ≤ (M : ℝ) :=
        max_le hnabs (by exact_mod_cast hM1)
      have hMnn : (0 : ℝ) ≤ (M : ℝ) := by positivity
      calc |((P.eval n : ℤ) : ℝ)| ≤ C₁ * max |(n : ℝ)| 1 ^ P.natDegree := hC₁ n
        _ ≤ C₁ * (M : ℝ) ^ D := by
            refine mul_le_mul_of_nonneg_left ?_ hC₁nn
            calc max |(n : ℝ)| 1 ^ P.natDegree ≤ (M : ℝ) ^ P.natDegree :=
                  pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hmax _
              _ ≤ (M : ℝ) ^ D := pow_le_pow_right₀ (by exact_mod_cast hM1) hDdeg
        _ ≤ ((Cfan * M ^ D : ℕ) : ℝ) := by
            push_cast
            exact mul_le_mul_of_nonneg_right hCfanC₁ (by positivity)
    have hMK : ∀ n : ℕ, n ≤ K → Nat.floor (a n) ≤ M := by
      intro n hn
      have h1 : Nat.floor (a n) ≤ Nat.floor (a K) := Nat.floor_mono (hmono_a hn)
      have h2 : Nat.floor (a K) ≤ M := by
        have : ((Nat.floor (a K) : ℕ) : ℝ≥0) ≤ (M : ℝ≥0) :=
          le_trans (Nat.floor_le (by positivity)) haKM
        exact_mod_cast this
      exact le_trans h1 h2
    have hXD1 : M + 1 ≤ 2 * (Cfan * M ^ D) := by
      have hMD : M ≤ M ^ D := by
        calc M = M ^ 1 := (pow_one M).symm
          _ ≤ M ^ D := Nat.pow_le_pow_right hM1 hD1
      have hMle : M ≤ Cfan * M ^ D := le_trans hMD (Nat.le_mul_of_pos_left _ (by omega))
      omega
    have hcond : ∀ j ∈ Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ),
        ∀ n : ℤ, 1 ≤ n → n ≤ (M : ℤ) →
        (1 ≤ j - n ∧ j - n ≤ (B : ℤ)) ∧ (1 ≤ j - P.eval n ∧ j - P.eval n ≤ (B : ℤ)) := by
      intro j hj n hn1 hnM
      have h2A : (2 * Cfan * M ^ D : ℤ) = 2 * ((Cfan * M ^ D : ℕ) : ℤ) := by push_cast; ring
      have h4A : (4 * Cfan * M ^ D : ℤ) = 4 * ((Cfan * M ^ D : ℕ) : ℤ) := by push_cast; ring
      have hjlo : 2 * ((Cfan * M ^ D : ℕ) : ℤ) ≤ j := by
        rw [← h2A]; exact (Finset.mem_Icc.mp hj).1
      have hjhi : j ≤ 4 * ((Cfan * M ^ D : ℕ) : ℤ) := by
        rw [← h4A]; exact (Finset.mem_Icc.mp hj).2
      have hXD1z : (M : ℤ) + 1 ≤ 2 * ((Cfan * M ^ D : ℕ) : ℤ) := by
        have h2 : ((M + 1 : ℕ) : ℤ) ≤ ((2 * (Cfan * M ^ D) : ℕ) : ℤ) := by exact_mod_cast hXD1
        have e1 : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by push_cast; ring
        have e2 : ((2 * (Cfan * M ^ D) : ℕ) : ℤ) = 2 * ((Cfan * M ^ D : ℕ) : ℤ) := by
          push_cast; ring
        rw [e1, e2] at h2
        exact h2
      have hPabs : |((P.eval n : ℤ) : ℝ)| ≤ ((Cfan * M ^ D : ℕ) : ℝ) := hPbound n hn1 hnM
      have hPl : P.eval n ≤ ((Cfan * M ^ D : ℕ) : ℤ) := by
        have : ((P.eval n : ℤ) : ℝ) ≤ ((Cfan * M ^ D : ℕ) : ℝ) :=
          le_trans (le_abs_self _) hPabs
        exact_mod_cast this
      have hPg : -(((Cfan * M ^ D : ℕ) : ℤ)) ≤ P.eval n := by
        have h1 : -(((Cfan * M ^ D : ℕ) : ℝ)) ≤ -|((P.eval n : ℤ) : ℝ)| := neg_le_neg hPabs
        have h2 : -|((P.eval n : ℤ) : ℝ)| ≤ ((P.eval n : ℤ) : ℝ) := neg_abs_le _
        exact_mod_cast (le_trans h1 h2)
      have hBz : (B : ℤ) = 5 * ((Cfan * M ^ D : ℕ) : ℤ) := by
        rw [hB]; push_cast; ring
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

    have hcardval : (Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card
        = 2 * Cfan * M ^ D + 1 := by
      rw [Int.card_Icc]
      have h : (4 * Cfan * M ^ D : ℤ) + 1 - (2 * Cfan * M ^ D : ℤ)
          = ((2 * Cfan * M ^ D + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h, Int.toNat_natCast]
    have hcardnn : ((Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card : ℝ≥0∞) ≠ 0 := by
      rw [hcardval, ne_eq, Nat.cast_eq_zero]; omega
    have hBJ : (B : ℝ≥0∞) ≤ ((Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card : ℝ≥0∞)
        * 3 := by
      rw [hcardval, hB]
      have h : 5 * Cfan * M ^ D ≤ (2 * Cfan * M ^ D + 1) * 3 := by
        nlinarith [Nat.zero_le (Cfan * M ^ D)]
      calc ((5 * Cfan * M ^ D : ℕ) : ℝ≥0∞)
          ≤ (((2 * Cfan * M ^ D + 1) * 3 : ℕ) : ℝ≥0∞) := Nat.cast_le.mpr h
        _ = ((2 * Cfan * M ^ D + 1 : ℕ) : ℝ≥0∞) * 3 := by push_cast; ring
    have h310 : (3 : ℝ≥0∞) ≤ (10 : ℝ≥0∞) ^ p.toReal := by
      have hq1 : (1 : ℝ) ≤ p.toReal := by
        have := ENNReal.toReal_mono hptop hp1
        simpa using this
      calc (3 : ℝ≥0∞) ≤ 10 := by norm_num
        _ = (10 : ℝ≥0∞) ^ (1 : ℝ) := (ENNReal.rpow_one 10).symm
        _ ≤ (10 : ℝ≥0∞) ^ p.toReal := ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hq1
    have hlow := prodVar_testFun_lower_lp (P := P) (μ := μ) hrpos hf hg hT hp0 hptop hMK hcond
    have hup := eLpNorm_prodSys_le (P := P) (μ := μ) hrpos hZ hΛ ha ha'
      (aemeasurable_testFun (μ := μ) (T := T) hf B) (aemeasurable_testFun (μ := μ) (T := T) hg B)
      hp0 hptop
      h1p₁ htp₁ h1p₂ htp₂ hpq
    have hn₁ := eLpNorm_testFun (μ := μ) (T := T) hT hf (B := B) (p₁ := p₁)
      (lt_trans one_pos h1p₁).ne' htp₁
    have hn₂ := eLpNorm_testFun (μ := μ) (T := T) hT hg (B := B) (p₁ := p₂)
      (lt_trans one_pos h1p₂).ne' htp₂
    set XV : ℝ≥0∞ := eLpNorm (fun x => variationalNorm r (fun n => A T (a (min n K)) X P f g x)) p μ with hXV
    set PV : ℝ≥0∞ := eLpNorm (prodVar r P a (testFun T f B) (testFun T g B)) p
      (μ.prod (Measure.count : Measure ℤ)) with hPV
    have hA : (eLpNorm (testFun T f B) p₁ (μ.prod (Measure.count : Measure ℤ))) ^ p.toReal
        = (B : ℝ≥0∞) ^ (p.toReal / p₁.toReal) * (eLpNorm f p₁ μ) ^ p.toReal := by
      calc (eLpNorm (testFun T f B) p₁ (μ.prod (Measure.count : Measure ℤ))) ^ p.toReal
          = ((eLpNorm (testFun T f B) p₁ (μ.prod (Measure.count : Measure ℤ))) ^ p₁.toReal)
              ^ (p.toReal / p₁.toReal) := by
            rw [← ENNReal.rpow_mul,
              show p₁.toReal * (p.toReal / p₁.toReal) = p.toReal from by field_simp]
        _ = ((B : ℝ≥0∞) * (eLpNorm f p₁ μ) ^ p₁.toReal) ^ (p.toReal / p₁.toReal) := by rw [hn₁]
        _ = (B : ℝ≥0∞) ^ (p.toReal / p₁.toReal)
              * ((eLpNorm f p₁ μ) ^ p₁.toReal) ^ (p.toReal / p₁.toReal) :=
            ENNReal.mul_rpow_of_nonneg _ _ hqq.le
        _ = (B : ℝ≥0∞) ^ (p.toReal / p₁.toReal) * (eLpNorm f p₁ μ) ^ p.toReal := by
            rw [← ENNReal.rpow_mul,
              show p₁.toReal * (p.toReal / p₁.toReal) = p.toReal from by field_simp]
    have hG : (eLpNorm (testFun T g B) p₂ (μ.prod (Measure.count : Measure ℤ))) ^ p.toReal
        = (B : ℝ≥0∞) ^ (p.toReal / p₂.toReal) * (eLpNorm g p₂ μ) ^ p.toReal := by
      calc (eLpNorm (testFun T g B) p₂ (μ.prod (Measure.count : Measure ℤ))) ^ p.toReal
          = ((eLpNorm (testFun T g B) p₂ (μ.prod (Measure.count : Measure ℤ))) ^ p₂.toReal)
              ^ (p.toReal / p₂.toReal) := by
            rw [← ENNReal.rpow_mul,
              show p₂.toReal * (p.toReal / p₂.toReal) = p.toReal from by field_simp]
        _ = ((B : ℝ≥0∞) * (eLpNorm g p₂ μ) ^ p₂.toReal) ^ (p.toReal / p₂.toReal) := by rw [hn₂]
        _ = (B : ℝ≥0∞) ^ (p.toReal / p₂.toReal)
              * ((eLpNorm g p₂ μ) ^ p₂.toReal) ^ (p.toReal / p₂.toReal) :=
            ENNReal.mul_rpow_of_nonneg _ _ hqq₂.le
        _ = (B : ℝ≥0∞) ^ (p.toReal / p₂.toReal) * (eLpNorm g p₂ μ) ^ p.toReal := by
            rw [← ENNReal.rpow_mul,
              show p₂.toReal * (p.toReal / p₂.toReal) = p.toReal from by field_simp]
    have hBtop : (B : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hB0 : (B : ℝ≥0∞) ≠ 0 := by
      rw [hB]; positivity
    have hpow : (B : ℝ≥0∞) ^ (p.toReal / p₁.toReal) * (B : ℝ≥0∞) ^ (p.toReal / p₂.toReal)
        = (B : ℝ≥0∞) := by
      rw [← ENNReal.rpow_add _ _ hB0 hBtop, hrel, ENNReal.rpow_one]
    have hupq : PV ^ p.toReal
        ≤ (Cv Λ : ℝ≥0∞) ^ p.toReal * (B : ℝ≥0∞) * (eLpNorm f p₁ μ) ^ p.toReal
          * (eLpNorm g p₂ μ) ^ p.toReal := by
      have h2 : PV ^ p.toReal ≤ ((Cv Λ : ℝ≥0∞)
          * eLpNorm (testFun T f B) p₁ (μ.prod (Measure.count : Measure ℤ))
          * eLpNorm (testFun T g B) p₂ (μ.prod (Measure.count : Measure ℤ))) ^ p.toReal :=
        ENNReal.rpow_le_rpow hup hqpos.le
      have h3 := h2
      rw [ENNReal.mul_rpow_of_nonneg _ _ hqpos.le, ENNReal.mul_rpow_of_nonneg _ _ hqpos.le,
        hA, hG] at h3
      refine h3.trans (le_of_eq ?_)
      calc (Cv Λ : ℝ≥0∞) ^ p.toReal
            * (↑B ^ (p.toReal / p₁.toReal) * (eLpNorm f p₁ μ) ^ p.toReal)
            * (↑B ^ (p.toReal / p₂.toReal) * (eLpNorm g p₂ μ) ^ p.toReal)
          = (Cv Λ : ℝ≥0∞) ^ p.toReal
              * (↑B ^ (p.toReal / p₁.toReal) * ↑B ^ (p.toReal / p₂.toReal))
              * ((eLpNorm f p₁ μ) ^ p.toReal * (eLpNorm g p₂ μ) ^ p.toReal) := by ac_rfl
        _ = (Cv Λ : ℝ≥0∞) ^ p.toReal * ↑B
              * ((eLpNorm f p₁ μ) ^ p.toReal * (eLpNorm g p₂ μ) ^ p.toReal) := by rw [hpow]
        _ = (Cv Λ : ℝ≥0∞) ^ p.toReal * ↑B * (eLpNorm f p₁ μ) ^ p.toReal
              * (eLpNorm g p₂ μ) ^ p.toReal := by ac_rfl
    have hcomb : ((Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card : ℝ≥0∞)
          * XV ^ p.toReal
        ≤ ((Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card : ℝ≥0∞)
          * (((10 : ℝ≥0∞) * (Cv Λ : ℝ≥0∞)) ^ p.toReal
            * (eLpNorm f p₁ μ) ^ p.toReal * (eLpNorm g p₂ μ) ^ p.toReal) := by
      have hstep : (Cv Λ : ℝ≥0∞) ^ p.toReal * (B : ℝ≥0∞)
          ≤ ((Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card : ℝ≥0∞)
            * ((10 : ℝ≥0∞) * (Cv Λ : ℝ≥0∞)) ^ p.toReal := by
        have hBJ' : (B : ℝ≥0∞)
            ≤ (((Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card : ℕ) : ℝ≥0∞)
              * (10 : ℝ≥0∞) ^ p.toReal := by
          exact hBJ.trans (mul_le_mul' le_rfl h310)
        calc (Cv Λ : ℝ≥0∞) ^ p.toReal * (B : ℝ≥0∞)
            ≤ (Cv Λ : ℝ≥0∞) ^ p.toReal
              * ((((Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card : ℕ) : ℝ≥0∞)
                * (10 : ℝ≥0∞) ^ p.toReal) := by gcongr
          _ = (((Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card : ℕ) : ℝ≥0∞)
              * ((10 : ℝ≥0∞) ^ p.toReal * (Cv Λ : ℝ≥0∞) ^ p.toReal) := by
                rw [mul_assoc, mul_comm ((Cv Λ : ℝ≥0∞) ^ p.toReal), mul_assoc]
          _ = (((Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card : ℕ) : ℝ≥0∞)
              * ((10 : ℝ≥0∞) * (Cv Λ : ℝ≥0∞)) ^ p.toReal := by
                rw [ENNReal.mul_rpow_of_nonneg _ _ hqpos.le]
      calc ((Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card : ℝ≥0∞) * XV ^ p.toReal
          ≤ PV ^ p.toReal := hlow
        _ ≤ (Cv Λ : ℝ≥0∞) ^ p.toReal * (B : ℝ≥0∞) * (eLpNorm f p₁ μ) ^ p.toReal
              * (eLpNorm g p₂ μ) ^ p.toReal := hupq
        _ ≤ (((Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card : ℝ≥0∞)
              * ((10 : ℝ≥0∞) * (Cv Λ : ℝ≥0∞)) ^ p.toReal)
              * (eLpNorm f p₁ μ) ^ p.toReal * (eLpNorm g p₂ μ) ^ p.toReal := by
            gcongr
        _ = ((Finset.Icc (2 * Cfan * M ^ D : ℤ) (4 * Cfan * M ^ D : ℤ)).card : ℝ≥0∞)
              * (((10 : ℝ≥0∞) * (Cv Λ : ℝ≥0∞)) ^ p.toReal
                * (eLpNorm f p₁ μ) ^ p.toReal * (eLpNorm g p₂ μ) ^ p.toReal) := by
            ring
    have hfin : XV ^ p.toReal ≤ ((10 : ℝ≥0∞) * (Cv Λ : ℝ≥0∞)) ^ p.toReal
        * (eLpNorm f p₁ μ) ^ p.toReal * (eLpNorm g p₂ μ) ^ p.toReal :=
      (ENNReal.mul_le_mul_iff_right hcardnn ENNReal.coe_ne_top).mp hcomb
    calc XV = (XV ^ p.toReal) ^ (p.toReal)⁻¹ := (ENNReal.rpow_rpow_inv hqne _).symm
      _ ≤ (((10 : ℝ≥0∞) * (Cv Λ : ℝ≥0∞)) ^ p.toReal * (eLpNorm f p₁ μ) ^ p.toReal
            * (eLpNorm g p₂ μ) ^ p.toReal) ^ (p.toReal)⁻¹ :=
          ENNReal.rpow_le_rpow hfin (by positivity)
      _ = (10 : ℝ≥0∞) * (Cv Λ : ℝ≥0∞) * eLpNorm f p₁ μ * eLpNorm g p₂ μ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
          rw [ENNReal.rpow_rpow_inv hqne, ENNReal.rpow_rpow_inv hqne, ENNReal.rpow_rpow_inv hqne]

  rw [show (fun x : 𝓧 => variationalNorm r (fun n => A T (a n) X P f g x))
      = (fun x => ⨆ K, variationalNorm r (fun n => A T (a (min n K)) X P f g x)) from by
    funext x
    exact variationalNorm_eq_iSup_comp_min r (fun n => A T (a n) X P f g x)]
  exact eLpNorm_iSup_le_of_le hp0 hptop
    (fun K => (measurable_variationalNorm hrpos (fun n => measurable_A T (a (min n K)) X P hf hg)).aemeasurable)
    (fun x => fun i j hij => variationalNorm_comp_min_mono r (fun n => A T (a n) X P f g x) hij)
    hpoint

end PointwiseErgodicTheorems
end Submission
