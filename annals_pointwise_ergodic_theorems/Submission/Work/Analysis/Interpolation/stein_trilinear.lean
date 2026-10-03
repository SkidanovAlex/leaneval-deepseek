/-
Copyright (c) 2026 The Annals formalisation team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.Analysis.Interpolation.BilinearThreeLines
import Submission.Work.Analysis.Interpolation.analyticFamily_eq_sum
import Submission.Work.Analysis.Interpolation.bddAbove_bilinear_family

/-!
# Stein's trilinear interpolation of `Lᵖ` estimates

This module proves the three-variable companion of
`Work.Analysis.Interpolation.stein_bilinear`: **interpolation of a trilinear form**.  If a
trilinear form `Λ` on functions over three measure spaces satisfies the two endpoint estimates

`‖Λ u v w‖ ≤ Mᵢ ‖u‖_{pᵢ} ‖v‖_{qᵢ} ‖w‖_{rᵢ}`   (`i = 0, 1`)

(with extended `Lᵖ` seminorms and *arbitrary* functions `u, v, w`), then for `θ ∈ (0,1)` and the
interpolated exponents

`1/p = (1-θ)/p₀ + θ/p₁`,  `1/q = (1-θ)/q₀ + θ/q₁`,  `1/r = (1-θ)/r₀ + θ/r₁`

one has

`‖Λ f g h‖ ≤ M₀^{1-θ} M₁^θ ‖f‖_p ‖g‖_q ‖h‖_r`

for all *simple* functions `f, g, h`.

The proof is Hadamard's three lines theorem (`Complex.HadamardThreeLines`) applied to the
analytic family

`z ↦ Λ (|f|^{a(z)} f/|f|) (|g|^{b(z)} g/|g|) (|h|^{c(z)} h/|h|)`,

exactly as in the classical proof of Riesz--Thorin and of Stein's multilinear interpolation.  The
only analytic inputs -- entireness of the family, and its boundedness on the closed strip -- are
discharged from the level-set decomposition of the simple functions, using trilinearity of `Λ`
(which reduces the family to a finite sum of exponentials of affine functions of `z`).  No
measurability of `Λ`, no measurability of the test functions, no `σ`-finiteness and no support
hypotheses are needed: the endpoint estimates are assumed for *all* functions, and all `eLpNorm`
computations are pointwise identities of the integrands.

This is the interpolation step used in Krause--Mirek--Tao, *Pointwise ergodic theorems for
non-conventional bilinear polynomial averages*, Annals 195 (2022), §5--§6 and §10, to pass from an
estimate proved for one triple of exponents to the exponents of the application, with the
constants combined log-convexly.

## Main results

* `trilinear_decomposition`: the level-set decomposition of the trilinear pairing of the three
  analytic families;
* `differentiable_trilinear_of_decomposition`, `bddAbove_trilinear_family`: the two analytic
  inputs of the three lines theorem, for an arbitrary trilinear `Λ`;
* `stein_trilinear_of_decomposition`: the three lines argument proper;
* `stein_trilinear`: **Stein's trilinear interpolation theorem**.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Work.Analysis.Interpolation

/-! ## Arithmetic of the interpolated exponents -/

/-- Arithmetic core of the four-factor `rpow` interpolation: for coefficients `m₀, m₁ ≥ 0`,
points `x, y, w > 0` and exponents satisfying `(1-θ) α₀ + θ α₁ = 1`, `(1-θ) β₀ + θ β₁ = 1` and
`(1-θ) γ₀ + θ γ₁ = 1`, the `θ`-interpolated product of the two monomials `mᵢ x^{αᵢ} y^{βᵢ} w^{γᵢ}`
is the interpolated coefficient times `x * y * w`.  This is `rpow_interp_arith` with one further
positive factor. -/
lemma rpow_interp_arith3 {m₀ m₁ x y w α₀ α₁ β₀ β₁ γ₀ γ₁ θ : ℝ} (hm₀ : 0 ≤ m₀) (hm₁ : 0 ≤ m₁)
    (hx : 0 < x) (hy : 0 < y) (hw : 0 < w)
    (hα : (1 - θ) * α₀ + θ * α₁ = 1) (hβ : (1 - θ) * β₀ + θ * β₁ = 1)
    (hγ : (1 - θ) * γ₀ + θ * γ₁ = 1) :
    (m₀ * x ^ α₀ * y ^ β₀ * w ^ γ₀) ^ (1 - θ) * (m₁ * x ^ α₁ * y ^ β₁ * w ^ γ₁) ^ θ
      = m₀ ^ (1 - θ) * m₁ ^ θ * x * y * w := by
  have hxp : ∀ a : ℝ, 0 < x ^ a := fun a => Real.rpow_pos_of_pos hx a
  have hyp : ∀ a : ℝ, 0 < y ^ a := fun a => Real.rpow_pos_of_pos hy a
  have hwp : ∀ a : ℝ, 0 < w ^ a := fun a => Real.rpow_pos_of_pos hw a
  have key : ∀ (m a b c d : ℝ), 0 ≤ m →
      (m * x ^ a * y ^ b * w ^ c) ^ d = m ^ d * x ^ (a * d) * y ^ (b * d) * w ^ (c * d) := by
    intro m a b c d hm
    rw [Real.mul_rpow (mul_nonneg (mul_nonneg hm (hxp a).le) (hyp b).le) (hwp c).le,
        Real.mul_rpow (mul_nonneg hm (hxp a).le) (hyp b).le,
        Real.mul_rpow hm (hxp a).le,
        ← Real.rpow_mul hx.le, ← Real.rpow_mul hy.le, ← Real.rpow_mul hw.le]
  have hxx : x ^ (α₀ * (1 - θ)) * x ^ (α₁ * θ) = x := by
    rw [← Real.rpow_add hx (α₀ * (1 - θ)) (α₁ * θ)]
    have hsum : α₀ * (1 - θ) + α₁ * θ = 1 := by
      rw [mul_comm α₀ (1 - θ), mul_comm α₁ θ]; exact hα
    rw [hsum, Real.rpow_one]
  have hyy : y ^ (β₀ * (1 - θ)) * y ^ (β₁ * θ) = y := by
    rw [← Real.rpow_add hy (β₀ * (1 - θ)) (β₁ * θ)]
    have hsum : β₀ * (1 - θ) + β₁ * θ = 1 := by
      rw [mul_comm β₀ (1 - θ), mul_comm β₁ θ]; exact hβ
    rw [hsum, Real.rpow_one]
  have hww : w ^ (γ₀ * (1 - θ)) * w ^ (γ₁ * θ) = w := by
    rw [← Real.rpow_add hw (γ₀ * (1 - θ)) (γ₁ * θ)]
    have hsum : γ₀ * (1 - θ) + γ₁ * θ = 1 := by
      rw [mul_comm γ₀ (1 - θ), mul_comm γ₁ θ]; exact hγ
    rw [hsum, Real.rpow_one]
  have rearr : m₀ ^ (1 - θ) * x ^ (α₀ * (1 - θ)) * y ^ (β₀ * (1 - θ)) * w ^ (γ₀ * (1 - θ)) *
        (m₁ ^ θ * x ^ (α₁ * θ) * y ^ (β₁ * θ) * w ^ (γ₁ * θ))
      = m₀ ^ (1 - θ) * m₁ ^ θ * (x ^ (α₀ * (1 - θ)) * x ^ (α₁ * θ)) *
        (y ^ (β₀ * (1 - θ)) * y ^ (β₁ * θ)) * (w ^ (γ₀ * (1 - θ)) * w ^ (γ₁ * θ)) := by ring
  rw [key m₀ α₀ β₀ γ₀ (1 - θ) hm₀, key m₁ α₁ β₁ γ₁ θ hm₁, rearr, hxx, hyy, hww]

/-- The `ofReal`/`toReal` conversion of the interpolated constant for three norms: the real
product `m₀^(1-θ) m₁^θ U.toReal V.toReal W.toReal` of finite extended nonnegative reals
corresponds to the extended product `(ofReal m₀)^(1-θ) (ofReal m₁)^θ U V W`. -/
lemma ofReal_arith_convert3 {m₀ m₁ : ℝ} (hm₀ : 0 ≤ m₀) (hm₁ : 0 ≤ m₁) {U V W : ℝ≥0∞}
    (hU : U < ⊤) (hV : V < ⊤) (hW : W < ⊤) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    ENNReal.ofReal (m₀ ^ (1 - θ) * m₁ ^ θ * U.toReal * V.toReal * W.toReal)
      = (ENNReal.ofReal m₀) ^ (1 - θ) * (ENNReal.ofReal m₁) ^ θ * U * V * W := by
  have h1 : ENNReal.ofReal (m₀ ^ (1 - θ) * m₁ ^ θ * U.toReal * V.toReal * W.toReal)
      = ENNReal.ofReal (m₀ ^ (1 - θ)) * ENNReal.ofReal (m₁ ^ θ)
        * ENNReal.ofReal U.toReal * ENNReal.ofReal V.toReal * ENNReal.ofReal W.toReal := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  rw [h1, ENNReal.ofReal_rpow_of_nonneg hm₀ (by linarith),
    ENNReal.ofReal_rpow_of_nonneg hm₁ hθ₀, ENNReal.ofReal_toReal (ne_top_of_lt hU),
    ENNReal.ofReal_toReal (ne_top_of_lt hV), ENNReal.ofReal_toReal (ne_top_of_lt hW)]

/-- `ENNReal.ofReal` of a real power of the `toReal` of a finite extended nonnegative real. -/
private lemma ofReal_toReal_rpow_of_ne_top3 {U : ℝ≥0∞} (hU : U ≠ ⊤) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (U.toReal ^ p) = U ^ p := by
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp, ENNReal.ofReal_toReal hU]

/-- Degenerate case of `ofReal_toReal_const_eq3`: if one of the three extended reals vanishes,
then both sides of the identity vanish (all exponents are positive). -/
private lemma toRealConst_zero3 {m : ℝ} {U V W : ℝ≥0∞} {α β δ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ) (h2 : U = 0 ∨ V = 0 ∨ W = 0) :
    ENNReal.ofReal (m * U.toReal ^ α * V.toReal ^ β * W.toReal ^ δ)
      = ENNReal.ofReal m * U ^ α * V ^ β * W ^ δ := by
  rcases h2 with h | h | h
  · rw [h, ENNReal.toReal_zero]
    simp [Real.zero_rpow (ne_of_gt hα), ENNReal.zero_rpow_of_pos hα]
  · rw [h, ENNReal.toReal_zero]
    simp [Real.zero_rpow (ne_of_gt hβ), ENNReal.zero_rpow_of_pos hβ]
  · rw [h, ENNReal.toReal_zero]
    simp [Real.zero_rpow (ne_of_gt hδ), ENNReal.zero_rpow_of_pos hδ]

/-- For a finite extended nonnegative real `U` and an exponent `α ≥ 0`, the extended power
`U ^ α` is `ENNReal.ofReal` of the ordinary real power of the "real part" `U.toReal`, also in the
presence of two further factors which may be infinite (in which case everything vanishes). -/
private lemma ofReal_toReal_const_eq3 (m : ℝ) (hm : 0 ≤ m) (U V W : ℝ≥0∞) (α β δ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hδ : 0 < δ)
    (hU : U < ⊤ ∨ V = 0 ∨ W = 0) (hV : V < ⊤ ∨ U = 0 ∨ W = 0) (hW : W < ⊤ ∨ U = 0 ∨ V = 0) :
    ENNReal.ofReal (m * U.toReal ^ α * V.toReal ^ β * W.toReal ^ δ)
      = ENNReal.ofReal m * U ^ α * V ^ β * W ^ δ := by
  by_cases hUf : U < ⊤
  · by_cases hVf : V < ⊤
    · by_cases hWf : W < ⊤
      · rw [ENNReal.ofReal_mul
            (mul_nonneg (mul_nonneg hm (Real.rpow_nonneg ENNReal.toReal_nonneg α))
              (Real.rpow_nonneg ENNReal.toReal_nonneg β)),
          ofReal_toReal_const_eq m hm U V α β hα hβ (Or.inl hUf) (Or.inl hVf),
          ofReal_toReal_rpow_of_ne_top3 (ne_top_of_lt hWf) hδ.le]
      · exact toRealConst_zero3 hα hβ hδ (by
          have h : W = ⊤ := eq_top_iff.mpr (not_lt.mp hWf)
          rcases hW with h' | h' | h'
          · exact absurd h' (by rw [h]; exact lt_irrefl ⊤)
          · exact Or.inl h'
          · exact Or.inr (Or.inl h'))
    · exact toRealConst_zero3 hα hβ hδ (by
        have h : V = ⊤ := eq_top_iff.mpr (not_lt.mp hVf)
        rcases hV with h' | h' | h'
        · exact absurd h' (by rw [h]; exact lt_irrefl ⊤)
        · exact Or.inl h'
        · exact Or.inr (Or.inr h'))
  · exact toRealConst_zero3 hα hβ hδ (by
      have h : U = ⊤ := eq_top_iff.mpr (not_lt.mp hUf)
      rcases hU with h' | h' | h'
      · exact absurd h' (by rw [h]; exact lt_irrefl ⊤)
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h'))

/-! ## The level-set decomposition of the trilinear pairing -/

/-- The trilinear pairing of the three analytic families of simple functions, evaluated at the
level sets, is the finite triple sum over the ranges of the simple functions, with `z`-dependent
entire coefficients `phasePow c (expFamily t₀ t₁ z) * phasePow d (expFamily u₀ u₁ z) *
phasePow e (expFamily v₀ v₁ z)` in front of the `z`-independent contributions
`Λ 1_{f⁻¹{c}} 1_{g⁻¹{d}} 1_{h⁻¹{e}}`.  The order of the three sums is the one produced by
pushing `Λ` (as a `LinearMap`, hence additive in each variable) through the three sums. -/
lemma trilinear_decomposition {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (Λ : (α → ℂ) →ₗ[ℂ] (β → ℂ) →ₗ[ℂ] (γ → ℂ) →ₗ[ℂ] ℂ)
    (f : SimpleFunc α ℂ) (g : SimpleFunc β ℂ) (h : SimpleFunc γ ℂ) (t₀ t₁ u₀ u₁ v₀ v₁ : ℂ)
    (z : ℂ) :
    Λ (analyticFamily (f : α → ℂ) t₀ t₁ z) (analyticFamily (g : β → ℂ) u₀ u₁ z)
        (analyticFamily (h : γ → ℂ) v₀ v₁ z)
    = ∑ e ∈ h.range, ∑ d ∈ g.range, ∑ c ∈ f.range,
        (phasePow c (expFamily t₀ t₁ z) * phasePow d (expFamily u₀ u₁ z)
          * phasePow e (expFamily v₀ v₁ z))
        * Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
            (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
            (Set.indicator (h ⁻¹' {e}) (fun _ => (1 : ℂ))) := by
  rw [analyticFamily_eq_sum f t₀ t₁ z, analyticFamily_eq_sum g u₀ u₁ z,
    analyticFamily_eq_sum h v₀ v₁ z]
  simp only [map_sum, LinearMap.map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, mul_assoc]

/-! ## Differentiability of the trilinear family -/

/-- A finite double sum of differentiable functions of `z` is differentiable.  The sum
is over three `Finset`s, and each summand may depend on all three indices and on `z`. -/
lemma differentiable_sum_sum_sum {ι κ o : Type*} (s : Finset ι) (t : Finset κ) (u : Finset o)
    (A : ι → κ → o → ℂ → ℂ)
    (h : ∀ i ∈ s, ∀ j ∈ t, ∀ k ∈ u, Differentiable ℂ (fun z => A i j k z)) :
    Differentiable ℂ (fun z => ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, A i j k z) := by
  have h1 : (fun z => ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, A i j k z)
      = ∑ i ∈ s, (fun z => ∑ j ∈ t, ∑ k ∈ u, A i j k z) := by
    funext z; simp
  rw [h1]
  refine Differentiable.sum fun i hi => ?_
  have h2 : (fun z => ∑ j ∈ t, ∑ k ∈ u, A i j k z)
      = ∑ j ∈ t, (fun z => ∑ k ∈ u, A i j k z) := by
    funext z; simp
  rw [h2]
  refine Differentiable.sum fun j hj => ?_
  have h3 : (fun z => ∑ k ∈ u, A i j k z) = ∑ k ∈ u, (fun z => A i j k z) := by
    funext z; simp
  rw [h3]
  exact Differentiable.sum fun k hk => h i hi j hj k hk

/-- If the trilinear form `Λ` evaluated on the analytic families of three simple functions
decomposes as a finite sum over level sets with coefficients `phasePow c (expFamily t₀ t₁ z) *
phasePow d (expFamily u₀ u₁ z) * phasePow e (expFamily v₀ v₁ z)` times `z`-independent constants,
then `z ↦ Λ (analyticFamily f t₀ t₁ z) (analyticFamily g u₀ u₁ z) (analyticFamily h v₀ v₁ z)`
is entire. -/
lemma differentiable_trilinear_of_decomposition {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (Λ : (α → ℂ) → (β → ℂ) → (γ → ℂ) → ℂ)
    (f : SimpleFunc α ℂ) (g : SimpleFunc β ℂ) (h : SimpleFunc γ ℂ) (t₀ t₁ u₀ u₁ v₀ v₁ : ℂ)
    (hΛ : ∀ z : ℂ,
      Λ (analyticFamily (f : α → ℂ) t₀ t₁ z) (analyticFamily (g : β → ℂ) u₀ u₁ z)
          (analyticFamily (h : γ → ℂ) v₀ v₁ z)
        = ∑ e ∈ h.range, ∑ d ∈ g.range, ∑ c ∈ f.range,
            (phasePow c (expFamily t₀ t₁ z) * phasePow d (expFamily u₀ u₁ z)
              * phasePow e (expFamily v₀ v₁ z))
            * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
                (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
                (Set.indicator (h ⁻¹' {e}) (fun _ => (1 : ℂ))))) :
    Differentiable ℂ fun z : ℂ =>
      Λ (analyticFamily (f : α → ℂ) t₀ t₁ z) (analyticFamily (g : β → ℂ) u₀ u₁ z)
        (analyticFamily (h : γ → ℂ) v₀ v₁ z) := by
  have hF : (fun z : ℂ =>
        Λ (analyticFamily (f : α → ℂ) t₀ t₁ z) (analyticFamily (g : β → ℂ) u₀ u₁ z)
          (analyticFamily (h : γ → ℂ) v₀ v₁ z))
      = fun z : ℂ => ∑ e ∈ h.range, ∑ d ∈ g.range, ∑ c ∈ f.range,
          (phasePow c (expFamily t₀ t₁ z) * phasePow d (expFamily u₀ u₁ z)
            * phasePow e (expFamily v₀ v₁ z))
          * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
              (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
              (Set.indicator (h ⁻¹' {e}) (fun _ => (1 : ℂ)))) := by
    funext z
    exact hΛ z
  rw [hF]
  refine differentiable_sum_sum_sum h.range g.range f.range
    (fun e d c z => (phasePow c (expFamily t₀ t₁ z) * phasePow d (expFamily u₀ u₁ z)
        * phasePow e (expFamily v₀ v₁ z))
      * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
          (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
          (Set.indicator (h ⁻¹' {e}) (fun _ => (1 : ℂ))))) ?_
  intro e _ d _ c _
  exact (((differentiable_phasePow_expFamily c t₀ t₁).mul
      (differentiable_phasePow_expFamily d u₀ u₁)).mul
      (differentiable_phasePow_expFamily e v₀ v₁)).mul (differentiable_const _)

/-! ## Boundedness of the trilinear family on the closed strip -/

/-- Triangle inequality for a finite triple sum. -/
lemma norm_triple_sum_le {ι κ o : Type*} (s : Finset ι) (t : Finset κ) (u : Finset o)
    (T : ι → κ → o → ℂ) (U : ι → κ → o → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ t, ∀ k ∈ u, ‖T i j k‖ ≤ U i j k) :
    ‖∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, T i j k‖ ≤ ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ u, U i j k := by
  refine (norm_sum_le s (fun i => ∑ j ∈ t, ∑ k ∈ u, T i j k)).trans
    (Finset.sum_le_sum fun i hi => ?_)
  refine (norm_sum_le t (fun j => ∑ k ∈ u, T i j k)).trans
    (Finset.sum_le_sum fun j hj => ?_)
  exact (norm_sum_le u (fun k => T i j k)).trans (Finset.sum_le_sum fun k hk => h i hi j hj k hk)

/-- The trilinear family `z ↦ Λ (F z) (G z) (H z)` of three simple functions, with *real*
endpoint exponents, is bounded on the closed vertical strip `0 ≤ re z ≤ 1`, provided it admits
the level-set decomposition: the finite sum of exponentials of affine functions is bounded by the
explicit finite sum of the pointwise bounds `max 1 (max (‖c‖^a₀) (‖c‖^a₁))` of the `phasePow`
factors.  This is the boundedness input of Hadamard's three lines theorem. -/
lemma bddAbove_trilinear_family {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (Λ : (α → ℂ) → (β → ℂ) → (γ → ℂ) → ℂ) (f : SimpleFunc α ℂ)
    (g : SimpleFunc β ℂ) (h : SimpleFunc γ ℂ) (a₀ a₁ b₀ b₁ c₀ c₁ : ℝ)
    (hΛ : ∀ z : ℂ,
      Λ (analyticFamily (f : α → ℂ) (a₀ : ℂ) (a₁ : ℂ) z)
          (analyticFamily (g : β → ℂ) (b₀ : ℂ) (b₁ : ℂ) z)
          (analyticFamily (h : γ → ℂ) (c₀ : ℂ) (c₁ : ℂ) z)
        = ∑ e ∈ h.range, ∑ d ∈ g.range, ∑ c ∈ f.range,
            (phasePow c (expFamily (a₀ : ℂ) (a₁ : ℂ) z)
              * phasePow d (expFamily (b₀ : ℂ) (b₁ : ℂ) z)
              * phasePow e (expFamily (c₀ : ℂ) (c₁ : ℂ) z))
            * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
                (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
                (Set.indicator (h ⁻¹' {e}) (fun _ => (1 : ℂ))))) :
    BddAbove ((norm ∘ fun z : ℂ =>
        Λ (analyticFamily (f : α → ℂ) (a₀ : ℂ) (a₁ : ℂ) z)
          (analyticFamily (g : β → ℂ) (b₀ : ℂ) (b₁ : ℂ) z)
          (analyticFamily (h : γ → ℂ) (c₀ : ℂ) (c₁ : ℂ) z))
      '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  refine bddAbove_image_norm_of_le (M := ∑ e ∈ h.range, ∑ d ∈ g.range, ∑ c ∈ f.range,
    (max 1 (max (‖c‖ ^ a₀) (‖c‖ ^ a₁))) * (max 1 (max (‖d‖ ^ b₀) (‖d‖ ^ b₁)))
      * (max 1 (max (‖e‖ ^ c₀) (‖e‖ ^ c₁)))
      * ‖Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
          (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
          (Set.indicator (h ⁻¹' {e}) (fun _ => (1 : ℂ)))‖) ?_
  intro z hz
  have hzre : z.re ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
  have hterm : ∀ e ∈ h.range, ∀ d ∈ g.range, ∀ c ∈ f.range,
      ‖(phasePow c (expFamily (a₀ : ℂ) (a₁ : ℂ) z)
          * phasePow d (expFamily (b₀ : ℂ) (b₁ : ℂ) z)
          * phasePow e (expFamily (c₀ : ℂ) (c₁ : ℂ) z))
        * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
            (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
            (Set.indicator (h ⁻¹' {e}) (fun _ => (1 : ℂ))))‖
      ≤ (max 1 (max (‖c‖ ^ a₀) (‖c‖ ^ a₁))) * (max 1 (max (‖d‖ ^ b₀) (‖d‖ ^ b₁)))
        * (max 1 (max (‖e‖ ^ c₀) (‖e‖ ^ c₁)))
        * ‖Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
            (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
            (Set.indicator (h ⁻¹' {e}) (fun _ => (1 : ℂ)))‖ := by
    intro e _ d _ c _
    have hc : 0 ≤ max 1 (max (‖c‖ ^ a₀) (‖c‖ ^ a₁)) := le_trans zero_le_one (le_max_left 1 _)
    have hd : 0 ≤ max 1 (max (‖d‖ ^ b₀) (‖d‖ ^ b₁)) := le_trans zero_le_one (le_max_left 1 _)
    have he : 0 ≤ max 1 (max (‖e‖ ^ c₀) (‖e‖ ^ c₁)) := le_trans zero_le_one (le_max_left 1 _)
    simp only [norm_mul]
    exact mul_le_mul
      (mul_le_mul
        (mul_le_mul (norm_phasePow_expFamily_le_of_re_mem hzre)
          (norm_phasePow_expFamily_le_of_re_mem hzre) (norm_nonneg _) hc)
        (norm_phasePow_expFamily_le_of_re_mem hzre)
        (norm_nonneg _) (mul_nonneg hc hd))
      le_rfl (norm_nonneg _) (mul_nonneg (mul_nonneg hc hd) he)
  rw [hΛ z]
  exact norm_triple_sum_le h.range g.range f.range _ _ hterm

/-! ## Stein's trilinear interpolation -/

/-- **Stein's trilinear interpolation, three lines form.**  Given a "trilinear" pairing `Λ` whose
values on the level sets of three simple functions are known, and two endpoint estimates for `Λ`,
the interpolated estimate holds for the simple functions themselves. -/
theorem stein_trilinear_of_decomposition
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {ρ : Measure γ}
    (Λ : (α → ℂ) → (β → ℂ) → (γ → ℂ) → ℂ) (f : SimpleFunc α ℂ) (g : SimpleFunc β ℂ)
    (h : SimpleFunc γ ℂ)
    {p₀ p₁ q₀ q₁ r₀ r₁ p q r θ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 0 < q₀)
    (hq₁ : 0 < q₁) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hpθ : 1 / p = (1 - θ) / p₀ + θ / p₁) (hqθ : 1 / q = (1 - θ) / q₀ + θ / q₁)
    (hrθ : 1 / r = (1 - θ) / r₀ + θ / r₁)
    {M₀ M₁ : ℝ≥0}
    (h₀ : ∀ u v w, ‖Λ u v w‖ₑ ≤ (M₀ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₀) μ
      * eLpNorm v (ENNReal.ofReal q₀) ν * eLpNorm w (ENNReal.ofReal r₀) ρ)
    (h₁ : ∀ u v w, ‖Λ u v w‖ₑ ≤ (M₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₁) μ
      * eLpNorm v (ENNReal.ofReal q₁) ν * eLpNorm w (ENNReal.ofReal r₁) ρ)
    (hΛ : ∀ z : ℂ,
      Λ (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
          (analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
          (analyticFamily (h : γ → ℂ) ((r / r₀ : ℝ) : ℂ) ((r / r₁ : ℝ) : ℂ) z)
        = ∑ e ∈ h.range, ∑ d ∈ g.range, ∑ c ∈ f.range,
            (phasePow c (expFamily ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
              * phasePow d (expFamily ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
              * phasePow e (expFamily ((r / r₀ : ℝ) : ℂ) ((r / r₁ : ℝ) : ℂ) z))
            * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
                (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
                (Set.indicator (h ⁻¹' {e}) (fun _ => (1 : ℂ)))))
    (hB : BddAbove ((norm ∘ fun z : ℂ =>
        Λ (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
          (analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
          (analyticFamily (h : γ → ℂ) ((r / r₀ : ℝ) : ℂ) ((r / r₁ : ℝ) : ℂ) z))
        '' Complex.HadamardThreeLines.verticalClosedStrip 0 1)) :
    ‖Λ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)‖ₑ
      ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ
        * eLpNorm (f : α → ℂ) (ENNReal.ofReal p) μ
        * eLpNorm (g : β → ℂ) (ENNReal.ofReal q) ν
        * eLpNorm (h : γ → ℂ) (ENNReal.ofReal r) ρ := by
  set U : ℝ≥0∞ := eLpNorm (f : α → ℂ) (ENNReal.ofReal p) μ with hUdef
  set V : ℝ≥0∞ := eLpNorm (g : β → ℂ) (ENNReal.ofReal q) ν with hVdef
  set W : ℝ≥0∞ := eLpNorm (h : γ → ℂ) (ENNReal.ofReal r) ρ with hWdef
  set F : ℂ → ℂ := fun z =>
    Λ (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
      (analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
      (analyticFamily (h : γ → ℂ) ((r / r₀ : ℝ) : ℂ) ((r / r₁ : ℝ) : ℂ) z) with hFdef
  -- the trivial cases where one of the constants vanishes
  rcases eq_or_ne M₀ 0 with hM₀ | hM₀
  · have h0 : (M₀ : ℝ≥0∞) = 0 := by rw [hM₀]; rfl
    have hh := h₀ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)
    rw [h0, zero_mul, zero_mul, zero_mul] at hh
    exact le_trans hh bot_le
  rcases eq_or_ne M₁ 0 with hM₁ | hM₁
  · have h1 : (M₁ : ℝ≥0∞) = 0 := by rw [hM₁]; rfl
    have hh := h₁ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)
    rw [h1, zero_mul, zero_mul, zero_mul] at hh
    exact le_trans hh bot_le
  have hM₀pos : (0 : ℝ≥0∞) < (M₀ : ℝ≥0∞) := pos_iff_ne_zero.mpr (by simpa using hM₀)
  have hM₁pos : (0 : ℝ≥0∞) < (M₁ : ℝ≥0∞) := pos_iff_ne_zero.mpr (by simpa using hM₁)
  -- the case where the right-hand side is automatically `⊤`
  by_cases htop : (U = ⊤ ∧ V ≠ 0 ∧ W ≠ 0) ∨ (V = ⊤ ∧ U ≠ 0 ∧ W ≠ 0)
      ∨ (W = ⊤ ∧ U ≠ 0 ∧ V ≠ 0)
  · have hpos₀ : (0 : ℝ≥0∞) < (M₀ : ℝ≥0∞) ^ (1 - θ) :=
      ENNReal.rpow_pos hM₀pos ENNReal.coe_ne_top
    have hpos₁ : (0 : ℝ≥0∞) < (M₁ : ℝ≥0∞) ^ θ :=
      ENNReal.rpow_pos hM₁pos ENNReal.coe_ne_top
    have hpos : (0 : ℝ≥0∞) < (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ :=
      ENNReal.mul_pos (ne_of_gt hpos₀) (ne_of_gt hpos₁)
    have hRHS : (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V * W = ⊤ := by
      rcases htop with ⟨hU, hV, hW⟩ | ⟨hV, hU, hW⟩ | ⟨hW, hU, hV⟩
      · rw [hU, ENNReal.mul_top (ne_of_gt hpos), ENNReal.top_mul hV, ENNReal.top_mul hW]
      · rw [hV, ENNReal.mul_top (mul_ne_zero (ne_of_gt hpos) hU), ENNReal.top_mul hW]
      · rw [hW, ENNReal.mul_top (mul_ne_zero (mul_ne_zero (ne_of_gt hpos) hU) hV)]
    rw [hRHS]
    exact le_top
  have hUopen : U < ⊤ ∨ V = 0 ∨ W = 0 := by
    by_cases hUf : U < ⊤
    · exact Or.inl hUf
    · refine Or.inr ?_
      by_cases hV0 : V = 0
      · exact Or.inl hV0
      · refine Or.inr ?_
        by_contra hW0
        exact htop (Or.inl ⟨eq_top_iff.mpr (not_lt.mp hUf), hV0, hW0⟩)
  have hVopen : V < ⊤ ∨ U = 0 ∨ W = 0 := by
    by_cases hVf : V < ⊤
    · exact Or.inl hVf
    · refine Or.inr ?_
      by_cases hU0 : U = 0
      · exact Or.inl hU0
      · refine Or.inr ?_
        by_contra hW0
        exact htop (Or.inr (Or.inl ⟨eq_top_iff.mpr (not_lt.mp hVf), hU0, hW0⟩))
  have hWopen : W < ⊤ ∨ U = 0 ∨ V = 0 := by
    by_cases hWf : W < ⊤
    · exact Or.inl hWf
    · refine Or.inr ?_
      by_cases hU0 : U = 0
      · exact Or.inl hU0
      · refine Or.inr ?_
        by_contra hV0
        exact htop (Or.inr (Or.inr ⟨eq_top_iff.mpr (not_lt.mp hWf), hU0, hV0⟩))
  -- the analytic inputs
  have hΛraw : ∀ z : ℂ,
      Λ (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
        (analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
        (analyticFamily (h : γ → ℂ) ((r / r₀ : ℝ) : ℂ) ((r / r₁ : ℝ) : ℂ) z)
      = ∑ e ∈ h.range, ∑ d ∈ g.range, ∑ c ∈ f.range,
          (phasePow c (expFamily ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
            * phasePow d (expFamily ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
            * phasePow e (expFamily ((r / r₀ : ℝ) : ℂ) ((r / r₁ : ℝ) : ℂ) z))
          * (Λ (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
              (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
              (Set.indicator (h ⁻¹' {e}) (fun _ => (1 : ℂ)))) := hΛ
  have hFdiff : Differentiable ℂ F := by
    rw [hFdef]
    exact differentiable_trilinear_of_decomposition Λ f g h _ _ _ _ _ _ hΛraw
  -- the boundary estimates
  have hedge0 : ∀ z ∈ Complex.re ⁻¹' {0},
      ‖F z‖ ≤ (M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀)
        * W.toReal ^ (r / r₀) := by
    intro z hz
    have hz' : z.re = 0 := hz
    have h1 : ‖F z‖ₑ ≤ (M₀ : ℝ≥0∞)
        * eLpNorm (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
            (ENNReal.ofReal p₀) μ
        * eLpNorm (analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
            (ENNReal.ofReal q₀) ν
        * eLpNorm (analyticFamily (h : γ → ℂ) ((r / r₀ : ℝ) : ℂ) ((r / r₁ : ℝ) : ℂ) z)
            (ENNReal.ofReal r₀) ρ := by
      rw [hFdef]
      exact h₀ _ _ _
    rw [eLpNorm_analyticFamily_re_zero (μ := μ) hp₀ hp₁ hp hz'
        (aemeasurable_analyticFamily f ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z).aestronglyMeasurable
        f.aestronglyMeasurable,
      eLpNorm_analyticFamily_re_zero (μ := ν) hq₀ hq₁ hq hz'
        (aemeasurable_analyticFamily g ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z).aestronglyMeasurable
        g.aestronglyMeasurable,
      eLpNorm_analyticFamily_re_zero (μ := ρ) hr₀ hr₁ hr hz'
        (aemeasurable_analyticFamily h ((r / r₀ : ℝ) : ℂ) ((r / r₁ : ℝ) : ℂ) z).aestronglyMeasurable
        h.aestronglyMeasurable] at h1
    rw [← hUdef, ← hVdef, ← hWdef] at h1
    have h2 : (M₀ : ℝ≥0∞) * U ^ (p / p₀) * V ^ (q / q₀) * W ^ (r / r₀)
        = ENNReal.ofReal ((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀)
            * W.toReal ^ (r / r₀)) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := M₀),
        ← ofReal_toReal_const_eq3 (M₀ : ℝ) (by positivity) U V W (p / p₀) (q / q₀) (r / r₀)
          (by positivity) (by positivity) (by positivity) hUopen hVopen hWopen]
    rw [h2, ← ofReal_norm] at h1
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  have hedge1 : ∀ z ∈ Complex.re ⁻¹' {1},
      ‖F z‖ ≤ (M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁)
        * W.toReal ^ (r / r₁) := by
    intro z hz
    have hz' : z.re = 1 := hz
    have h1 : ‖F z‖ₑ ≤ (M₁ : ℝ≥0∞)
        * eLpNorm (analyticFamily (f : α → ℂ) ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z)
            (ENNReal.ofReal p₁) μ
        * eLpNorm (analyticFamily (g : β → ℂ) ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z)
            (ENNReal.ofReal q₁) ν
        * eLpNorm (analyticFamily (h : γ → ℂ) ((r / r₀ : ℝ) : ℂ) ((r / r₁ : ℝ) : ℂ) z)
            (ENNReal.ofReal r₁) ρ := by
      rw [hFdef]
      exact h₁ _ _ _
    rw [eLpNorm_analyticFamily_re_one (μ := μ) hp₀ hp₁ hp hz'
        (aemeasurable_analyticFamily f ((p / p₀ : ℝ) : ℂ) ((p / p₁ : ℝ) : ℂ) z).aestronglyMeasurable
        f.aestronglyMeasurable,
      eLpNorm_analyticFamily_re_one (μ := ν) hq₀ hq₁ hq hz'
        (aemeasurable_analyticFamily g ((q / q₀ : ℝ) : ℂ) ((q / q₁ : ℝ) : ℂ) z).aestronglyMeasurable
        g.aestronglyMeasurable,
      eLpNorm_analyticFamily_re_one (μ := ρ) hr₀ hr₁ hr hz'
        (aemeasurable_analyticFamily h ((r / r₀ : ℝ) : ℂ) ((r / r₁ : ℝ) : ℂ) z).aestronglyMeasurable
        h.aestronglyMeasurable] at h1
    rw [← hUdef, ← hVdef, ← hWdef] at h1
    have h2 : (M₁ : ℝ≥0∞) * U ^ (p / p₁) * V ^ (q / q₁) * W ^ (r / r₁)
        = ENNReal.ofReal ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁)
            * W.toReal ^ (r / r₁)) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := M₁),
        ← ofReal_toReal_const_eq3 (M₁ : ℝ) (by positivity) U V W (p / p₁) (q / q₁) (r / r₁)
          (by positivity) (by positivity) (by positivity) hUopen hVopen hWopen]
    rw [h2, ← ofReal_norm] at h1
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  have hhad := norm_le_interp_of_strip_edges hθ₀.le hθ₁.le hFdiff hB hedge0 hedge1
  have hselfp : (1 - (θ : ℂ)) * ((p / p₀ : ℝ) : ℂ) + (θ : ℂ) * ((p / p₁ : ℝ) : ℂ) = 1 :=
    expFamily_interp_self (ne_of_gt hp) hpθ
  have hselfq : (1 - (θ : ℂ)) * ((q / q₀ : ℝ) : ℂ) + (θ : ℂ) * ((q / q₁ : ℝ) : ℂ) = 1 :=
    expFamily_interp_self (ne_of_gt hq) hqθ
  have hselfr : (1 - (θ : ℂ)) * ((r / r₀ : ℝ) : ℂ) + (θ : ℂ) * ((r / r₁ : ℝ) : ℂ) = 1 :=
    expFamily_interp_self (ne_of_gt hr) hrθ
  have hFθ : F (θ : ℂ) = Λ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ) := by
    rw [hFdef]
    simp only [analyticFamily_self hselfp, analyticFamily_self hselfq,
      analyticFamily_self hselfr]
  -- the degenerate cases where one of the three norms vanishes
  rcases eq_or_ne U 0 with hU0 | hU0
  · have ha0 : (M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀) * W.toReal ^ (r / r₀)
        = 0 := by
      rw [hU0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hp hp₀))]; ring
    have hb0 : (M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁) * W.toReal ^ (r / r₁)
        = 0 := by
      rw [hU0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hp hp₁))]; ring
    have hzero : ‖F (θ : ℂ)‖ ≤ 0 := by
      have h := hhad
      rw [ha0, hb0, Real.zero_rpow (ne_of_gt (sub_pos.mpr hθ₁)),
        Real.zero_rpow (ne_of_gt hθ₀), mul_zero] at h
      exact h
    have hRHS : (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V * W = 0 := by
      rw [hU0]; simp
    have : ‖Λ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)‖ₑ ≤ 0 := by
      rw [← hFθ, ← ofReal_norm, ← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_le_ofReal hzero
    rw [hRHS]
    exact this
  rcases eq_or_ne V 0 with hV0 | hV0
  · have ha0 : (M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀) * W.toReal ^ (r / r₀)
        = 0 := by
      rw [hV0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hq hq₀))]; ring
    have hb0 : (M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁) * W.toReal ^ (r / r₁)
        = 0 := by
      rw [hV0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hq hq₁))]; ring
    have hzero : ‖F (θ : ℂ)‖ ≤ 0 := by
      have h := hhad
      rw [ha0, hb0, Real.zero_rpow (ne_of_gt (sub_pos.mpr hθ₁)),
        Real.zero_rpow (ne_of_gt hθ₀), mul_zero] at h
      exact h
    have hRHS : (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V * W = 0 := by
      rw [hV0]; simp
    have : ‖Λ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)‖ₑ ≤ 0 := by
      rw [← hFθ, ← ofReal_norm, ← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_le_ofReal hzero
    rw [hRHS]
    exact this
  rcases eq_or_ne W 0 with hW0 | hW0
  · have ha0 : (M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀) * W.toReal ^ (r / r₀)
        = 0 := by
      rw [hW0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hr hr₀))]; ring
    have hb0 : (M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁) * W.toReal ^ (r / r₁)
        = 0 := by
      rw [hW0, ENNReal.toReal_zero, Real.zero_rpow (ne_of_gt (div_pos hr hr₁))]; ring
    have hzero : ‖F (θ : ℂ)‖ ≤ 0 := by
      have h := hhad
      rw [ha0, hb0, Real.zero_rpow (ne_of_gt (sub_pos.mpr hθ₁)),
        Real.zero_rpow (ne_of_gt hθ₀), mul_zero] at h
      exact h
    have hRHS : (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V * W = 0 := by
      rw [hW0]; simp
    have : ‖Λ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)‖ₑ ≤ 0 := by
      rw [← hFθ, ← ofReal_norm, ← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_le_ofReal hzero
    rw [hRHS]
    exact this
  -- the main case
  have hUpos : 0 < U := pos_iff_ne_zero.mpr hU0
  have hVpos : 0 < V := pos_iff_ne_zero.mpr hV0
  have hWpos : 0 < W := pos_iff_ne_zero.mpr hW0
  have hUfin : U < ⊤ := by
    rcases hUopen with h | h | h
    · exact h
    · exact absurd h hV0
    · exact absurd h hW0
  have hVfin : V < ⊤ := by
    rcases hVopen with h | h | h
    · exact h
    · exact absurd h hU0
    · exact absurd h hW0
  have hWfin : W < ⊤ := by
    rcases hWopen with h | h | h
    · exact h
    · exact absurd h hU0
    · exact absurd h hV0
  have hα : (1 - θ) * (p / p₀) + θ * (p / p₁) = 1 := interp_self (ne_of_gt hp) hpθ
  have hβ : (1 - θ) * (q / q₀) + θ * (q / q₁) = 1 := interp_self (ne_of_gt hq) hqθ
  have hγ : (1 - θ) * (r / r₀) + θ * (r / r₁) = 1 := interp_self (ne_of_gt hr) hrθ
  have harith : ((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀) * W.toReal ^ (r / r₀))
        ^ (1 - θ)
      * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁) * W.toReal ^ (r / r₁)) ^ θ
      = (M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ * U.toReal * V.toReal * W.toReal :=
    rpow_interp_arith3 (by positivity) (by positivity)
      (ENNReal.toReal_pos hU0 (ne_top_of_lt hUfin))
      (ENNReal.toReal_pos hV0 (ne_top_of_lt hVfin))
      (ENNReal.toReal_pos hW0 (ne_top_of_lt hWfin)) hα hβ hγ
  have hconv : ENNReal.ofReal (((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀)
        * W.toReal ^ (r / r₀)) ^ (1 - θ)
      * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁) * W.toReal ^ (r / r₁)) ^ θ)
      = (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V * W := by
    rw [harith,
      ofReal_arith_convert3 (by positivity) (by positivity) hUfin hVfin hWfin hθ₀.le hθ₁.le,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  calc ‖Λ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)‖ₑ
      = ENNReal.ofReal ‖F (θ : ℂ)‖ := by rw [hFθ, ofReal_norm]
    _ ≤ ENNReal.ofReal (((M₀ : ℝ) * U.toReal ^ (p / p₀) * V.toReal ^ (q / q₀)
          * W.toReal ^ (r / r₀)) ^ (1 - θ)
        * ((M₁ : ℝ) * U.toReal ^ (p / p₁) * V.toReal ^ (q / q₁) * W.toReal ^ (r / r₁)) ^ θ) :=
        ENNReal.ofReal_le_ofReal hhad
    _ = (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * U * V * W := hconv

/-- **Stein's trilinear interpolation theorem.**  If a trilinear form satisfies the two endpoint
estimates `‖Λ u v w‖ ≤ Mᵢ ‖u‖_{pᵢ} ‖v‖_{qᵢ} ‖w‖_{rᵢ}` (`i = 0, 1`) for *all* functions, then the
interpolated estimate holds for simple functions, with the exponents interpolated reciprocally and
the constants combined log-convexly. -/
theorem stein_trilinear {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} {ρ : Measure γ} (Λ : (α → ℂ) →ₗ[ℂ] (β → ℂ) →ₗ[ℂ] (γ → ℂ) →ₗ[ℂ] ℂ) {p₀ p₁ q₀ q₁ r₀ r₁ p q r θ : ℝ} (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hq₀ : 0 < q₀) (hq₁ : 0 < q₁) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hpθ : 1 / p = (1 - θ) / p₀ + θ / p₁) (hqθ : 1 / q = (1 - θ) / q₀ + θ / q₁) (hrθ : 1 / r = (1 - θ) / r₀ + θ / r₁) {M₀ M₁ : ℝ≥0} (h₀ : ∀ f g h, ‖Λ f g h‖ₑ ≤ (M₀ : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p₀) μ * eLpNorm g (ENNReal.ofReal q₀) ν * eLpNorm h (ENNReal.ofReal r₀) ρ) (h₁ : ∀ f g h, ‖Λ f g h‖ₑ ≤ (M₁ : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p₁) μ * eLpNorm g (ENNReal.ofReal q₁) ν * eLpNorm h (ENNReal.ofReal r₁) ρ) (f : SimpleFunc α ℂ) (g : SimpleFunc β ℂ) (h : SimpleFunc γ ℂ) : ‖Λ (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ)‖ₑ ≤ (M₀ : ℝ≥0∞) ^ (1 - θ) * (M₁ : ℝ≥0∞) ^ θ * eLpNorm (f : α → ℂ) (ENNReal.ofReal p) μ * eLpNorm (g : β → ℂ) (ENNReal.ofReal q) ν * eLpNorm (h : γ → ℂ) (ENNReal.ofReal r) ρ := by
  refine stein_trilinear_of_decomposition (fun u v w => Λ u v w) f g h hp₀ hp₁ hq₀ hq₁ hr₀ hr₁
    hp hq hr hθ₀ hθ₁ hpθ hqθ hrθ h₀ h₁ ?_ ?_
  · intro z
    exact trilinear_decomposition Λ f g h _ _ _ _ _ _ z
  · exact bddAbove_trilinear_family (fun u v w => Λ u v w) f g h _ _ _ _ _ _
      (fun z => trilinear_decomposition Λ f g h _ _ _ _ _ _ z)

end Work.Analysis.Interpolation
