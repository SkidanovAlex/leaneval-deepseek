import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.Hfun_le_of_large
import Submission.Work.GM.Affine.summable_int_inv_one_add_abs_pow

/-!
# GM §9: a finite window mass is dominated by the total window mass `WinMass`

For `f : ℝ → ℝ` (continuous, with Fourier decay of power type `(T/|ξ|)^j`), the total window mass

`WinMass f M₂ M₃ = ∑' ℓ : ℤ, ∫ τ in [-2,2], ‖H_ℓ(τ)‖²`,  `H_ℓ(τ) = Hfun f M₂ M₃ ℓ τ`

is an honest real number: the family `ℓ ↦ ∫_{[-2,2]} ‖H_ℓ(τ)‖²` is summable.  Consequently any
finite sub-sum is bounded by it:

`∑_{ℓ ∈ s} ∫_{[-2,2]} ‖H_ℓ(τ)‖² dτ ≤ WinMass f M₂ M₃`.

This is the step in the region-II reduction (GM §9) that allows a *finite* set of resonant
frequencies `ℓ` to be compared with the *full* lattice sum; it is used in
`Work.GM.Affine.region_II_reduction`.

## Proof

Summability is read off from the decay hypothesis at `(j, ε) = (3, 1)`.  For `|ℓ| ≥ 4` and
`τ ∈ [-2,2]`, every `m₂ ∈ R2 M₂` satisfies `m₂ ≥ 1`, so `m₂ (ℓ + τ/M₃) ≠ 0`, and the triangle
inequality gives `|ℓ + τ/M₃| ≥ |ℓ|/2`, hence `|m₂ (ℓ + τ/M₃)| ≥ |ℓ|/2`.  With
`D = max (c 3 1 * Λ) 0` the decay hypothesis yields

`‖F̂f (m₂ (ℓ+τ/M₃))‖ ≤ D · T · (T / |m₂(ℓ+τ/M₃)|)³ ≤ 8 D T⁴ / |ℓ|³`,

so with `B = ∑_{m₂ ∈ R2 M₂} m₂` the sum defining `H_ℓ` is bounded by

`‖H_ℓ(τ)‖ ≤ B · 8 D T⁴ / |ℓ|³ =: Kc / |ℓ|³`   (`|ℓ| ≥ 4`, `τ ∈ [-2,2]`).

Integrating the square over an interval of length `4` and comparing `|ℓ|` with `1 + |ℓ|`
gives `∫_{[-2,2]} ‖H_ℓ‖² ≤ 256 Kc² / (1+|ℓ|)⁶`, and `∑_{ℓ ∈ ℤ} 1/(1+|ℓ|)⁶ < ∞`
(`summable_int_inv_one_add_abs_pow`).  `Summable.of_norm_bounded_eventually` then gives
summability away from the finitely many `|ℓ| ≤ 3`; finally a finite partial sum of a summable
nonnegative family is at most the total sum (`Summable.sum_le_tsum`).

Note that no support, nonnegativity or integrability hypothesis on `f` is needed: the finitely
many exceptional `ℓ` with `|ℓ| ≤ 3` are absorbed by `Summable.of_norm_bounded_eventually`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- A nonnegative function bounded by `D` on `[-2,2]` has integral at most `4 * D` there.
No measurability of `F` is needed: `integral_mono_of_nonneg` asks only for the pointwise
domination and for nonnegativity. -/
private lemma window_setIntegral_Icc_le_of_bound (F : ℝ → ℝ) (D : ℝ)
    (hF : ∀ τ ∈ Set.Icc (-2:ℝ) 2, F τ ≤ D) (hFnn : ∀ τ, 0 ≤ F τ) :
    (∫ τ in Set.Icc (-2:ℝ) 2, F τ) ≤ 4 * D := by
  have hs : MeasurableSet (Set.Icc (-2:ℝ) 2) := measurableSet_Icc
  have hgi : Integrable (fun _ : ℝ => D)
      (Measure.restrict (volume : Measure ℝ) (Set.Icc (-2:ℝ) 2)) := by
    have hvol : (volume : Measure ℝ) (Set.Icc (-2:ℝ) 2) ≠ ⊤ := by
      rw [Real.volume_Icc]; simp
    exact integrableOn_const hvol (by simp)
  have hD' : F ≤ᵐ[Measure.restrict (volume : Measure ℝ) (Set.Icc (-2:ℝ) 2)] (fun _ => D) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' hs]
    exact Filter.Eventually.of_forall (fun x hx => hF x hx)
  have hmain := integral_mono_of_nonneg
    (μ := Measure.restrict (volume : Measure ℝ) (Set.Icc (-2:ℝ) 2))
    (f := F) (g := fun _ => D) (Filter.Eventually.of_forall hFnn) hgi hD'
  have hconst : ∫ τ in Set.Icc (-2:ℝ) 2, (D:ℝ) = 4 * D := by
    rw [setIntegral_const, Measure.real, Real.volume_Icc]
    norm_num
  rwa [hconst] at hmain

/-- **A finite window mass is at most the total window mass**
`WinMass f M₂ M₃ = ∑' ℓ, ∫_{[-2,2]} ‖H_ℓ(τ)‖² dτ`.

The mathematical content is the summability of `ℓ ↦ ∫_{[-2,2]} ‖H_ℓ(τ)‖² dτ`, which follows
from the Fourier decay hypothesis `hdec` used at `j = 3`, `ε = 1`; a finite partial sum of a
summable nonnegative family is then at most the total sum. -/
theorem window_mass_le_WinMass {c : ℕ → ℝ → ℝ} {T Λ : ℝ} (hT : 1 ≤ T)
    {M₂ M₃ : ℝ} (hM₂ : 0 < M₂) (hM₃ : 1 ≤ M₃) {f : ℝ → ℝ} (hf : Continuous f)
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ)
    (s : Finset ℤ) :
    ∑ ℓ ∈ s, ∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖^2 ≤ WinMass f M₂ M₃ := by
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  set B : ℝ := ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) with hB
  set γ : ℝ := max (c 3 1 * Λ) 0 with hγ
  set Kc : ℝ := B * (8 * γ * T ^ 4) with hKc
  have hBnn : 0 ≤ B := by
    rw [hB]
    apply Finset.sum_nonneg
    intro m₂ hm₂
    have h1 : (1:ℤ) ≤ m₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm₂).1).1
    have h1' : (1:ℝ) ≤ (m₂:ℝ) := by exact_mod_cast h1
    linarith
  -- pointwise bound for `|ℓ| ≥ 4`, from the decay hypothesis at `(j, ε) = (3, 1)`
  have hpoint : ∀ (ℓ : ℤ), 4 ≤ |ℓ| → ∀ (τ : ℝ), τ ∈ Set.Icc (-2:ℝ) 2 →
      ‖Hfun f M₂ M₃ ℓ τ‖ ≤ Kc / (((|ℓ|:ℤ)):ℝ)^3 := by
    intro ℓ hℓ τ hτ
    have h := Hfun_le_of_large (M₂ := M₂) (M₃ := M₃) hT hM₂ hM₃ hdec ℓ hℓ τ hτ
    rw [hKc, hB, hγ]
    exact h
  -- integrating the square over `[-2,2]` and comparing with `(1+|ℓ|)^{-6}`
  have hcomp : ∀ ℓ : ℤ, 4 ≤ |ℓ| →
      (∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖^2)
        ≤ 256 * Kc^2 / (1 + |((ℓ:ℤ):ℝ)|)^6 := by
    intro ℓ hℓ
    have hL1 : (1:ℝ) ≤ (((|ℓ|:ℤ)):ℝ) := by
      have h : (4:ℝ) ≤ (((|ℓ|:ℤ)):ℝ) := by exact_mod_cast hℓ
      linarith
    have h1 : (∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖^2)
        ≤ 4 * (Kc / (((|ℓ|:ℤ)):ℝ)^3)^2 := by
      refine window_setIntegral_Icc_le_of_bound (fun τ => ‖Hfun f M₂ M₃ ℓ τ‖^2)
        ((Kc / (((|ℓ|:ℤ)):ℝ)^3)^2) ?_ ?_
      · intro τ hτ
        exact pow_le_pow_left₀ (norm_nonneg _) (hpoint ℓ hℓ τ hτ) (2:ℕ)
      · intro τ; exact sq_nonneg _
    have h2 : 4 * (Kc / (((|ℓ|:ℤ)):ℝ)^3)^2 ≤ 256 * Kc^2 / (1 + (((|ℓ|:ℤ)):ℝ))^6 := by
      have hp : (1 + (((|ℓ|:ℤ)):ℝ))^6 ≤ 64 * (((|ℓ|:ℤ)):ℝ)^6 := by
        calc (1 + (((|ℓ|:ℤ)):ℝ))^6 ≤ (2 * (((|ℓ|:ℤ)):ℝ))^6 :=
              pow_le_pow_left₀ (by linarith) (by linarith) (6:ℕ)
          _ = 64 * (((|ℓ|:ℤ)):ℝ)^6 := by ring
      have hmul : 4 * Kc^2 * (1 + (((|ℓ|:ℤ)):ℝ))^6 ≤ 256 * Kc^2 * (((|ℓ|:ℤ)):ℝ)^6 := by
        calc 4 * Kc^2 * (1 + (((|ℓ|:ℤ)):ℝ))^6 ≤ 4 * Kc^2 * (64 * (((|ℓ|:ℤ)):ℝ)^6) :=
              mul_le_mul_of_nonneg_left hp (by positivity)
          _ = 256 * Kc^2 * (((|ℓ|:ℤ)):ℝ)^6 := by ring
      rw [div_pow, show ((((|ℓ|:ℤ)):ℝ)^3)^2 = (((|ℓ|:ℤ)):ℝ)^6 by ring]
      rw [show 4 * (Kc^2 / (((|ℓ|:ℤ)):ℝ)^6) = 4 * Kc^2 / (((|ℓ|:ℤ)):ℝ)^6 by ring_nf]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      exact hmul
    rw [← Int.cast_abs]
    linarith
  -- the comparison family is summable
  have hGsum : Summable (fun ℓ : ℤ => 256 * Kc^2 / (1 + |((ℓ:ℤ):ℝ)|)^6) := by
    have h := (summable_int_inv_one_add_abs_pow 6 (by norm_num)).mul_left (256 * Kc^2)
    refine h.congr (fun ℓ => ?_)
    ring
  -- the bound holds for all but finitely many `ℓ`
  have hev : ∀ᶠ ℓ : ℤ in Filter.cofinite,
      ‖(∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖^2)‖
        ≤ 256 * Kc^2 / (1 + |((ℓ:ℤ):ℝ)|)^6 := by
    rw [Filter.eventually_cofinite]
    have hfin : ({ℓ : ℤ | ¬ (4 ≤ |ℓ|)}).Finite := by
      refine Set.Finite.subset (Finset.finite_toSet (Finset.Icc (-3:ℤ) 3)) ?_
      intro ℓ hℓ
      simp only [Set.mem_ofPred_eq] at hℓ
      simp only [Finset.mem_coe, Finset.mem_Icc]
      have h3 : |ℓ| ≤ 3 := by omega
      exact abs_le.mp h3
    refine Set.Finite.subset hfin ?_
    intro ℓ hℓ
    simp only [Set.mem_ofPred_eq] at hℓ ⊢
    intro h4
    have hnn : 0 ≤ ∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖^2 :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall (fun τ => sq_nonneg _))
    refine hℓ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hcomp ℓ h4
  have hsummable : Summable (fun ℓ : ℤ => ∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖^2) :=
    Summable.of_norm_bounded_eventually hGsum hev
  have hnn2 : ∀ i ∉ s, 0 ≤ (∫ τ in Set.Icc (-2:ℝ) 2, ‖Hfun f M₂ M₃ i τ‖^2) := fun i _ =>
    integral_nonneg_of_ae (Filter.Eventually.of_forall (fun τ => sq_nonneg _))
  have key := hsummable.sum_le_tsum s hnn2
  simpa only [WinMass] using key

end

end Work.GM.Affine
