/-
Copyright: work module for the Elgindi finite-time singularity project.

# `odd_powers_complete`, corrected: measurability of `g` is *required*

The statement requested at `Submission/Work/FTS/PhiStar/Gegenbauer/odd_powers_complete.lean`,

```
theorem odd_powers_complete {g : ℝ → ℝ}
    (hg : IntegrableOn (fun u => g u ^ 2 * √(1 - u ^ 2)) (Set.Icc 0 1))
    (h : ∀ k : ℕ, (∫ u in (0 : ℝ)..1, g u * u ^ (2 * k + 1) * √(1 - u ^ 2)) = 0) :
    g =ᵐ[volume.restrict (Set.Icc 0 1)] 0
```

is **false as written**, and the reason is a missing hypothesis, not a missing piece of library.

* `Integrable f μ` (Mathlib) is `AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ`, so `hg` only
  forces `u ↦ g u ^ 2 * √(1 - u ^ 2)` to be a.e. strongly measurable.  `g` itself need *not* be:
  for a non-Lebesgue-measurable set `A ⊆ (0,1)` the function `g = 1_A - 1_{Aᶜ}` has `g ^ 2 = 1`
  everywhere, so `hg` holds, while `g` is not a.e. strongly measurable.
* The Bochner integral is `0` on functions that are not a.e. strongly measurable
  (`MeasureTheory.integral_non_aestronglyMeasurable`,
  `intervalIntegral.integral_non_aestronglyMeasurable`).  The integrands
  `u ↦ g u * u ^ (2k+1) * √(1 - u ^ 2)` of the hypotheses `h k` are *not* a.e. strongly measurable
  for that `g` (dividing by the a.e.-positive factor `u ^ (2k+1) * √(1 - u ^ 2)` would make `g`
  a.e. strongly measurable).  Hence every hypothesis `h k` holds *vacuously*, while the conclusion
  fails, since `{u | g u ≠ 0} = [0,1]` has measure one.  (Non-measurable sets do exist in this
  foundational setting: `MeasurableSpace.cardinal_measurableSet_le_continuum` shows that the Borel
  σ-algebra of `ℝ` has cardinality at most `𝔠 < 2 ^ 𝔠`.)

This module proves the corrected statement, with the missing a.e.-measurability made explicit.
That form is the honest version of the "Jacobi-density input" recorded in
`NOTES_bslOp_sol_exists.md` §1 — the completeness of the odd powers `u ^ (2k+1)` in
`L²((0,1), √(1-u²) du)` — and it is *equivalent* to the requested statement for measurable `g`.

The proof is the natural one.  Substituting `u = cos θ` (so that `√(1-u²) du = sin²θ dθ`) turns
the odd moments of `g` into `∫_{Jθ} (g (cos θ) sin θ) · cos θ ^ (2k+1) · sin θ dθ = 0`; Chebyshev's
`U`-identity writes `sin (2mθ) = 2 cos θ sin θ · U_{m-1} (cos 2θ)` as a linear combination of
those test functions, so `A = cosMul g` is orthogonal to *every* sine mode `sin (2mθ)`; the
already-proved completeness of the sine system on `Iθ` (`Work.FTS.EllipticEst.sin_system_complete`)
then gives `A =ᵐ 0`, and undoing the substitution yields `∫₀¹ g u ^ 2 √(1-u²) du = 0`, whence
`g = 0` a.e.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.sin2_parseval_aesm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open MeasureTheory
open Polynomial

namespace Work.FTS.PhiStar.Gegenbauer

/-- The interval `[0, π/2]` on which the substitution `u = cos θ` is taken. -/
abbrev Jθ : Set ℝ := Set.Icc 0 (Real.pi / 2)

/-- The substituted function `θ ↦ g (cos θ) · sin θ`. -/
def cosMul (g : ℝ → ℝ) : ℝ → ℝ := fun θ => g (Real.cos θ) * Real.sin θ

/-- `Real.cos` maps `[0, π/2]` onto `[0,1]`. -/
theorem cos_image_Icc_pi_div_two : Real.cos '' Jθ = Set.Icc 0 1 := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩, Real.cos_le_one x⟩
  · have h := intermediate_value_Icc' (a := 0) (b := Real.pi / 2) (by linarith [Real.pi_pos])
      (f := Real.cos) Real.continuous_cos.continuousOn
    rw [Real.cos_zero, Real.cos_pi_div_two] at h
    exact h

/-- `Real.cos` is injective on `[0, π/2]`, so the change of variables `u = cos θ` is legitimate. -/
theorem cos_injOn_Jθ : Set.InjOn Real.cos Jθ :=
  Real.strictAntiOn_cos.injOn.mono (by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)

/-- The derivative datum for the change of variables `u = cos θ` on `[0, π/2]`. -/
theorem hasDerivWithinAt_cos_Jθ :
    ∀ x ∈ Jθ, HasDerivWithinAt Real.cos (-Real.sin x) Jθ x :=
  fun x _ => (Real.hasDerivAt_cos x).hasDerivWithinAt

/-- Pointwise `√(1 - cos θ ^ 2) = sin θ` on `[0, π/2]`. -/
theorem sqrt_one_sub_cos_sq {θ : ℝ} (hθ : θ ∈ Jθ) :
    Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have h1 : 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
  rw [h1, Real.sqrt_sq hsin]

/-- **Change of variables, moments.**  The odd moments of `g` become moments of `cosMul g`
against `cos θ ^ (2k+1) sin θ`. -/
theorem moment_cos_subst {g : ℝ → ℝ}
    (h : ∀ k : ℕ, (∫ u in (0 : ℝ)..1, g u * u ^ (2 * k + 1) * Real.sqrt (1 - u ^ 2)) = 0)
    (k : ℕ) :
    ∫ θ in Jθ, cosMul g θ * (Real.cos θ ^ (2 * k + 1) * Real.sin θ) = 0 := by
  have hΦ : ∫ u in Set.Icc 0 1, g u * u ^ (2 * k + 1) * Real.sqrt (1 - u ^ 2) = 0 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc (x := 0) (y := 1),
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact h k
  have key := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Jθ) (f := Real.cos) (f' := fun x => -Real.sin x)
    measurableSet_Icc hasDerivWithinAt_cos_Jθ cos_injOn_Jθ
    (fun u => g u * u ^ (2 * k + 1) * Real.sqrt (1 - u ^ 2))
  have hpt : ∀ θ ∈ Jθ,
      |-Real.sin θ| • (g (Real.cos θ) * Real.cos θ ^ (2 * k + 1) * Real.sqrt (1 - Real.cos θ ^ 2))
        = cosMul g θ * (Real.cos θ ^ (2 * k + 1) * Real.sin θ) := by
    intro θ hθ
    have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    rw [sqrt_one_sub_cos_sq hθ, abs_neg, abs_of_nonneg hsin, smul_eq_mul]
    simp only [cosMul]
    ring
  have hkey2 : ∫ x in Jθ,
        |-Real.sin x| • (g (Real.cos x) * Real.cos x ^ (2 * k + 1) * Real.sqrt (1 - Real.cos x ^ 2))
      = ∫ x in Jθ, cosMul g x * (Real.cos x ^ (2 * k + 1) * Real.sin x) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpt
  rw [← hkey2, ← key, cos_image_Icc_pi_div_two]
  exact hΦ

/-- **Change of variables, `L²`.**  `cosMul g` is square-integrable on `Jθ` as soon as
`u ↦ g u ^ 2 √(1-u²)` is integrable on `[0,1]`. -/
theorem integrableOn_cosMul_sq {g : ℝ → ℝ}
    (hg : IntegrableOn (fun u => g u ^ 2 * Real.sqrt (1 - u ^ 2)) (Set.Icc 0 1)) :
    IntegrableOn (fun θ => cosMul g θ ^ 2) Jθ := by
  have h := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Jθ) (f := Real.cos) (f' := fun x => -Real.sin x)
    measurableSet_Icc hasDerivWithinAt_cos_Jθ cos_injOn_Jθ
    (fun u => g u ^ 2 * Real.sqrt (1 - u ^ 2))).mp (by rwa [cos_image_Icc_pi_div_two])
  refine (MeasureTheory.integrableOn_congr_fun ?_ measurableSet_Icc).mp h
  intro θ hθ
  show |-Real.sin θ| • (g (Real.cos θ) ^ 2 * Real.sqrt (1 - Real.cos θ ^ 2)) = cosMul g θ ^ 2
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  rw [sqrt_one_sub_cos_sq hθ, abs_neg, abs_of_nonneg hsin, smul_eq_mul]
  simp only [cosMul]
  ring

/-- **Change of variables, integrated form.**  The `L²`-norms match. -/
theorem sq_integral_subst {g : ℝ → ℝ} :
    ∫ θ in Jθ, cosMul g θ ^ 2 = ∫ u in Set.Icc 0 1, g u ^ 2 * Real.sqrt (1 - u ^ 2) := by
  have key := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Jθ) (f := Real.cos) (f' := fun x => -Real.sin x)
    measurableSet_Icc hasDerivWithinAt_cos_Jθ cos_injOn_Jθ
    (fun u => g u ^ 2 * Real.sqrt (1 - u ^ 2))
  have hpt : ∀ θ ∈ Jθ, cosMul g θ ^ 2
      = |-Real.sin θ| • (g (Real.cos θ) ^ 2 * Real.sqrt (1 - Real.cos θ ^ 2)) := by
    intro θ hθ
    have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    rw [sqrt_one_sub_cos_sq hθ, abs_neg, abs_of_nonneg hsin, smul_eq_mul]
    simp only [cosMul]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpt, ← key, cos_image_Icc_pi_div_two]

/-- `cosMul g ∈ L²(Jθ)` for measurable `g` with `∫₀¹ g² √(1-u²) < ∞`. -/
theorem memLp_cosMul {g : ℝ → ℝ}
    (hg : IntegrableOn (fun u => g u ^ 2 * Real.sqrt (1 - u ^ 2)) (Set.Icc 0 1))
    (hgm : Measurable g) :
    MemLp (cosMul g) 2 (MeasureTheory.volume.restrict Jθ) := by
  have hmeas : AEStronglyMeasurable (cosMul g) (MeasureTheory.volume.restrict Jθ) :=
    ((hgm.comp Real.measurable_cos).mul Real.continuous_sin.measurable).aestronglyMeasurable
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas]
  refine (MeasureTheory.integrable_congr (Filter.Eventually.of_forall ?_)).mp
    (integrableOn_cosMul_sq hg)
  intro θ
  show cosMul g θ ^ 2 = ‖cosMul g θ‖ ^ 2
  rw [Real.norm_eq_abs, sq_abs]

/-- **Chebyshev `U`-identity, summed.**  For every `m`,
`sin (2 m θ)` is the combination `∑ j, 2 c j · (cos θ ^ (2j+1) sin θ)` of the test functions of
`moment_cos_subst`, with `c` the coefficients of the polynomial `U_{m-1} (2 X - 1)`. -/
theorem sin_two_mul_coeff_sum (m : ℕ) (θ : ℝ) :
    Real.sin (2 * m * θ) =
      ∑ j ∈ ((Polynomial.Chebyshev.U ℝ ((m : ℤ) - 1)).comp
          (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)).support,
        (2 * (((Polynomial.Chebyshev.U ℝ ((m : ℤ) - 1)).comp
          (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)).coeff j)) *
          (Real.cos θ ^ (2 * j + 1) * Real.sin θ) := by
  set P : ℝ[X] := (Polynomial.Chebyshev.U ℝ ((m : ℤ) - 1)).comp
    (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) with hP
  have hQ : ((Polynomial.C 2 * Polynomial.X - Polynomial.C 1 : ℝ[X])).eval (Real.cos θ ^ 2)
      = Real.cos (2 * θ) := by
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_ofNat]
    linarith [Real.cos_two_mul θ]
  have hUeval : Polynomial.eval (Real.cos (2 * θ)) (Polynomial.Chebyshev.U ℝ ((m : ℤ) - 1))
      = P.eval (Real.cos θ ^ 2) := by
    rw [hP, Polynomial.eval_comp, hQ]
  have hU : Polynomial.eval (Real.cos (2 * θ)) (Polynomial.Chebyshev.U ℝ ((m : ℤ) - 1))
      * Real.sin (2 * θ) = Real.sin (2 * m * θ) := by
    have h := Polynomial.Chebyshev.U_real_cos (2 * θ) ((m : ℤ) - 1)
    have hcast : ((((m : ℤ) - 1 : ℤ)) : ℝ) + 1 = (m : ℝ) := by push_cast; ring
    rw [hcast] at h
    have harg : (m : ℝ) * (2 * θ) = 2 * (m : ℝ) * θ := by ring
    rw [harg] at h
    exact h
  have hPval : P.eval (Real.cos θ ^ 2) = ∑ j ∈ P.support, P.coeff j * Real.cos θ ^ (2 * j) := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [← pow_mul]
  calc Real.sin (2 * m * θ)
      = Polynomial.eval (Real.cos (2 * θ)) (Polynomial.Chebyshev.U ℝ ((m : ℤ) - 1))
          * Real.sin (2 * θ) := hU.symm
    _ = P.eval (Real.cos θ ^ 2) * (2 * Real.sin θ * Real.cos θ) := by
        rw [hUeval, Real.sin_two_mul]
    _ = (∑ j ∈ P.support, P.coeff j * Real.cos θ ^ (2 * j))
          * (2 * Real.sin θ * Real.cos θ) := by rw [hPval]
    _ = ∑ j ∈ P.support, (2 * P.coeff j) * (Real.cos θ ^ (2 * j + 1) * Real.sin θ) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring

/-- Orthogonality of `cosMul g` to every sine mode `sin (2mθ)`, `m ≥ 1`. -/
theorem sin_moment_zero {g : ℝ → ℝ}
    (hg : IntegrableOn (fun u => g u ^ 2 * Real.sqrt (1 - u ^ 2)) (Set.Icc 0 1))
    (hgm : Measurable g)
    (h : ∀ k : ℕ, (∫ u in (0 : ℝ)..1, g u * u ^ (2 * k + 1) * Real.sqrt (1 - u ^ 2)) = 0)
    (m : ℕ) :
    ∫ θ in Jθ, cosMul g θ * Real.sin (2 * (m : ℝ) * θ) = 0 := by
  set P : ℝ[X] := (Polynomial.Chebyshev.U ℝ ((m : ℤ) - 1)).comp
    (Polynomial.C 2 * Polynomial.X - Polynomial.C 1) with hP
  have hAint : Integrable (cosMul g) (MeasureTheory.volume.restrict Jθ) :=
    (memLp_cosMul hg hgm).integrable (by norm_num)
  have hint : ∀ j ∈ P.support,
      Integrable (fun θ => (2 * P.coeff j) *
        (cosMul g θ * (Real.cos θ ^ (2 * j + 1) * Real.sin θ)))
        (MeasureTheory.volume.restrict Jθ) := by
    intro j _
    refine Integrable.const_mul ?_ _
    refine hAint.mul_bdd (by fun_prop) (c := 1) (Filter.Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    calc |Real.cos θ| ^ (2 * j + 1) * |Real.sin θ| ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one θ))
            (Real.abs_sin_le_one θ) (abs_nonneg _) zero_le_one
      _ = 1 := by norm_num
  calc ∫ θ in Jθ, cosMul g θ * Real.sin (2 * (m : ℝ) * θ)
      = ∫ θ in Jθ, cosMul g θ * (∑ j ∈ P.support, (2 * P.coeff j) *
            (Real.cos θ ^ (2 * j + 1) * Real.sin θ)) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
        rw [sin_two_mul_coeff_sum m θ]
    _ = ∫ θ in Jθ, ∑ j ∈ P.support, (2 * P.coeff j) *
            (cosMul g θ * (Real.cos θ ^ (2 * j + 1) * Real.sin θ)) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j ∈ P.support, (2 * P.coeff j) *
          ∫ θ in Jθ, cosMul g θ * (Real.cos θ ^ (2 * j + 1) * Real.sin θ) := by
        rw [MeasureTheory.integral_finsetSum _ (fun j hj => hint j hj)]
        exact Finset.sum_congr rfl fun j _ => by
          rw [MeasureTheory.integral_const_mul]
    _ = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [show (∫ θ in Jθ, cosMul g θ * (Real.cos θ ^ (2 * j + 1) * Real.sin θ)) = 0 from
          moment_cos_subst h j, mul_zero]

/-- **Completeness of the odd powers, corrected form (measurable `g`).** -/
theorem odd_powers_complete_of_measurable {g : ℝ → ℝ}
    (hg : IntegrableOn (fun u => g u ^ 2 * Real.sqrt (1 - u ^ 2)) (Set.Icc 0 1))
    (hgm : Measurable g)
    (h : ∀ k : ℕ, (∫ u in (0 : ℝ)..1, g u * u ^ (2 * k + 1) * Real.sqrt (1 - u ^ 2)) = 0) :
    g =ᵐ[MeasureTheory.volume.restrict (Set.Icc 0 1)] 0 := by
  have hmem : MemLp (cosMul g) 2 (MeasureTheory.volume.restrict Jθ) := memLp_cosMul hg hgm
  have hsin : ∀ n : ℕ,
      ∫ θ in Jθ, cosMul g θ * Real.sin (2 * ((n : ℝ) + 1) * θ) = 0 := by
    intro n
    have h1 : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hmom := sin_moment_zero hg hgm h (n + 1)
    rwa [h1] at hmom
  have hAzero : cosMul g =ᵐ[MeasureTheory.volume.restrict Jθ] 0 :=
    Work.FTS.EllipticEst.sin_system_complete hmem hsin
  have hA2zero : ∫ θ in Jθ, cosMul g θ ^ 2 = 0 := by
    have hae : (fun θ => cosMul g θ ^ 2)
        =ᵐ[MeasureTheory.volume.restrict Jθ] (0 : ℝ → ℝ) := by
      filter_upwards [hAzero] with θ hθ
      rw [hθ]; simp
    rw [MeasureTheory.integral_congr_ae hae]
    simp
  have hfin : ∫ u in Set.Icc 0 1, g u ^ 2 * Real.sqrt (1 - u ^ 2) = 0 := by
    rw [← sq_integral_subst]
    exact hA2zero
  have hprod : (fun u => g u ^ 2 * Real.sqrt (1 - u ^ 2))
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc 0 1)] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun u => by positivity) hg).mp hfin
  have hsne : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Icc 0 1)),
      Real.sqrt (1 - u ^ 2) ≠ 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    have hne : ∀ᵐ u ∂(MeasureTheory.volume : Measure ℝ), u ≠ 1 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with u hu huIcc
    have hlt : u < 1 := lt_of_le_of_ne huIcc.2 hu
    simp only [ne_eq, Real.sqrt_eq_zero', not_le]
    nlinarith [huIcc.1, hlt]
  filter_upwards [hprod, hsne] with u hp hs
  rcases mul_eq_zero.mp hp with h0 | h0
  · exact sq_eq_zero_iff.mp h0
  · exact absurd h0 hs

/-- **Completeness of the odd powers, corrected form (a.e.-measurable `g`).**

This is the requested statement with the single missing hypothesis
`AEStronglyMeasurable g (volume.restrict (Icc 0 1))` added. -/
theorem odd_powers_complete_of_aestronglyMeasurable {g : ℝ → ℝ}
    (hg : IntegrableOn (fun u => g u ^ 2 * Real.sqrt (1 - u ^ 2)) (Set.Icc 0 1))
    (hgm : AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Icc 0 1)))
    (h : ∀ k : ℕ, (∫ u in (0 : ℝ)..1, g u * u ^ (2 * k + 1) * Real.sqrt (1 - u ^ 2)) = 0) :
    g =ᵐ[MeasureTheory.volume.restrict (Set.Icc 0 1)] 0 := by
  set g' : ℝ → ℝ := AEStronglyMeasurable.mk g hgm with hg'def
  have hg'meas : Measurable g' := hgm.stronglyMeasurable_mk.measurable
  have hgg' : g =ᵐ[MeasureTheory.volume.restrict (Set.Icc 0 1)] g' := hgm.ae_eq_mk
  have hg'int : IntegrableOn (fun u => g' u ^ 2 * Real.sqrt (1 - u ^ 2)) (Set.Icc 0 1) := by
    refine (MeasureTheory.integrable_congr ?_).mp hg
    filter_upwards [hgg'] with u hu
    rw [hu]
  have hIcc : ∀ k : ℕ,
      ∫ u in Set.Icc 0 1, g u * u ^ (2 * k + 1) * Real.sqrt (1 - u ^ 2) = 0 := by
    intro k
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc (x := 0) (y := 1),
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact h k
  have hIcc' : ∀ k : ℕ,
      ∫ u in Set.Icc 0 1, g' u * u ^ (2 * k + 1) * Real.sqrt (1 - u ^ 2) = 0 := by
    intro k
    refine (MeasureTheory.integral_congr_ae ?_).trans (hIcc k)
    filter_upwards [hgg'] with u hu
    rw [hu]
  have h' : ∀ k : ℕ, (∫ u in (0 : ℝ)..1, g' u * u ^ (2 * k + 1) * Real.sqrt (1 - u ^ 2)) = 0 := by
    intro k
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc (x := 0) (y := 1)]
    exact hIcc' k
  exact hgg'.trans (odd_powers_complete_of_measurable hg'int hg'meas h')

end Work.FTS.PhiStar.Gegenbauer
