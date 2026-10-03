/-
# Facts about the `L`-series of `χ₄` on `re s > 1`

This file proves `Work.FIArea6Hecke.R.axisChi4_LSeries_facts`, the elementary analytic facts
about the `L`-series of the quadratic character `χ₄` (`axisChi4`) needed on the real axis
`1 < σ ≤ 2`:

* `LSeries axisChi4` is complex differentiable for `re s > 1`;
* it does not vanish there;
* the real part of its logarithmic derivative `-L'/L` is bounded above on `(1,2]`.

The route is to identify `axisChi4` with the `ℕ`-restriction of the Dirichlet character
`χ₄ : DirichletCharacter ℂ 4` (obtained from `ZMod.χ₄` by pushing forward along `ℤ → ℂ`) and
then use the Mathlib theory of Dirichlet `L`-functions: `DirichletCharacter.LFunction χ₄` is
entire and nonvanishing on `re s ≥ 1`, and it agrees with the naive `L`-series on `re s > 1`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.AxisLogDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea6Hecke.R

open Complex
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The Dirichlet character `χ₄` with values in `ℂ` -/

/-- The primitive quadratic Dirichlet character modulo `4`, with values in `ℂ`, obtained from
`ZMod.χ₄ : MulChar (ZMod 4) ℤ` by pushing forward along `ℤ → ℂ`. -/
def chi4C : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- `axisChi4` is the `ℕ`-restriction of `chi4C`. -/
lemma axisChi4_eq_chi4C (n : ℕ) : axisChi4 n = chi4C (n : ZMod 4) := by
  simp [axisChi4, chi4C, MulChar.ringHomComp_apply]

/-- `ZMod.χ₄` is not the trivial character modulo `4`. -/
lemma zmodChi4_ne_one : (ZMod.χ₄ : MulChar (ZMod 4) ℤ) ≠ 1 := by
  intro h
  have h3 := congrArg (fun χ : MulChar (ZMod 4) ℤ => χ (3 : ZMod 4)) h
  rw [show (1 : MulChar (ZMod 4) ℤ) (3 : ZMod 4) = 1 from MulChar.one_apply (by decide)]
    at h3
  rw [show ZMod.χ₄ (3 : ZMod 4) = -1 from by decide] at h3
  norm_num at h3

/-- `chi4C` is a nontrivial Dirichlet character. -/
lemma chi4C_ne_one : chi4C ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ) Int.cast_injective).mpr
    zmodChi4_ne_one

/-- The `L`-series of `axisChi4` is the `L`-series of the `ℕ`-restriction of `chi4C`. -/
lemma LSeries_chi4C_eq :
    LSeries (fun n : ℕ => chi4C (n : ZMod 4)) = LSeries axisChi4 := by
  funext s
  exact LSeries_congr (f := fun n : ℕ => chi4C (n : ZMod 4)) (g := axisChi4)
    (fun {n} _ => (axisChi4_eq_chi4C n).symm) s

/-- On `re s > 1` the `L`-series of `axisChi4` agrees with the (entire) Dirichlet `L`-function
of `chi4C`. -/
lemma LSeries_axisChi4_eq_LFunction {s : ℂ} (hs : 1 < s.re) :
    LSeries axisChi4 s = chi4C.LFunction s := by
  rw [← LSeries_chi4C_eq]
  exact (DirichletCharacter.LFunction_eq_LSeries chi4C hs).symm

/-! ## The abscissa of absolute convergence -/

lemma abscissaOfAbsConv_chi4C :
    LSeries.abscissaOfAbsConv (fun n : ℕ => chi4C (n : ZMod 4)) = 1 :=
  DirichletCharacter.absicssaOfAbsConv_eq_one (by norm_num : (4 : ℕ) ≠ 0) chi4C

/-! ## Differentiability -/

lemma differentiableAt_LSeries_axisChi4 {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (LSeries axisChi4) s := by
  rw [← LSeries_chi4C_eq]
  refine (LSeries_hasDerivAt ?_).differentiableAt
  rw [abscissaOfAbsConv_chi4C]
  exact_mod_cast hs

/-! ## Nonvanishing -/

lemma LSeries_axisChi4_ne_zero {s : ℂ} (hs : 1 < s.re) : LSeries axisChi4 s ≠ 0 := by
  rw [LSeries_axisChi4_eq_LFunction hs]
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi4C (Or.inl chi4C_ne_one)
    (le_of_lt hs)

/-! ## Boundedness of the logarithmic derivative on the real axis -/

/-- The logarithmic derivative `-L'/L` of `χ₄`, expressed through the entire function
`chi4C.LFunction` so that it makes sense on `re s ≥ 1`. -/
def chi4LogDeriv : ℂ → ℂ :=
  fun s => -deriv chi4C.LFunction s / chi4C.LFunction s

lemma continuousOn_chi4LogDeriv : ContinuousOn chi4LogDeriv {s : ℂ | 1 ≤ s.re} := by
  have h1 : ContinuousOn (fun s : ℂ => deriv chi4C.LFunction s) {s : ℂ | 1 ≤ s.re} :=
    ((DirichletCharacter.differentiable_LFunction chi4C_ne_one).deriv).continuous.continuousOn
  have h2 : ContinuousOn (fun s : ℂ => chi4C.LFunction s) {s : ℂ | 1 ≤ s.re} :=
    (DirichletCharacter.differentiable_LFunction chi4C_ne_one).continuous.continuousOn
  have h3 : ∀ s ∈ {s : ℂ | 1 ≤ s.re}, chi4C.LFunction s ≠ 0 :=
    fun s hs => DirichletCharacter.LFunction_ne_zero_of_one_le_re chi4C (Or.inl chi4C_ne_one) hs
  have h := (h1.neg).div h2 h3
  rw [show chi4LogDeriv = (-(fun s : ℂ => deriv chi4C.LFunction s) /
      fun s : ℂ => chi4C.LFunction s) from rfl]
  exact h

/-- The logarithmic derivative of `χ₄` is bounded above on the real interval `(1,2]`. -/
lemma exists_bound_chi4LogDeriv_re :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 → (chi4LogDeriv (σ : ℂ)).re ≤ C := by
  have hcont : ContinuousOn (fun σ : ℝ => (chi4LogDeriv (σ : ℂ)).re) (Set.Icc 1 2) := by
    have hmaps : Set.MapsTo (fun σ : ℝ => (σ : ℂ)) (Set.Icc 1 2) {s : ℂ | 1 ≤ s.re} := by
      intro σ hσ
      simpa using hσ.1
    have := (continuousOn_chi4LogDeriv.comp continuous_ofReal.continuousOn hmaps)
    simpa [Function.comp_def] using Complex.continuous_re.comp_continuousOn this
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro σ h1 h2
  have hb := hC σ ⟨le_of_lt h1, h2⟩
  calc (chi4LogDeriv (σ : ℂ)).re ≤ ‖(chi4LogDeriv (σ : ℂ)).re‖ := Real.le_norm_self _
    _ ≤ C := hb
    _ ≤ max C 0 := le_max_left _ _

/-- The logarithmic derivative of the `L`-series of `axisChi4` agrees, on `re s > 1`, with
`chi4LogDeriv`. -/
lemma logDeriv_LSeries_axisChi4_eq {σ : ℝ} (hσ : 1 < σ) :
    -deriv (LSeries axisChi4) (σ : ℂ) / LSeries axisChi4 (σ : ℂ)
      = chi4LogDeriv (σ : ℂ) := by
  have hd : deriv (LSeries axisChi4) (σ : ℂ) = deriv chi4C.LFunction (σ : ℂ) := by
    rw [← LSeries_chi4C_eq]
    exact (DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi4C hσ).symm
  have hv : LSeries axisChi4 (σ : ℂ) = chi4C.LFunction (σ : ℂ) :=
    LSeries_axisChi4_eq_LFunction hσ
  simp only [chi4LogDeriv, hd, hv]

/-! ## The main statement -/

theorem axisChi4_LSeries_facts :
    (∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (LSeries Work.FIArea6Hecke.R.axisChi4) s) ∧
    (∀ s : ℂ, 1 < s.re → LSeries Work.FIArea6Hecke.R.axisChi4 s ≠ 0) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv (LSeries Work.FIArea6Hecke.R.axisChi4) (σ : ℂ) /
        LSeries Work.FIArea6Hecke.R.axisChi4 (σ : ℂ)).re ≤ C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact differentiableAt_LSeries_axisChi4 hs
  · intro s hs
    exact LSeries_axisChi4_ne_zero hs
  · obtain ⟨C, hC0, hC⟩ := exists_bound_chi4LogDeriv_re
    refine ⟨C, hC0, ?_⟩
    intro σ h1 h2
    rw [logDeriv_LSeries_axisChi4_eq h1]
    exact hC σ h1 h2

end

end Work.FIArea6Hecke.R
