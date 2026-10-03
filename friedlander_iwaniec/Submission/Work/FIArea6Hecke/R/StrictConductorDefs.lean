/-
# `Work.FIArea6Hecke.R.StrictConductorDefs`

Vocabulary for the **conductor reduction** of a strict character `χ` modulo `4d`
(`Work.FIArea5.S16Hecke.IsCharMod4dStrict d χ`).

The Hecke `L`-function of the Größencharacter `ψ(z) = χ(z)(z/|z|)^m` of `ℚ(i)` depends only on the
values of `χ` on the *primary* Gaussian integers (`R/heckeFEStrictConductor.heckeLam_eq_of_primary_agree`),
and a strict `χ` mod `4d` is the inflation of a *primitive* character `χ₀` of a unique minimal
modulus `𝔪 ∣ (4d)`, its **conductor**:

* `IsUnitMod M z` — `z` is a unit modulo `M`;
* `IsPrimitivePartner d χ M χ₀` — `M` generates the conductor of `χ` and `χ₀` is the associated
  primitive partner: multiplicative, `χ₀ 1 = 1`, `‖χ₀‖ ≤ 1`, periodic modulo `M`, vanishing off
  the units modulo `M`, equal to `χ` on the primary units modulo `4d`, and *primitive* at level
  `M` (nontrivial on `1 + M'` for every proper divisor `M' ∣ M`);
* `capValuation M` / `thetaLevel M` — the `(1+i)`-adic valuation capped at `3`, and
  `N(lcm((1+i)^3, M))`, the level of the theta transformation law of the primary-coset theta
  series of `χ₀` (`R/primaryCosetThetaLaw`).  For `𝔪 = (4)` one has `thetaLevel = 16`, and for
  `𝔪 = (3)` one has `thetaLevel = 72`, as required by the numerical verification of
  `NOTES_FEStrictConductor.md`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Defs

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- `z` is a **unit modulo `M`**: `∃ w, M ∣ z*w - 1`.  (`M = 0` gives `IsUnitMod 0 z ↔ z*w = 1`,
i.e. `z` a unit of `ℤ[i]`.) -/
def IsUnitMod (M : GaussianInt) (z : GaussianInt) : Prop := ∃ w : GaussianInt, M ∣ (z * w - 1)

/-- The `(1+i)`-adic valuation of `M`, capped at `3`. -/
def capValuation (M : GaussianInt) : ℕ := by
  classical
  exact if (Work.FIArea5.S16Hecke.oneAddI ^ 3) ∣ M then 3
    else if (Work.FIArea5.S16Hecke.oneAddI ^ 2) ∣ M then 2
    else if Work.FIArea5.S16Hecke.oneAddI ∣ M then 1 else 0

/-- The **level** of the theta transformation law attached to the period `M`, namely
`N(lcm((1+i)^3, M)) = 8·N(M)/2^{min(3, v_{(1+i)}(M))}`. -/
def thetaLevel (M : GaussianInt) : ℕ := 8 * Work.FIPlan.gnorm M / 2 ^ capValuation M

/-- **The conductor of `χ` and its (primitive) partner.**  `M` generates the Hecke conductor of
the strict character `χ` mod `4d`, and `χ₀` is the induced character of `(ℤ[i]/M)^*` (extended by
zero off the units), which is primitive at level `M`.

The clause `chi₀ z = chi z` on the primary units mod `4d` together with `M`-periodicity is what
makes `χ₀` well defined; primitivity is deliberately **not** part of this predicate (it is the
hypothesis of `R/partnerThetaLaw`, and is automatic for the minimal `M`). -/
def IsConductorPartner (d : ℕ) (chi : GaussianInt → ℂ) (M : GaussianInt)
    (chi₀ : GaussianInt → ℂ) : Prop :=
  M ∣ (((4 * d : ℕ) : ℤ) : GaussianInt) ∧ M ≠ 0 ∧
  chi₀ 1 = 1 ∧
  (∀ z w : GaussianInt, chi₀ (z * w) = chi₀ z * chi₀ w) ∧
  (∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) ∧
  (∀ z w : GaussianInt, M ∣ (z - w) → chi₀ z = chi₀ w) ∧
  (∀ z : GaussianInt, ¬ IsUnitMod M z → chi₀ z = 0) ∧
  (∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
    Work.FIArea5.S16Hecke.IsUnitMod4d d z → chi₀ z = chi z)

/-- `χ₀` is **primitive** at level `M`: for every non-unit divisor `M' ∣ M` the character `χ₀` is
nontrivial on `1 + M'` (equivalently, `χ₀` does not factor through `(ℤ[i]/M')^*`). -/
def IsPrimitiveAt (M : GaussianInt) (chi₀ : GaussianInt → ℂ) : Prop :=
  ∀ M' : GaussianInt, M' ∣ M → ¬ (M ∣ M') → ¬ IsUnit M' →
    ∃ z : GaussianInt, M' ∣ (z - 1) ∧ chi₀ z ≠ 1

/-- The conclusion of `heckeFEStrictConductor`: an entire `Φ` with the reflected functional
equation, agreeing on `re s > 1 + |m|/2` with `(X/π)^s Γ(s+|m|/2) L(s,ψ_χ)` times a finite product
of inverse Euler factors at the rational primes dividing `4d`. -/
def HasConductorFEle (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) : Prop :=
  ∃ (X : ℝ) (c₁ c₂ : ℕ → ℂ) (S : Finset ℕ) (Phi : ℂ → ℂ) (W : ℂ),
    1 ≤ X ∧ X ≤ 4 * (d : ℝ) ∧
    (∀ p ∈ S, Nat.Prime p ∧ p ∣ 4 * d ∧ ‖c₁ p‖ ≤ 1 ∧ ‖c₂ p‖ ≤ 1) ∧
    W ≠ 0 ∧ AnalyticOn ℂ Phi Set.univ ∧
    (∀ s : ℂ, Phi s = W * star (Phi (star (1 - s)))) ∧
    (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
      Phi s = ((X / Real.pi : ℝ) : ℂ) ^ s *
        Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) *
        Work.FIArea5.S16Hecke.heckeLSeries chi m s *
        ∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s))))⁻¹)

end

end Work.FIArea6Hecke.R
