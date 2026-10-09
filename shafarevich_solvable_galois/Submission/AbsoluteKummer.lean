/-
Copyright (c) 2025. All rights reserved.

# Kummer theory in the absolute-Galois language

`Submission/Work/AbsoluteKummer/` builds the continuous cohomology `H⁰`, `H¹`, `H²` of the absolute
Galois group `G_k = Field.absoluteGaloisGroup k` with coefficients in a discrete module, **Hilbert 90**
for `G_k`, and the **Kummer isomorphism** `kˣ/(kˣ)ⁿ ≅ H¹(G_k, μₙ)`.  This is the bridge between the
arithmetic results of `Submission/Work/QuadraticLocalGlobal` (Grünwald in degree `2`, the Hasse norm
theorem, Hasse–Brauer–Noether) and the embedding-problem machinery of
`Submission/Work/Properness` / `Submission/Work/AbsoluteGalois` (where the obstruction of an
embedding problem with abelian kernel is a class in `H²`).

## Main results

* `Submission.kummerEquiv` — the Kummer isomorphism `kˣ/(kˣ)ⁿ ≃* H¹(G_k, μₙ)` for `μ_n ⊆ k`
  (values: `σ ↦ σ(α)/α` for any `α` with `αⁿ = x`);
* `Submission.kummerEquivRatTwo` — the case `k = ℚ`, `n = 2`: **`ℚˣ/(ℚˣ)² ≃* H¹(G_ℚ, μ₂)`**;
* `Submission.hilbert90_H1_eq_zero` — **Hilbert 90 for `G_k`**: `H¹(G_k, k̄ˣ) = 0`;
* `Submission.grunwald_sqClassLocalize_surjective` — **Grünwald's theorem in degree 2** (from
  `Work/QuadraticLocalGlobal`), i.e. the localisation map `ℚˣ/(ℚˣ)² → ∏_i ℚ_{q_i}ˣ/(ℚ_{q_i}ˣ)²` is
  surjective for finitely many distinct primes `q i`; its `H¹` form (conditional only on the
  *local* Kummer identifications) is `Work.AbsoluteKummer.grunwald_h1_surjective(_pi)`, and
  `Work.AbsoluteKummer.sqClassLocalize_surjective_pi` is the coefficient-module version.

The finite-level (inflation) description of the cohomology of `G_k`, the low-degree exact sequences,
and the dictionary with `Work.Properness`'s embedding problems live in the same directory; see
`Submission/Work/AbsoluteKummer/NOTES.md`.
-/
import Mathlib
import Submission.Work.AbsoluteKummer.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

open scoped Classical

noncomputable section

/-- **The Kummer isomorphism** `kˣ/(kˣ)ⁿ ≃* H¹(G_k, μₙ)` for a field `k` containing a primitive
`n`-th root of unity `ζ`.  The map sends the class of `x` to the class of the crossed homomorphism
`σ ↦ σ(α)/α`, where `α` is any `n`-th root of `x` in `k̄`. -/
def kummerEquiv {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)] {n : ℕ} [NeZero n]
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) :
    (kˣ ⧸ Work.Kummer.nthPowerSubgroup n kˣ) ≃*
      Multiplicative (Work.AbsoluteKummer.H1 (Work.AbsoluteKummer.G k)
        (Additive (rootsOfUnity n (AlgebraicClosure k)))) :=
  Work.AbsoluteKummer.kummerEquiv hζ

/-- The Kummer isomorphism for `k = ℚ`, `n = 2`: **`ℚˣ/(ℚˣ)² ≃* H¹(G_ℚ, μ₂)`**. -/
def kummerEquivRatTwo :
    (ℚˣ ⧸ Work.Kummer.nthPowerSubgroup 2 ℚˣ) ≃*
      Multiplicative (Work.AbsoluteKummer.H1 (Field.absoluteGaloisGroup ℚ)
        (Additive (rootsOfUnity 2 (AlgebraicClosure ℚ)))) :=
  Work.AbsoluteKummer.kummerEquivRatTwo

/-- **Hilbert 90 for the absolute Galois group**: every locally constant crossed homomorphism
`G_k → k̄ˣ` is principal, i.e. `H¹(G_k, k̄ˣ) = 0`. -/
theorem hilbert90_H1_eq_zero (k : Type*) [Field k] [IsGalois k (AlgebraicClosure k)]
    (x : Work.AbsoluteKummer.H1 (Field.absoluteGaloisGroup k)
      (Additive (AlgebraicClosure k)ˣ)) : x = 0 :=
  Work.AbsoluteKummer.Hilbert90.H1_eq_zero_absolute x

theorem grunwald_sqClassLocalize_surjective {ι : Type*} [Fintype ι] (q : ι → ℕ)
    [∀ i, Fact (q i).Prime] (hq : Function.Injective q) :
    Function.Surjective (fun x : Work.AbsoluteKummer.SqClass ℚ => fun i : ι =>
      Work.AbsoluteKummer.sqClassLocalize (q i) x) :=
  Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective q hq

end

end Submission
