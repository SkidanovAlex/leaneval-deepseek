/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# Positive definiteness of `U(G) = N(G)[(N(G) ∖ {0})⁻¹]`

`Work.ORVonNeumann.IsPositiveDefinite R` says that `R` is `*`-regular and that every matrix
ring `Matₙ(R)` is `*`-regular (Jaikin-Zapirain–López-Álvarez, arXiv:1810.12135, §3.1).  Here
we prove it for the algebra of affiliated operators of a group von Neumann algebra.

The `*`-regularity of `U(G)` itself is Berberian's theorem
(`Work.ORVonNeumann.VonNeumannAlgebra.starRegularAffiliated`).  For the matrix rings the
existing reduction `Work.ORVonNeumann.Regular.matrix_isStarRegularRing` shows that it is
enough to know that `U(G)` has **no non-trivial sums of squares**:
`∑ i, x i * (x i)⋆ = 0` forces every `x i = 0`.

That is what is proved here.  The argument is the trace argument of the theory of finite von
Neumann algebras, transported to the Ore localisation:

* write the `x i` as fractions over a *common* denominator `e ∈ S = nzd(N(G))`, i.e.
  `numU e * x i = numU (b i)` with `b i ∈ N(G)`
  (`Work.ORVonNeumann.Rep.oreCommonDenom`);
* multiplying `∑ i, x i * (x i)⋆ = 0` on the left by `numU e` and on the right by
  `numU (star e)` and using `star (numU e * x i) = star (x i) * numU (star e)` turns it into
  `∑ i, b i * (b i)⋆ = 0` **inside** `N(G)` (here `numU` is injective);
* applying the faithful positive trace `τ` to that sum, traciality turns every term into
  `τ ((b i)⋆ * b i)`, a non-negative real number; a vanishing sum of non-negative reals has
  all terms zero, so `τ ((b i)⋆ * b i) = 0` and faithfulness of `τ` gives `b i = 0`, whence
  `x i = 0`.  This last step is
  `Work.ORVonNeumann.tauSumNormsEqZero` (`Submission/Work/ORVonNeumann/tauSumNormsEqZero`).

## Main results

* `Work.ORVonNeumann.VonNeumannAlgebra.hasNoNontrivialSquares_affiliated` — for every model
  `D : GroupVonNeumannAlgebra G`, `HasNoNontrivialSquares D.affiliated`;
* `Work.ORVonNeumann.VonNeumannAlgebra.posDefAffiliated` — the unconditional statement
  `IsPositiveDefinite U(G)` for `U(G) = N(G)[(nzd)⁻¹]`, `G` countable.
-/
import Mathlib
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.rankAffiliated
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.starRegularAffiliated
import Submission.Work.ORVonNeumann.Basic
import Submission.Work.ORVonNeumann.Regular.matrix_isStarRegularRing
import Submission.Work.ORVonNeumann.Regular.matrix_vonNeumannRegular
import Submission.Work.ORVonNeumann.tauSumNormsEqZero

set_option autoImplicit false

namespace Work.ORVonNeumann.VonNeumannAlgebra

open OreLocalization

/-! ### Two elementary identities for sums of norms -/

section Sums

variable {R : Type*} [Ring R] [StarMul R]

/-- `∑ j, (A * f j) * ((f j)⋆ * B) = A * (∑ j, f j * (f j)⋆) * B`. -/
theorem sum_mul_star_mul {n : ℕ} (A B : R) (f : Fin n → R) :
    (∑ j, (A * f j) * (star (f j) * B)) = A * (∑ j, f j * star (f j)) * B := by
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by noncomm_ring

/-- `∑ j, (A * f j) * (A * f j)⋆ = A * (∑ j, f j * (f j)⋆) * A⋆`. -/
theorem sum_mul_star_self {n : ℕ} (A : R) (f : Fin n → R) :
    (∑ j, (A * f j) * star (A * f j)) = A * (∑ j, f j * star (f j)) * star A := by
  rw [← sum_mul_star_mul (A := A) (B := star A) (f := f)]
  exact Finset.sum_congr rfl fun j _ => by rw [star_mul]

end Sums

/-! ### No non-trivial sums of squares in `U(G)` -/

section Affiliated

variable {G : Type*} [Group G]

/-- **`U(G)` has no non-trivial sums of squares.**  If `∑ i, x i * (x i)⋆ = 0` in the
algebra `U(G)` of affiliated operators, then every `x i` vanishes.

The proof clears denominators in the Ore localisation and then applies the faithful positive
trace of `N(G)`; see the module docstring. -/
theorem hasNoNontrivialSquares_affiliated (D : GroupVonNeumannAlgebra G) :
    HasNoNontrivialSquares D.affiliated := by
  intro n x hx
  -- Every element of the localisation is a fraction.
  have hrep : ∀ i : Fin n, ∃ (a : D.N) (s : nonZeroDivisors D.N),
      x i = (a /ₒ s : D.affiliated) := fun i =>
    OreLocalization.ind (X := D.N)
      (β := fun y : D.affiliated => ∃ (a : D.N) (s : nonZeroDivisors D.N),
        y = (a /ₒ s : D.affiliated))
      (fun a s => ⟨a, s, rfl⟩) (x i)
  choose a s hs using hrep
  -- A common denominator for the whole family.
  obtain ⟨e, t, b, _hte, hbs⟩ :=
    Work.ORVonNeumann.Rep.oreCommonDenom (R := D.N) (S := nonZeroDivisors D.N) le_rfl a s
  have hxbe : ∀ j, x j = (b j /ₒ e : D.affiliated) := fun j => (hs j).trans (hbs j)
  -- Multiplying by the denominator clears it.
  have hnum : ∀ j, numU D (e : D.N) * x j = numU D (b j) := by
    intro j
    rw [hxbe j]
    show (↑(OreLocalization.numeratorUnit (S := nonZeroDivisors D.N) e) : D.affiliated)
        * (b j /ₒ e) = b j /ₒ 1
    exact OreLocalization.mul_cancel
  -- Clearing denominators in the sum of norms.
  have hstep : (∑ j, numU D (b j * star (b j)))
      = numU D (e : D.N) * (∑ j, x j * star (x j)) * numU D (star (e : D.N)) := by
    calc ∑ j, numU D (b j * star (b j))
        = ∑ j, numU D (b j) * star (numU D (b j)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_mul, affiliated_star_numerator]
      _ = ∑ j, (numU D (e : D.N) * x j) * star (numU D (e : D.N) * x j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hnum j]
      _ = numU D (e : D.N) * (∑ j, x j * star (x j)) * star (numU D (e : D.N)) :=
            sum_mul_star_self _ _
      _ = numU D (e : D.N) * (∑ j, x j * star (x j)) * numU D (star (e : D.N)) := by
            rw [affiliated_star_numerator]
  have hchain : numU D (∑ j, b j * star (b j)) = 0 := by
    rw [map_sum]
    rw [hstep, hx, mul_zero, zero_mul]
  -- Being zero in `U(G)` and being zero in `N(G)` agree on numerators.
  have hinj : Function.Injective (numU D) :=
    OreLocalization.numeratorHom_inj (S := nonZeroDivisors D.N)
      (fun t ht => (mem_nonZeroDivisors_iff'.mp ht).1)
  have hN : (∑ j, b j * star (b j)) = 0 := hinj (by rw [hchain, map_zero])
  -- The trace argument inside `N(G)` (delegated to `tauSumNormsEqZero`).
  have hb : ∀ j, b j = 0 := Work.ORVonNeumann.tauSumNormsEqZero D b hN
  intro i
  rw [hxbe i, hb i]
  exact OreLocalization.zero_oreDiv e

end Affiliated

/-! ### Positive definiteness of `U(G)` -/

theorem posDefAffiliated {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] : IsPositiveDefinite (Work.ORVonNeumann.Rep.countableGroupVonNeumann (G := G)).affiliated := by
  have hsr : IsStarRegularRing (Work.ORVonNeumann.Rep.countableGroupVonNeumann (G := G)).affiliated :=
    starRegularAffiliated (G := G)
  exact ⟨hsr, fun n => Regular.matrix_isStarRegularRing hsr.1
    (hasNoNontrivialSquares_affiliated _) n⟩

end Work.ORVonNeumann.VonNeumannAlgebra
