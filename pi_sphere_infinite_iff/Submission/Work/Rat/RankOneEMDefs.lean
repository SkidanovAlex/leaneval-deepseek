import Mathlib
import Submission.Work.Serre.Defs
import Submission.Work.StemsB.Fibrations
import Submission.Work.RatHurewicz.RelHomotopy

/-!
# Interfaces for the rank-one Eilenberg–MacLane computation

`Work.Rat.rangeModelAcyclicOddUnbounded` (the target of this area) states: if `Z` has trivial
homotopy groups up to degree `M+1` except in an odd degree `d ≥ 3`, where `H_d(Z;ℚ) ≅ ℚ`, then
`H_j(Z;ℚ) = 0` for `d < j ≤ M+1`.

The (M+1)-type of such a `Z` is the (M+1)-type of `K(A,d)` with `A = π_d(Z)`, `A ⊗ ℚ ≅ ℚ`; the
mathematical content is therefore the *rank-one* case of the rational homology computation of an
Eilenberg–MacLane space.  This file fixes the two interfaces in which that computation, in the
"free top" form of `Submission/Work/Stems/Engine/C2FreeTop.lean` (`C2evenFree` / `C2oddFree`, which
the workspace states for `ℤ`-coefficients), enters the proof:

* `RankOneOddFree c` — the odd clause with **arbitrary rank-one coefficients** (`H_n(X;ℚ) ≅ ℚ`
  instead of `π_n(X) ≅ ℤ`) and a free top `N`, with the linear deficit `c·n` of the induction;
* `RankOneC1` — the base case `n = 1`: a connected space whose `π_i` vanish for `2 ≤ i ≤ N` and
  whose `H_1(X;ℚ) ≅ ℚ` is rationally a circle in the range.

Both are strictly weaker than the target (they carry the deficit `c·n` and do not mention the
target's `Z`); the target follows from `RankOneOddFree 1` by the Postnikov truncation
`Work.Serre.serrePostnikovTower` and the mapping theorem `Work.Serre.SerreE3a`, which is the
assembly proved in `Submission/Work/Rat/rangeModelAcyclicOddUnbounded.lean`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Rat

noncomputable section

/-- **The odd `K(A,·)` clause with rank-one coefficients, free top.**  For odd `n`, a space `X`
whose homotopy groups vanish up to degree `N` except in degree `n`, where `H_n(X;ℚ) ≅ ℚ`, has
vanishing rational homology in the degrees `n < j ≤ N - c·n`.

(The hypothesis is exactly `H_n(X;ℚ) ≅ ℚ`: by the Hurewicz theorem in the first non-vanishing
degree this says `π_n(X) ⊗ ℚ ≅ ℚ`, i.e. that the coefficient group has rational rank one; it does
not pin down `π_n(X)`, which may be `ℤ`, `ℚ`, `ℤ ⊕ T`, … .) -/
def RankOneOddFree (c : ℕ) : Prop :=
  ∀ (n N : ℕ), 3 ≤ n → Odd n → ∀ {X : Type} [TopologicalSpace X] (x₀ : X),
    (∀ j : ℕ, j ≤ N → j ≠ n → Subsingleton (HomotopyGroup (Fin j) X x₀)) →
    Nonempty (Work.Serre.ratH (TopCat.of X) n ≅ ModuleCat.of ℚ ℚ) →
    ∀ j : ℕ, n < j → j ≤ N - c * n →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) j)

/-- **The `n = 1` clause with rank-one coefficients** (in the *abelian* case).  A connected space
whose fundamental group is abelian, whose `H_1(-;ℚ) ≅ ℚ` and whose homotopy groups vanish in
degrees `2 ≤ i ≤ N`, has vanishing rational homology in degrees `1 < j ≤ N - 1`.

The abelianness hypothesis is essential and is *not* implied by `H_1 ≅ ℚ`: for a closed aspherical
`3`-manifold with first Betti number one (`π_1` non-abelian, e.g. an Anosov torus bundle) one has
`H_1 ≅ ℚ` and `H_2 ≅ ℚ ≠ 0` by Poincaré duality.  For abelian `π₁` with `H_1(-;ℚ) ≅ ℚ` the
statement is the rank-one case of `K(A,1)` (`H_*(A;ℚ) = Λ(A ⊗ ℚ) = ℚ` in degrees `0,1`).

This is `Work.Serre.RangeEMVanOne` with the torsion hypothesis on `π₁` replaced by
`H_1(-;ℚ) ≅ ℚ` (the case that the finite-coefficient statement
`Work.Serre.RangeEMVanOneFin` does not cover). -/
def RankOneC1Ab : Prop :=
  ∀ (N : ℕ) {X : Type} [TopologicalSpace X] (x₀ : X),
    Subsingleton (HomotopyGroup (Fin 0) X x₀) →
    (∀ a b : HomotopyGroup (Fin 1) X x₀, a * b = b * a) →
    Nonempty (Work.Serre.ratH (TopCat.of X) 1 ≅ ModuleCat.of ℚ ℚ) →
    (∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) X x₀)) →
    ∀ j : ℕ, 1 < j → j ≤ N - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) j)

/-- **The homological Gysin periodicity in the range given by the fibre.**  For a Serre fibration
`p : E → B` with rationally acyclic total space, path-connected base and fibre a rational `r`-sphere
through degree `N` (`H_t(F;ℚ) = 0` for `0 < t ≤ N`, `t ≠ r`, and `H_r(F;ℚ) ≅ ℚ`), the rational
homology of the base is periodic of period `r+1` through degree `N+1`:
`H_m(B;ℚ) ≅ H_{m+r+1}(B;ℚ)` for `m + r + 1 ≤ N + 1`.

This is the *homological* form of the Euler-class/Gysin statement `Work.Serre.SerreE3b` (no cup
product is mentioned): it is the input of the `C2` even step of the Eilenberg–MacLane computation,
in the sole form in which that step uses it. -/
def GysinPeriodicityHom : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (r N : ℕ),
    1 ≤ r → Work.StemsB.IsSerreFibration p → SimplyConnectedSpace B → Work.Serre.RatAcyclic E →
      (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
        IsZero (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) t)) →
      Nonempty (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) r ≅
        ModuleCat.of ℚ ℚ) →
      ∀ m : ℕ, m + r + 1 ≤ N + 1 →
        Nonempty (Work.Serre.ratH (TopCat.of B) m ≅ Work.Serre.ratH (TopCat.of B) (m + r + 1))

/-- **Range models of the same rank-one type have the same rational homology in the range.**  If `X`
is a range model through `N` and `P` one through `M ≥ N` with the same hole degree `d` (homotopy
groups trivial below the top except in degree `d`), and both have `H_d(-;ℚ) ≅ ℚ`, then
`H_i(X;ℚ) ≅ H_i(P;ℚ)` for `i ≤ N`.

This is the `rank-one` (arbitrary coefficient group of rational rank one) form of
`Work.StemsB.rangeModel_ratH_iso_le`, which is proved for `ℤ`-coefficients. -/
def RangeModelComparison : Prop :=
  ∀ (d N M : ℕ) {X P : Type} [TopologicalSpace X] [TopologicalSpace P] (x₀ : X) (p₀ : P),
    N ≤ M →
    (∀ j : ℕ, j ≤ N → j ≠ d → Subsingleton (HomotopyGroup (Fin j) X x₀)) →
    (∀ j : ℕ, j ≤ M → j ≠ d → Subsingleton (HomotopyGroup (Fin j) P p₀)) →
    Nonempty (Work.Serre.ratH (TopCat.of X) d ≅ ModuleCat.of ℚ ℚ) →
    Nonempty (Work.Serre.ratH (TopCat.of P) d ≅ ModuleCat.of ℚ ℚ) →
    ∀ i : ℕ, i ≤ N →
      Nonempty (Work.Serre.ratH (TopCat.of X) i ≅ Work.Serre.ratH (TopCat.of P) i)

/-- **The Postnikov truncation of a rank-one range model, with the comparison in the range.**  For a
space `Z` whose homotopy groups vanish up to degree `M+1` except in degree `d ≥ 3`, where
`H_d(Z;ℚ) ≅ ℚ`, there is a space `P` that is a range model of the same type through the *larger*
top `M+1+d` (`π_j(P) = 0` for `j ≤ M+1+d`, `j ≠ d`), still has `H_d(P;ℚ) ≅ ℚ`, and has the same
rational homology as `Z` in degrees `≤ M+1`.

The space `P` is the Postnikov truncation `Work.Serre.serrePostnikovTower` of `Z` at `M+1` (with top
`M+1+d`; this is the case `d ≤ M+1`), and the comparison is `Work.StemsB.rangeModel_ratH_iso` (proved for an arbitrary
coefficient group) applied to the two range models `Z` (through `M+1`) and `P` (through `M+1+d`),
together with the weakening of the top. -/
def TruncationComparison : Prop :=
  ∀ {d M : ℕ}, 3 ≤ d → d ≤ M + 1 → ∀ {Z : Type} [TopologicalSpace Z] (z₀ : Z),
    (∀ j : ℕ, j ≤ M + 1 → j ≠ d → Subsingleton (HomotopyGroup (Fin j) Z z₀)) →
    Nonempty (Work.Serre.ratH (TopCat.of Z) d ≅ ModuleCat.of ℚ ℚ) →
    ∃ (P : Type) (_ : TopologicalSpace P) (p₀ : P),
      (∀ j : ℕ, j ≤ M + 1 + d → j ≠ d → Subsingleton (HomotopyGroup (Fin j) P p₀)) ∧
      Nonempty (Work.Serre.ratH (TopCat.of P) d ≅ ModuleCat.of ℚ ℚ) ∧
      (∀ j : ℕ, j ≤ M + 1 →
        Nonempty (Work.Serre.ratH (TopCat.of Z) j ≅ Work.Serre.ratH (TopCat.of P) j))

end

end Work.Rat
