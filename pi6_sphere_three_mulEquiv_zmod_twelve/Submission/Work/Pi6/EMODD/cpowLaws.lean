import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.cupBilinear
import Submission.Work.Serre.cohMap_oneH
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The elementary laws for cup powers `Work.Pi6.cpow`

`Work.Pi6.cpow x k` is the `k`-th cup power of a degree-`2` class: `cpow x 0 = 1` and
`cpow x (k+1) = cup (cpow x k) x`.  This file records its two elementary laws:

* naturality, `f^*(w^k) = (f^* w)^k`, from the naturality of the cup product
  (`Work.Cohomology.cupNaturalH`) and of the unit (`Work.Serre.cohMap_oneH`);
* homogeneity, `(a·w)^k = a^k·w^k`, from the `R`-bilinearity of `cup`.

The proofs are inductions on `k`.  The cohomology modules of `Work.Pi6.Interfaces` (`Work.Pi6.Coh`)
and the `SSet`-level modules on which `cupH'` lives are *definitionally* — but not syntactically —
equal, which makes `rw` choke on the `SSet`-spelled lemmas (`rw` matches at a low transparency at
which `singularCohomology`/`singularCochainComplex` are not unfolded).  The individual manipulation
steps are therefore performed with the `Work.Pi6.cup`-spelled phrases of the interface, where the
terms match syntactically, and the only definitional identifications needed (`Coh R X n` against the
`SSet` cohomology, and `2 * k + 2` against `2 * (k + 1)`) are left to the elaborator.

## Main results

* `Work.Pi6.EMODD.cpow_zero`, `Work.Pi6.EMODD.cpow_succ` — the recursion equations of `cpow`;
* `Work.Pi6.EMODD.cup_smul_left`, `Work.Pi6.EMODD.cup_smul_right` — homogeneity of `cup` in either
  variable, at the `Work.Pi6.cup` spelling;
* `Work.Pi6.EMODD.cpowLaws` — naturality and homogeneity of the cup power.

**A caveat at `R = ℤ`** (harmless, but worth knowing).  In `cpowLaws` the coefficient ring is a
*variable* with `[CommRing R]`, so the scalar action `a • w` on the cohomology module can only come
from the `Module R` structure.  When the lemma is *instantiated* at `R = ℤ`, a consumer who writes
`a • w` (with `a : ℤ`) on their side gets the `ZSMul.toSMul` action instead (it has higher instance
priority than the one inherited from `Module ℤ`), and the two are only *propositionally* equal:
`int_smul_eq_zsmul`.  `Work.Pi6.EMODD.cpow_smul_int` below is the ℤ-spelled homogeneity law, stated
with the instance a consumer obtains; it is proved from `cpowLaws ℤ` by that bridge.
-/

namespace Work.Pi6.EMODD

open CategoryTheory

open Work.Pi6

noncomputable section

/-- The `0`-th cup power is the unit class. -/
theorem cpow_zero {R : Type} [CommRing R] {X : Type} [TopologicalSpace X] (x : Coh R X 2) :
    cpow x 0 = one R X := rfl

/-- The recursion step of the cup power: `x^(k+1) = x^k ⌣ x`. -/
theorem cpow_succ {R : Type} [CommRing R] {X : Type} [TopologicalSpace X] (x : Coh R X 2)
    (k : ℕ) : cpow x (k + 1) = cup R X (2 * k) 2 (cpow x k) x := rfl

/-- Homogeneity of `cup` in its first variable. -/
theorem cup_smul_left {R : Type} [CommRing R] {X : Type} [TopologicalSpace X]
    (n m : ℕ) (a : R) (x : Coh R X n) (y : Coh R X m) :
    cup R X n m (a • x) y = a • cup R X n m x y :=
  Work.Cohomology.cupH'_smul_left R (TopCat.toSSet.obj (TopCat.of X)) n m a x y

/-- Homogeneity of `cup` in its second variable. -/
theorem cup_smul_right {R : Type} [CommRing R] {X : Type} [TopologicalSpace X]
    (n m : ℕ) (a : R) (x : Coh R X n) (y : Coh R X m) :
    cup R X n m x (a • y) = a • cup R X n m x y :=
  Work.Cohomology.cupH'_smul_right R (TopCat.toSSet.obj (TopCat.of X)) n m a x y

/-- **The two elementary laws for cup powers `Work.Pi6.cpow`.**  For a commutative ring `R`, a continuous map `f : X → Y` and a class `w : H²(Y;R)` the `k`-th cup power (`Work.Pi6.cpow`) is natural, `f^*(w^k) = (f^* w)^k`, and it is homogeneous, `(a·w)^k = a^k·w^k`.
(Route: `Work.Pi6.cpow` is defined by `cpow w 0 = 1` and `cpow w (k+1) = cup (cpow w k) w`; naturality follows from the naturality of the cup product `Work.Cohomology.cupNaturalH` and of the unit `Work.Serre.cohMap_oneH`, homogeneity from the `R`-bilinearity of `cup` (`Work.Cohomology.cupBilinear`) by induction on `k`.) -/
theorem cpowLaws (R : Type) [CommRing R] :
    (∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
        (w : Work.Pi6.Coh R Y 2) (k : ℕ),
        Work.Pi6.cpow ((Work.Pi6.cmap R f 2).hom w) k
          = (Work.Pi6.cmap R f (2 * k)).hom (Work.Pi6.cpow w k)) ∧
      (∀ {X : Type} [TopologicalSpace X] (a : R) (w : Work.Pi6.Coh R X 2) (k : ℕ),
        Work.Pi6.cpow (a • w) k = a ^ k • Work.Pi6.cpow w k) := by
  constructor
  · -- naturality of the cup power
    intro X Y _ _ f w k
    induction k with
    | zero =>
        rw [cpow_zero (x := (cmap R f 2).hom w), cpow_zero (x := w)]
        exact (Work.Serre.cohMap_oneH R f).symm
    | succ k ih =>
        calc cpow ((cmap R f 2).hom w) (k + 1)
            = cup R X (2 * k) 2 (cpow ((cmap R f 2).hom w) k) ((cmap R f 2).hom w) :=
                cpow_succ _ _
          _ = cup R X (2 * k) 2 ((cmap R f (2 * k)).hom (cpow w k)) ((cmap R f 2).hom w) := by
                rw [ih]
          _ = (cmap R f (2 * (k + 1))).hom (cpow w (k + 1)) :=
                (Work.Cohomology.cupNaturalH R (TopCat.ofHom f) (2 * k) 2 (cpow w k) w).symm
  · -- homogeneity of the cup power
    intro X _ a w k
    induction k with
    | zero =>
        rw [cpow_zero (x := a • w), cpow_zero (x := w)]
        rw [pow_zero, one_smul]
    | succ k ih =>
        calc cpow (a • w) (k + 1)
            = cup R X (2 * k) 2 (cpow (a • w) k) (a • w) := cpow_succ _ _
          _ = cup R X (2 * k) 2 (a ^ k • cpow w k) (a • w) := by rw [ih]
          _ = a ^ k • cup R X (2 * k) 2 (cpow w k) (a • w) :=
                cup_smul_left (2 * k) 2 (a ^ k) (cpow w k) (a • w)
          _ = a ^ k • (a • cup R X (2 * k) 2 (cpow w k) w) := by
                rw [cup_smul_right (2 * k) 2 a (cpow w k) w]
          _ = a ^ (k + 1) • cup R X (2 * k) 2 (cpow w k) w := by
                rw [smul_smul, pow_succ]

/-- **The ℤ-spelled homogeneity law.**  In a consumer's file at `R = ℤ` the notation `a • w`
resolves to the `ZSMul.toSMul` action on the cohomology module, whereas `cpowLaws ℤ` is stated with
the action inherited from the `Module ℤ` structure; the two agree by `int_smul_eq_zsmul`.  This is
the version matching the consumer's spelling, so that a goal written as
`cpow (a • w) k = a ^ k • cpow w k` (with `a : ℤ`) is closed by `cpow_smul_int a w k`. -/
theorem cpow_smul_int {X : Type} [TopologicalSpace X] (a : ℤ) (w : Coh ℤ X 2) (k : ℕ) :
    cpow (a • w) k = a ^ k • cpow w k := by
  have h := (cpowLaws ℤ).2 (X := X) a w k
  rw [show (a • w : Coh ℤ X 2)
        = (inferInstance : Module ℤ (Coh ℤ X 2)).smul a w from (int_smul_eq_zsmul _ a w).symm,
      show (a ^ k • cpow w k : Coh ℤ X (2 * k))
        = (inferInstance : Module ℤ (Coh ℤ X (2 * k))).smul (a ^ k) (cpow w k) from
        (int_smul_eq_zsmul _ (a ^ k) (cpow w k)).symm]
  exact h

end

end Work.Pi6.EMODD
