/-
# The kernel of the non-split torus in `PGL(2,F)`

Let `c ∈ F` be a non-square.  The quadratic algebra `A = F[X]/(X²-c)` is a field, and any
`B ∈ GL(2,F)` with `B * B = c • 1` realises `A` as an `F`-subalgebra of `M₂(F)` via
`torusAlgHom B c hB : A →+* M₂(F)`, `X ↦ B` (irreducible, since `c` is a non-square).

Composing `torusGL = Units.map (torusAlgHom …)` with the projection `GL(2,F) → PGL(2,F)` and
with the faithful Möbius action of `PGL(2,F)` on `ℙ¹(F)` produces the permutation
representation `torusPerm B c hB` of `Aˣ`.

The kernel of this representation is computed here: it consists exactly of the *scalar* units
of `A`, i.e. of the image of `Fˣ` under `AdjoinRoot.of`.  The two inputs are

* `pglHom` is injective (`Work.AUTL2.Aut.pglHomInjective`), so `torusPerm u = 1` forces
  `mk (torusGL u) = 1`, i.e. `torusGL u` is a scalar matrix `v • 1` (`v : Fˣ`);
* `torusAlgHom` is injective (`torusAlgHom_injective`, using that `¬ IsSquare c` makes
  `X² - c` irreducible), so `torusAlgHom u = v • 1 = torusAlgHom (of v)` gives `u = of v`.

The reverse inclusion is `torusAlgHom (of v) = v • 1`, i.e. `torusGL (of v)` is a scalar
matrix.
-/
import Mathlib
import Submission.Work.DSTR.M110.nonsplitAux
-- `Work.AUTL2.Aut.pglHomInjective` is available transitively, via `Aut.pglIndex`.

open Polynomial Matrix

namespace Work.DSTR.M110

/-- A scalar matrix equals the corresponding scalar multiple of the identity. -/
private lemma scalar_fin_two_eq_smul_one {F : Type*} [Field F] (a : F) :
    (Matrix.scalar (Fin 2) a : Matrix (Fin 2) (Fin 2) F) = a • 1 := by
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

/-- The matrix underlying `torusGL u` is `torusAlgHom u`. -/
private lemma coe_torusGL {F : Type*} [Field F] (B : Matrix.GeneralLinearGroup (Fin 2) F) (c : F)
    (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = c • 1)
    (u : (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C c : Polynomial F))ˣ) :
    ((torusGL B c hB u : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      torusAlgHom B c hB u := by
  simp only [torusGL, Units.coe_map]
  rfl

/-- **The kernel of the non-split torus permutation representation.**  For a matrix
`B ∈ GL(2,F)` with `B * B = c • 1` and `c` a non-square, the units of `F[X]/(X²-c)` acting
trivially on `ℙ¹(F)` are exactly the scalar units, i.e. the image of `Fˣ` under
`AdjoinRoot.of`. -/
theorem kerTorusPerm (F : Type*) [Field F] [DecidableEq F] (B : Matrix.GeneralLinearGroup (Fin 2) F)
    (c : F) (hB : (B : Matrix (Fin 2) (Fin 2) F) * B = c • 1) (hc : ¬ IsSquare c) :
    (Work.DSTR.M110.torusPerm B c hB).ker =
      (Units.map (AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C c : Polynomial F)).toMonoidHom).range := by
  ext u
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · -- `u` acts trivially, hence `torusGL u` is a scalar matrix.
    intro hu
    rw [torusPerm_apply] at hu
    have h2 : Matrix.ProjGenLinGroup.mk (torusGL B c hB u) = 1 :=
      Work.AUTL2.Aut.pglHomInjective F (by rw [hu, map_one])
    have h3 : torusGL B c hB u ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) :=
      Matrix.ProjGenLinGroup.mk_eq_one.mp h2
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] at h3
    obtain ⟨v, hv⟩ := h3
    refine ⟨v, ?_⟩
    -- `torusAlgHom u = v • 1`, and `torusAlgHom (of v) = v • 1`; injectivity gives `u = of v`.
    have hmat : torusAlgHom B c hB
        (u : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C c : Polynomial F)) = (v : F) • 1 := by
      rw [← coe_torusGL B c hB u, ← congrArg Units.val hv,
        Matrix.GeneralLinearGroup.coe_scalar, scalar_fin_two_eq_smul_one]
    apply Units.ext
    change (AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C c : Polynomial F)) ↑v =
      (u : AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C c : Polynomial F))
    refine torusAlgHom_injective B c hB hc ?_
    rw [← AdjoinRoot.algebraMap_eq, torusAlgHom_of]
    exact hmat.symm
  · -- A scalar unit acts trivially, since `torusAlgHom (of v) = v • 1` is a scalar matrix.
    rintro ⟨v, rfl⟩
    rw [torusPerm_apply]
    have hgl : torusGL B c hB
        (Units.map (AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C c : Polynomial F)).toMonoidHom v) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) v := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar]
      change torusAlgHom B c hB
        (AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C c : Polynomial F) ↑v) =
        Matrix.scalar (Fin 2) ↑v
      rw [← AdjoinRoot.algebraMap_eq, torusAlgHom_of, scalar_fin_two_eq_smul_one]
    rw [hgl, Matrix.ProjGenLinGroup.mk_scalar, map_one]

end Work.DSTR.M110
