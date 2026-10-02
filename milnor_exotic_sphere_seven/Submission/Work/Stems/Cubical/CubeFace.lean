import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Faces of the cube `I^n`, and the cubical singular `n`-chains

Singular `n`-cubes in `X` are the continuous maps `I^n → X`; the `i`-th face pair of an
`(n+1)`-cube is obtained by freezing the `i`-th coordinate at `0` or `1`.  The cubical `n`-chains
are the free `ℤ`-module on the `n`-cubes, with differential the alternating sum of the faces.
-/

open scoped unitInterval Topology

namespace Work.Stems.Cubical

/-- The cube `I^n`, as a type. -/
abbrev IC (n : ℕ) := Fin n → unitInterval

/-- The `i`-th face inclusion `I^n → I^{n+1}` (freezing coordinate `i` at `b`). -/
def faceFun {n : ℕ} (i : Fin (n + 1)) (b : unitInterval) : IC n → IC (n + 1) :=
  fun t => @Fin.succAboveCases n (fun _ => unitInterval) i b t

@[simp]
theorem faceFun_apply {n : ℕ} (i : Fin (n + 1)) (b : unitInterval) (t : IC n) :
    faceFun i b t = @Fin.succAboveCases n (fun _ => unitInterval) i b t := rfl

/-- The face inclusion as a continuous map. -/
def faceCM {n : ℕ} (i : Fin (n + 1)) (b : unitInterval) : C(IC n, IC (n + 1)) where
  toFun := faceFun i b
  continuous_toFun := by
    apply Continuous.finInsertNth
    · exact continuous_const
    · exact continuous_id

@[simp]
theorem faceCM_apply {n : ℕ} (i : Fin (n + 1)) (b : unitInterval) (t : IC n) :
    faceCM i b t = faceFun i b t := rfl

/-- The `i`-th face (in direction `b`) of a cube. -/
def faceCube {n : ℕ} {X : Type} [TopologicalSpace X] (i : Fin (n + 1)) (b : unitInterval)
    (s : C(IC (n + 1), X)) : C(IC n, X) :=
  s.comp (faceCM i b)

/-- The cubical `n`-chains of `X`: finite `ℤ`-linear combinations of `n`-cubes. -/
abbrev Cub (n : ℕ) (X : Type) [TopologicalSpace X] := C(IC n, X) →₀ ℤ

/-- The cubical differential: the alternating sum of the faces. -/
noncomputable def cubD (n : ℕ) (X : Type) [TopologicalSpace X] :
    Cub (n + 1) X →ₗ[ℤ] Cub n X :=
  Finsupp.linearCombination ℤ
    (fun s : C(IC (n + 1), X) => ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
      (Finsupp.single (faceCube i 0 s) (1 : ℤ) - Finsupp.single (faceCube i 1 s) (1 : ℤ)))

@[simp]
theorem cubD_single {n : ℕ} {X : Type} [TopologicalSpace X] (s : C(IC (n + 1), X)) :
    cubD n X (Finsupp.single s 1) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        (Finsupp.single (faceCube i 0 s) (1 : ℤ) - Finsupp.single (faceCube i 1 s) (1 : ℤ)) := by
  simp [cubD]

end Work.Stems.Cubical
