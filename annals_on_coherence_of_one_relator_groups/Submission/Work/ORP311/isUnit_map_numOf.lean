/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (JZLA20 Proposition 3.11 in the concrete `U(G)`)

# Step 2 of the P311 route: injectivity of `matOp Z` makes `num(Z)` a unit

Let `G` be a countable group, `N(G) = ρ(G)' ⊆ B(ℓ²(G))` its group von Neumann algebra and
`U(G) = N(G)[(nzd)⁻¹]` its Ore localisation at the non-zero-divisors (`Work.ORVonNeumann`).
Write `numG G : N(G) →+* U(G)` for the structure map (`Work.ORP311.P311.numG`).

The main result of this file is

* `Work.ORP311.isUnit_map_numOf`: for a square matrix `Z` over `N(G)` whose matrix operator
  `Work.ORVonNeumann.Rep.matOp Z` is injective, the entrywise image `Z.map (numG G)` is a
  **unit** of `Mₙ(U(G))`.

This is Step 2 of `P311_DESIGN_LEAD.md`: from injectivity of `matOp Z` to a unit in the
localisation.

## The argument

* `matOp` is faithful (`Work.ORP311.matOp_eq_zero_iff`) and multiplicative
  (`Work.ORVonNeumann.Rep.vnMatOpMul`), so injectivity of `matOp Z` makes `Z` a two-sided
  non-zero-divisor of `Mₙ(N(G))` (`nzd_left_matOp`, `nzd_right_matOp`; the second uses the
  stability of injectivity under the conjugate transpose,
  `injective_conjTranspose_of_injective`).
* `U(G)` is von Neumann regular (`StarRegularEnvelope.starRegular`), hence so is `Mₙ(U(G))`
  (`Work.ORVonNeumann.Regular.matrix_vonNeumannRegular`).
* `numG G` is the numerator map of the Ore localisation, so it is injective
  (`OreLocalization.numeratorHom_inj`) and sends denominators to units
  (`OreLocalization.numerator_isUnit`).
* Every `W ∈ Mₙ(U(G))` can be cleared to a single left denominator `e ∈ nzd`:
  `Matrix.scalar (Fin n) (numG G e) * W` is `b.map (numG G)` for some `b ∈ Mₙ(N(G))`
  (`exists_denom_mat_s`, from the Ore condition `Work.ORVonNeumann.Rep.oreCommonDenom`).
  Comparing with `W * numG Z = 0` then forces `b * Z = 0`, hence `b = 0` and `W = 0`:
  `numG Z` is a right non-zero-divisor.
* The conjugate-transpose argument (`numG_conjTranspose_s`, from
  `VonNeumannAlgebra.affiliated_star_numerator`) reduces `numG Z * W = 0` to `W = 0` as well.

In a von Neumann regular ring a two-sided non-zero-divisor is a unit
(`Work.ORP311.isUnit_of_regular_of_nzd`), which concludes the proof.
-/
import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.isUnit_of_regular_of_nzd
import Submission.Work.ORP311.matOp_eq_zero_iff
import Submission.Work.ORP311.injective_conjTranspose_of_injective
import Submission.Work.ORVonNeumann.VonNeumannAlgebra.rankAffiliated
import Submission.Work.ORVonNeumann.Regular.matrix_vonNeumannRegular

set_option synthInstance.maxHeartbeats 200000

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.ORP311

open Work.ORVonNeumann

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-! ## Generic facts about the numerator map `numOf` of an Ore localisation -/

/-- The numerator map `N(G) →+* U(G)` of the Ore localisation at the non-zero-divisors is
injective, because the set of non-zero-divisors is contained in the *left* non-zero-divisors
(`OreLocalization.numeratorHom_inj`). -/
theorem numOf_injective_g (D : GroupVonNeumannAlgebra G) :
    Function.Injective (VonNeumannAlgebra.numOf D) := by
  letI := D.oreSet
  exact OreLocalization.numeratorHom_inj (S := nonZeroDivisors D.N) inf_le_left

/-- The numerator of a non-zero-divisor is a unit of the localisation. -/
theorem numOf_isUnit_denom_g (D : GroupVonNeumannAlgebra G) (s : nonZeroDivisors D.N) :
    IsUnit (VonNeumannAlgebra.numOf D (s : D.N)) := by
  letI := D.oreSet
  exact OreLocalization.numerator_isUnit s

/-- **A common left denominator for finitely many elements of `U(G)`.**  For `d : Fin m → U(G)`
there are a single non-zero-divisor `e ∈ N(G)` and numerators `b : Fin m → N(G)` with
`numOf e * d i = numOf (b i)` for all `i`.

This is the Ore condition for the non-zero-divisors: write each `d i` as a left fraction and
pass to a common left multiple of the denominators
(`Work.ORVonNeumann.Rep.oreCommonDenom`). -/
theorem common_denom_g (D : GroupVonNeumannAlgebra G) {m : ℕ} (d : Fin m → D.affiliated) :
    ∃ (e : nonZeroDivisors D.N) (b : Fin m → D.N),
      ∀ i, VonNeumannAlgebra.numOf D e * d i = VonNeumannAlgebra.numOf D (b i) := by
  classical
  have hrep : ∀ i, ∃ (a : D.N) (s : nonZeroDivisors D.N), d i = a /ₒ s := fun i =>
    OreLocalization.ind (β := fun y : D.affiliated =>
      ∃ (a : D.N) (s : nonZeroDivisors D.N), y = a /ₒ s) (fun r t => ⟨r, t, rfl⟩) (d i)
  choose a s hs using hrep
  obtain ⟨e, t, b, _hte, hbs⟩ := Work.ORVonNeumann.Rep.oreCommonDenom
    (S := nonZeroDivisors D.N) le_rfl a s
  refine ⟨e, b, fun i => ?_⟩
  rw [hs i, hbs i, VonNeumannAlgebra.numOf_apply, VonNeumannAlgebra.numOf_apply,
    OreLocalization.numeratorHom_apply, OreLocalization.numeratorHom_apply]
  exact OreLocalization.mul_cancel (R := D.N) (r := b i) (s := e) (t := 1)

/-- **Clearing denominators of a matrix over `U(G)`.**  For every matrix `W` over `U(G)` there
are a non-zero-divisor `e ∈ N(G)` and a matrix `b` over `N(G)` with
`Matrix.scalar (Fin n) (numOf e) * W = b.map (numOf)`.

The matrix identity is entrywise `common_denom_g`. -/
theorem exists_denom_mat_g (D : GroupVonNeumannAlgebra G) {n : ℕ}
    (W : Matrix (Fin n) (Fin n) D.affiliated) :
    ∃ (e : nonZeroDivisors D.N) (b : Matrix (Fin n) (Fin n) D.N),
      Matrix.scalar (Fin n) (VonNeumannAlgebra.numOf D e) * W
        = b.map (VonNeumannAlgebra.numOf D) := by
  classical
  let X : Fin (n * n) → D.affiliated :=
    fun k => W (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  obtain ⟨e, b', hb⟩ := common_denom_g D X
  let b : Matrix (Fin n) (Fin n) D.N := fun i j => b' (finProdFinEquiv (i, j))
  refine ⟨e, b, ?_⟩
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.map_apply]
  have := hb (finProdFinEquiv (i, j))
  simp only [X] at this
  simpa [b] using this

/-! ## The same facts for the concrete model `numG G = numOf (countableModel G)` -/

/-- `numG G` is injective. -/
theorem numG_injective_s : Function.Injective (P311.numG G) := by
  change Function.Injective (VonNeumannAlgebra.numOf (countableModel G))
  letI := (countableModel G).oreSet
  exact OreLocalization.numeratorHom_inj (S := nonZeroDivisors (countableModel G).N) inf_le_left

/-- The numerator of a non-zero-divisor of `N(G)` is a unit of `U(G)`. -/
theorem numG_isUnit_denom_s (e : nonZeroDivisors ↥(groupVonNeumann G)) :
    IsUnit (P311.numG G e) := by
  change IsUnit (VonNeumannAlgebra.numOf (countableModel G)
    (show (countableModel G).N from (e : ↥(groupVonNeumann G))))
  letI := (countableModel G).oreSet
  exact OreLocalization.numerator_isUnit (show nonZeroDivisors (countableModel G).N from e)

/-- Clearing denominators of a matrix over `U(G)`, in terms of `numG G`. -/
theorem exists_denom_mat_s {n : ℕ} (W : Matrix (Fin n) (Fin n) (concreteEnvelope G).U) :
    ∃ (e : nonZeroDivisors ↥(groupVonNeumann G))
      (b : Matrix (Fin n) (Fin n) ↥(groupVonNeumann G)),
      Matrix.scalar (Fin n) (P311.numG G e) * W = b.map (P311.numG G) := by
  obtain ⟨e, b, hb⟩ := exists_denom_mat_g (countableModel G) W
  exact ⟨show nonZeroDivisors ↥(groupVonNeumann G) from e,
    show Matrix (Fin n) (Fin n) ↥(groupVonNeumann G) from b, hb⟩

/-- `numG G` commutes with the involution. -/
theorem numG_star_s (z : ↥(groupVonNeumann G)) :
    star (P311.numG G z) = P311.numG G (star z) :=
  VonNeumannAlgebra.affiliated_star_numerator (countableModel G) z

/-- `numG G` commutes with the conjugate transpose entrywise. -/
theorem numG_conjTranspose_s {n : ℕ} (Z : Matrix (Fin n) (Fin n) ↥(groupVonNeumann G)) :
    (Z.map (P311.numG G)).conjTranspose = (Matrix.conjTranspose Z).map (P311.numG G) := by
  rw [← Matrix.conjTranspose_map (f := ⇑(P311.numG G))
    (fun a => (numG_star_s (G := G) a).symm)]

/-! ## `Z` is a two-sided non-zero-divisor of `Mₙ(N(G))` -/

/-- **Right non-zero-divisor.**  If `matOp Z` is injective and `Z * w = 0` then `w = 0`:
`matOp (Z * w) = matOp Z ∘ matOp w` and `matOp` is faithful. -/
theorem nzd_left_matOp {n : ℕ} (Z : Matrix (Fin n) (Fin n) ↥(groupVonNeumann G))
    (hZ : Function.Injective (Rep.matOp (G := G) Z))
    (w : Matrix (Fin n) (Fin n) ↥(groupVonNeumann G)) (hw : Z * w = 0) : w = 0 := by
  have hcomp : (Rep.matOp (G := G) Z).comp (Rep.matOp (G := G) w) = 0 := by
    rw [← Rep.vnMatOpMul, hw]
    simp [Rep.matOp]
  have hw0 : Rep.matOp (G := G) w = 0 := by
    apply ContinuousLinearMap.ext; intro x
    have h1 : Rep.matOp (G := G) Z (Rep.matOp (G := G) w x) = 0 := by
      have := congrArg (fun T => T x) hcomp; simpa using this
    exact hZ (h1.trans (map_zero _).symm)
  exact (Work.ORP311.matOp_eq_zero_iff (G := G) w).mp hw0

/-- **Left non-zero-divisor.**  If `matOp Z` is injective and `w * Z = 0` then `w = 0`.
Take the conjugate transpose and apply `nzd_left_matOp` to `Zᴴ`, whose operator is injective
by `injective_conjTranspose_of_injective`. -/
theorem nzd_right_matOp {n : ℕ} (Z : Matrix (Fin n) (Fin n) ↥(groupVonNeumann G))
    (hZ : Function.Injective (Rep.matOp (G := G) Z))
    (w : Matrix (Fin n) (Fin n) ↥(groupVonNeumann G)) (hw : w * Z = 0) : w = 0 := by
  have hZ' : Function.Injective (Rep.matOp (G := G) (Matrix.conjTranspose Z)) :=
    Work.ORP311.injective_conjTranspose_of_injective (G := G) Z hZ
  have hw' : Matrix.conjTranspose Z * Matrix.conjTranspose w = 0 := by
    have := congrArg Matrix.conjTranspose hw
    rwa [Matrix.conjTranspose_mul, (Matrix.conjTranspose_zero (m := Fin n) (n := Fin n) (α := ↥(groupVonNeumann G)))] at this
  have h := nzd_left_matOp Z.conjTranspose hZ' (Matrix.conjTranspose w) hw'
  simpa [(Matrix.conjTranspose_zero (m := Fin n) (n := Fin n) (α := ↥(groupVonNeumann G)))] using congrArg Matrix.conjTranspose h

/-! ## `numG Z` is a two-sided non-zero-divisor of `Mₙ(U(G))` -/

/-- If `W * numG Z = 0` in `Mₙ(U(G))` then `W = 0`.  Clear denominators
`numG e • W = b.map numG`, multiply on the right by `numG Z` and use that `b * Z = 0` forces
`b = 0`. -/
theorem num_map_mul_right_s {n : ℕ} (Z : Matrix (Fin n) (Fin n) ↥(groupVonNeumann G))
    (hZ : Function.Injective (Rep.matOp (G := G) Z))
    (W : Matrix (Fin n) (Fin n) (concreteEnvelope G).U)
    (hW : W * Z.map (P311.numG G) = 0) : W = 0 := by
  obtain ⟨e, b, hb⟩ := exists_denom_mat_s (G := G) W
  have h1 : (b.map (P311.numG G)) * (Z.map (P311.numG G)) = 0 := by
    rw [← hb, mul_assoc, hW, mul_zero]
  have h2 : (b * Z).map (P311.numG G) = 0 := by
    rw [Matrix.map_mul, h1]
  have h3 : b * Z = 0 := by
    apply Matrix.ext; intro i j
    apply numG_injective_s (G := G)
    have hh := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at hh
    simpa using hh
  have h4 : b = 0 := nzd_right_matOp (G := G) Z hZ b h3
  have h5 : Matrix.scalar (Fin n) (P311.numG G e) * W = 0 := by
    rw [hb, h4]; simp
  have hE : IsUnit (Matrix.scalar (Fin n) (P311.numG G e)) :=
    (numG_isUnit_denom_s (G := G) e).map (Matrix.scalar (Fin n))
  exact (IsUnit.mul_right_eq_zero hE).mp h5

/-! ## The main theorem -/

/-- **Step 2 of the P311 route.**  If a square matrix `Z` over `N(G)` has injective matrix
operator `matOp Z`, then its image `Z.map (numG G)` is a unit of `Mₙ(U(G))`.

`Mₙ(U(G))` is von Neumann regular, and `numG Z` is a two-sided non-zero-divisor: on the right
by `num_map_mul_right_s`, on the left by taking the conjugate transpose and applying the right
case to the (again injective) `matOp Zᴴ`. -/
theorem isUnit_map_numOf {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ} (Z : Matrix (Fin n) (Fin n) ↥(Work.ORVonNeumann.groupVonNeumann G)) (hZ : Function.Injective (Work.ORVonNeumann.Rep.matOp (G := G) Z)) : IsUnit (Z.map (Work.ORP311.P311.numG G)) := by
  classical
  have hreg : VonNeumannRegular (Matrix (Fin n) (Fin n) (concreteEnvelope G).U) :=
    Work.ORVonNeumann.Regular.matrix_vonNeumannRegular
      ((concreteEnvelope G).starRegular.regular) n
  refine Work.ORP311.isUnit_of_regular_of_nzd hreg ?_ ?_
  · -- `numG Z * W = 0`: conjugate transpose and use the right case for `Zᴴ`.
    intro W hW
    have hZ' : Function.Injective (Rep.matOp (G := G) (Matrix.conjTranspose Z)) :=
      Work.ORP311.injective_conjTranspose_of_injective (G := G) Z hZ
    have hW' : Matrix.conjTranspose W * (Matrix.conjTranspose Z).map (P311.numG G) = 0 := by
      have := congrArg Matrix.conjTranspose hW
      rwa [Matrix.conjTranspose_mul, numG_conjTranspose_s, Matrix.conjTranspose_zero] at this
    have h := num_map_mul_right_s (Matrix.conjTranspose Z) hZ' (Matrix.conjTranspose W) hW'
    simpa using congrArg Matrix.conjTranspose h
  · -- `W * numG Z = 0`: the direct denominator-clearing argument.
    intro W hW
    exact num_map_mul_right_s Z hZ W hW

end Work.ORP311
