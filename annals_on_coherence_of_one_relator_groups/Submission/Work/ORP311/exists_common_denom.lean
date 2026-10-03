/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (JZLA20 Proposition 3.11 in the concrete `U(G)`)

# Common denominators (node B2 of `P311_DESIGN_LEAD.md`)

Let `G` be countable, `N ≤ G` a subgroup and `A ∈ Mₙ(U(G))` a matrix whose entries all lie in
the image of the inclusion `liftUN N : U(↥N) → U(G)`.  Then there is a single denominator
`e ∈ N(↥N)` which is a non-zero-divisor and numerators `B ∈ Mₙ(N(↥N))` with

`numG G (Φ_N e) * A i j = numG G (Φ_N (B i j))`   for all `i j`,

i.e. `numG G (Φ_N e) * A` is "integral" (lies in the image of `N(↥N)` under the diagonal
embedding followed by `numG G`).

The proof is the same clearing-of-denominators as
`Work.ORVonNeumann.Rep.linnell_common_denom`: each entry is written as a left fraction
`a /ₒ s` in the Ore localisation `U(↥N)`, the Ore condition
`Work.ORVonNeumann.Rep.oreCommonDenom` produces a common denominator `e`, and the defining
`numerator` property of the universal lift converts the resulting equation in `U(↥N)` into an
equation in `U(G)`.
-/
import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.closureCN_subset_range_liftUN
import Submission.Work.ORP311.PhiN_mapsTo
import Submission.Work.ORVonNeumann.Rep.oreCommonDenom

set_option autoImplicit false

namespace Work.ORP311

open Work.ORVonNeumann

/-! ## The numerator compatibility of `liftUN` -/

/-- The fourth component of the specification of `liftUN N` (the `choose_spec` of
`Work.ORVonNeumann.VonNeumannAlgebra.exists_liftU_of_diagHom`): the lift sends the numerator
map `N(↥N) →+* U(↥N)` to the composite of the diagonal embedding `Φ_N` with the numerator map
`N(G) →+* U(G)`. -/
theorem P311.liftUN_numG {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (N : Subgroup G)
    (b : (Rep.countableGroupVonNeumann (G := ↥N)).N) :
    P311.liftUN N (VonNeumannAlgebra.numOf (Rep.countableGroupVonNeumann (G := ↥N)) b) =
      P311.numG G (P311.PhiN N b) :=
  ((VonNeumannAlgebra.exists_liftU_of_diagHom N (P311.cosetDataN N) (P311.PhiN N)
    (P311.PhiN_spec N).2.1 (P311.PhiN_spec N).2.2.1 (P311.PhiN_spec N).2.2.2).choose_spec
    ).2.2.2 b

/-! ## A common denominator for finitely many elements of `U(G)` -/

/-- **A common denominator in a group von Neumann algebra.**  Given finitely many elements
`d i` of `U(G)`, there are a non-zero-divisor `e ∈ N(G)` and numerators `b i ∈ N(G)` with
`numOf e * d i = numOf (b i)` for all `i`.

This is the Ore condition at the non-zero-divisors: write `d i = a i /ₒ s i` and pass to a
common left multiple `e = t i * s i` of the denominators. -/
private theorem exists_common_denom_aux {G : Type*} [Group G] (D : GroupVonNeumannAlgebra G)
    {m : ℕ} (d : Fin m → D.affiliated) :
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

/-! ## The main result -/

theorem exists_common_denom {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (N : Subgroup G) (n : ℕ) (A : Matrix (Fin n) (Fin n) (Work.ORP311.concreteEnvelope G).U) (hA : ∀ i j, A i j ∈ Set.range (Work.ORP311.P311.liftUN N)) : ∃ e : ↥(Work.ORVonNeumann.groupVonNeumann ↥N), e ∈ nonZeroDivisors ↥(Work.ORVonNeumann.groupVonNeumann ↥N) ∧ ∃ B : Matrix (Fin n) (Fin n) ↥(Work.ORVonNeumann.groupVonNeumann ↥N), ∀ i j, Work.ORP311.P311.numG G (Work.ORP311.P311.PhiN N e) * A i j = Work.ORP311.P311.numG G (Work.ORP311.P311.PhiN N (B i j)) := by
  classical
  -- Each entry of `A` comes from `U(↥N)`.
  choose x hx using hA
  -- Flatten the index set to `Fin (n * n)`.
  let X : Fin (n * n) → (Rep.countableGroupVonNeumann (G := ↥N)).affiliated :=
    fun k => x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  -- Clear denominators in `U(↥N)`.
  obtain ⟨e, b, hb⟩ :=
    exists_common_denom_aux (Rep.countableGroupVonNeumann (G := ↥N)) X
  refine ⟨show ↥(groupVonNeumann ↥N) from (e : (Rep.countableGroupVonNeumann (G := ↥N)).N),
    show (e : (Rep.countableGroupVonNeumann (G := ↥N)).N) ∈
      nonZeroDivisors ↥(groupVonNeumann ↥N) from e.2,
    fun i j => show ↥(groupVonNeumann ↥N) from b (finProdFinEquiv (i, j)), ?_⟩
  intro i j
  have h := hb (finProdFinEquiv (i, j))
  have hX : X (finProdFinEquiv (i, j)) = x i j := by
    simp only [X, Equiv.symm_apply_apply]
  rw [hX] at h
  -- Push the equation through `liftUN N` and read it off the numerator compatibility.
  have h' := congrArg (P311.liftUN N) h
  rw [map_mul, P311.liftUN_numG, P311.liftUN_numG, hx i j] at h'
  exact h'

end Work.ORP311
