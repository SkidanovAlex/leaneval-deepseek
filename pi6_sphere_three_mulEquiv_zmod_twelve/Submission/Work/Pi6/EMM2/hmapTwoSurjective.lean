import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Stems.HurewiczMapNatural
import Submission.Work.Stems.HurewiczFirstDegree
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `π₂`-surjectivity implies `H₂`-surjectivity (EMM2: the reduction `K(ℤ,2) → K(ℤ/2,2)`)

The `K(ℤ,2)`-model of the EMM2 forcing argument (`Pi6/EMM2/kZmodel`) produces a reduction map
`r : KZ → X` from a `K(ℤ,2)` range model onto a `K(ℤ/2,2)` range model, together with the two
facts

* `Surjective (πmap r 1 k₀)`, i.e. `r_* : π₂(KZ) → π₂(X)` is onto (`Work.StemsB.πmap f n` is the
  map of `πₙ₊₁`, so the index `1` is degree `2`), and
* `Surjective (hmap ℤ r 2).hom`, i.e. `r_* : H₂(KZ;ℤ) → H₂(X;ℤ)` is onto.

This file derives the second from the first.  Both spaces have trivial `π₀` and `π₁` (they are
`K(·,2)` range models -- here `2 = m`, `hm : 0 < 2`, and both `0, 1 < 2`), so the integral Hurewicz
theorem in the first non-vanishing degree applies in degree `2`:

`Work.Stems.hurewicz_first_degree : π₂(Y,y₀) ≅ H₂(Y;ℤ)` for a `1`-connected `Y`

and naturality of the Hurewicz map (`Work.Stems.hurewiczMap_natural`) gives the commutative square

```
  π₂(KZ) --r_*--> π₂(X)
    |               |
  H≤₂              H≤₂
    v               v
  H₂(KZ) --r_*--> H₂(X)
```

so surjectivity at the top forces surjectivity at the bottom.

The threshold hypothesis `hN : 3 ≤ N` of the interface is not needed for this implication (only
`π₀`, `π₁` of the two spaces are used, and those are killed by `0, 1 < 2` alone); it is kept
because the caller states it uniformly for the whole area.
-/

open scoped Topology

set_option linter.unusedVariables false

namespace Work.Pi6.EMM2

/-- `Work.StemsB.πmap f n` (the map `πₙ₊₁(X,x) → πₙ₊₁(Y,f x)`, defined for the shifted index) is
`HomotopyGroup.map f`.  Both are `Quotient.map` of the postcomposition of a cube by `f`. -/
theorem πmap_eq_homotopyGroupMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) (x : X) (a : HomotopyGroup (Fin (n + 1)) X x) :
    Work.StemsB.πmap f n x a = HomotopyGroup.map f a := by
  induction a using Quotient.inductionOn with
  | h p => rfl

/-- **`π₂`-surjectivity implies `H₂`-surjectivity.**  If `g : A → B` induces a surjection on `π₂`
and `A`, `B` are `K(·,2)` range models (so their `π₀` and `π₁` vanish), then `g` induces a
surjection on `H₂(-;ℤ)`. -/
theorem hmapTwoSurjective {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (g : C(A, B))
    (a₀ : A) (N : ℕ) (hN : 3 ≤ N)
    (hA : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N A a₀)
    (hB : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N B (g a₀))
    (hsurj : Function.Surjective (Work.StemsB.πmap g 1 a₀)) :
    Function.Surjective (Work.Pi6.hmap ℤ g 2).hom := by
  -- Both spaces are `1`-connected: `π₀`, `π₁` are the `πᵢ` with `i < 2`, `i ≠ 2`.
  have hsubA : ∀ i : ℕ, i < 2 → Subsingleton (HomotopyGroup (Fin i) A a₀) :=
    fun i hi => hA.2 i (by omega) (Or.inl hi)
  have hsubB : ∀ i : ℕ, i < 2 → Subsingleton (HomotopyGroup (Fin i) B (g a₀)) :=
    fun i hi => hB.2 i (by omega) (Or.inl hi)
  -- The integral Hurewicz theorem in degree `2` for both spaces.
  have hbioA := Work.Stems.hurewicz_first_degree 2 (by norm_num) a₀ hsubA
  have hbioB := Work.Stems.hurewicz_first_degree 2 (by norm_num) (g a₀) hsubB
  intro y
  -- Lift `y ∈ H₂(B;ℤ)` to `b ∈ π₂(B)` and `b` to `a ∈ π₂(A)`, then push `a` down to `H₂(A;ℤ)`.
  obtain ⟨b, hb⟩ := hbioB.2 y
  obtain ⟨a, ha⟩ := hsurj b
  refine ⟨Work.Stems.hurewiczMapN 2 (by norm_num) a₀ a, ?_⟩
  -- Naturality of the Hurewicz map (Hurewicz of `g ∘ a` computed on either side).
  have hnat : Work.Stems.hurewiczMapN 2 (by norm_num) (g a₀) (HomotopyGroup.map g a)
      = (Work.Pi6.hmap ℤ g 2).hom (Work.Stems.hurewiczMapN 2 (by norm_num) a₀ a) :=
    Work.Stems.hurewiczMap_natural 2 (by norm_num) g (x₀ := a₀) a
  rw [← hnat, ← πmap_eq_homotopyGroupMap g 1 a₀ a, ha, hb]

end Work.Pi6.EMM2
