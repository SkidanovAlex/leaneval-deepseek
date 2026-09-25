import Mathlib
import Submission.NK.ShimizuRank.Basic

namespace NK.ShimizuRank

/-
**`rankGamma K K ℓ = 0`**: the ℓ-adic abelianisation of the trivial extension `K/K` is trivial.  This
is a small computation supporting the (loud) report that the sibling chapter's input
`NK.Reconstruct.RankFormulaInput K K' ℓ δ` is *unsatisfiable when `K'` is too small*, e.g. for
`K' = K`: its `formula` field asserts `0 = rComplex K + 1 + δ ≥ 1`.

`NK.Reconstruct.FrobLevel K K` (`Submission/Work/Reconstruct/Gamma.lean`) is the type of finite
normal number-field levels `L` with `K ⊆ L ⊆ K`; every such `L.L : IntermediateField K K` equals
`⊥` (equivalently `⊤`) and `↥L.L` is `K`-isomorphic to `K`, so `Gal(↥L.L/K)` is a subsingleton, hence
so is `NK.Reconstruct.LevelEllPart L.L ℓ`.  A product of subsingletons is a subsingleton, so the
projective limit `NK.Reconstruct.Gamma K K ℓ` (a subgroup of `∀ L : FrobLevel K K,
LevelEllPart L.L ℓ`) is a subsingleton.  Then `Additive (Gamma K K ℓ)` is a subsingleton, so its
quotient `GammaTF K K ℓ = Γ_K ⧸ GammaTorsion` is a subsingleton, and
`rankGamma K K ℓ = Module.finrank (PadicInt ℓ) (GammaTF K K ℓ) = 0`.
-/

/-! ## The trivial extension `K/K`

Every intermediate field of `K/K` is `⊥` (equivalently `⊤`), because the canonical algebra map
`K → K` is the identity: as subsets of `K`, both `⊥` and `⊤` are all of `K`. -/

/-- **Every intermediate field of `K/K` lies below `⊥`** (and hence equals it).  As a set inside `K`,
`⊥` is the range of the algebra map `K → K`, which is all of `K`. -/
theorem le_bot_of_intermediateField_self (K : Type*) [Field K] (E : IntermediateField K K) :
    E ≤ ⊥ := by
  intro x _
  rw [IntermediateField.mem_bot]
  exact ⟨x, Algebra.algebraMap_self_apply x⟩

/-- **The Galois group of the trivial extension is trivial.**  The map `K → ↥E` is surjective
(for `E : IntermediateField K K`), so a `K`-algebra automorphism of `↥E` is determined by its
values on the image of `K`, hence is the identity. -/
theorem subsingleton_gal_self (K : Type*) [Field K] (E : IntermediateField K K) :
    Subsingleton Gal(↥E/K) := by
  have hsurj : Function.Surjective (algebraMap K ↥E) := by
    intro x
    obtain ⟨a, ha⟩ := le_bot_of_intermediateField_self K E x.2
    refine ⟨a, Subtype.ext ?_⟩
    rw [← IntermediateField.algebraMap_apply E (algebraMap K ↥E a),
      ← IsScalarTower.algebraMap_apply K ↥E K a]
    exact ha
  refine ⟨fun f g => AlgEquiv.ext fun x => ?_⟩
  obtain ⟨a, rfl⟩ := hsurj x
  rw [f.commutes a, g.commutes a]

/-- **The ℓ-part of the abelianisation of a trivial level is trivial.**  In the trivial extension
`K/K` the Galois group is a subsingleton by `subsingleton_gal_self`, hence so is its
abelianisation `LevelAbelianization E` and every subgroup of it, in particular
`LevelEllPart E ℓ = ellPart (LevelAbelianization E) ℓ`. -/
instance instSubsingletonLevelEllPartSelf (K : Type*) [Field K] (ℓ : ℕ)
    (E : IntermediateField K K) :
    Subsingleton (NK.Reconstruct.LevelEllPart (K := K) (K' := K) E ℓ) := by
  haveI hG : Subsingleton Gal(↥E/K) := subsingleton_gal_self K E
  have hq : Subsingleton (Gal(↥E/K) ⧸ commutator Gal(↥E/K)) := inferInstance
  haveI hA : Subsingleton (NK.Reconstruct.LevelAbelianization (K := K) (K' := K) E) := hq
  exact inferInstance

/-- **`rankGamma K K ℓ = 0`**: the ℓ-adic abelianisation of the trivial extension `K/K` is trivial,
so its `ℤ_ℓ`-rank vanishes.

Every finite normal level `L` of `K/K` is `⊥`, so `Γ_{L,ℓ}` is trivial and the projective limit
`Γ_K = Gamma K K ℓ` — a subgroup of the product of the `Γ_{L,ℓ}` over the levels `L` — is a
subsingleton.  Passing to the torsion-free quotient (`GammaTF`) and to the `ℤ_ℓ`-rank gives `0`. -/
theorem rankGamma_self (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime] :
    NK.Reconstruct.rankGamma K K ℓ = 0 := by
  classical
  haveI hL : ∀ L : NK.Reconstruct.FrobLevel K K,
      Subsingleton (NK.Reconstruct.LevelEllPart (K := K) (K' := K) L.L ℓ) :=
    fun L => instSubsingletonLevelEllPartSelf K ℓ L.L
  haveI : Subsingleton (NK.Reconstruct.Gamma K K ℓ) :=
    ⟨fun f g => Subtype.ext (Subsingleton.elim f.1 g.1)⟩
  haveI : Subsingleton (NK.Reconstruct.GammaTF (K := K) (K' := K) ℓ) := inferInstance
  exact Module.finrank_zero_of_subsingleton

end NK.ShimizuRank
