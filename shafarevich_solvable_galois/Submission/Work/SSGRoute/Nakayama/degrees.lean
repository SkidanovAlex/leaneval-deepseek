import Mathlib.GroupTheory.Solvable
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.Commons.NumberTheory.NumberField.Completion.exists_mulEquiv_artinMap_of_commute
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Tate–Nakayama in the `ℤ`-coefficient case, in *all* degrees

`Commons.NumberTheory.NumberField.Completion.ArtinMap.addEquiv_tateCohomology_of_fundamental_class`
(Tate's theorem for a class formation `(G, C)`) proves

  `Ĥ^{-2}(G, ℤ) ≅ Ĥ^{0}(G, C)`,

i.e. the `i = 0` instance of the isomorphism `Ĥ^{i}(G, ℤ) ≅ Ĥ^{i+2}(G, C)` given by cup product with
the fundamental class `α`.  Its proof, however, only uses the two short exact sequences

* `AShortZ : 0 → C → Sprint → I → 0`  (`Sprint` acyclic, `I = augKer ⊆ ℤ[G]`),
* `IShort  : 0 → I → ℤ[G] → ℤ → 0`    (`ℤ[G]` acyclic),

through the connecting isomorphism `Ĥ^{r}(X₃) ≅ Ĥ^{r+1}(X₁)` of a short exact sequence with acyclic
middle, at two *arbitrary* degrees `r` and `r+1`.  Composing the two at `r = i` and `r = i+1`
therefore yields the isomorphism in *every* degree `i`, with no extra input: this file records that
generalisation.

The `i = 0` case is the base of the coefficient descent of Tate–Nakayama with arbitrary
coefficients (Milne, *Arithmetic Duality Theorems*, Theorem 0.2), which is the gateway of the local
Tate pairing `E7`/`G1` of the Shafarevich project (see
`Submission/Work/SSGRoute/PTembedding/tateNakayama_general.lean`).

Everything here is a corollary of proved material; no new axiom is introduced.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

open CategoryTheory

namespace Work.SSGRoute.Nakayama

open Commons.RepresentationTheory.TateCohomology

/-- **Tate–Nakayama with `ℤ`-coefficients, in every degree.**  For a finite solvable group `G`, a
`G`-module `C` with `H¹(H,C) = 0` and `|H²(H,C)| = |H|` for every subgroup `H ≤ G`, and a
fundamental class `α ∈ H²(G,C)` of order `|G|`, the groups `Ĥ^{i}(G, ℤ)` and `Ĥ^{i+2}(G, C)` are
isomorphic for every `i ∈ ℤ` (this is the map given by cup product with `α`). -/
theorem tateNakayama_int {G : Type} [Group G] [Fintype G] [Group.IsSolvable G]
    (C : Rep.{0,0,0} ℤ G)
    (h1 : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype C) 1))
    (h2 : ∀ H : Subgroup G, Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (α : groupCohomology C 2) (hα : addOrderOf α = Nat.card G) (i : ℤ) :
    Nonempty (tateCohomology (Rep.trivial ℤ G ℤ) i ≃+ tateCohomology C (i + 2)) := by
  obtain ⟨z, hzα, hz⟩ := NU.exists_normalized_cocycle C α
  -- The splitting module `Sprint = A(C)` of a normalised cocycle representing `α` is acyclic.
  have hacyc := NU.subsingleton_tateCohomology_Sprint C z hz α hzα hα h1 h2
  -- `0 → C → Sprint → I → 0`:  `Ĥ^{i+1}(I) ≅ Ĥ^{i+2}(C)`.
  obtain ⟨e2⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_iso_of_acyclic_middle_of_subsingleton
      (NU.AShortZ C z hz) (NU.AShortZ_shortExact C z hz) (i + 1) (hacyc (i + 1)) (hacyc (i + 1 + 1))
  -- `0 → I → ℤ[G] → ℤ → 0`:  `Ĥ^{i}(ℤ) ≅ Ĥ^{i+1}(I)`.
  obtain ⟨e1⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_iso_of_acyclic_middle_of_subsingleton
      (NU.IShort (G := G)) (NU.IShort_shortExact (G := G)) i
      (NU.subsingleton_tateCohomology_leftRegular G i)
      (NU.subsingleton_tateCohomology_leftRegular G (i + 1))
  rw [show i + 2 = i + 1 + 1 by ring]
  exact ⟨(e1.trans e2).toAddEquiv⟩

/-- Cardinality form of `tateNakayama_int`. -/
theorem natCard_tateCohomology_eq_int {G : Type} [Group G] [Fintype G] [Group.IsSolvable G]
    (C : Rep.{0,0,0} ℤ G)
    (h1 : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype C) 1))
    (h2 : ∀ H : Subgroup G, Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (α : groupCohomology C 2) (hα : addOrderOf α = Nat.card G) (i : ℤ) :
    Nat.card (tateCohomology (Rep.trivial ℤ G ℤ) i) = Nat.card (tateCohomology C (i + 2)) := by
  obtain ⟨e⟩ := tateNakayama_int C h1 h2 α hα i
  exact Nat.card_congr e.toEquiv

end Work.SSGRoute.Nakayama
