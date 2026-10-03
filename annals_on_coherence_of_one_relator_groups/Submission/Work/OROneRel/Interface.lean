/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).
-/
import Submission.Work.OROneRel.Basic

/-!
# One-relator combinatorics: the four classical inputs

This file states, for a relator `r` over a generating type `α`, the four classical theorems of
one-relator group theory that node `N2` of the route design provides, and bundles them into the
`Prop`-valued structure `OneRelatorCombinatorics`.

The four theorems are

* `FreiheitssatzAt r`  -- the Freiheitssatz (Magnus 1930): if `r` is cyclically reduced and `T ⊆ α`
  satisfies `r ∉ ⟨T⟩`, then `F(T) →* ⟨α | r⟩` is injective (so Magnus subgroups are free);
* `MagnusMoldavanskiiAt r` -- the Magnus--Moldavanskii--Masters hierarchy (see `HasMMHierarchy`);
* `WeinbaumAt r` -- Weinbaum's theorem: proper nontrivial subwords of powers of a cyclically reduced
  relator which is not a proper power are nontrivial in `⟨α | r⟩`;
* `KMSTorsionAt r` -- the Torsion theorem of Karrass--Magnus--Solitar: if `r = u ^ l` with `l ≥ 1`
  and `u` not a proper power, then `u` has order exactly `l` in `⟨α | r⟩` and every element of finite
  order is conjugate to a power of `u`.

The unbundled hypotheses `FreiheitssatzAt`, `WeinbaumAt`, `KMSTorsionAt`, `MagnusMoldavanskiiAt` are
useful per-relator (for inductions that supply them level by level); `OneRelatorCombinatorics` is the
global form.  The four named theorems `freiheitssatz`, `magnus_moldavanskii`, `weinbaum`,
`kms_torsion` take `C : OneRelatorCombinatorics` and reproduce the statements of the route design
verbatim.

The *proofs* of these four theorems are the deep combinatorial group theory content (Freiheitssatz,
Weinbaum, Karrass--Magnus--Solitar, the Moldavanskii hierarchy); this subproject proves the algebraic
consequences that the rest of the project consumes, and the special cases that are reachable from
Mathlib (see `Freiheitssatz.lean`, `Terminal.lean`, `Torsion.lean`, `Weinbaum.lean`).
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The Freiheitssatz at the relator `r`: if `r` is cyclically reduced and the generators `T` do not
generate `r` (i.e. `r ∉ ⟨T⟩ ⊆ F(α)`), then the canonical map `F(T) →* ⟨α | r⟩` is injective.  In
particular the *Magnus subgroups* of `⟨α | r⟩` are free. -/
def FreiheitssatzAt (r : FreeGroup α) : Prop :=
  IsCyclicallyReducedRelator r → ∀ T : Set α, r ∉ Subgroup.closure (FreeGroup.of '' T) →
    Function.Injective (presentedGroupMap r T)

/-- Weinbaum's theorem at the relator `r`: for `r` cyclically reduced and not a proper power, any
nontrivial subword of a power of `r` of length shorter than `r` represents a nontrivial element of
`⟨α | r⟩`. -/
def WeinbaumAt (r : FreeGroup α) : Prop :=
  IsCyclicallyReducedRelator r → ¬ IsProperPower r →
    ∀ (k : ℕ) (v : FreeGroup α), IsSubwordOf v (r ^ k) → relatorNorm v < relatorNorm r → v ≠ 1 →
      PresentedGroup.mk ({r} : Set (FreeGroup α)) v ≠ 1

/-- The Torsion theorem of Karrass--Magnus--Solitar at the relator `r`: if `r = u ^ l` with `l ≥ 1`
and `u` not a proper power, then `u` has order exactly `l` in `⟨α | r⟩`, and every element of finite
order in `⟨α | r⟩` is conjugate to a power of `u`. -/
def KMSTorsionAt (r : FreeGroup α) : Prop :=
  ∀ (u : FreeGroup α) (l : ℕ), 1 ≤ l → r = u ^ l → ¬ IsProperPower u →
    orderOf (PresentedGroup.mk ({r} : Set (FreeGroup α)) u) = l ∧
      ∀ g : PresentedGroup ({r} : Set (FreeGroup α)), IsOfFinOrder g →
        ∃ k : ℕ, ∃ c : PresentedGroup ({r} : Set (FreeGroup α)),
          g = c * (PresentedGroup.mk ({r} : Set (FreeGroup α)) u) ^ k * c⁻¹

/-- The Magnus--Moldavanskii hierarchy at the relator `r`. -/
def MagnusMoldavanskiiAt (r : FreeGroup α) : Prop :=
  IsCyclicallyReducedRelator r → r ≠ 1 → HasMMHierarchy α r

/-- `G` is a one-relator group which admits a Magnus--Moldavanskii hierarchy (equivalently, up to
isomorphism, `G = ⟨α | r⟩` for some `r` with `HasMMHierarchy α r`). -/
def HasHierarchy (G : Type u) [Group G] : Prop :=
  ∃ (α : Type u) (r : FreeGroup α), HasMMHierarchy α r ∧
    Nonempty (PresentedGroup ({r} : Set (FreeGroup α)) ≃* G)

/-- The four classical theorems of one-relator group theory, bundled.  This is a `Prop`: it is the
interface that node `N2` exports, and it is consumed by `N4` (virtual torsion-freeness, local
indicability), `N3` (Lyndon's identity theorem), `N7`/`N8` (the flatness and torsion crux) and
`N14` (assembly of group coherence). -/
structure OneRelatorCombinatorics : Prop where
  /-- The Freiheitssatz. -/
  freiheitssatz : ∀ {α : Type u} (r : FreeGroup α), FreiheitssatzAt r
  /-- The Magnus--Moldavanskii--Masters hierarchy. -/
  magnus_moldavanskii : ∀ {α : Type u} (r : FreeGroup α), MagnusMoldavanskiiAt r
  /-- Weinbaum's theorem on subwords of powers of a cyclically reduced relator. -/
  weinbaum : ∀ {α : Type u} (r : FreeGroup α), WeinbaumAt r
  /-- The Karrass--Magnus--Solitar torsion theorem. -/
  kms_torsion : ∀ {α : Type u} (r : FreeGroup α), KMSTorsionAt r

section Theorems

/-- **Freiheitssatz** (Magnus 1930).  If `r` is cyclically reduced and the set `T` of generators does
not generate `r` in the free group, then `F(T) →* ⟨α | r⟩` is injective. -/
theorem freiheitssatz (C : OneRelatorCombinatorics.{u}) {r : FreeGroup α} (hr : IsCyclicallyReducedRelator r) (T : Set α)
    (hT : r ∉ Subgroup.closure (FreeGroup.of '' T)) :
    Function.Injective (presentedGroupMap r T) :=
  C.freiheitssatz r hr T hT

/-- **Magnus--Moldavanskii hierarchy**: every one-relator group with a cyclically reduced nontrivial
relator admits a hierarchy of HNN extensions over free Magnus subgroups ending at a free product of a
free group and a finite cyclic group. -/
theorem magnus_moldavanskii (C : OneRelatorCombinatorics.{u}) {r : FreeGroup α} (hr : IsCyclicallyReducedRelator r) (hr1 : r ≠ 1) :
    HasMMHierarchy α r :=
  C.magnus_moldavanskii r hr hr1

/-- **Weinbaum's theorem.**  If `r` is cyclically reduced and not a proper power, then a nontrivial
subword `v` of a power of `r` with `|v| < |r|` is nontrivial in `⟨α | r⟩`. -/
theorem weinbaum (C : OneRelatorCombinatorics.{u}) {r : FreeGroup α} (hr : IsCyclicallyReducedRelator r) (hp : ¬ IsProperPower r)
    (k : ℕ) (v : FreeGroup α) (h : IsSubwordOf v (r ^ k))
    (hv : relatorNorm v < relatorNorm r) (hv1 : v ≠ 1) :
    PresentedGroup.mk ({r} : Set (FreeGroup α)) v ≠ 1 :=
  C.weinbaum r hr hp k v h hv hv1

/-- **Karrass--Magnus--Solitar torsion theorem.**  If `r = u ^ l`, `l ≥ 1`, with `u` not a proper
power, then `u` has order exactly `l` in `⟨α | r⟩` and every element of finite order in `⟨α | r⟩` is
conjugate to a power of `u`. -/
theorem kms_torsion (C : OneRelatorCombinatorics.{u}) {r u : FreeGroup α} {l : ℕ} (hl : 1 ≤ l) (hr : r = u ^ l)
    (hu : ¬ IsProperPower u) :
    orderOf (PresentedGroup.mk ({r} : Set (FreeGroup α)) u) = l ∧
      ∀ g : PresentedGroup ({r} : Set (FreeGroup α)), IsOfFinOrder g →
        ∃ k : ℕ, ∃ c : PresentedGroup ({r} : Set (FreeGroup α)),
          g = c * (PresentedGroup.mk ({r} : Set (FreeGroup α)) u) ^ k * c⁻¹ :=
  C.kms_torsion r u l hl hr hu

end Theorems

end Work.OROneRel
