/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The headline: Neukirch's *Kennzeichnung* in the form this workspace consumes it

The Neukirch–Uchida development in this workspace isolates, as its deepest local input,

  `NK.LocalStructure.LocalFieldFromFiniteExtensionLattice`

(`Submission/Work/LocalStructure/Defs.lean`): for `N` a finite extension of the `p`-adic field
`𝔮.adicCompletion L`, an isomorphism `Φ : Gal(L'/N) ≃* Gal(K'/𝔭.adicCompletion K)` of absolute
Galois groups, *together with a correspondence of the lattices of finite extensions*
(`NK.LocalStructure.FiniteExtensionCorrespondence Φ`), forces `N ≃+* 𝔭.adicCompletion K`.

The docstring of that definition records that the classical proof (Neukirch, Invent. Math. **6**
(1969), the local case of NSW (12.1.4)–(12.1.5)) recovers from the lattice (i) the ramification
filtration of the wild inertia and (ii) the field itself from the residue data plus that
filtration, and that (i) — the higher ramification theory — was missing in this workspace.  That
missing chapter is `Submission/Work/Ramification/`.

This file reduces the *catalogue*.  Write

  `NeukirchKennzeichnung`

for Neukirch's local theorem in its classical, data-free form: `Φ` is required only to be a
*continuous* isomorphism of profinite groups (equivalently, since both groups are compact
Hausdorff, a homeomorphism), with **no** lattice data.  Then

* `neukirchKennzeichnung_of_localFieldFromFiniteExtensionLattice` — the lattice form implies the
  classical form (proved, from `NK.LocalStructure.LocalNU.finiteExtensionCorrespondence_of_groupIso`);
* `localFieldFromFiniteExtensionLattice_of_neukirchKennzeichnung` — the classical form implies the
  lattice form, given the single auxiliary
  `NK.Ramification.continuous_of_finiteExtensionCorrespondence` (a correspondence of finite
  extension lattices forces `Φ` to be continuous: it is an open map because it carries the fixing
  subgroups of finite extensions, a basis of neighbourhoods of `1`, onto subgroups of finite index
  of a profinite group, hence onto open subgroups);

so the two are **equivalent**, and the data-heavy hypothesis `FiniteExtensionCorrespondence` can be
replaced by the classical continuity condition.

Independently, the workspace's single clean named input
`NK.LocalStructure.LocalNUExistence` (an isomorphism of absolute Galois groups of `p`-adic
fields, *no* lattice data at all) implies the lattice form
(`localFieldFromFiniteExtensionLattice_of_localNUExistence`), so the residual catalogue can be
taken to be the single proposition `NK.LocalStructure.LocalNUExistence`; the converse direction
is the on-disk `NK.LocalStructure.LocalNU.localNUExistence_of_finiteExtensionLattice`, whose only
extra hypothesis is the existence of a correspondence of lattices for every isomorphism (the
Galois-correspondence half, classically a consequence of Nikolov–Segal's theorem that finite-index
subgroups of finitely generated profinite groups are open).

What is *not* proved here, and what remains of the mathematics, is recorded honestly in
`Submission/Work/Ramification/README.md`: the content of `NeukirchKennzeichnung` is that the higher
ramification filtration of `Gal(K'/κ)` is an invariant of the abstract group, which is Neukirch's
hard step; this chapter supplies the filtration itself (lower and upper numbering, the Herbrand
function, the Hasse–Arf statement, the tower identities and the `p`-adic specialisation) but not
its group-theoretic definability.
-/
import Submission.NK.LocalStructure.Defs
import Submission.NK.LocalStructure.LocalNU.finiteExtensionCorrespondence_of_groupIso
import Submission.NK.LocalStructure.LocalNU.localNUExistence_of_finiteExtensionLattice
import Submission.NK.Ramification.continuous_of_finiteExtensionCorrespondence
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.Ramification

universe u

/-- **Neukirch's Kennzeichnung for `p`-adic fields** (Neukirch, *Kennzeichnung der `p`-adischen
und der endlich algebraischen Zahlkörper*, Invent. Math. **6** (1969); NSW (12.1.4)–(12.1.6)), in
its classical data-free form.

Let `N` be a finite extension of a `p`-adic field `𝔮.adicCompletion L`, realised inside a
separable closure `L'`, and let `𝔭.adicCompletion K` be another `p`-adic field.  Then a
*continuous* isomorphism `Gal(L'/N) ≃* Gal(K'/𝔭.adicCompletion K)` of absolute Galois groups
forces `N ≃+* 𝔭.adicCompletion K`.

Continuity is the correct hypothesis: both groups are compact Hausdorff profinite groups, so a
continuous bijective homomorphism is a homeomorphism, and the top-level Neukirch–Uchida theorem
consumes the homeomorphism form `IsHomeomorph ϕ`
(`Submission/NeukirchUchida/Core.lean`). -/
def NeukirchKennzeichnung : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (N : IntermediateField (𝔮.adicCompletion L) L') [FiniteDimensional (𝔮.adicCompletion L) ↥N]
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (Φ : Gal(L'/↥N) ≃* Gal(K'/𝔭.adicCompletion K)),
    Continuous ⇑Φ → Nonempty (↥N ≃+* 𝔭.adicCompletion K)

/-- **A correspondence of finite extension lattices forces the group isomorphism to be
continuous**, so that the lattice form of Neukirch's theorem is *not* weaker than the classical
form.

`Φ` carries `M.fixingSubgroup` — for `M` ranging over the finite extensions of the source, a basis
of neighbourhoods of `1` — onto `(C.level M).fixingSubgroup`, a fixing subgroup of a finite
extension, hence an open subgroup; a group homomorphism carrying such a basis onto open subgroups
is an open map, and an open bijection with compact source and Hausdorff target is a homeomorphism.

This statement is recorded as a `Prop` so that the headline equivalence below is *unconditional*
modulo it; it is proved in
`Submission/Work/Ramification/continuous_of_finiteExtensionCorrespondence.lean`. -/
def ContinuousOfFiniteExtensionCorrespondence : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (N : IntermediateField (𝔮.adicCompletion L) L') [FiniteDimensional (𝔮.adicCompletion L) ↥N]
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (Φ : Gal(L'/↥N) ≃* Gal(K'/𝔭.adicCompletion K)),
    NK.LocalStructure.FiniteExtensionCorrespondence Φ → Continuous ⇑Φ

/-- **The classical form implies the lattice form** of Neukirch's theorem, modulo the single
auxiliary `ContinuousOfFiniteExtensionCorrespondence`. -/
theorem localFieldFromFiniteExtensionLattice_of_neukirchKennzeichnung
    (hcont : ContinuousOfFiniteExtensionCorrespondence.{u})
    (h : NeukirchKennzeichnung.{u}) :
    NK.LocalStructure.LocalFieldFromFiniteExtensionLattice.{u} := by
  intro K L _ _ _ _ 𝔭 𝔮 L' _ _ _ N _ K' _ _ _ Φ C
  exact h K L 𝔭 𝔮 L' N K' Φ (hcont K L 𝔭 𝔮 L' N K' Φ C)

/-- **The lattice form implies the classical form** of Neukirch's theorem: a continuous
isomorphism of absolute Galois groups gives rise to a correspondence of finite extension lattices
(`NK.LocalStructure.LocalNU.finiteExtensionCorrespondence_of_groupIso`), to which the lattice
form applies. -/
theorem neukirchKennzeichnung_of_localFieldFromFiniteExtensionLattice
    (h : NK.LocalStructure.LocalFieldFromFiniteExtensionLattice.{u}) :
    NeukirchKennzeichnung.{u} := by
  intro K L _ _ _ _ 𝔭 𝔮 L' _ _ _ N _ K' _ _ _ Φ hΦ
  obtain ⟨C⟩ := NK.LocalStructure.LocalNU.finiteExtensionCorrespondence_of_groupIso
    K L 𝔭 𝔮 L' N K' Φ hΦ
  exact h K L 𝔭 𝔮 L' N K' Φ C

/-- **The equivalence**: Neukirch's Kennzeichnung in the classical data-free form is equivalent to
the lattice form consumed by this workspace, modulo the auxiliary
`ContinuousOfFiniteExtensionCorrespondence`. -/
theorem neukirchKennzeichnung_iff_localFieldFromFiniteExtensionLattice
    (hcont : ContinuousOfFiniteExtensionCorrespondence.{u}) :
    NeukirchKennzeichnung.{u} ↔
      NK.LocalStructure.LocalFieldFromFiniteExtensionLattice.{u} :=
  ⟨localFieldFromFiniteExtensionLattice_of_neukirchKennzeichnung hcont,
    neukirchKennzeichnung_of_localFieldFromFiniteExtensionLattice⟩

/-- **The lattice form follows from the workspace's single data-free input.**

`NK.LocalStructure.LocalNUExistence` asserts that an isomorphism of absolute Galois groups of
`p`-adic fields forces the fields to be isomorphic, with **no** lattice data; since the data of the
lattice form includes such an isomorphism, the lattice form follows immediately.  Together with
`NK.LocalStructure.LocalNU.localNUExistence_of_finiteExtensionLattice` (the converse, modulo the
existence of lattice correspondences) this identifies the residual catalogue with the single
proposition `NK.LocalStructure.LocalNUExistence`. -/
theorem localFieldFromFiniteExtensionLattice_of_localNUExistence
    (h : NK.LocalStructure.LocalNUExistence.{u}) :
    NK.LocalStructure.LocalFieldFromFiniteExtensionLattice.{u} := by
  intro K L _ _ _ _ 𝔭 𝔮 L' _ _ _ N _ K' _ _ _ Φ _
  exact h K L 𝔭 𝔮 L' N K' ⟨Φ⟩

/-- **The residual catalogue is a single proposition.**  The two forms of Neukirch's local theorem
on disk are equivalent modulo the (classically proved) existence of lattice correspondences for
every isomorphism of absolute Galois groups. -/
theorem localFieldFromFiniteExtensionLattice_iff_localNUExistence
    (hcorr : ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
      (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
      [IsSepClosure (𝔮.adicCompletion L) L']
      (N : IntermediateField (𝔮.adicCompletion L) L') [FiniteDimensional (𝔮.adicCompletion L) ↥N]
      (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
      [IsSepClosure (𝔭.adicCompletion K) K']
      (Φ : Gal(L'/↥N) ≃* Gal(K'/𝔭.adicCompletion K)),
      Nonempty (NK.LocalStructure.FiniteExtensionCorrespondence Φ)) :
    NK.LocalStructure.LocalFieldFromFiniteExtensionLattice.{u} ↔
      NK.LocalStructure.LocalNUExistence.{u} :=
  ⟨fun h => NK.LocalStructure.LocalNU.localNUExistence_of_finiteExtensionLattice h hcorr,
    localFieldFromFiniteExtensionLattice_of_localNUExistence⟩

/-! ## The unconditional headline -/

/-- **The auxiliary `ContinuousOfFiniteExtensionCorrespondence` holds**, so the equivalence below
is unconditional. -/
theorem continuousOfFiniteExtensionCorrespondence :
    ContinuousOfFiniteExtensionCorrespondence.{u} := by
  intro K L _ _ _ _ 𝔭 𝔮 L' _ _ _ N _ K' _ _ _ Φ C
  exact NK.Ramification.continuous_of_finiteExtensionCorrespondence K L 𝔭 𝔮 L' N K' Φ C

/-- **Neukirch's Kennzeichnung: the two forms are equivalent.**

Neukirch's local theorem in the classical data-free form (`NeukirchKennzeichnung`: a continuous —
equivalently, homeomorphic — isomorphism of absolute Galois groups of `p`-adic fields) is
equivalent to the lattice form `NK.LocalStructure.LocalFieldFromFiniteExtensionLattice` consumed
by this workspace.  Consequently the data-heavy hypothesis `FiniteExtensionCorrespondence` may be
replaced by the classical continuity condition, and conversely. -/
theorem neukirchKennzeichnung_iff_localFieldFromFiniteExtensionLattice' :
    NeukirchKennzeichnung.{u} ↔
      NK.LocalStructure.LocalFieldFromFiniteExtensionLattice.{u} :=
  neukirchKennzeichnung_iff_localFieldFromFiniteExtensionLattice
    continuousOfFiniteExtensionCorrespondence

/-- **The classical form implies the lattice form**, unconditionally. -/
theorem localFieldFromFiniteExtensionLattice_of_neukirchKennzeichnung'
    (h : NeukirchKennzeichnung.{u}) :
    NK.LocalStructure.LocalFieldFromFiniteExtensionLattice.{u} :=
  localFieldFromFiniteExtensionLattice_of_neukirchKennzeichnung
    continuousOfFiniteExtensionCorrespondence h

/-- **The corollary for the local Neukirch–Uchida existence statement**: the classical form of
Neukirch's Kennzeichnung, together with the existence of lattice correspondences, gives
`NK.LocalStructure.LocalNUExistence`. -/
theorem localNUExistence_of_neukirchKennzeichnung
    (hcorr : ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
      (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
      [IsSepClosure (𝔮.adicCompletion L) L']
      (N : IntermediateField (𝔮.adicCompletion L) L') [FiniteDimensional (𝔮.adicCompletion L) ↥N]
      (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
      [IsSepClosure (𝔭.adicCompletion K) K']
      (Φ : Gal(L'/↥N) ≃* Gal(K'/𝔭.adicCompletion K)),
      Nonempty (NK.LocalStructure.FiniteExtensionCorrespondence Φ))
    (h : NeukirchKennzeichnung.{u}) :
    NK.LocalStructure.LocalNUExistence.{u} :=
  (localFieldFromFiniteExtensionLattice_iff_localNUExistence hcorr).mp
    (localFieldFromFiniteExtensionLattice_of_neukirchKennzeichnung' h)

end NK.Ramification
