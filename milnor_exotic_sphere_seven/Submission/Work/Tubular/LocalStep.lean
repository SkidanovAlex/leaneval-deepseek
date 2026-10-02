import Submission.Work.Tubular.CapCupAdjunction
import Submission.Work.Tubular.CapCupAdjunctionRel
import Submission.Work.Tubular.NormalThom
import Submission.Work.Tubular.Interface
import Submission.Work.Cohomology.kronH_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Item 3, piece (B3): the local degree of the Pontryagin–Thom collapse

This module isolates the **one remaining geometric statement** of the tubular chapter's item 3
(Thom-class naturality), states it exactly, and proves the *reduction* that turns it into the two
Hurewicz pairings of `Work.Tubular.TubeThomRep` — i.e. into step 6 of the classical chain of
`PairingNotes.md` §2.

## The statement, in one line

For the normal bundle `ν` of an embedding `V ↪ ℝ^{8+k}`, with `U_ν ∈ H^k(ν.TotalSpace, ν.TotalSpace∖0)`
an integral Thom class and `c ∈ H_{k+8}(ν.TotalSpace, ν.TotalSpace∖0)` the class of the
Pontryagin–Thom collapse (i.e. the relative fundamental class of the disc bundle pair, transported
along the radial homeomorphism of `OnePointModel.lean`),

  `U_ν ⌢ c = z_*[V]`,

`z : V → ν.TotalSpace` the zero section and `[V]` the fundamental class of `V`.  This is
`Work.Tubular.TubeLocalDegree` below.

## Why this is exactly what is missing

`Work.Tubular.kronH_mixedCup_relCapPair` (piece (B1), proved) converts the *mixed* cap/cup
adjunction `⟨x, U ⌢ c⟩ = ⟨x ⌣ U, c'⟩` (an absolute class `x ∈ H^8`, a relative class
`U ∈ H^k(ν, ν∖0)`, a relative cycle `c` with absolute lift `c'`).  The theorem
`Work.Tubular.kronH_mixedCup_eq_fundClass` below composes it with `TubeLocalDegree` and with the
naturality of the Kronecker pairing (`Work.Cohomology.kronH_natural`) to obtain

  `⟨x ⌣ U_ν, c'⟩ = ⟨z^*x, [V]⟩`,

which is the **Thom isomorphism evaluated on the fundamental class**: the left side is the pairing of
the Thom-iso image of `x` with the collapsed sphere, the right side the pairing of `x` with `[V]`.

## What is *not* in this module

* the identification of `c` with the Hurewicz image of the collapse map
  (`Work.Tubular.tubeGenLoopOnePoint`) — it needs the comparison of the cohomology of the one-point
  compactification with the relative cohomology of the Thom pair, recorded as
  `Work.Tubular.NormalThomComparison` below (this is the ν-side half of
  `Grassmann/README.md` §5(4));
* the description of the classes `p₁²U`, `p₂U` of the universal target `D` — that is the Grassmann
  chapter's obligation (`README.md` §17 of this directory: they must be the *mixed* / Thom-iso
  images, not space-level cup products), recorded as `Work.Tubular.GrassmannClassDescription`.

Both are stated at the end of this file so that the remaining work is exactly named.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ} {ι : Type}

/-! ## The zero section and the fundamental class of `V` inside the total space -/

/-- The zero section of a real bundle, as a morphism of topological spaces. -/
def zeroSectionTop (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι) :
    TopCat.of V.pt ⟶ TopCat.of Z.TotalSpace :=
  TopCat.ofHom (Work.Thom.zeroSection Z)

/-- **The fundamental class of `V` inside the total space of the normal bundle**, along the zero
section: `z_*[V] ∈ H_8(ν.TotalSpace)`.  The local degree statement below asserts that the cap
product of the Thom class with the collapse class is this class. -/
def fundClassInTotal (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι) :
    (singularChains ℤ (TopCat.of Z.TotalSpace)).homology 8 :=
  (HomologicalComplex.homologyMap
    (chainMap ℤ (TopCat.of V.pt) (TopCat.of Z.TotalSpace) (zeroSectionTop Z)) 8) V.c

/-- The zero section pushes the fundamental class of `V` to `fundClassInTotal`. -/
theorem zeroSection_homology_fund (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι) :
    (HomologicalComplex.homologyMap
      (chainMap ℤ (TopCat.of V.pt) (TopCat.of Z.TotalSpace) (zeroSectionTop Z)) 8) V.c
      = fundClassInTotal Z := rfl

/-! ## The local degree -/

/-- **The local degree of the Pontryagin–Thom collapse** (piece (B3) of the brief, and step 6 of
`PairingNotes.md` §2).  This is the **corrected** form (`README.md` §21.1 and §23):

* `U` is a Thom class of the normal bundle `ν` (for the embedding `V ↪ ℝ^{8+k}`, of rank `k`): a
  class in `H^k(ν.TotalSpace, ν.TotalSpace ∖ 0)`;
* `c` is the *relative* class of the collapse map `S^{8+k} → Th(ν)` in
  `H_{k+8}(ν.TotalSpace, ν.TotalSpace ∖ 0)` — the relative fundamental class of the disc bundle
  pair, transported along the radial homeomorphism of `OnePointModel.lean`;
* the conclusion is the local-degree statement `U ⌢ c = z_*[V]`.

The cap product is `Work.Cohomology.relCapPair` (a *relative* class in degree `k` against a
relative class in degree `k+8`, giving an absolute class in degree `8`).

**No absolute lift of `c` occurs.**  The earlier form of this definition carried an absolute class
`c'` together with a proof `π c' = c`; that hypothesis is satisfiable only for `c = 0` in the
application (the total space of a bundle over a compact `8`-manifold has vanishing `H_{k+8}` for
`k ≥ 1`), which made it vacuous.  It is kept below as `TubeLocalDegreeWithLift`. -/
def TubeLocalDegree (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι)
    (U : Work.Thom.OpenThom Z k)
    (c : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology (k + 8)) :
    Prop :=
  relCapPair (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) k 8 U c = fundClassInTotal Z

/-- **The local degree, in pairing form**: for every absolute class `x` of degree `8` on the total
space of the normal bundle, the mixed pairing of the Thom-iso image `x ⌣ U` with the collapse class
is the pairing of `x` with the fundamental class of `V` along the zero section.

This is the form in which the local degree feeds the two Hurewicz pairings of
`Work.Tubular.TubeThomRep`; `Work.Tubular.TubeLocalDegree.pairing` below shows that it is implied by
`TubeLocalDegree`, and the two are in fact equivalent (both are the statement that the Thom
isomorphism carries the collapse class to the fundamental class). -/
def TubeLocalDegreePairing (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι)
    (U : Work.Thom.OpenThom Z k)
    (c : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology (k + 8)) :
    Prop :=
  ∀ x : Work.Thom.Coh ℤ 8 (TopCat.of Z.TotalSpace),
    relKronH (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) (k + 8)
        ((Nat.add_comm 8 k) ▸
          (mixedCup (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) 8 k x U)) c
      = kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8).hom x) V.c

/-- **The superseded form of the local degree**, carrying an absolute lift `c'` of the collapse class.
Retained for the record: `README.md` §21.1 shows that its hypothesis `hc` can only be met with
`c = 0` for a bundle over a compact `8`-manifold, so it is vacuous in the application.  Use
`TubeLocalDegree` instead. -/
def TubeLocalDegreeWithLift (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι)
    (U : Work.Thom.OpenThom Z k)
    (c' : (singularChains ℤ (TopCat.of Z.TotalSpace)).homology (k + 8))
    (c : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology (k + 8))
    (hc : HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of Z.TotalSpace)
          (Work.Thom.zeroComplement Z))) (k + 8) c' = c) : Prop :=
  relCapPair (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) k 8 U c = fundClassInTotal Z

/-! ## The reduction: the local degree gives the pairing with the fundamental class -/

/-- **The mixed pairing of the Thom class with the collapsed sphere is the pairing of the zero-section
pullback with `[V]`.**  From the local degree `U ⌢ c = z_*[V]`:

  `⟨x ⌣ U, c'⟩ = ⟨z^*x, [V]⟩`

for every absolute class `x ∈ H^8(ν.TotalSpace)`.  The proof is the composition of

* `Work.Tubular.kronH_mixedCup_relCapPair` (piece (B1)) — the mixed cap/cup adjunction;
* the local degree;
* `Work.Cohomology.kronH_natural` — naturality of the Kronecker pairing along the zero section.

This is the precise form of step 6 of `PairingNotes.md` §2, and with the description
`p₁²U = thom(p₁(γ)²)` of the Grassmann classes (§17 of this directory's `README.md`) it is what
produces the two Hurewicz pairings of `Work.Tubular.TubeThomRep`. -/
theorem kronH_mixedCup_eq_fundClass_lift
    {Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι} {U : Work.Thom.OpenThom Z k}
    {c' : (singularChains ℤ (TopCat.of Z.TotalSpace)).homology (k + 8)}
    {c : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology (k + 8)}
    {hc : HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of Z.TotalSpace)
          (Work.Thom.zeroComplement Z))) (k + 8) c' = c}
    (hdeg : TubeLocalDegreeWithLift Z U c' c hc)
    (x : Work.Thom.Coh ℤ 8 (TopCat.of Z.TotalSpace)) :
    kronH ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace)) (k + 8)
        ((Nat.add_comm 8 k) ▸
          (HomologicalComplex.homologyMap
            (relIncl ℤ (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)) (8 + k)
            (mixedCup (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) 8 k x U)))
        c'
      = kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8).hom x) V.c := by
  have hpq : Even (k * 8) := ⟨4 * k, by ring⟩
  have h1 := kronH_mixedCup_relCapPair (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
    k 8 hpq x U c c' hc
  have h2 : relCapPair (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) k 8 U c
      = fundClassInTotal Z := hdeg
  rw [← h1, h2]
  exact kronH_natural (TopCat.of V.pt) (TopCat.of Z.TotalSpace) (zeroSectionTop Z) 8 x V.c

/-- **The local degree implies its pairing form** (this is piece (B1) of the brief, now finished:
`Work.Tubular.kronH_mixedCup_relKronH`).  From `U ⌢ c = z_*[V]`:

  `⟨x ⌣ U, c⟩ = ⟨z^*x, [V]⟩`

for every absolute class `x ∈ H^8(ν.TotalSpace)` — the **Thom isomorphism evaluated on the
fundamental class**.  The proof is the mixed cap/cup adjunction (in the corrected, non-vacuous
relative form), followed by the local degree and the naturality of the Kronecker pairing along the
zero section. -/
theorem TubeLocalDegree.pairing
    {Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι} {U : Work.Thom.OpenThom Z k}
    {c : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology (k + 8)}
    (hk : 1 ≤ k) (hdeg : TubeLocalDegree Z U c) : TubeLocalDegreePairing Z U c := by
  intro x
  have hpq : Even (k * 8) := ⟨4 * k, by ring⟩
  rw [← kronH_mixedCup_relKronH (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) k 8
      hk (by norm_num) hpq x U c, hdeg]
  exact kronH_natural (TopCat.of V.pt) (TopCat.of Z.TotalSpace) (zeroSectionTop Z) 8 x V.c

/-- The same reduction, spelled out with `kronH` on the left: the pairing of the Thom-iso image of
an absolute class of degree `8` with the collapsed sphere is the pairing of the pullback along the
zero section with the fundamental class of `V`. -/
theorem kronH_relKronH_eq_fundClass
    {Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι} {U : Work.Thom.OpenThom Z k}
    {c : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology (k + 8)}
    (hk : 1 ≤ k) (hdeg : TubeLocalDegree Z U c) (x : Work.Thom.Coh ℤ 8 (TopCat.of Z.TotalSpace)) :
    relKronH (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) (k + 8)
        ((Nat.add_comm 8 k) ▸
          (mixedCup (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) 8 k x U)) c
      = kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (Work.Thom.zeroSection Z) ℤ 8).hom x) V.c :=
  TubeLocalDegree.pairing hk hdeg x

/-- **The pairing form of the local degree implies the class form**, provided the Kronecker pairing
`⟨·, z_*[V]⟩` separates `z_*[V]` in `H_8(ν.TotalSpace)`.  Together with
`Work.Tubular.TubeLocalDegree.pairing` this shows that the two forms of the local degree are
equivalent: `U ⌢ c = z_*[V]` if and only if `⟨x ⌣ U, c⟩ = ⟨z^*x, [V]⟩` for every absolute class
`x` of degree `8`.

The non-degeneracy hypothesis is a theorem about the closed oriented `8`-manifold `V` (the
Kronecker pairing of `H^8` with `H_8` is non-degenerate: `H_8(ν.TotalSpace) ≅ H_8(V) ≅ ℤ` with
`H_8(V)` generated by `[V]`, and `H^8(V) ≅ Hom(H_8(V),ℤ)` by universal coefficients).  It is
recorded as a hypothesis because `Work.Cohomology` does not (yet) contain the universal coefficient
theorem for a closed manifold. -/
theorem TubeLocalDegree.of_pairing
    {Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι} {U : Work.Thom.OpenThom Z k}
    {c : (relChains (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)).homology (k + 8)}
    (hk : 1 ≤ k)
    (hnd : ∀ y : (singularChains ℤ (TopCat.of Z.TotalSpace)).homology 8,
      (∀ x : Work.Thom.Coh ℤ 8 (TopCat.of Z.TotalSpace),
        kronH ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace)) 8 x y
          = kronH ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace)) 8 x (fundClassInTotal Z)) →
      y = fundClassInTotal Z)
    (h : TubeLocalDegreePairing Z U c) : TubeLocalDegree Z U c := by
  apply hnd
  intro x
  have hpq : Even (k * 8) := ⟨4 * k, by ring⟩
  rw [kronH_mixedCup_relKronH (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) k 8
    hk (by norm_num) hpq x U c, h x]
  exact (kronH_natural (TopCat.of V.pt) (TopCat.of Z.TotalSpace) (zeroSectionTop Z) 8 x V.c).symm

/-! ## The two remaining links, and who owns them

The two statements below are the ones that are **not** in this directory.  Neither is stated as a
`Prop` here, because neither can be *stated* in this workspace yet — each needs a comparison that
does not exist:

**(A) The ν-side one-point comparison** (the ν-side half of `Grassmann/README.md` §5(4); item (A) of
`README.md` §16.5).

The Pontryagin–Thom collapse of the chapter is a map `S^{8+k} = OnePoint (Euc (8+k)) → OnePoint
(NormalTotal E)` (`Work.Tubular.collapseToOnePoint`, `Work.Tubular.tubeGenLoopOnePoint`), so its
Hurewicz class `h(collapse)` lives in the homology of the one-point compactification
`OnePoint (NormalTotal E) = Th(ν)`, whereas `Work.Tubular.TubeLocalDegree` is stated against the
*relative* homology `H_{k+8}(ν.TotalSpace, ν.TotalSpace ∖ 0)`.  What is needed is

  `H_n(OnePoint Z.TotalSpace) ≅ H_n(Z.TotalSpace, Z.TotalSpace ∖ 0)`

for the gluing-data normal bundle `Z` (with the norm-preserving homeomorphism
`Z.TotalSpace ≃ₜ NormalTotal E` of `Work.Tubular.exists_euclidean_normalBundle`), together with the
identification of `h(collapse)` with the *relative fundamental class* `c` of the collapsed disc
bundle pair — the map of pairs `(D^{8+k}, S^{7+k}) → (D(ν), S(ν))` induced by the tube chart.  The
*existence* of the map of pairs is what `Work.Tubular.tubeCollapse` and
`Work.Tubular.TubeChart.tubeMap_inv` supply; the comparison of the two homology theories is what is
missing, and it is a statement about one-point compactifications of vector bundles (shared with the
Grassmann chapter).  The ingredients on this side: `Work.Tubular.normalThomSpace_homeo_onePoint`,
`Work.Tubular.collapseToOnePoint`, `Work.Tubular.tubeCollapse_mem_normalThomZero`,
`Work.Tubular.normalCoord_eq_zero_iff`, `Work.Tubular.exists_normalCoord_eq`, and
`Work.Cohomology.excision`.

**(B) The description of the Grassmann classes `p₁²U`, `p₂U`** (item (M1) of `PairingNotes.md` §4,
and §17 of `README.md`).

For the universal target `D = grassmannThomTarget k m …` of the Grassmann chapter, with universal
bundle `γ` over `G`, Thom class `U_γ`, and `x ∈ H^8(G)` the characteristic class in question, the
class `D.p1sqU` must be the **Thom-iso image** `π^*x ⌣ U_γ` of `x` — *not* a space-level product of
two classes of `H^*(Th γ)`, which is identically zero because `Th γ` is `(k-1)`-connected and
`H^8(Th γ) = 0` for `k > 8` (`Work.Thom.subsingleton_OpenThom_of_lt_rank`,
`Work.Tubular.subsingleton_openThom_normal`, `Work.Tubular.eq_zero_of_degree_eight_lt_rank`).  With
this description, `Work.Tubular.kronH_mixedCup_eq_fundClass` above computes the pairing as `⟨x, [V]⟩`.
-/

end

end Work.Tubular
