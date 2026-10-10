/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.LLink.Count

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A non-vanishing invariant coefficient from an open immersion missing a divisor

This file proves

`Work.CrauderKatz.BlowUp.exists_cInv_ne_zero_of_openImmersion_missingDivisor`

by exhibiting an explicit geometric witness: the affine plane `𝔸² = Spec 𝕜[X₀,X₁]` together with
the complement `U = D(X₀)` of the line `V(X₀)`, and the birational map `φ : 𝔸² ⤏ U` which is the
inverse of the open immersion `U ↪ 𝔸²`.

The mathematical content is the standard one-sided computation.  Write `η ∈ 𝔸²` for the generic
point of the missing line `V(X₀)` (the point with `η.asIdeal = (X₀)`, of codimension one).

* `φ` is an isomorphism at every point of `U`: it is represented there by the partial isomorphism
  `(U.partialIsoOfDense _).symm`, whose source is all of `U`.
* `φ` is *not* an isomorphism at `η`: any partial isomorphism `i` representing `φ.hom`
  is, by `isOver_toPartialMap_isOver` below, compatible with the structure maps
  (`i.toPartialMap.hom ≫ U.ι = i.source.ι`), so that the image of `i.source` in `𝔸²` lies inside
  the image `U` of `U.ι`; hence `η ∉ i.source`.
* every other point of codimension one lies in `U` and so is not exceptional
  (`eq_missingPoint_of_coheight_eq_one_of_notMem`).

Consequently `exDiv φ = {η}`.  In the inverse direction `φ⁻¹` is represented by the partial
isomorphism `U.partialIsoOfDense _`, which is defined on all of `U`, so `exDiv φ⁻¹ = ∅`.  The
counting lemmas of `Work.LLink` then give `cInv 𝕜 η φ = 0 - 1 = -1`
(`cInv_eq_neg_one_of_exDiv_eq_singleton`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Work.CrauderKatz.BlowUp

noncomputable section

/-! ## General ingredients -/

/-- An open subscheme of an irreducible scheme is irreducible (the corresponding open set is
nonempty and preirreducible, hence irreducible). -/
lemma irreducibleSpace_opensOfDense {X : Scheme.{0}} [IrreducibleSpace X] {U : X.Opens}
    (hU : Dense (U : Set X)) : IrreducibleSpace U.toScheme := by
  have hne : (U : Set X).Nonempty := hU.nonempty
  have hpre : IsPreirreducible (U : Set X) :=
    isPreirreducible_iff_closure.mp (by
      rw [hU.closure_eq]
      exact PreirreducibleSpace.isPreirreducible_univ)
  exact Subtype.irreducibleSpace ⟨hne, hpre⟩

/-- The image of the inclusion of an open subscheme, as a set. -/
lemma range_opens_ι {X : Scheme.{0}} (U : X.Opens) :
    Set.range ⇑(U.ι) = (U : Set X) := by
  rw [← Hom.coe_opensRange, Opens.opensRange_ι]

/-- A partial isomorphism representing an `S`-birational map over `S` is itself over `S`, when
the source is reduced and the base `S` is separated.  (Local re-statement of
`Work.Motivic.isOver_toPartialMap_isOver`, whose module
`Submission.Work.Motivic.cInv_mul_pt_base` cannot be imported together with the counting lemmas
of `Submission.Work.LLink.Count`.) -/
lemma isOver_toPartialMap_isOver {X Y S : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [X.Over S] [Y.Over S] [IsReduced X] [S.IsSeparated]
    {φ : X.BirationalMap Y} (hφ : φ.hom.IsOver S)
    (i : X.PartialIso Y) (hi : i.toRationalMap = φ.hom) : i.toPartialMap.IsOver S := by
  refine PartialMap.isOver_toRationalMap_iff_of_isSeparated.mp ?_
  show RationalMap.IsOver S i.toRationalMap
  rw [hi]; exact hφ

/-- **Counting.**  A birational map whose only exceptional divisor is `x`, which is moreover the
base point of the invariant, has `[κ(x)]`-coefficient `0 - 1 = -1`. -/
theorem cInv_eq_neg_one_of_exDiv_eq_singleton (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace Y] [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
    (φ : X.BirationalMap Y) (x : X) (hx : exDiv φ = {x}) (hy : exDiv φ.symm = ∅) :
    cInv 𝕜 (Z := X) x φ = -1 := by
  have h1 : excCount 𝕜 x φ = 1 :=
    Work.LLink.excCount_eq_one_of_exDiv_eq_singleton x φ hx (Work.Motivic.ResEquiv.refl 𝕜 x)
  have h2 : excCount 𝕜 x φ.symm = 0 :=
    Work.LLink.excCount_eq_zero_of_exDiv_eq_empty x φ.symm hy
  show (excCount 𝕜 x φ.symm : ℤ) - (excCount 𝕜 x φ : ℤ) = -1
  rw [h1, h2]
  norm_num

/-- **The inverse of an open immersion is not an isomorphism along the missing divisor.**  Let `U`
be a dense open subscheme of an irreducible, reduced, separated scheme `X`, and let
`φ : X ⤏ U` be the inverse of the open immersion `U ↪ X`.  Then the exceptional divisors of `φ` in
the forward direction are exactly the codimension-one points of `X` outside `U`. -/
theorem exDiv_partialIsoOfDense_symm {X : Scheme.{0}} [IrreducibleSpace X] [IsReduced X]
    [X.IsSeparated] {U : X.Opens} [IrreducibleSpace U.toScheme] (hU : Dense (U : Set X)) :
    exDiv ((U.partialIsoOfDense hU).symm.toBirationalMap)
      = {z : X | Order.coheight z = 1 ∧ z ∉ (U : Set X)} := by
  -- `U.partialIsoOfDense hU` represents the open immersion `U ↪ X`, hence is a map over `X`
  -- (the base being `X` itself, with structure maps `U.ι` and `𝟙 X`).
  have hαov : (U.partialIsoOfDense hU).IsOver (U.ι) (𝟙 X) := by
    simp [PartialIso.IsOver, Opens.partialIsoOfDense]
  have hαs : (U.partialIsoOfDense hU).symm.toPartialMap.IsOver X := by
    have h2 := PartialIso.IsOver.symm hαov
    show ((U.partialIsoOfDense hU).symm.toPartialMap.hom).IsOver X
    rw [Scheme.Hom.isOver_iff]
    simp only [PartialIso.toPartialMap_hom, PartialIso.symm_iso]
    exact h2
  have hφov : ((U.partialIsoOfDense hU).symm.toBirationalMap).hom.IsOver X :=
    ⟨(U.partialIsoOfDense hU).symm.toPartialMap, hαs, rfl⟩
  ext z
  constructor
  · -- points of `U` are isomorphism points, so the exceptional locus lies outside `U`
    rintro ⟨hz1, hz2⟩
    refine ⟨hz1, fun hzU => hz2 ⟨(U.partialIsoOfDense hU).symm, ?_, rfl⟩⟩
    rwa [PartialIso.symm_source, Opens.partialIsoOfDense_target]
  · -- points outside `U` are not isomorphism points
    rintro ⟨hz1, hzU⟩
    refine ⟨hz1, ?_⟩
    rintro ⟨i, hzi, hi⟩
    have hi' : i.toRationalMap = (U.partialIsoOfDense hU).symm.toRationalMap := by
      simpa [PartialIso.toBirationalMap_hom] using hi
    haveI hiso : i.toPartialMap.IsOver X :=
      isOver_toPartialMap_isOver (φ := (U.partialIsoOfDense hU).symm.toBirationalMap) hφov i hi'
    -- the underlying morphism of `i` is compatible with the inclusion of `U`
    have hEq : i.toPartialMap.hom ≫ U.ι = i.source.ι := by
      have h : (i.toPartialMap.hom).IsOver X := hiso
      have h2 := (Scheme.Hom.isOver_iff (S := X)).mp h
      -- the structure maps of the open subschemes `U` and `i.source` over `X` (the base being `X`
      -- itself) are, definitionally, the inclusions followed by the identity of `X`
      change i.toPartialMap.hom ≫ (U.ι ≫ 𝟙 X) = (i.toPartialMap.domain).ι ≫ 𝟙 X at h2
      -- `i.toPartialMap.domain` and `i.source` are definitionally equal
      have h3 : i.toPartialMap.hom ≫ (U.ι ≫ 𝟙 X) = i.source.ι ≫ 𝟙 X := h2
      simpa using h3
    -- hence every point of the source of `i` lies in the image of `U.ι`
    have hmem : z ∈ Set.range ⇑(U.ι) := by
      have h1 : i.source.ι ⟨z, hzi⟩ = z := Opens.ι_apply i.source ⟨z, hzi⟩
      rw [← hEq] at h1
      exact Set.mem_range.mpr ⟨i.toPartialMap.hom ⟨z, hzi⟩, h1⟩
    exact hzU (by rwa [range_opens_ι] at hmem)

/-- The inverse direction of `exDiv_partialIsoOfDense_symm`: the inverse of the open immersion is
represented on all of `U`, so it has no exceptional divisor. -/
theorem exDiv_symm_partialIsoOfDense {X : Scheme.{0}} [IrreducibleSpace X] [IsReduced X]
    {U : X.Opens} [IrreducibleSpace U.toScheme] (hU : Dense (U : Set X)) :
    exDiv (((U.partialIsoOfDense hU).symm.toBirationalMap)).symm = ∅ := by
  have hsymm : (((U.partialIsoOfDense hU).symm.toBirationalMap)).symm
      = (U.partialIsoOfDense hU).toBirationalMap := by
    apply BirationalMap.ext
    rw [BirationalMap.symm_hom, PartialIso.toBirationalMap_inv, PartialIso.toBirationalMap_hom]
    rfl
  rw [hsymm, Set.eq_empty_iff_forall_notMem]
  rintro x ⟨-, hx⟩
  exact hx ⟨U.partialIsoOfDense hU, by rw [Opens.partialIsoOfDense_source]; trivial,
    PartialIso.toBirationalMap_hom _⟩

/-! ## The concrete witness: the affine plane and the complement of a line -/

/-- The coordinate ring `𝕜[X₀,X₁]` of the affine plane over `𝕜`. -/
noncomputable abbrev planeRing (𝕜 : Type) [Field 𝕜] : CommRingCat :=
  CommRingCat.of (MvPolynomial (Fin 2) 𝕜)

/-- The affine plane `𝔸² = Spec 𝕜[X₀,X₁]`. -/
noncomputable abbrev plane (𝕜 : Type) [Field 𝕜] : Scheme.{0} := Spec (planeRing 𝕜)

/-- The complement `D(X₀)` of the line `V(X₀)` in the affine plane. -/
noncomputable abbrev planeOpen (𝕜 : Type) [Field 𝕜] : (plane 𝕜).Opens :=
  PrimeSpectrum.basicOpen (MvPolynomial.X 0 : MvPolynomial (Fin 2) 𝕜)

/-- The generic point of the missing line `V(X₀)`, i.e. the point of the plane defined by the prime
ideal `(X₀)`. -/
noncomputable abbrev missingPoint (𝕜 : Type) [Field 𝕜] : plane 𝕜 :=
  ⟨Ideal.span {MvPolynomial.X 0},
    (Ideal.span_singleton_prime (MvPolynomial.X_prime.ne_zero)).mpr MvPolynomial.X_prime⟩

/-- The complement of the line is dense in the plane. -/
theorem planeOpen_dense (𝕜 : Type) [Field 𝕜] : Dense (planeOpen 𝕜 : Set (plane 𝕜)) := by
  refine IsOpen.dense (planeOpen 𝕜).2 ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  have h : ((⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ↑(planeRing 𝕜)) : plane 𝕜)
      ∈ PrimeSpectrum.basicOpen (MvPolynomial.X 0 : MvPolynomial (Fin 2) 𝕜) := by
    rw [PrimeSpectrum.mem_basicOpen]
    exact fun h => MvPolynomial.X_prime.ne_zero (Ideal.mem_bot.mp h)
  exact h

/-- The missing point has codimension one. -/
theorem coheight_missingPoint (𝕜 : Type) [Field 𝕜] : Order.coheight (missingPoint 𝕜) = 1 := by
  rw [← idealHeight_eq_coheight]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr MvPolynomial.X_prime.ne_zero)
    (fun h => MvPolynomial.X_prime.not_isUnit h)

/-- The missing point is not in the complement of the line: it is the generic point of `V(X₀)`. -/
theorem missingPoint_notMem (𝕜 : Type) [Field 𝕜] :
    missingPoint 𝕜 ∉ (planeOpen 𝕜 : Set (plane 𝕜)) := by
  intro h
  have h2 := (PrimeSpectrum.mem_basicOpen (MvPolynomial.X 0 : MvPolynomial (Fin 2) 𝕜)
    ((missingPoint 𝕜 : PrimeSpectrum ↑(planeRing 𝕜)))).mp h
  exact h2 (Ideal.mem_span_singleton.mpr (dvd_refl _))

/-- The missing point is the *only* codimension-one point of the plane outside the complement of
the line: in the UFD `𝕜[X₀,X₁]` a height-one prime ideal is principal, and the only principal prime
ideal dividing `X₀` is `(X₀)` itself. -/
theorem eq_missingPoint_of_coheight_eq_one_of_notMem (𝕜 : Type) [Field 𝕜] {z : plane 𝕜}
    (hz : Order.coheight z = 1) (hzU : z ∉ (planeOpen 𝕜 : Set (plane 𝕜))) : z = missingPoint 𝕜 := by
  have hznot : (MvPolynomial.X 0 : MvPolynomial (Fin 2) 𝕜)
      ∈ (z : PrimeSpectrum ↑(planeRing 𝕜)).asIdeal := by
    by_contra h
    exact hzU ((PrimeSpectrum.mem_basicOpen _ _).mpr h)
  have hheight : (z : PrimeSpectrum ↑(planeRing 𝕜)).asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight]
    exact hz
  haveI : (z : PrimeSpectrum ↑(planeRing 𝕜)).asIdeal.IsPrime :=
    (z : PrimeSpectrum ↑(planeRing 𝕜)).isPrime
  have hspan := Ideal.eq_span_singleton_of_height_eq_one hheight hznot
    (MvPolynomial.X_prime (σ := Fin 2) (R := 𝕜))
  exact PrimeSpectrum.ext (by simpa using hspan)

/-- The scheme `U = D(X₀)`, the complement of the missing line. -/
noncomputable abbrev planeOpenScheme (𝕜 : Type) [Field 𝕜] : Scheme.{0} := (planeOpen 𝕜).toScheme

/-- The partial isomorphism `U ≅ 𝔸²` underlying the open immersion `U ↪ 𝔸²`. -/
noncomputable abbrev planeOpenIso (𝕜 : Type) [Field 𝕜] :
    (planeOpenScheme 𝕜).PartialIso (plane 𝕜) :=
  (planeOpen 𝕜).partialIsoOfDense (planeOpen_dense 𝕜)

/-- The birational map `φ : 𝔸² ⤏ U` inverse to the open immersion `U ↪ 𝔸²`. -/
noncomputable abbrev missingDivisorMap (𝕜 : Type) [Field 𝕜]
    [IrreducibleSpace (planeOpenScheme 𝕜)] :
    (plane 𝕜).BirationalMap (planeOpenScheme 𝕜) :=
  (planeOpenIso 𝕜).symm.toBirationalMap

/-! ## The statement -/

/-- A concrete computation of a non-vanishing invariant coefficient of the counting layer of Part A: there are schemes over `𝕜` and a birational map between them having a single exceptional divisor in the forward direction, none in the inverse direction, and hence coefficient `-1` at that divisor. This witnesses that `exDiv` and `cInv` are non-vacuous and computable at the level of actual schemes. Correct orientation of the witness: take `Y` the affine plane and `X` the complement of a line, with the map being the inverse of the open immersion (so the forward exceptional divisor is the generic point of the missing line). -/
theorem exists_cInv_ne_zero_of_openImmersion_missingDivisor (𝕜 : Type) [Field 𝕜] :
    ∃ (X Y : AlgebraicGeometry.Scheme.{0}) (_ : IrreducibleSpace X) (_ : IrreducibleSpace Y)
      (_ : X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
      (_ : Y.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
      (y : Y) (φ : Y.BirationalMap X), exDiv φ = {y} ∧ exDiv φ.symm = ∅ ∧ cInv 𝕜 y φ = -1 := by
  have hDense : Dense (planeOpen 𝕜 : Set (plane 𝕜)) := planeOpen_dense 𝕜
  haveI hIrrT : IrreducibleSpace (planeOpenScheme 𝕜) := irreducibleSpace_opensOfDense hDense
  haveI hIrrS : IrreducibleSpace (plane 𝕜) := inferInstance
  haveI hOvS : (plane 𝕜).Over (Spec (CommRingCat.of 𝕜)) := inferInstance
  haveI hOvT : (planeOpenScheme 𝕜).Over (Spec (CommRingCat.of 𝕜)) := inferInstance
  have hExDiv : exDiv (missingDivisorMap 𝕜) = {missingPoint 𝕜} := by
    rw [exDiv_partialIsoOfDense_symm hDense]
    ext z
    constructor
    · rintro ⟨hz1, hzU⟩
      exact eq_missingPoint_of_coheight_eq_one_of_notMem 𝕜 hz1 hzU
    · rintro rfl
      exact ⟨coheight_missingPoint 𝕜, missingPoint_notMem 𝕜⟩
  have hExDivSymm : exDiv (missingDivisorMap 𝕜).symm = ∅ :=
    exDiv_symm_partialIsoOfDense hDense
  have hCoeff : cInv 𝕜 (missingPoint 𝕜) (missingDivisorMap 𝕜) = -1 :=
    cInv_eq_neg_one_of_exDiv_eq_singleton 𝕜 (missingDivisorMap 𝕜) (missingPoint 𝕜)
      hExDiv hExDivSymm
  exact ⟨planeOpenScheme 𝕜, plane 𝕜, hIrrT, hIrrS, hOvT, hOvS, missingPoint 𝕜,
    missingDivisorMap 𝕜, hExDiv, hExDivSymm, hCoeff⟩

end

end Work.CrauderKatz.BlowUp
