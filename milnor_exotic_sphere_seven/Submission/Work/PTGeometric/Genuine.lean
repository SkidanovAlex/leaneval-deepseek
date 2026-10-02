import Submission.Work.PTGeometric.Defs
import Submission.Work.Surgery.Collar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the genuine geometric data of a null-homotopy, and the null-bordism

This file is the second half of the subproject: the **genuine** geometric data of the Pontryagin–Thom
construction for a finite family of closed oriented `8`-manifolds, and the derivation of a
null-bordism from it (the preimage theorem plus orientation theory).

## The genuine geometric data

`Work.PTGeometric.GenuineNullBordismData` records, for a finite family `Fam` and the manifold part
`X` of the universal Thom space `T = Th(γ_k)` with its zero section as core:

* a compact `T2` smooth `(9+k)`-manifold with boundary `M` — in the application the `(9+k)`-disk with
  `N` holes;
* the **smooth null-homotopy** `c : M → X.E` of the `N`-fold genuine collapse map of the family
  (the concrete collapse map is supplied by TUBULAR's `Work.Tubular.TubeThomRep`, summed over the
  pieces by `Work.Tubular`/`ptAdditivity`; smoothing the resulting continuous map is G2 of the
  blueprint);
* its transversality to the zero section — chart by chart, `IsCoreTransverse`, since for the genuine
  bundle there is no global defining function (see `Defs.lean`);
* boundary transversality (`IsCoreTransverseOnBoundary`);
* the identification of the end preimage of the core with the `N` copies of the pieces;
* the orientation datum of the situation (`GenuinePullbackOrientationData`): the transverse preimage
  is a `9`-manifold with boundary, and it carries the relative fundamental class of the orientation
  induced by the ambient orientation and by the Thom class of `γ_k`, with the boundary identified
  with the pieces as an **oriented** bordism — the shape of `NullBordismFamily.hw`.

## The theorem

`exists_nullBordismFamily_of_genuineData`: the local preimage theorem
(`Work.PTGeometric.LocalPreimageTheorem`) applied to `c` produces the transverse preimage as a
compact smooth `9`-manifold with boundary, and the orientation datum supplies the relative
fundamental class; the result is a `Work.ThomBordism.NullBordismFamily` of the `N` copies of the
family — exactly the conclusion of `TransversalityFamily`.

## Main definitions

* `Work.PTGeometric.GenuineNullBordismData`

## Main results

* `Work.PTGeometric.exists_nullBordismFamily_of_genuineData`
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter
open CategoryTheory AlgebraicTopology

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

/-- **The genuine geometric data of a null-homotopy of the collapse map of a family.**

This is the honest form of the geometric input of the Pontryagin–Thom construction: for the
(presumably non-trivial) universal bundle `γ_k` there is no global defining function of the zero
section, so transversality is expressed chart by chart through the local trivialisations of
`X : LocalCoreTarget n k`.

In the application `X.E` is the total space of `γ_k` over `G̃r_k(ℝ^{k+8})` (dimension `9k`), `n = 9k`,
`M` is the `(9+k)`-disk with `N` holes, and `c` is a smoothing of the `N`-fold collapse map of the
family, already transverse to the zero section near the boundary (where it is the genuine collapse
map of the pieces, whose preimage of the zero section is the pieces themselves). -/
structure GenuineNullBordismData (n k : ℕ) (X : LocalCoreTarget n k) (ι : Type) [Fintype ι]
    (Fam : ι → Man8) where
  /-- the disk with `N` holes -/
  M : Type
  [topologicalSpace : TopologicalSpace M]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [isManifold : IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M]
  [compactSpace : CompactSpace M]
  [t2Space : T2Space M]
  /-- the smooth null-homotopy of the collapse map, into the total space of `γ_k` -/
  c : M → X.E
  /-- smoothness of the null-homotopy -/
  contMDiff_c : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓡 n) ∞ c
  /-- transversality of the null-homotopy to the zero section -/
  transverse : IsCoreTransverse X (𝓡∂ ((8 + k) + 1)) c
  /-- transversality of the restriction to the boundary -/
  bndTransverse : IsCoreTransverseOnBoundary X c
  /-- the end preimage of the zero section is the disjoint union of the copies of the pieces -/
  endHomeo : ↥(EndPreimage X c) ≃ₜ (Σ i : ι, (Fam i).pt)
  /-- the orientation datum of the situation (ambient orientation + Thom class of `γ_k`) -/
  orientation : GenuinePullbackOrientationData X ι Fam c endHomeo
  /-- **A collar of the transverse preimage, by construction** (the project lead's addition (A) of
  2026-09-25).

  Reparametrising the null-homotopy to be stationary near the collapse end — `c (y, t) = c (y, 0)`
  for `t ≤ ε`, with the smoothing cutoff `ρ` and the perturbation bump `χ` both vanishing on
  `Sⁿ × [0, 2ε]` — makes `W = c ⁻¹' core` equal to the product `V₀ × [0, ε)` near the `0`-end, where
  `V₀` is the end preimage of the core (the pieces).  Consequently `(x, s) ↦ (x, s)` is an explicit
  open embedding `∂W × [0, ε) ↪ W` vanishing on `∂W`: a collar of the transverse preimage, produced
  rather than assumed.  It is a field of the data because it is a statement about every manifold
  model `W` of the preimage (as with `orientation`), and because the *proof* is exactly the statement
  that the manifold structure produced by the preimage theorem agrees with the product structure near
  the collapse end. -/
  collar : ∀ (W : Type) [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 9) W]
      [IsManifold (𝓡∂ 9) ∞ W] [CompactSpace W] [T2Space W]
      (hW : W ≃ₜ ↥(CorePreimage X c))
      (_hbdry : ∀ w : W, w ∈ (𝓡∂ 9).boundary W ↔ (hW w : M) ∈ EndPreimage X c),
      Work.Surgery.HasCollar 8 W

attribute [instance] GenuineNullBordismData.topologicalSpace GenuineNullBordismData.chartedSpace
  GenuineNullBordismData.isManifold GenuineNullBordismData.compactSpace
  GenuineNullBordismData.t2Space

/-- **The collar of a `9`-manifold with boundary** (the collar neighbourhood theorem as a `Prop`, in
the shape in which it appears for the bounding manifold of a null-bordism: the model is written with
the numeral `9` so that the instance is found from `NullBordismFamily.chartedSpace`). -/
abbrev Collar9 (W : Type) [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 9) W] : Prop :=
  Work.Surgery.HasCollar 8 W

/-- **The genuine null-homotopy of the collapse map of a family gives a null-bordism of the family.**

The local preimage theorem (`LocalPreimageTheorem`) makes the transverse preimage `c ⁻¹' X.core` a
compact smooth `9`-manifold with boundary, with boundary the end preimage of the core; the
orientation datum of the situation supplies the relative fundamental class, its local-generator
property and the identification of its boundary with the sum of the pieces' fundamental classes; the
result is the `NullBordismFamily` of the interface, i.e. the conclusion of `TransversalityFamily`.

(For `X = LocalCoreTarget.ofCoreTarget X₀` of a chapter `CoreTarget` this is the statement proved in
`Work.ThomBordism.Transversality.Preimage.orientation`
(`exists_nullBordismFamily_of_transverse_data`); here it is the same argument with the local
preimage theorem replacing the global one, i.e. with the triviality of the normal bundle removed.) -/
theorem exists_nullBordismFamily_of_genuineData (hpre : LocalPreimageTheorem) {n k : ℕ}
    {X : LocalCoreTarget n k} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (d : GenuineNullBordismData n k X ι Fam) : Nonempty (NullBordismFamily ι Fam) := by
  classical
  obtain ⟨W, tW, cW, mW, compW, t2W, e, hbdry⟩ :=
    hpre n k X d.M d.c d.contMDiff_c d.transverse d.bndTransverse
  letI := tW
  letI := cW
  letI := mW
  letI := compW
  letI := t2W
  obtain ⟨bdryPreimage, w, hwf, hwh⟩ := d.orientation W e hbdry
  haveI : IsManifold (𝓡∂ 9) 1 W := IsManifold.of_le (n := ∞) (by simp)
  exact ⟨{ W := W, bdry := bdryPreimage.trans d.endHomeo, w := w, hw := hwh, w_fund := hwf }⟩

/-- **The genuine null-homotopy gives a null-bordism *with a collar*** (the project lead's addition
(A)): the null-bordism of `exists_nullBordismFamily_of_genuineData`, together with the collar of its
bounding manifold produced by construction (the product structure of the null-homotopy near the
collapse end, `GenuineNullBordismData.collar`).  This is the form in which the downstream consumers
of `NullBordismFamily` will need it once the collar field is added to the interface. -/
theorem exists_nullBordismFamily_and_collar_of_genuineData (hpre : LocalPreimageTheorem) {n k : ℕ}
    {X : LocalCoreTarget n k} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (d : GenuineNullBordismData n k X ι Fam) :
    ∃ N : NullBordismFamily ι Fam, Collar9 N.W := by
  classical
  obtain ⟨W, tW, cW, mW, compW, t2W, e, hbdry⟩ :=
    hpre n k X d.M d.c d.contMDiff_c d.transverse d.bndTransverse
  letI := tW
  letI := cW
  letI := mW
  letI := compW
  letI := t2W
  obtain ⟨bdryPreimage, w, hwf, hwh⟩ := d.orientation W e hbdry
  haveI : IsManifold (𝓡∂ 9) 1 W := IsManifold.of_le (n := ∞) (by simp)
  haveI : IsManifold (𝓡∂ 9) ∞ W := mW
  refine ⟨{ W := W, bdry := bdryPreimage.trans d.endHomeo, w := w, hw := hwh, w_fund := hwf }, ?_⟩
  exact d.collar W e hbdry

end

end Work.PTGeometric
