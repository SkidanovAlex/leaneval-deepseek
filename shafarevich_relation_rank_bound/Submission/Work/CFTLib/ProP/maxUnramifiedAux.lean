import Mathlib
import Submission.Work.CFTLib.ShafDeps
import Submission.Work.CFTLib.ProP.Galois
import Submission.Work.CFTLib.ProP.le_maximalUnramifiedProPF
import Submission.Work.CFTLib.ProP.isGalois_maximalUnramifiedProPF
import Submission.Work.CFTLib.Unramified.isEverywhereUnramified_iff
import Submission.Work.CFTLib.Transport.isUnramified_algEquiv
import Submission.Work.CFT.MaxProP.ContCohomology.Defs
import Submission.Work.CFT.MaxProP.ContCohomology.Frattini

/-!
# Auxiliary lemmas for `exists_finset_generates_maxUnramified`

`E = F^{un,p} = maximalUnramifiedProPF F p` is the maximal everywhere-unramified pro-`p`
extension of `F`, and `G = Gal(E/F) = MaxUnramifiedProPGaloisGroup F p`.

This module contains the two structural lemmas that the proof of
`Work.CFTLib.ProP.exists_finset_generates_maxUnramified` needs on the field-theoretic side:

* `isUnramified_isPGroup_of_le_max`: a finite Galois subextension `K ⊆ E` of `E/F` is
  unramified over `F` (in the `CFTLib.IsUnramified` sense) and has `p`-group Galois group.
  This is `Work.CFTLib.ProP.le_maximalUnramifiedProPF` transported from the
  `IntermediateField F (AlgebraicClosure F)` presentation of `K` to the
  `IntermediateField F E` presentation.
* `isProPGroup_GG`: `Gal(E/F)` is a pro-`p` group: every quotient `G ⧸ U` by an open normal
  subgroup is a (finite) `p`-group, by the Galois correspondence.
-/

open NumberField

namespace Work.CFTLib.ProP

noncomputable section

variable (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]

/-- **A finite Galois subextension of `F^{un,p}/F` is unramified with `p`-group Galois group.**

If `K : IntermediateField F (E F p)` is finite dimensional, Galois and a number field, then
`K/F` is everywhere unramified and `Gal(K/F)` is a `p`-group.  Proof: the image
`K.map (E.val) ⊆ AlgebraicClosure F` is a finite Galois intermediate field of the algebraic
closure lying in `E`, so `Work.CFTLib.ProP.le_maximalUnramifiedProPF` applies to it; transport
back along `IntermediateField.equivMap` and the bridge
`Work.CFTLib.Unramified.isEverywhereUnramified_iff`. -/
theorem isUnramified_isPGroup_of_le_max (K : IntermediateField F (E F p))
    [FiniteDimensional F K] [NumberField ↥K] [IsGalois F K] :
    CFTLib.IsUnramified F ↥K ∧ IsPGroup p (K ≃ₐ[F] K) := by
  haveI hgalE : IsGalois F ↥(E F p) := isGalois_maximalUnramifiedProPF F p
  haveI hfin' : FiniteDimensional F ↥(K.map (IntermediateField.val (E F p))) := by
    have : Module.Finite F ↥(K.map (IntermediateField.val (E F p))) :=
      Module.Finite.equiv (IntermediateField.equivMap K
        (IntermediateField.val (E F p))).toLinearEquiv
    exact ‹FiniteDimensional F _›
  haveI hgal' : IsGalois F ↥(K.map (IntermediateField.val (E F p))) :=
    IsGalois.of_algEquiv (IntermediateField.equivMap K (IntermediateField.val (E F p)))
  haveI hnf' : NumberField ↥(K.map (IntermediateField.val (E F p))) :=
    NumberField.of_module_finite F ↥(K.map (IntermediateField.val (E F p)))
  have hle : K.map (IntermediateField.val (E F p)) ≤ E F p := by
    intro x hx
    rw [IntermediateField.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.2
  obtain ⟨hunr, hp⟩ :=
    le_maximalUnramifiedProPF F p (K.map (IntermediateField.val (E F p))) hle
  have hunr' : CFTLib.IsUnramified F ↥(K.map (IntermediateField.val (E F p))) :=
    (Work.CFTLib.Unramified.isEverywhereUnramified_iff F
      ↥(K.map (IntermediateField.val (E F p)))).mp hunr
  exact ⟨Work.CFTLib.Transport.isUnramified_algEquiv
      (IntermediateField.equivMap K (IntermediateField.val (E F p))).symm hunr',
    IsPGroup.of_equiv hp (AlgEquiv.autCongr
      (IntermediateField.equivMap K (IntermediateField.val (E F p)))).symm⟩

/-- **`Gal(F^{un,p}/F)` is a pro-`p` group.**  For every open normal subgroup `U` of `G`, the
quotient `G ⧸ U` is a finite `p`-group: by the infinite Galois correspondence it is the Galois
group of the fixed field of `U`, a finite Galois subextension of `E/F`, which is a
everywhere-unramified `p`-extension of `F` by `isUnramified_isPGroup_of_le_max`. -/
theorem isProPGroup_GG (U : Work.CFT.MaxProP.OpenNormal (GG F p)) :
    IsPGroup p ((GG F p) ⧸ U.carrier) := by
  haveI hgalE : IsGalois F ↥(E F p) := isGalois_maximalUnramifiedProPF F p
  have hfd := fixedField_finiteDimensional (F := F) (p := p) hgalE U.isOpen
  have hgal := fixedField_isGalois (F := F) (p := p) hgalE U.normal U.isOpen
  haveI := hfd
  haveI := hgal
  haveI hnf : NumberField ↥(IntermediateField.fixedField U.carrier) :=
    NumberField.of_module_finite F ↥(IntermediateField.fixedField U.carrier)
  obtain ⟨_hunr, hp⟩ := isUnramified_isPGroup_of_le_max F p (IntermediateField.fixedField U.carrier)
  obtain ⟨e⟩ := quotient_fixedField (F := F) (p := p) hgalE U.normal U.isOpen
  exact IsPGroup.of_equiv hp e.symm

end

end Work.CFTLib.ProP
