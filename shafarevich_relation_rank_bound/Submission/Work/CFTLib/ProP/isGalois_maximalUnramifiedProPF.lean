import Mathlib
import Submission.Work.CFTLib.ShafDeps

namespace Work.CFTLib.ProP

open LeanEval.NumberTheory

/-- The index type of the supremum defining `F^{un,p}`: an intermediate field of `AlgebraicClosure F`
carrying all five properties (finite dimensional, Galois, `p`-group Galois group, a number field,
and everywhere unramified).

It is a `structure` rather than a `Subtype` of a `∧`-product so that the `FiniteDimensional`,
`IsGalois` and `NumberField` requirements are available as *typeclass instances* to a proof working
with an element of it. -/
structure ProPExtData (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)] where
  /-- the intermediate field -/
  M : IntermediateField F (AlgebraicClosure F)
  /-- it is finite dimensional over `F` -/
  fd : FiniteDimensional F M
  /-- it is Galois over `F` -/
  gal : IsGalois F M
  /-- its Galois group is a `p`-group -/
  pg : IsPGroup p (M ≃ₐ[F] M)
  /-- it is a number field -/
  nf : NumberField M
  /-- it is everywhere unramified over `F` -/
  unr : IsEverywhereUnramified F M

attribute [instance] ProPExtData.fd ProPExtData.gal ProPExtData.nf

/-- `maximalUnramifiedProPF F p` is the supremum of `M` over the bundled index `ProPExtData`. -/
lemma maximalUnramifiedProPF_eq_iSup
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)] :
    maximalUnramifiedProPF F p =
      ⨆ (i : ProPExtData F p), (i.M : IntermediateField F (AlgebraicClosure F)) := by
  unfold maximalUnramifiedProPF
  refine le_antisymm ?_ ?_
  · refine iSup_le fun M => iSup_le fun h1 => iSup_le fun h2 => iSup_le fun h3 =>
      iSup_le fun h4 => iSup_le fun h5 => ?_
    let i : ProPExtData F p := ⟨M, h1, h2, h3, h4, h5⟩
    exact le_iSup (fun i : ProPExtData F p => (i.M : IntermediateField F (AlgebraicClosure F))) i
  · refine iSup_le fun i => ?_
    have h : (i.M : IntermediateField F (AlgebraicClosure F)) ≤
        (⨆ (_ : FiniteDimensional F ↥(i.M)) (_ : IsGalois F ↥(i.M))
          (_ : IsPGroup p (↥(i.M) ≃ₐ[F] ↥(i.M))) (_ : NumberField ↥(i.M))
          (_ : IsEverywhereUnramified F ↥(i.M)),
          (i.M : IntermediateField F (AlgebraicClosure F))) := by
      rw [iSup_pos i.fd, iSup_pos i.gal, iSup_pos i.pg, iSup_pos i.nf, iSup_pos i.unr]
    refine h.trans ?_
    exact le_iSup (fun (M : IntermediateField F (AlgebraicClosure F)) =>
      ⨆ (_ : FiniteDimensional F M) (_ : IsGalois F M)
        (_ : IsPGroup p (M ≃ₐ[F] M)) (_ : NumberField M)
        (_ : IsEverywhereUnramified F M), M) i.M

/-- `F^{un,p}` is normal over `F`: a supremum of normal extensions is normal. -/
instance normal_maximalUnramifiedProPF
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)] :
    Normal F ↥(maximalUnramifiedProPF F p) := by
  rw [maximalUnramifiedProPF_eq_iSup]
  exact IntermediateField.normal_iSup
    (t := fun i : ProPExtData F p => (i.M : IntermediateField F (AlgebraicClosure F)))

/-- `F^{un,p}` is separable over `F`: a supremum of separable extensions is separable. -/
instance isSeparable_maximalUnramifiedProPF
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)] :
    Algebra.IsSeparable F ↥(maximalUnramifiedProPF F p) := by
  rw [maximalUnramifiedProPF_eq_iSup]
  exact IntermediateField.isSeparable_iSup
    (t := fun i : ProPExtData F p => (i.M : IntermediateField F (AlgebraicClosure F)))

/-- **`F^{un,p}/F` is Galois.**  `maximalUnramifiedProPF F p` is, by definition, the supremum
(inside `AlgebraicClosure F`) of the finite-dimensional Galois everywhere-unramified intermediate
fields of `F` whose Galois group is a `p`-group.  A supremum of normal (indeed Galois) extensions
is normal, and a supremum of separable extensions is separable, so it is Galois:

`IsGalois F ↥(maximalUnramifiedProPF F p)`.

Mathlib's `IntermediateField.normal_iSup` and `IntermediateField.isSeparable_iSup` do not need
directedness (the index type may be arbitrary); to apply them, bundle the dependent sup
`⨆ (M) (_ : FiniteDimensional F M) (_ : IsGalois F M) (_ : IsPGroup p (M ≃ₐ[F] M))
(_ : NumberField M) (_ : IsEverywhereUnramified F M), M`
as `⨆ (i : σ), i.1` for the subtype `σ` of intermediate fields carrying all five properties
(`iSup_subtype'`-type rewriting), then conclude `Normal` and `IsSeparable`.
A structure with an instance field `NumberField` may be needed to keep the `NumberField`
instance available when stating `IsEverywhereUnramified F M`. -/
theorem isGalois_maximalUnramifiedProPF
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)] :
    IsGalois F ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p) :=
  isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

end Work.CFTLib.ProP
