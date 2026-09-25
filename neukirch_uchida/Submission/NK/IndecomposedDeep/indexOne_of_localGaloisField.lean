import Mathlib
import Submission.NK.IndecomposedDeep.Corrected
import Submission.NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois
import Submission.NK.LocalDecomposition.Local.Korollar1Global

namespace NK.IndecomposedDeep

universe u

set_option linter.unusedVariables false

/-- **The corrected finishing step: maximality of decomposition groups with the local field of the
place in the hypothesis.**

Let `K` be a number field with separable closure `K'`, `A` a place of `K'` over the finite prime `𝔭`,
and `H ≤ D_A = stabSubgroup A` a **closed** subgroup which is isomorphic to the absolute Galois
group of the *local field of the place* `𝔭.adicCompletion K`, and which has finite relative index in
`D_A`.  Then `D_A = H`.

This is Neukirch's maximality statement (Invent. Math. **6** (1969); CoNF (12.1.9)–(12.1.10)) with
the labelling tied to the local field of the place — as happens in the Neukirch–Uchida endgame,
where the labelling is produced by the local correspondence
`NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois` — instead of quantifying
over an arbitrary `p`-adic field (see `README.md` §6 of `Submission/Work/IndecomposedDeep/`).

The hypothesis `hclosed` is Serre's statement that a subgroup of a `p`-adic absolute Galois group
which is isomorphic to a `p`-adic absolute Galois group is closed
(`NK.IndecomposedDeep.LocalSubgroupClosed`), applied to the image of `H` under the local
correspondence.  The two classical inputs are Neukirch's local reconstruction
(`NK.LocalStructure.LocalNUExistence`) and the degree rigidity of `p`-adic fields
(`NK.IndecomposedDeep.LocalDegreeRigidity`).

Suggested route.  Transport `H` along the local correspondence
`e : D_A ≃* Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K)`
(`NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`): the image
`H' = (H.subgroupOf (stabSubgroup A)).map e` is a subgroup of `Gal(L'/L)` (`L = 𝔭.adicCompletion K`)
which is isomorphic to `Gal(L'/L)` (immediate from `hloc`), has finite index (relative index is
transported by `NK.LocalDecomposition.relIndex_map_eq_of_mulEquiv`), and is closed (apply
`hclosed` with the number field `K`, the prime `𝔭`, the separable closure
`SeparableClosure (𝔭.adicCompletion K)` and the subgroup `H'`).  Then
`NK.IndecomposedDeep.localFinishingStep_local` (in
`Submission/Work/IndecomposedDeep/Corrected.lean`) gives `H' = ⊤`, whence `H = stabSubgroup A`. -/
theorem indexOne_of_localGaloisField (hNU : NK.LocalStructure.LocalNUExistence.{u})
    (hrig : NK.IndecomposedDeep.LocalDegreeRigidity.{u})
    (hclosed : ∀ (L : Type u) [Field L] [NumberField L]
      (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
      [IsSepClosure (𝔮.adicCompletion L) L']
      (H : Subgroup Gal(L'/𝔮.adicCompletion L)),
      Nonempty (H ≃* Gal(SeparableClosure (𝔮.adicCompletion L)/𝔮.adicCompletion L)) →
        IsClosed (H : Set Gal(L'/𝔮.adicCompletion L)))
    {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K')
      = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭)
    (H : Subgroup Gal(K'/K)) (hHcl : IsClosed (H : Set Gal(K'/K)))
    (hHle : H ≤ NK.BrauerTwist.stabSubgroup A)
    (hrel : 0 < H.relIndex (NK.BrauerTwist.stabSubgroup A))
    (hloc : Nonempty (H ≃* Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K))) :
    NK.BrauerTwist.stabSubgroup A = H := by
  classical
  -- The local correspondence `D_A ≃* Gal(L'/L)`, `L = 𝔭.adicCompletion K`, computed by
  -- `NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`.  Note that `D_A`
  -- (i.e. `NK.BrauerTwist.stabSubgroup A`) and `NK.Mine.decompositionGroupOf K K' A` are the
  -- same subgroup of `Gal(K'/K)`, so the isomorphism may be re-typed directly.
  obtain ⟨e₀⟩ := NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois 𝔭 A hA
  let D : Subgroup Gal(K'/K) := NK.BrauerTwist.stabSubgroup A
  let e : ↥D ≃* Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K) := e₀
  -- the image `H'` of `H ≤ D_A` in the local absolute Galois group
  let H' : Subgroup Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K) :=
    (H.subgroupOf D).map (e : ↥D →* Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K))
  -- `H'` is isomorphic to the whole local absolute Galois group, because `H` is
  obtain ⟨eH⟩ := hloc
  have hH'iso : Nonempty (↥H' ≃* Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K)) :=
    ⟨(MulEquiv.subgroupMap e (H.subgroupOf D)).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hHle).trans eH)⟩
  -- `H'` is closed: this is the input `hclosed` (Serre: a subgroup of the absolute Galois group of
  -- a `p`-adic field isomorphic to such a group is closed)
  have hH'cl : IsClosed (H' : Set Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K)) :=
    hclosed K 𝔭 (SeparableClosure (𝔭.adicCompletion K)) H' hH'iso
  -- `H'` has finite index, the relative index being transported by the correspondence
  have hH'fin : H'.FiniteIndex := ⟨by
    show ((H.subgroupOf D).map
      (e : ↥D →* Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K))).index ≠ 0
    rw [Subgroup.index_map_equiv (H.subgroupOf D) e]
    exact Nat.pos_iff_ne_zero.mp hrel⟩
  -- the local finishing step: a closed finite-index subgroup isomorphic to the whole group is all
  -- of it
  have hH'top : H' = ⊤ :=
    NK.IndecomposedDeep.localFinishingStep_local hNU hrig K 𝔭 H' hH'cl hH'fin hH'iso
  -- `H' = ⊤` forces `D_A ≤ H`, and `H ≤ D_A` is a hypothesis
  have hDH : D ≤ H := by
    intro x hx
    have hmem : e ⟨x, hx⟩ ∈ H' := by rw [hH'top]; exact trivial
    have hmem' : e ⟨x, hx⟩ ∈ (H.subgroupOf D).map
        (e : ↥D →* Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K)) := hmem
    rw [Subgroup.mem_map] at hmem'
    obtain ⟨y, hy, hye⟩ := hmem'
    have hyx : y = ⟨x, hx⟩ := e.injective hye
    rw [hyx] at hy
    exact hy
  exact le_antisymm hDH hHle

end NK.IndecomposedDeep
