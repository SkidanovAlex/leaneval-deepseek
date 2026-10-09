import Mathlib
import Submission.Work.SSGRoute.ZConstruction.AuxAssembly
import Submission.Work.SSGRoute.ZConstruction.AuxChase
import Submission.Work.SSGRoute.ZConstruction.sdiff_not_mem_cs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# (a'): the datum-specific orthogonality at the enlarged place set

The proved chase `Work.SSGRoute.auxDatum_orthogonal_of_productFormula` gives, for a datum `ν` with
`Work.SSGRoute.ZHyp` at `(Λ, S)` and a level-`K` representative set `T` of `cs(S)`,
`∑_{A ∈ T} pair (decomp k A ⊓ G_K) (auxDatum K S ν A) b = 0` for `b` relaxed at `Λ` over `T`.  The
section-4 level step needs the same for an *enlarged* place set `T⁺ ⊇ T`.

The extra summands die because `auxDatum K S ν` vanishes off `cs(S)`: by
`Work.SSGRoute.not_exists_isConjPlace_of_mem_sdiff` (`ZConstruction/sdiff_not_mem_cs.lean`) a place
`A ∈ T⁺∖T` is not `k`-conjugate into `S`, so the summand is `pair (…) 0 b = 0`
(`Work.SSGRoute.pair_zero_left`).

**On the hypothesis.**  The `b`-relaxation used below is `Work.SSGRoute.IsRelaxedDual K Λ T b`
(over the *base* set `T`), not over `T⁺`: `IsRelaxedDual K Λ T⁺ b` imposes *nothing* at the places of
`T⁺∖T` (they lie inside `cs(T⁺)`), while the `T`-relaxation demands unramifiedness — triviality at the
`Λ`-split ones — exactly there, and the failing place is the new one itself, so no choice of `T⁺`
repairs the restriction.  The caller supplies the `T`-relaxation explicitly, carrying the new-place
dual condition along.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- **(a')**: the datum-specific orthogonality at the enlarged place set.  See the module docstring. -/
theorem auxDatum_orthogonal_enlarged (K Λ : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hprod : ZDataMup.IsProductFormula p k Ω K pair)
    (hunr : IsUnramifiedOrthogonal (p := p) K pair)
    {S T Te : Finset (ValuationSubring Ω)}
    (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, KConj K A B → A = B)
    (hTconj : ∀ A ∈ T, ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A)
    (hTcov : ∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ T, KConj K A' B)
    (hTeT : ∀ A ∈ T, A ∈ Te)
    (hTefin : ∀ A ∈ Te, SSGRoute.IsFinPlace k A)
    (hTedisj : ∀ A ∈ Te, ∀ B ∈ Te, KConj K A B → A = B)
    {ν : (Ω ≃ₐ[k] Ω) → ZMod p} (hν : ZHyp (p := p) K Λ S ν)
    {b : (Ω ≃ₐ[k] Ω) → ZMod p} (hb : IsRelaxedDual (p := p) K Λ T b) :
    ∑ A ∈ Te, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
      (auxDatum (p := p) K S ν A) b = 0 := by
  classical
  -- the new places contribute nothing: the datum vanishes there
  have hzero' : ∑ A ∈ Te \ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
      (auxDatum (p := p) K S ν A) b = 0 := by
    refine Finset.sum_eq_zero fun A hA => ?_
    obtain ⟨hATe, hAnT⟩ := Finset.mem_sdiff.mp hA
    have hnot : ¬ ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A :=
      not_exists_isConjPlace_of_mem_sdiff K hTcov hTeT hTedisj hATe hAnT
    simp only [auxDatum]
    rw [if_neg hnot]
    exact pair_zero_left (p := p) hpair (hTefin A hATe)
      ⟨ZDataMup.isCocycleOn_of_le inf_le_right hb.1,
        ZDataMup.isLocConstOn_of_le inf_le_right hb.2.1⟩
  have hunion : T ∪ (Te \ T) = Te := Finset.union_sdiff_of_subset (fun a ha => hTeT a ha)
  calc ∑ A ∈ Te, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (auxDatum (p := p) K S ν A) b
      = ∑ A ∈ T ∪ (Te \ T), pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
          (auxDatum (p := p) K S ν A) b := by rw [hunion]
    _ = ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (auxDatum (p := p) K S ν A) b
          + ∑ A ∈ Te \ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
              (auxDatum (p := p) K S ν A) b := Finset.sum_union Finset.disjoint_sdiff
    _ = ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (auxDatum (p := p) K S ν A) b
          + 0 := by rw [hzero']
    _ = 0 := by
      rw [add_zero]
      exact auxDatum_orthogonal_of_productFormula (p := p) hpair hprod hunr hTfin hTdisj hTconj
        (fun B _ hconj => hTcov B hconj) hν hb

end Work.SSGRoute


/-!
## Elaborator notes (paid for with build cycles -- read before re-deriving)

* **The place-set equality.**  `T ∪ (T⁺∖T) = T⁺` for `T ⊆ T⁺` is
  `Finset.union_sdiff_of_subset (fun a ha => hTeT a ha)`, where `hTeT : ∀ A ∈ T, A ∈ T⁺`.  The
  `ext`/`simp only [Finset.mem_union, Finset.mem_sdiff]` route type-mismatches here.
* **The sum split.**  Use the shape of `Work.SSGRoute.auxExists_of_pairing_and_realisation`
  step (9): `conv_lhs => rw [← hunion]` followed by `Finset.sum_union Finset.disjoint_sdiff`, or a
  `calc` as in this file.  `Finset.sum_subset` is the wrong tool (its `⊆`-argument is elaborated
  with implicit binders and the `∀`-form of the subset hypothesis does not unify with it).
* **Existential hypotheses are applied to the existential.**  Three slips of this family were paid for
  in this lane this session: `hTcov B hc` must be `hTcov B ⟨A', hA', hc⟩` (the hypothesis is
  `∃ A ∈ S, IsConjPlace k A B`); the filter predicate must be written `¬ ∃ t ∈ T, KConj K t A` and not
  `∀ t ∈ T, ¬ KConj K t A` (different propositions under negation); and `IsConjPlace k A B` has `B` as
  the *target*, so `hSS⁺` must be instantiated at the target place and not at the representative.
-/
