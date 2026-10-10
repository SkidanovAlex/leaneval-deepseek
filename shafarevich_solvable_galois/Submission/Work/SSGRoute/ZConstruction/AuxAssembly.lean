import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.ZConstruction.AuxChase
import Submission.Work.SSGRoute.ZConstruction.exists_KConj_reps
import Submission.Work.SSGRoute.ZConstruction.kConj_of_local_agree
import Submission.Work.SSGRoute.eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `AuxExists` from the local Tate system and the Tate--Poitou realisation

`Work.SSGRoute.AuxExists` (`ZConstruction/ZDataAux.lean`) is the auxiliary-class obligation of
Schmidt--Wingberg §4, p. 18, and the only obligation of the node
`Work.SSGRoute.shafarevich_z_construction` beyond the one-dimensional gate `Work.SSGRoute.MupGate`.
This file splits it into

* `Work.SSGRoute.AuxPairingGate K` -- the existence of one local Tate system `pair` with the
  Hilbert-symbol product formula and the vanishing of the pairing of two inertia-trivial classes
  (`ZConstruction/AuxInterface.lean`); and
* `Work.SSGRoute.AuxRealisationExt K Λ M` (defined below) -- the **Tate--Poitou degree-one
  realisation** of local data which is orthogonal to the relaxed dual Selmer group, together with
  the vanishing on the involutions of `G_K`;

and proves, from those two gates alone, `Work.SSGRoute.AuxExists K Λ S`.  The bridge is the *proved*
diagram chase `Work.SSGRoute.auxDatum_orthogonal_of_productFormula` (`ZConstruction/AuxChase.lean`),
which supplies the orthogonality hypothesis of the realisation from the hypotheses `ZHyp` on the
datum -- so no arithmetic remains in the assembly itself.

## The shape of the realisation gate, and the place sets

The realisation is applied at a place set `T'` of pairwise level-`K`-non-conjugate finite places
which

* contains a base set `T` of representatives of the level-`K` classes of `cs(S)` (so that the datum
  prescribed at `T` is the local datum of the given class, `Work.SSGRoute.auxDatum`), and
* lies inside `cs(S')` for the enlarged set `S'` of the p. 18 step, so that the realised class is
  automatically *unramified* at every place outside `cs(S')` that is not split in the level `M = N`
  of the other summand of the §4 induction (this is the clause `hyS` of `ZHyp` at `(N,S')`).

The orthogonality hypothesis is stated with the relaxed dual Selmer conditions at the **base** set
`T`, not at `T'`.  This is the correct (stronger) form: `IsRelaxedDual K Λ T b` implies
`IsRelaxedDual K Λ T' b` for `T ⊆ T'` (the "outside `cs(T)`" conditions are the stronger ones), so
orthogonality against the relaxed duals at `T` implies it against those at `T'`, which is what the
Tate--Poitou counting identity consumes.  Conversely it is exactly what the chase proves, since the
places at which the datum ramifies outside `cs(S)` lie outside `cs(T)` (`ZHyp.hyT`) and are `Λ`-split
(`ZHyp.hyS`), where the relaxed dual `b` is locally trivial.

## The vanishing on the involutions

For odd `p` the last clause of the gate is free
(`Work.SSGRoute.eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot`: `Gal(Ω/K)` has no element of
order two as soon as `K` contains a primitive `p`-th root of unity for an odd prime `p`, so
`c ^ 2 = 1` forces `c = 1` and the clause reduces to `z 1 = 0`).  It is kept in the gate rather than
assumed away because for `p = 2` it is a genuine part of the §4 construction (the `p = 2` correction).
-/

open scoped Pointwise BigOperators

open Classical

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-! ## The two gates -/

/-- **Gate (R): the Tate--Poitou degree-one realisation, in the form consumed by the p. 18 step.**
See the module docstring for the shape of the place sets. -/
def AuxRealisationExt (K Λ M : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] : Prop :=
  ∀ (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p),
    ZDataMup.IsLocalTateSystem p k Ω K pair →
    ZDataMup.IsProductFormula p k Ω K pair →
    IsUnramifiedOrthogonal (p := p) K pair →
    ∀ (T T' : Finset (ValuationSubring Ω)),
      (∀ A ∈ T', SSGRoute.IsFinPlace k A) →
      (∀ A ∈ T', ∀ B ∈ T', KConj K A B → A = B) →
      (∀ A ∈ T, A ∈ T') →
    ∀ (f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p),
      (∀ A ∈ T', SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A)) →
      (∀ A ∈ T', SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A)) →
      (∀ A ∈ T' \ T, f A = 0) →
      (∀ b : (Ω ≃ₐ[k] Ω) → ZMod p, IsRelaxedDual (p := p) K Λ T b →
        ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b = 0) →
      ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
        SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
        (∀ A ∈ T', ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = f A σ) ∧
        (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ T', ¬ KConj K A B) → ¬ SSGRoute.IsSplitIn k M B →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0)

/-! ## Elementary consequences of the local axioms -/

/-- Additivity on `G_K` of a level-`K` cocycle (the restriction `res k K` is trivial on `G_K`). -/
theorem addOn_of_isCocycleOn {K : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] {z : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hz : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z) :
    ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h := by
  intro g hg h hh
  rw [hz g hg h hh, ZDataMup.res_eq_one_of_mem_fixingSubgroup hg, one_smul]

/-- The local pairing of the zero class on a local group vanishes (it is a coboundary). -/
theorem pair_zero_left {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p}
    (hpair : ZDataMup.IsLocalTateSystem p k Ω K pair)
    {A : ValuationSubring Ω} (hA : SSGRoute.IsFinPlace k A)
    {b : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b) :
    pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (0 : (Ω ≃ₐ[k] Ω) → ZMod p) b = 0 := by
  refine hpair.vanishes_coboundary _ ⟨A, hA, rfl⟩ (0 : (Ω ≃ₐ[k] Ω) → ZMod p) b ?_ hb (Or.inl ?_)
  · exact ⟨fun g hg h hh => by simp,
      ⟨⊤, isOpen_univ, fun g hg u hu huH => rfl⟩⟩
  · exact ⟨0, fun g hg => by simp⟩


/-- **Gate (R) without the vanishing on the involutions.**  Same statement as
`Work.SSGRoute.AuxRealisationExt` except that the conclusion does not require the realised class to
kill the involutions of `G_K`.  This is the form in which the odd-`p` lane proves the realisation
(the level-`K` Tate--Poitou counting identity, cf. `ZSplit/kRealized_of_orthogonal_of_counting` and
`ZDataMup.tatePoitou_h1_realisation`, all of which carry `p ≠ 2`).  For odd `p` the missing clause is
*automatic*, which is the content of `Work.SSGRoute.auxRealisationExt_of_noInv` below: `G_K` has no
element of order two as soon as `K` contains a primitive `p`-th root of unity. -/
def AuxRealisationNoInv (K Λ M : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] : Prop :=
  ∀ (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p),
    ZDataMup.IsLocalTateSystem p k Ω K pair →
    ZDataMup.IsProductFormula p k Ω K pair →
    IsUnramifiedOrthogonal (p := p) K pair →
    ∀ (T T' : Finset (ValuationSubring Ω)),
      (∀ A ∈ T', SSGRoute.IsFinPlace k A) →
      (∀ A ∈ T', ∀ B ∈ T', KConj K A B → A = B) →
      (∀ A ∈ T, A ∈ T') →
    ∀ (f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p),
      (∀ A ∈ T', SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A)) →
      (∀ A ∈ T', SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A)) →
      (∀ A ∈ T' \ T, f A = 0) →
      (∀ b : (Ω ≃ₐ[k] Ω) → ZMod p, IsRelaxedDual (p := p) K Λ T b →
        ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b = 0) →
      ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
        SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
        (∀ A ∈ T', ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = f A σ) ∧
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ T', ¬ KConj K A B) → ¬ SSGRoute.IsSplitIn k M B →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0)


/-! ## The assembly -/

/-- **`AuxExists` from the two gates.**  See the module docstring. -/
theorem auxExists_of_pairing_and_realisation {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hP : AuxPairingGate (p := p) K)
    (hR : ∀ (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M],
      AuxRealisationExt (p := p) K Λ M)
    {S : Finset (ValuationSubring Ω)} (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) :
    AuxExists (p := p) K Λ S := by
  classical
  refine auxExists_of_weakened (p := p) ?_
  intro N _instNf _instNg hΛN S' hS'fin hS'disj hS'sub _hS'ram L _instLadd _instLmod _instLfin hL y₁ hy₁
  -- (1) the local Tate system
  obtain ⟨pair, hpair, hprod, hunr⟩ := hP
  -- (2) the base place set: representatives of the level-`K` classes of `cs(S)`
  obtain ⟨T, hTfin, hTdisj, hTconj, hTcov⟩ := ZConstruction.exists_KConj_reps (k := k) (Ω := Ω) K S hSfin
  -- (3) the enlarged place set: representatives of the level-`K` classes of `cs(S')`
  obtain ⟨T'', hT''fin, hT''disj, hT''conj, hT''cov⟩ := ZConstruction.exists_KConj_reps (k := k) (Ω := Ω) K S' hS'fin
  -- (4) the realisation place set: `T` together with the new classes of `cs(S')`
  set T' : Finset (ValuationSubring Ω) := T ∪ T''.filter (fun A => ¬ ∃ t ∈ T, KConj K t A) with hT'
  have hT'T : ∀ A ∈ T, A ∈ T' := by
    intro A hA
    rw [hT']
    exact Finset.mem_union_left _ hA
  have hT'fin : ∀ A ∈ T', SSGRoute.IsFinPlace k A := by
    intro A hA
    rw [hT', Finset.mem_union] at hA
    rcases hA with hA | hA
    · exact hTfin A hA
    · exact hT''fin A (Finset.mem_filter.mp hA).1
  have hT'disj : ∀ A ∈ T', ∀ B ∈ T', KConj K A B → A = B := by
    intro A hA B hB hAB
    rw [hT', Finset.mem_union] at hA hB
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact hTdisj A hA B hB hAB
    · exact absurd ⟨A, hA, hAB⟩ (Finset.mem_filter.mp hB).2
    · exact absurd ⟨B, hB, ZConstruction.kConj_symm hAB⟩ (Finset.mem_filter.mp hA).2
    · exact hT''disj A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1 hAB
  have hT'sub : ∀ A ∈ T', ∃ A' ∈ S', SSGRoute.IsConjPlace k A' A := by
    intro A hA
    rw [hT', Finset.mem_union] at hA
    rcases hA with hA | hA
    · obtain ⟨A'', hA'', hc⟩ := hTconj A hA
      exact hS'sub A ⟨A'', hA'', hc⟩
    · exact hT''conj A (Finset.mem_filter.mp hA).1
  have hT'cov : ∀ B : ValuationSubring Ω, (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ T', KConj K A' B := by
    intro B hB
    obtain ⟨A, hA, hc⟩ := hT''cov B hB
    by_cases hnew : ∃ t ∈ T, KConj K t A
    · obtain ⟨t, ht, htA⟩ := hnew
      exact ⟨t, hT'T t ht, ZConstruction.kConj_trans htA hc⟩
    · exact ⟨A, by rw [hT']; exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hA, hnew⟩), hc⟩
  -- (5) the datum vanishes on `T' ∖ T` away from `cs(S)`, hence its prescribed value is `0` there
  have hT'zero : ∀ A ∈ T' \ T, ¬ ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A := by
    intro A hA hconj
    obtain ⟨hAT', hAnT⟩ := Finset.mem_sdiff.mp hA
    obtain ⟨t, ht, hc⟩ := hTcov A hconj
    have hEq : A = t := hT'disj A hAT' t (hT'T t ht) (ZConstruction.kConj_symm hc)
    exact hAnT (hEq ▸ ht)
  -- (6) the one-dimensional module `L` is `ZMod p`
  haveI : FiniteDimensional (ZMod p) L := Module.Finite.of_finite
  haveI : Nontrivial L := Module.finrank_pos_iff.mp (by rw [hL]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : L)
  have hap : ∀ x : ZMod p, LinearMap.toSpanSingleton (ZMod p) L v x = x • v := by
    intro x
    have h := map_smul (LinearMap.toSpanSingleton (ZMod p) L v) x (1 : ZMod p)
    rw [show x • (1 : ZMod p) = x from by rw [smul_eq_mul, mul_one],
      LinearMap.toSpanSingleton_apply_one] at h
    exact h
  have hinj : Function.Injective (LinearMap.toSpanSingleton (ZMod p) L v) := by
    intro a b hab
    have h2 : a • v = b • v := by rw [← hap a, ← hap b]; exact hab
    have h3 : (a - b) • v = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv
  have hrank : Module.finrank (ZMod p) (ZMod p) = Module.finrank (ZMod p) L := by
    rw [hL, CommSemiring.finrank_self]
  let e : ZMod p ≃ₗ[ZMod p] L := LinearEquiv.ofInjectiveOfFinrankEq _ hinj hrank
  -- (7) the datum transported to `ZMod p`
  set ν : (Ω ≃ₐ[k] Ω) → ZMod p := fun σ => e.symm (y₁ σ) with hν
  have hνhyp : ZHyp (p := p) K Λ S ν :=
    ZHyp.mapAdd (f := (e.symm : L →ₗ[ZMod p] ZMod p).toAddMonoidHom) hy₁
  -- (8) the prescribed data at `T'`
  set f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p :=
    fun A => auxDatum (p := p) K S ν A with hf
  have hfT : ∀ A ∈ T, f A = ν := by
    intro A hA
    simp only [hf, auxDatum]
    rw [if_pos (hTconj A hA)]
  have hfzero : ∀ A ∈ T' \ T, f A = 0 := by
    intro A hA
    have hnot := hT'zero A hA
    simp only [hf, auxDatum]
    rw [if_neg hnot]
  have hfcoc : ∀ A ∈ T', SSGRoute.IsCocycleOn (SSGRoute.res k K)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) := by
    intro A hA
    by_cases hAT : A ∈ T
    · rw [hfT A hAT]
      exact isCocycleOn_of_addOn inf_le_right
        (fun g hg h hh =>
          hνhyp.add g (Subgroup.mem_inf.mp hg).2 h (Subgroup.mem_inf.mp hh).2)
    · have hmem : A ∈ T' \ T := Finset.mem_sdiff.mpr ⟨hA, hAT⟩
      rw [hfzero A hmem]
      exact fun g hg h hh => by simp
  have hfloc : ∀ A ∈ T', SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) := by
    intro A hA
    by_cases hAT : A ∈ T
    · rw [hfT A hAT]
      exact ZDataMup.isLocConstOn_of_le inf_le_right hνhyp.locconst
    · have hmem : A ∈ T' \ T := Finset.mem_sdiff.mpr ⟨hA, hAT⟩
      rw [hfzero A hmem]
      exact ⟨⊤, isOpen_univ, fun g hg u hu huH => rfl⟩
  -- (9) the orthogonality: the extra places carry the zero datum, the places of `T` carry `ν`
  have horth : ∀ b : (Ω ≃ₐ[k] Ω) → ZMod p, IsRelaxedDual (p := p) K Λ T b →
      ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b = 0 := by
    intro b hb
    have hunion : T ∪ (T' \ T) = T' := Finset.union_sdiff_of_subset (fun a ha => hT'T a ha)
    have hdisj : Disjoint T (T' \ T) := Finset.disjoint_sdiff
    have hsplit : ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b
        = ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b
          + ∑ A ∈ T' \ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b := by
      conv_lhs => rw [← hunion]
      rw [Finset.sum_union hdisj]
    rw [hsplit]
    have hzero : ∑ A ∈ T' \ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b = 0 := by
      refine Finset.sum_eq_zero fun A hA => ?_
      rw [hfzero A hA]
      exact pair_zero_left (p := p) hpair (hT'fin A (Finset.mem_sdiff.mp hA).1)
        ⟨ZDataMup.isCocycleOn_of_le inf_le_right hb.1,
          ZDataMup.isLocConstOn_of_le inf_le_right hb.2.1⟩
    rw [hzero, add_zero]
    exact auxDatum_orthogonal_of_productFormula (p := p) hpair hprod hunr
      hTfin hTdisj hTconj (fun B _ hconj => hTcov B hconj) hνhyp hb
  -- (10) the realisation
  obtain ⟨z, hzcoc, hzloc, hzagree, hzinf, hzunr⟩ :=
    hR N pair hpair hprod hunr T T' hT'fin hT'disj hT'T f hfcoc hfloc hfzero horth
  have hzadd := addOn_of_isCocycleOn hzcoc
  -- (11) the realised class in `L`
  set yAux : (Ω ≃ₐ[k] Ω) → L := fun σ => e (z σ) with hyAux
  refine ⟨yAux, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- additivity
    intro g hg h hh
    show e (z (g * h)) = e (z g) + e (z h)
    rw [hzadd g hg h hh, map_add]
  · -- local constancy
    obtain ⟨U, hUo, hU⟩ := hzloc
    refine ⟨U, hUo, fun g hg u hu huK => ?_⟩
    show e (z (g * u)) = e (z g)
    rw [hU g hg u hu huK]
  · -- `hyS` at `(N,S')`
    intro B hB hnotS hnotsplit σ hσK hσI
    have hnotT' : ∀ A ∈ T', ¬ KConj K A B := by
      intro A hA hc
      obtain ⟨A'', hA'', hc''⟩ := hT'sub A hA
      exact hnotS A'' hA''
        (SSGRoute.isConjPlace_trans hc'' (ZConstruction.kConj_isConjPlace hc))
    show e (z σ) = 0
    rw [hzunr B hB hnotT' hnotsplit σ hσK hσI, map_zero]
  · -- vanishing on the involutions
    intro c hc hc2
    show e (z c) = 0
    rw [hzinf c hc hc2, map_zero]
  · -- agreement with `y₁` on the local groups of `cs(S)`
    intro B hB hconj σ hσ
    obtain ⟨t, ht, hc⟩ := hTcov B hconj
    have hloc : ∀ ρ ∈ SSGRoute.decomp k t ⊓ K.fixingSubgroup, yAux ρ = y₁ ρ := by
      intro ρ hρ
      have hρ' : ρ ∈ SSGRoute.decomp k t ⊓ K.fixingSubgroup := hρ
      show e (z ρ) = y₁ ρ
      rw [hzagree t (hT'T t ht) ρ hρ', hfT t ht]
      show e (e.symm (y₁ ρ)) = y₁ ρ
      rw [LinearEquiv.apply_symm_apply]
    exact ZConstruction.kConj_of_local_agree (k := k) (Ω := Ω)
      (fun g hg h hh => by
        show e (z (g * h)) = e (z g) + e (z h)
        rw [hzadd g hg h hh, map_add])
      hy₁.add hc hloc σ (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hσ).1, (Subgroup.mem_inf.mp hσ).2⟩)
  · -- vanishing on the local groups of `cs(S') ∖ cs(S)`
    intro B hB hnotS hconj σ hσ
    obtain ⟨A, hA, hc⟩ := hT'cov B hconj
    have hAnT : A ∉ T := by
      intro hAT
      obtain ⟨A'', hA'', hc''⟩ := hTconj A hAT
      exact hnotS A'' hA''
        (SSGRoute.isConjPlace_trans hc'' (ZConstruction.kConj_isConjPlace hc))
    have hmem : A ∈ T' \ T := Finset.mem_sdiff.mpr ⟨hA, hAnT⟩
    have hloc : ∀ ρ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, yAux ρ = (0 : (Ω ≃ₐ[k] Ω) → L) ρ := by
      intro ρ hρ
      show e (z ρ) = 0
      rw [hzagree A hA ρ hρ, hfzero A hmem]
      simp
    exact ZConstruction.kConj_of_local_agree (k := k) (Ω := Ω)
      (fun g hg h hh => by
        show e (z (g * h)) = e (z g) + e (z h)
        rw [hzadd g hg h hh, map_add])
      (fun g hg h hh => by simp) hc hloc σ
      (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hσ).1, (Subgroup.mem_inf.mp hσ).2⟩)

/-- **For odd `p` the involution clause of the realisation gate is automatic**, so the gate without
the involution clause (`Work.SSGRoute.AuxRealisationNoInv`) implies the gate with it
(`Work.SSGRoute.AuxRealisationExt`).  If `c ∈ G_K` has `c ^ 2 = 1` then `c = 1`
(`Work.SSGRoute.eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot` applied to the ring automorphism
`c.toRingEquiv`, which fixes `ζ` because `c ∈ G_K` and `ζ ∈ K`), and `z 1 = 0` is the cocycle
identity. -/
theorem auxRealisationExt_of_noInv {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (hp2 : p ≠ 2)
    {M : IntermediateField k Ω} [FiniteDimensional k M] [IsGalois k M]
    (hR : AuxRealisationNoInv (p := p) K Λ M) :
    AuxRealisationExt (p := p) K Λ M := by
  classical
  haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
  haveI : CharZero Ω :=
    charZero_of_injective_algebraMap (algebraMap k Ω).injective
  intro pair hpair hprod hunr T T' hT'fin hT'disj hT'T f hfcoc hfloc hfzero horth
  obtain ⟨z, hzc, hzl, hza, hzu⟩ :=
    hR pair hpair hprod hunr T T' hT'fin hT'disj hT'T f hfcoc hfloc hfzero horth
  refine ⟨z, hzc, hzl, hza, ?_, hzu⟩
  intro c hc hc2
  have hc1 : c = 1 := by
    have hcc : c.toRingEquiv * c.toRingEquiv = 1 := by
      ext x
      have h : c (c x) = x := by
        have h2 := congrArg (fun (g : Ω ≃ₐ[k] Ω) => g x) hc2
        simpa using h2
      simpa using h
    have hfix : c.toRingEquiv ζ = ζ := by
      have h : c ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff K c).mp hc ζ hζK
      simpa using h
    have h := eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot (c.toRingEquiv) hcc
      (Fact.out : p.Prime) hp2 hζ hfix
    ext x
    have h2 := congrArg (fun (g : Ω ≃+* Ω) => g x) h
    simpa using h2
  rw [hc1]
  exact z_one (addOn_of_isCocycleOn hzc)

/-- **`AuxExists` for odd `p`, from the local Tate system and the odd-`p` realisation gate.**
Combines `Work.SSGRoute.auxExists_of_pairing_and_realisation` with
`Work.SSGRoute.auxRealisationExt_of_noInv`: for odd `p` the gate needed is the realisation *without*
the involution clause -- exactly the odd-`p` level-`K` counting identity of the `ZDataMup`/`ZSplit`
lane -- and the involution clause is discharged by the absence of elements of order two in `G_K`. -/
theorem auxExists_of_pairing_and_realisation_odd {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (hp2 : p ≠ 2)
    (hP : AuxPairingGate (p := p) K)
    (hR : ∀ (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M],
      AuxRealisationNoInv (p := p) K Λ M)
    {S : Finset (ValuationSubring Ω)} (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A) :
    AuxExists (p := p) K Λ S :=
  auxExists_of_pairing_and_realisation (p := p) hP
    (fun M _ _ => auxRealisationExt_of_noInv (p := p) hζ hζK hp2 (hR M)) hSfin

end Work.SSGRoute
