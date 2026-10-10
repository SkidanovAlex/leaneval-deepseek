import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
import Submission.Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
import Submission.NeukirchUchida.Local.PlaceFromValuation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

open scoped Pointwise

/-- Suggested imports (beyond `Mathlib`):
* `Submission.NeukirchUchida.Local.PlaceFromValuation` — `placeOf p B hB N`, `placeOf_liesOver`,
  `comap_eq_valuationSubringAtPrime_placeOf`, and
  `mem_stabilizer_iff_forall_mem_decompositionSubgroup`.
* `Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one`.
* `Submission.Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely`.
* `Submission.Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois`. -/
theorem stabilizer_le_fixingSubgroup_iff_splitCompletely {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K']
    {N : IntermediateField K K'} [FiniteDimensional K N] [Normal K N] [NumberField ↥N]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (B : ValuationSubring K') (hB : B.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    MulAction.stabilizer Gal(K'/K) B ≤ N.fixingSubgroup ↔
      (p.asIdeal.primesOver (NumberField.RingOfIntegers ↥N)).ncard = Module.finrank K ↥N := by
  classical
  -- The place `w` of `N` cut out by the place `B` of `K'`.
  set w := Submission.NeukirchUchida.Local.placeOf p B hB N with hw_def
  have hwcomap : B.comap (algebraMap ↥N K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥N w :=
    Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf p B hB N
  have hwlies : w.asIdeal.LiesOver p.asIdeal :=
    Submission.NeukirchUchida.Local.placeOf_liesOver p B hB N
  -- The stabiliser of `B` is contained in the fixing subgroup of `N` exactly when the
  -- decomposition group of the induced place `w` of `N` is trivial.
  have key : MulAction.stabilizer Gal(K'/K) B ≤ N.fixingSubgroup ↔
      Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) w = ⊥ := by
    constructor
    · intro h
      rw [Subgroup.eq_bot_iff_forall]
      intro τ hτ
      -- Every element of the decomposition group of `w` is the restriction of an element of
      -- the stabiliser of `B` (surjectivity of restriction on decomposition groups).
      have hτ1 : τ ∈ MulAction.stabilizer Gal(↥N/K)
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥N w) :=
        (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
          w τ).mpr hτ
      have hτ2 : τ ∈ MulAction.stabilizer Gal(↥N/K) (B.comap (algebraMap ↥N K')) := by
        rw [hwcomap]; exact hτ1
      obtain ⟨σ, hσ, hστ⟩ :=
        Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
          B (Submission.NeukirchUchida.Local.comap_ne_top_of_eq p B hB) N τ hτ2
      have hfix : σ ∈ N.fixingSubgroup := h hσ
      have hker : σ ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') N).ker := by
        rw [IntermediateField.restrictNormalHom_ker (K := K) N]
        exact hfix
      have h1 : (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') N) σ = 1 :=
        MonoidHom.mem_ker.mp hker
      rw [← hστ]; exact h1
    · intro h σ hσ
      -- Conversely the restriction of an element of the stabiliser lies in the decomposition
      -- group of `w`, which is trivial by hypothesis.
      have hσD : (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') N) σ ∈
          Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) w :=
        Submission.NeukirchUchida.Local.restrictNormalHom_mem_decompositionSubgroup_of_mem_stabilizer
          B N w hwcomap σ hσ
      rw [h] at hσD
      rw [Subgroup.mem_bot] at hσD
      rw [← IntermediateField.restrictNormalHom_ker (K := K) N]
      exact MonoidHom.mem_ker.mpr hσD
  rw [key]
  -- The two decomposition subgroups (local and commons) are the same subgroup.
  have hdeq : Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) w =
      Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) w := rfl
  rw [hdeq,
    Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
      p w hwlies]
  -- Finally `w` is trivial iff `e = f = 1` iff `p` splits completely in `N`.
  exact (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
    (K := K) (L := ↥N) p).symm

end NK.Reconstruct
