import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.exists_valuation_extension_finite
import Submission.NK.LocalReciprocityLubinTate.Unramified.isNonarchimedeanLocalField_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Unramified.Instance

/-!
# Finite subextensions of `F^{sep}` are non-archimedean local fields

Let `K` be a number field, `Q` a finite place of `K` and `F = Q.adicCompletion K` the completion.
`F` is a non-archimedean local field (`Unramified.isNonarchimedeanLocalField_adicCompletion`).
Any finite-dimensional intermediate field
`L : IntermediateField F (SeparableClosure F)` is then a non-archimedean local field as well: it is
a finite separable extension of the complete discretely valued field `F`, so the valuation of `F`
extends (uniquely) to `L` (`Eval.exists_valuation_extension_finite`), the value group of the
extension is discrete of rank one, and `L` is locally compact because it is a finite-dimensional
topological vector space over the locally compact field `F`.

The statement only asks for the *existence* of a `ValuativeRel` and a `TopologicalSpace`, so we
exhibit them: the valuative relation is the one induced by the chosen extension `w` of the `Q`-adic
valuation, and the topology is the corresponding valuation topology.

## Main result

* `NK.LocalReciprocityLubinTate.Eval.exists_isNonarchimedeanLocalField_intermediateField`
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.LocalReciprocityLubinTate.Eval

open scoped WithZero

noncomputable section

theorem exists_isNonarchimedeanLocalField_intermediateField {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L : IntermediateField (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K)))
    [FiniteDimensional (Q.adicCompletion K) L] :
    ∃ (inst : ValuativeRel ↥L) (σ : TopologicalSpace ↥L),
      letI := inst; letI := σ; IsNonarchimedeanLocalField ↥L := by
  -- An extension of the `Q`-adic valuation of the completion `F = Q.adicCompletion K` to `L`.
  obtain ⟨w, hw⟩ := exists_valuation_extension_finite (Q.adicCompletion K) ↥L
  haveI hw' : Valuation.HasExtension (ValuativeRel.valuation (Q.adicCompletion K)) w := hw
  -- The valuative relation induced by `w`, and the corresponding valuation topology.
  let instL : ValuativeRel ↥L := ValuativeRel.ofValuation w
  letI : ValuativeRel ↥L := instL
  haveI hcompat : w.Compatible := Valuation.Compatible.ofValuation w
  let σ : TopologicalSpace ↥L := (ValuativeRel.valuation ↥L).subgroups_basis.topology
  refine ⟨instL, σ, ?_⟩
  haveI htop : IsValuativeTopology ↥L := inferInstance
  haveI hAddGroup : IsTopologicalAddGroup ↥L := inferInstance
  haveI hRing : NonarchimedeanRing ↥L := inferInstance
  -- A uniformiser of `F`: an element of valuation `< 1`.
  obtain ⟨g, hg0, hg1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := Q.adicCompletion K)
  obtain ⟨π, hπ_eq⟩ := ValuativeRel.valuation_surjective (K := Q.adicCompletion K) g
  have hπ_ne : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ_eq
    exact (ne_of_gt hg0) hπ_eq.symm
  have hπ_lt : ValuativeRel.valuation (Q.adicCompletion K) π < 1 := by
    rw [hπ_eq]; exact hg1
  -- The extended valuation `w` is nontrivial, hence so is the valuative relation on `L`.
  have hw_nt : w.IsNontrivial := by
    refine ⟨algebraMap (Q.adicCompletion K) ↥L π, ?_, ?_⟩
    · intro h
      have h2 : w (algebraMap (Q.adicCompletion K) ↥L π)
          = w (algebraMap (Q.adicCompletion K) ↥L 0) := by simp [h]
      rw [Valuation.HasExtension.val_map_eq_iff
        (vR := ValuativeRel.valuation (Q.adicCompletion K)) w π 0] at h2
      rw [hπ_eq, map_zero] at h2
      exact (ne_of_gt hg0) h2
    · intro h
      rw [Valuation.HasExtension.val_map_eq_one_iff
        (vR := ValuativeRel.valuation (Q.adicCompletion K)) w π] at h
      rw [hπ_eq] at h
      exact hg1.ne h
  haveI hnt : ValuativeRel.IsNontrivial ↥L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial (R := ↥L) w).mpr hw_nt
  -- The inclusion `F → L` is continuous for the valuation topologies.
  have hcont : Continuous (algebraMap (Q.adicCompletion K) ↥L) := by
    refine continuous_of_continuousAt_zero (algebraMap (Q.adicCompletion K) ↥L) ?_
    rw [ContinuousAt, map_zero]
    refine ((IsValuativeTopology.hasBasis_nhds_zero (Q.adicCompletion K)).tendsto_iff
      (IsValuativeTopology.hasBasis_nhds_zero ↥L)).mpr ?_
    intro γ _
    obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (K := ↥L) γ.val
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, map_zero] at hy
      exact (Units.ne_zero γ) hy.symm
    have hwy : w y ≠ 0 := by
      intro h
      exact hy0 ((Valuation.zero_iff w).mp h)
    have hq : w (algebraMap (Q.adicCompletion K) ↥L π) < 1 := by
      rw [Valuation.HasExtension.val_map_lt_one_iff
        (vR := ValuativeRel.valuation (Q.adicCompletion K)) w π]
      exact hπ_lt
    obtain ⟨N, hN⟩ := exists_pow_lt₀ hq (Units.mk0 (w y) hwy)
    have hπN_ne : ValuativeRel.valuation (Q.adicCompletion K) (π ^ N) ≠ 0 := by
      intro h
      exact pow_ne_zero _ hπ_ne
        ((Valuation.zero_iff (v := ValuativeRel.valuation (Q.adicCompletion K))).mp h)
    refine ⟨Units.mk0 (ValuativeRel.valuation (Q.adicCompletion K) (π ^ N)) hπN_ne, trivial, ?_⟩
    intro x hx
    have h1 : w (algebraMap (Q.adicCompletion K) ↥L x)
        < w (algebraMap (Q.adicCompletion K) ↥L (π ^ N)) :=
      (Valuation.HasExtension.val_map_lt_iff
        (vR := ValuativeRel.valuation (Q.adicCompletion K)) w x (π ^ N)).mpr hx
    have h2 : w (algebraMap (Q.adicCompletion K) ↥L (π ^ N)) < w y := by
      rw [map_pow, map_pow]
      simpa using hN
    have h3 : (algebraMap (Q.adicCompletion K) ↥L x) <ᵥ y := by
      rw [Valuation.vlt_iff_lt (v := w)]
      exact lt_trans h1 h2
    have h4 := (Valuation.vlt_iff_lt (v := ValuativeRel.valuation ↥L)).mp h3
    rw [hy] at h4
    exact h4
  haveI hsmul : ContinuousSMul (Q.adicCompletion K) ↥L :=
    ⟨by
      rw [show (fun z : Q.adicCompletion K × ↥L ↦ z.1 • z.2)
            = fun z ↦ algebraMap (Q.adicCompletion K) ↥L z.1 * z.2 from
          funext fun z ↦ Algebra.smul_def _ _]
      exact (hcont.comp continuous_fst).mul continuous_snd⟩
  -- `L` is a finite-dimensional topological vector space over the locally compact field `F`,
  -- hence locally compact.
  letI : NontriviallyNormedField (Q.adicCompletion K) := Valued.toNontriviallyNormedField _ _
  haveI hlc : LocallyCompactSpace ↥L :=
    LocallyCompactSpace.of_finiteDimensional_of_complete (Q.adicCompletion K) ↥L
  exact IsNonarchimedeanLocalField.mk

end

end NK.LocalReciprocityLubinTate.Eval
