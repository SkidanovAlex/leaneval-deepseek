import Mathlib.Data.Int.ConditionallyCompleteOrder
import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
import Submission.Commons.RingTheory.Valuation.exists_ringHom_completion_of_valuationSubring_eq
import Submission.Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField WithZero

namespace Commons.NumberTheory.NumberField

open IsDedekindDomain

/-- **Transport of the adic completion along an isomorphism of number fields.**

For an isomorphism `e : K ≃ₐ[ℚ] K₀` of number fields and a finite place `Q` of `K`, there is a
place `Q₀` of `K₀` and a ring isomorphism of the completions which is compatible with `e`, i.e.
carries `algebraMap K (Q.adicCompletion K) x` to `algebraMap K₀ (Q₀.adicCompletion K₀) (e x)`.

(Equivalently one may take `Q₀ = heightOneSpectrumMap e Q`; the proof route is the "dense image"
argument: the ring hom `K → Q₀.adicCompletion K₀`, `x ↦ algebraMap K₀ _ (e x)`, is continuous for
the `Q`-adic topology because it preserves the valuation, hence extends to the completion
`UniformSpace.Completion.extensionHom`; the same in the other direction, compared on the dense
image, gives the equivalence.) -/
theorem completion_ringEquiv_of_algEquiv {K K₀ : Type*} [Field K] [NumberField K] [Field K₀]
    [NumberField K₀] (e : K ≃ₐ[ℚ] K₀)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (Q₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₀))
      (Φ : Q.adicCompletion K ≃+* Q₀.adicCompletion K₀),
      ∀ x : K, Φ (algebraMap K (Q.adicCompletion K) x)
        = algebraMap K₀ (Q₀.adicCompletion K₀) (e x) := by
  -- The transported valuation on `K₀`.
  let w : Valuation K₀ ℤᵐ⁰ := (Q.valuation K).comap e.symm.toRingHom
  have hwe : ∀ y : K, w (e y) = Q.valuation K y := by
    intro y
    simp only [w, Valuation.comap_apply]
    exact congrArg (Q.valuation K) (e.symm_apply_apply y)
  have hwe' : ∀ y : K₀, w y = Q.valuation K (e.symm y) := by
    intro y
    simp only [w, Valuation.comap_apply]
    rfl
  -- `𝓞 K₀` is contained in the valuation subring of `w`.
  have hle : ∀ x : 𝓞 K₀, algebraMap (𝓞 K₀) K₀ x ∈ w.valuationSubring := by
    intro x
    rw [Valuation.mem_valuationSubring_iff]
    have hx : e.symm ((x : 𝓞 K₀) : K₀)
        = ((NumberField.RingOfIntegers.mapRingEquiv e.symm.toRingEquiv x : 𝓞 K) : K) :=
      NumberField.RingOfIntegers.mapRingEquiv_apply e.symm.toRingEquiv x
    rw [hwe', hx]
    exact Q.valuation_le_one _
  -- `w` is nontrivial
  have hw_nt : w.IsNontrivial := by
    obtain ⟨y, hy0, hy⟩ :=
      (Valuation.isNontrivial_iff_exists_lt_one (Q.valuation K)).mp inferInstance
    refine (Valuation.isNontrivial_iff_exists_lt_one w).mpr ⟨e y, ?_, ?_⟩
    · simpa using hy0
    · rw [hwe y]; exact hy
  have hA : w.valuationSubring ≠ ⊤ := by
    intro h
    exact (Valuation.valuationSubring_eq_top_iff w).mp h hw_nt
  obtain ⟨Q₀, hQ₀⟩ :=
    Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
      w.valuationSubring hA hle
  -- surjectivity of `w`
  have hw_surj : Function.Surjective w := by
    intro γ
    obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective K Q γ
    exact ⟨e y, by rw [hwe y]; exact hy⟩
  -- The map `K → K₀` is an isometry for the two valuations.
  let F1 : WithVal (Q.valuation K) ≃+* WithVal w :=
    WithVal.congr (Q.valuation K) w (e : K ≃+* K₀)
  have hF1a : ∀ x : WithVal (Q.valuation K),
      WithVal.valuation w (F1 x) = WithVal.valuation (Q.valuation K) x := by
    intro x
    simp only [F1, WithVal.congr_apply, WithVal.valuation_apply_eq_ofVal]
    exact hwe x.ofVal
  have hF1 : UniformContinuous (F1 : WithVal (Q.valuation K) → WithVal w) := by
    refine Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
      F1.toRingHom hF1a ?_
    intro γ hγ
    obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective K Q γ
    exact ⟨WithVal.toVal (Q.valuation K) y,
      by rw [WithVal.valuation_apply_eq_ofVal, hy]; exact hγ,
      by rw [WithVal.valuation_apply_eq_ofVal, hy]⟩
  have hF1b : ∀ x : WithVal w,
      WithVal.valuation (Q.valuation K) (F1.symm x) = WithVal.valuation w x := by
    intro x
    simp only [F1, WithVal.congr_symm, WithVal.congr_apply, WithVal.valuation_apply_eq_ofVal,
      AlgEquiv.toRingEquiv_symm]
    rw [hwe']
    rfl
  have hF1' : UniformContinuous (F1.symm : WithVal w → WithVal (Q.valuation K)) := by
    refine Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal
      F1.symm.toRingHom hF1b ?_
    intro γ hγ
    obtain ⟨y, hy⟩ := hw_surj γ
    exact ⟨WithVal.toVal w y,
      by rw [WithVal.valuation_apply_eq_ofVal, hy]; exact hγ,
      by rw [WithVal.valuation_apply_eq_ofVal, hy]⟩
  -- The isometry of completions `K_Q → K₀_w`.
  let Ψ1 : (Q.valuation K).Completion ≃+* w.Completion :=
    UniformSpace.Completion.mapRingEquiv F1 hF1.continuous hF1'.continuous
  -- The canonical isomorphism `K₀_w ≃ K₀_{Q₀}`, since `w` and `Q₀.valuation K₀` define
  -- the same valuation subring.
  obtain ⟨φ2, hφ2bij, hφ2coe⟩ :=
    Commons.RingTheory.Valuation.exists_ringHom_completion_of_valuationSubring_eq w
      (Q₀.valuation K₀)
      (by rw [hQ₀,
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring])
  let Ψ2 : w.Completion ≃+* (Q₀.valuation K₀).Completion :=
    RingEquiv.ofBijective φ2 hφ2bij
  refine ⟨Q₀, (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K Q).trans
    ((Ψ1.trans Ψ2).trans
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K₀ Q₀).symm), ?_⟩
  intro x
  have hcoe : algebraMap K (Q.adicCompletion K) x = (x : Q.adicCompletion K) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp
  have hcoe₀ : algebraMap K₀ (Q₀.adicCompletion K₀) (e x)
      = ((e x) : Q₀.adicCompletion K₀) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp
  rw [hcoe, hcoe₀]
  have hF1app : ∀ y : K, F1 (WithVal.toVal (Q.valuation K) y) = WithVal.toVal w (e y) := by
    intro y
    simp only [F1, WithVal.congr_apply]
    rfl
  have hΨ1 : ∀ y : K,
      Ψ1 (y : (Q.valuation K).Completion) = (e y : w.Completion) := by
    intro y
    change UniformSpace.Completion.mapRingEquiv F1 hF1.continuous hF1'.continuous
      (y : (Q.valuation K).Completion) = (e y : w.Completion)
    rw [UniformSpace.Completion.mapRingEquiv_apply, UniformSpace.Completion.map_coe hF1]
    try rw [WithVal.equiv_symm_apply]
    rw [hF1app y]
    try rfl
  have hΨ2 : ∀ y : K₀, Ψ2 (y : w.Completion) = (y : (Q₀.valuation K₀).Completion) := by
    intro y
    change RingEquiv.ofBijective φ2 hφ2bij (y : w.Completion) = _
    rw [RingEquiv.ofBijective_apply]
    exact hφ2coe y
  have hkey : (Ψ1.trans Ψ2) (x : (Q.valuation K).Completion)
      = ((e x : K₀) : (Q₀.valuation K₀).Completion) := by
    rw [RingEquiv.trans_apply, hΨ1 x, hΨ2 (e x)]
  show ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K₀ Q₀).symm
      ((Ψ1.trans Ψ2) ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K Q)
        (x : Q.adicCompletion K)))) = ((e x : K₀) : Q₀.adicCompletion K₀)
  rw [show (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv K Q) (x : Q.adicCompletion K)
      = (x : (Q.valuation K).Completion) from rfl]
  rw [hkey]
  rfl

end Commons.NumberTheory.NumberField