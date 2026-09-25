import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_pow_eq_algebraMap_of_isAlgebraic
import Submission.Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal

namespace NK.NeukirchUchida

open IsDedekindDomain

/-- **Cofinality of the value group of an algebraic extension.**
Let `K' / K` be an algebraic extension of fields and `A` a valuation subring of `K'`.  Then every
positive element of the value group of `A.valuation` dominates the `A.valuation`-value of some
nonzero element of `K`.

This is the classical fact that for an algebraic extension the value group extension is torsion:
for `y : K'` there are `n > 0` and `c : K` with `A.valuation y ^ n = A.valuation (algebraMap K K' c)`
(`Commons.RingTheory.Valuation.exists_pow_eq_algebraMap_of_isAlgebraic`); raising `c` (or `c⁻¹`)
to powers produces elements of `K` with value below (resp. above) `1`. -/
theorem exists_algebraMap_valuation_le_of_isAlgebraic {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] (A : ValuationSubring K') (halg : Algebra.IsAlgebraic K K')
    {γ : A.ValueGroup} (hγ : 0 < γ) :
    ∃ c : K, c ≠ 0 ∧ A.valuation (algebraMap K K' c) ≤ γ := by
  obtain ⟨y, hy⟩ := A.valuation_surjective γ
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero] at hy
    exact (ne_of_gt hγ) hy.symm
  obtain ⟨n, hn, c, hc0, hcn⟩ :=
    Commons.RingTheory.Valuation.exists_pow_eq_algebraMap_of_isAlgebraic (A.valuation)
      (halg.isAlgebraic y) hy0
  have hu : A.valuation (algebraMap K K' c) = γ ^ n := by rw [← hcn, hy]
  rcases le_or_gt 1 γ with hge | hlt
  · refine ⟨c⁻¹, inv_ne_zero hc0, ?_⟩
    rw [map_inv₀, Valuation.map_inv, hu]
    calc (γ ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hge)
      _ ≤ γ := hge
  · refine ⟨c, hc0, ?_⟩
    rw [hu]
    exact pow_le_of_le_one hγ.le hlt.le hn.ne'

theorem exists_ringHom_adicCompletion_placeCompletion {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    ∃ Φ : IsDedekindDomain.HeightOneSpectrum.adicCompletion K p →+*
        Valuation.Completion A.valuation,
      ∀ x : K, Φ (algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K p) x)
        = ((algebraMap K K' x : K') : Valuation.Completion A.valuation) := by
  have halg : Algebra.IsAlgebraic K K' := Algebra.IsSeparable.isAlgebraic K K'
  -- The valuation `u` on `K` induced by `A` is equivalent to the `p`-adic valuation.
  have heq : (IsDedekindDomain.HeightOneSpectrum.valuation K p).IsEquiv
      (A.valuation.comap (algebraMap K K')) := by
    rw [Valuation.isEquiv_iff_valuationSubring,
      ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring, ← hA]
    ext x
    simp only [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
      ValuationSubring.valuation_le_one_iff, Valuation.comap_apply]
  -- Uniform continuity of the two maps whose composite gives the desired extension.
  have hf : ∀ x : WithVal (A.valuation.comap (algebraMap K K')),
      WithVal.valuation A.valuation
        ((WithVal.map (A.valuation.comap (algebraMap K K')) A.valuation
          (algebraMap K K')) x)
        = WithVal.valuation (A.valuation.comap (algebraMap K K')) x := by
    intro x
    rw [WithVal.map_apply, WithVal.valuation_toVal, WithVal.valuation_apply_eq_ofVal]
    rfl
  have hc : ∀ γ : A.ValueGroup, 0 < γ →
      ∃ x : WithVal (A.valuation.comap (algebraMap K K')),
        0 < WithVal.valuation (A.valuation.comap (algebraMap K K')) x ∧
          WithVal.valuation (A.valuation.comap (algebraMap K K')) x ≤ γ := by
    intro γ hγ
    obtain ⟨c, hc0, hcle⟩ := exists_algebraMap_valuation_le_of_isAlgebraic A halg hγ
    refine ⟨WithVal.toVal _ c, ?_, ?_⟩
    · rw [WithVal.valuation_toVal]; exact (Valuation.pos_iff _).mpr hc0
    · rw [WithVal.valuation_toVal]; exact hcle
  have huc : UniformContinuous
      (WithVal.map (A.valuation.comap (algebraMap K K')) A.valuation (algebraMap K K')) :=
    Commons.Topology.Algebra.Valued.uniformContinuous_withVal_of_valuation_eq_of_cofinal _ hf hc
  have hcongr : UniformContinuous (WithVal.congr
      (IsDedekindDomain.HeightOneSpectrum.valuation K p)
      (A.valuation.comap (algebraMap K K')) (RingEquiv.refl K)) := heq.uniformContinuous_congr
  -- The induced maps of completions.
  let F : Valuation.Completion (IsDedekindDomain.HeightOneSpectrum.valuation K p) →+*
      Valuation.Completion (A.valuation.comap (algebraMap K K')) :=
    UniformSpace.Completion.mapRingHom _ hcongr.continuous
  let G : Valuation.Completion (A.valuation.comap (algebraMap K K')) →+*
      Valuation.Completion A.valuation :=
    UniformSpace.Completion.mapRingHom _ huc.continuous
  -- unfolding lemmas for the two completion maps
  have hF : ∀ y : WithVal (IsDedekindDomain.HeightOneSpectrum.valuation K p),
      F (↑y) = ↑((WithVal.congr (IsDedekindDomain.HeightOneSpectrum.valuation K p)
        (A.valuation.comap (algebraMap K K')) (RingEquiv.refl K)) y) := by
    intro y
    rw [show F = UniformSpace.Completion.mapRingHom
      (WithVal.congr (IsDedekindDomain.HeightOneSpectrum.valuation K p)
        (A.valuation.comap (algebraMap K K')) (RingEquiv.refl K)) hcongr.continuous from rfl]
    exact UniformSpace.Completion.mapRingHom_coe _ y
  have hG : ∀ z : WithVal (A.valuation.comap (algebraMap K K')),
      G (↑z) = ↑((WithVal.map (A.valuation.comap (algebraMap K K')) A.valuation
        (algebraMap K K')) z) := by
    intro z
    rw [show G = UniformSpace.Completion.mapRingHom
      (WithVal.map (A.valuation.comap (algebraMap K K')) A.valuation (algebraMap K K'))
        huc.continuous from rfl]
    exact UniformSpace.Completion.mapRingHom_coe _ z
  refine ⟨G.comp (F.comp (HeightOneSpectrum.adicCompletion.equiv K p).toRingHom), ?_⟩
  intro x
  have hx1 : algebraMap K (HeightOneSpectrum.adicCompletion K p) x
      = (x : HeightOneSpectrum.adicCompletion K p) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  change G (F ((HeightOneSpectrum.adicCompletion.equiv K p).toRingHom
      (x : HeightOneSpectrum.adicCompletion K p)))
    = ((algebraMap K K' x : K') : Valuation.Completion A.valuation)
  have hcoe : (HeightOneSpectrum.adicCompletion.equiv K p).toRingHom
        (x : HeightOneSpectrum.adicCompletion K p)
      = ↑((WithVal.equiv (IsDedekindDomain.HeightOneSpectrum.valuation K p)).symm x) := by
    rw [show (HeightOneSpectrum.adicCompletion.equiv K p).toRingHom
        (x : HeightOneSpectrum.adicCompletion K p)
        = (HeightOneSpectrum.adicCompletion.equiv K p)
          (x : HeightOneSpectrum.adicCompletion K p) from rfl]
    rw [HeightOneSpectrum.adicCompletion.equiv_apply,
      HeightOneSpectrum.adicCompletion.coe_toCompletion, WithVal.equiv_symm_apply]
  rw [hcoe, hF, hG, WithVal.congr_apply, WithVal.map_apply, WithVal.equiv_symm_apply]
  rfl

end NK.NeukirchUchida
