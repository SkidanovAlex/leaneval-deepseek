import Submission.Work.SSGRoute.sha2_hasse.Gateway
import Submission.Work.SSGRoute.sha2_hasse.exists_section_of_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField Pointwise

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.SSGRoute.sha2_hasse

variable {k : Type} [Field k] [NumberField k]

/-- **A finite Galois level carrying a locally constant cocycle witness.**  For a cochain `b`
which is locally constant on `D_A` (`A` a place of `k̄` above the finite place `p` of `k`), there
is a finite Galois level `E ⊇ L` containing all the values of `b` on `D_A` and on which the local
constancy of `b` is visible (i.e. right-invariance under `D_A ∩ Gal(k̄/E)`). -/
theorem exists_level_values_and_invariance
    (L : FiniteGaloisIntermediateField k (AlgebraicClosure k))
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring (AlgebraicClosure k))
    (hA : A.comap (algebraMap k (AlgebraicClosure k)) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k p)
    (b : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → Additive (AlgebraicClosure k)ˣ)
    (hb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) :
    ∃ E : FiniteGaloisIntermediateField k (AlgebraicClosure k),
      (L : IntermediateField k (AlgebraicClosure k)) ≤
        (E : IntermediateField k (AlgebraicClosure k)) ∧
      (∀ g ∈ SSGRoute.decomp k A,
        ((Additive.toMul (b g) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) ∈
          (E : IntermediateField k (AlgebraicClosure k))) ∧
      (∀ g ∈ SSGRoute.decomp k A,
        ∀ u ∈ (E : IntermediateField k (AlgebraicClosure k)).fixingSubgroup,
          u ∈ SSGRoute.decomp k A → b (g * u) = b g) := by
  classical
  obtain ⟨U, hUopen, hUconst⟩ := hb
  -- a finite normal level `M` on which the local constancy of `b` is visible and which contains `L`
  have hopen : IsOpen (((U ⊓ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup :
      Subgroup (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) :
        Set (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k))) := by
    have h := hUopen.inter (IntermediateField.fixingSubgroup_isOpen
      (L : IntermediateField k (AlgebraicClosure k)))
    rw [Subgroup.coe_inf]
    exact h
  obtain ⟨M, hMfin, hMnorm, hMle⟩ := Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le
    (U ⊓ (L : IntermediateField k (AlgebraicClosure k)).fixingSubgroup) hopen
  haveI : FiniteDimensional k M := hMfin
  haveI : Normal k M := hMnorm
  haveI hMgal : IsGalois k M := isGalois_iff.mpr ⟨inferInstance, hMnorm⟩
  have hLM : (L : IntermediateField k (AlgebraicClosure k)) ≤ M := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (k := k) (K := AlgebraicClosure k) M]
    exact (IntermediateField.le_iff_le M.fixingSubgroup
      (L : IntermediateField k (AlgebraicClosure k))).mpr (le_inf_iff.mp hMle).2
  let Mfg : FiniteGaloisIntermediateField k (AlgebraicClosure k) :=
    { toIntermediateField := M, finiteDimensional := hMfin, isGalois := hMgal }
  haveI : Fintype (Lf Mfg ≃ₐ[k] Lf Mfg) := AlgEquiv.fintype k (Lf Mfg)
  -- a section of `D_A → Stab(q_M)` over the level `M`
  obtain ⟨σ, hσmem, hσres⟩ := exists_section_of_decomp (k := k) p A hA Mfg
  let s : Set (AlgebraicClosure k) :=
    Set.range fun γ : ↥(MulAction.stabilizer (Lf Mfg ≃ₐ[k] Lf Mfg)
      (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.Local.placeOf p A hA
        (Mfg : IntermediateField k (AlgebraicClosure k))))) =>
      ((Additive.toMul (b (σ γ)) : (AlgebraicClosure k)ˣ) : AlgebraicClosure k)
  haveI : Finite s := Set.finite_range _
  -- the level `E = M ⊔` (Galois closure of the values of `b`)
  have hfixM : (Mfg : IntermediateField k (AlgebraicClosure k)) ≤
      ((Mfg ⊔ FiniteGaloisIntermediateField.adjoin k s : FiniteGaloisIntermediateField k
        (AlgebraicClosure k)) : IntermediateField k (AlgebraicClosure k)) :=
    (FiniteGaloisIntermediateField.le_iff _ _).mp le_sup_left
  refine ⟨Mfg ⊔ FiniteGaloisIntermediateField.adjoin k s, le_trans hLM le_sup_left, ?_, ?_⟩
  · intro g hg
    have hγmem : levelRes Mfg g ∈ MulAction.stabilizer (Lf Mfg ≃ₐ[k] Lf Mfg)
        (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.Local.placeOf p A hA
          (Mfg : IntermediateField k (AlgebraicClosure k)))) := by
      rw [stabilizer_ofFinite_eq_decompositionSubgroup]
      exact Submission.NeukirchUchida.Local.restrictNormalHom_mem_decompositionSubgroup_of_mem_stabilizer
        A (Mfg : IntermediateField k (AlgebraicClosure k))
        (Submission.NeukirchUchida.Local.placeOf p A hA (Mfg : IntermediateField k (AlgebraicClosure k)))
        (Submission.NeukirchUchida.Local.comap_eq_valuationSubringAtPrime_placeOf p A hA
          (Mfg : IntermediateField k (AlgebraicClosure k))) g hg
    let γ : ↥(MulAction.stabilizer (Lf Mfg ≃ₐ[k] Lf Mfg)
        (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.Local.placeOf p A hA
          (Mfg : IntermediateField k (AlgebraicClosure k))))) := ⟨levelRes Mfg g, hγmem⟩
    have hσγ : levelRes Mfg (σ γ) = levelRes Mfg g := hσres γ
    have hu : (σ γ)⁻¹ * g ∈ (Mfg : IntermediateField k (AlgebraicClosure k)).fixingSubgroup := by
      rw [← mem_ker_levelRes_iff Mfg ((σ γ)⁻¹ * g), map_mul, map_inv, hσγ]
      exact inv_mul_cancel _
    have huD : (σ γ)⁻¹ * g ∈ SSGRoute.decomp k A :=
      (SSGRoute.decomp k A).mul_mem ((SSGRoute.decomp k A).inv_mem (hσmem γ)) hg
    have huU : (σ γ)⁻¹ * g ∈ U := (le_inf_iff.mp hMle).1 hu
    have hgb : b g = b (σ γ) := by
      have h1 := hUconst (σ γ) (hσmem γ) ((σ γ)⁻¹ * g) huU huD
      rwa [mul_inv_cancel_left] at h1
    rw [hgb]
    exact (FiniteGaloisIntermediateField.le_iff (FiniteGaloisIntermediateField.adjoin k s)
      (Mfg ⊔ FiniteGaloisIntermediateField.adjoin k s)).mp le_sup_right
      (FiniteGaloisIntermediateField.subset_adjoin k s ⟨γ, rfl⟩)
  · intro g hg u hu huD
    exact hUconst g hg u ((le_inf_iff.mp hMle).1
      (IntermediateField.fixingSubgroup_antitone hfixM hu)) huD

end Work.SSGRoute.sha2_hasse
