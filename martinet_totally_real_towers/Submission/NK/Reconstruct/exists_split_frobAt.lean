import Mathlib
import Submission.NK.Reconstruct.splitFrobeniusBase
import Submission.NK.Reconstruct.frobElementAt
import Submission.NK.Chebotarev.FrobeniusOne
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHomType


namespace NK.Reconstruct

open scoped NumberField

/-- **Čebotarev with a prime completely split over `ℚ`.**  For `Ω/ℚ` a Galois extension of `ℚ`,
`L ⊆ Ω` a finite Galois number-field level, `N/L` a finite Galois number-field level inside `Ω`,
and `τ ∈ Gal(N/L)`, there is a prime `𝔭` of `L` which is **completely split over `ℚ`**
(`𝔭.asIdeal.inertiaDeg (𝓞 ℚ) = 1` and `𝔭.asIdeal.ramificationIdx (𝓞 ℚ) = 1`) and a prime `P` of
`𝓞 N` above `𝔭` at which `τ` is an arithmetic Frobenius element.

Plan: take the Galois closure `Ñ` of `N` over `ℚ` inside `Ω` (it exists and is finite, since `Ω/ℚ`
is Galois); `Ñ/ℚ` and `Ñ/L` are Galois, `N ⊆ Ñ` and `Gal(Ñ/L) → Gal(N/L)` is onto, so `τ` lifts to
`τ̃ ∈ Gal(Ñ/L) ⊆ Gal(Ñ/ℚ)`.  Apply `hc : ChebotarevInput ℚ Ω` at the level `Ñ/ℚ` to `τ̃`: this gives
a rational prime `p₀` and `P̃ | p₀` unramified at which `τ̃` is a Frobenius.  Since `τ̃` fixes `L`,
restricting (`NK.Chebotarev.IsFrobAtRestrictNormalHom`) gives `IsFrobAt (base ℚ) (P̃ ∩ L) 1`, so
with `p₀` unramified one gets `(P̃∩L).inertiaDeg (𝓞 ℚ) = 1` by
`NK.Chebotarev.IsFrobAt_eq_one_iff_inertiaDeg_eq_one`; the ramification index over `ℚ` is `1` by
`Ideal.ramificationIdx_tower`.  The base change `ℚ → L`
(`NK.Reconstruct.isFrobAt_of_isFrobAt_restrictScalars`) then converts `IsFrobAt (base ℚ) P̃ τ̃`
into `IsFrobAt (base L) P̃ τ̃`, and restricting to `N` (again
`NK.Chebotarev.IsFrobAtRestrictNormalHom`) gives the conclusion with `𝔭 := P̃ ∩ L` and
`P := P̃ ∩ N`. -/
theorem exists_split_frobAt {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    (hc : NK.Reconstruct.ChebotarevInput ℚ Ω) (L : NK.Reconstruct.FrobLevel ℚ Ω)
    (N : IntermediateField ↥L.L Ω) [FiniteDimensional ↥L.L N] [Normal ↥L.L N] [NumberField ↥N]
    (τ : Gal(↥N/↥L.L)) :
    ∃ (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L) (P : NK.Chebotarev.PrimeIdeal ↥N),
      P.asIdeal.LiesOver 𝔭.asIdeal ∧ NK.Reconstruct.SplitsCompletelyOverRat 𝔭 ∧
      NK.Chebotarev.IsFrobAt (K := ↥L.L) (L := ↥N) P τ := by
  classical
  -- ## Instances for the base fields
  haveI hNorLL : Normal ℚ ↥L.L := by
    have h := L.normal
    rwa [show (L.L.algebra' : Algebra ℚ ↥L.L) = (inferInstance : Algebra ℚ ↥L.L)
      from Subsingleton.elim _ _] at h
  haveI hGalLL : IsGalois ℚ ↥L.L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hNafin : FiniteDimensional ℚ ↥N := FiniteDimensional.trans ℚ ↥L.L ↥N
  -- ## The ℚ-Galois closure `M` of `N`
  let M : IntermediateField ℚ Ω := IntermediateField.normalClosure ℚ ↥N Ω
  letI : Algebra ℚ ↥M := IntermediateField.algebra' (K := ℚ) (L := Ω) M
  have hNM : (N : Set Ω) ⊆ (M : Set Ω) := by
    intro x hx
    exact AlgHom.fieldRange_le_normalClosure (IsScalarTower.toAlgHom ℚ ↥N Ω)
      (AlgHom.mem_fieldRange.mpr ⟨⟨x, hx⟩, by simp [IsScalarTower.toAlgHom]⟩)
  have hLM : L.L ≤ M := by
    intro x hx
    refine hNM ?_
    simpa using N.algebraMap_mem (⟨x, hx⟩ : ↥L.L)
  have hMfin : FiniteDimensional ℚ ↥M := normalClosure.is_finiteDimensional ℚ ↥N Ω
  haveI := hMfin
  have hMgal : IsGalois ℚ ↥M := IsGalois.normalClosure ℚ ↥N Ω
  haveI hMnorm : Normal ℚ ↥M := hMgal.to_normal
  haveI hMnf : NumberField ↥M :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField M
  -- ## The algebra structures of the tower `ℚ ⊆ L ⊆ N ⊆ M ⊆ Ω`
  letI : Algebra ↥L.L ↥M := (Subsemiring.inclusion hLM).toAlgebra
  letI : Algebra ↥N ↥M := (Subsemiring.inclusion hNM).toAlgebra
  haveI htow1 : @IsScalarTower ℚ ↥L.L ↥M ((inferInstance : Algebra ℚ ↥L.L).toSMul)
      ((inferInstance : Algebra ↥L.L ↥M).toSMul) ((inferInstance : Algebra ℚ ↥M).toSMul) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI htow2 : IsScalarTower ↥L.L ↥N ↥M := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI htow3 : IsScalarTower ↥L.L ↥M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI htow4 : IsScalarTower ↥N ↥M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI hNormLM : Normal ↥L.L ↥M := Normal.tower_top_of_normal ℚ ↥L.L ↥M
  haveI hNormLΩ : Normal ↥L.L Ω := inferInstance
  haveI hscalLΩ : IsScalarTower ℚ ↥L.L Ω := inferInstance
  haveI hfinLM : FiniteDimensional ↥L.L ↥M :=
    Module.Finite.of_restrictScalars_finite ℚ ↥L.L ↥M
  haveI hGalLM : IsGalois ↥L.L ↥M :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- ## The lift `ρ` of `τ` to `Gal(Ω/L)`
  obtain ⟨ρ, hρ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥L.L) (K₁ := ↥N) (E := Ω) τ
  let σ : Gal(Ω/ℚ) := ρ.restrictScalars ℚ
  let τtilde : Gal(↥M/ℚ) := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) M σ
  -- ## Čebotarev at the level `M/ℚ`
  obtain ⟨p₀, Ptilde, hPtilde, hPtildeunr, hPtildefrob⟩ := hc M τtilde
  -- ## `τtilde` fixes `L` pointwise, hence acts trivially on `𝓞 L`
  have hfix : ∀ y : ↥L.L, τtilde (algebraMap ↥L.L ↥M y) = algebraMap ↥L.L ↥M y := by
    intro y
    refine (algebraMap ↥M Ω).injective ?_
    rw [show τtilde = σ.restrictNormal ↥M from rfl, AlgEquiv.restrictNormal_commutes]
    rw [AlgEquiv.restrictScalars_apply, ← IsScalarTower.algebraMap_apply ↥L.L ↥M Ω]
    exact ρ.commutes y
  have hfixO : ∀ x : 𝓞 ↥L.L,
      ((galRestrict (𝓞 ℚ) ℚ ↥M (𝓞 ↥M) τtilde : 𝓞 ↥M ≃ₐ[𝓞 ℚ] 𝓞 ↥M))
        (algebraMap (𝓞 ↥L.L) (𝓞 ↥M) x) = algebraMap (𝓞 ↥L.L) (𝓞 ↥M) x := by
    intro x
    refine IsFractionRing.injective (𝓞 ↥M) ↥M ?_
    rw [algebraMap_galRestrict_apply]
    rw [← IsScalarTower.algebraMap_apply (𝓞 ↥L.L) (𝓞 ↥M) ↥M]
    rw [IsScalarTower.algebraMap_apply (𝓞 ↥L.L) ↥L.L ↥M]
    rw [hfix (algebraMap (𝓞 ↥L.L) ↥L.L x)]
  -- ## The Frobenius at the split prime is trivial
  have hfrobLL : NK.Chebotarev.IsFrobAt (K := ℚ) (L := ↥L.L)
      (Ptilde.under (𝓞 ↥L.L)) 1 := by
    rw [NK.Chebotarev.isFrobAt_def]
    intro x
    have hx : Nat.card (𝓞 ℚ ⧸ (Ptilde.under (𝓞 ↥L.L)).asIdeal.under (𝓞 ℚ))
        = Nat.card (𝓞 ℚ ⧸ Ptilde.asIdeal.under (𝓞 ℚ)) := by
      rw [show (Ptilde.under (𝓞 ↥L.L)).asIdeal = Ideal.under (𝓞 ↥L.L) Ptilde.asIdeal from rfl,
        Ideal.under_under]
    rw [hx, show (Ptilde.under (𝓞 ↥L.L)).asIdeal = Ideal.under (𝓞 ↥L.L) Ptilde.asIdeal from rfl,
      Ideal.mem_under, map_sub, map_pow]
    have hg : galRestrict (𝓞 ℚ) ℚ ↥L.L (𝓞 ↥L.L) (1 : Gal(↥L.L/ℚ)) x = x := by
      rw [map_one]
      rfl
    rw [hg]
    nth_rewrite 1 [← hfixO x]
    exact hPtildefrob (algebraMap (𝓞 ↥L.L) (𝓞 ↥M) x)
  -- ## The prime `𝔭 = P̃ ∩ 𝓞 L` is completely split over `ℚ`
  have h𝔭lies : (Ptilde.under (𝓞 ↥L.L)).asIdeal.LiesOver p₀.asIdeal := by
    refine ⟨?_⟩
    rw [show (Ptilde.under (𝓞 ↥L.L)).asIdeal = Ideal.under (𝓞 ↥L.L) Ptilde.asIdeal from rfl,
      Ideal.under_under]
    exact hPtilde.over
  have h𝔭unr : (Ptilde.under (𝓞 ↥L.L)).asIdeal.ramificationIdx (𝓞 ℚ) = 1 := by
    have h1 : Ptilde.asIdeal.ramificationIdx (𝓞 ℚ)
        = (Ideal.under (𝓞 ↥L.L) Ptilde.asIdeal).ramificationIdx (𝓞 ℚ)
          * Ptilde.asIdeal.ramificationIdx (𝓞 ↥L.L) :=
      Ideal.ramificationIdx_tower (q := Ideal.under (𝓞 ↥L.L) Ptilde.asIdeal) (r := Ptilde.asIdeal)
    rw [hPtildeunr] at h1
    rw [show (Ptilde.under (𝓞 ↥L.L)).asIdeal = Ideal.under (𝓞 ↥L.L) Ptilde.asIdeal from rfl]
    exact (mul_eq_one.mp h1.symm).1
  have hinertia : (Ptilde.under (𝓞 ↥L.L)).asIdeal.inertiaDeg (𝓞 ℚ) = 1 :=
    (NK.Chebotarev.IsFrobAt_eq_one_iff_inertiaDeg_eq_one (K := ℚ) (L := ↥L.L)
      (P := Ptilde.under (𝓞 ↥L.L)) h𝔭lies h𝔭unr).mp hfrobLL
  -- ## Base change `ℚ → L` at the level `M`, then descent to `N`
  let ρM : Gal(↥M/↥L.L) := AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) ↥M ρ
  have hρM : ρM.restrictScalars ℚ = τtilde := by
    refine AlgEquiv.ext fun y => ?_
    refine (algebraMap ↥M Ω).injective ?_
    change (algebraMap ↥M Ω) (ρM y) = (algebraMap ↥M Ω) (τtilde y)
    rw [show ρM = ρ.restrictNormal ↥M from rfl, AlgEquiv.restrictNormal_commutes]
    rw [show τtilde = σ.restrictNormal ↥M from rfl, AlgEquiv.restrictNormal_commutes]
    rw [AlgEquiv.restrictScalars_apply]
  have hfrobM : NK.Chebotarev.IsFrobAt (K := ↥L.L) (L := ↥M) Ptilde ρM :=
    NK.Reconstruct.isFrobAt_of_isFrobAt_restrictScalars (K := ℚ) (L := ↥L.L) (M := ↥M)
      Ptilde ρM hinertia (by rw [hρM]; exact hPtildefrob)
  have hfinal : NK.Chebotarev.IsFrobAt (K := ↥L.L) (L := ↥N)
      (Ptilde.under (𝓞 ↥N)) (AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := ↥M) ↥N ρM) :=
    NK.Chebotarev.IsFrobAtRestrictNormalHomType (K := ↥L.L) (E := ↥N) (M := ↥M)
      Ptilde ρM hfrobM
  have hresN : AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := ↥M) ↥N ρM = τ := by
    rw [show ρM = AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) ↥M ρ from rfl]
    exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (K₁ := ↥N) (K₂ := ↥M)
      (F := ↥L.L) (K₃ := Ω) ρ).symm.trans hρ
  -- ## Conclusion
  refine ⟨Ptilde.under (𝓞 ↥L.L), Ptilde.under (𝓞 ↥N), ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    rw [show (Ptilde.under (𝓞 ↥L.L)).asIdeal = Ideal.under (𝓞 ↥L.L) Ptilde.asIdeal from rfl,
      show (Ptilde.under (𝓞 ↥N)).asIdeal = Ideal.under (𝓞 ↥N) Ptilde.asIdeal from rfl,
      Ideal.under_under]
  · exact ⟨hinertia, h𝔭unr⟩
  · rw [← hresN]
    exact hfinal


end NK.Reconstruct
