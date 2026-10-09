import Mathlib
import Submission.Work.SSGRoute.isInertiaAt_smul_iff
import Submission.Work.SSGRoute.TPatom.inertia_le_fixingSubgroup_of_ramificationIdx_eq_one
import Submission.Work.SSGRoute.TPatom.ramificationIdx_eq_one_normalClosure
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGate

open scoped NumberField Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

theorem inertia_eq_bot_of_concentrated_level {k K L : Type} [Field k] [NumberField k]
    [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L] [IsGalois K L]
    (l : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (K1 : IntermediateField k L) [NumberField ↥K1] [FiniteDimensional k ↥K1] [IsGalois k ↥K1]
    (E : IntermediateField ↥K1 L) [FiniteDimensional ↥K1 ↥E] [IsGalois ↥K1 ↥E]
    (hgen : (⊤ : IntermediateField k L) ≤ (IsScalarTower.toAlgHom k K L).fieldRange ⊔ K1 ⊔
      ⨆ τ : (L ≃ₐ[k] L), (E.restrictScalars k).map (τ : L →ₐ[k] L))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : q'.asIdeal.LiesOver q.asIdeal)
    (hq'l : q'.asIdeal.LiesOver l.asIdeal)
    (hK1unr : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1),
      𝔭.asIdeal.LiesOver l.asIdeal →
        𝔭.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1)
    (hEunr : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1),
      𝔭.asIdeal.LiesOver l.asIdeal →
        ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E),
          𝔮.asIdeal.LiesOver 𝔭.asIdeal →
            𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥K1) = 1) :
    Ideal.inertia (L ≃ₐ[K] L) q'.asIdeal = ⊥ := by
  classical
  -- `E` regarded as an intermediate field of `L` over `k`, and its normal closure `F`.
  let E' : IntermediateField k L := E.restrictScalars k
  let Kf : IntermediateField k L := (IsScalarTower.toAlgHom k K L).fieldRange
  let F' : IntermediateField k L := IntermediateField.normalClosure k E' L
  -- `K₁ ≤ E`
  have hK1E' : (K1 : IntermediateField k L) ≤ E' := by
    intro x hx
    show x ∈ (E : Set L)
    simpa using E.algebraMap_mem (⟨x, hx⟩ : ↥K1)
  -- ### Step 1: every prime of `E` over `l` is unramified over `k`
  have hEunr_k : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥E),
      𝔮.asIdeal.LiesOver l.asIdeal →
        𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    intro 𝔮 h𝔮
    haveI : 𝔮.asIdeal.LiesOver (Ideal.under (NumberField.RingOfIntegers ↥K1) 𝔮.asIdeal) :=
      Ideal.over_under 𝔮.asIdeal
    let 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K1) :=
      ⟨Ideal.under (NumberField.RingOfIntegers ↥K1) 𝔮.asIdeal, inferInstance,
        Ideal.under_ne_bot _ 𝔮.ne_bot⟩
    have h𝔮𝔭 : 𝔮.asIdeal.LiesOver 𝔭.asIdeal := Ideal.over_under 𝔮.asIdeal
    have h𝔭 : 𝔭.asIdeal.LiesOver l.asIdeal :=
      Ideal.LiesOver.tower_bot (A := NumberField.RingOfIntegers k)
        (B := NumberField.RingOfIntegers ↥K1)
        (C := NumberField.RingOfIntegers ↥E) 𝔮.asIdeal 𝔭.asIdeal l.asIdeal
    rw [Ideal.ramificationIdx_tower 𝔭.asIdeal 𝔮.asIdeal, hK1unr 𝔭 h𝔭, one_mul]
    exact hEunr 𝔭 h𝔭 𝔮 h𝔮𝔭
  -- the same statement for `E' = E.restrictScalars k`
  have hE'unr : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥E'),
      𝔮.asIdeal.LiesOver l.asIdeal →
        𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 :=
    fun 𝔮 h𝔮 => hEunr_k 𝔮 h𝔮
  -- ### Step 2: the normal closure of `E'` is unramified over `l`
  have hF'unr :=
    Work.SSGRoute.TPatom.ramificationIdx_eq_one_normalClosure (k := k) (M := L) E' l hE'unr
  -- ### Step 3: the inertia group of `q'` in `Gal(L/k)` fixes `F'` pointwise
  have hQF : (q'.asIdeal.under (NumberField.RingOfIntegers ↥F')).LiesOver l.asIdeal := by
    refine Ideal.LiesOver.tower_bot (A := NumberField.RingOfIntegers k)
      (B := NumberField.RingOfIntegers ↥F') (C := NumberField.RingOfIntegers L) q'.asIdeal
      (Ideal.under (NumberField.RingOfIntegers ↥F') q'.asIdeal) l.asIdeal
  have hfix : Ideal.inertia (L ≃ₐ[k] L) q'.asIdeal ≤ F'.fixingSubgroup :=
    Work.SSGRoute.TPatom.inertia_le_fixingSubgroup_of_ramificationIdx_eq_one F' q'
      (hF'unr ⟨q'.asIdeal.under (NumberField.RingOfIntegers ↥F'), inferInstance,
        Ideal.under_ne_bot _ q'.ne_bot⟩ hQF)
  -- ### Step 4: `L` is generated over `k` by the image of `K` and by `F'`
  have hF'eq : F' = ⨆ τ : (L ≃ₐ[k] L), (E.restrictScalars k).map (τ : L →ₐ[k] L) := by
    change IntermediateField.normalClosure k (E.restrictScalars k) L = _
    rw [IntermediateField.normalClosure_def'']
  have hE'F' : E' ≤ F' := IntermediateField.le_normalClosure E'
  have hK1F' : (K1 : IntermediateField k L) ≤ F' := hK1E'.trans hE'F'
  have hgen' : (⊤ : IntermediateField k L) ≤ Kf ⊔ F' := by
    have hgenF : (⊤ : IntermediateField k L) ≤ Kf ⊔ K1 ⊔ F' := by
      rw [hF'eq]
      exact hgen
    exact le_of_le_of_eq hgenF (by rw [sup_assoc, sup_eq_right.mpr hK1F'])
  -- ### Step 5: conclude
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  -- `σ`, viewed in `Gal(L/k)`, is inertial at `q'`
  have hσ' : AlgEquiv.restrictScalars k σ ∈ Ideal.inertia (L ≃ₐ[k] L) q'.asIdeal := by
    rw [AddSubgroup.mem_inertia] at hσ ⊢
    exact fun x => hσ x
  have hfixF : AlgEquiv.restrictScalars k σ ∈ F'.fixingSubgroup := hfix hσ'
  -- `σ` fixes the image of `K`
  have hfixK : AlgEquiv.restrictScalars k σ ∈ Kf.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro x ⟨y, rfl⟩
    exact σ.commutes y
  have hle : AlgEquiv.restrictScalars k σ ∈ (Kf ⊔ F').fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hfixK, hfixF⟩
  have hρ1 : AlgEquiv.restrictScalars k σ = 1 := by
    have h2 := IntermediateField.fixingSubgroup_le hgen' hle
    rw [IntermediateField.fixingSubgroup_top] at h2
    exact Subgroup.mem_bot.mp h2
  refine AlgEquiv.ext fun x => ?_
  have h3 := DFunLike.congr_fun hρ1 x
  rwa [AlgEquiv.restrictScalars_apply, AlgEquiv.one_apply] at h3

end Work.SSGate
