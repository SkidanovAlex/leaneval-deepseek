import Submission.NK.EndgameRepair.ExistsSigma
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.LocalReciprocityLubinTate.Target

/-!
# The Neukirch–Uchida wall, version 2 (orchestrator-owned; do not edit)

The four inputs of the proved, axiom-clean `NK.EndgameRepair.exists_sigma_of_correctedResiduals`.
Replaces `NK.EndgameRepair.ClassicalChaptersRepaired`, which is UNSATISFIABLE (its `DeepInputs.indexOne`
fails for a quartic field with `2 = 𝔭₁𝔭₂³`; `TowerRankCore.finiteIndex_isClosed` lacks finite-dimensionality).
-/

namespace NK.NUV2

universe u u₁ u₂ u₃ u₄

/-- The place correspondence, for all fields in universe `u`. -/
def LCAll : Prop :=
  ∀ (K₁ K₂ K₁' K₂' : Type u) [Field K₁] [Field K₂] [Field K₁'] [Field K₂'] [NumberField K₁]
    [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)), IsHomeomorph ϕ → Nonempty (NK.Reconstruct.LocalCorrespondence ϕ)

/-- The Frobenius correspondence for every place correspondence. -/
def FrobAll : Prop :=
  ∀ (K₁ K₂ K₁' K₂' : Type u) [Field K₁] [Field K₂] [Field K₁'] [Field K₂'] [NumberField K₁]
    [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ),
    NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a

/-- Shimizu's corrected rank residual at `ℓ = 2`. -/
def ResAll : Prop :=
  ∀ (K₁ K₁' : Type u) [Field K₁] [Field K₁'] [NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁'],
    NK.RankTheoryDeep.CorrectedResidualsDerived K₁ K₁' 2

/-- Čebotarev. -/
def ChebAll : Prop :=
  ∀ (K₁ K₁' : Type u) [Field K₁] [Field K₁'] [NumberField K₁] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁'],
    NK.ReconstructEndgame.ChebotarevInputDerived K₁ K₁'

/-- The local reciprocity law at every completion of every number field (in `Type`). -/
def KCAll : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
    Nonempty (NK.LocalArtin.KernelCondition (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K)))

/-- The capstone: the challenge from the four inputs at the lifted universe. -/
def Capstone : Prop :=
  LCAll.{max u₁ u₂ u₃ u₄} → FrobAll.{max u₁ u₂ u₃ u₄} → ResAll.{max u₁ u₂ u₃ u₄} →
    ChebAll.{max u₁ u₂ u₃ u₄} →
    ∀ {K₁ : Type u₁} {K₂ : Type u₂} {K₁' : Type u₃} {K₂' : Type u₄} [Field K₁] [Field K₂] [Field K₁']
      [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
      [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)), IsHomeomorph ϕ →
      ∃! σ : K₂' ≃+* K₁', (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)

end NK.NUV2

namespace NK.NUV2

/-- `Type 0` versions of the four inputs. -/
def LCAll0 : Prop := LCAll.{0}
def FrobAll0 : Prop := FrobAll.{0}
def ResAll0 : Prop := ResAll.{0}
def ChebAll0 : Prop := ChebAll.{0}

universe v₁ v₂ v₃ v₄

/-- The capstone from the `Type 0` inputs (transport by `Shrink`: number fields and their separable closures
are countable). -/
def Capstone0 : Prop :=
  LCAll0 → FrobAll0 → ResAll0 → ChebAll0 →
    ∀ {K₁ : Type v₁} {K₂ : Type v₂} {K₁' : Type v₃} {K₂' : Type v₄} [Field K₁] [Field K₂] [Field K₁']
      [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
      [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)), IsHomeomorph ϕ →
      ∃! σ : K₂' ≃+* K₁', (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
        ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)

end NK.NUV2
