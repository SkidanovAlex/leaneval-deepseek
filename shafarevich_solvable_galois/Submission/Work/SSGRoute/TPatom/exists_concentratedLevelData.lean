import Mathlib
import Submission.Work.SSGRoute.TPatom.noninvariantLevelDefs
import Submission.Work.SSGRoute.TPatom.concentratedLevelData_proved
import Submission.Work.SSGRoute.TatePoitouRoute.exists_shapiro_c
import Submission.Work.SSGRoute.Sha2Lib.exists_cyclic_p_level_split_inert
import Submission.Work.SSGRoute.decompK_restrict_exists
import Submission.Work.SSGRoute.decompK_restrict_surjective
import Submission.Commons.NumberTheory.NumberField.finite_primesOver
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TPatom

open scoped NumberField Pointwise
open NumberField

/-! ## Bookkeeping: viewing an `IntermediateField k Ω` containing the image of `K` over `K` -/

/-- An `IntermediateField k Ω` containing the image of `K` (under `algebraMap K Ω`) is naturally an
`IntermediateField K Ω`. -/
def intermediateFieldOverK (k K Ω : Type) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : IntermediateField k Ω) (h : (IsScalarTower.toAlgHom k K Ω).fieldRange ≤ M) :
    IntermediateField K Ω :=
  { carrier := M
    mul_mem' := M.mul_mem'
    one_mem' := M.one_mem'
    add_mem' := M.add_mem'
    zero_mem' := M.zero_mem'
    inv_mem' := M.inv_mem'
    algebraMap_mem' := fun x => h (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩) }

theorem exists_concentratedLevelData (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ)
    (γ : K ≃ₐ[k] K) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (hcop : Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p)
      (d : ↥L ≃ₐ[k] ↥L) (f : ℕ)
      (hdH : d ^ f ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L))
      (y : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)) →* Multiplicative (ZMod p)),
      d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
      0 < f ∧
      (∀ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q'),
        ∃ m : ℕ, δ⁻¹ * d ^ m ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L)) ∧
      (∀ m : ℕ, 0 < m → m < f → d ^ m ∉ N.comap (SSGRoute.PTExt.galRes k K ↥L)) ∧
      (∀ x : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)),
        (x : ↥L ≃ₐ[k] ↥L) ∈
          Subgroup.normalClosure {σ : ↥L ≃ₐ[k] ↥L | SSGRoute.PTExt.IsInertiaAt q' σ} →
        y x = 1) ∧
      (∀ x : ↥L ≃ₐ[k] ↥L,
        y (TatePoitouRoute.cfunc (N.comap (SSGRoute.PTExt.galRes k K ↥L)) x
            (⟨d ^ f, hdH⟩ : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)))) = 1 ↔
          SSGRoute.PTExt.galRes k K ↥L x ∉ Work.SSGRoute.TPatom.concSet k K w N γ) := by
  classical
  -- The geometric input is proved in `TPatom/concentratedLevelData_proved.lean` (which is
  -- *byte-identical* in statement, 0 sorries, axioms `propext, Classical.choice, Quot.sound`).
  exact Work.SSGRoute.TPatom.concentratedLevelData_proved p k K Ω w q hwq hpq N hNI ζ hζ hNζ γ

end Work.SSGRoute.TPatom
