import Mathlib
import Submission.Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
import Submission.Work.SSGRoute.N2v2.kummerField_le_of_vanishes_on_fixingSubgroup
import Submission.Work.SSGRoute.kummer_character_realization_inf
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.N2v2

theorem kummer_level_realisation (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (E : IntermediateField ↥K Ω) [FiniteDimensional ↥K E] [IsGalois ↥K E] [NumberField ↥E]
    (χ : (↥E ≃ₐ[↥K] ↥E) →* Multiplicative (ZMod p)) :
    ∃ c : (↥K)ˣ,
      NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ E ∧
      ∀ σ : Ω ≃ₐ[↥K] Ω,
        χ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ) =
          Multiplicative.ofAdd
            (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ) := by
  classical
  haveI hsepK : IsSepClosure ↥K Ω := ⟨inferInstance, inferInstance⟩
  -- The `μ_p`-valued character `σ ↦ χ (σ|_E)` of `Gal(Ω/↥K)`.
  let zrK : Multiplicative (ZMod p) ≃* ↥(rootsOfUnity p ↥K) :=
    Work.SSGRoute.zr (Work.SSGRoute.isPrimitiveRoot_primRootUnit (F := ↥K) (p := p) hζ)
  let zK : (Ω ≃ₐ[↥K] Ω) →* Multiplicative (ZMod p) :=
    χ.comp (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E)
  let ω : (Ω ≃ₐ[↥K] Ω) →* ↥(rootsOfUnity p ↥K) := zrK.toMonoidHom.comp zK
  -- `ker ω` is open: it contains `E.fixingSubgroup`, open since `E/↥K` is finite.
  have hker : E.fixingSubgroup ≤ ω.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker]
    have h1 : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (K := ↥K) E]
      exact hσ
    show zrK (zK σ) = 1
    rw [show zK σ = 1 from by
      show χ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ) = 1
      rw [h1, map_one], map_one]
  have hopen : IsOpen (ω.ker : Set (Ω ≃ₐ[↥K] Ω)) :=
    Subgroup.isOpen_mono hker (IntermediateField.fixingSubgroup_isOpen E)
  -- Realise the character by a Kummer resolvent.
  obtain ⟨γ, hγmem, hγdiv⟩ :=
    Work.SSGRoute.kummer_character_realization_inf (U := ↥K) (L := Ω) (n := p)
      (Fact.out : p.Prime).ne_zero ω hopen
  obtain ⟨x, hx⟩ := hγmem
  have hγ0 : γ ≠ 0 := by
    have h1 : γ / γ = 1 := by simpa using hγdiv 1
    intro h0
    rw [h0, div_zero] at h1
    exact zero_ne_one h1
  have hx0 : x ≠ 0 := by
    intro h0
    refine hγ0 ?_
    have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have h2 : γ ^ p = 0 := by rw [← hx, h0, map_zero]
    exact (pow_eq_zero_iff hp).mp h2
  let c : (↥K)ˣ := Units.mk0 x hx0
  let γu : Ωˣ := Units.mk0 γ hγ0
  have hγu : γu ^ p = Units.map (algebraMap ↥K Ω) c := by
    apply Units.ext
    show γ ^ p = (algebraMap ↥K Ω) x
    exact hx.symm
  -- The Kummer ratio of the resolvent is the prescribed root of unity.
  have hratio : ∀ σ : Ω ≃ₐ[↥K] Ω, Work.Kummer.kummerRatio σ γu =
      Units.map (algebraMap ↥K Ω) (((ω σ : ↥(rootsOfUnity p ↥K)) : (↥K)ˣ)) := by
    intro σ
    apply Units.ext
    rw [Work.Kummer.kummerRatio_coe, Units.coe_map]
    show (σ : Ω → Ω) γ / γ =
      algebraMap ↥K Ω (((ω σ : ↥(rootsOfUnity p ↥K)) : (↥K)ˣ) : ↥K)
    exact hγdiv σ
  -- The character identity.
  have hmain : ∀ σ : Ω ≃ₐ[↥K] Ω,
      χ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ) =
        Multiplicative.ofAdd
          (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ) := by
    intro σ
    rw [Work.SSGRoute.kummerCharZMod_apply]
    rw [Work.SSGRoute.kummerIdx_congr (F := ↥K) (E := Ω) p hζ c
      (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) p c) hγu σ]
    have hA : ((Work.SSGRoute.zr (Work.SSGRoute.isPrimitiveRoot_mappedRoot
          (F := ↥K) (E := Ω) (p := p) hζ)
          (Multiplicative.ofAdd
            (Work.SSGRoute.kummerIdx (F := ↥K) (E := Ω) p hζ c γu hγu σ))
          : ↥(rootsOfUnity p Ω)) : Ωˣ)
        = Units.map (algebraMap ↥K Ω) (((ω σ : ↥(rootsOfUnity p ↥K)) : (↥K)ˣ)) := by
      rw [← Work.SSGRoute.kummerIdx_spec (F := ↥K) (E := Ω) p hζ c γu hγu σ, hratio σ]
    have hB : ((Work.SSGRoute.zr (Work.SSGRoute.isPrimitiveRoot_mappedRoot
          (F := ↥K) (E := Ω) (p := p) hζ)
          (χ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ))
          : ↥(rootsOfUnity p Ω)) : Ωˣ)
        = Units.map (algebraMap ↥K Ω) (((ω σ : ↥(rootsOfUnity p ↥K)) : (↥K)ˣ)) := by
      rw [show ω σ = zrK (χ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ)) from rfl]
      exact Work.SSGRoute.zr_map_eq (F := ↥K) (E := Ω) p hζ
        (χ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ))
    exact ((Work.SSGRoute.zr (Work.SSGRoute.isPrimitiveRoot_mappedRoot (F := ↥K) (E := Ω)
      (p := p) hζ)).injective (Subtype.ext (hA.trans hB.symm))).symm
  refine ⟨c, ?_, hmain⟩
  -- The Kummer field is contained in `E`.
  refine kummerField_le_of_vanishes_on_fixingSubgroup p k Ω K ζ hζ c E ?_
  intro σ hσ
  have h2 : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) E σ = 1 := by
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (K := ↥K) E]
    exact hσ
  have h1 : Multiplicative.ofAdd
      (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ) = 1 := by
    rw [← hmain σ, h2, map_one]
  have h3 := congrArg Multiplicative.toAdd h1
  simpa using h3

end Work.SSGRoute.N2v2
