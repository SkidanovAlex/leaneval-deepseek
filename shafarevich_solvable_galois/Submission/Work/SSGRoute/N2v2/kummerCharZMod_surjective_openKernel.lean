import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.N2v2.kummerField_le_of_vanishes_on_fixingSubgroup
import Submission.Work.SSGRoute.ZConstruction.kummerCharZModAdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Kummer surjectivity at the level `↥K` for characters with open kernel

`ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK` realises every additive, locally
constant cochain on `K.fixingSubgroup` as a Kummer character; in its proof the local constancy is
used *only* to obtain the openness of the kernel of the `↥K`-level character.  This file records the
form in which that is actually needed downstream: an additive character of `Gal(Ω/↥K)` with **open
kernel** is `σ ↦ χ_β σ` for some `β ∈ (↥K)ˣ`.  Its corollary realises any character of
`Gal(M/↥K)` killing the fixing subgroup of a subfield `F₀ ≤ M` as the descent of a Kummer character
with `KummerField c ≤ F₀`, which is the hypothesis `hreal` of `N2v2/separation.lean`.
-/

open scoped Pointwise
open NumberField IsDedekindDomain
open NK.GlobalCFT

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.N2v2

/-- **Kummer surjectivity at the level `↥K` for characters with open kernel.** -/
theorem kummerCharZMod_surjective_openKernel (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (z : (Ω ≃ₐ[↥K] Ω) →* Multiplicative (ZMod p))
    (hz : IsOpen (z.ker : Set (Ω ≃ₐ[↥K] Ω))) :
    ∃ β : (↥K)ˣ, ∀ σ : Ω ≃ₐ[↥K] Ω,
      z σ = Multiplicative.ofAdd
        (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ β σ) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- the `μ_p`-valued character
  let zrK : Multiplicative (ZMod p) ≃* ↥(rootsOfUnity p ↥K) :=
    Work.SSGRoute.zr (Work.SSGRoute.isPrimitiveRoot_primRootUnit (p := p) hζ)
  let ω : (Ω ≃ₐ[↥K] Ω) →* ↥(rootsOfUnity p ↥K) := zrK.toMonoidHom.comp z
  have hopen_ω : IsOpen (ω.ker : Set (Ω ≃ₐ[↥K] Ω)) := by
    have hkerω : (ω.ker : Subgroup (Ω ≃ₐ[↥K] Ω)) = z.ker := by
      ext σ
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      show zrK (z σ) = 1 ↔ z σ = 1
      constructor
      · intro h
        have h' : zrK (z σ) = zrK 1 := by rw [h, map_one]
        exact zrK.injective h'
      · intro h; rw [h, map_one]
    rw [show (ω.ker : Set (Ω ≃ₐ[↥K] Ω)) = (z.ker : Set (Ω ≃ₐ[↥K] Ω)) from by rw [hkerω]]
    exact hz
  -- realisation of the character by a Kummer resolvent
  haveI hsepK : IsSepClosure ↥K Ω := ⟨IsSepClosure.sep_closed Ω, inferInstance⟩
  obtain ⟨γ, hγmem, hγdiv⟩ :=
    Work.SSGRoute.kummer_character_realization_inf (U := ↥K) (L := Ω) (n := p)
      (Fact.out : p.Prime).ne_zero ω hopen_ω
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
  let β : (↥K)ˣ := Units.mk0 x hx0
  let γu : Ωˣ := Units.mk0 γ hγ0
  have hγu : γu ^ p = Units.map (algebraMap ↥K Ω) β := by
    apply Units.ext
    show γ ^ p = (algebraMap ↥K Ω) x
    exact hx.symm
  refine ⟨β, ?_⟩
  intro σ
  have hω_apply : ∀ τ : Ω ≃ₐ[↥K] Ω, ω τ = zrK (z τ) := fun τ => rfl
  have hratio : Work.Kummer.kummerRatio σ γu =
      Units.map (algebraMap ↥K Ω) (((ω σ : ↥(rootsOfUnity p ↥K)) : (↥K)ˣ)) := by
    apply Units.ext
    rw [Work.Kummer.kummerRatio_coe, Units.coe_map]
    show (σ : Ω → Ω) γ / γ =
      algebraMap ↥K Ω (((ω σ : ↥(rootsOfUnity p ↥K)) : (↥K)ˣ) : ↥K)
    exact hγdiv σ
  rw [Work.SSGRoute.kummerCharZMod_apply]
  rw [Work.SSGRoute.kummerIdx_congr p hζ β
    (Work.SSGRoute.kummerSqrtUnitZMod_pow (Ω := Ω) p β) hγu σ]
  have hkey : ((Work.SSGRoute.zr (Work.SSGRoute.isPrimitiveRoot_mappedRoot (F := ↥K) (E := Ω)
        (p := p) hζ)
        (Multiplicative.ofAdd
          (Work.SSGRoute.kummerIdx p hζ β γu hγu σ)) : ↥(rootsOfUnity p Ω)) : Ωˣ)
      = ((Work.SSGRoute.zr (Work.SSGRoute.isPrimitiveRoot_mappedRoot (F := ↥K) (E := Ω) (p := p)
        hζ) (z σ) : ↥(rootsOfUnity p Ω)) : Ωˣ) := by
    rw [← Work.SSGRoute.kummerIdx_spec p hζ β γu hγu σ, hratio, hω_apply σ]
    exact (Work.SSGRoute.zr_map_eq (F := ↥K) (E := Ω) p hζ (z σ)).symm
  have hfin : Multiplicative.ofAdd (Work.SSGRoute.kummerIdx p hζ β γu hγu σ) = z σ :=
    (Work.SSGRoute.zr (Work.SSGRoute.isPrimitiveRoot_mappedRoot (F := ↥K) (E := Ω) (p := p)
      hζ)).injective (Subtype.ext hkey)
  rw [← hfin]

/-- **Every character of `Gal(M/↥K)` killing the fixing subgroup of `F₀` is a Kummer character with
Kummer field inside `F₀`.** -/
theorem exists_kummerChar_of_vanishes_on_fixingSubgroup (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M]
    (F₀ : IntermediateField ↥K Ω) [FiniteDimensional ↥K F₀]
    (χ : (↥M ≃ₐ[↥K] ↥M) →* Multiplicative (ZMod p))
    (hχ : ∀ σ : Ω ≃ₐ[↥K] Ω, σ ∈ F₀.fixingSubgroup →
      χ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ) = 1) :
    ∃ c : (↥K)ˣ, NK.LocalAnabelian.kummerField (K' := Ω) p c ≤ F₀ ∧
      ∀ σ : Ω ≃ₐ[↥K] Ω,
        χ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ) =
          Multiplicative.ofAdd
            (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ) := by
  classical
  haveI hNumK : NumberField ↥K := NumberField.of_module_finite k ↥K
  -- the `↥K`-level avatar of `χ`
  let z : (Ω ≃ₐ[↥K] Ω) →* Multiplicative (ZMod p) :=
    χ.comp (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M)
  -- its kernel contains the open subgroup `F₀.fixingSubgroup`
  have hzopen : IsOpen (z.ker : Set (Ω ≃ₐ[↥K] Ω)) := by
    refine Subgroup.isOpen_of_mem_nhds z.ker (g := 1) ?_
    refine Filter.mem_of_superset
      (IsOpen.mem_nhds (IntermediateField.fixingSubgroup_isOpen F₀) (Subgroup.one_mem _)) ?_
    intro σ hσ
    have h2 : z σ = 1 := by
      show χ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M σ) = 1
      exact hχ σ hσ
    simpa using h2
  obtain ⟨c, hc⟩ := kummerCharZMod_surjective_openKernel p k Ω K ζ hζ z hzopen
  refine ⟨c, ?_, ?_⟩
  · -- the Kummer field of `c` lies in `F₀`
    refine kummerField_le_of_vanishes_on_fixingSubgroup p k Ω K ζ hζ c F₀ ?_
    intro τ hτ
    have h1 : z τ = 1 := by
      rw [show z τ = χ (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) M τ) from rfl, hχ τ hτ]
    have h2 : Multiplicative.ofAdd
        (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c τ) =
        Multiplicative.ofAdd (0 : ZMod p) := by
      rw [← hc τ, h1]
      rfl
    simpa using congrArg Multiplicative.toAdd h2
  · intro σ
    show z σ = Multiplicative.ofAdd
      (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ)
    exact hc σ

end Work.SSGRoute.N2v2
