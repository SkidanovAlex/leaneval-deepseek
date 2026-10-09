import Mathlib
import Submission.Work.SSGRoute.E8Helpers
import Submission.NK.NUV2.RouteC.inf_injective_range_eq
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_restriction_exact_of_subsingleton_H1
import Submission.Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory Representation

namespace Work.SSGRoute

/-- The `n`-torsion subgroup of an abelian group grows with `n`: for `n ∣ m` the kernel of
multiplication by `n` is contained in the kernel of multiplication by `m`. -/
lemma ker_zsmul_id_le_of_dvd {A : Type} [AddCommGroup A] [Module ℤ A] {n m : ℕ} (h : n ∣ m) :
    LinearMap.ker ((n : ℤ) • (LinearMap.id : A →ₗ[ℤ] A)) ≤
      LinearMap.ker ((m : ℤ) • (LinearMap.id : A →ₗ[ℤ] A)) := by
  obtain ⟨k, hk⟩ := h
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have hx' : (n : ℤ) • x = 0 := by simpa using hx
  have hgoal : (m : ℤ) • x = 0 := by
    have hcast : (m : ℤ) = (k : ℤ) * (n : ℤ) := by rw [hk]; push_cast; ring
    rw [hcast, mul_zsmul, hx']
    simp
  simpa using hgoal

/-- **The local-field "inflation range lies in the kernel of the restriction" (E8', step P3).** For a finite Galois extension of number fields `L₂ ⊆ L₃` and places `q₂ | q₃`, and normal subgroups `N₁, N₂` of the local Galois group `Gal((L₃)_{q₃}/(L₂)_{q₂})` with `N₂.index ∣ N₁.index`, the range of the inflation from `N₂` is contained in the kernel of the restriction to `N₁`. Proof: `NK.NUV2.RouteC.inf_injective_range_eq` gives `range (inf_N) = ker (N.index • id)` for each normal `N`, and `N₂.index ∣ N₁.index` makes the two kernels nested; `range (inf_{N₁}) = ker (res_{N₁})` by inflation–restriction exactness (Hilbert 90). Note `Submission/NK/NUV2/RouteC/inf_injective_range_eq.lean` already has the same-subgroup version `range_infNatTrans_le_ker_resNatTrans`. -/
theorem eb_local_range {L₂ L₃ : Type} [Field L₂] [NumberField L₂] [Field L₃] [NumberField L₃] [Algebra L₂ L₃] [FiniteDimensional L₂ L₃] [IsGalois L₂ L₃] (q₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₂)) (q₃ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L₃)) (hq₃₂ : q₃.asIdeal.LiesOver q₂.asIdeal) (N₁ N₂ : Subgroup (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂)) [N₁.Normal] [N₂.Normal] (h : N₂.index ∣ N₁.index) : LinearMap.range ((groupCohomology.infNatTrans ℤ N₂ 2).app (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂)).hom ≤ LinearMap.ker ((groupCohomology.resNatTrans ℤ (G := N₁) (H := NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂) N₁.subtype 2).app (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂)).hom := by
  letI : Algebra (q₂.adicCompletion L₂) (q₃.adicCompletion L₃) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q₂ q₃ hq₃₂)
  haveI hfdE : FiniteDimensional (q₂.adicCompletion L₂) (q₃.adicCompletion L₃) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion q₂ q₃ hq₃₂
  haveI hgalE : IsGalois (q₂.adicCompletion L₂) (q₃.adicCompletion L₃) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion q₂ q₃ hq₃₂
  -- Hilbert 90 for the local units, restricted to `N₁`
  have hH1 : Subsingleton (groupCohomology
      (Rep.res N₁.subtype (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂)) 1) :=
    Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units N₁
  -- Inflation–restriction exactness at `N₁`: `range (inf_{N₁}) = ker (res_{N₁})`
  have hexact : LinearMap.range ((groupCohomology.infNatTrans ℤ N₁ 2).app
        (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂)).hom =
      LinearMap.ker ((groupCohomology.resNatTrans ℤ (G := N₁)
        (H := NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂) N₁.subtype 2).app
        (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂)).hom :=
    Commons.RepresentationTheory.GroupCohomology.H2_inflation_restriction_exact_of_subsingleton_H1
      N₁ (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂) hH1
  -- The range of the inflation along a normal subgroup is its `index`-torsion (local CFT)
  have h₁ := (NK.NUV2.RouteC.inf_injective_range_eq q₂ q₃ hq₃₂ N₁).2
  have h₂ := (NK.NUV2.RouteC.inf_injective_range_eq q₂ q₃ hq₃₂ N₂).2
  calc LinearMap.range ((groupCohomology.infNatTrans ℤ N₂ 2).app
          (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂)).hom
      ≤ LinearMap.ker ((Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₂) : ℤ)
          • (LinearMap.id : _ →ₗ[ℤ] _)) := h₂.le
    _ ≤ LinearMap.ker ((Nat.card (NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂ ⧸ N₁) : ℤ)
          • (LinearMap.id : _ →ₗ[ℤ] _)) := ker_zsmul_id_le_of_dvd h
    _ = LinearMap.range ((groupCohomology.infNatTrans ℤ N₁ 2).app
          (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂)).hom := h₁.symm
    _ = LinearMap.ker ((groupCohomology.resNatTrans ℤ (G := N₁)
          (H := NK.NUV2.RouteC.localGaloisGroup L₂ L₃ q₂ q₃ hq₃₂) N₁.subtype 2).app
          (NK.NUV2.RouteC.localUnitsRep L₂ L₃ q₂ q₃ hq₃₂)).hom := hexact

end Work.SSGRoute
