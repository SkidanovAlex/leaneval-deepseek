import Mathlib
import Submission.Work.EKLProd.borelOrbitImage

/-!
# Continuity of the coordinates of the decomposition `H = T · U`

For closed subgroups `T, U ≤ H ≤ SL₃(ℝ)` with `T` normalising `U`, `H = T · U` and
`T ⊓ U = ⊥`, every `h ∈ H` factors uniquely as `h = t · u`, and we prove here that the
coordinates of this decomposition are continuous for the subspace topologies.  The `T`-coordinate
is the map `h ↦ t(h)`, the `U`-coordinate is `ρ h = t(h)⁻¹ · h`.

The mathematical content is the **open mapping theorem for σ-compact locally compact topological
groups** (`MonoidHom.isOpenMap_of_sigmaCompact`): `U ⊴ H` because `T` normalises `U`, so the
quotient `H/U` is a locally compact topological group, and the composite

`T ↪ H ↠ H/U`

is a continuous bijective group homomorphism (injective by `T ⊓ U = ⊥`, surjective by `H = T · U`).
Since `T` is a closed subgroup of the σ-compact locally compact group `SL₃(ℝ)` it is σ-compact,
so this homomorphism is open, hence a homeomorphism.  The `T`-coordinate is then `j⁻¹` composed
with the (continuous) quotient map, and `ρ h = t(h)⁻¹ · h` is continuous as a product in `H`.
-/

namespace Work.EKLProd

open Matrix
open Work.EKLContract

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **Continuity of the `U`-coordinate of the `H = T·U` decomposition.**
For closed subgroups `T, U ≤ H ≤ SL₃(ℝ)` with `H` closed, `T` normalising `U`, `H = T·U` (every `h ∈ H` is `t * u` with `t ∈ T`, `u ∈ U`) and `T ⊓ U = ⊥`, the `U`-coordinate of the unique decomposition is continuous on `H` (subspace topologies). -/
theorem continuous_uPart {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hH : IsClosed (H : Set Work.EKLContract.SL3)) (hT : IsClosed (T : Set Work.EKLContract.SL3))
    (hU : IsClosed (U : Set Work.EKLContract.SL3)) :
    ∃ ρ : ↥(H : Set Work.EKLContract.SL3) → ↥(U : Set Work.EKLContract.SL3),
      Continuous ρ ∧ ∀ h : ↥(H : Set Work.EKLContract.SL3),
        ∃ t ∈ T, (h : Work.EKLContract.SL3) = t * (ρ h : Work.EKLContract.SL3) := by
  classical
  haveI : SigmaCompactSpace SL3 := inferInstance
  haveI : SigmaCompactSpace ↥T := hT.sigmaCompactSpace
  haveI : LocallyCompactSpace ↥H := hH.locallyCompactSpace
  haveI : SigmaCompactSpace ↥H := hH.sigmaCompactSpace
  -- Step 1: `U` (viewed inside `H`) is normal, and closed.
  have hUnorm : (U.subgroupOf H).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨t, htT, u, huU, hgu⟩ := hcop (g : SL3) g.2
    show ((g : SL3) * (x : SL3) * (g : SL3)⁻¹) ∈ U
    rw [hgu]
    have h1 : (t * u) * (x : SL3) * (t * u)⁻¹ = t * (u * (x : SL3) * u⁻¹) * t⁻¹ := by group
    rw [h1]
    exact hnorm t htT _ (U.mul_mem (U.mul_mem huU hx) (U.inv_mem huU))
  haveI : (U.subgroupOf H).Normal := hUnorm
  haveI : IsClosed ((U.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.coe_subgroupOf]
    exact hU.preimage continuous_subtype_val
  -- Step 2: `T` is σ-compact, `H ⧸ U` is Baire (locally compact, T₃).
  haveI : BaireSpace (↥H ⧸ U.subgroupOf H) := inferInstance
  -- Step 3: the inclusion `T ↪ H ⧸ U` is a continuous bijective homomorphism.
  let jhom : ↥T →* (↥H ⧸ U.subgroupOf H) :=
    (QuotientGroup.mk' (U.subgroupOf H)).comp (Subgroup.inclusion hTH)
  have hjcont : Continuous ⇑jhom := by
    simp only [jhom, MonoidHom.coe_comp]
    exact QuotientGroup.continuous_mk.comp (continuous_subtype_val.subtype_mk _)
  have hjinj : Function.Injective ⇑jhom := by
    intro a b hab
    simp only [jhom, MonoidHom.coe_comp] at hab
    refine Subtype.ext (inv_mul_eq_one.mp ?_)
    have h1 : ((a : SL3))⁻¹ * (b : SL3) ∈ U :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq).mp hab)
    exact hdisj _ (T.mul_mem (T.inv_mem a.2) b.2) h1
  have hjsurj : Function.Surjective ⇑jhom := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨t, htT, u, huU, htu⟩ := hcop (h : SL3) h.2
    refine ⟨⟨t, htT⟩, ?_⟩
    simp only [jhom, MonoidHom.coe_comp]
    refine (QuotientGroup.eq).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    show (t : SL3)⁻¹ * (h : SL3) ∈ U
    rw [htu]
    simpa using huU
  -- Step 4: the open mapping theorem turns `j` into a homeomorphism.
  have hjopen : IsOpenMap ⇑jhom :=
    MonoidHom.isOpenMap_of_sigmaCompact jhom hjsurj hjcont
  let hjhomeo : ↥T ≃ₜ (↥H ⧸ U.subgroupOf H) :=
    (Equiv.ofBijective ⇑jhom ⟨hjinj, hjsurj⟩).toHomeomorphOfContinuousOpen hjcont hjopen
  have hjhomeo_apply : ∀ x : ↥T, hjhomeo x = QuotientGroup.mk (Subgroup.inclusion hTH x) := by
    intro x
    simp only [hjhomeo, Equiv.toHomeomorphOfContinuousOpen_apply, Equiv.ofBijective_apply, jhom,
      MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
  -- Step 5: the `T`-coordinate `h ↦ t(h)` is continuous, being `j⁻¹` after the quotient map.
  let tpart : ↥H → ↥T := fun h => hjhomeo.symm (QuotientGroup.mk h)
  have htpart_cont : Continuous tpart := by
    simp only [tpart]
    exact hjhomeo.symm.continuous.comp QuotientGroup.continuous_mk
  have hkey : ∀ h : ↥H, ((tpart h : ↥T) : SL3)⁻¹ * (h : SL3) ∈ U := by
    intro h
    have hj' : hjhomeo (tpart h) = QuotientGroup.mk h := by
      simp only [tpart, Homeomorph.apply_symm_apply]
    have hj : (QuotientGroup.mk (Subgroup.inclusion hTH (tpart h)) : ↥H ⧸ U.subgroupOf H)
        = QuotientGroup.mk h :=
      (hjhomeo_apply (tpart h)).symm.trans hj'
    have h1 : (Subgroup.inclusion hTH (tpart h))⁻¹ * h ∈ U.subgroupOf H :=
      (QuotientGroup.eq).mp hj
    simpa using Subgroup.mem_subgroupOf.mp h1
  refine ⟨fun h => ⟨((tpart h : ↥T) : SL3)⁻¹ * (h : SL3), hkey h⟩, ?_, ?_⟩
  · exact Continuous.subtype_mk (by fun_prop) (fun h => hkey h)
  · intro h
    exact ⟨((tpart h : ↥T) : SL3), (tpart h).2, by simp⟩

end Work.EKLProd
