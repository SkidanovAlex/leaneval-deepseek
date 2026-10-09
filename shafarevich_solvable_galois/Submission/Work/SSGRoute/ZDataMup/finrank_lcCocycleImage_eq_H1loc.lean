import Mathlib
import Submission.Work.SSGRoute.ZDataMup.QuotDefs
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

open scoped Pointwise

theorem finrank_lcCocycleImage_eq_H1loc {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] {H : Subgroup (Ω ≃ₐ[k] Ω)}
    (hH : H ≤ K.fixingSubgroup) :
    Module.finrank (ZMod p) ↥(Work.SSGRoute.ZDataMup.lcCocycleImage (p := p) K H) =
      Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K (ZMod p) H) := by
  have hsub : localCocycle (p := p) K H = Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H :=
    Submodule.ext fun _ => Iff.rfl
  have himg : lcCocycleImage (p := p) K H =
      (Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H).map (restrictToSub (p := p) H) := by
    show (localCocycle (p := p) K H).map (restrictToSub (p := p) H) =
      (Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H).map (restrictToSub (p := p) H)
    rw [hsub]
  let φ : ↥(Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H) →ₗ[ZMod p]
      ↥(lcCocycleImage (p := p) K H) :=
    { toFun := fun f => ⟨restrictToSub (p := p) H f.1, by
        rw [himg]; exact Submodule.mem_map.mpr ⟨f.1, f.2, rfl⟩⟩
      map_add' := fun f g => Subtype.ext ((restrictToSub (p := p) H).map_add f.1 g.1)
      map_smul' := fun c f => Subtype.ext ((restrictToSub (p := p) H).map_smul c f.1) }
  have hφ : ∀ f : ↥(Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H),
      (φ f).1 = restrictToSub (p := p) H f.1 := fun _ => rfl
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : y.1 ∈ (Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H).map
        (restrictToSub (p := p) H) := by
      rw [← himg]; exact y.2
    obtain ⟨b, hb, hbx⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨b, hb⟩, Subtype.ext hbx⟩
  have hker : LinearMap.ker φ =
      Submodule.comap (Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H).subtype
        (Work.SSGRoute.coboundaries p k Ω K (ZMod p) H) := by
    ext f
    rw [LinearMap.mem_ker, Submodule.mem_comap, Work.SSGRoute.mem_coboundaries]
    change φ f = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H f.1
    rw [isCoboundaryOn_iff_eqOn_zero (p := p) hH]
    change φ f = 0 ↔ ∀ g ∈ H, f.1 g = 0
    constructor
    · intro hf g hg
      have h2 := congrFun (congrArg Subtype.val hf) (⟨g, hg⟩ : ↥H)
      rw [hφ f] at h2
      simpa using h2
    · intro hf
      apply Subtype.ext
      funext x
      rw [hφ f]
      simpa using hf x.1 x.2
  have e : Work.SSGRoute.H1loc p k Ω K (ZMod p) H ≃ₗ[ZMod p]
      ↥(lcCocycleImage (p := p) K H) :=
    (Submodule.quotEquivOfEq (LinearMap.ker φ)
      (Submodule.comap (Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H).subtype
        (Work.SSGRoute.coboundaries p k Ω K (ZMod p) H)) hker).symm.trans
      (LinearMap.quotKerEquivOfSurjective φ hsurj)
  exact e.symm.finrank_eq

end Work.SSGRoute.ZDataMup
