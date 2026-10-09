import Mathlib
import Submission.Work.SSGRoute.ZDataMup.Defs
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup

/-- **The local half of `Work.SSGRoute.ZDataMup.localTateSystem_productFormula`.**

Given a family `F` of bilinear forms on the local `H¹`-groups, non-degenerate in the first variable
at every level-`K` local group `decomp k A ⊓ K.fixingSubgroup`, the descended pairing
`pair H a b := F H (toClass a) (toClass b)` (which is `0` automatically when `a` or `b` is not a
locally constant cocycle, because `toClass` is) satisfies all four local Tate axioms
`IsLocalTateSystem`:

* additivity in each variable comes from `toClass_add` and the bilinearity of `F H`;
* vanishing on a coboundary comes from `toClass_eq_zero_iff` (a coboundary is a locally constant
  cocycle, `coboundaries_le_lcCocycles`);
* perfectness: if `pair H a b = 0` for all locally constant cocycles `b`, then, since `toClass` is
  surjective onto the local `H¹` (`toClass_surjective`), `F H (toClass a) = 0`, so `toClass a = 0`
  by the first-variable non-degeneracy of `F H`, i.e. `a` is a coboundary by `toClass_eq_zero_iff`. -/
theorem isLocalTateSystem_of_family (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (F : ∀ H : Subgroup (Ω ≃ₐ[k] Ω),
      Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p]
        (Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p] ZMod p))
    (hF : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
        H = SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
      ∀ x, (∀ y, F H x y = 0) → x = 0) :
    Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K
      (fun H a b => F H (Work.SSGRoute.toClass p k Ω K (ZMod p) H a)
        (Work.SSGRoute.toClass p k Ω K (ZMod p) H b)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro H _ a a' b ha ha' _
    rw [Work.SSGRoute.toClass_add p k Ω K (ZMod p) H ha ha', map_add, LinearMap.add_apply]
  · intro H _ a b b' _ hb hb'
    rw [Work.SSGRoute.toClass_add p k Ω K (ZMod p) H hb hb', map_add]
  · intro H _ a b ha hb h
    rcases h with hcab | hcab
    · rw [show Work.SSGRoute.toClass p k Ω K (ZMod p) H a = 0 from
          (Work.SSGRoute.toClass_eq_zero_iff p k Ω K (ZMod p) H ha).mpr hcab,
        map_zero, LinearMap.zero_apply]
    · rw [show Work.SSGRoute.toClass p k Ω K (ZMod p) H b = 0 from
          (Work.SSGRoute.toClass_eq_zero_iff p k Ω K (ZMod p) H hb).mpr hcab,
        map_zero]
  · intro H hH a ha h
    have hzero : ∀ y : Work.SSGRoute.H1loc p k Ω K (ZMod p) H,
        F H (Work.SSGRoute.toClass p k Ω K (ZMod p) H a) y = 0 := by
      intro y
      obtain ⟨g, hg, hgy⟩ := Work.SSGRoute.toClass_surjective p k Ω K (ZMod p) H y
      have h0 : F H (Work.SSGRoute.toClass p k Ω K (ZMod p) H a)
          (Work.SSGRoute.toClass p k Ω K (ZMod p) H g) = 0 := h g hg
      simpa [hgy] using h0
    have hx : Work.SSGRoute.toClass p k Ω K (ZMod p) H a = 0 := hF H hH _ hzero
    exact (Work.SSGRoute.toClass_eq_zero_iff p k Ω K (ZMod p) H ha).mp hx

end Work.SSGRoute.ZDataMup
