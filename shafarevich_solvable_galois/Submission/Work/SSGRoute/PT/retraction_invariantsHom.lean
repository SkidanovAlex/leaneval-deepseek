import Mathlib
import Submission.Work.SSGRoute.PT.AlphaPairing
import Submission.Work.SSGRoute.PT.submodule_retraction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A retraction of `invariantsHom φ` for `𝔽_p[G]`-modules

For `𝔽_p[G]`-modules (`p` prime) and an equivariant *injective* `φ : N₁ →+ N₂`, the induced map
`invariantsHom φ hφ : (invariants G N₁) →+ (invariants G N₂)` admits an additive retraction.

This is the exactness input `hg'` of the `α²`-dévissage (`PT/AlphaTwoAssembly.lean`): the dual of
the injection `invariantsHom φ hφ` is surjective.

The proof: the image of `invariantsHom φ hφ` (viewed inside `N₂`) is an `𝔽_p`-subspace, hence a
direct summand of `N₂` (`PT/submodule_retraction.lean`); the retraction is transported along the
iso `(N₁)^G ≅ image`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Classical

namespace Work.SSGRoute.PT

theorem retraction_invariantsHom (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] {N₁ : Type*} [AddCommGroup N₁] [Module (ZMod p) N₁]
    [DistribMulAction G N₁] [SMulCommClass G (ZMod p) N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module (ZMod p) N₂] [DistribMulAction G N₂]
    [SMulCommClass G (ZMod p) N₂]
    (φ : N₁ →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hinj : Function.Injective φ) :
    ∃ r : ↥(Work.GroupCohomology.invariants G N₂) →+ ↥(Work.GroupCohomology.invariants G N₁),
      ∀ x : ↥(Work.GroupCohomology.invariants G N₁),
        r (Work.SSGRoute.PT.invariantsHom φ hφ x) = x := by
  classical
  haveI hne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- the image of the invariants of `N₁` inside `N₂`, as an `𝔽_p`-subspace
  let L : Submodule (ZMod p) N₂ :=
    { carrier := {x : N₂ | ∃ y : ↥(Work.GroupCohomology.invariants G N₁), φ (y : N₁) = x}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, rfl⟩
        refine ⟨c.val • a, ?_⟩
        change φ (c.val • (a : N₁)) = c • φ (a : N₁)
        rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p) c.val (φ (a : N₁)),
          ZMod.natCast_zmod_val] }
  obtain ⟨r', hr'⟩ := submodule_retraction p N₂ L
  -- the iso between the invariants of `N₁` and the image
  let e : ↥(Work.GroupCohomology.invariants G N₁) →+ ↥L :=
    { toFun := fun y => ⟨φ (y : N₁), ⟨y, rfl⟩⟩
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hbij : Function.Bijective e := by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact hinj (congrArg (fun t : ↥L => (t : N₂)) hab)
    · rintro ⟨z, y, hy⟩
      exact ⟨y, Subtype.ext hy⟩
  let e' : ↥(Work.GroupCohomology.invariants G N₁) ≃+ ↥L := AddEquiv.ofBijective e hbij
  refine ⟨e'.symm.toAddMonoidHom.comp (r'.comp (AddSubgroup.subtype _)), ?_⟩
  intro x
  have hx : r' (φ (x : N₁)) = e x := by
    have := hr' (e x)
    simpa [e] using this
  show e'.symm (r' ((Work.SSGRoute.PT.invariantsHom φ hφ x : N₂))) = x
  have hcoe : ((Work.SSGRoute.PT.invariantsHom φ hφ x : N₂)) = φ (x : N₁) := rfl
  rw [hcoe, hx]
  exact e'.symm_apply_apply x

end Work.SSGRoute.PT
