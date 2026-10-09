import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

/-- **The class of a nonzero additive character is nonzero.** For a group `G`, a prime `p` and an
additive homomorphism `f : Additive G →+ ℤ/p` with `f ≠ 0`, the class of the `1`-cocycle
`g ↦ f (Additive.ofMul g)` in `H¹(G, 𝔽_p)` (coefficient ring `SSGRoute.PTExt.Coeff = ULift ℤ`) is
nonzero.

Route: with trivial coefficients `Z¹(G, 𝔽_p) ≅ Hom(G, 𝔽_p)` via
`groupCohomology.H1IsoOfIsTrivial`, whose value on `H1π` of the cocycle of `f` is `f`
(`groupCohomology.H1IsoOfIsTrivial_inv_apply` / `groupCohomology.H1IsoOfIsTrivial_H1π_apply_apply`);
hence `H1π (cocycle f) = 0` implies `f = 0` by injectivity of the isomorphism. -/
theorem H1pi_character_ne_zero (G : Type) [Group G] (p : ℕ) [Fact p.Prime]
    (f : Additive G →+ ZMod p) (hf : f ≠ 0) :
    groupCohomology.H1π (Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p))
      ⟨f ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom
        (A := Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p)) f⟩ ≠ 0 := by
  -- `A` is the trivial `G`-module on `𝔽_p`.
  set A := Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p)
  set c : groupCohomology.cocycles₁ A :=
    ⟨f ∘ Additive.ofMul, groupCohomology.mem_cocycles₁_of_addMonoidHom (A := A) f⟩
  -- If the class of `f` were zero, the isomorphism `H¹(G, A) ≅ Hom(G, A)` would give `f = 0`.
  intro hc
  apply hf
  apply AddMonoidHom.ext
  intro x
  -- The isomorphism `H¹(G, A) ≅ Hom(G, A)` sends `H1π c` to `c` itself.
  have h1 : ((groupCohomology.H1IsoOfIsTrivial A).hom (groupCohomology.H1π A c)) x = c (Additive.toMul x) :=
    groupCohomology.H1IsoOfIsTrivial_H1π_apply_apply (A := A) c x
  rw [hc] at h1
  have h0 : ((groupCohomology.H1IsoOfIsTrivial A).hom 0) x = 0 := by simp
  rw [h0] at h1
  -- `c (Additive.toMul x)` is by definition `f x`.
  exact h1.symm

end Work.SSGRoute.Sha2Lib
