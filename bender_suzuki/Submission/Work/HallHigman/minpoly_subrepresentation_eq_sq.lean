import Mathlib
import Submission.Work.HallHigman.minpoly_eq_X_sub_one_sq_of_sq_eq_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

/-- **The minimal polynomial of an element of order dividing `p` on a subrepresentation.**

If `ρ` is a `ZMod p` representation of `G`, `W` a `G`-invariant submodule, and `x : G` acts
unipotently of index `2` on `M` (`(ρ x - 1)^2 = 0`), then the restriction of `ρ x` to `W` is
again unipotent of index `2`, and — provided it is not the identity — its minimal polynomial on
`W` is exactly `(X - 1)^2`.

The mathematical content is that the restriction `(ρ x - 1)|_W` of `ρ x - 1` to a stable
submodule is again square-zero (`Module.End.submodule_pow_eq_zero_of_pow_eq_zero`), and that
`(ρ x - 1)|_W = (ρ x)|_W - 1` (`LinearMap.restrict_sub`), so that the hypothesis of
`minpoly_eq_X_sub_one_sq_of_sq_eq_zero` is met. -/
theorem minpoly_subrepresentation_eq_sq {p : ℕ} [Fact p.Prime] {G M : Type*} [Group G]
    [AddCommGroup M] [Module (ZMod p) M] (ρ : Representation (ZMod p) G M)
    (W : Submodule (ZMod p) M) (hW : ∀ g, W ≤ W.comap (ρ g)) (x : G)
    (hsq : (ρ x - 1) ^ 2 = 0) (hne : (Representation.subrepresentation ρ W hW) x ≠ 1) :
    minpoly (ZMod p) ((Representation.subrepresentation ρ W hW) x) = (Polynomial.X - 1) ^ 2 := by
  apply minpoly_eq_X_sub_one_sq_of_sq_eq_zero
  · -- `(ρ x - 1)` maps `W` to itself, hence restricts to a square-zero endomorphism of `W`.
    have hf : Set.MapsTo (⇑(ρ x)) (W : Set M) (W : Set M) := hW x
    have hg : Set.MapsTo (⇑(1 : Module.End (ZMod p) M)) (W : Set M) (W : Set M) :=
      fun w hw => by simpa using hw
    have hfg : Set.MapsTo (⇑((ρ x) - (1 : Module.End (ZMod p) M))) (W : Set M) (W : Set M) :=
      fun w hw => W.sub_mem (hf hw) (hg hw)
    have hpz : (((ρ x) - (1 : Module.End (ZMod p) M)).restrict hfg) ^ 2 = 0 :=
      Module.End.submodule_pow_eq_zero_of_pow_eq_zero (N := W)
        (g := ((ρ x) - (1 : Module.End (ZMod p) M)).restrict hfg)
        (G := (ρ x) - (1 : Module.End (ZMod p) M))
        (LinearMap.subtype_comp_restrict hfg).symm hsq
    -- `(ρ x)|_W - 1 = (ρ x - 1)|_W`.
    have hres := LinearMap.restrict_sub hf hg (f := ρ x) (g := (1 : Module.End (ZMod p) M))
    have hone : (1 : Module.End (ZMod p) M).restrict hg = 1 := by
      ext w; simp [LinearMap.restrict]
    have hsub : (Representation.subrepresentation ρ W hW) x - 1
        = ((ρ x) - (1 : Module.End (ZMod p) M)).restrict hfg := by
      rw [Representation.subrepresentation_apply, ← hone]
      exact hres
    rw [hsub, hpz]
  · exact hne

end Work.HallHigman
