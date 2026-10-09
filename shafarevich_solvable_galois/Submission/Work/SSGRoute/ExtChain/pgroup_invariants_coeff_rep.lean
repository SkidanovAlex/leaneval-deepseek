import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.CohomologicallyTrivial.pgroup_invariants_ne_bot_int
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Nonzero invariants of a nontrivial `p`-group representation over `Coeff = ULift ℤ`

The `Coeff`-coefficient form (for the Poitou–Tate `Ext` core of `SSGRoute.PTDefs`) of the standard
fact that a finite `p`-group has no nontrivial simple modules in characteristic `p`: a nonzero
representation `N` of a finite `p`-group `G` whose vectors all have additive order dividing `p`
(`p • x = 0`) possesses a nonzero `G`-fixed vector.

The point is that the hypothesis `p • x = 0` — a statement purely about the *additive group* of
`N.V`, expressed with the natural-number scalar multiplication — turns `N.V` into a module over
`ZMod p` (`AddCommGroup.zmodModule`), and the `G`-action, which is `Coeff`-linear hence additive,
commutes with this scalar action (`ZMod.map_smul`).  So `N.V` is a `ZMod p`-representation of `G`
and the characteristic-`p` statement `pgroup_invariants_ne_bot` applies verbatim.
-/

namespace Work.SSGRoute.ExtChain

set_option linter.style.haveILetI false

theorem pgroup_invariants_coeff_rep {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (hpG : IsPGroup p G) (N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hN : ∀ x : N.V, p • x = 0) [Nontrivial N.V] :
    ∃ v : N.V, v ≠ 0 ∧ ∀ g : G, N.ρ g v = v := by
  classical
  -- `p • x = 0` makes the additive group of `N.V` a `ZMod p`-module.
  letI : Module (ZMod p) N.V := AddCommGroup.zmodModule hN
  -- The `G`-action of the representation, as a `DistribMulAction` on `N.V`.
  letI : DistribMulAction G N.V :=
    { smul := fun g v => N.ρ g v
      one_smul := fun v => by show N.ρ 1 v = v; rw [map_one]; rfl
      mul_smul := fun g h v => by show N.ρ (g * h) v = N.ρ g (N.ρ h v); rw [map_mul]; rfl
      smul_zero := fun g => by show N.ρ g 0 = 0; exact map_zero _
      smul_add := fun g x y => by
        show N.ρ g (x + y) = N.ρ g x + N.ρ g y
        exact map_add _ x y }
  -- Every `N.ρ g`, being additive, is `ZMod p`-linear for this scalar structure.
  letI : SMulCommClass G (ZMod p) N.V :=
    ⟨fun g c v => by
      show N.ρ g (c • v) = c • N.ρ g v
      exact ZMod.map_smul (N.ρ g).toAddMonoidHom c v⟩
  -- Apply the `ZMod p`-coefficient statement to `N.V` with this structure.
  obtain ⟨v, hv, hfix⟩ :=
    Work.CohomologicallyTrivial.pgroup_invariants_ne_bot hpG
      (Rep.ofDistribMulAction (ZMod p) G N.V) ‹Nontrivial N.V›
  exact ⟨v, hv, fun g => hfix g⟩

end Work.SSGRoute.ExtChain
