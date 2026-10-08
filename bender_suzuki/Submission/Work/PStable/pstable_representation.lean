import Mathlib
import Submission.Work.HallHigman.Basic
import Submission.Work.HallHigman.GLCore.glCore
import Submission.Work.HallHigman.GLCore.centralizer_opCore_le
import Submission.Work.HallHigman.ModRep
import Submission.Work.PStable.Quad.Defs
import Submission.Work.PStable.Quad.quadCore_of_representation
import Submission.Work.PStable.Quad.glCore_quad_algClosed

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.PStable

theorem pstable_representation {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (hps : Work.HallHigman.IsPSolvable p G)
    (h2 : p ≥ 5 ∨ ∀ Q : Sylow 2 G, IsMulCommutative ↥(Q : Subgroup G))
    (ρ : Representation (ZMod p) G V) (hfaith : Function.Injective ρ)
    (hOp : Work.HallHigman.pCore p G = ⊥)
    (A : Subgroup G) (hAp : IsPGroup p A) (hquad : ∀ a ∈ A, (ρ a - 1) ^ 2 = 0) :
    A = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by obtain ⟨k, hk⟩ := hodd; omega
  haveI hfd : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  by_contra hane
  -- reduction to the quadratic core hypothesis over `F_p`
  obtain ⟨Q, X, hcore, hfail⟩ :=
    Work.PStable.Quad.quadCore_of_representation hp hps h2 ρ hfaith hOp A hAp ha hane
      (hquad a ha)
  -- extend scalars to an algebraic closure of `F_p`
  haveI hcharL : CharP (AlgebraicClosure (ZMod p)) p :=
    charP_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (ZMod p) (AlgebraicClosure (ZMod p))) p
  haveI halg : IsAlgClosed (AlgebraicClosure (ZMod p)) := AlgebraicClosure.isAlgClosed (ZMod p)
  haveI hfdL : FiniteDimensional (AlgebraicClosure (ZMod p))
      (Fin (Module.finrank (ZMod p) V) → AlgebraicClosure (ZMod p)) := inferInstance
  let F : Module.End (ZMod p) V →+*
      Module.End (AlgebraicClosure (ZMod p))
        (Fin (Module.finrank (ZMod p) V) → AlgebraicClosure (ZMod p)) :=
    Work.HallHigman.GLCore.glCoreScalarMap (ZMod p) (AlgebraicClosure (ZMod p)) V
  have hF : Function.Injective F :=
    Work.HallHigman.GLCore.glCoreScalarMap_injective (ZMod p) (AlgebraicClosure (ZMod p))
      (FaithfulSMul.algebraMap_injective (ZMod p) (AlgebraicClosure (ZMod p))) V
  have hQ : Work.PStable.Quad.QuadCore p (Q.map (Units.map F.toMonoidHom))
      (Units.map F.toMonoidHom X) := hcore.unitsMap F hF
  refine (Work.PStable.Quad.glCore_quad_algClosed (K := AlgebraicClosure (ZMod p))
    (V := Fin (Module.finrank (ZMod p) V) → AlgebraicClosure (ZMod p)) hp2 hQ) ?_
  have hcoe : ((Units.map F.toMonoidHom X : (Module.End (AlgebraicClosure (ZMod p))
      (Fin (Module.finrank (ZMod p) V) → AlgebraicClosure (ZMod p)))ˣ) :
      Module.End (AlgebraicClosure (ZMod p))
        (Fin (Module.finrank (ZMod p) V) → AlgebraicClosure (ZMod p))) = F X :=
    Units.coe_map F.toMonoidHom X
  rw [hcoe]
  have hmap : (F (X : Module.End (ZMod p) V) - 1) ^ 2
      = F (((X : Module.End (ZMod p) V) - 1) ^ 2) := by
    rw [show (F (X : Module.End (ZMod p) V) - 1)
        = F ((X : Module.End (ZMod p) V) - 1) from by rw [map_sub, map_one], ← map_pow]
  rw [hmap, hfail, map_zero]

end Work.PStable
