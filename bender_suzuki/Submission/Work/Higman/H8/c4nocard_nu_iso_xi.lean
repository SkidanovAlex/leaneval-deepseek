import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.MSA.l8_defs
import Submission.Work.Higman.H8.c4nocard_nu_iso

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.H8

theorem c4nocard_nu_iso_xi {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    [hN : ((Work.Higman.powSub A 2).subgroupOf A).Normal] :
    ∃ Φ : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A) →* ↥(Work.Higman.omega1 P),
      Function.Bijective Φ ∧
      (∀ a : ↥A, Φ (QuotientGroup.mk (Work.Higman.MSA.xiSubAut h hA.map_eq a))
        = Work.Higman.MSA.xiSubAut h (Work.Higman.map_xi_omega1 h) (Φ (QuotientGroup.mk a))) := by
  classical
  -- `c4nocard_nu_iso` provides the squaring isomorphism `A/A² ≅ Ω₁(P)`.
  obtain ⟨Φ, hbij, hΦ⟩ := c4nocard_nu_iso h hA htop hcard
  refine ⟨Φ, hbij, fun a => ?_⟩
  -- On representatives the identity to prove is `ξ(a)² = ξ(a²)`, which holds because `ξ` is a
  -- group homomorphism.
  rw [hΦ (Work.Higman.MSA.xiSubAut h hA.map_eq a), hΦ a]
  refine Subtype.ext ?_
  change ((Work.Higman.MSA.xiSubAut h hA.map_eq a : ↥A) : P) ^ 2 = h.xi ((a : P) ^ 2)
  rw [Work.Higman.MSA.xiSubAut_apply, ← map_pow]

end Work.Higman.H8
