import Mathlib
import Submission.Work.BSHallW.Defs
import Submission.Work.BSHallW.WeakClosure
import Submission.Work.BSHallW.IterComm
import Submission.Work.Grun.Hyp
import Submission.Work.BSHallW.CosetKernel.cosetKernel_subgroupOf_normal
import Submission.Work.BSHallW.CosetKernel.not_le_cosetKernel_of_not_mem_normalizer
import Submission.Work.BSHallW.PGroup.exists_pow_mem_of_normal_not_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSHallW.HallHyp` — producing Hall's transfer hypothesis from weak closure

This is the technical heart of the corrected Hall–Wielandt theorem.  Let `G` be finite, `p` an odd
prime, `S ∈ Sylow p G`, `A ≤ S` abelian and weakly closed in `S` (w.r.t. `G`), and let
`H = N_G(A) ⊇ S`.  For the double coset `S x H` with `x ∉ H` (so `x ∉ N_G(A)`), Hall's transfer
theorem (Theorem 14.4.1, delivered as `Work.Grun.hall_14_4_1`) asks for an element `z ∈ S` with

* `z ∉ K(x)` — `z` moves some coset of `H` inside `S x H`;
* `z ^ p ∈ K(x)` — the induced permutation has order `p`;
* `⁅u, z⁆ ∈ K(x)` for all `u ∈ S` — `z` acts centrally;
* `e_p(u, z) = 1` for all `u ∈ S` — Hall's condition 1).

The construction is M. Hall's proof of Theorem 14.4.2, condition 2):

* `A ⊄ K(x)`, because `A ≤ K(x)` would give `x⁻¹Ax ≤ H`, and (Sylow conjugacy inside `H`, weak
  closure) that forces `x ∈ H` (`not_le_cosetKernel_of_not_mem_normalizer`);
* `K(x) ◁ S` (`cosetKernel_subgroupOf_normal`) and `A ◁ S` (weak closure), so the image
  `Ā = AK(x)/K(x)` is a nontrivial normal subgroup of the `p`-group `S/K(x)`; by
  `exists_pow_mem_of_normal_not_le` there is `z ∈ A` whose image in `S/K(x)` is a **central** element
  of order `p`.  This gives the first three conditions at once;
* the fourth is Hall's derivation of condition 1) from condition 2): `e_p(u,z) = e_{p-1}(⁅u,z⁆,z)`
  (`iterComm_succ_eq_iterComm_commutator`) with `⁅u,z⁆ ∈ A` (as `A ◁ S`) and `⁅u,z⁆, z ∈ A` abelian,
  so both iterated commutators vanish — here `p - 1 ≥ 2`, i.e. `p ≠ 2`, is used
  (`iterComm_eq_one_of_abelian`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.BSHallW

variable {G : Type} [Group G] [Finite G]

/-- **Hall's hypothesis for `N_G(A)`.**  If `S ∈ Sylow p G`, `p` an odd prime, and `A ≤ S` is
abelian and weakly closed in `S`, then the pair `(S, N_G(A))` satisfies
`Work.Grun.HallHyp`: every double coset `S x N_G(A) ≠ N_G(A)` carries a central `p`-cycle `z ∈ S`
with `e_p(·, z) = 1`. -/
theorem hallHyp_of_weaklyClosed {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (S : Sylow p G) {A : Subgroup G} (hAS : A ≤ (S : Subgroup G))
    (hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      A.map (MulAut.conj g).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Work.Grun.HallHyp p (S : Subgroup G) (Subgroup.normalizer (A : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro x hx
  -- `K = K(x)`, `A ⊄ K`
  have hnotK : ¬ A ≤ Work.Grun.cosetKernel (Subgroup.normalizer (A : Set G))
      (S : Subgroup G) x :=
    Work.BSHallW.CosetKernel.not_le_cosetKernel_of_not_mem_normalizer S hAS hwc hx
  -- `A ◁ S`, `K ◁ S`
  have hAnormal : (A.subgroupOf (S : Subgroup G)).Normal := subgroupOf_normal_of_weaklyClosed hAS hwc
  have hKnormal : ((Work.Grun.cosetKernel (Subgroup.normalizer (A : Set G))
      (S : Subgroup G) x).subgroupOf (S : Subgroup G)).Normal :=
    Work.BSHallW.CosetKernel.cosetKernel_subgroupOf_normal _ _ _
  have hnotK' : ¬ (A.subgroupOf (S : Subgroup G)) ≤
      ((Work.Grun.cosetKernel (Subgroup.normalizer (A : Set G))
        (S : Subgroup G) x).subgroupOf (S : Subgroup G)) := by
    intro hle
    refine hnotK fun a ha => ?_
    have h1 : (⟨a, hAS ha⟩ : ↥(S : Subgroup G)) ∈ (A.subgroupOf (S : Subgroup G)) := by
      rw [Subgroup.mem_subgroupOf]; exact ha
    have h2 := hle h1
    rwa [Subgroup.mem_subgroupOf] at h2
  -- the central element of order `p`
  obtain ⟨z, hzA, hzK, hzp, hzc⟩ :=
    Work.BSHallW.PGroup.exists_pow_mem_of_normal_not_le hp S.isPGroup' hKnormal hAnormal hnotK'
  have hzG : (z : G) ∈ A := Subgroup.mem_subgroupOf.mp hzA
  refine ⟨(z : G), z.2, ?_, ?_, ?_, ?_⟩
  · -- `z ∉ K(x)`
    intro hmem
    exact hzK (by rw [Subgroup.mem_subgroupOf]; exact hmem)
  · -- `z ^ p ∈ K(x)`
    have h1 : ((z ^ p : ↥(S : Subgroup G)) : G) ∈
        Work.Grun.cosetKernel (Subgroup.normalizer (A : Set G)) (S : Subgroup G) x :=
      Subgroup.mem_subgroupOf.mp hzp
    rwa [Subgroup.coe_pow] at h1
  · -- `⁅u, z⁆ ∈ K(x)` for `u ∈ S`
    intro u hu
    have h1 : ((⁅(⟨u, hu⟩ : ↥(S : Subgroup G)), z⁆ : ↥(S : Subgroup G)) : G) ∈
        Work.Grun.cosetKernel (Subgroup.normalizer (A : Set G)) (S : Subgroup G) x :=
      Subgroup.mem_subgroupOf.mp (hzc ⟨u, hu⟩)
    have h2 : ((⁅(⟨u, hu⟩ : ↥(S : Subgroup G)), z⁆ : ↥(S : Subgroup G)) : G)
        = ⁅u, (z : G)⁆ :=
      map_commutatorElement (f := (S : Subgroup G).subtype) ⟨u, hu⟩ z
    rwa [h2] at h1
  · -- `e_p(u,z) = 1` for `u ∈ S`
    intro u hu
    have hcomm : ⁅u, (z : G)⁆ ∈ A := commutator_mem_of_weaklyClosed hAS hwc hu hzG
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      omega
    have hsplit : p - 1 = (p - 2) + 1 := by omega
    rw [hsplit, iterComm_succ_eq_iterComm_commutator]
    exact iterComm_eq_one_of_abelian hAab hcomm hzG (by omega)

end Work.BSHallW
