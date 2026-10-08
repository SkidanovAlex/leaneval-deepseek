import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.ASM.CyclicSylow
import Submission.Work.ASM.FT
import Submission.Work.CORE2A.Basic

namespace Work.CORE3

open Work.GW2

/-- In the minimal-counterexample setting the Sylow 2-subgroup is not cyclic: a cyclic Sylow
2-subgroup lies in the centre of its normalizer, so a non-abelian finite simple group cannot
have one (already proved as `Work.ASM.false_of_cyclic_sylow_two` in
`Submission/Work/ASM/CyclicSylow.lean`; import it).  Hence, by `BenderCtx.sylow`, `S` is
dihedral of order `2n` with `n ≥ 2`. -/
theorem SylowDihedral (G : Type) [Group G] [Finite G] (h : BenderCtx G) (B : BenderSetup G) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
  haveI : IsSimpleGroup G := h.simple
  -- Feit–Thompson, in the vocabulary of the development.
  have hFT : FeitThompsonProp := Work.GW2.feitThompsonProp
  -- A cyclic Sylow 2-subgroup is impossible in a non-abelian finite simple group.
  have hnotcyc : ¬ IsCyclic ↥(B.S : Subgroup G) := fun hc =>
    Work.ASM.false_of_cyclic_sylow_two h.nonab hFT B.S hc
  rcases h.sylow B.S with hcyc | ⟨n, ⟨e⟩⟩
  · exact (hnotcyc hcyc).elim
  · refine ⟨n, ?_, ⟨e⟩⟩
    -- `n ≠ 1`, since `DihedralGroup 1` is cyclic and `↥B.S` is not.
    have hn1 : n ≠ 1 := by
      intro h1
      exact hnotcyc (e.isCyclic.mpr ((DihedralGroup.isCyclic_iff (n := n)).mpr h1))
    -- `n ≠ 0`, since `DihedralGroup 0` is infinite while `↥B.S` is finite.
    have hn0 : n ≠ 0 := by
      intro h0
      have hfin : Finite (DihedralGroup n) :=
        Finite.of_injective (e.symm : DihedralGroup n → ↥(B.S : Subgroup G)) e.symm.injective
      rw [h0] at hfin
      exact Infinite.not_finite hfin
    omega

end Work.CORE3
