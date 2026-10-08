import Mathlib
import Submission.Work.ZJB.Defs
import Submission.Work.ZJB.ZJBasic

namespace Work.ZJB.ZJApi

/-!
# `Z(J(P)) ≠ 1` for a nontrivial `p`-subgroup `P`

For a nontrivial finite `p`-subgroup `P` of a finite group `G`, Thompson's subgroup `J(P)`
(the join of the abelian subgroups of `P` of maximal order) is nontrivial and is again a
`p`-group, so its centre `Z(J(P)) = J(P) ∩ C_G(J(P)) = ZJ P` is nontrivial: a nontrivial
finite `p`-group has a nontrivial centre.

The only non-formal input is that `J(P)` contains `Z(P)`: the centre `C_G(P) ∩ P` of `P` is
abelian, hence lies in an abelian subgroup of `P` of maximal order
(`Subgroup.centralizer_inf_le_of_mem_maxAbelianIn`, Gorenstein Lemma 8.2.1), and every such
subgroup lies in the join `J(P)` (`Work.GW2.le_thompsonJ_of_mem_maxAbelianIn`).
-/

/-- **The centre of a nontrivial finite `p`-subgroup is nontrivial.**  In the ambient-group
encoding `Z(P) = C_G(P) ∩ P`.  The proof passes to the group `↥P` and uses Mathlib's
`IsPGroup.center_nontrivial`. -/
theorem centralizer_inf_ne_bot_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P) (hPbot : P ≠ ⊥) :
    Subgroup.centralizer (P : Set G) ⊓ P ≠ ⊥ := by
  intro hbot
  have hntP : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPbot
  have hfinP : Finite ↥P := Finite.of_injective (Subtype.val : ↥P → G) Subtype.val_injective
  have hntZ : Nontrivial ↥(Subgroup.center ↥P) := hP.center_nontrivial
  obtain ⟨z, hzn⟩ := exists_ne (1 : Subgroup.center ↥P)
  have hcomm : ∀ g : ↥P, g * (z : ↥P) = (z : ↥P) * g := Subgroup.mem_center_iff.mp z.2
  have hzcent : ((z : ↥P) : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun w : ↥P => (w : G)) (hcomm ⟨y, hy⟩)
    simpa using h
  have hmem : ((z : ↥P) : G) ∈ Subgroup.centralizer (P : Set G) ⊓ P :=
    ⟨hzcent, (z : ↥P).2⟩
  rw [hbot] at hmem
  exact hzn (Subtype.ext (Subtype.ext (by simpa using Subgroup.mem_bot.mp hmem)))

/-- `Z(J(P))` is nontrivial for a nontrivial finite `p`-subgroup `P`: `J(P)` is a nontrivial
`p`-group (it contains `Z(P) ≠ ⊥`), so its centre `Z(J(P)) = J(P) ∩ C_G(J(P))` is nontrivial.
The bridge to the centre of the group `↥(thompsonJ P)` is
`(Subgroup.center ↥(Work.GW2.thompsonJ P)).map (Work.GW2.thompsonJ P).subtype
  = Work.GW2.ZJ P`. -/
theorem ZJ_ne_bot {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) (hbot : P ≠ ⊥) : Work.GW2.ZJ P ≠ ⊥ := by
  -- `Z(P) ≠ 1`
  have hZP : Subgroup.centralizer (P : Set G) ⊓ P ≠ ⊥ :=
    centralizer_inf_ne_bot_of_isPGroup hP hbot
  -- `Z(P) ≤ J(P)`, so `J(P) ≠ 1`
  obtain ⟨A, hA⟩ := Subgroup.maxAbelianIn_nonempty P
  have hle : Subgroup.centralizer (P : Set G) ⊓ P ≤ Work.GW2.thompsonJ P :=
    (Subgroup.centralizer_inf_le_of_mem_maxAbelianIn hA).trans
      (Work.GW2.le_thompsonJ_of_mem_maxAbelianIn hA)
  have hJne : Work.GW2.thompsonJ P ≠ ⊥ := by
    intro hJbot
    exact hZP (le_bot_iff.mp (hJbot ▸ hle))
  -- `J(P)` is a nontrivial `p`-group, so `Z(J(P)) ≠ 1`
  have hJP : IsPGroup p (Work.GW2.thompsonJ P) := hP.to_le (Work.GW2.thompsonJ_le P)
  have hZJ : Subgroup.centralizer ((Work.GW2.thompsonJ P : Subgroup G) : Set G)
      ⊓ Work.GW2.thompsonJ P ≠ ⊥ := centralizer_inf_ne_bot_of_isPGroup hJP hJne
  simpa [Work.GW2.ZJ, inf_comm] using hZJ

end Work.ZJB.ZJApi
