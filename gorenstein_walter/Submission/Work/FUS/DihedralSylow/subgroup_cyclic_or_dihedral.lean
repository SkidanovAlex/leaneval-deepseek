import Mathlib
import Submission.Work.RED.DihedralSubgroup

namespace Work.FUS.DihedralSylow

/-- **Every `2`-subgroup of a finite group with dihedral Sylow `2`-subgroups is cyclic or
dihedral.**

Let `U` be a finite group whose Sylow `2`-subgroup `S` is isomorphic to the dihedral group
`DihedralGroup n` with `n ≥ 2`, and let `X ≤ U` be a `2`-subgroup.  Then `X` is cyclic, or
`X` is isomorphic to `DihedralGroup m` for some `m ≥ 2`.

The proof is the classical one: `X` lies in some Sylow `2`-subgroup `P` of `U` (Sylow's first
theorem), and `P ≅ S ≅ DihedralGroup n` (Sylow's second theorem).  Pushing `X` into
`DihedralGroup n`, the classification of subgroups of a dihedral group
(`Work.RED.DihedralSubgroup`) gives the dichotomy; the parameter `m ≥ 2` is automatic because
`DihedralGroup m` with `m ≤ 1` is (at most) of order `2`, hence cyclic. -/
theorem subgroup_cyclic_or_dihedral {U : Type*} [Group U] [Finite U]
    (S : Sylow 2 U) (n : ℕ) (hn : 2 ≤ n)
    (hiso : Nonempty ((S : Subgroup U) ≃* DihedralGroup n))
    (X : Subgroup U) (hX : IsPGroup 2 X) :
    IsCyclic ↥X ∨ ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥X ≃* DihedralGroup m) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Sylow's first theorem: the `2`-subgroup `X` lies in a Sylow `2`-subgroup `P`.
  obtain ⟨P, hPle⟩ := hX.exists_le_sylow
  -- Sylow's second theorem: all Sylow `2`-subgroups are conjugate, hence isomorphic,
  -- so `P ≅ S ≅ DihedralGroup n`.
  obtain ⟨eS⟩ := hiso
  let e : ↥(P : Subgroup U) ≃* DihedralGroup n := (Sylow.equiv P S).trans eS
  -- `X` viewed inside `P`, and its image `H ≤ DihedralGroup n`.
  let XP : Subgroup ↥(P : Subgroup U) := X.subgroupOf P
  let H : Subgroup (DihedralGroup n) := XP.map e.toMonoidHom
  have hXP : ↥X ≃* ↥H :=
    (Subgroup.subgroupOfEquivOfLe hPle).symm.trans
      (Subgroup.equivMapOfInjective XP e.toMonoidHom e.injective)
  haveI : NeZero n := ⟨by omega⟩
  -- The classification of subgroups of a dihedral group.
  rcases Work.RED.DihedralSubgroup n H with hcyc | ⟨m, ⟨em⟩⟩
  · exact Or.inl ((MulEquiv.isCyclic hXP).mpr hcyc)
  · -- `X ≅ DihedralGroup m`.  Either `m ≥ 2`, or `m ≤ 1` and `X` is cyclic.
    by_cases hm : 2 ≤ m
    · exact Or.inr ⟨m, hm, ⟨hXP.trans em⟩⟩
    · refine Or.inl ?_
      -- `|X| = 2 * m`, and `|X| > 0`, so `m = 1`, whence `DihedralGroup m` is cyclic.
      have hcard : Nat.card ↥X = 2 * m := by
        rw [Nat.card_congr (hXP.trans em).toEquiv, DihedralGroup.nat_card]
      have hpos : 0 < Nat.card ↥X := by
        haveI : Nonempty ↥X := ⟨⟨1, X.one_mem⟩⟩
        exact Nat.card_pos
      have hm1 : m = 1 := by omega
      haveI : IsCyclic (DihedralGroup m) := by
        rw [hm1]; exact DihedralGroup.isCyclic_iff.mpr rfl
      exact (MulEquiv.isCyclic (hXP.trans em)).mpr inferInstance

end Work.FUS.DihedralSylow
