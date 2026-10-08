import Mathlib
import Submission.Work.L2F.Bridge
import Submission.Work.CORE4.L2PAux.v2_le_centralizer_cyclic_two
import Submission.Work.CORE4.L2PAux.v2_exists_four_of_noncyclic_two_subgroup_of_dihedral

/-!
# `Work.CORE4.L2PAux.twoSubgroup_le_centralizer_or_four_v2`

The `ℓ = 2` input of `L2pLocal`, in a clash-free form (no import of `Submission.Work.ASM.Defs`).

`G = PSL(2, q)`, `q = ρ ^ k` odd, `q ≥ 5`.  Sylow `2`-subgroups of `G` are dihedral
(`Work.L2F.l2SylowDihedral`), so a `2`-subgroup `P ≤ G` lies in a subgroup `S ≅ DihedralGroup n`.

* If `P` is **cyclic**, then `P` is a cyclic `2`-group and a `T ≤ N_G(P)` of odd order acts on
  `P` through `T → MulAut P`, whose image has order dividing both the odd number `|T|` and the
  `2`-power `|MulAut P| = φ(|P|)`; hence the action is trivial and `P ≤ C_G(T)`
  (`v2_le_centralizer_cyclic_two`).
* If `P` is **not cyclic**, a non-cyclic `2`-subgroup of a dihedral group contains a Klein
  four-subgroup (`v2_exists_four_of_noncyclic_two_subgroup_of_dihedral`, which transports the
  purely dihedral statement `v2_dihedral_two_subgroup_has_four` along `S ≃* DihedralGroup n`).
-/

namespace Work.CORE4.L2PAux

/-- Clash-free copy of the ℓ = 2 input of `L2pLocal` (same statement as
`Work.CORE4.L2PAux.twoSubgroup_le_centralizer_or_four`).  IMPORTANT: prove this WITHOUT
importing `Submission.Work.CORE2A.*` or `Submission.Work.FUS.*` or any other module that
transitively imports `Submission.Work.ASM.Defs` (do not just `exact` the existing v1 file: the
consumer `Submission/Work/CORE4/L2pLocal.lean` must also import `Submission.Work.CORE4.Defs27`,
and `Submission.Work.ASM.Defs` and `Submission.Work.CORE4.Defs` both define
`Work.GW2.BenderSetup`, so any module importing both fails to elaborate).  Safe imports:
Mathlib, `Submission.Work.L2F.Bridge` (gives `l2SylowDihedralProp`), `Submission.Work.L2F.Defs`,
`Submission.Work.Dihedral.Defs`, and your own new helper files (which must also avoid the
forbidden modules).

Route: `P` is a 2-subgroup, so it lies in a Sylow 2-subgroup `S`, which is dihedral
(`l2SylowDihedralProp`).  If `P` is cyclic of order `2^m`, `Aut P` is a 2-group while `T` has odd
order, so the conjugation map `T → Aut P` is trivial and `P ≤ C(T)`.  If `P` is not cyclic, take
a reflection `s ∈ P` (a non-cyclic subgroup of a dihedral group contains one) and the involution
`z` in `P ∩` (rotation part) (which has even order `≥ 2` because `P` is a 2-group with `|P| ≥ 4`);
then `⟨z, s⟩` is a four-group inside `P`. -/
theorem twoSubgroup_le_centralizer_or_four_v2 {ρ k : ℕ} [Fact ρ.Prime] (hρ : Odd ρ) (hk : 5 ≤ ρ ^ k)
    (P T : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ρ k)))
    (hP : IsPGroup 2 P) (hT : Odd (Nat.card T))
    (hTN : T ≤ Subgroup.normalizer (P : Set _)) :
    P ≤ Subgroup.centralizer (T : Set _) ∨
      ∃ V : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField ρ k)),
        V ≤ P ∧ Nat.card V = 4 ∧ ∀ v ∈ V, v ^ 2 = 1 := by
  by_cases hcyc : IsCyclic P
  · -- `P` cyclic: the odd-order `T ≤ N(P)` acts trivially on it.
    exact Or.inl (v2_le_centralizer_cyclic_two P T hcyc hP hTN hT)
  · -- `P` not cyclic: put it in a dihedral Sylow `2`-subgroup and find a four-group in it.
    obtain ⟨S, hPS⟩ := IsPGroup.exists_le_sylow hP
    obtain ⟨n, -, ⟨ψ⟩⟩ := Work.L2F.l2SylowDihedral ρ k hρ hk S
    exact Or.inr (v2_exists_four_of_noncyclic_two_subgroup_of_dihedral P (S : Subgroup _) hPS ψ hP hcyc)

end Work.CORE4.L2PAux
