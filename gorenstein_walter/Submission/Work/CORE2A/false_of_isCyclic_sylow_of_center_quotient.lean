import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.sylow_two_dihedral_of_quotient

/-!
# CORE2A: a central extension by an odd-order centre with `A₇`/`L₂(q)` quotient

Let `Y` be a finite group with a **cyclic** Sylow 2-subgroup and odd-order centre, and
suppose that `Y ⧸ Z(Y)` is either `A₇` or `PSL(2, q)` with `q = p ^ k` odd, `q ≥ 5`.
Then `False`.

The two hypotheses are incompatible.  By `Work.CORE2A.sylow_two_dihedral_of_quotient`
(the reduction to the quotient: an odd-order central subgroup meets a Sylow 2-subgroup
trivially, so a Sylow 2-subgroup of `Y` embeds into `Y ⧸ Z(Y)`, where the model facts
`A7ModelProp`/`L2SylowDihedralProp` show that its Sylow 2-subgroups are *dihedral*),
every Sylow 2-subgroup of `Y` is isomorphic to `DihedralGroup n` with `n ≥ 2`.  But the
given Sylow 2-subgroup is cyclic, so `DihedralGroup n` would be cyclic — impossible for
`n ≠ 1` (`DihedralGroup.not_isCyclic`). -/

namespace Work.CORE2A

theorem false_of_isCyclic_sylow_of_center_quotient {Y : Type} [Group Y] [Finite Y]
    (T : Work.GW2.LocalToolkit)
    (hcyc : ∃ Q : Sylow 2 Y, IsCyclic ↥(Q : Subgroup Y))
    (hodd : Odd (Nat.card (Subgroup.center Y)))
    (hshape : Nonempty ((Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin 7)) ∨
      ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        Nonempty ((Y ⧸ Subgroup.center Y) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) :
    False := by
  -- A cyclic Sylow 2-subgroup, whose existence is `hcyc`.
  obtain ⟨Q, hQcyc⟩ := hcyc
  -- The quotient reduction: every Sylow 2-subgroup of `Y` is dihedral of order `≥ 4`.
  obtain ⟨n, hn2, ⟨e⟩⟩ := sylow_two_dihedral_of_quotient T.a7 T.l2syl hodd hshape Q
  -- Transport cyclicity across the isomorphism and contradict `DihedralGroup.not_isCyclic`.
  exact DihedralGroup.not_isCyclic (n := n) (by omega) ((MulEquiv.isCyclic e).mp hQcyc)

end Work.CORE2A
