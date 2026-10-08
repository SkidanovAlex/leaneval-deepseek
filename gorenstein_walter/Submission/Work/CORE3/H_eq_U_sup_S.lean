import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.ASM.CyclicSylow

namespace Work.CORE3

namespace Work.CORE3

open Work.GW2

/-- Bender 1981 §2 (p. 219): `H = SU`, i.e. `C_G(t) = O(C_G(t)) · S`, for `t` the central
involution of the Sylow 2-subgroup.  This is `CentralizerSplitProp` of the toolkit (`T.split`)
applied to `B.S`, using `B.S ≤ C_G(t)` (`Work.CORE2A.bSetup_S_le_H`) and `S` dihedral
(`Work.CORE3.SylowDihedral`, or the short argument: a cyclic Sylow 2 is impossible here). -/
theorem H_eq_U_sup_S (G : Type) [Group G] [Finite G] (T : LocalToolkit) (h : BenderCtx G)
    (B : BenderSetup G) : B.U ⊔ (B.S : Subgroup G) = B.H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup G := h.simple
  -- The Sylow 2-subgroup of a non-abelian finite simple group is not cyclic.
  have hnc : ¬ IsCyclic ↥(B.S : Subgroup G) :=
    fun hc => Work.ASM.false_of_cyclic_sylow_two h.nonab T.ft B.S hc
  -- Hence, by `DihOrCycSylow`, it is dihedral of order `2n` with `n ≥ 2`.
  obtain ⟨n, hn2, hdih⟩ :
      ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥(B.S : Subgroup G) ≃* DihedralGroup n) := by
    rcases h.sylow B.S with hcyc | ⟨n, hn⟩
    · exact absurd hcyc hnc
    · obtain ⟨e⟩ := hn
      refine ⟨n, ?_, ⟨e⟩⟩
      -- `|S| = 2n` and `|S| = 2 ^ k` (`S` is a 2-group); `S` not cyclic forces `n ≥ 2`.
      have hcard : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      have hncD : ¬ IsCyclic (DihedralGroup n) := fun hc => hnc (e.isCyclic.mpr hc)
      have hn1 : n ≠ 1 := fun h1 => hncD ((DihedralGroup.isCyclic_iff (n := n)).mpr h1)
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp B.S.isPGroup'
      have h2n : 2 * n = 2 ^ k := by rw [← hcard, hk]
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
  -- Apply the toolkit's centralizer splitting theorem.
  refine T.split G B.S n hn2 hdih B.t (Work.CORE2A.bSetup_t_mem_S B) B.t_order ?_
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_S_le_H B hx) B.t (by simp)).symm

end Work.CORE3

open Work.GW2

/-- The same lemma, stated at the namespace of the file path, so that it can be cited both as
`Work.CORE3.H_eq_U_sup_S` (the name the area requests) and as
`Work.CORE3.Work.CORE3.H_eq_U_sup_S` (the skeleton's namespace layout). -/
theorem H_eq_U_sup_S (G : Type) [Group G] [Finite G] (T : LocalToolkit) (h : BenderCtx G)
    (B : BenderSetup G) : B.U ⊔ (B.S : Subgroup G) = B.H :=
  _root_.Work.CORE3.Work.CORE3.H_eq_U_sup_S G T h B

end Work.CORE3
