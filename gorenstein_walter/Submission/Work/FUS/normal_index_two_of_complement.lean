import Mathlib
import Submission.Work.Dihedral.Defs
import Submission.Work.FUS.Dihedral

set_option linter.style.haveILetI false

namespace Work.FUS

/-- The reflection sign `DihedralGroup n →* Multiplicative (ZMod 2)` is surjective. -/
lemma reflSign_surjective (n : ℕ) : Function.Surjective (reflSign n) := by
  intro y
  rcases mulTwo_eq_one_or y with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨DihedralGroup.sr 0, reflSign_sr n 0⟩

/-- The rotation subgroup `⟨r⟩` has index `2` in the dihedral group. -/
lemma rot_index_two (n : ℕ) : (Work.Dihedral.rot n).index = 2 := by
  rw [← ker_reflSign n, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (reflSign_surjective n)]
  rw [Nat.card_congr (Subgroup.topEquiv (G := Multiplicative (ZMod 2))).toEquiv]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem normal_index_two_of_complement {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) (hN : N.Normal) (S : Sylow 2 G) (n : ℕ) (hn : 2 ≤ n)
    (hiso : Nonempty ((S : Subgroup G) ≃* DihedralGroup n))
    (hcompl : Subgroup.IsComplement' N (S : Subgroup G)) :
    ∃ M : Subgroup G, M.Normal ∧ M.index = 2 := by
  classical
  haveI : N.Normal := hN
  obtain ⟨g⟩ := hiso
  let e : G ⧸ N ≃* (S : Subgroup G) := (hcompl.symm).QuotientMulEquiv
  let φ : G →* DihedralGroup n :=
    g.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' N))
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨a, ha⟩ := g.surjective y
    obtain ⟨b, hb⟩ := e.surjective a
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective N b
    exact ⟨c, by
      show g (e (QuotientGroup.mk' N c)) = y
      rw [hc, hb, ha]⟩
  exact ⟨(Work.Dihedral.rot n).comap φ, (Work.Dihedral.rot_normal n).comap φ, by
    have hidx := Subgroup.index_comap_of_surjective (H := Work.Dihedral.rot n) (f := φ) hφ
    rw [hidx, rot_index_two n]⟩

end Work.FUS
