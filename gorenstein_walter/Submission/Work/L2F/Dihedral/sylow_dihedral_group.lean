import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.Dihedral.Defs
import Submission.Work.L2F.Dihedral.dihedral_recognition

set_option linter.style.haveILetI false

namespace Work.L2F.Dihedral

/-- Sylow 2-subgroups of a dihedral group are dihedral.  Proof: write `m = 2^a * b` with `b` odd
(and `m ≠ 0`); `P ∩ ⟨r⟩` is a subgroup of the cyclic group `⟨r⟩` of order `2^a` (`|P| = 2^(a+1)`
and `P ∩ ⟨r⟩` has index at most `2` in `P`), so it is the unique subgroup `⟨r^b⟩` of order `2^a`;
picking `s ∈ P \ ⟨r⟩` (a reflection, `s² = 1`) gives `P = ⟨r^b⟩ ⋊ ⟨s⟩` with `s r^b s = r^(-b)`, so
`P ≃* DihedralGroup (2^a)` by the cyclic-index-two criterion (prove that step inline: `r b` generates
the cyclic group of order `2^a` in `P` and `s ∉ ⟨r^b⟩` inverts it while `s² = 1`). -/
theorem sylow_dihedral_group (m : ℕ) (hm : m ≠ 0) (P : Sylow 2 (DihedralGroup m)) :
    ∃ n : ℕ, Nat.card P = 2 * n ∧
      Nonempty ((P : Subgroup (DihedralGroup m)) ≃* DihedralGroup n) := by
  classical
  haveI : NeZero m := ⟨hm⟩
  haveI : Finite (DihedralGroup m) := inferInstance
  by_cases hle : (P : Subgroup (DihedralGroup m)) ≤ Work.Dihedral.rot m
  · -- impossible: a Sylow `2`-subgroup cannot sit inside the cyclic rotation subgroup
    exfalso
    have hrot2 : (Work.Dihedral.rot m).index = 2 := by
      have h1 := Subgroup.index_mul_card (Work.Dihedral.rot m)
      rw [Work.Dihedral.nat_card_rot, DihedralGroup.nat_card] at h1
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hm) h1
    have hdvd : 2 ∣ (P : Subgroup (DihedralGroup m)).index := by
      rw [← Subgroup.relIndex_mul_index hle, hrot2]
      exact ⟨_, mul_comm _ 2⟩
    exact P.not_dvd_index hdvd
  · rw [IsConcreteLE.le_iff] at hle
    push Not at hle
    obtain ⟨s0, hs0S, hs0R⟩ := hle
    obtain ⟨i, hi⟩ := Work.Dihedral.notMem_rot.mp hs0R
    let S : Subgroup (DihedralGroup m) := (P : Subgroup (DihedralGroup m))
    haveI : Finite ↥S := Subtype.finite
    let s : ↥S := ⟨DihedralGroup.sr i, by rw [← hi]; exact hs0S⟩
    let K : Subgroup ↥S := (Work.Dihedral.rot m).subgroupOf S
    have hKcyc : IsCyclic ↥K := by
      let f : ↥K →* ↥(Work.Dihedral.rot m) :=
        { toFun := fun x => ⟨(x : ↥S), x.2⟩
          map_one' := Subtype.ext rfl
          map_mul' := fun a b => Subtype.ext rfl }
      refine isCyclic_of_injective f (fun a b h => ?_)
      have h1 : ((a : ↥S) : DihedralGroup m) = ((b : ↥S) : DihedralGroup m) :=
        congrArg (fun y : ↥(Work.Dihedral.rot m) => (y : DihedralGroup m)) h
      exact Subtype.ext (Subtype.ext h1)
    haveI : IsCyclic ↥K := hKcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥K)
    have hg' : Subgroup.zpowers g = ⊤ := (Subgroup.eq_top_iff' _).mpr hg
    have hsG : (s : DihedralGroup m) = DihedralGroup.sr i := rfl
    have hs2 : s ^ 2 = 1 := by
      apply Subtype.ext
      simp [Subgroup.coe_mul, hsG, pow_two, DihedralGroup.sr_mul_sr]
    have hsK : s ∉ K := by
      intro h
      have h2 := Subgroup.mem_subgroupOf.mp h
      simp [hsG] at h2
    have hgrot : ((g : ↥S) : DihedralGroup m) ∈ Work.Dihedral.rot m :=
      Subgroup.mem_subgroupOf.mp g.2
    obtain ⟨a, ha⟩ := Work.Dihedral.mem_rot.mp hgrot
    have hconjG :
        (s : DihedralGroup m) * ((g : ↥S) : DihedralGroup m) * (s : DihedralGroup m)⁻¹ =
          (((g : ↥S) : DihedralGroup m))⁻¹ := by
      rw [hsG, ha, DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
        DihedralGroup.inv_r]
      congr 1
      ring
    have hconj : s * (g : ↥S) * s⁻¹ = (g : ↥S)⁻¹ := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconjG
    have hcover : ∀ x : ↥S, x ∈ K ∨ x * s ∈ K := by
      intro x
      by_cases hx : (x : DihedralGroup m) ∈ Work.Dihedral.rot m
      · exact Or.inl (Subgroup.mem_subgroupOf.mpr hx)
      · refine Or.inr (Subgroup.mem_subgroupOf.mpr ?_)
        obtain ⟨j, hj⟩ := Work.Dihedral.notMem_rot.mp hx
        have hxs : ((x * s : ↥S) : DihedralGroup m) = DihedralGroup.r (i - j) := by
          rw [Subgroup.coe_mul, hj, hsG, DihedralGroup.sr_mul_sr]
        rw [hxs]
        exact Work.Dihedral.r_mem_rot _
    obtain ⟨e⟩ := dihedral_recognition K g hg' s hs2 hsK hconj hcover
    refine ⟨Nat.card K, ?_, ?_⟩
    · have hcard : Nat.card ↥S = Nat.card (DihedralGroup (Nat.card K)) :=
        Nat.card_congr e.toEquiv
      rw [DihedralGroup.nat_card] at hcard
      exact hcard
    · exact ⟨e⟩

end Work.L2F.Dihedral
