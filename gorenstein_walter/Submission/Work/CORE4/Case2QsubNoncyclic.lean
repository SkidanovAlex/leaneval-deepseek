import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.API
import Submission.Work.CORE4Qsub.A_le_pCoreInU
import Submission.Work.CORE4Qsub.normal_elementaryAbelian_le_z2
import Submission.OddOrder.BG.Ch1_Preliminary.S04_SmallRankBasic

namespace Work.CORE4

open Subgroup

section Helpers

variable {G : Type} [Group G] [Finite G]

/-- A subgroup of order `p ^ 2` all of whose elements have `p`-th power `1` (with `p` prime) is
not cyclic: a generator `g` would have `orderOf g = p ^ 2` while `g ^ p = 1` gives
`orderOf g ∣ p`. -/
theorem not_isCyclic_of_card_eq_prime_sq_exp {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hcard : Nat.card ↥E = p ^ 2) (hexp : ∀ x ∈ E, x ^ p = 1) : ¬ IsCyclic ↥E := by
  intro hcyc
  haveI := hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E)
  have hdvd : orderOf g ∣ p :=
    orderOf_dvd_iff_pow_eq_one.mpr (Subtype.ext (by simpa using hexp (g : G) g.2))
  rw [hg, hcard] at hdvd
  have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hdvd
  nlinarith [hp.two_le]

/-- A non-cyclic finite `p`-group (`p` odd) has a normal elementary abelian subgroup of order
`p ^ 2` (BG Lemma 4.5(a), available in the `OddOrder` development as
`OddOrder.BG.Ch1.S04.exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic`), pushed
into the ambient group. -/
theorem exists_normal_elementaryAbelian_le {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    {P : Subgroup G} (hPp : IsPGroup p ↥P) (hPnc : ¬ IsCyclic ↥P) :
    ∃ E : Subgroup G, E ≤ P ∧ (E.subgroupOf P).Normal ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ p = 1) ∧ Nat.card ↥E = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hBn, hBea, hBcard⟩ :=
    OddOrder.BG.Ch1.S04.exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic
      (R := ↥P) hPp hpodd hPnc
  have hEea : (B.map P.subtype).IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.map P.subtype_injective hBea
  refine ⟨B.map P.subtype, Subgroup.map_subtype_le B, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_subtype_le B)]
    intro x y hx hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr
      ⟨(⟨y, hy⟩ : ↥P) * z * (⟨y, hy⟩ : ↥P)⁻¹, hBn.conj_mem z hz ⟨y, hy⟩, rfl⟩
  · intro x hx y hy
    simpa using congrArg Subtype.val (hEea.1 ⟨x, hx⟩ ⟨y, hy⟩)
  · intro x hx
    simpa using congrArg Subtype.val (hEea.2 ⟨x, hx⟩)
  · rw [Subgroup.card_map_of_injective P.subtype_injective, hBcard]

end Helpers

/-- **Bender 1981, §4 (8).**  With `Q := Ω₁(Z₂(O_p(U)))` (`Qsub`), `Q` is not cyclic whenever the
`(p,p)`-subgroup `A ≤ F ⊔ K` of §4 (8) exists: `A` is an elementary abelian subgroup of order
`p ^ 2` of `O_p(U)` (`A_le_pCoreInU`), so `O_p(U)` is not cyclic; BG Lemma 4.5(a) then supplies a
*normal* elementary abelian `E ≤ O_p(U)` of order `p ^ 2`; a normal elementary abelian
`p ^ 2`-subgroup of a `p`-group lies in its second centre (`normal_elementaryAbelian_le_z2`), hence
`E ≤ Ω₁(Z₂(O_p(U))) = Q`, and `E ≅ C_p × C_p` is not cyclic. -/
theorem Case2QsubNoncyclic (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj C.D p P A →
          ¬ IsCyclic ↥(Work.CORE4.Qsub p B) := by
  intro G _ _ hbc B h2 C hplus h7 p P A hp hPF hPcard hObj
  obtain ⟨hAle, hPnc, hpodd, hPpg⟩ :=
    CORE4Qsub.A_le_pCoreInU I G hbc B h2 C hplus h7 p P A hp hPF hPcard hObj
  obtain ⟨E, hEle, hEn, hEcomm, hEexp, hEcard⟩ :=
    exists_normal_elementaryAbelian_le (G := G) hp hpodd hPpg hPnc
  have hEz : E ≤ z2 (Work.GW2.pCoreIn p B.U) :=
    CORE4Qsub.normal_elementaryAbelian_le_z2 p hp hEle hEn hPpg hEcomm hEexp hEcard
  have hEQ : E ≤ Work.CORE4.Qsub p B := by
    intro x hx
    show x ∈ Subgroup.closure (omega1Set p (z2 (Work.GW2.pCoreIn p B.U)))
    exact Subgroup.subset_closure ⟨hEz hx, hEexp x hx⟩
  have hEnc : ¬ IsCyclic ↥E :=
    not_isCyclic_of_card_eq_prime_sq_exp (G := G) hp hEcard hEexp
  intro hcyc
  haveI := hcyc
  exact hEnc (Subgroup.isCyclic_of_le hEQ)

end Work.CORE4
