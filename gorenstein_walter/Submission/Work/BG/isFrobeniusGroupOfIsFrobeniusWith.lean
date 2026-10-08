import Mathlib
import Submission.Work.BG.c3FrobWithImports

namespace Work.BG

/-
`Work.GW2.IsFrobeniusWith BF F B` says, in the ambient group `G`, that

* `F ≤ BF`, `F ◁ BF` (i.e. `(F.subgroupOf BF).Normal`),
* `B ⊔ F = BF` and `B ⊓ F = ⊥`  (`BF = F ⋊ B`),
* `F ≠ ⊥`, `B ≠ ⊥`,
* every `1 ≠ b ∈ B` acts fixed point freely on `F` (`F ⊓ C_G(b) = ⊥`).

The lemma below repackages exactly this as Isaacs' subgroup-pair form of a Frobenius
group, `OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥BF (F.subgroupOf BF) (B.subgroupOf BF)`,
i.e. Isaacs FGT Thm 6.4 condition (1) inside the group `↥BF`:
`(F.subgroupOf BF)` is normal and complemented by `(B.subgroupOf BF)`, and conjugation
by a nontrivial element of the complement is fixed point free on the kernel.

The only non-formal content is transporting the ambient data into the subgroup `↥BF`
(`·.subgroupOf` does not preserve `⊔` in general, but along an inclusion it does:
`Subgroup.subgroupOf_sup` applies here because both pieces lie in `BF`), then verifying
complementarity from `⊔ = ⊤` and `⊓ = ⊥` using normality
(`Subgroup.normal_mul`, `Subgroup.isComplement'_of_disjoint_and_mul_eq_univ`).
-/
theorem isFrobeniusGroupOfIsFrobeniusWith {G : Type} [Group G] (BF F B : Subgroup G)
    (h : Work.GW2.IsFrobeniusWith BF F B) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥BF (F.subgroupOf BF) (B.subgroupOf BF) := by
  obtain ⟨hFle, hFnorm, hsup, hdisj, hFne, hBne, hfixed⟩ := h
  -- `B ≤ BF` since `BF = B ⊔ F`.
  have hBle : B ≤ BF := by rw [← hsup]; exact le_sup_left
  refine ⟨hFnorm, ?_, ?_, ?_, ?_⟩
  · -- `F.subgroupOf BF` and `B.subgroupOf BF` are complements in `↥BF`.
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · -- disjointness, transported from `F ⊓ B = ⊥` in `G`
      rw [disjoint_iff]
      refine eq_bot_iff.mpr fun x hx => ?_
      rw [Subgroup.mem_inf] at hx
      simp only [Subgroup.mem_subgroupOf] at hx
      have hmem : (x : G) ∈ F ⊓ B := ⟨hx.1, hx.2⟩
      rw [show F ⊓ B = ⊥ from by rw [inf_comm]; exact hdisj, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      exact Subtype.ext (by simpa using hmem)
    · -- `⊔ = ⊤`: both pieces lie in `BF`, so `subgroupOf` commutes with `⊔` here
      have hsup' : (F.subgroupOf BF : Subgroup ↥BF) ⊔ (B.subgroupOf BF) = ⊤ := by
        have hFB : F ⊔ B = BF := by rw [sup_comm]; exact hsup
        rw [← Subgroup.subgroupOf_sup hFle hBle, hFB, Subgroup.subgroupOf_self]
      -- normality makes the set product the whole of `↥BF`
      have hmul := @Subgroup.normal_mul (↥BF) _ (F.subgroupOf BF) (B.subgroupOf BF) hFnorm
      rw [hsup', Subgroup.coe_top] at hmul
      exact hmul.symm
  · -- nontriviality of the kernel, transported from `F ≠ ⊥`
    intro hbot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    have h2 : F ⊓ BF = ⊥ := disjoint_iff.mp hbot
    rw [inf_eq_left.mpr hFle] at h2
    exact hFne h2
  · -- nontriviality of the complement, transported from `B ≠ ⊥`
    intro hbot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    have h2 : B ⊓ BF = ⊥ := disjoint_iff.mp hbot
    rw [inf_eq_left.mpr hBle] at h2
    exact hBne h2
  · -- fixed point freeness of the conjugation action of the complement on the kernel
    intro a ha ha1 n hn hn1 hconj
    have haG : (a : G) ∈ B := ha
    have hnG : (n : G) ∈ F := hn
    have ha_ne : (a : G) ≠ 1 := fun hh => ha1 (Subtype.ext hh)
    have hn_ne : (n : G) ≠ 1 := fun hh => hn1 (Subtype.ext hh)
    -- the equation in `↥BF` reads the same in `G`
    have hconjG : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      have := congrArg (fun x : ↥BF => (x : G)) hconj
      simpa using this
    -- hence `(n : G)` commutes with `(a : G)`
    have hcomm : (n : G) * (a : G) = (a : G) * (n : G) := by
      have h1 : (a : G) * (n : G) = (n : G) * (a : G) := by
        have := congrArg (· * (a : G)) hconjG
        simpa [mul_assoc] using this
      exact h1.symm
    -- so `(n : G) ∈ F ⊓ C_G(a) = ⊥`, contradicting `n ≠ 1`
    have hfx := hfixed (a : G) haG ha_ne
    have hmem : (n : G) ∈ F ⊓ Subgroup.centralizer ({(a : G)} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hnG, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    rw [hfx, Subgroup.mem_bot] at hmem
    exact hn_ne hmem

end Work.BG
