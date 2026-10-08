import Submission.Work.ZJB.Step1.Defs

/-!
# ZJB — Theorem 5.1, step (I): the assembly

`step1_of_leaves` is copied from the lead's design file `_design_gw/Core11ZJB.lean` §2c (the
companion of `NOTES_LEAD_gw_design11.md` §3.2), where it is proved.  It reduces step (I) of
Theorem 5.1 to the leaves F0, F2, F3, F4, L51, I.0, I.3–I.6, I.7a, I.7b, I.8; F1, I.1 and I.2
feed I.3 and I.8.

See `Submission/Work/ZJB/Step1/` for the individual leaves.
-/

namespace Work.ZJB

open Work.GW2
open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The assembly of (I) (Theorem 5.1, pp. 1117–1119, hypothesis (a)). -/
theorem step1_of_leaves
    (f0 : ZSLeZJProp G) (f2 : CardSylowInProp p G)
    (f3 : SylowOfNormalizerProp p G) (f4 : NormJLeNormZJProp G) (l51 : CpStarInOfCpInProp p G)
    (i0 : ExistsMaxBadProp p G) (i3 : ExistsAProp p G) (i4 : ExistsT1Prop p G)
    (i5 : DMemProp p G) (i6 : ExistsMaxHProp p G) (i7a : StepNProp p G) (i7b : ZJTMemProp p G)
    (i8 : FinalProp p G) : Step1Prop p G := by
  intro hA S g hgS
  by_contra hcon
  by_cases hS : (S : Subgroup G) = ⊥
  · apply hcon
    have hZ : ZS (S : Subgroup G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx2 : x ∈ (S : Subgroup G) := (Subgroup.mem_inf.mp hx).2
      rwa [hS] at hx2
    rw [hZ, pconj, Subgroup.map_bot]
    exact bot_le
  obtain ⟨S₁, hMB⟩ := i0 S g hgS hcon
  obtain ⟨hZ1, a, haND, ha⟩ := i3 S S₁ hMB
  obtain ⟨T₁, hT₁, hDT₁, hcT₁⟩ := i4 S S₁ hMB
  have hDmem := i5 S S₁ hS hMB hZ1 a haND T₁ hT₁ hDT₁ hcT₁
  obtain ⟨H, hH, hHmax⟩ := i6 S _ a hDmem
  have hH' := hH
  obtain ⟨_hHne, ⟨T, g', hg'N, hT, hZT, hZg', hZaT, hcT⟩, S₂, hZS₂, hHS₂⟩ := hH'
  have hCp := hA S₂ H hZS₂ hHS₂
  obtain ⟨n, hnN, hZn⟩ := i7a S H T g' a hCp hT hg'N hZT hZg' hZaT hS
  have hnZJ : n ∈ normalizer (ZJ T : Set G) := (Subgroup.mem_inf.mp hnN).2
  have hZJTmem := i7b S _ H T a n hH hT hZT hZaT hcT hnZJ hZn
  have hnu1 := hHmax _ hZJTmem
  have hcardT := f2 T _ hT
  have hnu2 : nuP p (normalizer (T : Set G)) ≤ nuP p (normalizer (ZJ T : Set G)) := by
    unfold nuP
    have hdvd : Nat.card ↥(normalizer (T : Set G)) ∣ Nat.card ↥(normalizer (ZJ T : Set G)) :=
      Subgroup.card_dvd_of_le (normalizer_le_normalizer_ZJ T)
    exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd p
  obtain ⟨T', hT'⟩ := f3 T hT.2.1 (by
    rw [hcardT]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (hnu2.trans hnu1))
  have hgood : ZS (S : Subgroup G) ≤ ZJ (T' : Subgroup G) :=
    hMB.2.2 T' (hT' ▸ hZT) (by unfold Dsub; rw [hT']; exact hcT)
  have hstar := l51 _ (hA S (ZS (S : Subgroup G)) le_rfl inf_le_right)
  have hZD : ZS (S : Subgroup G) ≤ Dsub S S₁ := by
    refine le_inf ?_ hMB.1
    exact ((f0 _).trans inf_le_left).trans (Subgroup.le_normalizer)
  have hZaD : pconj (ZS (S : Subgroup G)) a ≤ Dsub S S₁ := by
    rintro y ⟨x, hx, rfl⟩
    have hainv : a⁻¹ ∈ normalizer (Dsub S S₁ : Set G) :=
      inv_mem (Subgroup.mem_inf.mp haND).1
    exact (Subgroup.mem_normalizer_iff.mp hainv x).1 (hZD hx)
  have hZaN : pconj (ZS (S : Subgroup G)) a ≤ normalizer (ZJ (S : Subgroup G) : Set G) :=
    hZaD.trans (inf_le_left.trans (f4 _))
  exact ha (i8 S T' a n hstar hgood (hT' ▸ hnZJ) hZn hZaN)

end Work.ZJB
