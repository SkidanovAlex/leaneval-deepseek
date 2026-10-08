/-
# `Work.ThreePoints.ThmC.Defs` — vocabulary for the proof of Peterfalvi's Theorem C

Peterfalvi, *Le théorème de Bender–Suzuki I*, Astérisque 142–143 (1986), Chapter I
(pp. 147–162 + Appendices I–IV, pp. 199–210) and Chapter II §1–§3 (pp. 163–168).

Setting: `G` is a finite group, `H ≤ G` a **proper Bender group** (= `IsStronglyEmbedded H`),
`Ω = G ⧸ H` is the set of conjugates of `H`, on which `G` acts by left translation; for a
subgroup `X ≤ G`, `fixedPts H X` is the set of points of `Ω` fixed by `X` (so `X` fixes a point
`ω` iff `X ≤ MulAction.stabilizer G ω`, a conjugate of `H`), and `X` "fixes `≥ 3` points" when
`3 ≤ (fixedPts H X).ncard` (Peterfalvi writes `|Ω_X| ≥ 3`).

This file contains only definitions and elementary API; the numbered results of Chapters I–II
live in sibling modules of `Work.ThreePoints.ThmC`.
-/
import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.Omega
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.ThmC

open Submission.Blueprint
open Work.DoubleTransitivity

variable {G : Type} [Group G]

/-! ## 1. Maximal `p`-subgroups fixing three points (Peterfalvi I Ch. I §3) -/

/-- `P` is a `p`-subgroup of `G` **maximal among those fixing at least three points** of
`Ω = G ⧸ H` (Peterfalvi I Ch. I §3: "`P` maximal parmi les `p`-sous-groupes ayant au moins
3 points fixes"). -/
def IsMaxP3 (H : Subgroup G) (p : ℕ) (P : Subgroup G) : Prop :=
  IsPGroup p P ∧ 3 ≤ (fixedPts H P).ncard ∧
    ∀ R : Subgroup G, P ≤ R → IsPGroup p R → 3 ≤ (fixedPts H R).ncard → R = P

/-- `P` is a `p`-Sylow subgroup of the subgroup `D ≤ G`. -/
def IsSylowOf (p : ℕ) (P D : Subgroup G) : Prop :=
  P ≤ D ∧ IsPGroup p P ∧ ∀ Q : Subgroup G, P ≤ Q → Q ≤ D → IsPGroup p Q → Q = P

/-- `N_H(P) = N_G(P) ∩ H`, the normaliser of `P` inside the conjugate `H` of the Bender group. -/
abbrev normIn (H P : Subgroup G) : Subgroup G := Subgroup.normalizer (P : Set G) ⊓ H

/-- `O_{p'}(X)`, for a subgroup `X ≤ G`, as a subgroup of the ambient group `G`. -/
abbrev pPrimeCoreSub (p : ℕ) (X : Subgroup G) : Subgroup G :=
  (Submission.Blueprint.pPrimeCore p ↥X).map X.subtype

/-- `O_{2'}(X) = O(X)`, for a subgroup `X ≤ G`, as a subgroup of the ambient group `G`. -/
abbrev oddCoreSub (X : Subgroup G) : Subgroup G :=
  (Submission.Blueprint.oddCore ↥X).map X.subtype

/-! ## 2. Elementary API -/

theorem IsSylowOf.eq_of_le {p : ℕ} {P Q D : Subgroup G} (hP : IsSylowOf p P D)
    (hQ : IsSylowOf p Q D) (h : P ≤ Q) : P = Q :=
  (hP.2.2 Q h hQ.1 hQ.2.1).symm

theorem IsSylowOf.isPGroup {p : ℕ} {P D : Subgroup G} (h : IsSylowOf p P D) :
    IsPGroup p P := h.2.1

theorem IsSylowOf.le {p : ℕ} {P D : Subgroup G} (h : IsSylowOf p P D) : P ≤ D := h.1

/-- A point of `Ω` fixed by `P` is described by a conjugate of `H` containing `P`. -/
theorem exists_conj_of_mem_fixedPts {H P : Subgroup G} {ω : G ⧸ H}
    (hω : ω ∈ fixedPts H P) : ∃ g : G, MulAction.stabilizer G ω = conj g H ∧ P ≤ conj g H := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
  refine ⟨g, stabilizer_mk H g, ?_⟩
  rw [← stabilizer_mk H g]
  exact mem_fixedPts_iff_le_stabilizer.mp hω

/-- `X` fixes a point of `Ω` iff `X` is contained in a conjugate of `H`. -/
theorem nonempty_fixedPts_iff {H X : Subgroup G} :
    (fixedPts H X).Nonempty ↔ ∃ g : G, X ≤ conj g H := by
  constructor
  · rintro ⟨ω, hω⟩
    obtain ⟨g, hg, hle⟩ := exists_conj_of_mem_fixedPts hω
    exact ⟨g, hg.symm ▸ hle⟩
  · rintro ⟨g, hg⟩
    exact ⟨(g : G ⧸ H), mem_fixedPts_iff_le_stabilizer.mpr (by rw [stabilizer_mk]; exact hg)⟩

/-- Two points of `Ω` with the same stabiliser coincide. -/
theorem eq_of_stabilizer_eq {H : Subgroup G} (hH : IsStronglyEmbedded H) {ω₁ ω₂ : G ⧸ H}
    (h : MulAction.stabilizer G ω₁ = MulAction.stabilizer G ω₂) : ω₁ = ω₂ := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective ω₁
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ω₂
  rw [stabilizer_mk H x, stabilizer_mk H y] at h
  exact Work.ThreePoints.mk_eq_of_conj_eq hH h

/-- Three points of `Ω` fixed by `X` give three distinct conjugates of `H` containing `X`. -/
theorem exists_three_conj_of_three_fixedPts [Finite G] {H X : Subgroup G} (hH : IsStronglyEmbedded H)
    (h3 : 3 ≤ (fixedPts H X).ncard) :
    ∃ g₁ g₂ g₃ : G, conj g₁ H ≠ conj g₂ H ∧ conj g₁ H ≠ conj g₃ H ∧ conj g₂ H ≠ conj g₃ H ∧
      X ≤ conj g₁ H ⊓ conj g₂ H ⊓ conj g₃ H := by
  classical
  have h2 : 2 < (fixedPts H X).ncard := by omega
  obtain ⟨ω₁, hω₁, ω₂, hω₂, ω₃, hω₃, hne₁₂, hne₁₃, hne₂₃⟩ :=
    (Set.two_lt_ncard (s := fixedPts H X) (Set.toFinite _)).mp h2
  obtain ⟨g₁, hg₁, hle₁⟩ := exists_conj_of_mem_fixedPts hω₁
  obtain ⟨g₂, hg₂, hle₂⟩ := exists_conj_of_mem_fixedPts hω₂
  obtain ⟨g₃, hg₃, hle₃⟩ := exists_conj_of_mem_fixedPts hω₃
  refine ⟨g₁, g₂, g₃, ?_, ?_, ?_, le_inf (le_inf (hg₁.symm ▸ hle₁) (hg₂.symm ▸ hle₂))
    (hg₃.symm ▸ hle₃)⟩
  · exact fun hc => hne₁₂ (eq_of_stabilizer_eq hH (by rw [hg₁, hg₂, hc]))
  · exact fun hc => hne₁₃ (eq_of_stabilizer_eq hH (by rw [hg₁, hg₃, hc]))
  · exact fun hc => hne₂₃ (eq_of_stabilizer_eq hH (by rw [hg₂, hg₃, hc]))

end Work.ThreePoints.ThmC
