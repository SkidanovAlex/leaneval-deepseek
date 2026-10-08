import Mathlib
import Submission.Work.LocalPrelim.Defs
import Submission.Work.LocalPrelim.Basic
import Submission.Work.Fitting.Defs
import Submission.Work.PGroup.Basic
import Submission.Work.Transitivity.Basic.exists_isSCN_m_top_iff
import Submission.Work.Transitivity.Basic.exists_isSCN_m_top_of_mulEquiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `SCN_3`-freeness passes to a quotient by a normal `p'`-subgroup

If a finite group `S` has a Sylow `p`-subgroup `P` with no `SCN_3`-subgroup (no self-centralizing
normal abelian subgroup of rank `≥ 3`) and `N ⊴ S` is a normal `p'`-subgroup, then the image of
`P` in `S ⧸ N` is a Sylow `p`-subgroup of the quotient which again has no `SCN_3`-subgroup.

The point is that `N ∩ P = 1` (as `N` is a `p'`-group and `P` a `p`-group), so the natural map
`↥P → ↥(PN/N)` is an isomorphism, and `SCN_m(⊤)` is an isomorphism invariant
(`Work.Transitivity.Basic.exists_isSCN_m_top_of_mulEquiv`, `..._iff_map_subtype`).
-/

namespace Work.LocalPrelim

open scoped Classical Pointwise

set_option linter.style.haveILetI false

theorem scn3_empty_sylow_quotient {S : Type*} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (P : Sylow p S) (hSCN : ∀ A : Subgroup S, ¬ IsSCN_m 3 (P : Subgroup S) A)
    (N : Subgroup S) [N.Normal] (hN : Work.Fitting.IsPiNat (fun q => q ≠ p) (Nat.card ↥N)) :
    ∃ Q : Sylow p (S ⧸ N), ∀ Ā : Subgroup (S ⧸ N), ¬ IsSCN_m 3 (Q : Subgroup (S ⧸ N)) Ā := by
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : S →* S ⧸ N := QuotientGroup.mk' N
  have hφsurj : Function.Surjective φ := QuotientGroup.mk'_surjective N
  let Q : Sylow p (S ⧸ N) := P.mapSurjective hφsurj
  have hQcoe : (Q : Subgroup (S ⧸ N)) = (P : Subgroup S).map φ := rfl
  refine ⟨Q, ?_⟩
  intro Ā hĀ
  -- `|P|` and `|N|` are coprime, so `P ⊓ N = ⊥`
  have hcop : Nat.Coprime (Nat.card ↥(P : Subgroup S)) (Nat.card ↥N) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    rw [hn]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero]; exact Nat.coprime_one_left _
    · rw [Nat.coprime_pow_left_iff hpos]
      exact (hp.coprime_iff_not_dvd).mpr (fun hd => hN p hp hd rfl)
  have hdisj : Disjoint (P : Subgroup S) N := Subgroup.disjoint_of_coprime_natCard hcop
  -- the natural map `↥P → S ⧸ N` is injective
  have hInj : Function.Injective (φ.comp (P : Subgroup S).subtype) := by
    intro x y hxy
    have hxy' : φ (x : S) = φ (y : S) := hxy
    have hmemN : (x : S)⁻¹ * (y : S) ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      change φ ((x : S)⁻¹ * (y : S)) = 1
      rw [map_mul, map_inv, hxy', inv_mul_cancel]
    have hmemP : (x : S)⁻¹ * (y : S) ∈ (P : Subgroup S) :=
      (P : Subgroup S).mul_mem ((P : Subgroup S).inv_mem x.2) y.2
    have h1 : (x : S)⁻¹ * (y : S) = 1 := by
      have h2 : (x : S)⁻¹ * (y : S) ∈ (P : Subgroup S) ⊓ N := ⟨hmemP, hmemN⟩
      rw [Disjoint.eq_bot hdisj, Subgroup.mem_bot] at h2
      exact h2
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  -- the induced isomorphism `↥P ≃* ↥Q`
  let F : ↥(P : Subgroup S) →* ↥Q :=
    (φ.comp (P : Subgroup S).subtype).codRestrict (Q : Subgroup (S ⧸ N))
      (fun x => by
        rw [hQcoe]
        exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  have hFInj : Function.Injective F := by
    intro x y h
    exact hInj (congrArg Subtype.val h)
  have hFSurj : Function.Surjective F := by
    intro y
    have hy : (y : S ⧸ N) ∈ (P : Subgroup S).map φ := by
      rw [← hQcoe]; exact y.2
    obtain ⟨x, hxP, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hxP⟩, Subtype.ext hxy⟩
  let e : ↥(P : Subgroup S) ≃* ↥Q := MulEquiv.ofBijective F ⟨hFInj, hFSurj⟩
  -- transport `Ā ∈ SCN_3(Q)` to an `SCN_3`-subgroup of `P`
  have hmap : (Ā.subgroupOf (Q : Subgroup (S ⧸ N))).map (Q : Subgroup (S ⧸ N)).subtype = Ā :=
    Subgroup.map_subgroupOf_eq_of_le hĀ.le
  have hB : IsSCN_m 3 (⊤ : Subgroup ↥Q) (Ā.subgroupOf (Q : Subgroup (S ⧸ N))) :=
    (Work.Transitivity.Basic.isSCN_m_top_iff_map_subtype 3 (Q : Subgroup (S ⧸ N))
      (Ā.subgroupOf (Q : Subgroup (S ⧸ N)))).mpr (by rw [hmap]; exact hĀ)
  obtain ⟨C, hC⟩ := (Work.Transitivity.Basic.exists_isSCN_m_top_of_mulEquiv e).mpr ⟨_, hB⟩
  have hC' : IsSCN_m 3 (P : Subgroup S) (C.map (P : Subgroup S).subtype) :=
    (Work.Transitivity.Basic.isSCN_m_top_iff_map_subtype 3 (P : Subgroup S) C).mp hC
  exact hSCN _ hC'

end Work.LocalPrelim
