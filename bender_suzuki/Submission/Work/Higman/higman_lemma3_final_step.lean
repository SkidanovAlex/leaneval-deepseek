/-
Copyright (c) 2024. All rights reserved.

# Higman (1963), Lemma 3 — the final contradiction

Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), 79--96, pp. 83--84.  This file closes the
last step of the proof of Lemma 3 (the "contraction argument"): there is no Suzuki 2-group `P`
with a normal abelian `ξ`-invariant subgroup `A` of exponent `> 4` together with a `ξ`-invariant
subgroup `C ≥ A` with `C² ≤ A²` and an element `u ∈ C ∖ A` whose `A`-coset is all of `C ∖ A`.

The machinery (`Submission/Work/Higman/higman3_final_base.lean`): `ψ_u(a) = a * (u⁻¹ * a * u)`
is an endomorphism of the abelian group `A` with image `Tsub hA u ≤ A`; the squares of the
elements of the coset `A * u` form the coset `ψ_u(A) * u²` (`sq_mul_eq_psi`); and `ψ_u` commutes
with `ξ` because `ξ` preserves the coset `u * A` (`xi_psiHom`, `Tsub_map_xi`).

Dichotomy on `u ^ 2 ∈ Tsub hA u`:

* If `u ^ 2 ∈ ψ_u(A)`, say `ψ_u(a) = u⁻²`, then `(a * u) ^ 2 = 1`, so `a * u ∈ Ω₁(P) ≤ A`,
  contradicting `u ∉ A`.
* Otherwise `B := Tsub hA u ⊔ ⟨u²⟩` is a `ξ`-invariant subgroup of `A` strictly containing
  `Tsub hA u`.  Since `u⁴ = ψ_u(u²) ∈ Tsub hA u`, `B` is covered by the two cosets `Tsub` and
  `Tsub * u²`, so `|B| ≤ 2 |Tsub|` (`card_sup_zpowers_le_two_mul`).  But both are `ξ`-invariant
  subgroups of `A`, hence power subgroups `A ^ (2 ^ s)`, `A ^ (2 ^ t)` with `s < t`
  (`HomocyclicData.hstruct`), and `HomocyclicData.hcard` gives
  `|B : Tsub| = qcard A ^ (t - s) ≥ qcard A ≥ 4`, a contradiction.
-/
import Mathlib
import Submission.Work.Higman.higman_lemma3_base
import Submission.Work.Higman.higman_lemma3_delta
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.Basic
import Submission.Work.Higman.higman3_final_base

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Higman

theorem higman_lemma3_final_step {P : Type} [Group P] [Finite P]
    (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hC2 : powSub C 2 ≤ powSub A 2)
    (hOn : omega1 P ≤ A) (hAne : A ≠ ⊥)
    (D : HomocyclicData h A) (h3 : 3 ≤ D.e) (hq : 4 ≤ qcard A)
    {u : P} (huC : u ∈ C) (huA : u ∉ A)
    (hcoset : ∀ v ∈ C, v ∉ A → v * u⁻¹ ∈ A)
    (hid : ∀ a ∈ A, a * (u⁻¹ * a * u) ∈ powSub A 4) :
    False := by
  classical
  have hu2A : u ^ 2 ∈ A := pow_two_mem_of_mem_sq huC hC2
  by_cases hu2 : u ^ 2 ∈ Tsub hA u
  · -- Case 1: `u ^ 2 ∈ ψ_u(A)`; then `a * u` is an involution outside `A` for a suitable `a`.
    obtain ⟨a, ha⟩ := (mem_Tsub hA).mp (Subgroup.inv_mem (Tsub hA u) hu2)
    have hx2 : ((a : P) * u) ^ 2 = 1 := by
      rw [sq_mul_eq_psi hA hu2A a, ha]
      group
    have hxA : (a : P) * u ∈ omega1 P := h.mem_omega1.mpr hx2
    refine huA ?_
    have hsplit : u = (a : P)⁻¹ * ((a : P) * u) := by group
    rw [hsplit]
    exact A.mul_mem (A.inv_mem a.2) (hOn hxA)
  · -- Case 2: `u ^ 2 ∉ ψ_u(A)`.
    -- `ξ` fixes the coset `u * A`, hence `ξ u * u⁻¹ ∈ A` and `ψ_u` commutes with `ξ`.
    have hxiuC : h.xi u ∈ C := by
      have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom huC
      rwa [hCinv] at hm
    have hxiuA : h.xi u ∉ A := by
      intro hmem
      exact huA (by simpa using symm_mem_of_map_eq h.xi hA.map_eq hmem)
    have hcu : h.xi u * u⁻¹ ∈ A := hcoset _ hxiuC hxiuA
    have hBA : Tsub hA u ⊔ Subgroup.zpowers (u ^ 2) ≤ A :=
      sup_le (Tsub_le hA u) (Subgroup.zpowers_le.mpr hu2A)
    have hTξ : (Tsub hA u).map (h.xi : MulAut P).toMonoidHom = Tsub hA u :=
      Tsub_map_xi h hA hcu
    have hux : h.xi (u ^ 2) ∈ Tsub hA u ⊔ Subgroup.zpowers (u ^ 2) := by
      have hmem : A.subtype (psiHom hA.normal hA.abelian u ⟨h.xi u * u⁻¹, hcu⟩) ∈ Tsub hA u :=
        (mem_Tsub hA).mpr ⟨⟨h.xi u * u⁻¹, hcu⟩, rfl⟩
      rw [xi_u2_eq h hA hcu hu2A]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have hle : (Tsub hA u ⊔ Subgroup.zpowers (u ^ 2)).map (h.xi : MulAut P).toMonoidHom
        ≤ Tsub hA u ⊔ Subgroup.zpowers (u ^ 2) := by
      rw [Subgroup.map_sup, hTξ, zpowers_map]
      exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hux)
    -- the same for `ξ⁻¹`
    have hAinv' : A.map ((h.xi : MulAut P).symm).toMonoidHom = A :=
      map_symm_of_map_eq (h.xi : MulAut P) hA.map_eq
    have hCinv' : C.map ((h.xi : MulAut P).symm).toMonoidHom = C :=
      map_symm_of_map_eq (h.xi : MulAut P) hCinv
    have hxinvuC : (h.xi : MulAut P).symm u ∈ C := by
      have hm := Subgroup.mem_map_of_mem ((h.xi : MulAut P).symm).toMonoidHom huC
      rwa [hCinv'] at hm
    have hxinvuA : (h.xi : MulAut P).symm u ∉ A := by
      intro hmem
      exact huA (by simpa using
        symm_mem_of_map_eq ((h.xi : MulAut P).symm) hAinv' hmem)
    have hcu' : (h.xi : MulAut P).symm u * u⁻¹ ∈ A := hcoset _ hxinvuC hxinvuA
    have hTξ' : (Tsub hA u).map ((h.xi : MulAut P).symm).toMonoidHom = Tsub hA u := by
      have hcomp : (((h.xi : MulAut P).symm).toMonoidHom).comp (h.xi : MulAut P).toMonoidHom
          = MonoidHom.id P := by ext x; simp
      have h1 := congrArg (Subgroup.map ((h.xi : MulAut P).symm).toMonoidHom) hTξ
      rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h1
      exact h1.symm
    have hux' : (h.xi : MulAut P).symm (u ^ 2) ∈ Tsub hA u ⊔ Subgroup.zpowers (u ^ 2) := by
      have hmem : A.subtype
          (psiHom hA.normal hA.abelian u ⟨(h.xi : MulAut P).symm u * u⁻¹, hcu'⟩)
          ∈ Tsub hA u := (mem_Tsub hA).mpr ⟨⟨(h.xi : MulAut P).symm u * u⁻¹, hcu'⟩, rfl⟩
      have hxiu' : (h.xi : MulAut P).symm u = ((h.xi : MulAut P).symm u * u⁻¹) * u := by group
      have hval : (((h.xi : MulAut P).symm u * u⁻¹) * u) ^ 2
          = A.subtype (psiHom hA.normal hA.abelian u
              ⟨(h.xi : MulAut P).symm u * u⁻¹, hcu'⟩) * u ^ 2 :=
        sq_mul_eq_psi hA hu2A ⟨(h.xi : MulAut P).symm u * u⁻¹, hcu'⟩
      rw [map_pow, hxiu', hval]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have hle' : (Tsub hA u ⊔ Subgroup.zpowers (u ^ 2)).map
        ((h.xi : MulAut P).symm).toMonoidHom ≤ Tsub hA u ⊔ Subgroup.zpowers (u ^ 2) := by
      rw [Subgroup.map_sup, hTξ', zpowers_map]
      exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hux')
    have hBξ : (Tsub hA u ⊔ Subgroup.zpowers (u ^ 2)).map (h.xi : MulAut P).toMonoidHom
        = Tsub hA u ⊔ Subgroup.zpowers (u ^ 2) := by
      refine le_antisymm hle ?_
      intro y hy
      rw [Subgroup.mem_map]
      exact ⟨(h.xi : MulAut P).symm y, hle' (Subgroup.mem_map_of_mem _ hy), by simp⟩
    -- both subgroups are `ξ`-invariant subgroups of `A`, hence power subgroups
    obtain ⟨t, ht, hTt⟩ := D.hstruct (Tsub hA u) (Tsub_le hA u) hTξ
    obtain ⟨s, hs, hBs⟩ := D.hstruct (Tsub hA u ⊔ Subgroup.zpowers (u ^ 2)) hBA hBξ
    have hcardT : Nat.card ↥(Tsub hA u) = qcard A ^ (D.e - t) := by
      rw [hTt]; exact D.hcard t ht
    have hcardB : Nat.card ↥(Tsub hA u ⊔ Subgroup.zpowers (u ^ 2)) = qcard A ^ (D.e - s) := by
      rw [hBs]; exact D.hcard s hs
    -- `B` is covered by the two cosets `Tsub` and `Tsub * u²`, whence `|B| ≤ 2 |Tsub|`
    have hle2 : Nat.card ↥(Tsub hA u ⊔ Subgroup.zpowers (u ^ 2)) ≤ 2 * Nat.card ↥(Tsub hA u) :=
      card_sup_zpowers_le_two_mul (Tsub hA u) (u ^ 2)
        (fun y hy => hA.abelian y (Tsub_le hA u hy) (u ^ 2) hu2A)
        (by rw [← pow_mul]; exact pow_four_mem_Tsub hA hu2A)
    have hleT : Nat.card ↥(Tsub hA u) ≤ Nat.card ↥(Tsub hA u ⊔ Subgroup.zpowers (u ^ 2)) :=
      Nat.card_le_card_of_injective
        (fun a : ↥(Tsub hA u) =>
          (⟨a.1, Subgroup.mem_sup_left a.2⟩ : ↥(Tsub hA u ⊔ Subgroup.zpowers (u ^ 2))))
        (fun a b hab => Subtype.ext (by
          simpa only [Subgroup.coe_subtype, Subtype.coe_mk] using congrArg Subtype.val hab))
    have hq1 : 1 < qcard A := by omega
    have hts : s ≤ t := by
      have h : qcard A ^ (D.e - t) ≤ qcard A ^ (D.e - s) := by
        calc qcard A ^ (D.e - t) = Nat.card ↥(Tsub hA u) := hcardT.symm
          _ ≤ Nat.card ↥(Tsub hA u ⊔ Subgroup.zpowers (u ^ 2)) := hleT
          _ = qcard A ^ (D.e - s) := hcardB
      have h2 := (Nat.pow_le_pow_iff_right hq1).mp h
      omega
    have hne : t ≠ s := by
      rintro rfl
      have hthis : u ^ 2 ∈ Tsub hA u ⊔ Subgroup.zpowers (u ^ 2) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers (u ^ 2))
      rw [hBs] at hthis
      refine hu2 ?_
      rwa [hTt]
    have hst : s < t := by omega
    have hineq : qcard A ^ (D.e - s) ≤ 2 * qcard A ^ (D.e - t) := by
      rw [← hcardB, ← hcardT]; exact hle2
    have hlt : 2 * qcard A ^ (D.e - t) < qcard A ^ (D.e - s) := by
      have hstep : D.e - t + 1 ≤ D.e - s := by omega
      have h1 : qcard A ^ (D.e - t + 1) ≤ qcard A ^ (D.e - s) :=
        Nat.pow_le_pow_right (by omega) hstep
      have h2 : qcard A ^ (D.e - t + 1) = qcard A ^ (D.e - t) * qcard A := pow_succ _ _
      have h4 : 2 * qcard A ^ (D.e - t) < qcard A ^ (D.e - t) * 4 := by
        have hpos : 0 < qcard A ^ (D.e - t) := pow_pos (by omega) _
        omega
      calc 2 * qcard A ^ (D.e - t) < qcard A ^ (D.e - t) * 4 := h4
        _ ≤ qcard A ^ (D.e - t) * qcard A := Nat.mul_le_mul_left _ hq
        _ = qcard A ^ (D.e - t + 1) := h2.symm
        _ ≤ qcard A ^ (D.e - s) := h1
    exact absurd (lt_of_lt_of_le hlt hineq) (lt_irrefl _)

end Work.Higman
