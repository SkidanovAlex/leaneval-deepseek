/-
Copyright (c) 2024. All rights reserved.

# Higman (1963), Lemma 3 — the final step: shared vocabulary

For a Suzuki 2-group `P`, a normal abelian `ξ`-invariant subgroup `A` and an element `u` with
`u ^ 2 ∈ A`, this file studies the "norm" map

  `ψ_u : A → A,   a ↦ a * (u⁻¹ * a * u)`,

which is an endomorphism of the abelian group `A` (`psiHom`).  Its image is the subgroup
`Tsub hA u` of `P` (`mem_Tsub`), which lies in `A` (`Tsub_le`).

The two computational facts used in the proof of Higman's Lemma 3 are:

* the squares of the elements of the coset `A * u` are exactly the coset `ψ_u(A) * u²`
  (`sq_mul_eq_psi`: `(a * u) ^ 2 = ψ_u(a) * u ^ 2`), so that every `x ∈ A * u` has
  `x ^ 2 ∈ Tsub hA u * u ^ 2`;
* `ψ_u` commutes with `ξ` provided `ξ` fixes the coset `u * A`
  (`xi_psiHom`: `ξ (ψ_u(a)) = ψ_u (ξ a)`), hence `Tsub hA u` is `ξ`-invariant
  (`Tsub_map_xi`).

Also here: the general group-theoretic counting lemma `card_sup_zpowers_le_two_mul`
(if `x` commutes with `H` and `x ^ 2 ∈ H` then `|H ⊔ ⟨x⟩| ≤ 2 |H|`), and the elementary
facts `zpowers_map` and `map_symm_of_map_eq` about automorphisms.
-/
import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.higman_lemma3_delta
import Submission.Work.Higman.higman_lemma3_base

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

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]
variable {A C : Subgroup P}

/-! ## The norm map `ψ_u` -/

/-- The map `a ↦ a * (u⁻¹ * a * u)` from a normal subgroup `A` to itself. -/
noncomputable def psiFun (hAn : A.Normal) (u : P) (a : ↥A) : ↥A :=
  ⟨(a : P) * (u⁻¹ * (a : P) * u),
    A.mul_mem a.2 (by simpa only [inv_inv] using hAn.conj_mem (a : P) a.2 u⁻¹)⟩

theorem psiFun_coe (hAn : A.Normal) (u : P) (a : ↥A) :
    ((psiFun hAn u a : ↥A) : P) = (a : P) * (u⁻¹ * (a : P) * u) := rfl

/-- `ψ_u` is an endomorphism of an abelian normal subgroup `A`. -/
noncomputable def psiHom (hAn : A.Normal) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (u : P) : ↥A →* ↥A where
  toFun := psiFun hAn u
  map_one' := by
    apply Subtype.ext
    simp [psiFun]
  map_mul' a b := by
    apply Subtype.ext
    show ((a : P) * (b : P)) * (u⁻¹ * ((a : P) * (b : P)) * u)
      = ((a : P) * (u⁻¹ * (a : P) * u)) * ((b : P) * (u⁻¹ * (b : P) * u))
    have ha : u⁻¹ * (a : P) * u ∈ A := by
      simpa only [inv_inv] using hAn.conj_mem (a : P) a.2 u⁻¹
    have hswap : (b : P) * (u⁻¹ * (a : P) * u) = (u⁻¹ * (a : P) * u) * (b : P) :=
      hAb (b : P) b.2 _ ha
    calc ((a : P) * (b : P)) * (u⁻¹ * ((a : P) * (b : P)) * u)
        = (a : P) * ((b : P) * (u⁻¹ * (a : P) * u)) * ((u⁻¹ * (b : P) * u)) := by group
      _ = (a : P) * ((u⁻¹ * (a : P) * u) * (b : P)) * ((u⁻¹ * (b : P) * u)) := by rw [hswap]
      _ = ((a : P) * (u⁻¹ * (a : P) * u)) * ((b : P) * (u⁻¹ * (b : P) * u)) := by group

theorem psiHom_val (hAn : A.Normal) (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (u : P) (a : ↥A) :
    A.subtype (psiHom hAn hAb u a) = (a : P) * (u⁻¹ * (a : P) * u) := rfl

/-! ## The image `Tsub hA u ≤ A` -/

/-- The image of `ψ_u : A → A`, viewed as the subgroup `{a * (u⁻¹ * a * u) : a ∈ A}` of `P`. -/
noncomputable def Tsub {h : IsSuzuki2Grp P} (hA : IsXiAbelNormal h A) (u : P) : Subgroup P :=
  (A.subtype.comp (psiHom hA.normal hA.abelian u)).range

theorem mem_Tsub {h : IsSuzuki2Grp P} (hA : IsXiAbelNormal h A) {u y : P} :
    y ∈ Tsub hA u ↔ ∃ a : ↥A, A.subtype (psiHom hA.normal hA.abelian u a) = y :=
  MonoidHom.mem_range

theorem mem_Tsub_iff {h : IsSuzuki2Grp P} (hA : IsXiAbelNormal h A) {u y : P} :
    y ∈ Tsub hA u ↔ ∃ a : ↥A, (a : P) * (u⁻¹ * (a : P) * u) = y := by
  rw [mem_Tsub hA]
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, by rw [psiHom_val] at ha; exact ha⟩
  · rintro ⟨a, ha⟩; exact ⟨a, by rw [psiHom_val]; exact ha⟩

theorem Tsub_le {h : IsSuzuki2Grp P} (hA : IsXiAbelNormal h A) (u : P) : Tsub hA u ≤ A := by
  intro y hy
  obtain ⟨a, ha⟩ := (mem_Tsub hA).mp hy
  rw [← ha]
  exact A.mul_mem a.2 (by simpa only [inv_inv] using hA.normal.conj_mem (a : P) a.2 u⁻¹)

/-- If every `a * (u⁻¹ * a * u)` lies in `A⁴`, then so does all of `Tsub hA u`. -/
theorem Tsub_le_powSub_four {h : IsSuzuki2Grp P} (hA : IsXiAbelNormal h A) {u : P}
    (hid : ∀ a ∈ A, a * (u⁻¹ * a * u) ∈ powSub A 4) : Tsub hA u ≤ powSub A 4 := by
  intro y hy
  obtain ⟨a, ha⟩ := (mem_Tsub_iff hA).mp hy
  rw [← ha]
  exact hid a a.2

/-! ## The square of an element of the coset `A * u` -/

/-- `(a * u) ^ 2 = ψ_u(a) * u ^ 2` for `a ∈ A` and `u ^ 2 ∈ A`. -/
theorem sq_mul_eq_psi {h : IsSuzuki2Grp P} (hA : IsXiAbelNormal h A) {u : P}
    (hu2 : u ^ 2 ∈ A) (a : ↥A) :
    ((a : P) * u) ^ 2 = A.subtype (psiHom hA.normal hA.abelian u a) * u ^ 2 := by
  have hconj : u * (a : P) * u⁻¹ = u⁻¹ * (a : P) * u := by
    have hc : u ^ 2 * (a : P) = (a : P) * u ^ 2 := hA.abelian _ hu2 _ a.2
    have h1 : u * (u * (a : P) * u⁻¹) = u * (u⁻¹ * (a : P) * u) := by
      calc u * (u * (a : P) * u⁻¹) = u ^ 2 * (a : P) * u⁻¹ := by rw [pow_two]; group
        _ = (a : P) * u ^ 2 * u⁻¹ := by rw [hc]
        _ = u * (u⁻¹ * (a : P) * u) := by rw [pow_two]; group
    exact mul_left_cancel h1
  have hstep : ((a : P) * u) ^ 2 = (a : P) * (u * (a : P) * u⁻¹) * u ^ 2 := by
    rw [pow_two, pow_two]; group
  rw [hstep, hconj, psiHom_val]

/-- `ψ_u` commutes with an automorphism `φ` which fixes the coset `u * A`
(here: `ξ`, when `ξ u * u⁻¹ ∈ A`). -/
theorem xi_psiHom (h : IsSuzuki2Grp P) (hA : IsXiAbelNormal h A) {u : P}
    (hcu : h.xi u * u⁻¹ ∈ A) (a : ↥A) :
    h.xi (A.subtype (psiHom hA.normal hA.abelian u a))
      = A.subtype (psiHom hA.normal hA.abelian u (xiA h hA.map_eq a)) := by
  have hmem : h.xi (a : P) ∈ A := (xiA h hA.map_eq a).2
  have hxiu : h.xi u = (h.xi u * u⁻¹) * u := by group
  have hkey : (h.xi u)⁻¹ * h.xi (a : P) * h.xi u = u⁻¹ * h.xi (a : P) * u := by
    have hc : (h.xi u * u⁻¹)⁻¹ * h.xi (a : P) * (h.xi u * u⁻¹) = h.xi (a : P) := by
      rw [hA.abelian _ (A.inv_mem hcu) _ hmem]
      group
    have hstep : (h.xi u)⁻¹ * h.xi (a : P) * h.xi u
        = u⁻¹ * ((h.xi u * u⁻¹)⁻¹ * h.xi (a : P) * (h.xi u * u⁻¹)) * u := by
      conv_lhs => rw [hxiu]
      group
    rw [hstep, hc]
  rw [psiHom_val, psiHom_val, xiA_coe]
  simp only [map_mul, map_inv]
  rw [hkey]

/-- `Tsub hA u` is `ξ`-invariant when `ξ u * u⁻¹ ∈ A`. -/
theorem Tsub_map_xi (h : IsSuzuki2Grp P) (hA : IsXiAbelNormal h A) {u : P}
    (hcu : h.xi u * u⁻¹ ∈ A) :
    (Tsub hA u).map (h.xi : MulAut P).toMonoidHom = Tsub hA u := by
  refine le_antisymm ?_ ?_
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rw [mem_Tsub hA] at hz ⊢
    obtain ⟨a, ha⟩ := hz
    refine ⟨xiA h hA.map_eq a, ?_⟩
    have hx := xi_psiHom h hA hcu a
    rw [← ha] at hzy
    simp only [MulEquiv.coe_toMonoidHom] at hzy
    rw [hx] at hzy
    exact hzy
  · intro y hy
    rw [mem_Tsub hA] at hy
    obtain ⟨a, ha⟩ := hy
    refine Subgroup.mem_map.mpr
      ⟨A.subtype (psiHom hA.normal hA.abelian u (xiAinv h hA.map_eq a)), ?_, ?_⟩
    · rw [mem_Tsub hA]; exact ⟨xiAinv h hA.map_eq a, rfl⟩
    · have hx := xi_psiHom h hA hcu (xiAinv h hA.map_eq a)
      have hcomp : xiA h hA.map_eq (xiAinv h hA.map_eq a) = a := by
        apply Subtype.ext
        rw [xiA_coe, xiAinv_coe]
        exact MulEquiv.apply_symm_apply (h.xi : MulAut P) (a : P)
      rw [hcomp] at hx
      simp only [MulEquiv.coe_toMonoidHom]
      rw [hx, ha]

/-- `u ^ 4 = ψ_u(u ^ 2) ∈ Tsub hA u` whenever `u ^ 2 ∈ A`. -/
theorem pow_four_mem_Tsub {h : IsSuzuki2Grp P} (hA : IsXiAbelNormal h A) {u : P}
    (hu2 : u ^ 2 ∈ A) :
    u ^ 4 ∈ Tsub hA u := by
  rw [mem_Tsub hA]
  refine ⟨⟨u ^ 2, hu2⟩, ?_⟩
  rw [psiHom_val]
  have h2 : u⁻¹ * (u ^ 2 : P) * u = u ^ 2 := by rw [pow_two]; group
  rw [h2, ← pow_add]

/-- `ξ (u ^ 2) = ψ_u(c) * u ^ 2` for `c = ξ u * u⁻¹ ∈ A`. -/
theorem xi_u2_eq (h : IsSuzuki2Grp P) (hA : IsXiAbelNormal h A) {u : P}
    (hcu : h.xi u * u⁻¹ ∈ A) (hu2A : u ^ 2 ∈ A) :
    h.xi (u ^ 2) = A.subtype (psiHom hA.normal hA.abelian u ⟨h.xi u * u⁻¹, hcu⟩) * u ^ 2 := by
  rw [map_pow]
  have hxiu : h.xi u = (h.xi u * u⁻¹) * u := by group
  conv_lhs => rw [hxiu]
  exact sq_mul_eq_psi hA hu2A ⟨h.xi u * u⁻¹, hcu⟩

/-! ## Elementary group theory -/

/-- An automorphism maps `⟨x⟩` to `⟨φ x⟩`. -/
theorem zpowers_map (φ : MulAut P) (x : P) :
    (Subgroup.zpowers x).map φ.toMonoidHom = Subgroup.zpowers (φ x) := by
  rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, Set.image_singleton,
    ← Subgroup.zpowers_eq_closure]
  rfl

/-- If `A` is invariant under `φ` it is invariant under `φ⁻¹`. -/
theorem map_symm_of_map_eq (φ : MulAut P) {A : Subgroup P}
    (h : A.map φ.toMonoidHom = A) : A.map φ.symm.toMonoidHom = A := by
  have hcomp : (φ.symm.toMonoidHom).comp φ.toMonoidHom = MonoidHom.id P := by
    ext x; simp
  have h1 := congrArg (Subgroup.map φ.symm.toMonoidHom) h
  rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h1
  exact h1.symm

/-- If `x` commutes with the subgroup `H` and `x ^ 2 ∈ H`, then the subgroup generated by `H`
and `x` has at most twice the order of `H`. -/
theorem card_sup_zpowers_le_two_mul {G : Type*} [Group G] [Finite G] (H : Subgroup G) (x : G)
    (hcomm : ∀ h ∈ H, h * x = x * h) (hx2 : x ^ 2 ∈ H) :
    Nat.card ↥(H ⊔ Subgroup.zpowers x) ≤ 2 * Nat.card ↥H := by
  classical
  have hx2inv : x⁻¹ * x⁻¹ ∈ H := by
    have h : (x ^ 2)⁻¹ ∈ H := H.inv_mem hx2
    rwa [pow_two, mul_inv_rev] at h
  let S : Subgroup G :=
    { carrier := {y : G | y ∈ H ∨ ∃ h ∈ H, h * x = y}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro a b (ha | ⟨h, hh, rfl⟩) (hb | ⟨k, hk, rfl⟩)
        · exact Or.inl (H.mul_mem ha hb)
        · exact Or.inr ⟨a * k, H.mul_mem ha hk, by group⟩
        · exact Or.inr ⟨h * b, H.mul_mem hh hb, by rw [mul_assoc, hcomm b hb, ← mul_assoc]⟩
        · refine Or.inl ?_
          have h2 : h * x * (k * x) = h * k * x ^ 2 := by
            rw [pow_two]
            calc h * x * (k * x) = h * (x * k) * x := by simp only [mul_assoc]
              _ = h * (k * x) * x := by rw [hcomm k hk]
              _ = h * k * (x * x) := by simp only [mul_assoc]
          rw [h2]
          exact H.mul_mem (H.mul_mem hh hk) hx2
      inv_mem' := by
        rintro a (ha | ⟨h, hh, rfl⟩)
        · exact Or.inl (H.inv_mem ha)
        · refine Or.inr ⟨x⁻¹ * x⁻¹ * h⁻¹, H.mul_mem hx2inv (H.inv_mem hh), ?_⟩
          rw [mul_inv_rev]
          calc x⁻¹ * x⁻¹ * h⁻¹ * x = x⁻¹ * x⁻¹ * (h⁻¹ * x) := by simp only [mul_assoc]
            _ = x⁻¹ * x⁻¹ * (x * h⁻¹) := by rw [hcomm h⁻¹ (H.inv_mem hh)]
            _ = x⁻¹ * h⁻¹ := by group }
  have hsub : H ⊔ Subgroup.zpowers x ≤ S := by
    refine sup_le (fun y hy => Or.inl hy) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr ⟨1, H.one_mem, by simp⟩
  calc Nat.card ↥(H ⊔ Subgroup.zpowers x) ≤ Nat.card ↥S :=
        Nat.card_le_card_of_injective
          (fun a : ↥(H ⊔ Subgroup.zpowers x) => (⟨a.1, hsub a.2⟩ : ↥S))
          (fun a b hab => Subtype.ext (by
            simpa only [Subgroup.coe_subtype, Subtype.coe_mk] using congrArg Subtype.val hab))
    _ ≤ Nat.card (↥H × Bool) :=
        Nat.card_le_card_of_surjective
          (fun p : ↥H × Bool => match p.2 with
            | false => (⟨p.1.1, Or.inl p.1.2⟩ : ↥S)
            | true => (⟨p.1.1 * x, Or.inr ⟨p.1.1, p.1.2, rfl⟩⟩ : ↥S))
          (by
            rintro ⟨y, hy⟩
            rcases hy with hy | ⟨h, hh, rfl⟩
            · exact ⟨(⟨y, hy⟩, false), rfl⟩
            · exact ⟨(⟨h, hh⟩, true), rfl⟩)
    _ = 2 * Nat.card ↥H := by
        have hb : Nat.card Bool = 2 := by
          rw [Nat.card_eq_fintype_card, Fintype.card_bool]
        rw [Nat.card_prod, hb, Nat.mul_comm]

end Work.Higman
