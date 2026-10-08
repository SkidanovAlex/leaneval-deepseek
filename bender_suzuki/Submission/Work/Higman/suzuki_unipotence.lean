/-
Copyright (c) 2024. All rights reserved.

# Suzuki 2-groups: `P` acts trivially on `A/A²`

Higman, *Suzuki 2-groups* (1963), §3.  If `A` is a `ξ`-invariant abelian normal subgroup of a
Suzuki 2-group `P` then every element of `P` acts on `A` trivially modulo `A²`:

`⁅u, a⁆ ∈ powSub A 2 = A²` for all `u : P`, `a ∈ A`.

The reason is that all involutions of `P` are central, while the `2 ^ (e-1)`-st power map on `A`
(where `2 ^ e` is the exponent of `A`; Higman's Lemma 1, `higman_lemma1`) induces an isomorphism
`A/A² ≅ A ∩ Ω₁(P)` commuting with every automorphism of `P` preserving `A`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.SuzukiMaximal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- For a homomorphism `f`, `|ker f| * |range f| = |G|`. -/
theorem card_ker_mul_card_range' {G G' : Type*} [Group G] [Group G'] (f : G →* G') :
    Nat.card f.ker * Nat.card f.range = Nat.card G := by
  have h := Subgroup.card_mul_index f.ker
  rwa [Subgroup.index_ker f] at h

/-- **Higman 1963, Lemma 1 (isomorphism form).**  Let `A` be a `ξ`-invariant abelian normal
subgroup of a Suzuki 2-group, of exponent `2 ^ e`.  Then the `2 ^ (e-1)`-st power map induces a
bijection `A / A² ≅ A ∩ Ω₁(P)`; in particular, for `x ∈ A` one has
`x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1`. -/
theorem mem_powSub_two_iff (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A) :
    ∃ e : ℕ, (∀ a ∈ A, a ^ 2 ^ e = 1) ∧ (∃ a ∈ A, orderOf a = 2 ^ e) ∧
      (∀ x ∈ A, x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1) := by
  classical
  obtain ⟨hAn, hAinv, hAb⟩ := hA
  obtain ⟨e, he1, he2, he3⟩ := higman_lemma1 h hAb hAinv
  refine ⟨e, he1, he2, ?_⟩
  letI : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun x y => Subtype.ext (hAb x x.2 y y.2) }
  have hsq_le : powSub A 2 ≤ A := powSub_le (by norm_num : 0 < 2)
  rcases Nat.eq_zero_or_pos e with he0 | hepos
  · have hbot : A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have h := he1 x hx
      simpa [he0] using h
    intro x hx
    rw [hbot] at hx
    simp only [Subgroup.mem_bot] at hx
    subst hx
    simp
  set k : ℕ := 2 ^ (e - 1) with hk
  have hkpos : 0 < k := by rw [hk]; exact pow_pos (by norm_num) _
  have hk2 : 2 * k = 2 ^ e := by
    rw [hk, mul_comm 2 (2 ^ (e - 1)), ← pow_succ]
    congr 1
    omega
  have hk2' : k * 2 = 2 ^ e := by rw [mul_comm]; exact hk2
  set φ : ↥A →* ↥A := powMonoidHom (α := ↥A) k with hφ
  set ψ : ↥A →* ↥A := powMonoidHom (α := ↥A) 2 with hψ
  have hφ_apply : ∀ x : ↥A, (φ x : P) = (x : P) ^ k := by
    intro x; simp [hφ, powMonoidHom_apply]
  have hψ_apply : ∀ x : ↥A, (ψ x : P) = (x : P) ^ 2 := by
    intro x; simp [hψ, powMonoidHom_apply]
  have hrangeφ_sub : ∀ x : ↥A, (φ x : P) ∈ omega1 P := by
    intro x
    rw [h.mem_omega1, hφ_apply, ← pow_mul, hk2']
    exact he1 (x : P) x.2
  -- every involution of `A` is a `k`-th power in `A`
  have hrangeφ_surj : ∀ z : ↥A, (z : P) ∈ omega1 P → ∃ x : ↥A, (φ x : P) = (z : P) := by
    intro z hz
    rcases eq_or_ne (z : P) 1 with hz1 | hz1
    · refine ⟨1, ?_⟩
      rw [hφ_apply, Subgroup.coe_one, one_pow]
      exact hz1.symm
    obtain ⟨a₀, ha₀, hord⟩ := he2
    have hx₀mem : a₀ ^ k ∈ A := Subgroup.pow_mem A ha₀ k
    have hx₀sq : (a₀ ^ k) ^ 2 = 1 := by
      rw [← pow_mul, hk2']; exact he1 a₀ ha₀
    have hx₀ne : a₀ ^ k ≠ 1 := by
      intro hc
      have hdvd : 2 ^ e ∣ k := by
        rw [← hord]; exact orderOf_dvd_iff_pow_eq_one.mpr hc
      have hklt : k < 2 ^ e := by
        rw [hk]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      exact not_le_of_gt hklt (Nat.le_of_dvd hkpos hdvd)
    have hzsq : (z : P) ^ 2 = 1 := h.mem_omega1.mp hz
    obtain ⟨y, hyA, hy⟩ := exists_pow_eq_of_mem_invol h hAinv (s := e - 1)
      (x := a₀ ^ k) hx₀mem hx₀sq hx₀ne ⟨a₀, ha₀, rfl⟩ (z : P) z.2 hzsq
    exact ⟨⟨y, hyA⟩, by rw [hφ_apply]; exact hy⟩
  -- `|range φ| = |A ∩ Ω₁|`, via the bijection `y ↦ y`
  have hcardφrange : Nat.card ↥(φ.range) = Nat.card ↥(A ⊓ (omega1 P : Subgroup P)) := by
    refine Nat.card_eq_of_bijective
      (fun y : ↥(φ.range) =>
        (⟨(y.1 : P), Subgroup.mem_inf.mpr ⟨y.1.2, ?_⟩⟩ :
          ↥(A ⊓ (omega1 P : Subgroup P)))) ?_
    · obtain ⟨x, hx⟩ := y.2
      exact (congrArg (fun t : ↥A => (t : P)) hx) ▸ hrangeφ_sub x
    · constructor
      · intro y₁ y₂ hy
        refine Subtype.ext (Subtype.ext ?_)
        exact congrArg (fun t : ↥(A ⊓ (omega1 P : Subgroup P)) => (t : P)) hy
      · intro z
        have hz : (z : P) ∈ omega1 P := (Subgroup.mem_inf.mp z.2).2
        obtain ⟨x, hx⟩ := hrangeφ_surj ⟨(z : P), (Subgroup.mem_inf.mp z.2).1⟩ hz
        refine ⟨⟨⟨(z : P), (Subgroup.mem_inf.mp z.2).1⟩, ⟨x, ?_⟩⟩, ?_⟩
        · exact Subtype.ext hx
        · exact Subtype.ext rfl
  -- `|ker ψ| = |A ∩ Ω₁|`
  have hcardψker : Nat.card ↥(ψ.ker) = Nat.card ↥(A ⊓ (omega1 P : Subgroup P)) := by
    have h1 : Nat.card ↥(ψ.ker) = Nat.card {x : ↥A | x ^ 2 = 1} := by
      refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl ↥A) (fun x => ?_))
      show x ∈ ψ.ker ↔ x ^ 2 = 1
      rw [MonoidHom.mem_ker]
      constructor
      · intro hx
        refine Subtype.ext ?_
        have hh := congrArg (fun t : ↥A => (t : P)) hx
        simpa [hψ_apply] using hh
      · intro hx
        refine Subtype.ext ?_
        rw [hψ_apply]
        simpa using congrArg (fun t : ↥A => (t : P)) hx
    rw [h1]
    exact card_twoTorsion_eq_card_inf_omega1 h A
  -- `|range ψ| = |A²|`
  have hcardψrange : Nat.card ↥(ψ.range) = Nat.card ↥(powSub A 2) := by
    have hS : Nat.card {x : ↥A | (x : P) ∈ powSub A 2} = Nat.card ↥(powSub A 2) := by
      refine Nat.card_eq_of_bijective
        (fun y : {x : ↥A | (x : P) ∈ powSub A 2} => (⟨(y.1 : P), y.2⟩ : ↥(powSub A 2))) ?_
      constructor
      · intro y₁ y₂ hy
        exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥(powSub A 2) => (t : P)) hy))
      · intro w
        exact ⟨⟨⟨(w : P), hsq_le w.2⟩, w.2⟩, Subtype.ext rfl⟩
    have h2 : Nat.card ↥(ψ.range) = Nat.card {x : ↥A | (x : P) ∈ powSub A 2} := by
      refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl ↥A) (fun x => ?_))
      show x ∈ ψ.range ↔ (x : P) ∈ powSub A 2
      rw [MonoidHom.mem_range]
      constructor
      · rintro ⟨y, hy⟩
        rw [← hy, hψ_apply]
        exact pow_mem_powSub y.2
      · intro hx
        obtain ⟨y, hyA, hy⟩ := (mem_powSub_iff hAb).mp hx
        exact ⟨⟨y, hyA⟩, Subtype.ext hy⟩
    rw [h2, hS]
  have hcardψsplit : Nat.card ↥(ψ.ker) * Nat.card ↥(ψ.range) = Nat.card ↥A :=
    card_ker_mul_card_range' ψ
  have hcardφsplit : Nat.card ↥(φ.ker) * Nat.card ↥(φ.range) = Nat.card ↥A :=
    card_ker_mul_card_range' φ
  -- `|ker φ| = |A²|`
  have hcardkerφ : Nat.card ↥(φ.ker) = Nat.card ↥(powSub A 2) := by
    have hNpos : 0 < Nat.card ↥(A ⊓ (omega1 P : Subgroup P)) :=
      Nat.card_pos_iff.mpr ⟨⟨(1 : ↥(A ⊓ (omega1 P : Subgroup P)))⟩, inferInstance⟩
    have h2 : Nat.card ↥(powSub A 2) * Nat.card ↥(A ⊓ (omega1 P : Subgroup P)) =
        Nat.card ↥A := by
      have hh := hcardψsplit
      rw [hcardψker, hcardψrange] at hh
      rw [mul_comm]; exact hh
    have h4 : Nat.card ↥(φ.ker) * Nat.card ↥(A ⊓ (omega1 P : Subgroup P)) = Nat.card ↥A := by
      rw [← hcardφrange]
      exact hcardφsplit
    exact Nat.eq_of_mul_eq_mul_right hNpos (by rw [← h2] at h4; exact h4)
  -- `A² ⊆ ker φ`, with equality of cardinalities
  have hsqsub : ∀ x : ↥A, (x : P) ∈ powSub A 2 → x ∈ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    obtain ⟨z, hzA, hz⟩ := (mem_powSub_iff hAb).mp hx
    have hval : ((φ x : ↥A) : P) = ((1 : ↥A) : P) := by
      rw [Subgroup.coe_one, hφ_apply, ← hz, ← pow_mul, hk2]
      exact he1 z hzA
    simpa [hφ_apply] using hval
  have hinj : Function.Injective (fun w : ↥(powSub A 2) =>
      (⟨⟨(w : P), hsq_le w.2⟩, hsqsub ⟨(w : P), hsq_le w.2⟩ w.2⟩ : ↥(φ.ker))) := by
    intro a b hab
    exact Subtype.ext (congrArg (fun t : ↥(φ.ker) => ((t.1 : ↥A) : P)) hab)
  have hsurj : Function.Surjective (fun w : ↥(powSub A 2) =>
      (⟨⟨(w : P), hsq_le w.2⟩, hsqsub ⟨(w : P), hsq_le w.2⟩ w.2⟩ : ↥(φ.ker))) := by
    haveI : Fintype ↥(powSub A 2) := Fintype.ofFinite _
    haveI : Fintype ↥(φ.ker) := Fintype.ofFinite _
    have hcard : Fintype.card ↥(powSub A 2) = Fintype.card ↥(φ.ker) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardkerφ]
    exact ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩).2
  intro x hx
  constructor
  · intro hx2
    have hmem : (⟨x, hx⟩ : ↥A) ∈ φ.ker := hsqsub ⟨x, hx⟩ hx2
    rw [MonoidHom.mem_ker] at hmem
    have hh := congrArg (fun t : ↥A => (t : P)) hmem
    simpa [hφ_apply] using hh
  · intro hx2
    have hmem : (⟨x, hx⟩ : ↥A) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have hval : ((φ (⟨x, hx⟩ : ↥A) : ↥A) : P) = ((1 : ↥A) : P) := by
        rw [Subgroup.coe_one, hφ_apply]
        exact hx2
      simpa [hφ_apply] using hval
    obtain ⟨w, hw⟩ := hsurj ⟨⟨x, hx⟩, hmem⟩
    have hwx : (w : P) = x := congrArg (fun t : ↥(φ.ker) => ((t.1 : ↥A) : P)) hw
    rw [← hwx]
    exact w.2

/-- **Higman's dichotomy (power form).**  Let `A` be a `ξ`-invariant abelian normal subgroup of
a Suzuki 2-group, of exponent `2 ^ e`.  Then every element of `A` of order at most two is a
`2 ^ (e-1)`-st power inside `A`. -/
theorem mem_powSub_of_sq_eq_one (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    {e : ℕ} (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he2 : ∃ a ∈ A, orderOf a = 2 ^ e)
    {z : P} (hzA : z ∈ A) (hz2 : z ^ 2 = 1) : z ∈ powSub A (2 ^ (e - 1)) := by
  classical
  obtain ⟨hAn, hAinv, hAb⟩ := hA
  rcases eq_or_ne z 1 with hz1 | hz1
  · subst hz1
    exact Subgroup.one_mem _
  rcases Nat.eq_zero_or_pos e with he0 | hepos
  · have hbot : A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hh := he1 x hx
      simpa [he0] using hh
    rw [hbot] at hzA
    simp only [Subgroup.mem_bot] at hzA
    exact absurd hzA hz1
  · set k : ℕ := 2 ^ (e - 1) with hk
    have hkpos : 0 < k := by rw [hk]; exact pow_pos (by norm_num) _
    have hk2' : k * 2 = 2 ^ e := by
      rw [hk, ← pow_succ]; congr 1; omega
    obtain ⟨a₀, ha₀, hord⟩ := he2
    have hx₀mem : a₀ ^ k ∈ A := Subgroup.pow_mem A ha₀ k
    have hx₀sq : (a₀ ^ k) ^ 2 = 1 := by
      rw [← pow_mul, hk2']; exact he1 a₀ ha₀
    have hx₀ne : a₀ ^ k ≠ 1 := by
      intro hc
      have hdvd : 2 ^ e ∣ k := by
        rw [← hord]; exact orderOf_dvd_iff_pow_eq_one.mpr hc
      have hklt : k < 2 ^ e := by
        rw [hk]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      exact not_le_of_gt hklt (Nat.le_of_dvd hkpos hdvd)
    obtain ⟨y, hyA, hy⟩ := exists_pow_eq_of_mem_invol h hAinv (s := e - 1)
      (x := a₀ ^ k) hx₀mem hx₀sq hx₀ne ⟨a₀, ha₀, rfl⟩ z hzA hz2
    exact Subgroup.subset_closure ⟨y, hyA, hy⟩

/-- **Unipotence.**  In a Suzuki 2-group, every element acts trivially on `A / A²`:
`⁅u, a⁆ ∈ powSub A 2` for `u : P` and `a ∈ A`, whenever `A` is a `ξ`-invariant abelian normal
subgroup. -/
theorem commutator_mem_powSub_two (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A) :
    ∀ u : P, ∀ a ∈ A, ⁅u, a⁆ ∈ powSub A 2 := by
  classical
  obtain ⟨e, he1, he2, hkey⟩ := mem_powSub_two_iff h hA
  obtain ⟨hAn, hAinv, hAb⟩ := hA
  intro u a ha
  rcases Nat.eq_zero_or_pos e with he0 | hepos
  · have hbot : A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have h := he1 x hx
      simpa [he0] using h
    rw [hbot] at ha
    simp only [Subgroup.mem_bot] at ha
    subst ha
    simp
  · set k : ℕ := 2 ^ (e - 1) with hk
    have hk2' : k * 2 = 2 ^ e := by
      rw [hk, ← pow_succ]
      congr 1
      omega
    have hak : a ^ k ∈ omega1 P := by
      rw [h.mem_omega1, ← pow_mul, hk2']
      exact he1 a ha
    have hconj : u * a * u⁻¹ ∈ A := hAn.conj_mem a ha u
    have hstep : (u * a * u⁻¹) ^ k = a ^ k := by
      have h1 : (u * a * u⁻¹) ^ k = ((MulAut.conj u) a) ^ k := by rw [MulAut.conj_apply]
      have h2 : ((MulAut.conj u) a) ^ k = (MulAut.conj u) (a ^ k) := (map_pow _ a k).symm
      have h3 : (MulAut.conj u) (a ^ k) = u * a ^ k * u⁻¹ := MulAut.conj_apply u (a ^ k)
      rw [h1, h2, h3]
      rw [Subgroup.mem_center_iff.mp (h.omega1_le_center hak) u]
      group
    have hmemA : (u * a * u⁻¹) * a⁻¹ ∈ A := A.mul_mem hconj (A.inv_mem ha)
    have hcomm : Commute (u * a * u⁻¹) a⁻¹ := hAb _ hconj _ (A.inv_mem ha)
    have hpow1 : ((u * a * u⁻¹) * a⁻¹) ^ k = 1 := by
      rw [hcomm.mul_pow k, hstep, inv_pow, mul_inv_cancel]
    have hker : (u * a * u⁻¹) * a⁻¹ ∈ powSub A 2 := (hkey _ hmemA).mpr hpow1
    have : ⁅u, a⁆ = (u * a * u⁻¹) * a⁻¹ := by rw [commutatorElement_def]
    rw [this]
    exact hker

end Work.Higman
