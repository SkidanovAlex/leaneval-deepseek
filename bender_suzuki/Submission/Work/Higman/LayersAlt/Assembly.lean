/-
Copyright (c) 2024. All rights reserved.

# Assembly of the layer dichotomy

This file assembles `Work.Higman.layers_card_dichotomy_alt` from

* `Work.Higman.card_layers_eq_card_quotient`: the `ξ`-invariant layers `Z(P) ≤ M ≤ P` of order
  `|Z(P)| ^ 2` correspond to the `ξ`-invariant subgroups of `V = P / Z(P)` of order `2 ^ n`
  (`|Z(P)| = 2 ^ n`, so `|M| = 2 ^ (2n)`);
* `card_subgroups_eq_card_invSubspaces`: the bridge from subgroups of `V` to `𝔽₂`-subspaces of
  `V` (addition on `V` *is* the multiplication of `P / Z(P)`);
* the linear algebra: `exists_two_constituents`, `count_eq_one_add_hom` and
  `hom_card_eq_one_or_card` give `Nat.card (InvSubspaces σ n) = 1 + |Hom_σ(C₂,C₁)|` with
  `|Hom_σ(C₂,C₁)| = 1` or `= |C₂| = 2 ^ n`, whence the dichotomy `2` or `|Z(P)| + 1`.

The group-theoretic input `x ^ 2 ∈ Z(P)` is `Work.Higman.LayersAlt.sq_mem_center_fpf`.
-/

import Mathlib
import Submission.Work.Higman.LayersAlt.Defs
import Submission.Work.Higman.LayersAlt.GroupSide
import Submission.Work.Higman.LayersAlt.count_eq_one_add_hom
import Submission.Work.Higman.LayersAlt.exists_two_constituents
import Submission.Work.Higman.Layers.layers_quotient
import Submission.Work.Higman.Layers.hom_card_eq_one_or_card
import Submission.Work.Higman.LayersAlt.sq_mem_center_fpf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

open scoped commutatorElement

namespace Work.Higman.LayersAlt

variable {P : Type} [Group P] [Finite P]

/-! ## The bridge: subgroups of `V` versus `𝔽₂`-subspaces of `V` -/

/-- Over `𝔽₂`, a subgroup of a group whose multiplication is the addition of an `𝔽₂`-vector space
is the same thing as a submodule.  This is the (carrier-preserving) bijection. -/
def subgroupSubmoduleEquiv {V : Type} [Group V] [AddCommGroup V] [Module (ZMod 2) V]
    (hzero : (0 : V) = 1) (hadd : ∀ a b : V, a + b = a * b) :
    Subgroup V ≃ Submodule (ZMod 2) V where
  toFun N :=
    { carrier := N
      zero_mem' := by simpa [hzero] using N.one_mem
      add_mem' := by
        intro a b ha hb
        rw [hadd a b]
        exact N.mul_mem ha hb
      smul_mem' := by
        intro c x hx
        have h : c = 0 ∨ c = 1 := by revert c; decide
        rcases h with h | h
        · rw [h]; simpa [hzero] using N.one_mem
        · rw [h]; simpa using hx }
  invFun A :=
    { carrier := A
      mul_mem' := by
        intro a b ha hb
        rw [← hadd a b]
        exact A.add_mem ha hb
      one_mem' := by rw [← hzero]; exact A.zero_mem
      inv_mem' := by
        intro a ha
        have h2 : a + a = 0 := by
          have h := two_smul (ZMod 2) a
          rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
          exact h.symm
        have haa : a * a = 1 := by rw [← hadd a a, h2, hzero]
        rw [inv_eq_of_mul_eq_one_right haa]
        exact ha }
  left_inv N := by ext x; rfl
  right_inv A := by ext x; rfl

@[simp] theorem mem_subgroupSubmoduleEquiv {V : Type} [Group V] [AddCommGroup V]
    [Module (ZMod 2) V] (hzero : (0 : V) = 1) (hadd : ∀ a b : V, a + b = a * b)
    (N : Subgroup V) (x : V) :
    x ∈ (subgroupSubmoduleEquiv hzero hadd N : Submodule (ZMod 2) V) ↔ x ∈ N := Iff.rfl

/-- The cardinality of a subspace over `𝔽₂` is `2 ^ finrank`. -/
theorem natCard_submodule_eq_pow_finrank {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (U : Submodule (ZMod 2) V) :
    Nat.card ↥U = 2 ^ Module.finrank (ZMod 2) U := by
  haveI : Module.Finite (ZMod 2) ↥U := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥U), Nat.card_zmod]

/-- **The bridge.**  The `σ`-invariant subgroups of `V` of order `2 ^ n` are the
`σ`-invariant `𝔽₂`-subspaces of dimension `n` (the `σ`-invariance is tested with `τ`, a function
equal to `σ`, because on `V = P / Z(P)` the map `σ` is defined multiplicatively). -/
theorem card_subgroups_eq_card_invSubspaces {V : Type} [Group V] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (hzero : (0 : V) = 1) (hadd : ∀ a b : V, a + b = a * b)
    {σ : V →ₗ[ZMod 2] V} {τ : V → V} (hστ : ∀ x : V, σ x = τ x) (n : ℕ) :
    Nat.card {N : Subgroup V // (∀ y ∈ N, τ y ∈ N) ∧ Nat.card ↥N = 2 ^ n} =
      Nat.card (Layers.InvSubspaces σ n) := by
  classical
  refine Nat.card_congr (Equiv.subtypeEquiv (subgroupSubmoduleEquiv hzero hadd) ?_)
  intro N
  constructor
  · rintro ⟨hinv, hcard⟩
    refine ⟨?_, ?_⟩
    · intro v hv
      rw [hστ v]
      exact hinv v hv
    · have h1 : Nat.card ↥(subgroupSubmoduleEquiv hzero hadd N) =
          2 ^ Module.finrank (ZMod 2) (subgroupSubmoduleEquiv hzero hadd N) :=
        natCard_submodule_eq_pow_finrank _
      have h2 : Nat.card ↥(subgroupSubmoduleEquiv hzero hadd N) = 2 ^ n := hcard
      rw [h1] at h2
      exact Nat.pow_right_injective (by norm_num) h2
  · rintro ⟨hinv, hfr⟩
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [← hστ y]
      exact hinv y hy
    · have h1 : Nat.card ↥(subgroupSubmoduleEquiv hzero hadd N) =
          2 ^ Module.finrank (ZMod 2) (subgroupSubmoduleEquiv hzero hadd N) :=
        natCard_submodule_eq_pow_finrank _
      have h2 : Nat.card ↥(subgroupSubmoduleEquiv hzero hadd N) = 2 ^ n := by rw [h1, hfr]
      exact h2

/-! ## The dichotomy -/

theorem layers_card_dichotomy_aux (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ) :
    Nat.card {M : Subgroup P // IsXiLayer ξ M} = 2 ∨
      Nat.card {M : Subgroup P // IsXiLayer ξ M} =
        Nat.card ↥(Subgroup.center P) + 1 := by
  classical
  obtain ⟨n, hZn⟩ : ∃ n : ℕ, Nat.card ↥(Subgroup.center P) = 2 ^ n :=
    (h.isPGroup.to_subgroup (Subgroup.center P)).exists_card_eq
  have hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P := sq_mem_center_fpf h hξ
  -- `V = P / Z(P)` has exponent two, hence is abelian
  have hmulself : ∀ v : P ⧸ Subgroup.center P, v * v = 1 := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) v
    subst hx
    have h1 : (QuotientGroup.mk (x * x) : P ⧸ Subgroup.center P) = 1 :=
      (QuotientGroup.eq_one_iff (x * x)).mpr (by simpa [pow_two] using hsq x)
    simpa [QuotientGroup.mk'_apply, ← map_mul] using h1
  have hcommQ : ∀ a b : P ⧸ Subgroup.center P, a * b = b * a := by
    intro a b
    have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hmulself a)
    have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hmulself b)
    have hab : (a * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hmulself (a * b))
    rw [← hab, mul_inv_rev, ha, hb]
  letI : CommGroup (P ⧸ Subgroup.center P) :=
    { (inferInstance : Group (P ⧸ Subgroup.center P)) with mul_comm := hcommQ }
  letI hAC : AddCommGroup (P ⧸ Subgroup.center P) :=
    (Additive.ofMul : (P ⧸ Subgroup.center P) ≃ Additive (P ⧸ Subgroup.center P)).addCommGroup
  have hzero : (0 : P ⧸ Subgroup.center P) = 1 := rfl
  have hadd : ∀ a b : P ⧸ Subgroup.center P, a + b = a * b := fun a b => rfl
  have h2v : ∀ v : P ⧸ Subgroup.center P, (2 : ℕ) • v = 0 := by
    intro v
    calc (2 : ℕ) • v = v + v := two_nsmul v
      _ = v * v := hadd v v
      _ = 1 := hmulself v
      _ = 0 := hzero.symm
  letI hMod : Module (ZMod 2) (P ⧸ Subgroup.center P) := AddCommGroup.zmodModule h2v
  -- ## the automorphism `σ` induced by `ξ`
  let σ : (P ⧸ Subgroup.center P) →ₗ[ZMod 2] (P ⧸ Subgroup.center P) :=
    AddMonoidHom.toZModLinearMap 2
      { toFun := ⇑(xiQuot ξ), map_zero' := map_one (xiQuot ξ), map_add' := fun a b => map_mul _ a b }
  have hσ_apply : ∀ a : P ⧸ Subgroup.center P, σ a = xiQuot ξ a := fun _ => rfl
  have hσ_mk : ∀ x : P, σ (QuotientGroup.mk x) = QuotientGroup.mk (ξ x) := fun x => xiQuot_mk ξ x
  have hσ_pow_mk : ∀ (k : ℕ) (x : P),
      (σ ^ k) (QuotientGroup.mk x) = QuotientGroup.mk ((ξ ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
        intro x
        rw [pow_succ', Module.End.mul_apply, ih, hσ_mk, pow_succ', MulAut.mul_apply]
  -- ## `σ ^ k = 1 ↔ ξ ^ k = 1`
  have hpow_iff : ∀ k : ℕ, σ ^ k = 1 ↔ ξ ^ k = 1 := by
    intro k
    constructor
    · intro hσ
      by_contra hne
      obtain ⟨a, b, hab⟩ := h.noncomm
      have haZ : a ∉ Subgroup.center P := fun ha =>
        hab ((Subgroup.mem_center_iff.mp ha b).symm)
      have hσa : (σ ^ k) (QuotientGroup.mk a) = QuotientGroup.mk a := by rw [hσ]; rfl
      have h2 : ((QuotientGroup.mk a : P ⧸ Subgroup.center P)) =
          QuotientGroup.mk ((ξ ^ k) a) := by
        rw [← hσ_pow_mk k a]
        exact hσa.symm
      have h3 : a⁻¹ * ((ξ ^ k) a) ∈ Subgroup.center P := QuotientGroup.eq.mp h2
      have hza : (ξ ^ k) a = a * (a⁻¹ * ((ξ ^ k) a)) := by group
      have hfix := pow_fixes_sq h hξ k h3 hza
      have haa1 : a * a ≠ 1 := by
        intro haa
        have h1 : a ^ 2 = 1 := by rw [pow_two]; exact haa
        exact haZ (h.omega1_le_center (h.mem_omega1.mpr h1))
      exact haa1 (hξ.fpf k hne (a * a) hfix)
    · intro h1
      ext q
      refine Quotient.inductionOn q (fun x => ?_)
      rw [hσ_pow_mk k x, h1]
      rfl
  have hσ_ord : orderOf σ = 2 ^ n - 1 := by
    have hdvd1 : orderOf σ ∣ orderOf ξ := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact (hpow_iff (orderOf ξ)).mpr (pow_orderOf_eq_one ξ)
    have hdvd2 : orderOf ξ ∣ orderOf σ := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact (hpow_iff (orderOf σ)).mp (pow_orderOf_eq_one σ)
    rw [Nat.dvd_antisymm hdvd1 hdvd2, hξ.order, hZn]
  have hσ_sr : Layers.Semiregular σ := by
    intro k v hv hfix
    rw [hpow_iff k]
    by_contra hne
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) v
    subst hx
    have hxZ : x ∉ Subgroup.center P := fun hc =>
      hv (by rw [QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff x).mpr hc)
    have hfix' : (σ ^ k) (QuotientGroup.mk x) = QuotientGroup.mk x := by
      simpa [QuotientGroup.mk'_apply] using hfix
    have h2 : ((QuotientGroup.mk x : P ⧸ Subgroup.center P)) =
        QuotientGroup.mk ((ξ ^ k) x) := by
      rw [← hσ_pow_mk k x]
      exact hfix'.symm
    have h3 : x⁻¹ * ((ξ ^ k) x) ∈ Subgroup.center P := QuotientGroup.eq.mp h2
    have hza : (ξ ^ k) x = x * (x⁻¹ * ((ξ ^ k) x)) := by group
    have hfix2 := pow_fixes_sq h hξ k h3 hza
    have hxx1 : x * x ≠ 1 := by
      intro hxx
      have h1 : x ^ 2 = 1 := by rw [pow_two]; exact hxx
      exact hxZ (h.omega1_le_center (h.mem_omega1.mpr h1))
    exact hxx1 (hξ.fpf k hne (x * x) hfix2)
  have hn1 : 1 ≤ n := by
    have h4 : 4 ≤ Nat.card ↥(Subgroup.center P) := by
      rw [center_eq_omega1_of_fpf h hξ]
      exact h.omega1_card_ge_four
    have h2 : (2:ℕ) ^ 2 ≤ 2 ^ n := by
      calc (2:ℕ) ^ 2 = 4 := by norm_num
        _ ≤ Nat.card ↥(Subgroup.center P) := h4
        _ = 2 ^ n := hZn
    have h3 : ¬ (n < 2) := by
      intro hlt
      have h5 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h5
      omega
    omega
  have hcardV : Nat.card (P ⧸ Subgroup.center P) = 2 ^ (2 * n) := by
    have hcard : Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) =
        Nat.card P := (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)).symm
    have hP : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3 := hξ.card_cube
    have hpos : 0 < Nat.card ↥(Subgroup.center P) := Nat.card_pos
    have h2 : Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) =
        2 ^ (2 * n) * Nat.card ↥(Subgroup.center P) := by
      rw [hcard, hP, hZn, ← pow_mul, ← pow_add]
      congr 1
      omega
    rw [Nat.mul_right_cancel hpos h2]
  -- ## the linear algebra
  obtain ⟨C₁, C₂, h1, h2, hdisj, hsup, hfr1, hfr2⟩ :=
    exists_two_constituents (σ := σ) hn1 hcardV hσ_ord hσ_sr
  have hcount := count_eq_one_add_hom (σ := σ) (n := n) h1 h2 hdisj hsup hfr1 hfr2
  have hhom := Layers.hom_card_eq_one_or_card (σ := σ) h1 h2
  have hbij := Work.Higman.card_layers_eq_card_quotient (ξ := ξ) hZn
  have hbr := card_subgroups_eq_card_invSubspaces (V := P ⧸ Subgroup.center P) hzero hadd
    (σ := σ) (τ := ⇑(xiQuot ξ)) (fun x => hσ_apply x) n
  have hcardC2 : Nat.card ↥C₂ = 2 ^ n := by
    rw [natCard_submodule_eq_pow_finrank (U := C₂), hfr2]
  rcases hhom with hh | hh
  · left
    rw [hbij, hbr, hcount, hh]
  · right
    have hC2Z : Nat.card ↥C₂ = Nat.card ↥(Subgroup.center P) := hcardC2.trans hZn.symm
    rw [hbij, hbr, hcount, hh, hC2Z]
    omega

end Work.Higman.LayersAlt
