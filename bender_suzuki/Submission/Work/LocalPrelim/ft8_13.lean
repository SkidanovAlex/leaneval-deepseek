import Mathlib
import Submission.Work.LocalPrelim.Defs
import Submission.Work.Fitting.Defs
import Submission.Work.SmallRank.Defs
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.frattini_eq_agemo_sup_commutator
import Submission.Work.PGroup.exists_isCriticalSubgroup
import Submission.Work.PGroup.centralizer_inf_eq_of_maximal_normal_abelian
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.commutator_le_frattiniIn
import Submission.Work.PGroup.mRank_mono
import Submission.Work.LocalPrelim.scn3_empty_no_elementaryP3
import Submission.Work.Coprime.trivial_of_trivial_on_frattiniQuotient
import Submission.Work.Coprime.trivial_of_trivial_on_omega1
import Submission.Work.LocalPrelim.ft8_1
import Submission.Work.LocalPrelim.ft8_4_i
import Submission.Work.LocalPrelim.mulAut_commutator_isPGroup_of_elementary_abelian_p2
import Submission.Work.LocalPrelim.mulAut_center_quotient_ker_isPGroup_of_isGroupOfOrderP3ExpP
import Submission.Work.LocalPrelim.scn3_empty_sylow_quotient
import Submission.Work.LocalPrelim.chiefFactor_pFactor_map_quotient
import Submission.Work.SmallRank.card_le_p3_of_exponent_p
import Submission.Work.SmallRank.isExtraspecial_of_isGroupOfOrderP3ExpP
import Submission.Work.Fitting.Main
import Submission.Work.Transitivity.Basic.exists_isSCN_m_top_iff
import Submission.Work.Skeleton.odd_card_of_surjective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.LocalPrelim.ft8_13` — FT Lemma 8.13 (status / plan)

Target: *Suppose `P` is an `S_p`-subgroup of the solvable group `S`, `SCN₃(P) = ∅` and `|S|` is
odd. Then `S'` centralizes every chief `p`-factor of `S`.*  (Feit–Thompson, Pacific J. Math. 13
(1963), Lemma 8.13, Chapter II p. 793; Bender–Glauberman, *Local analysis for the odd order
theorem*, Corollary 4.19.)

## What is proved in this file

* `frattiniIn_top_eq_frattini`, `operator_centralizes_of_centralizes_frattini` (BG Theorem 1.8,
  Burnside: a `p'`-operator group trivial on `R/Φ(R)` is trivial on `R`);
* `centerIn_eq_inf_centralizer`, `commutator_le_center_of_sup_abelian_normal`,
  `commutator_le_center_of_subgroup` (class-two lemmas);
* `mul_pow_eq_one_of_class_two`, `mem_omega_top_iff_of_class_two`,
  `pow_eq_one_of_mem_omega_top_of_class_two` (in a group of class ≤ 2 and `p` odd, `Ω₁` is the
  set of elements of order dividing `p`, and has exponent `p`);
* `omega_map_mulAut`, `omega_characteristic`, `omega_map_injective`,
  `mem_omega_iff_of_subgroup` (`Ωᵢ` is characteristic and commutes with injective images);
* `mulAut_fixes_of_fixes_omega1` — **FT 3.6 for characteristic subgroups**: a `p`-automorphism
  of `p'`-order fixing `Ω₁(C)` pointwise fixes `C` pointwise;
* `restrictMulAut`-style restriction of an automorphism to an invariant subgroup is available
  from `Work.LocalPrelim.ft8_1` (`restrictMulAut`), as is FT Lemma 8.1 (`ft8_1`).

## The proof of `ft8_13`

The target theorem is proved by strong induction on `|S|` (`ft8_13_all`), the step being
`ft8_13_step`, which splits on `O_{p'}(S)`:

* `ft8_13_reduced`: if `O_{p'}(S) = 1` then Bender--Glauberman 4.18 (`S' ≤ O_p(S)`, reproduced
  privately below as `derived_le_pCore_of_no_scn3`) makes `S'` a normal `p`-subgroup of `S`, hence
  nilpotent, and a normal nilpotent subgroup centralizes every chief factor
  (`Work.Fitting.commutator_le_of_isChiefFactor_of_nilpotent`).
* `ft8_13_quotient`: if `O_{p'}(S) ≠ 1` then `O_{p'}(S)` centralizes every chief `p`-factor
  `K/H`, so it suffices to apply the induction hypothesis to `S ⧸ O_{p'}(S)`;
  `scn3_empty_sylow_quotient` transports `𝒮𝒞𝒩₃(P) = ∅` and `chiefFactor_pFactor_map_quotient`
  transports the chief `p`-factor, while `K ⊓ O_{p'}(S) ≤ H` converts the quotient statement back
  to `S` by Dedekind's modular law.

The two Bender--Glauberman inputs needed here are *reproduced privately* in this file (as
`bg_4_17_copy` and `derived_le_pCore_of_no_scn3`) because the modules
`Submission/Work/LocalPrelim/bg_4_17.lean` and `Submission/Work/LocalPrelim/ft8_13_cent.lean`
import *this* module (they use `thompson_char_omega1_subgroup` and
`isPGroup_of_quotient_of_isPGroup`), so they cannot be imported back.  `bg_4_17_copy` is
Bender--Glauberman 4.17: for a `p`-group `R` with no elementary abelian subgroup of order `p³`
and `A ≤ Aut R` solvable of odd order, the derived subgroup `A'` is a `p`-group.
-/

namespace Work.LocalPrelim

universe u

open scoped Classical Pointwise
open commutatorElement

/-! ## `Φ(⊤) = Φ(R)` and BG Theorem 1.8 -/

/-- `Φ(⊤) = Φ(R)`. -/
theorem frattiniIn_top_eq_frattini (R : Type*) [Group R] :
    Work.PGroup.frattiniIn (⊤ : Subgroup R) = frattini R := by
  rw [Work.PGroup.frattiniIn]
  have h : (Subgroup.topEquiv : ↥(⊤ : Subgroup R) ≃* R).toMonoidHom =
      (⊤ : Subgroup R).subtype := by
    ext x; rfl
  rw [← h]
  exact Work.PGroup.frattini_map_mulEquiv Subgroup.topEquiv

/-- **BG Theorem 1.8 (Burnside).** -/
theorem operator_centralizes_of_centralizes_frattini {p : ℕ} (hp : p.Prime)
    {R : Type*} [Group R] [Finite R] (hR : IsPGroup p R)
    {A : Type*} [Group A] [Finite A] [MulDistribMulAction A R]
    (hcop : (Nat.card A).Coprime (Nat.card R))
    (h : ∀ (a : A) (x : R), a • x * x⁻¹ ∈ Work.PGroup.frattiniIn (⊤ : Subgroup R)) :
    ∀ (a : A) (x : R), a • x = x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have key : FT.commutator A (⊤ : Subgroup R) ≤ frattini R := by
    rw [FT.commutator_def', Subgroup.closure_le]
    rintro y ⟨a, x, -, rfl⟩
    have hx' : a • x * x⁻¹ ∈ frattini R := by
      rw [← frattiniIn_top_eq_frattini R]; exact h a x
    have hN : (frattini R).Normal := inferInstance
    have hconj : x⁻¹ * (a • x * x⁻¹) * x ∈ frattini R := by
      have := hN.conj_mem (a • x * x⁻¹) hx' x⁻¹
      simpa using this
    have heq : x⁻¹ * (a • x) = x⁻¹ * (a • x * x⁻¹) * x := by group
    rw [heq]; exact hconj
  exact Work.Coprime.trivial_of_trivial_on_frattiniQuotient A hcop p hR key

/-! ## Class-two toolkit -/

section ClassTwo

variable {G : Type*} [Group G]

/-- In a class-two group (all commutators central), `[v ^ n, u] = [v,u] ^ n`. -/
lemma commutatorElement_pow_left_of_center {u v : G} (h : ⁅v, u⁆ ∈ Subgroup.center G) (n : ℕ) :
    ⁅v ^ n, u⁆ = ⁅v, u⁆ ^ n := by
  have hv : v ^ n * u = ⁅v, u⁆ ^ n * (u * v ^ n) :=
    Work.Coprime.tto_pow_mul_comm_center h n
  rw [commutatorElement_def, hv]
  group

/-- `Z(H)` as a subgroup of the ambient group: `centerIn H = H ⊓ C_G(H)`. -/
theorem centerIn_eq_inf_centralizer (H : Subgroup G) :
    Work.PGroup.centerIn H = H ⊓ Subgroup.centralizer (H : Set G) := by
  rw [Work.PGroup.centerIn]
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨z, hz⟩)
  · intro hx
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, Subgroup.mem_center_iff.mpr (fun y => ?_), rfl⟩
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hxC) (y : G) y.2

/-- A group generated by two normal abelian subgroups is nilpotent of class at most two. -/
theorem commutator_le_center_of_sup_abelian_normal {A B : Subgroup G} (hA : A.Normal)
    (hB : B.Normal) (hAc : IsMulCommutative A) (hBc : IsMulCommutative B) :
    ⁅A ⊔ B, A ⊔ B⁆ ≤ Work.PGroup.centerIn (A ⊔ B) := by
  haveI := hA
  haveI := hB
  have hAA : ⁅A, A⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr hAc
  have hBB : ⁅B, B⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr hBc
  have hAB_le : ⁅A ⊔ B, A ⊔ B⁆ ≤ ⁅A, B⁆ := by
    rw [Subgroup.commutator_sup_right A B (A ⊔ B), Subgroup.commutator_sup_left A A B,
      Subgroup.commutator_sup_left B A B, hAA, hBB, Subgroup.commutator_comm B A]
    simp
  rw [centerIn_eq_inf_centralizer]
  have hcA0 : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAA
  have hcB0 : B ≤ Subgroup.centralizer (B : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBB
  have hleA : ⁅A ⊔ B, A ⊔ B⁆ ≤ Subgroup.centralizer (A : Set G) :=
    hAB_le.trans ((Subgroup.commutator_le_left A B).trans hcA0)
  have hleB : ⁅A ⊔ B, A ⊔ B⁆ ≤ Subgroup.centralizer (B : Set G) :=
    hAB_le.trans ((Subgroup.commutator_le_right A B).trans hcB0)
  have hcent : ⁅A ⊔ B, A ⊔ B⁆ ≤ Subgroup.centralizer (((A ⊔ B : Subgroup G)) : Set G) := by
    refine (Subgroup.le_centralizer_iff (H := ⁅A ⊔ B, A ⊔ B⁆)
      (K := (A ⊔ B : Subgroup G))).mpr ?_
    exact sup_le (Subgroup.le_centralizer_iff.mp hleA) (Subgroup.le_centralizer_iff.mp hleB)
  refine le_inf ?_ hcent
  exact hAB_le.trans ((Subgroup.commutator_le_right A B).trans le_sup_right)

end ClassTwo

/-! ## The class-two `Ω₁` computation -/

section Intrinsic

/-- In a group of class at most two, the product of two elements of order dividing `p`
(`p` odd) has order dividing `p`. -/
theorem mul_pow_eq_one_of_class_two {H : Type*} [Group H] {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hc : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ Subgroup.center H) {x y : H}
    (hx : x ^ p = 1) (hy : y ^ p = 1) : (x * y) ^ p = 1 := by
  have hp2 : p ≠ 2 := by obtain ⟨k, hk⟩ := hpodd; omega
  have hmem : ⁅y, x⁆ ∈ Subgroup.center H :=
    hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x))
  have hcx : ⁅y, x⁆ ^ p = 1 := by
    rw [← commutatorElement_pow_left_of_center hmem p, hy, commutatorElement_one_left]
  exact Work.Coprime.tto_dpow_eq_one hmem (by rw [hx, hy, one_mul]) hcx hp hp2

/-- In a group of class at most two, `Ω₁` is exactly the set of elements of order dividing `p`. -/
theorem mem_omega_top_iff_of_class_two {H : Type*} [Group H] {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hc : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ Subgroup.center H) {x : H} :
    x ∈ Work.PGroup.omega p 1 (⊤ : Subgroup H) ↔ x ^ p = 1 := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => simpa using hy.2
    | one => simp
    | mul a b _ _ iha ihb => exact mul_pow_eq_one_of_class_two hp hpodd hc iha ihb
    | inv a _ iha => rw [inv_pow, iha, inv_one]
  · intro hx
    exact Subgroup.subset_closure ⟨Subgroup.mem_top x, by simpa using hx⟩

/-- `Ω₁` of a group of class at most two and odd prime `p` has exponent `p`. -/
theorem pow_eq_one_of_mem_omega_top_of_class_two {H : Type*} [Group H] {p : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hc : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ Subgroup.center H) {x : H}
    (hx : x ∈ Work.PGroup.omega p 1 (⊤ : Subgroup H)) : x ^ p = 1 :=
  (mem_omega_top_iff_of_class_two hp hpodd hc).mp hx

end Intrinsic

/-! ## `Ωᵢ` is characteristic -/

/-- `Ωᵢ` commutes with `Subgroup.map` along an automorphism. -/
theorem omega_map_mulAut {G : Type*} [Group G] (p i : ℕ) (C : Subgroup G) (φ : MulAut G) :
    (Work.PGroup.omega p i C).map φ.toMonoidHom =
      Work.PGroup.omega p i (C.map φ.toMonoidHom) := by
  have hs : φ.toMonoidHom '' {x : G | x ∈ C ∧ x ^ (p ^ i) = 1} =
      {y : G | y ∈ C.map φ.toMonoidHom ∧ y ^ (p ^ i) = 1} := by
    ext y; constructor
    · rintro ⟨x, ⟨hxC, hx1⟩, rfl⟩
      refine ⟨⟨x, hxC, rfl⟩, ?_⟩
      have h2 : φ (x ^ (p ^ i)) = 1 := by rw [hx1, map_one]
      simpa using h2
    · rintro ⟨⟨x, hxC, rfl⟩, hy1⟩
      refine ⟨x, ⟨hxC, ?_⟩, rfl⟩
      have h2 : φ (x ^ (p ^ i)) = 1 := by simpa using hy1
      exact φ.injective (by rw [h2, map_one])
  rw [Work.PGroup.omega, Work.PGroup.omega, MonoidHom.map_closure, hs]

/-- `Ωᵢ(C)` is characteristic in `C`. -/
theorem omega_characteristic {G : Type*} [Group G] (p i : ℕ) {C : Subgroup G}
    (hC : C.Characteristic) : (Work.PGroup.omega p i C).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  rw [omega_map_mulAut, (Subgroup.characteristic_iff_map_eq.mp hC) φ]

/-! ## `Ω₁` of a class-two subgroup -/

/-- `Ωᵢ` commutes with `Subgroup.map` along an injective homomorphism. -/
theorem omega_map_injective {G N : Type*} [Group G] [Group N] (p i : ℕ) (C : Subgroup G)
    (f : G →* N) (hf : Function.Injective f) :
    (Work.PGroup.omega p i C).map f = Work.PGroup.omega p i (C.map f) := by
  have hs : f '' {x : G | x ∈ C ∧ x ^ (p ^ i) = 1} =
      {y : N | y ∈ C.map f ∧ y ^ (p ^ i) = 1} := by
    ext y; constructor
    · rintro ⟨x, ⟨hxC, hx1⟩, rfl⟩
      refine ⟨⟨x, hxC, rfl⟩, ?_⟩
      have h2 : f (x ^ (p ^ i)) = 1 := by rw [hx1, map_one]
      simpa using h2
    · rintro ⟨⟨x, hxC, rfl⟩, hy1⟩
      refine ⟨x, ⟨hxC, ?_⟩, rfl⟩
      apply hf
      rw [map_one, map_pow, hy1]
  rw [Work.PGroup.omega, Work.PGroup.omega, MonoidHom.map_closure, hs]

/-- A subgroup with `⁅C,C⁆ ≤ Z(C)` is a group of class at most two. -/
theorem commutator_le_center_of_subgroup {G : Type*} [Group G] {C : Subgroup G}
    (hc : ⁅C, C⁆ ≤ Work.PGroup.centerIn C) :
    ⁅(⊤ : Subgroup ↥C), (⊤ : Subgroup ↥C)⁆ ≤ Subgroup.center ↥C := by
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_center_iff]
  intro c
  apply Subtype.ext
  have hmem := hc (Subgroup.commutator_mem_commutator b.2 a.2)
  rw [centerIn_eq_inf_centralizer] at hmem
  have hcent : ⁅(b : G), (a : G)⁆ ∈ Subgroup.centralizer (C : Set G) :=
    (Subgroup.mem_inf.mp hmem).2
  have hcc : Commute (c : G) ⁅(b : G), (a : G)⁆ :=
    (Subgroup.mem_centralizer_iff.mp hcent) (c : G) c.2
  have h1 : ⁅(a : G), (b : G)⁆ = ⁅(b : G), (a : G)⁆⁻¹ :=
    (commutatorElement_inv (b : G) (a : G)).symm
  have hgoal : (c : G) * ⁅(a : G), (b : G)⁆ = ⁅(a : G), (b : G)⁆ * (c : G) := by
    rw [h1, hcc.inv_right.eq]
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def] using hgoal

/-- In a class-two subgroup, `Ω₁` has exponent `p`. -/
theorem omega_subgroup_pow_eq_one {G : Type*} [Group G] {C : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hc : ⁅C, C⁆ ≤ Work.PGroup.centerIn C) {x : G}
    (hx : x ∈ Work.PGroup.omega p 1 C) : x ^ p = 1 := by
  have hc' := commutator_le_center_of_subgroup hc
  have hmap : (Work.PGroup.omega p 1 (⊤ : Subgroup ↥C)).map C.subtype = Work.PGroup.omega p 1 C := by
    have h := omega_map_injective p 1 (⊤ : Subgroup ↥C) C.subtype C.subtype_injective
    have hC : (⊤ : Subgroup ↥C).map C.subtype = C := by
      ext x; constructor
      · intro hx
        obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
        exact y.2
      · intro hx
        exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    rwa [hC] at h
  rw [← hmap] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hyp : (y : ↥C) ^ p = 1 := pow_eq_one_of_mem_omega_top_of_class_two hp hpodd hc' hy
  rw [← hyx]
  exact congrArg Subtype.val hyp

/-- `x ∈ Ω₁(C) ↔ x ∈ C ∧ x^p = 1` for a class-two subgroup `C`. -/
theorem mem_omega_iff_of_subgroup {G : Type*} [Group G] {C : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hc : ⁅C, C⁆ ≤ Work.PGroup.centerIn C) {x : G} :
    x ∈ Work.PGroup.omega p 1 C ↔ x ∈ C ∧ x ^ p = 1 :=
  ⟨fun hx => ⟨Work.PGroup.omega_le p 1 C hx, omega_subgroup_pow_eq_one hp hpodd hc hx⟩,
    fun hx => Subgroup.subset_closure ⟨hx.1, by simpa using hx.2⟩⟩

/-! ## The `Ω₁` of a critical subgroup (FT 8.2 / BG Theorem 1.13) -/

/-! ## The `Ω₁` of a critical subgroup (FT 8.2 / BG Theorem 1.13) -/

/-- A `p'`-automorphism of a `p`-group that fixes `Ω₁` of a characteristic subgroup pointwise
fixes the subgroup pointwise (FT 3.6). -/
theorem mulAut_fixes_of_fixes_omega1 {R : Type*} [Group R] [Finite R] {p : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hR : IsPGroup p R) {C : Subgroup R} (hCchar : C.Characteristic)
    {α : MulAut R} (hfix : ∀ c : R, c ∈ Work.PGroup.omega p 1 C → α c = c)
    (hcop : ¬ p ∣ orderOf α) : ∀ c : R, c ∈ C → α c = c := by
  have hp2 : p ≠ 2 := by obtain ⟨k, hk⟩ := hpodd; omega
  have hCmap : C.map α.toMonoidHom = C := (Subgroup.characteristic_iff_map_eq.mp hCchar) α
  have hCmap' : C.map α.symm.toMonoidHom = C :=
    (Subgroup.characteristic_iff_map_eq.mp hCchar) α.symm
  let γ : MulAut ↥C :=
    { toFun := fun x => ⟨α (x : R), by
        have h1 : α (x : R) ∈ C.map α.toMonoidHom := ⟨(x : R), x.2, rfl⟩
        rwa [hCmap] at h1⟩
      invFun := fun x => ⟨α.symm (x : R), by
        have h1 : α.symm (x : R) ∈ C.map α.symm.toMonoidHom := ⟨(x : R), x.2, rfl⟩
        rwa [hCmap'] at h1⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (map_mul α (x : R) (y : R)) }
  have hγcoe : ∀ x : ↥C, ((γ x : ↥C) : R) = α (x : R) := fun x => rfl
  have hγpow : ∀ n : ℕ, ∀ x : ↥C, (((γ ^ n) x : ↥C) : R) = (α ^ n) (x : R) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih (γ x), hγcoe x]
      simp [pow_succ, MulAut.mul_apply]
  have hγorder : orderOf γ ∣ orderOf α := by
    rw [orderOf_dvd_iff_pow_eq_one]
    ext x
    rw [hγpow, pow_orderOf_eq_one]
    rfl
  have hmap2 : (FT.omega1 p ↥C).map C.subtype = Work.PGroup.omega p 1 C := by
    have hset : C.subtype '' {x : ↥C | x ^ p = 1} = {y : R | y ∈ C ∧ y ^ (p ^ 1) = 1} := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, by simpa using congrArg (fun z : ↥C => (z : R)) hx⟩
      · rintro ⟨hy, hyp⟩
        exact ⟨⟨y, hy⟩, by simpa using hyp, rfl⟩
    rw [FT.omega1, Work.PGroup.omega, MonoidHom.map_closure, hset]
  have key : ∀ n : ℕ, ∀ x : ↥C, (x : R) ∈ Work.PGroup.omega p 1 C → (γ ^ n) x = x := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      have hγxH : (γ x : R) ∈ Work.PGroup.omega p 1 C := by
        rw [hγcoe, hfix (x : R) hx]
        exact hx
      rw [pow_succ, MulAut.mul_apply, ih (γ x) hγxH]
      exact Subtype.ext (hfix (x : R) hx)
  have homega : FT.IsTrivialOn ↥(Subgroup.zpowers γ) ↥(FT.omega1 p ↥C) := by
    intro i x
    have hxH : (((x : ↥(FT.omega1 p ↥C)) : ↥C) : R) ∈ Work.PGroup.omega p 1 C := by
      rw [← hmap2]
      exact Subgroup.mem_map.mpr ⟨_, (x : ↥(FT.omega1 p ↥C)).2, rfl⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp i.2
    show ((i : ↥(Subgroup.zpowers γ)) : MulAut ↥C) • x = x
    rw [← hm]
    have hgoal : (γ ^ m) ((x : ↥(FT.omega1 p ↥C)) : ↥C) = ((x : ↥(FT.omega1 p ↥C)) : ↥C) := by
      cases m with
      | ofNat n => exact key n (x : ↥C) hxH
      | negSucc n =>
        rw [zpow_negSucc]
        have h1 : (γ ^ (n + 1)) ((x : ↥(FT.omega1 p ↥C)) : ↥C) =
            ((x : ↥(FT.omega1 p ↥C)) : ↥C) := key (n + 1) (x : ↥C) hxH
        have h3 := congrArg (fun y => (((γ ^ (n + 1))⁻¹ : MulAut ↥C) y)) h1
        simpa using h3.symm
    exact Subtype.ext hgoal
  have hcopC : (Nat.card ↥(Subgroup.zpowers γ)).Coprime (Nat.card ↥C) := by
    rw [Nat.card_zpowers]
    have hpγ : ¬ p ∣ orderOf γ := fun hd => hcop (hd.trans hγorder)
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hR.to_subgroup C)
    rw [hk]
    exact (hp.coprime_iff_not_dvd.mpr hpγ).symm.pow_right k
  have htriv := Work.Coprime.trivial_of_trivial_on_omega1 ↥(Subgroup.zpowers γ)
    hcopC p hp hp2 (hR.to_subgroup C) homega
  intro c hc
  exact congrArg Subtype.val (htriv ⟨γ, Subgroup.mem_zpowers γ⟩ ⟨c, hc⟩)

/-- A `p'`-automorphism fixing a critical subgroup pointwise is trivial (FT 8.2 (ii)). -/
theorem mulAut_eq_one_of_fixes_critical {R : Type*} [Group R] [Finite R] {p : ℕ}
    (hp : p.Prime) (hR : IsPGroup p R) {C : Subgroup R}
    (hCchar : C.Characteristic) (hCne : C ≠ ⊥)
    (hCfr : Work.PGroup.frattiniIn C ≤ Work.PGroup.centerIn C)
    (hCcomm : ⁅(⊤ : Subgroup R), C⁆ ≤ Work.PGroup.centerIn C)
    (hCsc : Subgroup.centralizer (C : Set R) ≤ C)
    {α : MulAut R} (hfixC : ∀ c : R, c ∈ C → α c = c) (hα : α ≠ 1) :
    p ∣ orderOf α := by
  by_contra hpdvd
  have hCcommC : ⁅(⊤ : Subgroup R), C⁆ ≤ C :=
    hCcomm.trans (by rw [centerIn_eq_inf_centralizer]; exact inf_le_left)
  -- `x⁻¹ α(x) ∈ C` for every `x`, because `α` fixes every `[x,c]`, `c ∈ C`.
  have hu : ∀ x : R, x⁻¹ * α x ∈ C := by
    intro x
    refine hCsc ?_
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hxc : ⁅x, c⁆ ∈ C :=
      hCcommC (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) hc)
    have h1 : ⁅α x, c⁆ = ⁅x, c⁆ := by
      have hm : α (⁅x, c⁆) = ⁅α x, α c⁆ := map_commutatorElement α.toMonoidHom x c
      rw [hfixC _ hxc, hfixC c hc] at hm
      exact hm.symm
    have hrel : α x * c * (α x)⁻¹ = x * c * x⁻¹ := by
      have h2 : α x * c * (α x)⁻¹ * c⁻¹ = x * c * x⁻¹ * c⁻¹ := by
        simpa only [commutatorElement_def] using h1
      exact mul_right_cancel h2
    calc c * (x⁻¹ * α x) = x⁻¹ * (x * c * x⁻¹) * α x := by group
      _ = x⁻¹ * (α x * c * (α x)⁻¹) * α x := by rw [hrel]
      _ = (x⁻¹ * α x) * c := by group
  have hall : ∀ x : R, α x = x := by
    intro x
    have hux : α (x⁻¹ * α x) = x⁻¹ * α x := hfixC _ (hu x)
    have hax : α x = x * (x⁻¹ * α x) := by group
    have key : ∀ k : ℕ, (α ^ k) x = x * (x⁻¹ * α x) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc (α ^ (k+1)) x = α ((α ^ k) x) := by rw [pow_succ']; rfl
          _ = α (x * (x⁻¹ * α x) ^ k) := by rw [ih]
          _ = α x * (α (x⁻¹ * α x)) ^ k := by rw [map_mul, map_pow]
          _ = (x * (x⁻¹ * α x)) * (x⁻¹ * α x) ^ k := by rw [hux]; nth_rw 1 [hax]
          _ = x * (x⁻¹ * α x) ^ (k+1) := by rw [pow_succ', mul_assoc]
    have hpow : (x⁻¹ * α x) ^ orderOf α = 1 := by
      have h := key (orderOf α)
      rw [pow_orderOf_eq_one, MulAut.one_apply] at h
      exact mul_left_cancel (by rw [← h, mul_one])
    have hdiv : orderOf (x⁻¹ * α x) ∣ orderOf α := orderOf_dvd_iff_pow_eq_one.mpr hpow
    obtain ⟨j, hj⟩ := hR.exists_pow_pow_eq_one (x⁻¹ * α x)
    have hdivp : orderOf (x⁻¹ * α x) ∣ p ^ j := orderOf_dvd_iff_pow_eq_one.mpr hj
    have hcop : Nat.Coprime (orderOf (x⁻¹ * α x)) (p ^ j) :=
      Nat.Coprime.coprime_dvd_left hdiv ((hp.coprime_iff_not_dvd.mpr hpdvd).symm.pow_right j)
    have hd1 : orderOf (x⁻¹ * α x) = 1 := hcop.eq_one_of_dvd hdivp
    have hu1 : x⁻¹ * α x = 1 := orderOf_eq_one_iff.mp hd1
    rw [inv_mul_eq_one] at hu1
    exact hu1.symm
  exact hα (MulEquiv.ext hall)

/-- An extension of a `p`-group by a `p`-group is a `p`-group. -/
theorem isPGroup_of_quotient_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p ↥N) (hQ : IsPGroup p (G ⧸ N)) :
    IsPGroup p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hN
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hQ
  refine IsPGroup.iff_card.mpr ⟨a + b, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, ha, hb, pow_add, mul_comm]

/-- `NoElementaryP3` passes to subgroups. -/
theorem noElementaryP3_of_le {p : ℕ} {X : Type*} [Group X] (h : Work.SmallRank.NoElementaryP3 p X)
    {Y : Subgroup X} : Work.SmallRank.NoElementaryP3 p ↥Y := by
  rintro ⟨E, hE, hEcard⟩
  exact h ⟨E.map Y.subtype, Work.PGroup.isElementaryAbelian_map Y.subtype_injective hE, by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hEcard]⟩

/-- **BG Theorem 1.13**, Feit--Thompson Lemma 8.2 in the `Ω₁` form: for `p` odd and `R` a
non-trivial finite `p`-group there is a characteristic subgroup `H` with `[H,R] ≤ Z(H)`,
`[H,H] ≤ Z(H)`, exponent `p`, and such that `p'`-automorphisms of `R` fixing `H` pointwise are
trivial. -/
theorem thompson_char_omega1_subgroup {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (R : Type*) [Group R] [Finite R] (hR : IsPGroup p R) [Nontrivial R] :
    ∃ H : Subgroup R, H.Characteristic ∧ H ≠ ⊥ ∧
      ⁅H, ⊤⁆ ≤ Work.PGroup.centerIn H ∧ ⁅H, H⁆ ≤ Work.PGroup.centerIn H ∧
      (∀ x : H, x ^ p = 1) ∧
      (∀ α : MulAut R, (∀ h : R, h ∈ H → α h = h) → α ≠ 1 → p ∣ orderOf α) := by
  obtain ⟨C, hCchar, hCne, hCfr, hCcomm, hCsc⟩ :=
    Work.PGroup.exists_characteristic_critical_intrinsic (H := R) hp hR
  have hCp : IsPGroup p ↥C := hR.to_subgroup C
  have hcc : ⁅C, C⁆ ≤ Work.PGroup.centerIn C :=
    (Work.PGroup.commutator_le_frattiniIn hp C hCp).trans hCfr
  have hHchar : (Work.PGroup.omega p 1 C).Characteristic := omega_characteristic p 1 hCchar
  haveI hHnorm : (Work.PGroup.omega p 1 C).Normal := by haveI := hHchar; infer_instance
  refine ⟨Work.PGroup.omega p 1 C, hHchar, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Ω₁(C) ≠ ⊥`
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Nontrivial ↥C := (Subgroup.nontrivial_iff_ne_bot C).mpr hCne
    haveI hZr : Nontrivial ↥(Subgroup.center ↥C) := IsPGroup.center_nontrivial hCp
    obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥C))
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hCp) (z : ↥C)
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exfalso
        have h1 : orderOf (z : ↥C) = 1 := by rw [hk, h, pow_zero]
        exact hz1 (Subtype.ext (orderOf_eq_one_iff.mp h1))
      · exact h
    set y : ↥C := (z : ↥C) ^ p ^ (k - 1) with hy
    have hyp : y ^ p = 1 := by
      rw [hy, ← pow_mul]
      have hmul : p ^ (k - 1) * p = p ^ k := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
      rw [hmul, ← hk, pow_orderOf_eq_one]
    have hyne : y ≠ 1 := by
      intro h1
      have hd : orderOf (z : ↥C) ∣ p ^ (k - 1) := by
        rw [orderOf_dvd_iff_pow_eq_one, ← hy]; exact h1
      rw [hk] at hd
      have hle : p ^ k ≤ p ^ (k - 1) := Nat.le_of_dvd (pow_pos hp.pos _) hd
      have : k ≤ k - 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
      omega
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨(y : R), Work.PGroup.subset_omega y.2 (by simpa using congrArg Subtype.val hyp)⟩, ?_⟩
    intro h1
    have h2 : (y : R) = 1 := congrArg (fun w : ↥(Work.PGroup.omega p 1 C) => (w : R)) h1
    exact hyne (Subtype.ext h2)
  · -- `[Ω₁(C), R] ≤ Z(Ω₁(C))`
    have hHC : ⁅Work.PGroup.omega p 1 C, (⊤ : Subgroup R)⁆ ≤ Work.PGroup.centerIn C :=
      (Subgroup.commutator_mono_left (Work.PGroup.omega_le p 1 C)).trans (by
        rw [Subgroup.commutator_comm]; exact hCcomm)
    have hcent : ⁅Work.PGroup.omega p 1 C, (⊤ : Subgroup R)⁆ ≤
        Subgroup.centralizer (Work.PGroup.omega p 1 C : Set R) :=
      (hHC.trans (by rw [centerIn_eq_inf_centralizer]; exact inf_le_right)).trans
        (Subgroup.centralizer_le (Work.PGroup.omega_le p 1 C))
    rw [centerIn_eq_inf_centralizer]
    exact le_inf (Subgroup.commutator_le_left _ _) hcent
  · -- `[Ω₁(C), Ω₁(C)] ≤ Z(Ω₁(C))`
    have hHH : ⁅Work.PGroup.omega p 1 C, Work.PGroup.omega p 1 C⁆ ≤ Work.PGroup.centerIn C :=
      (Subgroup.commutator_mono (Work.PGroup.omega_le p 1 C) (Work.PGroup.omega_le p 1 C)).trans hcc
    have hcent : ⁅Work.PGroup.omega p 1 C, Work.PGroup.omega p 1 C⁆ ≤
        Subgroup.centralizer (Work.PGroup.omega p 1 C : Set R) :=
      (hHH.trans (by rw [centerIn_eq_inf_centralizer]; exact inf_le_right)).trans
        (Subgroup.centralizer_le (Work.PGroup.omega_le p 1 C))
    rw [centerIn_eq_inf_centralizer]
    exact le_inf (Subgroup.commutator_le_left _ _) hcent
  · -- exponent `p`
    intro x
    exact Subtype.ext ((mem_omega_iff_of_subgroup hp hpodd hcc).mp x.2).2
  · -- the kernel condition
    intro α hfix hne
    by_contra hpdvd
    exact hpdvd (mulAut_eq_one_of_fixes_critical hp hR hCchar hCne hCfr hCcomm hCsc
      (mulAut_fixes_of_fixes_omega1 hp hpodd hR hCchar hfix hpdvd) hne)

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-! ## Self-contained copies of the two Bender--Glauberman inputs

The modules `Submission/Work/LocalPrelim/bg_4_17.lean` and
`Submission/Work/LocalPrelim/ft8_13_cent.lean` import *this* module (for
`thompson_char_omega1_subgroup` and `isPGroup_of_quotient_of_isPGroup`), so this module cannot
import them back.  The two results that the proof of `ft8_13` needs from them are therefore
reproduced here, privately (so that no declaration name is duplicated):

* `bg_4_17_copy` -- Bender--Glauberman 4.17: if `R` is a `p`-group with no elementary abelian
  subgroup of order `p ^ 3` and `A ≤ Aut R` is solvable of odd order, then `A'` is a `p`-group;
* `derived_le_pCore_of_no_scn3` -- Bender--Glauberman 4.18 (`S' ≤ O_p(S)` when `O_{p'}(S) = 1`),
  which follows from 4.17 as in the source file.
-/

/-! ### Elementary helpers -/

/-- `Nat.card` of the range of a monoid hom divides `Nat.card` of its domain. -/
private lemma card_range_dvd_card {G N : Type*} [Group G] [Group N] [Finite G] (f : G →* N) :
    Nat.card ↥f.range ∣ Nat.card G := by
  haveI : f.ker.Normal := f.normal_ker
  haveI : Finite ↥f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have h1 : Nat.card ↥f.ker * f.ker.index = Nat.card G := Subgroup.card_mul_index f.ker
  have h2 : f.ker.index = Nat.card ↥f.range := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  exact ⟨Nat.card ↥f.ker, by rw [← h1, h2, mul_comm]⟩

/-- An extension of a `p`-group by a `p`-group is a `p`-group (cardinality form). -/
private lemma isPGroup_of_ker_of_range {p : ℕ} (hp : p.Prime) {G N : Type*} [Group G] [Group N]
    [Finite G] (f : G →* N) (hker : IsPGroup p ↥f.ker) (hrange : IsPGroup p ↥f.range) :
    IsPGroup p G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : f.ker.Normal := f.normal_ker
  haveI : Finite ↥f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  rw [IsPGroup.iff_card] at hker hrange ⊢
  obtain ⟨a, ha⟩ := hker
  obtain ⟨b, hb⟩ := hrange
  refine ⟨a + b, ?_⟩
  have h1 : Nat.card ↥f.ker * f.ker.index = Nat.card G := Subgroup.card_mul_index f.ker
  have h2 : f.ker.index = Nat.card ↥f.range := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [← h1, h2, ha, hb, ← pow_add]

/-- A group admitting an injective homomorphism into a `p`-group is a `p`-group. -/
private lemma isPGroup_of_injective {p : ℕ} {G N : Type*} [Group G] [Group N]
    (hN : IsPGroup p N) (f : G →* N) (hf : Function.Injective f) : IsPGroup p G := by
  intro g
  obtain ⟨n, hn⟩ := hN (f g)
  exact ⟨n, hf (by rw [map_pow, map_one]; exact hn)⟩

/-- A natural number `≠ 0, 1` all of whose prime divisors equal `p` is a power of `p`. -/
private lemma exists_pow_of_prime_dvd {p : ℕ} (hp : p.Prime) :
    ∀ n, n ≠ 0 → (∀ q, q.Prime → q ∣ n → q = p) → ∃ k, n = p ^ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn h
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exact absurd h0 hn
    rcases Nat.eq_or_lt_of_le hpos with h1 | hgt
    · exact ⟨0, by rw [← h1, pow_zero]; rfl⟩
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    have hqp : q = p := h q hq hqd
    have hqdp : p ∣ n := hqp ▸ hqd
    obtain ⟨m, rfl⟩ := hqdp
    have hm0 : m ≠ 0 := by rintro rfl; simp at hn
    have hmlt : m < p * m := by
      have h1 : 1 * m < p * m :=
        Nat.mul_lt_mul_of_pos_right hp.one_lt (Nat.pos_of_ne_zero hm0)
      simpa using h1
    obtain ⟨k, hk⟩ := ih m hmlt hm0 (fun r hr hrd => h r hr (hrd.trans ⟨p, mul_comm p m⟩))
    exact ⟨k + 1, by rw [hk, pow_succ, mul_comm]⟩

/-- Elementarity is preserved by the inclusion `↥H ↪ G`. -/
private lemma isElementaryAbelian_map_subtype {G : Type*} [Group G] {p : ℕ} {H : Subgroup G}
    {E : Subgroup ↥H} (h : Work.PGroup.IsElementaryAbelian p E) :
    Work.PGroup.IsElementaryAbelian p (E.map H.subtype) :=
  ⟨Work.PGroup.map_subtype_isMulCommutative H E h.1, fun x => by
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
    have hy' : (y ^ p : ↥H) = 1 := by
      simpa using congrArg (fun z : ↥E => (z : ↥H)) (h.2 ⟨y, hy⟩)
    apply Subtype.ext
    show ((x : G)) ^ p = 1
    rw [← hyx, ← map_pow H.subtype y p, hy', map_one]⟩


/-! ### Automorphisms of a small class-two group of exponent `p` -/

/-- **Auxiliary lemma.**  Let `p` be an odd prime and `H` a finite group of exponent `p` and
nilpotency class at most two with `|H| ≤ p ^ 3` and no elementary abelian subgroup of order
`p ^ 3`.  Then the derived subgroup of every odd-order subgroup `L ≤ Aut H` is a `p`-group.

This is the group-theoretic core of BG 4.17: `H` is elementary abelian of rank `≤ 2` (in which
case the claim is the GL₂ statement `mulAut_commutator_isPGroup_of_elementary_abelian_p2`), or
`H` is the non-abelian group of order `p ^ 3` and exponent `p`, in which case the kernel of
`Aut H → Aut (H / Z(H))` is a `p`-group
(`mulAut_center_quotient_ker_isPGroup_of_isGroupOfOrderP3ExpP`) and the image is a subgroup of the
automorphism group of an elementary abelian group of order `p ^ 2`. -/
private theorem commutator_isPGroup_of_odd_le_mulAut
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) {H : Type*} [Group H] [Finite H]
    (hexp : ∀ x : H, x ^ p = 1)
    (hclass : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ Subgroup.center H)
    (hcard : Nat.card H ≤ p ^ 3)
    (hnoE : Work.SmallRank.NoElementaryP3 p H)
    (L : Subgroup (MulAut H)) (hodd : Odd (Nat.card L)) :
    IsPGroup p ↥(⁅L, L⁆) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hHp : IsPGroup p H := fun x => ⟨1, by simpa using hexp x⟩
  -- a `p`-group of order at most `p ^ 2` and exponent `p` is commutative
  have hsmall : Nat.card H ≤ p ^ 2 → IsMulCommutative H := by
    intro hle
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hHp
    have hm2 : m ≤ 2 := by
      rw [hm] at hle
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    interval_cases m
    · have h1 : Nat.card H = 1 := by rw [hm, pow_zero]
      haveI : Subsingleton H := (Nat.card_eq_one_iff_unique.mp h1).1
      exact isMulCommutative_iff.mpr fun a b => Subsingleton.elim _ _
    · exact (isCyclic_of_prime_card (p := p) (by simpa using hm)).isMulCommutative
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hm
  by_cases hcomm : IsMulCommutative H
  · -- `H` is elementary abelian of order at most `p ^ 2`
    have hcard2 : Nat.card H ≤ p ^ 2 := by
      by_contra h
      rw [not_le] at h
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hHp
      have hk3 : k ≤ 3 := by
        rw [hk] at hcard
        exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard
      have hk2 : 2 < k := by
        rw [hk] at h
        exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp h
      have hk' : k = 3 := by omega
      refine hnoE ⟨⊤, ⟨?_, ?_⟩, ?_⟩
      · exact isMulCommutative_iff.mpr
          (fun a b => Subtype.ext (isMulCommutative_iff.mp hcomm (a : H) (b : H)))
      · intro x
        exact Subtype.ext (by simpa using hexp (x : H))
      · have h1 : Nat.card ↥(⊤ : Subgroup H) = Nat.card H :=
          Nat.card_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H).toEquiv
        rw [h1, hk, hk']
    exact mulAut_commutator_isPGroup_of_elementary_abelian_p2 hcomm hexp hcard2 L hodd
  · -- `H` is the non-abelian group of order `p ^ 3` and exponent `p`
    have hcard3 : Nat.card H = p ^ 3 := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hHp
      have hk3 : k ≤ 3 := by
        rw [hk] at hcard
        exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard
      have hk3' : 3 ≤ k := by
        by_contra h
        rw [not_le] at h
        have hle : Nat.card H ≤ p ^ 2 := by
          rw [hk]
          exact Nat.pow_le_pow_right hp.pos (by omega)
        exact hcomm (hsmall hle)
      have : k = 3 := by omega
      rw [hk, this]
    have hH : Work.SmallRank.IsGroupOfOrderP3ExpP p H := ⟨hcard3, hexp, hcomm⟩
    obtain ⟨ρ, hρapp, hρker⟩ :=
      Work.LocalPrelim.mulAut_center_quotient_ker_isPGroup_of_isGroupOfOrderP3ExpP hp hH
    have hZcard : Nat.card (Subgroup.center H) = p :=
      (Work.SmallRank.isExtraspecial_of_isGroupOfOrderP3ExpP hp hH).2
    -- the quotient `H ⧸ Z(H)` is elementary abelian of order `p ^ 2`
    have hVcomm : IsMulCommutative (H ⧸ Subgroup.center H) := by
      rw [isMulCommutative_iff]
      intro x y
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) y
      have h1 : (QuotientGroup.mk' (Subgroup.center H)) (a * b)
          = (QuotientGroup.mk' (Subgroup.center H)) (b * a) := by
        have hmem : ⁅a, b⁆ ∈ Subgroup.center H :=
          hclass (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
        have hmem' : ⁅a, b⁆ ∈ (QuotientGroup.mk' (Subgroup.center H)).ker := by
          rw [QuotientGroup.ker_mk' (Subgroup.center H)]
          exact hmem
        have h2 : (QuotientGroup.mk' (Subgroup.center H)) ⁅a, b⁆ = 1 :=
          MonoidHom.mem_ker.mp hmem'
        rw [map_commutatorElement] at h2
        exact commutatorElement_eq_one_iff_mul_comm.mp h2
      rw [← map_mul, ← map_mul]
      exact h1
    have hVexp : ∀ v : H ⧸ Subgroup.center H, v ^ p = 1 := by
      intro v
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) v
      rw [← map_pow, hexp a, map_one]
    have hVcard : Nat.card (H ⧸ Subgroup.center H) ≤ p ^ 2 := by
      have h1 : Nat.card H = Nat.card (H ⧸ Subgroup.center H) * Nat.card ↥(Subgroup.center H) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
      rw [hcard3, hZcard] at h1
      have h2 : Nat.card (H ⧸ Subgroup.center H) * p = p ^ 2 * p := by
        rw [← h1]; ring
      exact Nat.le_of_mul_le_mul_right (le_of_eq h2) hp.pos
    -- the restricted map
    let ψ : ↥L →* MulAut (H ⧸ Subgroup.center H) := ρ.comp L.subtype
    have hψker : IsPGroup p ↥ψ.ker := by
      have hmem : ∀ x : ↥ψ.ker, ((x : ↥L) : MulAut H) ∈ ρ.ker := by
        intro x
        rw [MonoidHom.mem_ker]
        have hx : ψ (x : ↥L) = 1 := MonoidHom.mem_ker.mp x.2
        simpa [ψ] using hx
      refine isPGroup_of_injective (G := ↥ψ.ker) (N := ↥ρ.ker) hρker
        { toFun := fun x => ⟨((x : ↥L) : MulAut H), hmem x⟩
          map_one' := Subtype.ext rfl
          map_mul' := fun a b => Subtype.ext rfl } ?_
      intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥ρ.ker => (z : MulAut H)) hab))
    have hψodd : Odd (Nat.card ↥ψ.range) := Odd.of_dvd_nat hodd (card_range_dvd_card ψ)
    have hβ : IsPGroup p ↥⁅ψ.range, ψ.range⁆ :=
      mulAut_commutator_isPGroup_of_elementary_abelian_p2 hVcomm hVexp hVcard ψ.range hψodd
    -- restrict further to the derived subgroup of `L`
    have hLL : (⁅L, L⁆ : Subgroup (MulAut H)) ≤ L := by
      rw [Subgroup.commutator_le]
      intro g₁ h₁ g₂ h₂
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem h₁ h₂) (L.inv_mem h₁)) (L.inv_mem h₂)
    let χ : ↥(⁅L, L⁆) →* MulAut (H ⧸ Subgroup.center H) := ψ.comp (Subgroup.inclusion hLL)
    have hχker : IsPGroup p ↥χ.ker := by
      refine isPGroup_of_injective (G := ↥χ.ker) (N := ↥ψ.ker) hψker
        { toFun := fun x => ⟨Subgroup.inclusion hLL x, ?_⟩
          map_one' := Subtype.ext rfl
          map_mul' := fun a b => Subtype.ext rfl } ?_
      · rw [MonoidHom.mem_ker]
        have hx : χ (x : ↥(⁅L, L⁆)) = 1 := MonoidHom.mem_ker.mp x.2
        simpa [χ] using hx
      · intro a b hab
        exact Subtype.ext (Subtype.ext
          (congrArg (fun z : ↥ψ.ker => ((z : ↥L) : MulAut H)) hab))
    have hχrange : χ.range = ⁅ψ.range, ψ.range⁆ := by
      have h1 : Subgroup.map (Subgroup.inclusion hLL) (⊤ : Subgroup ↥(⁅L, L⁆)) =
          (⁅L, L⁆).subgroupOf L := by
        ext x
        rw [Subgroup.mem_map]
        constructor
        · rintro ⟨y, -, rfl⟩
          rw [Subgroup.mem_subgroupOf]
          exact y.2
        · intro hx
          rw [Subgroup.mem_subgroupOf] at hx
          exact ⟨⟨(x : MulAut H), hx⟩, Subgroup.mem_top _, Subtype.ext rfl⟩
      have h2 : (⁅L, L⁆).subgroupOf L = (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L) := by
        apply Subgroup.map_injective (Subgroup.subtype_injective L)
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLL, Subgroup.map_commutator,
          ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have h3 : χ = ψ.comp (Subgroup.inclusion hLL) := rfl
      rw [h3, MonoidHom.range_eq_map, ← Subgroup.map_map, h1, h2, Subgroup.map_commutator,
        ← MonoidHom.range_eq_map]
    exact isPGroup_of_ker_of_range hp χ hχker (by rw [hχrange]; exact hβ)

/-- **BG Lemma 4.17.**  Let `p` be an odd prime, `R` a finite `p`-group with no elementary abelian
subgroup of order `p ^ 3`, and `A ≤ Aut R` solvable of odd order.  Then `A'` is a `p`-group. -/
private theorem bg_4_17_copy {p : ℕ} (hp : p.Prime) (hpodd : Odd p) {R : Type*} [Group R] [Finite R]
    (hR : IsPGroup p R) (hE : Work.SmallRank.NoElementaryP3 p R)
    (A : Subgroup (MulAut R)) (hAsolv : Group.IsSolvable ↥A) (hAodd : Odd (Nat.card A)) :
    IsPGroup p ↥(⁅A, A⁆) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hnt : Nontrivial R
  · haveI : Nontrivial R := hnt
    obtain ⟨H, hHchar, hHne, hHR, hHH, hexp, hker⟩ :=
      thompson_char_omega1_subgroup hp hpodd R hR
    have hHmap : ∀ a : MulAut R, Subgroup.map a.toMonoidHom H = H :=
      fun a => Subgroup.characteristic_iff_map_eq.mp hHchar a
    -- the pointwise stabiliser of `H` in `MulAut R` is a `p`-group
    let K : Subgroup (MulAut R) :=
      { carrier := {φ | ∀ h : R, h ∈ H → φ h = h}
        mul_mem' := by
          intro a b ha hb h hh
          rw [MulAut.mul_apply, hb h hh, ha h hh]
        one_mem' := by intro h hh; rfl
        inv_mem' := by
          intro a ha h hh
          exact a.injective (by rw [ha h hh]; exact MulEquiv.apply_symm_apply a h) }
    have hKp : IsPGroup p ↥K := by
      rw [IsPGroup.iff_card]
      refine exists_pow_of_prime_dvd hp (Nat.card ↥K) (Nat.card_pos.ne') ?_
      intro q hq hqdvd
      haveI : Fact q.Prime := ⟨hq⟩
      obtain ⟨ψ, hψ⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) q hqdvd
      have hfix : ∀ h : R, h ∈ H → ((ψ : MulAut R)) h = h := ψ.2
      have hne : (ψ : MulAut R) ≠ 1 := by
        intro h1
        have h2 : orderOf (ψ : MulAut R) = 1 := by rw [h1, orderOf_one]
        rw [Subgroup.orderOf_coe, hψ] at h2
        exact absurd h2 hq.ne_one
      have hpq : p ∣ q := by
        have := hker (ψ : MulAut R) hfix hne
        rwa [Subgroup.orderOf_coe, hψ] at this
      exact (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq |>.symm
    -- the restriction homomorphism `A → MulAut H`
    let φ : ↥A →* MulAut ↥H :=
      { toFun := fun a => restrictMulAut (a : MulAut R) H (hHmap a)
        map_one' := by ext y; simp
        map_mul' := by intro a b; ext y; simp [MulAut.mul_apply] }
    -- the hypotheses of the auxiliary lemma for `H`
    have hclassH : ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ ≤ Subgroup.center ↥H := by
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      have hmem : ⁅(g₁ : R), (g₂ : R)⁆ ∈ Work.PGroup.centerIn H :=
        hHH (Subgroup.commutator_mem_commutator g₁.2 g₂.2)
      rw [Work.PGroup.centerIn, Subgroup.mem_map] at hmem
      obtain ⟨z, hz, hzeq⟩ := hmem
      have hzeq' : z = ⁅g₁, g₂⁆ :=
        Subtype.ext (hzeq.trans (map_commutatorElement H.subtype g₁ g₂).symm)
      rw [← hzeq']
      exact hz
    have hcardH : Nat.card ↥H ≤ p ^ 3 :=
      Work.SmallRank.card_le_p3_of_exponent_p hp hR hE H hexp
    have hnoEH : Work.SmallRank.NoElementaryP3 p ↥H := by
      rintro ⟨E, hEelem, hEcard⟩
      refine hE ⟨E.map H.subtype, isElementaryAbelian_map_subtype hEelem, ?_⟩
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact hEcard
    have hBodd : Odd (Nat.card ↥φ.range) := Odd.of_dvd_nat hAodd (card_range_dvd_card φ)
    have hγ : IsPGroup p ↥⁅φ.range, φ.range⁆ :=
      commutator_isPGroup_of_odd_le_mulAut hp hpodd hexp hclassH hcardH hnoEH φ.range hBodd
    -- the derivative of `A`, restricted to `H`
    have hAA : (⁅A, A⁆ : Subgroup (MulAut R)) ≤ A := by
      rw [Subgroup.commutator_le]
      intro g₁ h₁ g₂ h₂
      rw [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem h₁ h₂) (A.inv_mem h₁)) (A.inv_mem h₂)
    let ψ : ↥(⁅A, A⁆) →* MulAut ↥H := φ.comp (Subgroup.inclusion hAA)
    -- the kernel of `ψ` is a `p`-group
    have hψker : IsPGroup p ↥ψ.ker := by
      have hmem : ∀ x : ↥ψ.ker, ((x : ↥(⁅A, A⁆)) : MulAut R) ∈ K := by
        intro x
        show ∀ h : R, h ∈ H → ((x : ↥(⁅A, A⁆)) : MulAut R) h = h
        intro h hh
        have hy : ψ (x : ↥(⁅A, A⁆)) = 1 := MonoidHom.mem_ker.mp x.2
        have h2 := congrArg (fun f : MulAut ↥H => (f ⟨h, hh⟩ : ↥H)) hy
        exact congrArg (fun z : ↥H => (z : R)) h2
      refine isPGroup_of_injective (G := ↥ψ.ker) (N := ↥K) hKp
        { toFun := fun x => ⟨((x : ↥(⁅A, A⁆)) : MulAut R), hmem x⟩
          map_one' := Subtype.ext rfl
          map_mul' := fun a b => Subtype.ext rfl } ?_
      intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥K => (z : MulAut R)) hab))
    -- the range of `ψ` is the derived subgroup of the image of `A` in `MulAut H`
    have hψrange : ψ.range = ⁅φ.range, φ.range⁆ := by
      have h1 : Subgroup.map (Subgroup.inclusion hAA) (⊤ : Subgroup ↥(⁅A, A⁆)) =
          (⁅A, A⁆).subgroupOf A := by
        ext x
        rw [Subgroup.mem_map]
        constructor
        · rintro ⟨y, -, rfl⟩
          rw [Subgroup.mem_subgroupOf]
          exact y.2
        · intro hx
          rw [Subgroup.mem_subgroupOf] at hx
          exact ⟨⟨(x : MulAut R), hx⟩, Subgroup.mem_top _, Subtype.ext rfl⟩
      have h2 : (⁅A, A⁆).subgroupOf A = (⁅(⊤ : Subgroup ↥A), ⊤⁆ : Subgroup ↥A) := by
        apply Subgroup.map_injective (Subgroup.subtype_injective A)
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAA, Subgroup.map_commutator,
          ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have h3 : ψ = φ.comp (Subgroup.inclusion hAA) := rfl
      rw [h3, MonoidHom.range_eq_map, ← Subgroup.map_map, h1, h2, Subgroup.map_commutator,
        ← MonoidHom.range_eq_map]
    exact isPGroup_of_ker_of_range hp ψ hψker (by rw [hψrange]; exact hγ)
  · -- `R` is the trivial group: then `MulAut R` is trivial
    haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hnt
    haveI : Subsingleton (MulAut R) :=
      ⟨fun f g => MulEquiv.ext (fun x => Subsingleton.elim _ _)⟩
    have hbot : (⁅A, A⁆ : Subgroup (MulAut R)) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      exact Subsingleton.elim x 1
    rw [hbot]
    refine fun x => ⟨0, ?_⟩
    rw [pow_zero, pow_one]
    exact Subsingleton.elim x 1

/-! ## Helpers -/

/-- The range of a monoid homomorphism from a finite group has cardinality dividing the source. -/
private theorem card_range_dvd_card' {G N : Type*} [Group G] [Group N] [Finite G] (f : G →* N) :
    Nat.card ↥f.range ∣ Nat.card G := by
  haveI : f.ker.Normal := f.normal_ker
  have h1 : Nat.card ↥f.ker * f.ker.index = Nat.card G := Subgroup.card_mul_index f.ker
  have h2 : f.ker.index = Nat.card ↥f.range := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  exact ⟨Nat.card ↥f.ker, by rw [← h1, h2, mul_comm]⟩

/-- `NoElementaryP3` transfers across an injective homomorphism. -/
private theorem noElementaryP3_of_injective {p : ℕ} {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Injective f) (h : Work.SmallRank.NoElementaryP3 p Y) :
    Work.SmallRank.NoElementaryP3 p X := by
  rintro ⟨E, hE, hEcard⟩
  exact h ⟨E.map f, Work.PGroup.isElementaryAbelian_map hf hE, by
    rw [Subgroup.card_map_of_injective hf, hEcard]⟩

/-- `NoElementaryP3` transfers across a multiplicative equivalence. -/
private theorem noElementaryP3_of_equiv {p : ℕ} {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (h : Work.SmallRank.NoElementaryP3 p Y) : Work.SmallRank.NoElementaryP3 p X :=
  noElementaryP3_of_injective e.toMonoidHom e.injective h

/-- A subgroup of a `p`-group is a `p`-group. -/
private theorem isPGroup_subgroupOf' {p : ℕ} {G : Type*} [Group G] {C H : Subgroup G}
    (h : IsPGroup p ↥C) : IsPGroup p ↥(C.subgroupOf H) :=
  h.of_injective
    { toFun := fun x => ⟨(x : G), x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
    (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun z : ↥C => (z : G)) hab)))

/-- The kernel of the conjugation action on a normal subgroup is the centralizer. -/
private theorem conjNormal_ker {G : Type*} [Group G] {R : Subgroup G} [R.Normal] :
    (MulAut.conjNormal (H := R)).ker = Subgroup.centralizer (R : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h r hr
    have h2 := congrArg (fun f : MulAut ↥R => f ⟨r, hr⟩) h
    simp only [MulAut.one_apply] at h2
    have h3 : g * r * g⁻¹ = r := by
      have := congrArg (fun x : ↥R => (x : G)) h2
      simpa [MulAut.conjNormal_apply] using this
    have h4 : g * r = r * g := by
      calc g * r = g * r * g⁻¹ * g := by group
        _ = r * g := by rw [h3]
    exact h4.symm
  · intro h
    apply MulEquiv.ext
    intro r
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have hr := h (r : G) r.2
    rw [← hr]; group

/-! ## Step: `S' ≤ O_p(S)` in the reduced case (BG Theorem 4.18) -/

/-- **Bender–Glauberman Theorem 4.18**, key step: if `S` is solvable of odd order with
`O_{p'}(S) = 1` and `𝒮𝒞𝒩₃(P) = ∅` for a Sylow `p`-subgroup `P`, then `S' ≤ O_p(S)`. -/
private theorem derived_le_pCore_of_no_scn3 {S : Type*} [Group S] [Finite S] (hsol : Group.IsSolvable S)
    (hodd : Odd (Nat.card S)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (P : Sylow p S)
    (hSCN : ∀ A : Subgroup S, ¬ Work.LocalPrelim.IsSCN_m 3 (P : Subgroup S) A)
    (hOp' : Work.Fitting.pPrimeCore p S = ⊥) :
    ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ ≤ Work.Fitting.pCore p S := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set R : Subgroup S := Work.Fitting.pCore p S with hRdef
  haveI hRnorm : R.Normal := by
    rw [hRdef]; haveI := Work.Fitting.pCore_characteristic p S; infer_instance
  have hfit : Work.Fitting.fitting S = R := by
    rw [hRdef]; exact Work.Fitting.fitting_eq_pCore_of_pPrimeCore_eq_bot p S hp hOp'
  have hC : Subgroup.centralizer (R : Set S) ≤ R := by
    rw [← hfit]; exact Work.Fitting.centralizer_fitting_le S
  have hRP : R ≤ (P : Subgroup S) := by rw [hRdef]; exact Work.Fitting.pCore_le_sylow P
  have hRpg : IsPGroup p ↥R := P.isPGroup'.to_le hRP
  have hSCN_P : ∀ A : Subgroup ↥(P : Subgroup S),
      ¬ Work.LocalPrelim.IsSCN_m 3 (⊤ : Subgroup ↥(P : Subgroup S)) A :=
    fun A hA => by
      obtain ⟨A', hA'⟩ := (Work.Transitivity.Basic.exists_isSCN_m_top_iff (G := S) 3
        (P : Subgroup S)).mp ⟨A, hA⟩
      exact hSCN A' hA'
  have hnoE_P : ¬ ∃ E : Subgroup ↥(P : Subgroup S),
      Work.PGroup.IsElementaryAbelian p E ∧ p ^ 3 ≤ Nat.card E :=
    no_elementary_of_no_scn3 hp hpodd P.isPGroup' hSCN_P
  have hnoE_R : Work.SmallRank.NoElementaryP3 p ↥R := by
    rintro ⟨E, hE, hEcard⟩
    refine hnoE_P ⟨E.map (Subgroup.inclusion hRP), ?_, ?_⟩
    · exact Work.PGroup.isElementaryAbelian_map (Subgroup.inclusion_injective hRP) hE
    · rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hRP), hEcard]
  set C : Subgroup S := Subgroup.centralizer (R : Set S) with hCdef
  set φ : S →* MulAut ↥R := MulAut.conjNormal (H := R) with hφdef
  have hφker : φ.ker = C := by rw [hφdef, hCdef]; exact conjNormal_ker
  haveI hCnorm : C.Normal := hφker ▸ φ.normal_ker
  set A : Subgroup (MulAut ↥R) := φ.range with hAdef
  have hAsolv : Group.IsSolvable ↥A := Group.isSolvable_of_surjective φ.rangeRestrict_surjective
  have hAodd : Odd (Nat.card ↥A) := hodd.of_dvd_nat (card_range_dvd_card' φ)
  have hA' : IsPGroup p ↥(⁅A, A⁆) := bg_4_17_copy hp hpodd hRpg hnoE_R A hAsolv hAodd
  have hAd : IsPGroup p ↥(⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆) := by
    have hmap : Subgroup.map A.subtype (⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ : Subgroup ↥A)
        = ⁅A, A⁆ := by
      rw [Subgroup.map_commutator]
      simp only [Subgroup.map_top, Subgroup.range_subtype]
    have h2 : IsPGroup p ↥(Subgroup.map A.subtype
        (⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ : Subgroup ↥A)) := by
      exact hmap.symm ▸ hA'
    exact h2.of_equiv (Subgroup.equivMapOfInjective _ A.subtype A.subtype_injective).symm
  have he : S ⧸ C ≃* ↥A := by
    rw [hAdef]
    exact (QuotientGroup.quotientMulEquivOfEq hφker).symm.trans
      (QuotientGroup.quotientKerEquivRange φ)
  have hSq : IsPGroup p ↥(⁅(⊤ : Subgroup (S ⧸ C)), (⊤ : Subgroup (S ⧸ C))⁆) := by
    have hmap : Subgroup.map he.toMonoidHom (⁅(⊤ : Subgroup (S ⧸ C)), (⊤ : Subgroup (S ⧸ C))⁆)
        = (⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ : Subgroup ↥A) := by
      rw [Subgroup.map_commutator, Subgroup.map_top,
        (MonoidHom.range_eq_top (f := he.toMonoidHom)).mpr he.surjective]
    have h2 : IsPGroup p ↥(Subgroup.map he.toMonoidHom
        (⁅(⊤ : Subgroup (S ⧸ C)), (⊤ : Subgroup (S ⧸ C))⁆)) := by
      exact hmap.symm ▸ hAd
    exact h2.of_equiv (Subgroup.equivMapOfInjective _ he.toMonoidHom he.injective).symm
  -- the quotient `S' / (S' ⊓ C)` is a `p`-group
  have hquot : IsPGroup p (↥(⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆) ⧸
      (C.subgroupOf ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆)) := by
    set f : ↥(⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆) →* (S ⧸ C) :=
      (QuotientGroup.mk' C).comp (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆).subtype with hf
    have hker : f.ker = C.subgroupOf ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ := by
      ext x
      simp only [hf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
        Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hidx : (C.subgroupOf ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆).index =
        Nat.card ↥f.range := by
      rw [← hker, Subgroup.index_eq_card]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have h3 : IsPGroup p ↥f.range := by
      have hrf : f.range = Subgroup.map (QuotientGroup.mk' C)
          (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆) := by
        rw [hf, MonoidHom.range_eq_map, ← Subgroup.map_map]
        simp only [Subgroup.map_top, Subgroup.range_subtype]
      have hmapC : Subgroup.map (QuotientGroup.mk' C) (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆)
          = ⁅(⊤ : Subgroup (S ⧸ C)), (⊤ : Subgroup (S ⧸ C))⁆ := by
        rw [Subgroup.map_commutator, Subgroup.map_top,
          (MonoidHom.range_eq_top (f := QuotientGroup.mk' C)).mpr (QuotientGroup.mk'_surjective C)]
      rw [hrf]
      exact hmapC.symm ▸ hSq
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h3
    refine IsPGroup.iff_card.mpr ⟨m, ?_⟩
    rw [← Subgroup.index_eq_card, hidx]
    exact hm
  have hCsubpg : IsPGroup p ↥(C.subgroupOf ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆) :=
    isPGroup_subgroupOf' (C := C) (H := ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆) (hRpg.to_le hC)
  haveI hCsubnorm : (C.subgroupOf ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆).Normal :=
    Subgroup.Normal.subgroupOf hCnorm _
  have hSpg : IsPGroup p ↥(⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆) :=
    isPGroup_of_quotient_of_isPGroup hp _ hCsubpg hquot
  rw [hRdef]
  exact Work.Fitting.le_piCore (inferInstance : (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆).Normal)
    ((Work.Fitting.isPiNat_prime_iff_isPGroup hp (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆)).mpr hSpg)


/-! ## Assembly of FT 8.13 -/

/-- FT 8.13 in the reduced case `O_{p'}(S) = 1`: Bender--Glauberman 4.18 gives `S' ≤ O_p(S)`, and
a normal nilpotent subgroup centralizes every chief factor. -/
private theorem ft8_13_reduced {S : Type u} [Group S] [Finite S] (hsol : Group.IsSolvable S)
    (hodd : Odd (Nat.card S)) {p : ℕ} (hp : p.Prime) (P : Sylow p S)
    (hSCN : ∀ A : Subgroup S, ¬ IsSCN_m 3 (P : Subgroup S) A)
    {H K : Subgroup S} (hHK : Work.Fitting.IsChiefFactor H K) (hpf : IsPFactor p H K)
    (hOp' : Work.Fitting.pPrimeCore p S = ⊥) :
    CentralizesFactor ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ K H := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- `p` is odd, since `p ∣ [K : H] ∣ |S|` and `|S|` is odd
  have hp2 : p ≠ 2 := by
    have hidx_ne : (H.subgroupOf K).index ≠ 1 := by
      intro h1
      rw [Subgroup.index_eq_one] at h1
      exact not_le_of_gt hHK.2.2.1 (Subgroup.subgroupOf_eq_top.mp h1)
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hidx_ne
    have hqeq : q = p := hpf.2 q hq hqdvd
    have hKdvd : Nat.card ↥K ∣ Nat.card S := ⟨K.index, by rw [Subgroup.card_mul_index]⟩
    have hp_dvd : p ∣ Nat.card S :=
      ((hqeq ▸ hqdvd).trans (Subgroup.index_dvd_card (H.subgroupOf K))).trans hKdvd
    intro h
    rw [h] at hp_dvd
    obtain ⟨k, hk⟩ := hodd
    omega
  have hSpc := derived_le_pCore_of_no_scn3 hsol hodd hp hp2 P hSCN hOp'
  have hSpg : IsPGroup p ↥(⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆) :=
    P.isPGroup'.to_le (hSpc.trans (Work.Fitting.pCore_le_sylow P))
  haveI : Group.IsNilpotent ↥(⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆) := hSpg.isNilpotent
  haveI : (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S).Normal :=
    Subgroup.commutator_normal _ _
  haveI : H.Normal := hHK.1
  have hcomm : ⁅K, ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆⁆ ≤ H :=
    Work.Fitting.commutator_le_of_isChiefFactor_of_nilpotent inferInstance hHK
  show ⁅⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆, K⁆ ≤ H
  rw [Subgroup.commutator_comm]
  exact hcomm

/-- FT 8.13, quotient step: if `O_{p'}(S) ≠ 1` then the statement for `S` follows from the
statement for all groups of smaller order, applied to `S ⧸ O_{p'}(S)`. -/
private theorem ft8_13_quotient {S : Type u} [Group S] [Finite S] (hsol : Group.IsSolvable S)
    (hodd : Odd (Nat.card S)) {p : ℕ} (hp : p.Prime) (P : Sylow p S)
    (hSCN : ∀ A : Subgroup S, ¬ IsSCN_m 3 (P : Subgroup S) A)
    {H K : Subgroup S} (hHK : Work.Fitting.IsChiefFactor H K) (hpf : IsPFactor p H K)
    (hIH : ∀ {T : Type u} [Group T] [Finite T], Nat.card T < Nat.card S →
      Group.IsSolvable T → Odd (Nat.card T) → ∀ {q : ℕ}, q.Prime → ∀ Q : Sylow q T,
      (∀ A : Subgroup T, ¬ IsSCN_m 3 (Q : Subgroup T) A) →
      ∀ {H' K' : Subgroup T}, Work.Fitting.IsChiefFactor H' K' → IsPFactor q H' K' →
      CentralizesFactor ⁅(⊤ : Subgroup T), (⊤ : Subgroup T)⁆ K' H')
    (hN : Work.Fitting.pPrimeCore p S ≠ ⊥) :
    CentralizesFactor ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ K H := by
  classical
  set N : Subgroup S := Work.Fitting.pPrimeCore p S with hNdef
  haveI hNnorm : N.Normal := by
    rw [hNdef]
    haveI := Work.Fitting.pPrimeCore_characteristic p S
    infer_instance
  haveI : H.Normal := hHK.1
  have hNpi : Work.Fitting.IsPiNat (fun q => q ≠ p) (Nat.card ↥N) := by
    rw [hNdef]
    exact Work.Fitting.piCore_isPiNat S (fun q => q ≠ p)
  -- the Sylow `p`-subgroup of the quotient, with `𝒮𝒞𝒩₃ = ∅`
  obtain ⟨Q, hQ⟩ := scn3_empty_sylow_quotient hp P hSCN N hNpi
  -- the chief `p`-factor descends to the quotient
  obtain ⟨hc1, hc2, hc3⟩ := chiefFactor_pFactor_map_quotient hHK hpf hNpi
  -- the induction hypothesis
  have hcard : Nat.card (S ⧸ N) < Nat.card S := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
    calc Nat.card (S ⧸ N) = Nat.card (S ⧸ N) * 1 := (mul_one _).symm
      _ < Nat.card (S ⧸ N) * Nat.card ↥N :=
          Nat.mul_lt_mul_of_pos_left ((Subgroup.one_lt_card_iff_ne_bot N).mpr hN) Nat.card_pos
  have hsolQ : Group.IsSolvable (S ⧸ N) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective N)
  have hoddQ : Odd (Nat.card (S ⧸ N)) :=
    Work.Skeleton.odd_card_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hodd
  have hIH' := hIH hcard hsolQ hoddQ hp Q hQ hc1 hc2
  -- `[S',K]` maps into the image of `H ⊔ N`
  have hNbot : Subgroup.map (QuotientGroup.mk' N) N = ⊥ :=
    (Subgroup.map_eq_bot_iff N).mpr (le_of_eq (QuotientGroup.ker_mk' N).symm)
  have hmap : Subgroup.map (QuotientGroup.mk' N) (⁅⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆, K⁆)
      = ⁅⁅(⊤ : Subgroup (S ⧸ N)), (⊤ : Subgroup (S ⧸ N))⁆,
          Subgroup.map (QuotientGroup.mk' N) K⁆ := by
    have htop : Subgroup.map (QuotientGroup.mk' N) (⊤ : Subgroup S) = ⊤ := by
      rw [Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
    rw [Subgroup.map_commutator, Subgroup.map_commutator, htop]
  have hmap2 : Subgroup.map (QuotientGroup.mk' N) (H ⊔ N) =
      Subgroup.map (QuotientGroup.mk' N) H := by
    rw [Subgroup.map_sup, hNbot, sup_bot_eq]
  have hle : Subgroup.map (QuotientGroup.mk' N) (⁅⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆, K⁆)
      ≤ Subgroup.map (QuotientGroup.mk' N) (H ⊔ N) := by
    rw [hmap, hmap2]
    exact hIH'
  have key : ⁅⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆, K⁆ ≤ H ⊔ N := by
    have h1 : ⁅⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆, K⁆ ≤ Subgroup.comap (QuotientGroup.mk' N)
        (Subgroup.map (QuotientGroup.mk' N) (⁅⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆, K⁆)) :=
      Subgroup.le_comap_map _ _
    have h2 : Subgroup.comap (QuotientGroup.mk' N)
        (Subgroup.map (QuotientGroup.mk' N) (⁅⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆, K⁆)) ≤
        Subgroup.comap (QuotientGroup.mk' N) (Subgroup.map (QuotientGroup.mk' N) (H ⊔ N)) :=
      Subgroup.comap_mono hle
    have h3 : Subgroup.comap (QuotientGroup.mk' N) (Subgroup.map (QuotientGroup.mk' N) (H ⊔ N))
        = H ⊔ N := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      simp
    exact (h1.trans h2).trans (le_of_eq h3)
  -- Dedekind's modular law finishes the job
  haveI : K.Normal := hHK.2.1
  show ⁅⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆, K⁆ ≤ H
  refine le_trans (le_inf (Subgroup.commutator_le_right _ _) key) ?_
  intro x hx
  obtain ⟨hxK, hxHN⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨h, hh, n, hn, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := H) (t := N)).mp hxHN
  have hhK : h ∈ K := hHK.2.2.1.le hh
  have hnK : n ∈ K := by
    have h1 : h⁻¹ * (h * n) ∈ K := K.mul_mem (K.inv_mem hhK) hxK
    simpa using h1
  have hnH : n ∈ H := hc3 (Subgroup.mem_inf.mpr ⟨hnK, hn⟩)
  exact H.mul_mem hh hnH

/-- One step of the induction: either `O_{p'}(S) = 1` (reduced case) or we pass to
`S ⧸ O_{p'}(S)`. -/
private theorem ft8_13_step {S : Type u} [Group S] [Finite S] (hsol : Group.IsSolvable S)
    (hodd : Odd (Nat.card S)) {p : ℕ} (hp : p.Prime) (P : Sylow p S)
    (hSCN : ∀ A : Subgroup S, ¬ IsSCN_m 3 (P : Subgroup S) A)
    {H K : Subgroup S} (hHK : Work.Fitting.IsChiefFactor H K) (hpf : IsPFactor p H K)
    (hIH : ∀ {T : Type u} [Group T] [Finite T], Nat.card T < Nat.card S →
      Group.IsSolvable T → Odd (Nat.card T) → ∀ {q : ℕ}, q.Prime → ∀ Q : Sylow q T,
      (∀ A : Subgroup T, ¬ IsSCN_m 3 (Q : Subgroup T) A) →
      ∀ {H' K' : Subgroup T}, Work.Fitting.IsChiefFactor H' K' → IsPFactor q H' K' →
      CentralizesFactor ⁅(⊤ : Subgroup T), (⊤ : Subgroup T)⁆ K' H') :
    CentralizesFactor ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ K H := by
  by_cases hOp' : Work.Fitting.pPrimeCore p S = ⊥
  · exact ft8_13_reduced hsol hodd hp P hSCN hHK hpf hOp'
  · exact ft8_13_quotient hsol hodd hp P hSCN hHK hpf hIH hOp'

/-- FT 8.13 by strong induction on `|S|`. -/
private theorem ft8_13_all : ∀ (n : ℕ), ∀ {T : Type u} [Group T] [Finite T], Nat.card T = n →
    Group.IsSolvable T → Odd (Nat.card T) → ∀ {q : ℕ}, q.Prime → ∀ Q : Sylow q T,
    (∀ A : Subgroup T, ¬ IsSCN_m 3 (Q : Subgroup T) A) →
    ∀ {H' K' : Subgroup T}, Work.Fitting.IsChiefFactor H' K' → IsPFactor q H' K' →
    CentralizesFactor ⁅(⊤ : Subgroup T), (⊤ : Subgroup T)⁆ K' H' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T _ _ hcard hsol hodd q hq Q hSCN H' K' hHK' hpf'
    exact ft8_13_step hsol hodd hq Q hSCN hHK' hpf'
      (fun {T'} _ _ hlt hsol' hodd' {q'} hq' Q' hSCN' {H''} {K''} hHK'' hpf'' =>
        ih (Nat.card T') (by rw [← hcard]; exact hlt) (T := T') rfl hsol' hodd' hq' Q' hSCN'
          hHK'' hpf'')

/-- **FT Lemma 8.13.** -/
theorem ft8_13 {S : Type*} [Group S] [Finite S] (hsol : Group.IsSolvable S)
    (hodd : Odd (Nat.card S)) {p : ℕ} (hp : p.Prime) (P : Sylow p S)
    (h : ∀ A : Subgroup S, ¬ IsSCN_m 3 (P : Subgroup S) A)
    {H K : Subgroup S} (hHK : Work.Fitting.IsChiefFactor H K) (hpf : IsPFactor p H K) :
    CentralizesFactor ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ K H :=
  ft8_13_all (Nat.card S) rfl hsol hodd hp P h hHK hpf

end Work.LocalPrelim
