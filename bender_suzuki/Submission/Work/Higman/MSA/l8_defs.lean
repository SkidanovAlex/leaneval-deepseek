/-
Copyright (c) 2024. All rights reserved.

# Higman's auxiliary result 8: the layers `V = C/A` and `W = Ω₁(P)` and the two pairings

This file sets up the objects used in the proof of Higman's auxiliary result 8 in the form
needed by the Lemma-9 development (`Submission/Work/Higman/MSA/higman_lemma8_msa.lean`).

Setting: `P` is a Suzuki 2-group with automorphism `ξ`, `A ≤ C` are subgroups with `A` a
`ξ`-invariant abelian normal subgroup, `C` a `ξ`-invariant normal subgroup, `C/A` a minimal normal
`ξ`-section, `C ^ (2) ≤ A` and `⁅C,C⁆ = A`.  We work in the case `A ≠ ⊥`, so that `Ω₁(P) ≤ A` and
`A` is homocyclic of exponent `2 ^ e`, and in the case `A ^ 2 ≠ ⊥`, so that `e ≥ 2`.

* `V := ↥C ⧸ A.subgroupOf C = C/A` is the first layer, `W := ↥(omega1 P) = Ω₁(P)` the second.
* `BV : V → V → W` is the commutator pairing `(uA, vA) ↦ (⁅u⁻¹,v⁆) ^ 2 ^ (e-1)`.
* `sV : V → W` is the power map `uA ↦ u ^ 2 ^ e`.
* `betaV : V → W → W` is the bracket `(uA, p a) ↦ (⁅u,a⁆) ^ 2 ^ (e-2)`, where `p a = a ^ 2 ^ (e-1)`.

The two identifications `A/A² ≅ Ω₁(P)` (power map `a ↦ a ^ 2 ^ (e-1)`) and
`A²/A⁴ ≅ Ω₁(P)` (power map `x ↦ x ^ 2 ^ (e-2)`) are `Work.Higman.Fq_structure`, and the
well-definedness of `BV` and `betaV` on representatives is exactly the content of the commutation
relations `⁅C,A⁆ = A²`, `⁅C,A²⁆ ⊆ A⁴` (`Work.Higman.commutator_powSub_A_C`).
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.powSub_C_eq_of_cover
import Submission.Work.Higman.Fq_structure
import Submission.Work.Higman.omega1_iso_field

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.MSA

variable {P : Type} [Group P] [Finite P]

/-! ## The automorphism induced by `ξ` on an invariant subgroup -/

/-- The automorphism of `↥H` induced by `ξ` when `H` is `ξ`-invariant. -/
noncomputable def xiSubAut (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) : MulAut ↥H where
  toFun x := ⟨h.xi (x : P), by
    have hx := Subgroup.mem_map_of_mem ((h.xi : MulAut P).toMonoidHom) x.2
    rwa [hinv] at hx⟩
  invFun x := ⟨(h.xi : MulAut P).symm (x : P),
    symm_mem_of_map_eq (h.xi : MulAut P) hinv x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem xiSubAut_apply (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) (x : ↥H) :
    ((xiSubAut h hinv x : ↥H) : P) = h.xi (x : P) := rfl

/-! ## The quotient `V = C/A` and the induced `ξ`-action -/

section Quot

variable {A C : Subgroup P} [hAn : A.Normal]

/-- Every element of `C / A` is an involution (`C ^ (2) ≤ A`). -/
theorem quot_sq_one (hC2 : powSub C 2 ≤ A) (x : ↥C ⧸ (A.subgroupOf C)) : x * x = 1 := by
  induction x using QuotientGroup.induction_on with
  | _ c =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_one, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have hmem : (c : P) * (c : P) ∈ A := by
        have h2 : (c : P) ^ 2 ∈ powSub C 2 := pow_mem_powSub (A := C) c.2
        rw [pow_two] at h2
        exact hC2 h2
      simpa using A.inv_mem_iff.mpr hmem

/-- `C / A` is abelian (`⁅C,C⁆ = A`). -/
theorem quot_comm (hCd : ⁅C, C⁆ = A) (x y : ↥C ⧸ (A.subgroupOf C)) : x * y = y * x := by
  induction x using QuotientGroup.induction_on with
  | _ c =>
      induction y using QuotientGroup.induction_on with
      | _ d =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          have hmem : (⁅d⁻¹, c⁻¹⁆ : ↥C) ∈ A.subgroupOf C := by
            rw [Subgroup.mem_subgroupOf]
            exact hCd ▸ Subgroup.commutator_mem_commutator (C.inv_mem d.2) (C.inv_mem c.2)
          have h : (c * d)⁻¹ * (d * c) = ⁅d⁻¹, c⁻¹⁆ := by
            rw [commutatorElement_def]
            group
          rwa [h]

/-- The automorphism of `↥C` induced by `ξ`. -/
noncomputable abbrev xiC (h : IsSuzuki2Grp P) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) :
    MulAut ↥C :=
  xiSubAut h hCinv

/-- `ξ` preserves `A` viewed inside `C`. -/
theorem map_xi_subgroupOf (h : IsSuzuki2Grp P) (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) :
    Subgroup.map (xiC h hCinv : ↥C ≃* ↥C) (A.subgroupOf C)
      = A.subgroupOf C := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h1 : (((xiC h hCinv) y : ↥C) : P) = h.xi (y : P) :=
      xiSubAut_apply h hCinv y
    rw [← hyx]
    show h.xi (y : P) ∈ A
    rw [← hAinv]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hy)
  · intro hx
    refine ⟨(xiC h hCinv)⁻¹ x, ?_, by simp⟩
    show h.xi.symm (x : P) ∈ A
    exact symm_mem_of_map_eq (h.xi : MulAut P) hAinv (Subgroup.mem_subgroupOf.mp hx)

/-- **The automorphism of `V = C / A` induced by `ξ`.** -/
noncomputable def xiQuot (h : IsSuzuki2Grp P) (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) :
    (↥C ⧸ (A.subgroupOf C)) ≃* (↥C ⧸ (A.subgroupOf C)) :=
  QuotientGroup.congr (A.subgroupOf C) (A.subgroupOf C) (xiC h hCinv)
    (map_xi_subgroupOf (A := A) (C := C) h hAinv hCinv)

/-- **Well-definedness of the power map** `uA ↦ u ^ (2 ^ e)`: it is constant on cosets of `A`,
because `A` has exponent `2 ^ e` and conjugation by `u` changes an element of `A` by an element of
`A²`: `(u*a) ^ 2 = u ^ 2 * (⁅u⁻¹,a⁆ * a^2)` with `⁅u⁻¹,a⁆ ∈ A²` and `a ^ 2 ∈ A²`. -/
theorem pow_two_pow_mul_mem (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A) (hC2 : powSub C 2 ≤ A) {e : ℕ}
    (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he : 1 ≤ e) {u : P} (hu : u ∈ C) {a : P} (ha : a ∈ A) :
    (u * a) ^ 2 ^ e = u ^ 2 ^ e := by
  have hmul : ∀ x : P, x ^ 2 ^ e = (x ^ 2) ^ 2 ^ (e - 1) := by
    intro x
    rw [← pow_mul,
      show 2 * 2 ^ (e - 1) = 2 ^ e from by rw [← pow_succ']; congr 1; omega]
  have hmemA : ⁅u⁻¹, a⁆ ∈ powSub A 2 := commutator_mem_powSub_two h hA u⁻¹ a ha
  have hc : (u * a) ^ 2 = u ^ 2 * (⁅u⁻¹, a⁆ * a ^ 2) := by
    rw [commutatorElement_def]
    simp only [pow_two]
    group
  have hcA2 : ⁅u⁻¹, a⁆ * a ^ 2 ∈ powSub A 2 :=
    Subgroup.mul_mem _ hmemA (pow_mem_powSub ha)
  obtain ⟨d, hdA, hd⟩ := (mem_powSub_iff hA.abelian).mp hcA2
  have hmem1 : u ^ 2 ∈ A := hC2 (pow_mem_powSub hu)
  have hcomm : Commute (u ^ 2) d := hA.abelian _ hmem1 _ hdA
  have hstep : (u ^ 2 * d ^ 2) ^ 2 ^ (e - 1) =
      (u ^ 2) ^ 2 ^ (e - 1) * (d ^ 2) ^ 2 ^ (e - 1) := by
    rw [pow_two d]
    exact (hcomm.mul_right hcomm).mul_pow _
  rw [hmul (u * a), hmul u, hc, ← hd, hstep, ← hmul d, he1 d hdA, mul_one]

/-- For `u ∈ C` the `2 ^ e`-th power of `u` lies in `Ω₁(P)`: this is the map
`sV : C/A → Ω₁(P)` on representatives. -/
theorem pow_two_pow_mem_omega1 (h : IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : IsXiAbelNormal h A) (hC2 : powSub C 2 ≤ A) {e : ℕ}
    (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he : 1 ≤ e) {u : P} (hu : u ∈ C) :
    u ^ 2 ^ e ∈ omega1 P := by
  have hsq : u ^ 2 ∈ A := hC2 (pow_mem_powSub hu)
  have hpow : u ^ 2 ^ e = (u ^ 2) ^ 2 ^ (e - 1) := by
    rw [← pow_mul,
      show 2 * 2 ^ (e - 1) = 2 ^ e from by rw [← pow_succ']; congr 1; omega]
  rw [hpow]
  rw [h.mem_omega1, ← pow_mul,
    show 2 ^ (e - 1) * 2 = 2 ^ e from by rw [← pow_succ]; congr 1; omega]
  exact he1 (u ^ 2) hsq

/-- **The map `sV : C/A → Ω₁(P)`**, `uA ↦ u ^ (2 ^ e)`: Higman's squaring map composed with the
identification `A/A² ≅ Ω₁(P)`, well defined by `pow_two_pow_mul_mem` (this is the raw,
unpackaged form of `sV`). -/
noncomputable def sQuot (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hA : IsXiAbelNormal h A) (hC2 : powSub C 2 ≤ A) {e : ℕ}
    (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he : 1 ≤ e)
    (x : ↥C ⧸ (A.subgroupOf C)) : ↥(omega1 P) :=
  Quotient.liftOn x
    (fun u : ↥C => ⟨(u : P) ^ 2 ^ e, pow_two_pow_mem_omega1 h hA hC2 he1 he u.2⟩)
    (by
      intro u v huv
      have huv' : QuotientGroup.leftRel (A.subgroupOf C) u v := huv
      rw [QuotientGroup.leftRel_apply] at huv'
      have ha : (((u⁻¹ * v : ↥C) : P)) ∈ A := Subgroup.mem_subgroupOf.mp huv'
      apply Subtype.ext
      have hw := pow_two_pow_mul_mem h hA hC2 he1 he u.2 (a := ((u⁻¹ * v : ↥C) : P)) ha
      have hgroup : (u : P) * (((u⁻¹ * v : ↥C) : P)) = (v : P) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hgroup] at hw
      exact hw.symm)

/-- The value of `sQuot` on a representative. -/
theorem sQuot_mk (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hA : IsXiAbelNormal h A) (hC2 : powSub C 2 ≤ A) {e : ℕ}
    (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he : 1 ≤ e) (u : ↥C) :
    ((sQuot h hA hC2 he1 he (QuotientGroup.mk u) : ↥(omega1 P)) : P) = (u : P) ^ 2 ^ e :=
  rfl

end Quot

/-! ## The hypothesis package -/

/-- The hypotheses and exponent data of Higman's auxiliary result 8 in the nontrivial case:
`A ≠ ⊥` and `2 ≤ e`, where `2 ^ e` is the exponent of the homocyclic group `A`.

The fields `htopA` (`A ^ (2 ^ (e-1)) = Ω₁(P)`) and `hkey` (the elementwise kernel statement
`x ∈ A² ↔ x ^ 2 ^ (e-1) = 1` for `x ∈ A`) are the two forms of Higman's Lemma 1 that are used
below; both are produced by `Work.Higman.homogeneous_structure` (the second one from the layer
cardinalities). -/
structure L8D (h : IsSuzuki2Grp P) (A C : Subgroup P) [A.Normal] where
  /-- `A` is a `ξ`-invariant abelian normal subgroup. -/
  hA : IsXiAbelNormal h A
  /-- `C` is normal in `P`. -/
  hCn : C.Normal
  /-- `C` is `ξ`-invariant. -/
  hCinv : C.map (h.xi : MulAut P).toMonoidHom = C
  /-- `A ≤ C`. -/
  hAC : A ≤ C
  /-- `A ≠ C`. -/
  hCA : A ≠ C
  /-- `C/A` is a minimal normal `ξ`-section. -/
  hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C
  /-- `C ^ (2) ≤ A`. -/
  hC2 : powSub C 2 ≤ A
  /-- `⁅C,C⁆ = A`. -/
  hCd : ⁅C, C⁆ = A
  /-- `A ≠ ⊥` (the case `A = ⊥` is trivial). -/
  hAne : A ≠ ⊥
  /-- `Ω₁(P) ≤ A`. -/
  hOmega : omega1 P ≤ A
  /-- the exponent parameter of `A`. -/
  e : ℕ
  /-- `1 ≤ e`. -/
  he : 1 ≤ e
  /-- `2 ≤ e`, i.e. `A ^ 2 ≠ ⊥` (the case `A ^ 2 = ⊥` is the conclusion). -/
  he2 : 2 ≤ e
  /-- `A` has exponent `2 ^ e`. -/
  he1 : ∀ a ∈ A, a ^ 2 ^ e = 1
  /-- the top of the layer tower is `Ω₁(P)`. -/
  htopA : powSub A (2 ^ (e - 1)) = omega1 P
  /-- the kernel of the power map, elementwise. -/
  hkey : ∀ x ∈ A, x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1

variable {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]

/-- `Ω₁(P) ≤ A` in the situation of Lemma 8 with `A ≠ ⊥`. -/
theorem L8D.omega1_le (S : L8D h A C) : omega1 P ≤ A := S.hOmega

/-- `A ⊓ Ω₁(P) = Ω₁(P)` in the situation of Lemma 8 with `A ≠ ⊥`. -/
theorem L8D.inf_omega1_eq (S : L8D h A C) : A ⊓ omega1 P = omega1 P :=
  inf_eq_right.mpr S.hOmega

/-- The `2 ^ (e-1)`-st power of an element of `A` is an involution. -/
theorem mem_omega1_pow_two_pow_sub_one' (S : L8D h A C) {x : P} (hx : x ∈ A) :
    x ^ 2 ^ (S.e - 1) ∈ omega1 P := by
  rw [h.mem_omega1, ← pow_mul,
    show 2 ^ (S.e - 1) * 2 = 2 ^ S.e from by rw [← pow_succ, Nat.sub_add_cancel S.he]]
  exact S.he1 x hx

/-- `Ω₁(P) ⊆ A²` when `2 ≤ e`. -/
theorem L8D.omega1_le_powSub_two (S : L8D h A C) : omega1 P ≤ powSub A 2 := by
  have he2 : 2 ≤ S.e := S.he2
  rw [← S.htopA]
  refine powSub_le_of_dvd S.hA.abelian ⟨2 ^ (S.e - 2), ?_⟩
  show 2 ^ (S.e - 1) = 2 * 2 ^ (S.e - 2)
  rw [mul_comm, ← pow_succ, show S.e - 2 + 1 = S.e - 1 from by omega]

/-- `A ^ 2 ≠ ⊥` in the situation of Lemma 8 with `2 ≤ e` and `A ≠ ⊥`. -/
theorem L8D.powSub_two_ne_bot (S : L8D h A C) : powSub A 2 ≠ ⊥ := by
  intro hbot
  have h1 : omega1 P ≤ (⊥ : Subgroup P) := S.omega1_le_powSub_two.trans (le_of_eq hbot)
  have h2 : Nat.card ↥(omega1 P) = 1 := by
    rw [le_bot_iff.mp h1, Subgroup.card_bot]
  have h3 := h.omega1_card_ge_four
  rw [h2] at h3
  omega

/-! ## The first layer `V = C / A` and the choice of representatives -/

/-- A representative in `↥C` of a coset of `C/A`. -/
noncomputable def repC (x : ↥C ⧸ (A.subgroupOf C)) : ↥C :=
  Classical.choose (Quotient.exists_rep x)

/-- The defining property of `repC`. -/
theorem repC_spec (x : ↥C ⧸ (A.subgroupOf C)) :
    QuotientGroup.mk (repC (A := A) (C := C) x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

/-- Two elements of `↥C` with the same image in `C/A` differ by an element of `A`. -/
theorem repC_mul_inv_mem {x : ↥C ⧸ (A.subgroupOf C)} {u : ↥C}
    (hu : QuotientGroup.mk u = x) : (((repC (A := A) (C := C) x)⁻¹ * u : ↥C) : P) ∈ A := by
  have h1 : (QuotientGroup.mk (repC (A := A) (C := C) x) : ↥C ⧸ (A.subgroupOf C))
      = QuotientGroup.mk u := by rw [repC_spec, hu]
  exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1)

/-! ## The commutator pairing `BV : V → V → W` -/

/-- **The commutator pairing** `BV : C/A × C/A → Ω₁(P)`,
`(uA, vA) ↦ (⁅u⁻¹,v⁆) ^ 2 ^ (e-1)`.  This is the pairing `L₁ × L₁ → L₂` composed with
the power-map identification `A/A² ≅ Ω₁(P)`. -/
noncomputable def BV (S : L8D (P := P) h A C) (x y : ↥C ⧸ (A.subgroupOf C)) : ↥(omega1 P) := by
  refine ⟨(⁅(((repC (A := A) (C := C) x : ↥C) : P))⁻¹,
      ((repC (A := A) (C := C) y : ↥C) : P)⁆) ^ 2 ^ (S.e - 1), ?_⟩
  have hmem : ⁅(((repC (A := A) (C := C) x : ↥C) : P))⁻¹,
      ((repC (A := A) (C := C) y : ↥C) : P)⁆ ∈ (⁅C, C⁆ : Subgroup P) :=
    Subgroup.commutator_mem_commutator
      (Subgroup.inv_mem C (repC (A := A) (C := C) x).2)
      (repC (A := A) (C := C) y).2
  exact mem_omega1_pow_two_pow_sub_one' S (S.hCd ▸ hmem)

/-- `BV` evaluated on the chosen representatives. -/
theorem BV_apply (S : L8D (P := P) h A C) (x y : ↥C ⧸ (A.subgroupOf C)) :
    ((BV S x y : ↥(omega1 P)) : P)
      = (⁅(((repC (A := A) (C := C) x : ↥C) : P))⁻¹,
          ((repC (A := A) (C := C) y : ↥C) : P)⁆) ^ 2 ^ (S.e - 1) := rfl

/-- **The power map** `sV : C/A → Ω₁(P)`, `uA ↦ u ^ 2 ^ e`. -/
noncomputable def sV (S : L8D (P := P) h A C) (x : ↥C ⧸ (A.subgroupOf C)) : ↥(omega1 P) :=
  sQuot h S.hA S.hC2 S.he1 S.he x

/-- `sV` on a representative. -/
theorem sV_mk (S : L8D (P := P) h A C) (u : ↥C) :
    ((sV S (QuotientGroup.mk u) : ↥(omega1 P)) : P) = (u : P) ^ 2 ^ S.e :=
  sQuot_mk h S.hA S.hC2 S.he1 S.he u

/-! ## The lifts of `W = Ω₁(P)` up to `A` and the bracket `betaV` -/

/-- Every element of `Ω₁(P)` is a `2 ^ (e-1)`-st power in `A`. -/
theorem exists_liftA (S : L8D (P := P) h A C) (w : ↥(omega1 P)) :
    ∃ a : ↥A, (a : P) ^ 2 ^ (S.e - 1) = (w : P) := by
  have hmem : (w : P) ∈ powSub A (2 ^ (S.e - 1)) := by
    rw [S.htopA]
    exact w.2
  obtain ⟨a, ha, haeq⟩ := (mem_powSub_iff S.hA.abelian).mp hmem
  exact ⟨⟨a, ha⟩, haeq⟩

/-- A chosen lift of `w ∈ Ω₁(P)` to `A`: an element whose `2 ^ (e-1)`-st power is `w`. -/
noncomputable def liftA (S : L8D (P := P) h A C) (w : ↥(omega1 P)) : ↥A :=
  Classical.choose (exists_liftA S w)

/-- The defining property of `liftA`. -/
theorem liftA_spec (S : L8D (P := P) h A C) (w : ↥(omega1 P)) :
    ((liftA S w : ↥A) : P) ^ 2 ^ (S.e - 1) = (w : P) :=
  Classical.choose_spec (exists_liftA S w)

/-- `⁅C,A⁆ ≤ A²`: the unipotence relation, in the form `⁅u,a⁆ ∈ A²`. -/
theorem commutator_mem_powSub_two' (S : L8D (P := P) h A C) (u : P) (a : ↥A) :
    ⁅u, (a : P)⁆ ∈ powSub A 2 :=
  commutator_mem_powSub_two h S.hA u (a : P) a.2

/-- **The bracket pairing** `betaV : C/A × Ω₁(P) → Ω₁(P)`,
`(uA, p a) ↦ (⁅u,a⁆) ^ 2 ^ (e-2)`, where `p a = a ^ 2 ^ (e-1)`.  This is the bracket
`L₁ × L₂ → L₃` composed with the identification `A²/A⁴ ≅ Ω₁(P)`. -/
noncomputable def betaV (S : L8D (P := P) h A C)
    (x : ↥C ⧸ (A.subgroupOf C)) (w : ↥(omega1 P)) : ↥(omega1 P) := by
  refine ⟨(⁅((repC (A := A) (C := C) x : ↥C) : P), ((liftA S w : ↥A) : P)⁆) ^ 2 ^ (S.e - 2), ?_⟩
  have hmem : ⁅((repC (A := A) (C := C) x : ↥C) : P), ((liftA S w : ↥A) : P)⁆ ∈ powSub A 2 :=
    commutator_mem_powSub_two' S _ _
  have hexp : (⁅((repC (A := A) (C := C) x : ↥C) : P), ((liftA S w : ↥A) : P)⁆) ^ 2 ^ (S.e - 1)
      = 1 := powSub_two_exp h S.hA S.he1 hmem
  have he2 : 2 ≤ S.e := S.he2
  rw [h.mem_omega1]
  rw [← pow_mul, show 2 ^ (S.e - 2) * 2 = 2 ^ (S.e - 1) from by
    rw [← pow_succ]; congr 1; omega]
  exact hexp

/-- `betaV` evaluated on the chosen representatives. -/
theorem betaV_apply (S : L8D (P := P) h A C)
    (x : ↥C ⧸ (A.subgroupOf C)) (w : ↥(omega1 P)) :
    ((betaV S x w : ↥(omega1 P)) : P)
      = (⁅((repC (A := A) (C := C) x : ↥C) : P), ((liftA S w : ↥A) : P)⁆) ^ 2 ^ (S.e - 2) := rfl

end Work.Higman.MSA
