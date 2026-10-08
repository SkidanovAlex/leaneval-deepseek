/-
Self-contained local infrastructure for Higman's Lemma 8.

This module recreates (under a fresh namespace `Work.Higman.MSA.L8`) the quotient model
`V = C / A`, the `ξ`-action on it, and the three maps `BV`, `sV`, `betaV` of
`Submission.Work.Higman.MSA.l8_defs`.  It is a copy of the strictly necessary part of
`Submission.Work.Higman.clo_quot` and `Submission.Work.Higman.MSA.l8_defs`; those modules
currently sit behind a broken work-in-progress file and cannot be imported.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.Fq_structure
import Submission.Work.Higman.clo_setup
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

namespace Work.Higman.MSA.L8

variable {P : Type} [Group P] [Finite P]

/-! ## The `ξ`-action on an invariant subgroup -/

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

theorem xiSubAut_pow_apply (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) (k : ℕ) (x : ↥H) :
    (((xiSubAut h hinv) ^ k) x : P) = (h.xi ^ k) (x : P) := by
  revert x
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih (xiSubAut h hinv x), xiSubAut_apply, pow_succ,
        MulAut.mul_apply]

/-! ## The quotient module `V = C / A` -/

variable {A C : Subgroup P} [hAn : A.Normal]

/-- `ξ` preserves `A` viewed inside `C`. -/
theorem map_xi_subgroupOf (h : IsSuzuki2Grp P)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) :
    Subgroup.map (xiSubAut h hCinv : ↥C ≃* ↥C) (A.subgroupOf C) = A.subgroupOf C := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h1 : (((xiSubAut h hCinv) y : ↥C) : P) = h.xi (y : P) := xiSubAut_apply h hCinv y
    rw [← hyx]
    show h.xi (y : P) ∈ A
    rw [← hAinv]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hy)
  · intro hx
    refine ⟨(xiSubAut h hCinv)⁻¹ x, ?_, by simp⟩
    show h.xi.symm (x : P) ∈ A
    exact symm_mem_of_map_eq (h.xi : MulAut P) hAinv (Subgroup.mem_subgroupOf.mp hx)

/-- The automorphism of `V = C / A` induced by `ξ`. -/
noncomputable def xiQuot (h : IsSuzuki2Grp P)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) :
    (↥C ⧸ (A.subgroupOf C)) ≃* (↥C ⧸ (A.subgroupOf C)) :=
  QuotientGroup.congr (A.subgroupOf C) (A.subgroupOf C) (xiSubAut h hCinv)
    (map_xi_subgroupOf h hAinv hCinv)

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
            rw [commutatorElement_def]; group
          rwa [h]

/-- With `C ^ (2) ≤ A` the quotient has exponent two, hence `Additive` of it carries a
`ZMod 2`-module structure (`AddCommGroup.zmodModule`). -/
theorem quot_exp_two (hC2 : powSub C 2 ≤ A) :
    ∀ x : Additive (↥C ⧸ (A.subgroupOf C)), 2 • x = 0 := by
  intro x
  rw [two_nsmul]
  show Additive.ofMul (x.toMul * x.toMul) = Additive.ofMul (1 : ↥C ⧸ (A.subgroupOf C))
  rw [quot_sq_one hC2 x.toMul]

/-! ## The power map `sV : C/A → Ω₁(P)` -/

/-- **The map `s : C/A → Ω₁(P)`**, `uA ↦ u ^ (2 ^ e)`. -/
noncomputable def sQuot (h : IsSuzuki2Grp P) (hA : IsXiAbelNormal h A)
    (hC2 : powSub C 2 ≤ A) {e : ℕ}
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

theorem sQuot_mk (h : IsSuzuki2Grp P) (hA : IsXiAbelNormal h A)
    (hC2 : powSub C 2 ≤ A) {e : ℕ}
    (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he : 1 ≤ e) (u : ↥C) :
    ((sQuot h hA hC2 he1 he (QuotientGroup.mk u) : ↥(omega1 P)) : P) = (u : P) ^ 2 ^ e :=
  rfl

/-! ## The hypothesis package `D` and the three maps -/

variable {h : IsSuzuki2Grp P}

/-- The hypotheses and exponent data of Higman's Lemma 8 in the nontrivial case (`A ≠ ⊥` and
`2 ≤ e`), mirroring `Work.Higman.MSA.L8D`. -/
structure D (h : IsSuzuki2Grp P) (A C : Subgroup P) [A.Normal] where
  hA : IsXiAbelNormal h A
  hCn : C.Normal
  hCinv : C.map (h.xi : MulAut P).toMonoidHom = C
  hAC : A ≤ C
  hCA : A ≠ C
  hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C
  hC2 : powSub C 2 ≤ A
  hCd : ⁅C, C⁆ = A
  hAne : A ≠ ⊥
  hOmega : omega1 P ≤ A
  e : ℕ
  he : 1 ≤ e
  he2 : 2 ≤ e
  he1 : ∀ a ∈ A, a ^ 2 ^ e = 1
  htopA : powSub A (2 ^ (e - 1)) = omega1 P
  hkey : ∀ x ∈ A, x ∈ powSub A 2 ↔ x ^ 2 ^ (e - 1) = 1

/-! ## The first layer `V = C / A` and choices of representatives -/

/-- A representative in `↥C` of a coset of `C/A`. -/
noncomputable def repC (x : ↥C ⧸ (A.subgroupOf C)) : ↥C :=
  Classical.choose (Quotient.exists_rep x)

/-- The defining property of `repC`. -/
theorem repC_spec (x : ↥C ⧸ (A.subgroupOf C)) : QuotientGroup.mk (repC x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

/-- Two elements of `↥C` with the same image in `C/A` differ by an element of `A`. -/
theorem repC_mul_inv_mem {x : ↥C ⧸ (A.subgroupOf C)} {u : ↥C}
    (hu : QuotientGroup.mk u = x) : (((repC x)⁻¹ * u : ↥C) : P) ∈ A := by
  have h1 : (QuotientGroup.mk (repC (A := A) (C := C) x) : ↥C ⧸ (A.subgroupOf C))
      = QuotientGroup.mk u := by rw [repC_spec, hu]
  exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1)

/-! ## The commutator pairing `BV : V ⧸ ⧸ → Ω₁` -/

/-- **The commutator pairing** `BV : C/A × C/A → Ω₁(P)`,
`(uA, vA) ↦ (⁅u⁻¹,v⁆) ^ 2 ^ (e-1)`. -/
noncomputable def BV (S : D (P := P) h A C) (x y : ↥C ⧸ (A.subgroupOf C)) : ↥(omega1 P) := by
  refine ⟨(⁅(((repC (A := A) (C := C) x : ↥C) : P))⁻¹,
      ((repC (A := A) (C := C) y : ↥C) : P)⁆) ^ 2 ^ (S.e - 1), ?_⟩
  have hmem : ⁅(((repC (A := A) (C := C) x : ↥C) : P))⁻¹,
      ((repC (A := A) (C := C) y : ↥C) : P)⁆ ∈ (⁅C, C⁆ : Subgroup P) :=
    Subgroup.commutator_mem_commutator
      (Subgroup.inv_mem C (repC (A := A) (C := C) x).2)
      (repC (A := A) (C := C) y).2
  exact mem_omega1_pow_two_pow_sub_one h S.hA S.he1 S.he (S.hCd ▸ hmem)

/-- `BV` evaluated on the chosen representatives. -/
theorem BV_apply (S : D (P := P) h A C) (x y : ↥C ⧸ (A.subgroupOf C)) :
    ((BV S x y : ↥(omega1 P)) : P)
      = (⁅(((repC (A := A) (C := C) x : ↥C) : P))⁻¹,
          ((repC (A := A) (C := C) y : ↥C) : P)⁆) ^ 2 ^ (S.e - 1) := rfl

/-! ## The power map `sV : V → Ω₁` -/

/-- **The power map** `sV : C/A → Ω₁(P)`, `uA ↦ u ^ (2 ^ e)`. -/
noncomputable def sV (S : D (P := P) h A C) (x : ↥C ⧸ (A.subgroupOf C)) : ↥(omega1 P) :=
  sQuot h S.hA S.hC2 S.he1 S.he x

/-- `sV` on a representative. -/
theorem sV_mk (S : D (P := P) h A C) (u : ↥C) :
    ((sV S (QuotientGroup.mk u) : ↥(omega1 P)) : P) = (u : P) ^ 2 ^ S.e :=
  sQuot_mk h S.hA S.hC2 S.he1 S.he u

/-! ## The lifts of `Ω₁` up to `A` and the bracket `betaV` -/

/-- Every element of `Ω₁(P)` is a `2 ^ (e-1)`-st power in `A`. -/
theorem exists_liftA (S : D (P := P) h A C) (w : ↥(omega1 P)) :
    ∃ a : ↥A, (a : P) ^ 2 ^ (S.e - 1) = (w : P) := by
  have hmem : (w : P) ∈ powSub A (2 ^ (S.e - 1)) := by
    rw [S.htopA]
    exact w.2
  obtain ⟨a, ha, haeq⟩ := (mem_powSub_iff S.hA.abelian).mp hmem
  exact ⟨⟨a, ha⟩, haeq⟩

/-- A chosen lift of `w ∈ Ω₁(P)` to `A`. -/
noncomputable def liftA (S : D (P := P) h A C) (w : ↥(omega1 P)) : ↥A :=
  Classical.choose (exists_liftA S w)

/-- The defining property of `liftA`. -/
theorem liftA_spec (S : D (P := P) h A C) (w : ↥(omega1 P)) :
    ((liftA S w : ↥A) : P) ^ 2 ^ (S.e - 1) = (w : P) :=
  Classical.choose_spec (exists_liftA S w)

/-- `⁅C,A⁆ ≤ A²`: the unipotence relation, in the form `⁅u,a⁆ ∈ A²`. -/
theorem commutator_mem_powSub_two' (S : D (P := P) h A C) (u : P) (a : ↥A) :
    ⁅u, (a : P)⁆ ∈ powSub A 2 :=
  commutator_mem_powSub_two h S.hA u (a : P) a.2

/-- **The bracket pairing** `betaV : C/A × Ω₁(P) → Ω₁(P)`,
`(uA, p a) ↦ (⁅u,a⁆) ^ 2 ^ (e-2)` where `p a = a ^ 2 ^ (e-1)`. -/
noncomputable def betaV (S : D (P := P) h A C)
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
theorem betaV_apply (S : D (P := P) h A C)
    (x : ↥C ⧸ (A.subgroupOf C)) (w : ↥(omega1 P)) :
    ((betaV S x w : ↥(omega1 P)) : P)
      = (⁅((repC (A := A) (C := C) x : ↥C) : P), ((liftA S w : ↥A) : P)⁆) ^ 2 ^ (S.e - 2) := rfl

end Work.Higman.MSA.L8
