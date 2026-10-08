import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.powSub_C_eq_of_cover
import Submission.Work.Higman.Fq_structure
import Submission.Work.Higman.clo_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Higman's Lemma 8: the objects of the two layers `V = C/A`, `W = Ω₁(P)` and the pairings

This file is a *self-contained* (import-cycle free) copy of the objects used in the proof of
Higman's auxiliary result 8: the quotient `V = C/A` with its induced `ξ`-action, the power map
`sV : V → Ω₁(P)`, the commutator pairing `BPair : V × V → Ω₁(P)` and the bracket
`betaV : V × Ω₁(P) → Ω₁(P)`.

Setting: `P` a Suzuki 2-group with automorphism `ξ`, `A ≤ C` subgroups with `A` a `ξ`-invariant
abelian normal subgroup, `C` a `ξ`-invariant normal subgroup, `C/A` a minimal normal `ξ`-section,
`C ^ (2) ≤ A`, `⁅C,C⁆ = A` (Higman's Lemma 8), `A ≠ ⊥` (so `Ω₁(P) ≤ A`) and `A ^ 2 ≠ ⊥`.
The exponent parameter `e` is the one of Higman's Lemma 1: `2 ^ e` is the exponent of the
homocyclic group `A`, `A ^ (2 ^ (e-1)) = Ω₁(P)`, and for `x ∈ A`, `x ∈ A² ↔ x ^ 2 ^ (e-1) = 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-! ## The automorphism induced by `ξ` on a `ξ`-invariant subgroup -/

/-- The automorphism of `↥H` induced by `ξ` when `H` is `ξ`-invariant. -/
noncomputable def cloXiSub (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) : MulAut ↥H where
  toFun x := ⟨h.xi (x : P), by
    have hx := Subgroup.mem_map_of_mem ((h.xi : MulAut P).toMonoidHom) x.2
    rwa [hinv] at hx⟩
  invFun x := ⟨(h.xi : MulAut P).symm (x : P),
    symm_mem_of_map_eq (h.xi : MulAut P) hinv x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem cloXiSub_apply (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) (x : ↥H) :
    ((cloXiSub h hinv x : ↥H) : P) = h.xi (x : P) := rfl

theorem cloXiSub_pow_apply (h : IsSuzuki2Grp P) {H : Subgroup P}
    (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) (k : ℕ) (x : ↥H) :
    (((cloXiSub h hinv) ^ k) x : P) = (h.xi ^ k) (x : P) := by
  revert x
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih (cloXiSub h hinv x), cloXiSub_apply, pow_succ,
        MulAut.mul_apply]

/-! ## `Ω₁(P)` with its `ξ`-action -/

/-- The automorphism of `Ω₁(P)` induced by `ξ`. -/
noncomputable def cloXiOm (h : IsSuzuki2Grp P) : ↥(omega1 P) ≃* ↥(omega1 P) :=
  cloXiSub h (map_xi_omega1 h)

theorem cloXiOm_apply (h : IsSuzuki2Grp P) (z : ↥(omega1 P)) :
    ((cloXiOm h z : ↥(omega1 P)) : P) = h.xi (z : P) := rfl

theorem cloXiOm_pow_apply (h : IsSuzuki2Grp P) (k : ℕ) (z : ↥(omega1 P)) :
    (((cloXiOm h) ^ k) z : P) = (h.xi ^ k) (z : P) :=
  cloXiSub_pow_apply h (map_xi_omega1 h) k z

/-! ## The quotient `V = C/A` with its induced `ξ`-action -/

section Quot

variable {A C : Subgroup P} [hAn : A.Normal]

/-- Every element of `C / A` is an involution (`C ^ (2) ≤ A`). -/
theorem cloQuot_sq_one (hC2 : powSub C 2 ≤ A) (x : ↥C ⧸ (A.subgroupOf C)) : x * x = 1 := by
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
theorem cloQuot_comm (hCd : ⁅C, C⁆ = A) (x y : ↥C ⧸ (A.subgroupOf C)) : x * y = y * x := by
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
noncomputable abbrev cloXiC (h : IsSuzuki2Grp P)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) : MulAut ↥C :=
  cloXiSub h hCinv

/-- `ξ` preserves `A` viewed inside `C`. -/
theorem clo_map_xi_subgroupOf (h : IsSuzuki2Grp P)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) :
    Subgroup.map (cloXiC h hCinv : ↥C ≃* ↥C) (A.subgroupOf C) = A.subgroupOf C := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h1 : (((cloXiC h hCinv) y : ↥C) : P) = h.xi (y : P) := cloXiSub_apply h hCinv y
    rw [← hyx]
    show h.xi (y : P) ∈ A
    rw [← hAinv]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hy)
  · intro hx
    refine ⟨(cloXiC h hCinv)⁻¹ x, ?_, by simp⟩
    show h.xi.symm (x : P) ∈ A
    exact symm_mem_of_map_eq (h.xi : MulAut P) hAinv (Subgroup.mem_subgroupOf.mp hx)

/-- **The automorphism of `V = C / A` induced by `ξ`.** -/
noncomputable def cloXiQuot (h : IsSuzuki2Grp P)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) :
    (↥C ⧸ (A.subgroupOf C)) ≃* (↥C ⧸ (A.subgroupOf C)) :=
  QuotientGroup.congr (A.subgroupOf C) (A.subgroupOf C) (cloXiC h hCinv)
    (clo_map_xi_subgroupOf h hAinv hCinv)

/-- The power map `V → Ω₁(P)`, `uA ↦ u ^ 2 ^ e`, well defined by `clo_setup.pow_two_pow_mul_mem`. -/
noncomputable def cloSQuot (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
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

/-- The value of `cloSQuot` on a representative. -/
theorem cloSQuot_mk (h : IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hA : IsXiAbelNormal h A) (hC2 : powSub C 2 ≤ A) {e : ℕ}
    (he1 : ∀ a ∈ A, a ^ 2 ^ e = 1) (he : 1 ≤ e) (u : ↥C) :
    ((cloSQuot h hA hC2 he1 he (QuotientGroup.mk u) : ↥(omega1 P)) : P) = (u : P) ^ 2 ^ e :=
  rfl

end Quot

/-! ## The hypothesis package of Lemma 8 in the nontrivial case -/

/-- The hypotheses and exponent data of Higman's Lemma 8 in the nontrivial case: `A ≠ ⊥` and
`2 ≤ e`, where `2 ^ e` is the exponent of the homocyclic group `A`. -/
structure CloH8Data (h : IsSuzuki2Grp P) (A C : Subgroup P) [A.Normal] where
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

namespace CloH8Data

variable {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]

theorem omega1_le (S : CloH8Data h A C) : omega1 P ≤ A := S.hOmega

theorem inf_omega1_eq (S : CloH8Data h A C) : A ⊓ omega1 P = omega1 P :=
  inf_eq_right.mpr S.hOmega

end CloH8Data

/-! ## The pairings on the first layer -/

variable {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]

/-- A representative in `↥C` of a coset of `C/A`. -/
noncomputable def cloRepC (x : ↥C ⧸ (A.subgroupOf C)) : ↥C :=
  Classical.choose (Quotient.exists_rep x)

/-- The defining property of `cloRepC`. -/
theorem cloRepC_spec (x : ↥C ⧸ (A.subgroupOf C)) :
    QuotientGroup.mk (cloRepC x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

/-- Two elements of `↥C` with the same image in `C/A` differ by an element of `A`. -/
theorem cloRepC_mul_inv_mem {x : ↥C ⧸ (A.subgroupOf C)} {u : ↥C}
    (hu : QuotientGroup.mk u = x) : (((cloRepC x)⁻¹ * u : ↥C) : P) ∈ A := by
  have h1 : (QuotientGroup.mk (cloRepC (A := A) (C := C) x) : ↥C ⧸ (A.subgroupOf C))
      = QuotientGroup.mk u := by rw [cloRepC_spec, hu]
  exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1)

/-- **The power map** `cloSM : C/A → Ω₁(P)`, `uA ↦ u ^ 2 ^ e`. -/
noncomputable def cloSM (S : CloH8Data h A C) (x : ↥C ⧸ (A.subgroupOf C)) : ↥(omega1 P) :=
  cloSQuot h S.hA S.hC2 S.he1 S.he x

/-- `cloSM` on a representative. -/
theorem cloSM_mk (S : CloH8Data h A C) (u : ↥C) :
    ((cloSM S (QuotientGroup.mk u) : ↥(omega1 P)) : P) = (u : P) ^ 2 ^ S.e :=
  cloSQuot_mk h S.hA S.hC2 S.he1 S.he u

/-- **The commutator pairing** `cloBPair : C/A × C/A → Ω₁(P)`,
`(uA, vA) ↦ (⁅u⁻¹,v⁆) ^ 2 ^ (e-1)`. -/
noncomputable def cloBPair (S : CloH8Data h A C) (x y : ↥C ⧸ (A.subgroupOf C)) :
    ↥(omega1 P) := by
  refine ⟨(⁅(((cloRepC (A := A) (C := C) x : ↥C) : P))⁻¹,
      ((cloRepC (A := A) (C := C) y : ↥C) : P)⁆) ^ 2 ^ (S.e - 1), ?_⟩
  have hmem : ⁅(((cloRepC (A := A) (C := C) x : ↥C) : P))⁻¹,
      ((cloRepC (A := A) (C := C) y : ↥C) : P)⁆ ∈ (⁅C, C⁆ : Subgroup P) :=
    Subgroup.commutator_mem_commutator
      (Subgroup.inv_mem C (cloRepC (A := A) (C := C) x).2)
      (cloRepC (A := A) (C := C) y).2
  exact mem_omega1_pow_two_pow_sub_one h S.hA S.he1 S.he (S.hCd ▸ hmem)

theorem cloBPair_apply (S : CloH8Data h A C) (x y : ↥C ⧸ (A.subgroupOf C)) :
    ((cloBPair S x y : ↥(omega1 P)) : P)
      = (⁅(((cloRepC (A := A) (C := C) x : ↥C) : P))⁻¹,
          ((cloRepC (A := A) (C := C) y : ↥C) : P)⁆) ^ 2 ^ (S.e - 1) := rfl

/-- Every element of `Ω₁(P)` is a `2 ^ (e-1)`-st power in `A`. -/
theorem clo_exists_liftA (S : CloH8Data h A C) (w : ↥(omega1 P)) :
    ∃ a : ↥A, (a : P) ^ 2 ^ (S.e - 1) = (w : P) := by
  have hmem : (w : P) ∈ powSub A (2 ^ (S.e - 1)) := by
    rw [S.htopA]
    exact w.2
  obtain ⟨a, ha, haeq⟩ := (mem_powSub_iff S.hA.abelian).mp hmem
  exact ⟨⟨a, ha⟩, haeq⟩

/-- A chosen lift of `w ∈ Ω₁(P)` to `A`. -/
noncomputable def cloLiftA (S : CloH8Data h A C) (w : ↥(omega1 P)) : ↥A :=
  Classical.choose (clo_exists_liftA S w)

theorem cloLiftA_spec (S : CloH8Data h A C) (w : ↥(omega1 P)) :
    ((cloLiftA S w : ↥A) : P) ^ 2 ^ (S.e - 1) = (w : P) :=
  Classical.choose_spec (clo_exists_liftA S w)

/-- **The bracket pairing** `cloBetaV : C/A × Ω₁(P) → Ω₁(P)`,
`(uA, p a) ↦ (⁅u,a⁆) ^ 2 ^ (e-2)`. -/
noncomputable def cloBetaV (S : CloH8Data h A C)
    (x : ↥C ⧸ (A.subgroupOf C)) (w : ↥(omega1 P)) : ↥(omega1 P) := by
  refine ⟨(⁅((cloRepC (A := A) (C := C) x : ↥C) : P),
      ((cloLiftA S w : ↥A) : P)⁆) ^ 2 ^ (S.e - 2), ?_⟩
  have he2 : 2 ≤ S.e := S.he2
  have hmem : ⁅((cloRepC (A := A) (C := C) x : ↥C) : P),
      ((cloLiftA S w : ↥A) : P)⁆ ∈ powSub A 2 :=
    commutator_mem_powSub_two h S.hA _ ((cloLiftA S w : ↥A) : P) (cloLiftA S w).2
  have hexp : (⁅((cloRepC (A := A) (C := C) x : ↥C) : P),
      ((cloLiftA S w : ↥A) : P)⁆) ^ 2 ^ (S.e - 1) = 1 :=
    powSub_two_exp h S.hA S.he1 hmem
  rw [h.mem_omega1]
  rw [← pow_mul, show 2 ^ (S.e - 2) * 2 = 2 ^ (S.e - 1) from by
    rw [← pow_succ]; congr 1; omega]
  exact hexp

theorem cloBetaV_apply (S : CloH8Data h A C)
    (x : ↥C ⧸ (A.subgroupOf C)) (w : ↥(omega1 P)) :
    ((cloBetaV S x w : ↥(omega1 P)) : P)
      = (⁅((cloRepC (A := A) (C := C) x : ↥C) : P), ((cloLiftA S w : ↥A) : P)⁆) ^ 2 ^ (S.e - 2) :=
  rfl

end Work.Higman
