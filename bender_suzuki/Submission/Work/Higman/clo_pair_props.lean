import Mathlib
import Submission.Work.Higman.clo_hard_defs
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.squaring_layer
import Submission.Work.Higman.bracket_expansion
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.Fq_structure
import Submission.Work.Higman.clo_comm_expansion
import Submission.Work.Higman.H8.pairing_foundations

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Properties of the commutator pairing `cloBPair` of Higman's Lemma 8

Setting: `P` a Suzuki 2-group, `A` a `ξ`-invariant abelian normal subgroup, `C` a normal
`ξ`-invariant subgroup with `C ^ (2) ≤ A = ⁅C,C⁆` and `C/A` a minimal normal `ξ`-section (the
hypothesis package `CloH8Data`).

The commutator pairing is
`cloBPair S x y = ⁅u⁻¹, v⁆ ^ (2 ^ (e-1))` for representatives `u ∈ x`, `v ∈ y` of the classes
`x, y ∈ C/A` (where `2 ^ e` is the exponent of the homocyclic group `A`).  Here we prove:

* `clo_pair_wd` — the value does not depend on the chosen representatives (this is
  `Work.Higman.H8.cloBPair_mk`);
* `cloBPair_add_left`, `cloBPair_add_right` — `cloBPair` is biadditive;
* `cloBPair_diag` — `cloBPair` is alternating (`cloBPair x x = 1`);
* `cloBPair_xi` — `cloBPair` is `ξ`-equivariant;
* `cloBPair_ne_one` — `cloBPair` is non-trivial.

The key group-theoretic input is that `⁅A, P⁆ ≤ A ^ (2)` (unipotence), so that the commutator of
two elements of `C` — which lies in `⁅C,C⁆ = A` — is additive modulo `A ^ (2)` in each variable
(`Work.Higman.clo_comm_expansion`), while the `2 ^ (e-1)`-st power map kills exactly `A ^ (2)`
(Higman's Lemma 1, `Work.Higman.pow_two_pow_sub_one_class`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]
variable {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]

/-! ## The pairing on explicit representatives -/

/-- **Well-definedness of `cloBPair`.**  For `u ∈ x` and `v ∈ y` the value of the pairing is
`⁅u⁻¹, v⁆ ^ (2 ^ (e-1))`. -/
theorem clo_pair_wd (S : CloH8Data h A C) (x y : ↥C ⧸ (A.subgroupOf C)) (u v : ↥C)
    (hu : QuotientGroup.mk u = x) (hv : QuotientGroup.mk v = y) :
    ((cloBPair S x y : ↥(omega1 P)) : P)
      = ((commutatorElement (G := P)).bracket ((u : P))⁻¹ ((v : P))) ^ 2 ^ (S.e - 1) :=
  H8.cloBPair_mk S x y u v hu hv

/-! ## Biadditivity

Both proofs follow the same pattern: replace the classes by explicit representatives `u, v, w`,
use `clo_pair_wd`, and compare the two `2 ^ (e-1)`-st powers.  The two commutators involved differ
by an element of `A ^ (2)` (`clo_comm_mul_left`, `clo_comm_mul_right`), and `A ^ (2)` lies in the
kernel of the `2 ^ (e-1)`-st power map (`pow_two_pow_sub_one_class`); `A` is abelian, so the power
of a product is the product of the powers. -/

/-- **Biadditivity in the first variable, on representatives.** -/
theorem cloBPair_add_left_mk (S : CloH8Data h A C) (u v w : ↥C) :
    cloBPair S (QuotientGroup.mk (u * v)) (QuotientGroup.mk w)
      = cloBPair S (QuotientGroup.mk u) (QuotientGroup.mk w)
        * cloBPair S (QuotientGroup.mk v) (QuotientGroup.mk w) := by
  have huA : ⁅(u : P)⁻¹, (w : P)⁆ ∈ A := by
    rw [← S.hCd]
    exact Subgroup.commutator_mem_commutator (C.inv_mem u.2) w.2
  have hvA : ⁅(v : P)⁻¹, (w : P)⁆ ∈ A := by
    rw [← S.hCd]
    exact Subgroup.commutator_mem_commutator (C.inv_mem v.2) w.2
  have hbA : ⁅(v : P)⁻¹ * (u : P)⁻¹, (w : P)⁆ ∈ A := by
    rw [← S.hCd]
    exact Subgroup.commutator_mem_commutator (C.mul_mem (C.inv_mem v.2) (C.inv_mem u.2)) w.2
  have hcw : ⁅(v : P)⁻¹ * (u : P)⁻¹, (w : P)⁆
      * (⁅(u : P)⁻¹, (w : P)⁆ * ⁅(v : P)⁻¹, (w : P)⁆)⁻¹ ∈ powSub A 2 :=
    clo_comm_mul_left h S.hA S.hCd (C.inv_mem v.2) (C.inv_mem u.2) w.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [H8.cloBPair_mk S _ _ (u * v) w rfl rfl, H8.cloBPair_mk S _ _ u w rfl rfl,
    H8.cloBPair_mk S _ _ v w rfl rfl]
  have hprod : ((((u * v : ↥C) : P)))⁻¹ = ((v : P)⁻¹ * (u : P)⁻¹) := by
    rw [Subgroup.coe_mul, mul_inv_rev]
  rw [hprod,
    pow_two_pow_sub_one_class h S.hA (e := S.e) S.he1
      (a := ⁅(u : P)⁻¹, (w : P)⁆ * ⁅(v : P)⁻¹, (w : P)⁆)
      (b := ⁅(v : P)⁻¹ * (u : P)⁻¹, (w : P)⁆)
      (Subgroup.mul_mem _ huA hvA) hbA hcw,
    Commute.mul_pow (show Commute ⁅(u : P)⁻¹, (w : P)⁆ ⁅(v : P)⁻¹, (w : P)⁆ from
      S.hA.abelian _ huA _ hvA)]

/-- **Biadditivity in the second variable, on representatives.** -/
theorem cloBPair_add_right_mk (S : CloH8Data h A C) (u v w : ↥C) :
    cloBPair S (QuotientGroup.mk u) (QuotientGroup.mk (v * w))
      = cloBPair S (QuotientGroup.mk u) (QuotientGroup.mk v)
        * cloBPair S (QuotientGroup.mk u) (QuotientGroup.mk w) := by
  have huA : ⁅(u : P)⁻¹, (v : P)⁆ ∈ A := by
    rw [← S.hCd]
    exact Subgroup.commutator_mem_commutator (C.inv_mem u.2) v.2
  have hwA : ⁅(u : P)⁻¹, (w : P)⁆ ∈ A := by
    rw [← S.hCd]
    exact Subgroup.commutator_mem_commutator (C.inv_mem u.2) w.2
  have hbA : ⁅(u : P)⁻¹, (v : P) * (w : P)⁆ ∈ A := by
    rw [← S.hCd]
    exact Subgroup.commutator_mem_commutator (C.inv_mem u.2) (C.mul_mem v.2 w.2)
  have hcw : ⁅(u : P)⁻¹, (v : P) * (w : P)⁆
      * (⁅(u : P)⁻¹, (v : P)⁆ * ⁅(u : P)⁻¹, (w : P)⁆)⁻¹ ∈ powSub A 2 :=
    clo_comm_mul_right h S.hA S.hCd (C.inv_mem u.2) v.2 w.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [H8.cloBPair_mk S _ _ u (v * w) rfl rfl, H8.cloBPair_mk S _ _ u v rfl rfl,
    H8.cloBPair_mk S _ _ u w rfl rfl]
  rw [show (((v * w : ↥C) : P)) = (v : P) * (w : P) from rfl,
    pow_two_pow_sub_one_class h S.hA (e := S.e) S.he1
      (a := ⁅(u : P)⁻¹, (v : P)⁆ * ⁅(u : P)⁻¹, (w : P)⁆)
      (b := ⁅(u : P)⁻¹, (v : P) * (w : P)⁆)
      (Subgroup.mul_mem _ huA hwA) hbA hcw,
    Commute.mul_pow (show Commute ⁅(u : P)⁻¹, (v : P)⁆ ⁅(u : P)⁻¹, (w : P)⁆ from
      S.hA.abelian _ huA _ hwA)]

/-- **`cloBPair` is biadditive in the first variable.** -/
theorem cloBPair_add_left (S : CloH8Data h A C) (x y z : ↥C ⧸ (A.subgroupOf C)) :
    cloBPair S (x * y) z = cloBPair S x z * cloBPair S y z := by
  induction x using QuotientGroup.induction_on with
  | _ u =>
    induction y using QuotientGroup.induction_on with
    | _ v =>
      induction z using QuotientGroup.induction_on with
      | _ w =>
        rw [← QuotientGroup.mk_mul]
        exact cloBPair_add_left_mk S u v w

/-- **`cloBPair` is biadditive in the second variable.** -/
theorem cloBPair_add_right (S : CloH8Data h A C) (x y z : ↥C ⧸ (A.subgroupOf C)) :
    cloBPair S x (y * z) = cloBPair S x y * cloBPair S x z := by
  induction x using QuotientGroup.induction_on with
  | _ u =>
    induction y using QuotientGroup.induction_on with
    | _ v =>
      induction z using QuotientGroup.induction_on with
      | _ w =>
        rw [← QuotientGroup.mk_mul]
        exact cloBPair_add_right_mk S u v w

/-! ## Alternation, `ξ`-equivariance and non-triviality -/

/-- **`cloBPair` is alternating.** -/
theorem cloBPair_diag (S : CloH8Data h A C) (x : ↥C ⧸ (A.subgroupOf C)) :
    cloBPair S x x = 1 := by
  induction x using QuotientGroup.induction_on with
  | _ u =>
    apply Subtype.ext
    rw [H8.cloBPair_mk S _ _ u u rfl rfl]
    have h1 : ⁅(u : P)⁻¹, (u : P)⁆ = 1 := by
      rw [commutatorElement_def]; group
    rw [h1, one_pow]
    rfl

/-- `ξ` commutes with the commutator-power expression `⁅x⁻¹, y⁆ ^ k`. -/
theorem clo_xi_commutator_pow (h : IsSuzuki2Grp P) (x y : P) (k : ℕ) :
    h.xi (⁅x⁻¹, y⁆ ^ k) = ⁅(h.xi x)⁻¹, (h.xi y)⁆ ^ k := by
  rw [map_pow]
  congr 1
  simp only [commutatorElement_def, map_mul, map_inv]

/-- **`cloBPair` is `ξ`-equivariant.** -/
theorem cloBPair_xi (S : CloH8Data h A C) (x y : ↥C ⧸ (A.subgroupOf C)) :
    cloXiOm h (cloBPair S x y)
      = cloBPair S (cloXiQuot h S.hA.map_eq S.hCinv x)
          (cloXiQuot h S.hA.map_eq S.hCinv y) := by
  induction x using QuotientGroup.induction_on with
  | _ u =>
    induction y using QuotientGroup.induction_on with
    | _ v =>
      rw [cloXiQuot_mk, cloXiQuot_mk]
      apply Subtype.ext
      rw [cloXiOm_apply, H8.cloBPair_mk S _ _ u v rfl rfl,
        H8.cloBPair_mk S _ _ (cloXiC h S.hCinv u) (cloXiC h S.hCinv v) rfl rfl,
        clo_xi_commutator_pow, cloXiSub_apply h S.hCinv u, cloXiSub_apply h S.hCinv v]

/-- There is a commutator `⁅u⁻¹, v⁆` with `u, v ∈ C` which does not lie in `A ^ (2)`. -/
theorem clo_comm_notMem_powSub_two (S : CloH8Data h A C) :
    ∃ u ∈ C, ∃ v ∈ C, ⁅u⁻¹, v⁆ ∉ powSub A 2 := by
  by_contra hcon
  push Not at hcon
  refine H8.not_le_powSub_two S ?_
  have hle : ⁅C, C⁆ ≤ powSub A 2 := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have h1 : ⁅(x⁻¹)⁻¹, y⁆ ∈ powSub A 2 := hcon x⁻¹ (C.inv_mem hx) y hy
    simpa using h1
  rwa [S.hCd] at hle

/-- **`cloBPair` is non-trivial.** -/
theorem cloBPair_ne_one (S : CloH8Data h A C) :
    ∃ x y : ↥C ⧸ (A.subgroupOf C), cloBPair S x y ≠ 1 := by
  obtain ⟨u, hu, v, hv, huv⟩ := clo_comm_notMem_powSub_two S
  refine ⟨QuotientGroup.mk ⟨u, hu⟩, QuotientGroup.mk ⟨v, hv⟩, ?_⟩
  intro hcon
  have h1 : ⁅(u : P)⁻¹, (v : P)⁆ ^ 2 ^ (S.e - 1) = 1 := by
    have h2 := congrArg (fun t : ↥(omega1 P) => (t : P)) hcon
    rw [H8.cloBPair_mk S _ _ ⟨u, hu⟩ ⟨v, hv⟩ rfl rfl, Subgroup.coe_one] at h2
    exact h2
  have hmem : ⁅(u : P)⁻¹, (v : P)⁆ ∈ A := by
    rw [← S.hCd]
    exact Subgroup.commutator_mem_commutator (C.inv_mem hu) hv
  exact huv ((S.hkey _ hmem).mpr h1)

/-! ## The statement -/

theorem clo_pair_props {P : Type} [Group P] [Finite P] {h : IsSuzuki2Grp P} {A C : Subgroup P}
    [A.Normal] (S : CloH8Data h A C) :
    (∀ (x y : ↥C ⧸ (A.subgroupOf C)) (u v : ↥C),
      QuotientGroup.mk u = x → QuotientGroup.mk v = y →
      ((cloBPair S x y : ↥(omega1 P)) : P)
        = ((commutatorElement (G := P)).bracket ((u : P))⁻¹ ((v : P))) ^ 2 ^ (S.e - 1)) ∧
    (∀ x y z : ↥C ⧸ (A.subgroupOf C), cloBPair S (x * y) z = cloBPair S x z * cloBPair S y z) ∧
    (∀ x y z : ↥C ⧸ (A.subgroupOf C), cloBPair S x (y * z) = cloBPair S x y * cloBPair S x z) ∧
    (∀ x : ↥C ⧸ (A.subgroupOf C), cloBPair S x x = 1) ∧
    (∀ x y : ↥C ⧸ (A.subgroupOf C),
      cloXiOm h (cloBPair S x y)
        = cloBPair S (cloXiQuot h S.hA.map_eq S.hCinv x) (cloXiQuot h S.hA.map_eq S.hCinv y)) ∧
    (∃ x y : ↥C ⧸ (A.subgroupOf C), cloBPair S x y ≠ 1) :=
  ⟨fun x y u v hu hv => clo_pair_wd S x y u v hu hv,
    fun x y z => cloBPair_add_left S x y z,
    fun x y z => cloBPair_add_right S x y z,
    fun x => cloBPair_diag S x,
    fun x y => cloBPair_xi S x y,
    cloBPair_ne_one S⟩

end Work.Higman
