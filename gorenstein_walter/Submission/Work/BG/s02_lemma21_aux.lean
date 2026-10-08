import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.centralValue
import Submission.Work.BG.Lambda
import Submission.Work.BG.CharBridge
import Submission.Work.BG.sconjLam
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.lambda_mul_mem
import Submission.Work.BG.sq_eq_one_eq_of_isCyclic

/-!
# Area BG: foundations for BG Lemma 2.1 (`Work.BG.Lemma21Prop`)

This module collects the group-theoretic facts about the `Λ`-orbit of an irreducible
character of `H₀` that Bender–Glauberman's Lemma 2.1 (p. 204) is about.

The standing data is a `Sec2Ctx G` (`Work.BG.Sec2Ctx`), so in particular

* `Q := quotGroup C.P = H₀/U` is a **cyclic 2-group** (`C.quot_cyclic`, `C.quot_two`),
  hence commutative (`quot_comm`, `quotCommGroup`);
* `Λ := quotGroup C.P →* ℂˣ` is its character group, with a canonical commutative group
  structure, and it is finite (`Finite` instance from `HasEnoughRootsOfUnity`);
* `a := quotMk C.P C.t` is the unique element of order `2` of `Q`
  (`quotMk_t_ne_one`, `quotMk_t_sq`), and the evaluation `ev_a : Λ →* ℂˣ` is onto `{±1}`
  (`exists_negChar`).
-/

set_option linter.style.haveILetI false

namespace Work.BG

open OddOrder.RepresentationTheory
open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- `Λ = Hom(H₀/U, ℂˣ)`, the character group of `H₀/U`. -/
abbrev Lam (C : Sec2Ctx G) : Type := quotGroup C.P →* ℂˣ

/-! ## 0. Group identities in `Λ`

`Λ` is a subtype of `H₀/U → ℂˣ`; its `Mul`/`Inv` instances (pointwise on the codomain
`ℂˣ`) are *definitionally* but not *syntactically* the ones attached to the `CommGroup`
instance, so the generic `rw [inv_mul_cancel]`-style lemmas do not match.  The following
one-line restatements are elaborated in the same way as goals about `Λ`, so they do match. -/

theorem lam_inv_mul_cancel (C : Sec2Ctx G) (x : Lam C) : x⁻¹ * x = 1 := inv_mul_cancel x

theorem lam_mul_inv_cancel (C : Sec2Ctx G) (x : Lam C) : x * x⁻¹ = 1 := mul_inv_cancel x

theorem lam_one_mul (C : Sec2Ctx G) (x : Lam C) : 1 * x = x := one_mul x

theorem lam_mul_one (C : Sec2Ctx G) (x : Lam C) : x * 1 = x := mul_one x

theorem lam_mul_assoc (C : Sec2Ctx G) (x y z : Lam C) : x * y * z = x * (y * z) :=
  mul_assoc x y z

theorem lam_mul_assoc' (C : Sec2Ctx G) (x y z : Lam C) : x * (y * z) = x * y * z :=
  (mul_assoc x y z).symm

theorem lam_inv_inv (C : Sec2Ctx G) (x : Lam C) : x⁻¹⁻¹ = x := inv_inv x

theorem lam_mul_inv_rev (C : Sec2Ctx G) (x y : Lam C) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
  mul_inv_rev x y

theorem lam_mul_comm (C : Sec2Ctx G) (x y : Lam C) : x * y = y * x := mul_comm x y

theorem lam_mul_mul_mul_comm (C : Sec2Ctx G) (a b c d : Lam C) :
    a * b * (c * d) = a * c * (b * d) := mul_mul_mul_comm a b c d

theorem lam_mul_left_cancel (C : Sec2Ctx G) {a b c : Lam C} (h : a * b = a * c) : b = c :=
  mul_left_cancel h

theorem lam_pow_two (C : Sec2Ctx G) (x : Lam C) : x ^ 2 = x * x := pow_two x

theorem lam_conj (C : Sec2Ctx G) (a b : Lam C) : a * (a⁻¹ * b) = b :=
  mul_inv_cancel_left a b

theorem lam_conj' (C : Sec2Ctx G) (a b : Lam C) : a⁻¹ * (a * b) = b :=
  inv_mul_cancel_left a b

/-- `a ↦ β · a` on `Λ`. -/
noncomputable def lamMulLeft (C : Sec2Ctx G) (β : Lam C) : Lam C ≃ Lam C where
  toFun a := β * a
  invFun a := β⁻¹ * a
  left_inv a := lam_conj' C β a
  right_inv a := lam_conj C β a

@[simp] theorem lamMulLeft_apply (C : Sec2Ctx G) (β a : Lam C) :
    lamMulLeft C β a = β * a := rfl

/-! ## 1. `Q = H₀/U` is a finite commutative group -/

/-- `H₀/U` is cyclic: `C.quot_cyclic` exhibits a generator. -/
theorem quot_cyclic_aux (C : Sec2Ctx G) : IsCyclic (quotGroup C.P) := by
  obtain ⟨c, hc, hgen⟩ := C.quot_cyclic
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨quotMk C.P ⟨c, hc⟩, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨k, hk⟩ := hgen (y : G) y.2
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_zpow]
  refine (QuotientGroup.eq).mpr ?_
  rw [Subgroup.mem_subgroupOf]
  have hnorm : (C.P.U.subgroupOf C.P.H0).Normal := C.U_normal
  have hyinv : (y : G)⁻¹ ∈ C.P.H0 := C.P.H0.inv_mem y.2
  have hconj := hnorm.conj_mem
    (⟨(y : G) * (c ^ k)⁻¹, C.P.U_le_H0 hk⟩ : ↥C.P.H0)
    (by rw [Subgroup.mem_subgroupOf]; exact hk)
    (⟨(y : G)⁻¹, hyinv⟩ : ↥C.P.H0)
  rw [Subgroup.mem_subgroupOf] at hconj
  simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using hconj

instance quotIsCyclic (C : Sec2Ctx G) : IsCyclic (quotGroup C.P) := quot_cyclic_aux C

/-- `H₀/U` is commutative (it is cyclic). -/
theorem quot_comm (C : Sec2Ctx G) (x y : quotGroup C.P) : x * y = y * x := by
  haveI : IsCyclic (quotGroup C.P) := quot_cyclic_aux C
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := quotGroup C.P)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
  rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]

noncomputable instance quotCommGroup (C : Sec2Ctx G) : CommGroup (quotGroup C.P) :=
  { toGroup := QuotientGroup.Quotient.group (C.P.U.subgroupOf C.P.H0)
    mul_comm := fun a b => quot_comm C a b }

instance quotFinite (C : Sec2Ctx G) : Finite (quotGroup C.P) :=
  Finite.of_surjective (quotMk C.P) (QuotientGroup.mk'_surjective _)

/-! ## 2. The evaluation at `t`, and a character with value `-1` -/

/-- `a := t·U` is nontrivial in `H₀/U`. -/
theorem quotMk_t_ne_one (C : Sec2Ctx G) : (quotMk C.P C.t : quotGroup C.P) ≠ 1 := by
  intro h
  exact C.t_not_mem_U ((QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) C.t).mp h)

/-- `a := t·U` has order two in `H₀/U`. -/
theorem quotMk_t_sq (C : Sec2Ctx G) : (quotMk C.P C.t : quotGroup C.P) ^ 2 = 1 := by
  rw [← map_pow, C.t_sq, map_one]

/-- **Existence of a character of `H₀/U` with value `-1` at `t`.**

`Λ := Hom(H₀/U, ℂˣ)` contains an element `β` with `β(tU) = -1`: since `tU ≠ 1` and `ℂ` has
enough roots of unity, the duality `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`
provides `β` with `β(tU) ≠ 1`, and `β(tU)² = β(tU²) = 1` forces `β(tU) = -1`.

This is the element of `Λ` which Bender–Glauberman write `λ₁` or `λ₂` (the two characters of
`Λ` that are inverted by `s`, p. 204). -/
theorem exists_negChar (C : Sec2Ctx G) :
    ∃ β : quotGroup C.P →* ℂˣ, lamCF C β C.t = -1 := by
  have hne : (quotMk C.P C.t : quotGroup C.P) ≠ 1 := quotMk_t_ne_one C
  obtain ⟨β, hβ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (quotGroup C.P) ℂ hne
  refine ⟨β, ?_⟩
  have h2 : β (quotMk C.P C.t) ^ 2 = 1 := by
    rw [← map_pow, quotMk_t_sq, map_one]
  have hval : ((β (quotMk C.P C.t) : ℂˣ) : ℂ) = -1 := by
    have h2' : (((β (quotMk C.P C.t) : ℂˣ) : ℂ)) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h2]; rfl
    have hfac : (((β (quotMk C.P C.t) : ℂˣ) : ℂ) - 1) *
        (((β (quotMk C.P C.t) : ℂˣ) : ℂ) + 1) = 0 := by linear_combination h2'
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) (fun hh => hβ (Units.ext hh))
    · exact add_eq_zero_iff_eq_neg.mp h
  rw [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]
  exact hval

/-! ## 3. The orbit `Λν` and irreducibility -/

/-- Membership in the `Λ`-orbit. -/
theorem mem_lamOrbit_iff (C : Sec2Ctx G) {ν χ : ClassFunction ↥C.P.H0 ℂ} :
    χ ∈ lamOrbit C ν ↔ ∃ β : quotGroup C.P →* ℂˣ, χ = lamCF C β * ν := Iff.rfl

/-- Every `lamCF C β` lies in `Λ`. -/
theorem lamCF_mem_Lambda (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) :
    lamCF C β ∈ Lambda C.P := ⟨β, rfl⟩

/-- `ν` lies in its own `Λ`-orbit. -/
theorem mem_lamOrbit_self (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    ν ∈ lamOrbit C ν := s02c_LamEquiv_refl C ν

/-- **`Λ` preserves `Irr(H₀)`**: every element of the orbit `Λν` of an irreducible `ν` is
irreducible. -/
theorem irreducible_of_mem_lamOrbit (C : Sec2Ctx G) {ν χ : ClassFunction ↥C.P.H0 ℂ}
    (hχ : χ ∈ lamOrbit C ν) (hν : IsIrreducibleCharacter ν) : IsIrreducibleCharacter χ := by
  obtain ⟨β, rfl⟩ := hχ
  exact lambda_mul_irreducible C.P (lamCF_mem_Lambda C β) hν

/-! ## 4. `s` centralises `t` -/

/-- Conjugation by `s` fixes `t` (since `t` is central in `H ∋ s`). -/
theorem conjMulEquiv_s_t (C : Sec2Ctx G) : conjMulEquiv C.P C.s C.t = C.t := by
  apply Subtype.ext
  rw [conjMulEquiv_apply, C.t_comm_H (C.s : G) C.s.2, mul_assoc, mul_inv_cancel, mul_one]

/-- `ν^s(t) = ν(t)`. -/
theorem sconj_apply_t (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C ν C.t = ν C.t := by
  rw [sconj, conjByH_apply, conjMulEquiv_s_t]

/-! ## 5. The `2`-torsion of `Q` and of `Λ = Hom(Q, ℂˣ)` -/

/-- The `2`-torsion of `Q = H₀/U`, as a set. -/
def torsionQ (C : Sec2Ctx G) : Set (quotGroup C.P) := {q | q * q = 1}

/-- Non-identity solutions of `q² = 1` in `Q` are all equal to `tU`. -/
theorem eq_quotMk_t_of_sq_eq_one (C : Sec2Ctx G) {q : quotGroup C.P} (hq : q * q = 1)
    (hq1 : q ≠ 1) : q = quotMk C.P C.t :=
  sq_eq_one_eq_of_isCyclic hq1 (quotMk_t_ne_one C) (by rw [pow_two]; exact hq)
    (quotMk_t_sq C)

/-- **The `2`-torsion of the cyclic `2`-group `Q = H₀/U` has exactly two elements**: the
non-identity solutions of `q² = 1` in a cyclic group form a single element (`tU`). -/
theorem ncard_torsionQ (C : Sec2Ctx G) : (torsionQ C).ncard = 2 := by
  classical
  have ha1 : (quotMk C.P C.t : quotGroup C.P) ≠ 1 := quotMk_t_ne_one C
  have ha2 : (quotMk C.P C.t : quotGroup C.P) ^ 2 = 1 := quotMk_t_sq C
  have ha2' : (quotMk C.P C.t : quotGroup C.P) * (quotMk C.P C.t) = 1 := by
    rw [← pow_two]; exact ha2
  have hset : torsionQ C = ({1, quotMk C.P C.t} : Set (quotGroup C.P)) := by
    rw [torsionQ]
    ext q
    rw [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hq
      by_cases h : q = 1
      · exact Or.inl h
      · exact Or.inr (eq_quotMk_t_of_sq_eq_one C hq h)
    · rintro (rfl | rfl)
      · exact one_mul 1
      · exact ha2'
  rw [hset, Set.ncard_pair (Ne.symm ha1)]

/-- **The `2`-torsion of `Q` has exactly two elements** (subtype form). -/
theorem card_twoTorsion_quot (C : Sec2Ctx G) :
    Nat.card {q : quotGroup C.P // q * q = 1} = 2 := by
  change (torsionQ C).ncard = 2
  exact ncard_torsionQ C

/-- `2` divides `|Q|`. -/
theorem two_dvd_card_quot (C : Sec2Ctx G) : 2 ∣ Nat.card (quotGroup C.P) := by
  have ha2 : (quotMk C.P C.t : quotGroup C.P) ^ 2 = 1 := quotMk_t_sq C
  have ha1 : (quotMk C.P C.t : quotGroup C.P) ≠ 1 := quotMk_t_ne_one C
  have hord : orderOf (quotMk C.P C.t : quotGroup C.P) = 2 := orderOf_eq_prime ha2 ha1
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.zpowers (quotMk C.P C.t) : Subgroup (quotGroup C.P))
  rw [Nat.card_zpowers, hord] at h
  exact ⟨Nat.card (quotGroup C.P ⧸ Subgroup.zpowers (quotMk C.P C.t)), by rw [h, mul_comm]⟩

/-- `2` divides `|Λ|` (as `Λ ≃* Q`). -/
theorem two_dvd_card_lam (C : Sec2Ctx G) : 2 ∣ Nat.card (quotGroup C.P →* ℂˣ) := by
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (quotGroup C.P) ℂ]
  exact two_dvd_card_quot C

noncomputable instance lamFintype (C : Sec2Ctx G) : Fintype (quotGroup C.P →* ℂˣ) :=
  Fintype.ofFinite _

/-- The `2`-torsion of `Λ`, as a set. -/
def torsionSet (C : Sec2Ctx G) : Set (quotGroup C.P →* ℂˣ) := {x | x * x = 1}

@[simp] theorem mem_torsionSet (C : Sec2Ctx G) {x : quotGroup C.P →* ℂˣ} :
    x ∈ torsionSet C ↔ x * x = 1 := Iff.rfl

@[simp] theorem mem_torsionQ (C : Sec2Ctx G) {q : quotGroup C.P} :
    q ∈ torsionQ C ↔ q * q = 1 := Iff.rfl

/-- **The `2`-torsion of `Λ` has exactly two elements**, because `Λ ≃* Q` (duality of finite
abelian groups) and the `2`-torsion of the cyclic `2`-group `Q` has two elements. -/
theorem ncard_torsionSet (C : Sec2Ctx G) : (torsionSet C).ncard = 2 := by
  classical
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (quotGroup C.P) ℂ
  have h2 : (torsionSet C).ncard = (torsionQ C).ncard := by
    refine Set.ncard_congr (fun x _ => e x) ?_ ?_ ?_
    · intro x hx
      rw [mem_torsionQ, ← e.map_mul, hx, map_one]
    · intro x y _ _ hxy
      exact e.injective hxy
    · intro q hq
      refine ⟨e.symm q, ?_, e.apply_symm_apply q⟩
      rw [mem_torsionSet, ← e.map_eq_one_iff]
      simp only [map_mul, MulEquiv.apply_symm_apply]
      rw [mem_torsionQ] at hq
      exact hq
  rw [h2, ncard_torsionQ]

/-- **The `2`-torsion of `Λ` has exactly two elements** (subtype form). -/
theorem card_twoTorsion_char (C : Sec2Ctx G) :
    Nat.card {x : (quotGroup C.P →* ℂˣ) // x * x = 1} = 2 := by
  change (torsionSet C).ncard = 2
  exact ncard_torsionSet C

/-! ## 6. `ev_t` and the squares in `Λ` -/

/-- The evaluation `Λ → ℂˣ`, `β ↦ β(tU)`. -/
noncomputable def evHom (C : Sec2Ctx G) : (quotGroup C.P →* ℂˣ) →* ℂˣ where
  toFun β := β (quotMk C.P C.t)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem evHom_apply (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) :
    evHom C β = β (quotMk C.P C.t) := rfl

theorem mem_evHom_ker_iff (C : Sec2Ctx G) {β : quotGroup C.P →* ℂˣ} :
    β ∈ (evHom C).ker ↔ lamCF C β C.t = 1 := by
  rw [MonoidHom.mem_ker, ← Units.val_eq_one, evHom_apply, lamCF,
    ClassFunction.compHom_apply, linearClassFunction_apply]

/-- The set of squares in `Λ`. -/
def sqSet (C : Sec2Ctx G) : Set (quotGroup C.P →* ℂˣ) := {x | ∃ w, w * w = x}

/-- The kernel of `ev_t`, as a set: the characters of `H₀/U` trivial at `t`. -/
def kerSet (C : Sec2Ctx G) : Set (quotGroup C.P →* ℂˣ) := {x | lamCF C x C.t = 1}

@[simp] theorem mem_sqSet (C : Sec2Ctx G) {x : quotGroup C.P →* ℂˣ} :
    x ∈ sqSet C ↔ ∃ w, w * w = x := Iff.rfl

@[simp] theorem mem_kerSet (C : Sec2Ctx G) {x : quotGroup C.P →* ℂˣ} :
    x ∈ kerSet C ↔ lamCF C x C.t = 1 := Iff.rfl

/-- `Λ² ⊆ ker(ev_t)`: a square is trivial at `t`. -/
theorem sqSet_subset_kerSet (C : Sec2Ctx G) : sqSet C ⊆ kerSet C := by
  rintro x ⟨w, rfl⟩
  rw [mem_kerSet, s02c_lamCF_mul, ClassFunction.mul_apply]
  have h : lamCF C w C.t = ((w (quotMk C.P C.t) : ℂˣ) : ℂ) := by
    rw [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]
  have h2 : (w (quotMk C.P C.t)) ^ 2 = 1 := by
    rw [← map_pow, quotMk_t_sq, map_one]
  rw [h, ← Units.val_mul, ← pow_two, h2]
  rfl

end Work.BG
