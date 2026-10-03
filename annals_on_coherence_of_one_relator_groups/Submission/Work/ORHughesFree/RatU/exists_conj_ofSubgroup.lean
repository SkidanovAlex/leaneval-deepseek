import Mathlib
import Submission.Work.ORHughesFree.Rat.Source
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.Rat.Restrict
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.exists_ringEquiv_of_mulEquiv
import Submission.Work.ORHughesFree.RatU.conj_mul_identity
import Submission.Work.ORHughesFree.RatU.ofGroup_ratOp_conj

/-!
# Conjugating the image of a subgroup in `Rat(Γ)`

Let `Γ` be a group, `N ≤ Γ` a subgroup normalised by an element `t`, and `k : ℤ`.  This file shows
that the image of `Rat(N)` in `Rat(Γ)` is preserved by the inner automorphism of `Rat(Γ)` given by
conjugation by (the image of) `t ^ k`:

  `ofGroup (t ^ k) * ofSubgroup N β = ofSubgroup N β' * ofGroup (t ^ k)`

for a suitable `β' : Rat(N)` (namely the image of `β` under the ring isomorphism `Rat(N) → Rat(N)`
induced by the group automorphism `n ↦ t ^ k * n * t ^ (-k)` of `N`).

The proof is an application of the universal property of `Rat`: the two ring homomorphisms
`Rat(N) →+* Rat(Γ)` given by `β ↦ ofGroup (t^k) * ofSubgroup N β * ofGroup (t^-k)` and by
`ofSubgroup N ∘ transport` are both morphisms of rational `N`-semirings for the same structure
(the `N`-action twisted by conjugation), so they coincide by uniqueness.
-/

namespace Work.ORHughesFree.RatU

open Work.ORHughesFree

variable {Γ : Type} [Group Γ]

/-! ## Conjugation by `t ^ k` on `Γ` and on a normalised subgroup -/

/-- Conjugation by `t ^ k` as a multiplicative equivalence of `Γ`. -/
noncomputable def conjMulEquiv (t : Γ) (k : ℤ) : Γ ≃* Γ :=
  MulEquiv.mk
    { toFun := fun u => t ^ k * u * t ^ (-k)
      invFun := fun u => t ^ (-k) * u * t ^ k
      left_inv := by intro u; group
      right_inv := by intro u; group }
    (by intro u v; group)

@[simp] theorem conjMulEquiv_apply (t : Γ) (k : ℤ) (u : Γ) :
    conjMulEquiv t k u = t ^ k * u * t ^ (-k) := rfl

/-- Conjugation by `t ^ k` as a multiplicative equivalence of a subgroup `N` normalised by `t`. -/
noncomputable def conjSubMulEquiv (N : Subgroup Γ) (t : Γ)
    (htN : ∀ (k : ℤ) (n : Γ), n ∈ N → t ^ k * n * t ^ (-k) ∈ N) (k : ℤ) : ↥N ≃* ↥N :=
  MulEquiv.mk
    { toFun := fun n => ⟨t ^ k * (n : Γ) * t ^ (-k), htN k n n.2⟩
      invFun := fun n => ⟨t ^ (-k) * (n : Γ) * t ^ k, by simpa using htN (-k) n n.2⟩
      left_inv := by intro n; apply Subtype.ext; simp only [Subtype.coe_mk]; group
      right_inv := by intro n; apply Subtype.ext; simp only [Subtype.coe_mk]; group }
    (by intro a b; apply Subtype.ext; simp only [Subtype.coe_mk, Subgroup.coe_mul]; group)

@[simp] theorem conjSubMulEquiv_coe (N : Subgroup Γ) (t : Γ)
    (htN : ∀ (k : ℤ) (n : Γ), n ∈ N → t ^ k * n * t ^ (-k) ∈ N) (k : ℤ) (n : ↥N) :
    ((conjSubMulEquiv N t htN k n : ↥N) : Γ) = t ^ k * (n : Γ) * t ^ (-k) := rfl

theorem conjSubMulEquiv_coe_eq (N : Subgroup Γ) (t : Γ)
    (htN : ∀ (k : ℤ) (n : Γ), n ∈ N → t ^ k * n * t ^ (-k) ∈ N) (k : ℤ) (n : ↥N) :
    ((conjSubMulEquiv N t htN k n : ↥N) : Γ) = conjMulEquiv t k (n : Γ) := rfl

/-! ## Elementary identities for `ofGroup` -/

theorem ofGroup_zpow_mul_neg (t : Γ) (k : ℤ) :
    ofGroup (t ^ k) * ofGroup (t ^ (-k)) = (1 : RatU Γ) := by
  rw [← ofGroup_mul, ← zpow_add, add_neg_cancel, zpow_zero, ofGroup_one]

theorem ofGroup_neg_mul_zpow (t : Γ) (k : ℤ) :
    ofGroup (t ^ (-k)) * ofGroup (t ^ k) = (1 : RatU Γ) := by
  rw [← ofGroup_mul, ← zpow_add, neg_add_cancel, zpow_zero, ofGroup_one]

theorem ofGroup_conj_zpow (t : Γ) (k : ℤ) (u : Γ) :
    ofGroup (t ^ k) * ofGroup u * ofGroup (t ^ (-k)) = ofGroup (t ^ k * u * t ^ (-k)) := by
  rw [← ofGroup_mul, ← ofGroup_mul]

/-! ## The conjugation ring homomorphism of `Rat(Γ)` -/

/-- The ring homomorphism `x ↦ c * x * c'` of `Rat(Γ)` (conjugation by the unit `c`). -/
noncomputable def conjRingHom (c c' : RatU Γ) (h : c * c' = 1) (h' : c' * c = 1) :
    RatU Γ →+* RatU Γ where
  toFun x := c * x * c'
  map_one' := by rw [mul_one, h]
  map_zero' := by rw [mul_zero, zero_mul]
  map_add' x y := by rw [mul_add, add_mul]
  map_mul' x y := conj_mul_identity c c' h' x y

theorem conjRingHom_apply (c c' : RatU Γ) (h : c * c' = 1) (h' : c' * c = 1) (x : RatU Γ) :
    conjRingHom c c' h h' x = c * x * c' := rfl

/-- Conjugation by the image of `t ^ k` in `Rat(Γ)`. -/
noncomputable def zpowConjHom (t : Γ) (k : ℤ) : RatU Γ →+* RatU Γ :=
  conjRingHom (ofGroup (t ^ k)) (ofGroup (t ^ (-k))) (ofGroup_zpow_mul_neg t k)
    (ofGroup_neg_mul_zpow t k)

@[simp] theorem zpowConjHom_apply (t : Γ) (k : ℤ) (x : RatU Γ) :
    zpowConjHom t k x = ofGroup (t ^ k) * x * ofGroup (t ^ (-k)) := rfl

theorem zpowConjHom_ofGroup (t : Γ) (k : ℤ) (u : Γ) :
    zpowConjHom t k (ofGroup u) = ofGroup (t ^ k * u * t ^ (-k)) := by
  rw [zpowConjHom_apply, ofGroup_conj_zpow]

/-- The conjugation `x ↦ ofGroup (t^k) * x * ofGroup (t^-k)` commutes with the rational
operation (`Work.ORHughesFree.RatU.ofGroup_ratOp_conj`). -/
theorem zpowConjHom_ratOp (t : Γ) (k : ℤ) (x : RatU Γ) :
    zpowConjHom t k (RatU.ratOp x) = RatU.ratOp (zpowConjHom t k x) := by
  rw [zpowConjHom_apply, zpowConjHom_apply, ofGroup_ratOp_conj]

/-! ## The canonical map `Rat(V) → Rat(U)` against the `ratOp` and the actions -/

theorem ofSubgroup_ratOp' (N : Subgroup Γ) (x : RatU ↥N) :
    RatU.ofSubgroup N (RatU.ratOp x) = RatU.ratOp (RatU.ofSubgroup N x) :=
  (RatU.ofSubgroup_isHom N).map_rat x

theorem ofSubgroup_smul' (N : Subgroup Γ) (v : ↥N) (x : RatU ↥N) :
    RatU.ofSubgroup N (RatU.smul v x) = RatU.ofGroup ((v : ↥N) : Γ) * RatU.ofSubgroup N x := by
  rw [← RatU.smul_eq_ofGroup_mul]
  exact (RatU.ofSubgroup_isHom N).map_smul v x

theorem ofSubgroup_smulRight' (N : Subgroup Γ) (x : RatU ↥N) (v : ↥N) :
    RatU.ofSubgroup N (RatU.smulRight x v) = RatU.ofSubgroup N x * RatU.ofGroup ((v : ↥N) : Γ) := by
  rw [← RatU.smulRight_eq_mul_ofGroup]
  exact (RatU.ofSubgroup_isHom N).map_smulRight x v

/-! ## The two morphisms of rational `N`-semirings

The `N`-action on `Rat(Γ)` for which both maps below are morphisms of rational `N`-semirings is the
action twisted by the conjugation `n ↦ t^k * n * t^-k`, i.e. the restriction of scalars of the
structure `Rat.comap (conjMulEquiv t k)` on `Rat(Γ)`:

  `v · x = ofGroup (t^k * v * t^-k) * x`. -/

theorem isRationalHom_zpowConjHom_comp_ofSubgroup (N : Subgroup Γ) (t : Γ)
    (htN : ∀ (k : ℤ) (n : Γ), n ∈ N → t ^ k * n * t ^ (-k) ∈ N) (k : ℤ) :
    IsRationalUSemiringHom (RatU.rational (U := ↥N))
      (RationalUSemiring.restrict N (Work.ORHughesFree.Rat.comap (conjMulEquiv t k)))
      ((zpowConjHom t k).comp (RatU.ofSubgroup N)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    show zpowConjHom t k (RatU.ofSubgroup N (RatU.ratOp x)) =
      RatU.ratOp (zpowConjHom t k (RatU.ofSubgroup N x))
    rw [ofSubgroup_ratOp', zpowConjHom_ratOp]
  · intro v x
    show zpowConjHom t k (RatU.ofSubgroup N (RatU.smul v x)) =
      RatU.smul (conjMulEquiv t k (v : Γ))
        (zpowConjHom t k (RatU.ofSubgroup N x))
    rw [ofSubgroup_smul', map_mul, zpowConjHom_ofGroup, RatU.smul_eq_ofGroup_mul,
      conjMulEquiv_apply]
  · intro x v
    show zpowConjHom t k (RatU.ofSubgroup N (RatU.smulRight x v)) =
      RatU.smulRight (zpowConjHom t k (RatU.ofSubgroup N x)) (conjMulEquiv t k (v : Γ))
    rw [ofSubgroup_smulRight', map_mul, zpowConjHom_ofGroup, RatU.smulRight_eq_mul_ofGroup,
      conjMulEquiv_apply]

theorem isRationalHom_ofSubgroup_comp_transport (N : Subgroup Γ) (t : Γ)
    (htN : ∀ (k : ℤ) (n : Γ), n ∈ N → t ^ k * n * t ^ (-k) ∈ N) (k : ℤ) :
    IsRationalUSemiringHom (RatU.rational (U := ↥N))
      (RationalUSemiring.restrict N (Work.ORHughesFree.Rat.comap (conjMulEquiv t k)))
      ((RatU.ofSubgroup N).comp (Work.ORHughesFree.Rat.transport (conjSubMulEquiv N t htN k))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    show RatU.ofSubgroup N
        (Work.ORHughesFree.Rat.transport (conjSubMulEquiv N t htN k) (RatU.ratOp x)) =
      RatU.ratOp (RatU.ofSubgroup N
        (Work.ORHughesFree.Rat.transport (conjSubMulEquiv N t htN k) x))
    rw [Work.ORHughesFree.Rat.transport_rat, ofSubgroup_ratOp']
  · intro v x
    show RatU.ofSubgroup N
        (Work.ORHughesFree.Rat.transport (conjSubMulEquiv N t htN k) (RatU.smul v x)) =
      RatU.smul (conjMulEquiv t k (v : Γ))
        (RatU.ofSubgroup N (Work.ORHughesFree.Rat.transport (conjSubMulEquiv N t htN k) x))
    rw [Work.ORHughesFree.Rat.transport_smul, RatU.smul_eq_ofGroup_mul, RatU.smul_eq_ofGroup_mul,
      map_mul, Work.ORHughesFree.Rat.ofSubgroup_ofGroup, conjSubMulEquiv_coe_eq, conjMulEquiv_apply]
  · intro x v
    show RatU.ofSubgroup N
        (Work.ORHughesFree.Rat.transport (conjSubMulEquiv N t htN k) (RatU.smulRight x v)) =
      RatU.smulRight (RatU.ofSubgroup N
        (Work.ORHughesFree.Rat.transport (conjSubMulEquiv N t htN k) x)) (conjMulEquiv t k (v : Γ))
    rw [Work.ORHughesFree.Rat.transport_smulRight, RatU.smulRight_eq_mul_ofGroup,
      RatU.smulRight_eq_mul_ofGroup, map_mul, Work.ORHughesFree.Rat.ofSubgroup_ofGroup,
      conjSubMulEquiv_coe_eq, conjMulEquiv_apply]

/-- The image of `Rat(N)` in `Rat(Γ)` is stable under conjugation by `ofGroup (t ^ k)`: the
conjugate of `ofSubgroup N β` is the image of the conjugate of `β` under the group automorphism
`n ↦ t ^ k * n * t ^ (-k)` of `N`. -/
theorem zpowConjHom_ofSubgroup (N : Subgroup Γ) (t : Γ)
    (htN : ∀ (k : ℤ) (n : Γ), n ∈ N → t ^ k * n * t ^ (-k) ∈ N) (k : ℤ) (β : RatU ↥N) :
    zpowConjHom t k (RatU.ofSubgroup N β) =
      RatU.ofSubgroup N (Work.ORHughesFree.Rat.transport (conjSubMulEquiv N t htN k) β) := by
  have h1 := RatU.lift_unique (RatU Γ)
    (RationalUSemiring.restrict N (Work.ORHughesFree.Rat.comap (conjMulEquiv t k)))
    ((zpowConjHom t k).comp (RatU.ofSubgroup N)) (isRationalHom_zpowConjHom_comp_ofSubgroup N t htN k)
  have h2 := RatU.lift_unique (RatU Γ)
    (RationalUSemiring.restrict N (Work.ORHughesFree.Rat.comap (conjMulEquiv t k)))
    ((RatU.ofSubgroup N).comp (Work.ORHughesFree.Rat.transport (conjSubMulEquiv N t htN k)))
    (isRationalHom_ofSubgroup_comp_transport N t htN k)
  exact DFunLike.congr_fun (h1.trans h2.symm) β

theorem exists_conj_ofSubgroup {Γ : Type} [Group Γ] (N : Subgroup Γ) (t : Γ)
    (htN : ∀ (k : ℤ) (n : Γ), n ∈ N → t ^ k * n * t ^ (-k) ∈ N) (k : ℤ)
    (β : Work.ORHughesFree.RatU ↥N) :
    ∃ β' : Work.ORHughesFree.RatU ↥N,
      Work.ORHughesFree.RatU.ofGroup (t ^ k) * Work.ORHughesFree.RatU.ofSubgroup N β =
        Work.ORHughesFree.RatU.ofSubgroup N β' * Work.ORHughesFree.RatU.ofGroup (t ^ k) := by
  refine ⟨Work.ORHughesFree.Rat.transport (conjSubMulEquiv N t htN k) β, ?_⟩
  have hmain := zpowConjHom_ofSubgroup N t htN k β
  have hcc' : ofGroup (t ^ (-k)) * ofGroup (t ^ k) = (1 : RatU Γ) := ofGroup_neg_mul_zpow t k
  have hstep : zpowConjHom t k (RatU.ofSubgroup N β) * ofGroup (t ^ k)
      = ofGroup (t ^ k) * RatU.ofSubgroup N β := by
    rw [zpowConjHom_apply, mul_assoc, hcc', mul_one]
  rw [← hstep, hmain]

end Work.ORHughesFree.RatU
