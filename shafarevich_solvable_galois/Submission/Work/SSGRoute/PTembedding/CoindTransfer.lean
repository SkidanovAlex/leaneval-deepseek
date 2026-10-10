import Mathlib.GroupTheory.Index
import Submission.Work.SSGRoute.PT.ClassFormation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unit `M → Coind_S^Γ M` and the trace `Coind_S^Γ M → M`

For a subgroup `S ≤ Γ` and a `Γ`-module `M` (hence an `S`-module), the coinduced module
`Coind_S^Γ M = {f : Γ → M | ∀ x u, f (x * u) = u⁻¹ • f x}` carries the classical pair of
`Γ`-equivariant maps

* `coindIncl : M →+ Coind_S^Γ M`, `m ↦ (x ↦ x⁻¹ • m)`  (the "unit" of the induction adjunction);
* `coindTrace : Coind_S^Γ M →+ M`, `f ↦ ∑_{q ∈ Γ/S} t_q • f t_q`  (the "trace"/norm map, the
  `t_q` being any representatives of the left cosets `Γ/S`).

Their composite is multiplication by the index: `coindTrace (coindIncl m) = [Γ : S] • m`.

This is exactly the pair of maps that makes the composite
`H³(Γ,M) → H³(Γ, Coind_S^Γ M) ≅ H³(S,M)` (restriction followed by Shapiro) injective on the
`p`-torsion when `p ∤ [Γ : S]`.
-/

open scoped Classical

namespace Work.SSGRoute.PTembedding

noncomputable section

variable {Γ : Type} [Group Γ] (S : Subgroup Γ)
variable {M : Type} [AddCommGroup M] [DistribMulAction Γ M]

/-! ## The unit `M → Coind_S^Γ M` -/

/-- The function `x ↦ x⁻¹ • m` underlying the inclusion `M → Coind_S^Γ M`. -/
def coindInclFun (m : M) : Γ → M := fun x => x⁻¹ • m

theorem coindInclFun_mem (m : M) :
    coindInclFun m ∈ Work.SSGRoute.PT.coindSub Γ S M := by
  intro x u
  show (x * (u : Γ))⁻¹ • m = u⁻¹ • (x⁻¹ • m)
  rw [mul_inv_rev, Subgroup.smul_def, Subgroup.coe_inv, mul_smul]

/-- **The `Γ`-equivariant inclusion `M → Coind_S^Γ M`**, `m ↦ (x ↦ x⁻¹ • m)`. -/
def coindIncl : M →+ Work.SSGRoute.PT.Coind Γ S M where
  toFun m := ⟨coindInclFun m, coindInclFun_mem (S := S) m⟩
  map_zero' := Subtype.ext (funext fun x => by simp [coindInclFun])
  map_add' m m' := Subtype.ext (funext fun x => by simp [coindInclFun, smul_add])

@[simp] theorem coindIncl_apply (m : M) (x : Γ) :
    (coindIncl S m : Γ → M) x = x⁻¹ • m := rfl

/-- `coindIncl` is `Γ`-equivariant. -/
theorem coindIncl_equivariant :
    Work.GroupCohomology.IsEquivariant Γ (coindIncl (M := M) S) := by
  intro γ m
  ext x
  simp only [coindIncl_apply, Work.SSGRoute.PT.Coind.smul_apply, mul_inv_rev, inv_inv,
    mul_smul]

/-! ## The trace `Coind_S^Γ M → M` -/

/-- Each summand of the trace map is independent of the chosen representative: it is `y • f y`
for `y` any representative of the coset.  (Stated for the concrete representative `Quotient.out`
of the coset of `y`.) -/
theorem coindTraceFun_summand_mk (f : Work.SSGRoute.PT.Coind Γ S M) (y : Γ) :
    (Quotient.out (QuotientGroup.mk y : Γ ⧸ S)) • f (Quotient.out (QuotientGroup.mk y : Γ ⧸ S))
      = y • f y := by
  set o : Γ := Quotient.out (QuotientGroup.mk y : Γ ⧸ S) with ho
  have hs : o⁻¹ * y ∈ S := by
    rw [← QuotientGroup.eq]
    exact QuotientGroup.out_eq' _
  set s : ↥S := ⟨o⁻¹ * y, hs⟩ with hsd
  have hy : y = o * (s : Γ) := by
    rw [hsd]
    show y = o * (o⁻¹ * y)
    rw [mul_inv_cancel_left]
  rw [hy, Work.SSGRoute.PT.Coind.coe_mul, Subgroup.smul_def, Subgroup.coe_inv, mul_smul]
  simp

variable [Fintype (Γ ⧸ S)]

/-- The underlying function of the trace map: `f ↦ ∑_{q ∈ Γ/S} t_q • f t_q`, where `t_q` is any
representative of the left coset `q` (here `Quotient.out`). -/
def coindTraceFun (f : Work.SSGRoute.PT.Coind Γ S M) : M :=
  ∑ q : Γ ⧸ S, (Quotient.out q) • f (Quotient.out q)

/-- **The trace map `Coind_S^Γ M →+ M`**, `f ↦ ∑_{q ∈ Γ/S} t_q • f t_q`. -/
def coindTrace : Work.SSGRoute.PT.Coind Γ S M →+ M where
  toFun := coindTraceFun S
  map_zero' := by
    simp only [coindTraceFun]
    simp
  map_add' f g := by
    simp only [coindTraceFun]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show (f + g) (Quotient.out q) = f (Quotient.out q) + g (Quotient.out q) from rfl,
      smul_add]

theorem coindTrace_apply (f : Work.SSGRoute.PT.Coind Γ S M) :
    coindTrace S f = ∑ q : Γ ⧸ S, (Quotient.out q) • f (Quotient.out q) := rfl

/-- The computation of the trace on the unit: `coindTrace (coindIncl m) = [Γ : S] • m`. -/
theorem coindTrace_coindIncl (m : M) :
    coindTrace S (coindIncl S m) = S.index • m := by
  rw [coindTrace_apply]
  have h : ∀ q : Γ ⧸ S,
      (Quotient.out q) • (coindIncl S m : Γ → M) (Quotient.out q) = m := by
    intro q
    rw [coindIncl_apply, smul_inv_smul]
  calc (∑ q : Γ ⧸ S, (Quotient.out q) • (coindIncl S m : Γ → M) (Quotient.out q))
      = ∑ _q : Γ ⧸ S, m := Finset.sum_congr rfl (fun q _ => h q)
    _ = Finset.univ.card • m := Finset.sum_const m
    _ = S.index • m := by
        congr 1
        rw [Finset.card_univ, Subgroup.index_eq_card]
        exact (Nat.card_eq_fintype_card).symm

end

end Work.SSGRoute.PTembedding
