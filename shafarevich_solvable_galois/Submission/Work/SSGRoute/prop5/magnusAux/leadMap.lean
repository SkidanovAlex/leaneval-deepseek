/-
# The Magnus leading term as a map on the graded pieces

`lamLead X k hk : Λ (k-1) = γ_{k-1}/γ_k → (1 + filq X (k+1) k)` is the map induced by the Magnus
leading term `magLead (k+1)`.  The point of the construction is the compatibility

`lamLead (cls y) = magLead (k+1) y`   (`lamLead_cls`)

and its linear version on the span of the commutator monomials of the trees of size `k`

`lamLead (treeToLam μ) = mk (Σ μ c • monBrk c)`   (`lamLead_treeToLam`).
-/
import Mathlib
import Submission.Work.SSGRoute.prop5.magnusBase
import Submission.Work.SSGRoute.prop5.core.Defs
import Submission.Work.SSGRoute.prop5.core.relations_zero
import Submission.Work.SSGRoute.prop5.core.magLeadLemmas
import Submission.Work.SSGRoute.prop5.magLead_mem_nestedImage
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-- `Gam X q` is the lower central series term as defined in `core/Defs.lean`. -/
theorem mem_Gam_iff {q : ℕ} {z : FreeGroup X} :
    z ∈ core.Gam X q ↔ z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries q :=
  Iff.rfl

/-- `monGrp` agrees with the copy `core.monGrp`. -/
theorem monGrp_eq_core (c : Magma X) : monGrp X c = core.monGrp X c := by
  induction c with
  | gen x => rfl
  | mul a b iha ihb => rw [monGrp_mul, core.monGrp_mul, iha, ihb]

/-! ## The leading term as a map on `Λ (k-1)` -/

/-- The Magnus leading term, as a monoid homomorphism `γ_{k-1}/γ_k →* (1 + filq X (k+1) k)`. -/
noncomputable def lamLeadMul (X : Type) (k : ℕ) (hk : 1 ≤ k) :
    graded.GLam (G := FreeGroup X) (k - 1) →* Multiplicative (↥(filq X (k + 1) k)) :=
  QuotientGroup.lift ((core.Gam X (k - 1 + 1)).subgroupOf (core.Gam X (k - 1)))
    (MonoidHom.mk' (fun u : core.Gam X (k - 1) =>
      Multiplicative.ofAdd (⟨magLead (k + 1) (u : FreeGroup X),
        magLead_mem_filq (X := X) (k + 1) k hk (by omega) (mem_Gam_iff.mp u.2)⟩ :
          ↥(filq X (k + 1) k)))
      (by
        intro a b
        apply Multiplicative.ext
        apply Subtype.ext
        exact magLead_mul (X := X) (k + 1) k hk (by omega) (by omega)
          (mem_Gam_iff.mp a.2) (mem_Gam_iff.mp b.2)))
    (by
      intro u hu
      apply Multiplicative.ext
      apply Subtype.ext
      have hu1 : (u : FreeGroup X) ∈
          (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1 + 1) :=
        mem_Gam_iff.mp ((Subgroup.mem_subgroupOf).1 hu)
      have hu2 : (u : FreeGroup X) ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries k := by
        rwa [Nat.sub_add_cancel hk] at hu1
      exact magLead_eq_zero_of_mem_succ (X := X) k hu2)

/-- The Magnus leading term, as an additive map on the graded piece `Λ (k-1) = γ_{k-1}/γ_k`. -/
noncomputable def lamLead (X : Type) (k : ℕ) (hk : 1 ≤ k) :
    core.Lam X (k - 1) →+ ↥(filq X (k + 1) k) where
  toFun z := Multiplicative.toAdd (lamLeadMul X k hk (Additive.toMul z))
  map_zero' := by
    show Multiplicative.toAdd (lamLeadMul X k hk 1) = 0
    rw [map_one]
    rfl
  map_add' a b := by
    show Multiplicative.toAdd (lamLeadMul X k hk (Additive.toMul (a + b))) =
      Multiplicative.toAdd (lamLeadMul X k hk (Additive.toMul a)) +
        Multiplicative.toAdd (lamLeadMul X k hk (Additive.toMul b))
    rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl, map_mul]
    rfl

theorem lamLead_cls (X : Type) (k : ℕ) (hk : 1 ≤ k) (u : core.Gam X (k - 1)) :
    lamLead X k hk (core.cls X (k - 1) u) =
      ⟨magLead (k + 1) (u : FreeGroup X),
        magLead_mem_filq (X := X) (k + 1) k hk (by omega) (mem_Gam_iff.mp u.2)⟩ := rfl

/-- The bracketed monomial of a tree of size `k` is the Magnus leading term of the corresponding
commutator monomial. -/
theorem magLead_monGrp_eq (X : Type) (k : ℕ) (c : core.TreeIdx X k) :
    magLead (k + 1) (core.monGrp X c.1) = Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1) := by
  have h1 := core.magLead_monGrp_sub_mem (X := X) (k + 1) c.1 (by rw [c.2])
  rw [show Magma.size c.1 + 1 = k + 1 from by rw [c.2]] at h1
  rw [filq_self_eq_bot' (X := X) (k + 1), Submodule.mem_bot] at h1
  exact sub_eq_zero.mp h1

/-- **The compatibility of the leading-term map with the span of the tree monomials.** -/
theorem lamLead_treeToLam (X : Type) (k : ℕ) (hk : 1 ≤ k) (μ : core.TreeIdx X k →₀ ℤ) :
    Submodule.subtype (filq X (k + 1) k) (lamLead X k hk (core.treeToLam X k μ)) =
      Ideal.Quotient.mk (fil X (k + 1))
        (Finsupp.linearCombination ℤ (fun c : core.TreeIdx X k => monBrk X c.1) μ) := by
  induction μ using Finsupp.induction_linear with
  | zero => simp
  | add f g ihf ihg => simp only [map_add, ihf, ihg]
  | single c b =>
      have hc : Submodule.subtype (filq X (k + 1) k) (lamLead X k hk (core.treeClOf X k c)) =
          Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1) := by
        rw [core.treeClOf, lamLead_cls]
        change magLead (k + 1) (core.monGrp X c.1) =
          Ideal.Quotient.mk (fil X (k + 1)) (monBrk X c.1)
        rw [magLead_monGrp_eq X k c]
      rw [core.treeToLam, Finsupp.linearCombination_single, Finsupp.linearCombination_single,
        map_zsmul, map_zsmul, map_zsmul, hc]

end Work.SSGRoute.prop5
