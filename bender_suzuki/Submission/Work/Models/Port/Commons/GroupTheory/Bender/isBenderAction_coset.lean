import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.involution_mem_conj
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.inv_mul_mem_of_conj_mem_of_orderTwo
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.mem_map_conj_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Bender

/-- **The coset action of a group with a strongly embedded subgroup.**

Let `G` be a finite group and `M < G` a proper subgroup of even order such that
`M ∩ Mᵍ` has odd order for every `g ∉ M` ("`M` is strongly embedded in `G`").
Then the natural action of `G` on the coset space `G ⧸ M` has the following properties:

* it is transitive;
* the coset space is non-trivial, `1 < |G ⧸ M|`;
* `|G|` is even;
* every involution `t` of `G` fixes exactly one coset.

The last statement is the "Bender action" property: the fixed-point set of an involution
has size one.  Concretely, `t` fixes `xM` iff `x⁻¹ t x ∈ M`, and

* existence: `involution_mem_conj` produces some `x` with `x⁻¹ t x ∈ M`;
* uniqueness: if `x⁻¹ t x ∈ M` and `y⁻¹ t y ∈ M`, then `a := x⁻¹ t x` is an involution
  lying in `M` and in the conjugate `M^(x⁻¹y)`, so `x⁻¹ y ∈ M` by the hypothesis
  (`inv_mul_mem_of_conj_mem_of_orderTwo`); hence `x M = y M`. -/
theorem isBenderAction_coset {G : Type*} [Group G] [Finite G] (M : Subgroup G) (hM : M ≠ ⊤)
    (hEven : Even (Nat.card M))
    (hOdd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G)))) :
    MulAction.IsPretransitive G (G ⧸ M) ∧ 1 < Nat.card (G ⧸ M) ∧ Even (Nat.card G) ∧
      ∀ t : G, orderOf t = 2 → ∃! x : G ⧸ M, t • x = x := by
  classical
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · -- the coset space `G ⧸ M` has at least two elements since `M ≠ ⊤`
    rw [← Subgroup.index_eq_card]
    exact Subgroup.one_lt_index_of_ne_top hM
  · -- `|M|` divides `|G|`, and `|M|` is even
    rw [← M.card_mul_index]
    exact hEven.mul_right M.index
  · intro t ht
    -- an involution is its own inverse
    have ht2 : t * t = 1 := by
      have h : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
      simpa [pow_two] using h
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    -- the fixed points of `t` on `G ⧸ M`
    have key : ∀ a : G,
        t • (QuotientGroup.mk a : G ⧸ M) = QuotientGroup.mk a ↔ a⁻¹ * t * a ∈ M := by
      intro a
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
      constructor
      · intro h; rwa [mul_inv_rev, htinv] at h
      · intro h; rwa [mul_inv_rev, htinv]
    -- existence: some conjugate of `M` contains `t`
    obtain ⟨x, hx⟩ := Commons.GroupTheory.StronglyEmbedded.involution_mem_conj M hEven hOdd ht
    have hxM : x⁻¹ * t * x ∈ M :=
      (Commons.GroupTheory.StronglyEmbedded.mem_map_conj_iff (A := M) (z := x) (u := t)).mp hx
    refine ⟨QuotientGroup.mk x, (key x).mpr hxM, ?_⟩
    intro y hy
    have hyout : t • (QuotientGroup.mk y.out : G ⧸ M) = QuotientGroup.mk y.out := by
      rw [QuotientGroup.out_eq' y]
      exact hy
    have hyM : y.out⁻¹ * t * y.out ∈ M := (key y.out).mp hyout
    have hmem : x⁻¹ * y.out ∈ M :=
      Commons.GroupTheory.StronglyEmbedded.inv_mul_mem_of_conj_mem_of_orderTwo M hOdd ht hxM hyM
    exact ((QuotientGroup.eq.mpr hmem).trans (QuotientGroup.out_eq' y)).symm

end Commons.GroupTheory.Bender
