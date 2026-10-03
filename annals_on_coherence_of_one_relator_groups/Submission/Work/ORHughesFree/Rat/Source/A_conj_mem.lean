import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.RatU.exists_conj_ofSubgroup

namespace Work.ORHughesFree.Rat.Source

open Work.ORHughesFree

/-- Conjugation by `ofGroup a` of the class of a term `t : RTerm U` is the class of the term
obtained by applying the inner automorphism `MulAut.conj a` of `U` to every group element occurring
in `t`.

This is the term-model form of the identity

  `x ∈ A V ↔ φa·x·φa⁻¹ ∈ A (V.map (MulAut.conj a))`

for `x ∈ A V` (`Rat.mem_A_iff`): it is proved by induction on `t`, the non-atomic clauses being
the multiplicativity of conjugation (`RatU.conj_mul_identity`), its additivity (distributivity in
`Rat(U)`), and its compatibility with the rational operation `⋄` (`RatU.ofGroup_ratOp_conj` at
`k = 1`). -/
theorem ofGroup_conj_mk {U : Type} [Group U] (a : U) (t : RTerm U) :
    RatU.ofGroup a * RatU.mk t * RatU.ofGroup a⁻¹
      = RatU.mk (RTerm.map (MulAut.conj a) t) := by
  have hac : RatU.ofGroup a⁻¹ * RatU.ofGroup a = (1 : RatU U) := by
    rw [← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one]
  have hca : RatU.ofGroup a * RatU.ofGroup a⁻¹ = (1 : RatU U) := by
    rw [← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one]
  have hconj : ∀ u : U, RatU.ofGroup a * RatU.ofGroup u * RatU.ofGroup a⁻¹
      = RatU.ofGroup (MulAut.conj a u) := by
    intro u; rw [← RatU.ofGroup_mul, ← RatU.ofGroup_mul]; rfl
  induction t with
  | z => rw [RTerm.map, RatU.mk_zero]; simp
  | o => rw [RTerm.map, RatU.mk_one]; simpa using hca
  | add s u ihs ihu =>
    rw [RTerm.map, RatU.mk_add, RatU.mk_add, mul_add, add_mul, ihs, ihu]
  | mul s u ihs ihu =>
    rw [RTerm.map, RatU.mk_mul, RatU.mk_mul,
      RatU.conj_mul_identity (RatU.ofGroup a) (RatU.ofGroup a⁻¹) hac (RatU.mk s) (RatU.mk u),
      ihs, ihu]
  | rat s ihs =>
    rw [RTerm.map, RatU.mk_rat, RatU.mk_rat]
    have h := RatU.ofGroup_ratOp_conj a 1 (RatU.mk s)
    simp only [zpow_one, zpow_neg_one] at h
    rw [h, ihs]
  | smulL u s ihs =>
    rw [RTerm.map, RatU.mk_smulL, RatU.mk_smulL, RatU.smul_eq_ofGroup_mul,
      RatU.smul_eq_ofGroup_mul, ← ihs, ← hconj u]
    exact RatU.conj_mul_identity _ _ hac _ _
  | smulR u s ihs =>
    rw [RTerm.map, RatU.mk_smulR, RatU.mk_smulR, RatU.smulRight_eq_mul_ofGroup,
      RatU.smulRight_eq_mul_ofGroup, ← ihs, ← hconj u]
    exact RatU.conj_mul_identity _ _ hac _ _

theorem A_conj_mem {U : Type} [Group U] {V : Subgroup U} {a : U} {x : Work.ORHughesFree.RatU U}
    (hx : x ∈ Work.ORHughesFree.Rat.A V) :
    Work.ORHughesFree.RatU.ofGroup a * x * Work.ORHughesFree.RatU.ofGroup a⁻¹ ∈
      Work.ORHughesFree.Rat.A (V.map (MulAut.conj a)) := by
  rw [Rat.mem_A_iff] at hx ⊢
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨RTerm.map (MulAut.conj a) t, ?_, ?_⟩
  · intro u' hu'
    obtain ⟨u, hu, rfl⟩ := Rat.supp_map_mem (MulAut.conj a) t hu'
    exact ⟨u, ht u hu, rfl⟩
  · exact (ofGroup_conj_mk a t).symm

end Work.ORHughesFree.Rat.Source
