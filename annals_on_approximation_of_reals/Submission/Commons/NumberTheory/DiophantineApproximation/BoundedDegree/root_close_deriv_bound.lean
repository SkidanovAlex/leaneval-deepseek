import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

/-- Pull a scalar factor out of a multiset sum. -/
private lemma mul_multiset_sum_distrib {α ι : Type*} [NonUnitalNonAssocSemiring α]
    (a : α) (f : ι → α) (s : Multiset ι) :
    (s.map (fun i : ι => a * f i)).sum = a * (s.map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [ih]
      rw [mul_add]

/-- If `α` is a point of the multiset of roots with minimal distance from `ξ`,
then replacing the factor `ξ - β` (for any root `β`) by `ξ - α` can only
decrease the norm of the product of all factors. -/
private lemma norm_erase_factor_le {r : Multiset ℂ} {ξ α : ℂ}
    (hαmin : ∀ γ ∈ r, ‖ξ - α‖ ≤ ‖ξ - γ‖) {β : ℂ} (hβ : β ∈ r) :
    ‖(ξ - α) * ((r.erase β).map (fun γ : ℂ => ξ - γ)).prod‖ ≤
      ‖(r.map (fun γ : ℂ => ξ - γ)).prod‖ := by
  calc
    ‖(ξ - α) * ((r.erase β).map (fun γ : ℂ => ξ - γ)).prod‖
        = ‖ξ - α‖ * ‖((r.erase β).map (fun γ : ℂ => ξ - γ)).prod‖ := by rw [norm_mul]
    _ ≤ ‖ξ - β‖ * ‖((r.erase β).map (fun γ : ℂ => ξ - γ)).prod‖ := by
        exact mul_le_mul_of_nonneg_right (hαmin β hβ) (norm_nonneg _)
    _ = ‖(ξ - β) * ((r.erase β).map (fun γ : ℂ => ξ - γ)).prod‖ := by rw [norm_mul]
    _ = ‖(r.map (fun γ : ℂ => ξ - γ)).prod‖ := by
        have hmap : ((β ::ₘ r.erase β).map (fun γ : ℂ => ξ - γ)).prod =
            (ξ - β) * ((r.erase β).map (fun γ : ℂ => ξ - γ)).prod := by
          rw [Multiset.map_cons, Multiset.prod_cons]
        have herase : (β ::ₘ r.erase β) = r := Multiset.cons_erase hβ
        rw [← hmap, herase]

/-- Core estimate in terms of the (multi)set of roots: if `α` is a point of
minimal distance from `ξ` among the roots of `S`, then
`‖ξ - α‖ * ‖S′(ξ)‖ ≤ (number of roots counted with multiplicity) * ‖S(ξ)‖`. -/
private lemma root_bound_of_closest {S : Polynomial ℂ} (ξ : ℂ) {α : ℂ}
    (hαmin : ∀ β ∈ S.roots, ‖ξ - α‖ ≤ ‖ξ - β‖) :
    ‖ξ - α‖ * ‖(S.derivative).eval ξ‖ ≤ (S.roots.card : ℝ) * ‖S.eval ξ‖ := by
  have hsplit : S.Splits := IsAlgClosed.splits S
  have hderiv : S.derivative.eval ξ =
      S.leadingCoeff * (S.roots.map (fun β : ℂ =>
        ((S.roots.erase β).map (fun γ : ℂ => ξ - γ)).prod)).sum := by
    simpa using (hsplit.eval_derivative ξ)
  have heval : S.eval ξ =
      S.leadingCoeff * (S.roots.map (fun γ : ℂ => ξ - γ)).prod := by
    simpa using (hsplit.eval_eq_prod_roots ξ)
  have hpoint : ∀ β ∈ S.roots,
      ‖ξ - α‖ * ‖((S.roots.erase β).map (fun γ : ℂ => ξ - γ)).prod‖ ≤
        ‖(S.roots.map (fun γ : ℂ => ξ - γ)).prod‖ := by
    intro β hβ
    calc
      ‖ξ - α‖ * ‖((S.roots.erase β).map (fun γ : ℂ => ξ - γ)).prod‖
          = ‖(ξ - α) * ((S.roots.erase β).map (fun γ : ℂ => ξ - γ)).prod‖ := by
            rw [norm_mul]
      _ ≤ ‖(S.roots.map (fun γ : ℂ => ξ - γ)).prod‖ := norm_erase_factor_le hαmin hβ
  have hsum : (S.roots.map (fun β : ℂ =>
          ‖ξ - α‖ * ‖((S.roots.erase β).map (fun γ : ℂ => ξ - γ)).prod‖)).sum ≤
        (S.roots.card : ℝ) * ‖(S.roots.map (fun γ : ℂ => ξ - γ)).prod‖ := by
    calc
      (S.roots.map (fun β : ℂ =>
          ‖ξ - α‖ * ‖((S.roots.erase β).map (fun γ : ℂ => ξ - γ)).prod‖)).sum
          ≤ (S.roots.map (fun _ : ℂ => ‖(S.roots.map (fun γ : ℂ => ξ - γ)).prod‖)).sum := by
              exact Multiset.sum_map_le_sum_map
                (fun β : ℂ => ‖ξ - α‖ * ‖((S.roots.erase β).map (fun γ : ℂ => ξ - γ)).prod‖)
                (fun _ : ℂ => ‖(S.roots.map (fun γ : ℂ => ξ - γ)).prod‖) hpoint
      _ = (S.roots.card : ℝ) * ‖(S.roots.map (fun γ : ℂ => ξ - γ)).prod‖ := by
          simp
  calc
    ‖ξ - α‖ * ‖(S.derivative).eval ξ‖
        = ‖ξ - α‖ * ‖S.leadingCoeff *
            (S.roots.map (fun β : ℂ =>
              ((S.roots.erase β).map (fun γ : ℂ => ξ - γ)).prod)).sum‖ := by
            rw [hderiv]
    _ = ‖ξ - α‖ * (‖S.leadingCoeff‖ *
          ‖(S.roots.map (fun β : ℂ =>
            ((S.roots.erase β).map (fun γ : ℂ => ξ - γ)).prod)).sum‖) := by
            rw [norm_mul]
    _ ≤ ‖ξ - α‖ * (‖S.leadingCoeff‖ *
          (S.roots.map (fun β : ℂ =>
            ‖((S.roots.erase β).map (fun γ : ℂ => ξ - γ)).prod‖)).sum) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (by
                  simpa [Multiset.map_map] using
                    (norm_multiset_sum_le (S.roots.map (fun β : ℂ =>
                      ((S.roots.erase β).map (fun γ : ℂ => ξ - γ)).prod))))
                (norm_nonneg S.leadingCoeff))
              (norm_nonneg (ξ - α))
    _ = ‖S.leadingCoeff‖ * (S.roots.map (fun β : ℂ =>
          ‖ξ - α‖ * ‖((S.roots.erase β).map (fun γ : ℂ => ξ - γ)).prod‖)).sum := by
          rw [mul_multiset_sum_distrib]
          ring
    _ ≤ ‖S.leadingCoeff‖ * ((S.roots.card : ℝ) *
          ‖(S.roots.map (fun γ : ℂ => ξ - γ)).prod‖) := by
          exact mul_le_mul_of_nonneg_left hsum (norm_nonneg S.leadingCoeff)
    _ = (S.roots.card : ℝ) * (‖S.leadingCoeff‖ *
          ‖(S.roots.map (fun γ : ℂ => ξ - γ)).prod‖) := by ring
    _ = (S.roots.card : ℝ) * ‖S.leadingCoeff * (S.roots.map (fun γ : ℂ => ξ - γ)).prod‖ := by
          rw [norm_mul]
    _ = (S.roots.card : ℝ) * ‖S.eval ξ‖ := by rw [heval]

/-- Root-transfer lemma (classical argument of Prop 5.1 / Bugeaud §2): for a
non-constant complex polynomial `S` and a complex number `ξ`, some root `α` of `S`
satisfies `|ξ − α| · |S′(ξ)| ≤ deg(S) · |S(ξ)|`. -/
theorem root_close_deriv_bound {S : Polynomial ℂ} (hS : 1 ≤ S.natDegree) (ξ : ℂ) :
    ∃ α : ℂ, S.IsRoot α ∧
      ‖ξ - α‖ * ‖(S.derivative).eval ξ‖ ≤ (S.natDegree : ℝ) * ‖S.eval ξ‖ := by
  have hsplit : S.Splits := IsAlgClosed.splits S
  have hroots : S.roots ≠ 0 := by
    intro hzero
    have hc : S.roots.card = 0 := by simp [hzero]
    have hnat : S.natDegree = S.roots.card := hsplit.natDegree_eq_card_roots (f := S)
    omega
  obtain ⟨α, hα, hαmin⟩ := Multiset.exists_min_image (fun β : ℂ => ‖ξ - β‖) hroots
  refine ⟨α, Polynomial.isRoot_of_mem_roots hα, ?_⟩
  have hb : ‖ξ - α‖ * ‖(S.derivative).eval ξ‖ ≤ (S.roots.card : ℝ) * ‖S.eval ξ‖ :=
    root_bound_of_closest ξ hαmin
  have hcard : (S.roots.card : ℝ) = (S.natDegree : ℝ) := by
    rw [hsplit.natDegree_eq_card_roots (f := S)]
  rwa [hcard] at hb

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree