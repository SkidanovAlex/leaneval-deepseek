import Mathlib
import Submission.Work.Frobenius.Pair

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The induced class function on nontrivial elements of a Frobenius complement

Let `H ≤ G` be a Frobenius complement and `f : H → ℂ` a class function on `H`.
For `h ∈ H`, `h ≠ 1`, the induced function `indFun H f` takes at `h` the value `f h`:
the conjugates `x * h * x⁻¹` of `h` lying in `H` are exactly the `H`-conjugates of `h`,
and there are `|H|` of them; each contributes `f h` by the class-function property, and
the normalising factor `|H|⁻¹` cancels the `|H|`-fold sum.

The key structural input is `mul_conj_mem_iff_of_isFrobeniusComplement`: if `h ∈ H` is
nontrivial then `x * h * x⁻¹ ∈ H` forces `x ∈ H` (otherwise `h` would lie in
`H ⊓ H^{x⁻¹} = ⊥`, by the Frobenius `TI` condition).
-/

open Classical

open scoped Pointwise

namespace Work.Frobenius.Induction

variable {G : Type*}

/-- In a Frobenius complement `H`, a `G`-conjugate `x * h * x⁻¹` of a nontrivial
`h ∈ H` lies in `H` if and only if the conjugating element `x` lies in `H`. -/
theorem mul_conj_mem_iff_of_isFrobeniusComplement [Group G] {H : Subgroup G}
    (hH : IsFrobeniusComplement H) {h : G} (hh : h ∈ H) (hh1 : h ≠ 1) (x : G) :
    x * h * x⁻¹ ∈ H ↔ x ∈ H := by
  refine ⟨fun hconj => ?_, fun hx => H.mul_mem (H.mul_mem hx hh) (H.inv_mem hx)⟩
  by_contra hx
  have hxinv : x⁻¹ ∉ H := fun hc => hx (by simpa using H.inv_mem hc)
  have hmem : h ∈ (H ⊓ (MulAut.conj x⁻¹ • H) : Subgroup G) := by
    refine ⟨hh, ?_⟩
    show h ∈ (MulAut.conj x⁻¹ • H : Set G)
    rw [mem_conj_smul_iff']
    simpa using hconj
  have h2 := hmem
  rw [hH.ti x⁻¹ hxinv] at h2
  exact hh1 (by simpa using h2)

/-- The sum of the constant `c` over the elements of a subgroup `H` of a finite group,
written as a sum over the ambient group with an indicator. -/
theorem sum_ite_mem_eq_card_mul [Group G] [Fintype G] (H : Subgroup G) (c : ℂ) :
    (∑ x : G, if x ∈ H then c else 0) = (Nat.card H : ℂ) * c := by
  have h1 : (∑ x : G, if x ∈ H then c else 0) = (Fintype.card H : ℂ) * c := by
    rw [← Finset.sum_filter (fun x : G => x ∈ H) (fun _ => c)]
    rw [Finset.sum_subtype (F := inferInstance) (p := fun x : G => x ∈ H)
      (Finset.univ.filter (fun x : G => x ∈ H)) (by simp) (fun _ : G => c)]
    rw [Finset.sum_const]
    simp only [Finset.card_univ, nsmul_eq_mul]
  have h2 : (Nat.card H : ℂ) = (Fintype.card H : ℂ) := by rw [Nat.card_eq_fintype_card]
  rw [h1, ← h2]

theorem indFun_apply_of_mem_complement {G : Type*} [Group G] [Fintype G] {H : Subgroup G} (hH : IsFrobeniusComplement H) {f : H → ℂ} (hf : IsClassFun f) {h : G} (hh : h ∈ H) (hh1 : h ≠ 1) : indFun H f h = f ⟨h, hh⟩ := by
  classical
  have hterm : ∀ x : G, (if hx : x * h * x⁻¹ ∈ H then f ⟨x * h * x⁻¹, hx⟩ else 0) =
      if x ∈ H then f ⟨h, hh⟩ else 0 := by
    intro x
    by_cases hxH : x ∈ H
    · have hconj : x * h * x⁻¹ ∈ H :=
        (mul_conj_mem_iff_of_isFrobeniusComplement hH hh hh1 x).mpr hxH
      rw [dite_eq_left hconj, ite_eq_left hxH]
      have h1 : (⟨x * h * x⁻¹, hconj⟩ : H) = ⟨x, hxH⟩ * ⟨h, hh⟩ * ⟨x, hxH⟩⁻¹ := by
        ext
        simp
      rw [h1]
      exact hf ⟨h, hh⟩ ⟨x, hxH⟩
    · have hconj : x * h * x⁻¹ ∉ H :=
        fun hc => hxH ((mul_conj_mem_iff_of_isFrobeniusComplement hH hh hh1 x).mp hc)
      rw [dite_eq_right hconj, ite_eq_right hxH]
  have hcongr : (∑ x : G, if hx : x * h * x⁻¹ ∈ H then f ⟨x * h * x⁻¹, hx⟩ else 0) =
      (∑ x : G, if x ∈ H then (f ⟨h, hh⟩ : ℂ) else 0) :=
    Finset.sum_congr rfl fun x _ => hterm x
  have hne : (Nat.card H : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    simp
  rw [indFun, hcongr, sum_ite_mem_eq_card_mul]
  exact inv_mul_cancel_left₀ hne _

end Work.Frobenius.Induction
