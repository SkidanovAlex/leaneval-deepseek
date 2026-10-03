import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.OROneRel.exists_letter_once_data

/-!
# A letter occurring exactly once makes the Fox vector a unit

If the reduced word of `u : F(α)` contains the letter `(x, b)` exactly once and the letter
`(x, !b)` not at all, then `x` occurs exactly once in `u`, and the Fox derivative `∂u/∂x` is (up to
sign) a single monomial of `K[F(α)]`: writing `u.toWord = L₁ ++ [(x, b)] ++ L₂` with `x` absent from
`L₁` and `L₂`, the recursion `D(c :: L) = D(c) + c · D(L)` gives

`∂u/∂x = (mk L₁) · δ`,  `δ = 1` for `b = true` and `δ = -(of x)⁻¹` for `b = false`.

Pushing this along the presentation `F(α) →* ⟨α | r⟩` turns the component `rootVec K r u x` of the
root Fox vector into (up to sign) a group element of `K[G]`, hence a **unit**.  This is the
"terminal / free-product bottom" of the Magnus hierarchy, and the input consumed by the reduction
`Work.ORLyndon.lyndonIndependence_of_rootVec_isUnit`.

The combinatorial heart is `foxWord_eq_pm_of_count` below: an induction on the word, in which the
distinguished occurrence contributes `foxLetter x (x, b)` and every other letter `c` contributes
`letterGroup c` on the left, its own `foxLetter x c` vanishing because `c` does not involve `x`.
-/

namespace Work.ORLyndon

open MonoidAlgebra

/-- **The Fox derivative of a word in which `x` occurs exactly once.**  If the list `L` contains the
letter `(x, b)` once and `(x, !b)` not at all, then `∂L/∂x = ± of g` for some group element `g`.

(Here `∂L/∂x` is `foxWord x L`, the Fox derivative of the word; the case where `x` is absent from
`L` is the trivial special case `g = 1`, `+`.) -/
theorem foxWord_eq_pm_of_count {α : Type*} [DecidableEq α] {K : Type*} [Ring K]
    (x : α) (b : Bool) :
    ∀ L : List (α × Bool), L.count (x, b) = 1 → L.count (x, !b) = 0 →
      ∃ g : FreeGroup α, foxWord (K := K) x L = (MonoidAlgebra.of K (FreeGroup α)) g ∨
        foxWord (K := K) x L = -((MonoidAlgebra.of K (FreeGroup α)) g) := by
  intro L
  induction L with
  | nil => intro h1 _; simp at h1
  | cons c t ih =>
    intro h1 h2
    by_cases hc : c = (x, b)
    · -- the head is the distinguished occurrence: the tail carries no letter involving `x`
      subst hc
      have ht1 : t.count (x, b) = 0 := by
        rw [List.count_cons_self] at h1; omega
      have hne : (x, b) ≠ (x, !b) := by cases b <;> simp
      have ht2 : t.count (x, !b) = 0 := by
        rw [List.count_cons_of_ne hne] at h2; exact h2
      have hnot : x ∉ letters t := by
        rw [mem_letters]
        rintro ⟨b', hb'⟩
        have hcases : b' = b ∨ b' = !b := by cases b <;> cases b' <;> simp
        rcases hcases with h | h
        · rw [h] at hb'; exact (List.count_eq_zero.mp ht1) hb'
        · rw [h] at hb'; exact (List.count_eq_zero.mp ht2) hb'
      rw [foxWord_cons, foxWord_eq_zero_of_notMem hnot, mul_zero, add_zero]
      cases b
      · exact ⟨(FreeGroup.of x)⁻¹, Or.inr (by rw [foxLetter_false, if_pos rfl])⟩
      · exact ⟨1, Or.inl (by rw [foxLetter_true, if_pos rfl, map_one])⟩
    · -- the head does not involve `x`: it multiplies the answer of the tail on the left
      have hcx : c.1 ≠ x := by
        intro h
        have hcb : c = (x, c.2) := Prod.ext h rfl
        have hcases : c.2 = b ∨ c.2 = !b := by cases b <;> cases c.2 <;> simp
        rcases hcases with hcc | hcc
        · exact hc (by rw [hcb, hcc])
        · have : c = (x, !b) := by rw [hcb, hcc]
          rw [this, List.count_cons_self] at h2; omega
      have h1' : t.count (x, b) = 1 := by rw [List.count_cons_of_ne hc] at h1; exact h1
      have hcne : c ≠ (x, !b) := fun h => hcx (by rw [h])
      have h2' : t.count (x, !b) = 0 := by rw [List.count_cons_of_ne hcne] at h2; exact h2
      obtain ⟨g, hg⟩ := ih h1' h2'
      have hletter : foxLetter (K := K) x c = 0 := foxLetter_eq_zero_of_ne hcx c.2
      rw [foxWord_cons, hletter, zero_add]
      rcases hg with hg | hg
      · refine ⟨letterGroup c * g, Or.inl ?_⟩
        rw [hg, ← map_mul]
      · refine ⟨letterGroup c * g, Or.inr ?_⟩
        rw [hg, mul_neg, ← map_mul]

/-- **A letter occurring exactly once makes the Fox vector a unit.**  If the reduced word of `u`
contains the letter `(x, b)` exactly once and `(x, !b)` not at all, then `rootVec K r u x`, the
`x`-component `(∂u/∂x)_x` of the root Fox vector pushed into `K[⟨α | r⟩]`, is a unit: it is (up to
sign) the image of a single group element, and group elements of a monoid algebra are units. -/
theorem isUnit_rootVec_of_letterOnce {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (r u : FreeGroup α) (x : α) (b : Bool)
    (hcount : (FreeGroup.toWord u).count (x, b) = 1 ∧ (FreeGroup.toWord u).count (x, !b) = 0) :
    IsUnit (Work.ORLyndon.rootVec K r u x) := by
  obtain ⟨hc1, hc0⟩ := hcount
  obtain ⟨g, hg⟩ := foxWord_eq_pm_of_count (K := K) x b (FreeGroup.toWord u) hc1 hc0
  have hfox : foxD (K := K) x u = foxWord (K := K) x (FreeGroup.toWord u) := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := u)]
    rw [foxD_mk]
  rw [rootVec_apply, hfox]
  have hunit : IsUnit ((MonoidAlgebra.of K (OneRelatorGroup r)) (presentRho r g)) := by
    rw [← presentAlg_of K r g]
    exact IsUnit.map (presentAlg K r)
      (isUnit_iff_exists.mpr ⟨MonoidAlgebra.of K (FreeGroup α) g⁻¹,
        by rw [← map_mul, mul_inv_cancel, map_one],
        by rw [← map_mul, inv_mul_cancel, map_one]⟩)
  rcases hg with hg | hg
  · rw [hg, presentAlg_of]
    exact hunit
  · rw [hg, map_neg, presentAlg_of]
    exact IsUnit.neg hunit

end Work.ORLyndon
