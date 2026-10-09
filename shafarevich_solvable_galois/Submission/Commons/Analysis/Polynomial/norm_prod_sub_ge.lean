import Mathlib.Analysis.Normed.Field.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Polynomial

/-- A multiset of nonnegative reals, each at least `η ≥ 0`, has product at least `η ^ card`. -/
lemma pow_card_le_prod {s : Multiset ℝ} {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ x ∈ s, η ≤ x) : η ^ s.card ≤ s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.card_cons, Multiset.prod_cons, pow_succ]
      have ha : η ≤ a := h a (Multiset.mem_cons_self a s)
      have hs : ∀ x ∈ s, η ≤ x := fun x hx => h x (Multiset.mem_cons_of_mem hx)
      have ihs := ih hs
      have hsprod_nonneg : 0 ≤ s.prod := Multiset.prod_nonneg (fun x hx => le_trans hη (hs x hx))
      calc η ^ s.card * η ≤ s.prod * η := mul_le_mul_of_nonneg_right ihs hη
        _ ≤ s.prod * a := mul_le_mul_of_nonneg_left ha hsprod_nonneg
        _ = a * s.prod := by rw [mul_comm]

lemma norm_prod_sub_ge {L : Type*} [NormedField L] (α : L) (η : ℝ) (hη : 0 ≤ η)
    (m : Multiset L) (hfar : ∀ β ∈ m, η ≤ ‖α - β‖) :
    η ^ m.card ≤ (Multiset.map (fun β : L => ‖α - β‖) m).prod := by
  rw [← Multiset.card_map]
  apply pow_card_le_prod hη
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨β, hβ, rfl⟩ := hx
  exact hfar β hβ

end Commons.Analysis.Polynomial