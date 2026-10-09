import Mathlib
import Submission.Work.SSGRoute.prop5.mw.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The graded Hall spanning theorem in `ψ`-form

`VspanSize ψ n` is the `ℤ`-span of the values `ψ h` for `h` a **Hall** tree of size `n`.
The lemma `psi_mem_VspanSize` says that `ψ w` lies in that span for `n = Magma.size w`, i.e. the
Hall trees of a fixed size span the degree-`n` part of any Lie-ring-valued bracket evaluation.

This is the degree-graded refinement of `witt.hall_spanning`: the "collecting" algorithm behind
Hall's spanning theorem only ever produces trees with the same `Multiset` of leaves as the pair it
started from, so all Hall trees that occur have the same number of leaves.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5.mw

variable {X : Type*} [LinearOrder X] {M : Type*} [LieRing M]

/-- Every `Good` tree occurring in the expansion of `⁅ψ x, ψ y⁆` has `size x + size y` leaves,
because its foliage has the same multiset of letters as `foliage x ++ foliage y`. -/
lemma W_le_VspanSize (ψ : Magma X → M) (x y : Magma X) {m : M}
    (hm : m ∈ witt.W ψ x y) : m ∈ VspanSize ψ (Magma.size x + Magma.size y) := by
  rw [witt.W] at hm
  refine Submodule.span_le.mpr ?_ hm
  rintro m ⟨c, hc, rfl⟩
  obtain ⟨hcH, hcms, a, b, hab, hcfol⟩ := hc
  refine Submodule.subset_span ⟨⟨c, hcH, ?_⟩, rfl⟩
  have hcard := congrArg Multiset.card hcms
  simp only [Multiset.card_add, Multiset.coe_card] at hcard
  rw [← Magma.foliage_length c, ← Magma.foliage_length x, ← Magma.foliage_length y]
  exact hcard

/-- The bracket of two **Hall** elements lies in the graded Hall span of the pair's size. -/
lemma bracket_hall_mem_VspanSize (ψ : Magma X → M)
    (hψ : ∀ a b : Magma X, ψ (Magma.mul a b) = ⁅ψ a, ψ b⁆) (x y : Magma X)
    (hx : IsHall x) (hy : IsHall y) :
    ⁅ψ x, ψ y⁆ ∈ VspanSize ψ (Magma.size x + Magma.size y) := by
  rcases eq_or_ne x y with rfl | hne
  · rw [lie_self]; exact Submodule.zero_mem _
  · rcases lt_trichotomy (Magma.foliage x) (Magma.foliage y) with h | h | h
    · exact W_le_VspanSize ψ x y (witt.pair_mem ψ hψ x y hx hy h)
    · exact absurd (witt.hall_foliage_injective_aux hx hy h) hne
    · rw [(lie_skew (ψ x) (ψ y)).symm]
      refine Submodule.neg_mem _ ?_
      have hmem := W_le_VspanSize ψ y x (witt.pair_mem ψ hψ y x hy hx h)
      rwa [Nat.add_comm (Magma.size y) (Magma.size x)] at hmem

/-- The Lie bracket of two elements of graded Hall spans lands in the graded Hall span. -/
lemma bracket_mem_VspanSize (ψ : Magma X → M)
    (hψ : ∀ a b : Magma X, ψ (Magma.mul a b) = ⁅ψ a, ψ b⁆) {p q : M} {n k : ℕ}
    (hp : p ∈ VspanSize ψ n) (hq : q ∈ VspanSize ψ k) :
    ⁅p, q⁆ ∈ VspanSize ψ (n + k) := by
  have key : ∀ p ∈ VspanSize ψ n, ∀ q ∈ VspanSize ψ k, ⁅p, q⁆ ∈ VspanSize ψ (n + k) := by
    intro p hp
    refine Submodule.span_induction
      (p := fun x _ => ∀ q ∈ VspanSize ψ k, ⁅x, q⁆ ∈ VspanSize ψ (n + k)) ?_ ?_ ?_ ?_ hp
    · rintro m ⟨h, rfl⟩ q hq
      refine Submodule.span_induction
        (p := fun y _ => ⁅ψ h.1, y⁆ ∈ VspanSize ψ (n + k)) ?_ ?_ ?_ ?_ hq
      · rintro m' ⟨h', rfl⟩
        have := bracket_hall_mem_VspanSize ψ hψ h.1 h'.1 h.2.1 h'.2.1
        rwa [h.2.2, h'.2.2] at this
      · rw [lie_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
      · intro r a _ ha; rw [lie_zsmul]; exact Submodule.smul_mem _ r ha
    · intro q _; rw [zero_lie]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb q hq; rw [add_lie]; exact Submodule.add_mem _ (ha q hq) (hb q hq)
    · intro r a _ ha q hq; rw [zsmul_lie]; exact Submodule.smul_mem _ r (ha q hq)
  exact key p hp q hq

theorem psi_mem_VspanSize {X : Type} [LinearOrder X] {M : Type} [LieRing M]
    (ψ : Work.SSGRoute.prop5.Magma X → M)
    (hψ : ∀ a b : Work.SSGRoute.prop5.Magma X,
      ψ (Work.SSGRoute.prop5.Magma.mul a b) = ⁅ψ a, ψ b⁆)
    (w : Work.SSGRoute.prop5.Magma X) :
    ψ w ∈ Work.SSGRoute.prop5.mw.VspanSize ψ (Work.SSGRoute.prop5.Magma.size w) := by
  have key : ∀ n : ℕ, ∀ w : Magma X, Magma.size w = n → ψ w ∈ VspanSize ψ (Magma.size w) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hw
      cases w with
      | gen x =>
        exact Submodule.subset_span (Set.mem_range_self
          (f := fun h : {h : Magma X // IsHall h ∧ Magma.size h = Magma.size (Magma.gen x)} =>
            ψ h.1) ⟨Magma.gen x, isHall_gen x, rfl⟩)
      | mul a b =>
        rw [hψ a b, Magma.size_mul]
        refine bracket_mem_VspanSize ψ hψ ?_ ?_
        · exact ih (Magma.size a) (by rw [← hw]; exact Magma.size_left_lt a b) a rfl
        · exact ih (Magma.size b) (by rw [← hw]; exact Magma.size_right_lt a b) b rfl
  exact key (Magma.size w) w rfl

end Work.SSGRoute.prop5.mw
