import Mathlib
import Submission.Work.Mostow.gapAEvenDefs
import Submission.Work.Mostow.poAction_ge1
import Submission.Work.Mostow.poAction_hypIso_zero
import Submission.Work.Mostow.hypIsometry_ge1
import Submission.Work.Mostow.elliptic_normal_form
import Submission.Work.Mostow.boundedTorsionAux

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-! ## The canonical rotation norm of an elliptic isometry -/

open Classical in
/-- The canonical (intrinsic) rotation norm of an elliptic isometry: the `rotN` of the normal part
of the normal form produced by `elliptic_normal_form` (junk `0` when `c` has no fixed point).
By `Work.Mostow.ftbRotEq` this is independent of the block normal form used. -/
noncomputable def rotCanon (hAall : ∀ k, Submission.Mostow.POActionProp k)
    (hIall : ∀ k, Submission.Mostow.HypIsometryProp k) {N : ℕ} (c : PO N 1) : ℝ :=
  if h : ∃ p : E N, c • p = p then
    rotN ((elliptic_normal_form N (hAall N) (hIall N) hAall hIall c h).choose_spec.choose_spec.choose_spec.choose_spec.choose)
  else 0

/-! ## Auxiliary facts -/

/-- `nearGrp Λ z η ≠ ⊥` supplies a nontrivial element of `Λ` that is `η`-near-identity at `z`. -/
lemma exists_nearId_of_nearGrp_ne_bot {n : ℕ} {Λ : Subgroup (PO n 1)} {z : E n} {η : ℝ}
    (h : nearGrp Λ z η ≠ ⊥) :
    ∃ g : PO n 1, g ∈ Λ ∧ g ≠ 1 ∧ NearIdAt g z η := by
  by_contra hc
  push_neg at hc
  have hsub : ({g : PO n 1 | g ∈ Λ ∧ NearIdAt g z η} : Set (PO n 1)) ⊆ {1} :=
    fun g hg => Set.mem_singleton_iff.mpr (by by_contra hg1; exact hc g hg.1 hg1 hg.2)
  have hbot : nearGrp Λ z η = ⊥ := by
    rw [nearGrp]
    refine le_antisymm ?_ bot_le
    intro x hx
    refine Subgroup.closure_induction (p := fun y _ => y = 1) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Set.mem_singleton_iff.mp (hsub hy)
    · rfl
    · intro a b _ _ ha hb
      rw [ha, hb, one_mul]
    · intro a _ ha
      rw [ha, inv_one]
  exact h hbot

/-- An element of a finite subgroup is of finite order. -/
lemma isOfFinOrder_of_mem_finite_subgroup {G : Type*} [Group G] {H : Subgroup G} (hH : Finite H)
    {x : G} (hx : x ∈ H) : IsOfFinOrder x := by
  haveI : Fintype H := Fintype.ofFinite H
  obtain ⟨m, k, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => (⟨x ^ i, pow_mem hx i⟩ : H))
  rw [isOfFinOrder_iff_pow_eq_one]
  have h3 : x ^ m = x ^ k := Subtype.ext_iff.mp heq
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨k - m, Nat.sub_pos_of_lt hlt, ?_⟩
    have h2 : x ^ k = x ^ m * x ^ (k - m) := by rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    have h4 : x ^ m * 1 = x ^ m * x ^ (k - m) := by rw [mul_one, ← h2]; exact h3
    exact (mul_left_cancel h4).symm
  · refine ⟨m - k, Nat.sub_pos_of_lt hlt, ?_⟩
    have h2 : x ^ m = x ^ k * x ^ (m - k) := by rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    have h4 : x ^ k * 1 = x ^ k * x ^ (m - k) := by rw [mul_one, ← h2]; exact h3.symm
    exact (mul_left_cancel h4).symm

end Work.Mostow
