/-
  WilE5 / Strat — a child state of the stratification recursion is contained in its parent.

  A child `childSt c M NΦ σ t s` is obtained from the state `σ` by appending conditions:
  * its system `childB c σ t = σ.B ++ [(peelVal c σ t, t.l)]` extends `σ.B`;
  * its accumulated vanishing list `childΞ c M NΦ σ t` starts with `σ.Ξ`;
  * its strict positivity list `childν c σ t s` starts with `σ.ν`.

  Since `stSemiPf X σ = semiPfAnd X (stCond σ)` and `semiPfAnd` intersects `X.set` with the
  basic condition `stCond σ`, an inclusion of the condition lists in the appropriate direction
  immediately yields the inclusion of the sets.
-/
import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.Wilkies.E.Spec

namespace Work.WilE5.Strat

open WilkiesDesign WilkiesDesign.E

/-- A conjunction of basic conditions is monotone in the two condition lists. -/
theorem holds_mono {k r : ℕ} {c : EAChain k r} {B B' : Basic k r}
    (he : ∀ f ∈ B.eqs, f ∈ B'.eqs) (hp : ∀ g ∈ B.pos, g ∈ B'.pos) {x : Fin k → ℝ}
    (h : B'.holds c x) : B.holds c x :=
  ⟨fun f hf => h.1 f (he f hf), fun g hg => h.2 g (hp g hg)⟩

/-- Every equation of the parent state is an equation of a child. -/
theorem stCond_eqs_subset_child {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r)
    (t : Test q) (s : Bool) :
    ∀ f ∈ (stCond σ).eqs, f ∈ (stCond (childSt X.c M NΦ σ t s)).eqs := by
  intro f hf
  simp only [stCond, childSt, childB, childΞ, List.map_append, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, List.map_cons, List.map_nil] at hf ⊢
  tauto

/-- Every strict positivity condition of the parent state is one of a child. -/
theorem stCond_pos_subset_child {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r)
    (t : Test q) (s : Bool) :
    ∀ g ∈ (stCond σ).pos, g ∈ (stCond (childSt X.c M NΦ σ t s)).pos := by
  intro g hg
  simp only [stCond, childSt, childν, List.mem_append] at hg ⊢
  exact Or.inl hg

theorem child_subset_parent {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (M NΦ : ℕ)
    (σ : Work.WilE5.St p q X.r) (t : Work.WilE5.Test q) (s : Bool) :
    (Work.WilE5.stSemiPf X (Work.WilE5.childSt X.c M NΦ σ t s)).set ⊆
      (Work.WilE5.stSemiPf X σ).set := by
  intro x hx
  rw [stSemiPf, semiPfAnd_set] at hx ⊢
  exact ⟨hx.1, holds_mono (stCond_eqs_subset_child X M NΦ σ t s)
    (stCond_pos_subset_child X M NΦ σ t s) hx.2⟩

end Work.WilE5.Strat
