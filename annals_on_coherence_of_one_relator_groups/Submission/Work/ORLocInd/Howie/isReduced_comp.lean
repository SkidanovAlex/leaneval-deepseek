/-
# Reducedness of a concatenation of paths

The main result of this file is

`Quiver.Path.isReduced_comp_iff : (p.comp q).IsReduced ↔ p.IsReduced ∧ q.IsReduced ∧ ¬ JoinConflict p q`

(see `Submission/Work/ORLocInd/Howie/PathReduced.lean` for `JoinConflict`): a backtrack in a
concatenation of paths is either a backtrack inside one of the two factors, or a backtrack
straddling the join, i.e. the last arrow of `p` is the reverse of the first arrow of `q`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.PathReduced
import Submission.Work.ORBassSerre.Path.Reduction.deleteBacktrack_diamond
import Submission.Work.ORBassSerre.Tree.Prefix.qpath_exists_eq_comp_of_comp_eq

set_option autoImplicit false

universe u

namespace Quiver.Path

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
variable {a b c : V}

/-- A backtrack of a concatenation `p.comp q` is either a backtrack inside one of the two
factors, or a backtrack straddling the join (`JoinConflict p q`). -/
theorem deleteBacktrack_comp_cases {p : Path a b} {q : Path b c} {r : Path a c}
    (h : DeleteBacktrack (p.comp q) r) :
    (∃ s : Path a b, DeleteBacktrack p s) ∨ (∃ s : Path b c, DeleteBacktrack q s) ∨
      JoinConflict p q := by
  obtain ⟨x, y, p₁, e, p₂, hE, -⟩ := Work.ORBassSerre.Path.Reduction.deleteBacktrack_cases h
  rcases lt_or_ge p₁.length p.length with hlt | hle
  · -- `p₁` is strictly shorter than `p`: the deleted pair starts inside `p`
    obtain ⟨r₁, hp₁⟩ := Work.ORBassSerre.Tree.Prefix.exists_comp_of_length_le hE.symm
      (le_of_lt hlt)
    have h1 : r₁.comp q = e.toPath.comp ((Quiver.reverse e).toPath.comp p₂) := by
      rw [hp₁, Quiver.Path.comp_assoc] at hE
      exact (Quiver.Path.comp_inj_right (p := p₁)).1 hE
    have hlen : 1 ≤ r₁.length := by
      have hl := congrArg Path.length hp₁
      simp only [Path.length_comp] at hl
      omega
    rcases lt_or_ge r₁.length 2 with hlt2 | hge2
    · -- `r₁` is a single arrow: the deleted pair straddles the join
      obtain ⟨b₁, f, r₂, hr₂len, hr₁eq⟩ :=
        Path.eq_toPath_comp_of_length_eq_succ r₁ (n := 0) (by omega)
      have hb₁ : b₁ = b := Path.eq_of_length_zero r₂ hr₂len
      cases hb₁
      have hr₂nil : r₂ = Path.nil := Path.eq_nil_of_length_zero r₂ hr₂len
      rw [hr₂nil, Path.comp_nil] at hr₁eq
      have h1' : f.toPath.comp q = e.toPath.comp ((Quiver.reverse e).toPath.comp p₂) := by
        rw [← hr₁eq]
        exact h1
      obtain rfl : b = y := Work.ORBassSerre.Path.Reduction.eq_target_of_toPath_comp_eq h1'
      have h2 : f.toPath = e.toPath ∧ q = (Quiver.reverse e).toPath.comp p₂ :=
        (Path.comp_inj' (by simp : f.toPath.length = e.toPath.length)).1 h1'
      have hfe : f = e := Work.ORBassSerre.Path.Reduction.toPath_inj h2.1
      refine Or.inr (Or.inr ⟨x, p₁, e, p₂, ?_, h2.2⟩)
      rw [hp₁, hr₁eq, hfe]
      rfl
    · -- `r₁` has length at least two: the deleted pair lies inside `p`
      obtain ⟨b₁, f, r₂, hr₂len, hr₁eq⟩ :=
        Path.eq_toPath_comp_of_length_eq_succ r₁ (n := r₁.length - 1) (by omega)
      have h1' : f.toPath.comp (r₂.comp q) = e.toPath.comp ((Quiver.reverse e).toPath.comp p₂) := by
        rw [hr₁eq, Path.comp_assoc] at h1
        exact h1
      obtain rfl : b₁ = y := Work.ORBassSerre.Path.Reduction.eq_target_of_toPath_comp_eq h1'
      have h2 : f.toPath = e.toPath ∧ r₂.comp q = (Quiver.reverse e).toPath.comp p₂ :=
        (Path.comp_inj' (by simp : f.toPath.length = e.toPath.length)).1 h1'
      have hfe : f = e := Work.ORBassSerre.Path.Reduction.toPath_inj h2.1
      obtain ⟨b₂, g, r₃, hr₃len, hr₂eq⟩ :=
        Path.eq_toPath_comp_of_length_eq_succ r₂ (n := r₂.length - 1) (by omega)
      have h3 : g.toPath.comp (r₃.comp q) = (Quiver.reverse e).toPath.comp p₂ := by
        rw [hr₂eq, Path.comp_assoc] at h2
        exact h2.2
      obtain rfl : b₂ = x := Work.ORBassSerre.Path.Reduction.eq_target_of_toPath_comp_eq h3
      have h3' : g.toPath = (Quiver.reverse e).toPath ∧ r₃.comp q = p₂ :=
        (Path.comp_inj' (by simp : g.toPath.length = (Quiver.reverse e).toPath.length)).1 h3
      have hge : g = Quiver.reverse e := Work.ORBassSerre.Path.Reduction.toPath_inj h3'.1
      refine Or.inl ⟨p₁.comp r₃, ?_⟩
      rw [hp₁, hr₁eq, hfe, hr₂eq, hge]
      exact DeleteBacktrack.intro p₁ e r₃
  · -- the deleted pair lies in `q`
    obtain ⟨r₁, hp₁⟩ := Work.ORBassSerre.Tree.Prefix.exists_comp_of_length_le hE hle
    have h1 : q = r₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)) := by
      rw [hp₁, Quiver.Path.comp_assoc] at hE
      exact (Quiver.Path.comp_inj_right (p := p)).1 hE
    refine Or.inr (Or.inl ⟨r₁.comp p₂, ?_⟩)
    rw [h1]
    exact DeleteBacktrack.intro r₁ e p₂

/-- **A path is reduced iff its two factors are reduced and no backtrack straddles the join.** -/
theorem isReduced_comp_iff {p : Path a b} {q : Path b c} :
    (p.comp q).IsReduced ↔ p.IsReduced ∧ q.IsReduced ∧ ¬ JoinConflict p q := by
  constructor
  · intro h
    have hq : q.IsReduced := by
      intro r hr
      exact h (p.comp r) (hr.comp_left p)
    exact ⟨h.of_comp, hq, fun hc => joinConflict_not_isReduced hc h⟩
  · rintro ⟨hp, hq, hnj⟩ r hr
    rcases deleteBacktrack_comp_cases hr with ⟨s, hs⟩ | ⟨s, hs⟩ | hc
    · exact hp s hs
    · exact hq s hs
    · exact hnj hc

end Quiver.Path
