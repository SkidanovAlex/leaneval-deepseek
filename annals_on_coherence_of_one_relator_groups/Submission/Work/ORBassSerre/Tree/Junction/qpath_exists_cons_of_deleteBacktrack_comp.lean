import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic
import Submission.Work.ORBassSerre.Tree.Prefix.qpath_exists_eq_comp_of_comp_eq

namespace Work.ORBassSerre.Tree.Junction

open Quiver

/-- Unfolding of `Quiver.Path.DeleteBacktrack` into an explicit decomposition. -/
theorem deleteBacktrack_cases {V : Type*} [Quiver V] [Quiver.HasReverse V] {A B : V}
    {p q : Quiver.Path A B} (h : Quiver.Path.DeleteBacktrack p q) :
    ∃ (x y : V) (p₁ : Quiver.Path A x) (e : x ⟶ y) (p₂ : Quiver.Path x B),
      p = p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)) ∧ q = p₁.comp p₂ := by
  cases h with
  | intro p₁ e p₂ => exact ⟨_, _, p₁, e, p₂, rfl, rfl⟩

/-- If `u.comp v` is not reduced while both `u` and `v` are, then the backtrack that is deleted
lies at the junction: `u` ends with an arrow `f` and `v` starts with `f⁻¹`. -/
theorem qpath_exists_cons_of_deleteBacktrack_comp {V : Type*} [Quiver V]
    [Quiver.HasReverse V] {a b c : V} {u : Quiver.Path a b} {v : Quiver.Path b c}
    {w : Quiver.Path a c} (hu : u.IsReduced) (hv : v.IsReduced)
    (h : Quiver.Path.DeleteBacktrack (u.comp v) w) :
    ∃ (x : V) (f : x ⟶ b) (u' : Quiver.Path a x) (v' : Quiver.Path x c),
      u = u'.cons f ∧ v = (Quiver.reverse f).toPath.comp v' ∧ w = u'.comp v' := by
  obtain ⟨x, y, p₁, e, p₂, hE, hw⟩ := deleteBacktrack_cases h
  rcases Work.ORBassSerre.Tree.Prefix.qpath_exists_eq_comp_of_comp_eq hE with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- the backtrack lies inside `v`
    have hdb : Quiver.Path.DeleteBacktrack v (r.comp p₂) := by
      have hv' : v = r.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)) := by
        refine (Quiver.Path.comp_inj_right (p := u)).1 ?_
        rw [hE, hr, Quiver.Path.comp_assoc]
      rw [hv']
      exact Quiver.Path.DeleteBacktrack.intro r e p₂
    exact absurd hdb (hv (r.comp p₂))
  · -- `u = p₁.comp r`
    have hcancel : r.comp v = e.toPath.comp ((Quiver.reverse e).toPath.comp p₂) := by
      refine (Quiver.Path.comp_inj_right (p := p₁)).1 ?_
      rw [← Quiver.Path.comp_assoc, ← hr]
      exact hE
    rcases Work.ORBassSerre.Tree.Prefix.qpath_exists_eq_comp_of_comp_eq hcancel with
      ⟨s, hs⟩ | ⟨s, hs⟩
    · -- first arrow of `r` is `e`
      have hlen : r.length + s.length = 1 := by
        have hh := congrArg Quiver.Path.length hs
        rw [Quiver.Path.length_toPath, Quiver.Path.length_comp] at hh
        omega
      rcases Nat.eq_zero_or_pos r.length with hrlen | hrpos
      · -- `r = nil` forces the backtrack inside `v`
        have hx := Quiver.Path.eq_of_length_zero r hrlen
        subst hx
        have hrnil : r = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero r hrlen
        subst hrnil
        have hvR : v = e.toPath.comp ((Quiver.reverse e).toPath.comp p₂) := by
          simpa using hcancel
        have hdb : Quiver.Path.DeleteBacktrack v p₂ := by
          rw [hvR]
          simpa using Quiver.Path.DeleteBacktrack.intro Quiver.Path.nil e p₂
        exact absurd hdb (hv p₂)
      · -- success: the backtrack straddles the junction
        have hslen : s.length = 0 := by omega
        have hby := Quiver.Path.eq_of_length_zero s hslen
        subst hby
        have hsnil : s = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero s hslen
        subst hsnil
        simp only [Quiver.Path.comp_nil] at hs
        have hr_eq : r = e.toPath := hs.symm
        have hvR : v = (Quiver.reverse e).toPath.comp p₂ := by
          have h1 := hcancel
          rw [hr_eq] at h1
          exact (Quiver.Path.comp_inj_right (p := e.toPath)).1 h1
        exact ⟨x, e, p₁, p₂, by rw [hr, hr_eq, Quiver.Path.comp_toPath_eq_cons], hvR, hw⟩
    · -- `r = e.toPath.comp s`
      have hs2 : s.comp v = (Quiver.reverse e).toPath.comp p₂ := by
        refine (Quiver.Path.comp_inj_right (p := e.toPath)).1 ?_
        rw [← Quiver.Path.comp_assoc, ← hs]
        exact hcancel
      rcases Work.ORBassSerre.Tree.Prefix.qpath_exists_eq_comp_of_comp_eq hs2 with
        ⟨t, ht⟩ | ⟨t, ht⟩
      · have hlen : s.length + t.length = 1 := by
          have hh := congrArg Quiver.Path.length ht
          rw [Quiver.Path.length_toPath, Quiver.Path.length_comp] at hh
          omega
        rcases Nat.eq_zero_or_pos s.length with hslen | hspos
        · -- success
          have hby := Quiver.Path.eq_of_length_zero s hslen
          subst hby
          have hsnil : s = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero s hslen
          subst hsnil
          simp only [Quiver.Path.comp_nil] at hs
          have hr_eq : r = e.toPath := hs
          have hvR : v = (Quiver.reverse e).toPath.comp p₂ := by simpa using hs2
          exact ⟨x, e, p₁, p₂, by rw [hr, hr_eq, Quiver.Path.comp_toPath_eq_cons], hvR, hw⟩
        · -- `s = (reverse e).toPath` gives a backtrack inside `u`
          have htlen : t.length = 0 := by omega
          have hbs := Quiver.Path.eq_of_length_zero t htlen
          subst hbs
          have htnil : t = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero t htlen
          subst htnil
          simp only [Quiver.Path.comp_nil] at ht
          have hs_eq : s = (Quiver.reverse e).toPath := ht.symm
          have hr_eq : r = e.toPath.comp ((Quiver.reverse e).toPath) := by rw [hs, hs_eq]
          have hdbr : Quiver.Path.DeleteBacktrack r Quiver.Path.nil := by
            rw [hr_eq]
            simpa only [Quiver.Path.nil_comp, Quiver.Path.comp_nil] using
              Quiver.Path.DeleteBacktrack.intro Quiver.Path.nil e Quiver.Path.nil
          have hdbu : Quiver.Path.DeleteBacktrack u p₁ := by
            have hh := Quiver.Path.DeleteBacktrack.comp_left hdbr p₁
            simpa [hr] using hh
          exact absurd hdbu (hu p₁)
      · -- `s = (reverse e).toPath.comp t` gives a backtrack inside `u`
        have hr_eq : r = e.toPath.comp ((Quiver.reverse e).toPath.comp t) := by rw [hs, ht]
        have hdbr : Quiver.Path.DeleteBacktrack r t := by
          rw [hr_eq]
          simpa using Quiver.Path.DeleteBacktrack.intro Quiver.Path.nil e t
        have hdbu : Quiver.Path.DeleteBacktrack u (p₁.comp t) := by
          have hh := Quiver.Path.DeleteBacktrack.comp_left hdbr p₁
          simpa [hr] using hh
        exact absurd hdbu (hu (p₁.comp t))

end Work.ORBassSerre.Tree.Junction
