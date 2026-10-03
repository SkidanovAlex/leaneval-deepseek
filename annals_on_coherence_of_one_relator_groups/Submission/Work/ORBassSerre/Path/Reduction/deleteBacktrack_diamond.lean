import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic
import Submission.Work.ORBassSerre.Tree.Prefix.qpath_exists_eq_comp_of_comp_eq

namespace Work.ORBassSerre.Path.Reduction

open Quiver

/-- Unfolding of `Quiver.Path.DeleteBacktrack` into an explicit decomposition: a single
backtrack deletion writes the path as `p₁ ++ e ++ e⁻¹ ++ p₂` and removes the middle pair. -/
theorem deleteBacktrack_cases {V : Type*} [Quiver V] [Quiver.HasReverse V] {A B : V}
    {p q : Quiver.Path A B} (h : Quiver.Path.DeleteBacktrack p q) :
    ∃ (x y : V) (p₁ : Quiver.Path A x) (e : x ⟶ y) (p₂ : Quiver.Path x B),
      p = p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)) ∧ q = p₁.comp p₂ := by
  cases h with
  | intro p₁ e p₂ => exact ⟨_, _, p₁, e, p₂, rfl, rfl⟩

/-- Arrows between the same vertices are equal when their `toPath`s are. -/
theorem toPath_inj {V : Type*} [Quiver V] {a b : V} {e f : a ⟶ b}
    (h : e.toPath = f.toPath) : e = f :=
  eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons h)

/-- If `e.toPath.comp S = f.toPath.comp S'` for arrows `e, f` with a common source, then the
targets of `e` and `f` coincide. -/
theorem eq_target_of_toPath_comp_eq {V : Type*} [Quiver V] {a b b' c : V} {e : a ⟶ b}
    {S : Quiver.Path b c} {f : a ⟶ b'} {S' : Quiver.Path b' c}
    (h : e.toPath.comp S = f.toPath.comp S') : b = b' := by
  obtain ⟨s, hs⟩ := Work.ORBassSerre.Tree.Prefix.exists_comp_of_length_le h
    (by simp : e.toPath.length ≤ f.toPath.length)
  have hsl : s.length = 0 := by
    have hh := congrArg Quiver.Path.length hs
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hh
    omega
  exact Quiver.Path.eq_of_length_zero s hsl

/-- The heart of the diamond property, in the situation where the first deletion happens at a
position `≤` the second one.  Writing `u = p₁ ++ (e ++ e⁻¹ ++ p₂)` for the first deletion and
`u = q₁ ++ (f ++ f⁻¹ ++ q₂)` with `q₁ = p₁ ++ r` for the second one, the segment `r` records
how much further along the second deletion is.  Depending on `r.length` (`0`, `1`, or `≥ 2`)
the two reducts are either literally equal or both delete two disjoint backtracks. -/
private theorem diamond_le {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {a b x y x' y' : V} {p₁ : Quiver.Path a x} {e : x ⟶ y} {p₂ : Quiver.Path x b}
    {q₁ : Quiver.Path a x'} {f : x' ⟶ y'} {q₂ : Quiver.Path x' b} {r : Quiver.Path x x'}
    (hqr : q₁ = p₁.comp r)
    (hR : e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)
        = r.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp q₂))) :
    ∃ z : Quiver.Path a b, (p₁.comp p₂).ReducesTo z ∧ (q₁.comp q₂).ReducesTo z := by
  rcases Nat.eq_zero_or_pos r.length with hr0 | hrpos
  · -- the two deletions happen at the same position, hence the reducts coincide
    obtain rfl : x = x' := Quiver.Path.eq_of_length_zero r hr0
    have hrnil : r = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero r hr0
    subst r
    simp only [Quiver.Path.comp_nil, Quiver.Path.nil_comp] at hqr hR
    obtain rfl : y = y' := eq_target_of_toPath_comp_eq hR
    have h1 : f.toPath = e.toPath ∧
        (Quiver.reverse f).toPath.comp q₂ = (Quiver.reverse e).toPath.comp p₂ :=
      (Quiver.Path.comp_inj' (by simp : f.toPath.length = e.toPath.length)).1 hR.symm
    have hfe : f = e := toPath_inj h1.1
    subst f
    have h2 : q₂ = p₂ := (Quiver.Path.comp_inj_right (p := (Quiver.reverse e).toPath)).1 h1.2
    subst q₂
    subst q₁
    exact ⟨p₁.comp p₂, Quiver.Path.ReducesTo.refl _, Quiver.Path.ReducesTo.refl _⟩
  · -- split off the first arrow of `r`
    obtain ⟨y'', g, r₁, hr₁_len, hr_eq⟩ :=
      Quiver.Path.eq_toPath_comp_of_length_eq_succ r (n := r.length - 1) (by omega)
    have hR₁ : e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)
        = g.toPath.comp (r₁.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp q₂))) := by
      rw [hr_eq, Quiver.Path.comp_assoc] at hR
      exact hR
    obtain rfl : y = y'' := eq_target_of_toPath_comp_eq hR₁
    have h1 : g.toPath = e.toPath ∧
        r₁.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp q₂))
          = (Quiver.reverse e).toPath.comp p₂ :=
      (Quiver.Path.comp_inj' (by simp : g.toPath.length = e.toPath.length)).1 hR₁.symm
    have hge : g = e := toPath_inj h1.1
    subst g
    have hR₂ : r₁.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp q₂))
        = (Quiver.reverse e).toPath.comp p₂ := h1.2
    rcases Nat.eq_zero_or_pos r₁.length with hr₁0 | hr₁pos
    · -- `r` has length `1`: the two deletions are adjacent and have the same reduct
      obtain rfl : y = x' := Quiver.Path.eq_of_length_zero r₁ hr₁0
      have hr₁nil : r₁ = Quiver.Path.nil := Quiver.Path.eq_nil_of_length_zero r₁ hr₁0
      subst r₁
      simp only [Quiver.Path.nil_comp] at hR₂
      obtain rfl : x = y' := (eq_target_of_toPath_comp_eq hR₂).symm
      have h2 : f.toPath = (Quiver.reverse e).toPath ∧
          (Quiver.reverse f).toPath.comp q₂ = p₂ :=
        (Quiver.Path.comp_inj' (by simp : f.toPath.length = (Quiver.reverse e).toPath.length)).1 hR₂
      have hf : f = Quiver.reverse e := toPath_inj h2.1
      simp only [Quiver.Path.comp_nil] at hr_eq
      subst r
      have hp2 : p₂ = e.toPath.comp q₂ := by
        have hh := h2.2
        rw [hf] at hh
        simpa only [Quiver.reverse_reverse] using hh.symm
      refine ⟨p₁.comp p₂, Quiver.Path.ReducesTo.refl _, ?_⟩
      rw [hqr, hp2]
      simp only [Quiver.Path.comp_assoc]
      exact Quiver.Path.ReducesTo.refl _
    · -- `r` has length `≥ 2`: the two backtracks are disjoint and can both be deleted
      obtain ⟨y''', h, r₂, hr₂_len, hr₁_eq⟩ :=
        Quiver.Path.eq_toPath_comp_of_length_eq_succ r₁ (n := r₁.length - 1) (by omega)
      have hR₃ : h.toPath.comp (r₂.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp q₂)))
          = (Quiver.reverse e).toPath.comp p₂ := by
        rw [← hR₂, hr₁_eq, Quiver.Path.comp_assoc]
      obtain rfl : x = y''' := (eq_target_of_toPath_comp_eq hR₃).symm
      have h3 : h.toPath = (Quiver.reverse e).toPath ∧
          r₂.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp q₂)) = p₂ :=
        (Quiver.Path.comp_inj' (by simp : h.toPath.length = (Quiver.reverse e).toPath.length)).1 hR₃
      have hh : h = Quiver.reverse e := toPath_inj h3.1
      refine ⟨p₁.comp (r₂.comp q₂), ?_, ?_⟩
      · -- delete the second backtrack from `v`
        have hd : Quiver.Path.DeleteBacktrack
            (r₂.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp q₂))) (r₂.comp q₂) :=
          Quiver.Path.DeleteBacktrack.intro r₂ f q₂
        rw [← h3.2]
        exact Quiver.Path.ReducesTo.tail (Quiver.Path.ReducesTo.refl _)
          (Quiver.Path.DeleteBacktrack.comp_left hd p₁)
      · -- delete the first backtrack from `w`
        have hd : Quiver.Path.DeleteBacktrack
            (e.toPath.comp ((Quiver.reverse e).toPath.comp (r₂.comp q₂))) (r₂.comp q₂) := by
          simpa using Quiver.Path.DeleteBacktrack.intro (Quiver.Path.nil) e (r₂.comp q₂)
        have hq₁ : q₁ = p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp r₂)) := by
          rw [hqr, hr_eq, hr₁_eq, hh]
        rw [hq₁]
        simp only [Quiver.Path.comp_assoc]
        exact Quiver.Path.ReducesTo.tail (Quiver.Path.ReducesTo.refl _)
          (Quiver.Path.DeleteBacktrack.comp_left hd p₁)

/-- Local confluence of backtrack deletion: two single backtrack deletions from the same path can be completed to a common reduct. -/
theorem deleteBacktrack_diamond {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {a b : V} {u v w : Quiver.Path a b}
    (hv : Quiver.Path.DeleteBacktrack u v) (hw : Quiver.Path.DeleteBacktrack u w) :
    ∃ z : Quiver.Path a b, v.ReducesTo z ∧ w.ReducesTo z := by
  obtain ⟨x, y, p₁, e, p₂, hE₁, hv'⟩ := deleteBacktrack_cases hv
  obtain ⟨x', y', q₁, f, q₂, hE₂, hw'⟩ := deleteBacktrack_cases hw
  have hcomp : p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂))
      = q₁.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp q₂)) := hE₁.symm.trans hE₂
  rcases le_total p₁.length q₁.length with hle | hle
  · obtain ⟨r, hr⟩ := Work.ORBassSerre.Tree.Prefix.exists_comp_of_length_le hcomp hle
    have hR : e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)
        = r.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp q₂)) := by
      have hh : p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂))
          = p₁.comp (r.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp q₂))) := by
        rw [hcomp, hr, Quiver.Path.comp_assoc]
      exact (Quiver.Path.comp_inj_right (p := p₁)).1 hh
    obtain ⟨z, hz₁, hz₂⟩ := diamond_le hr hR
    exact ⟨z, by rw [hv']; exact hz₁, by rw [hw']; exact hz₂⟩
  · obtain ⟨r, hr⟩ := Work.ORBassSerre.Tree.Prefix.exists_comp_of_length_le hcomp.symm hle
    have hR : f.toPath.comp ((Quiver.reverse f).toPath.comp q₂)
        = r.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)) := by
      have hh : q₁.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp q₂))
          = q₁.comp (r.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂))) := by
        rw [← hcomp, hr, Quiver.Path.comp_assoc]
      exact (Quiver.Path.comp_inj_right (p := q₁)).1 hh
    obtain ⟨z, hz₁, hz₂⟩ := diamond_le hr hR
    exact ⟨z, by rw [hv']; exact hz₂, by rw [hw']; exact hz₁⟩

end Work.ORBassSerre.Path.Reduction
