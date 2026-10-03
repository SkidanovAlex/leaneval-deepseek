import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic

namespace Work.ORBassSerre.Tree.Map

open Quiver

/-- Explicit description of a single backtrack deletion: a backtrack consists of an arrow `e`
immediately followed by its reverse `reverse e`, and one deletion removes this pair. -/
theorem deleteBacktrack_iff_exists {V : Type*} [Quiver V] [Quiver.HasReverse V]
    {a b : V} (X R : Quiver.Path a b) :
    Quiver.Path.DeleteBacktrack X R ↔
      ∃ (x y : V) (p₁ : Quiver.Path a x) (e : x ⟶ y) (p₂ : Quiver.Path x b),
        X = p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)) ∧ R = p₁.comp p₂ := by
  constructor
  · intro h; cases h with | intro p₁ e p₂ => exact ⟨_, _, p₁, e, p₂, rfl, rfl⟩
  · rintro ⟨x, y, p₁, e, p₂, rfl, rfl⟩; exact Quiver.Path.DeleteBacktrack.intro p₁ e p₂

/-- A backtrack deleted from `p.cons e` is either a backtrack deleted from `p`, or the one arising
at the junction between `p` and `e` (namely `p` ends with the reverse of `e`). -/
theorem deleteBacktrack_cons_iff {V : Type*} [Quiver V] [Quiver.HasReverse V]
    {a c b : V} (p : Quiver.Path a c) (e : c ⟶ b) (r : Quiver.Path a b) :
    Quiver.Path.DeleteBacktrack (p.cons e) r ↔
      (∃ r₀ : Quiver.Path a c, Quiver.Path.DeleteBacktrack p r₀ ∧ r = r₀.cons e) ∨
      (∃ (p' : Quiver.Path a b) (e' : b ⟶ c),
        p = p'.cons e' ∧ e = Quiver.reverse e' ∧ r = p') := by
  constructor
  · intro h
    obtain ⟨x, y, p₁, e₀, p₂, hX, hR⟩ := (deleteBacktrack_iff_exists (p.cons e) r).mp h
    cases p₂ with
    | nil =>
      simp only [Quiver.Path.comp_nil, Quiver.Path.comp_toPath_eq_cons] at hX
      have hcy : c = y := Quiver.Path.obj_eq_of_cons_eq_cons hX
      subst hcy
      have heq1 := Quiver.Path.heq_of_cons_eq_cons hX
      have heq2 := Quiver.Path.hom_heq_of_cons_eq_cons hX
      refine Or.inr ⟨p₁, e₀, eq_of_heq heq1, eq_of_heq heq2, ?_⟩
      simpa using hR
    | cons p₂' f =>
      simp only [Quiver.Path.comp_cons] at hX
      have hcu : c = _ := Quiver.Path.obj_eq_of_cons_eq_cons hX
      subst hcu
      have heq1 := Quiver.Path.heq_of_cons_eq_cons hX
      have heq2 : e ≍ f := Quiver.Path.hom_heq_of_cons_eq_cons (e := e) (e' := f) hX
      refine Or.inl ⟨p₁.comp p₂', ?_, ?_⟩
      · rw [eq_of_heq heq1]
        exact Quiver.Path.DeleteBacktrack.intro p₁ e₀ p₂'
      · rw [hR, ← eq_of_heq heq2]
        rfl
  · rintro (⟨r₀, hr₀, hr⟩ | ⟨p', e', hp, he, hr⟩)
    · subst hr
      obtain ⟨x, y, p₁, e₀, p₂, hX, hR⟩ := (deleteBacktrack_iff_exists p r₀).mp hr₀
      subst hX
      subst hR
      exact Quiver.Path.DeleteBacktrack.intro p₁ e₀ (p₂.cons e)
    · rw [hp, he, hr]
      exact Quiver.Path.DeleteBacktrack.intro p' e' Path.nil

/-- If a path is mapped by a prefunctor injective on objects to a path ending with an arrow `e'`,
then the source path ends with an arrow mapping to `e'`. -/
theorem mapPath_eq_cons {V W : Type*} [Quiver V] [Quiver W] (F : V ⥤q W)
    (hinj_obj : Function.Injective F.obj)
    {a b b' : V} {p : Quiver.Path a b} {p' : Quiver.Path (F.obj a) (F.obj b')}
    {e' : F.obj b' ⟶ F.obj b} (h : F.mapPath p = p'.cons e') :
    ∃ (p'' : Quiver.Path a b') (e'' : b' ⟶ b), p = p''.cons e'' ∧ F.map e'' = e' := by
  cases p with
  | nil =>
    simp only [Prefunctor.mapPath_nil] at h
    exact absurd h.symm (Quiver.Path.cons_ne_nil p' e')
  | cons p'' e'' =>
    rw [Prefunctor.mapPath_cons] at h
    have h_obj : F.obj _ = F.obj b' := Quiver.Path.obj_eq_of_cons_eq_cons h
    have hb : _ = b' := hinj_obj h_obj
    subst hb
    refine ⟨p'', e'', rfl, ?_⟩
    exact eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons h)

/-- A prefunctor which is injective on vertices and on arrows and preserves reversal maps
reduced paths to reduced paths. -/
theorem qpath_mapPath_isReduced {V W : Type*} [Quiver V] [Quiver.HasReverse V] [Quiver W]
    [Quiver.HasReverse W] (F : V ⥤q W) [F.MapReverse]
    (hinj_obj : Function.Injective F.obj)
    (hinj : ∀ ⦃a b : V⦄, Function.Injective (fun e : a ⟶ b => F.map e))
    {a b : V} {p : Quiver.Path a b} (hp : p.IsReduced) : (F.mapPath p).IsReduced := by
  induction p with
  | nil =>
    rw [Prefunctor.mapPath_nil]
    exact Quiver.Path.IsReduced.nil (F.obj a)
  | cons p₀ e₀ ih =>
    rw [Prefunctor.mapPath_cons]
    rw [Quiver.Path.IsReduced]
    intro q hq
    rcases (deleteBacktrack_cons_iff (F.mapPath p₀) (F.map e₀) q).mp hq with
      ⟨r₀, hr₀, -⟩ | ⟨p', e', hmap, he', -⟩
    · exact ih (Quiver.Path.IsReduced.of_comp (p := p₀) (q := e₀.toPath) hp) r₀ hr₀
    · obtain ⟨p'', e'', hp_decomp, hFmap⟩ := mapPath_eq_cons F hinj_obj hmap
      have hrev : F.map e₀ = F.map (Quiver.reverse e'') := by
        rw [he', Prefunctor.map_reverse, hFmap]
      have heq : e₀ = Quiver.reverse e'' := hinj hrev
      refine hp p'' ?_
      subst hp_decomp
      subst heq
      exact Quiver.Path.DeleteBacktrack.intro p'' e'' Quiver.Path.nil

end Work.ORBassSerre.Tree.Map
