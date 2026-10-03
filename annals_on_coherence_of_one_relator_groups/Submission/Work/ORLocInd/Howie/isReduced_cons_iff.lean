import Mathlib
import Submission.Work.ORLocInd.Howie.PathReduced

set_option autoImplicit false

universe u

namespace Work.ORLocInd.Howie

open Quiver

/-- Unfolding a single backtrack deletion: if `q` is obtained from `p` by deleting one
backtrack, then `p` splits as a prefix `p₁`, an arrow `g` followed by its reverse, and a
suffix `p₂`, while `q` is the concatenation of the prefix and the suffix. -/
theorem deleteBacktrack_decomp {V : Type u} [Quiver V] [Quiver.HasReverse V]
    {a b : V} {p q : Quiver.Path a b} (h : Quiver.Path.DeleteBacktrack p q) :
    ∃ (x y : V) (p₁ : Quiver.Path a x) (g : x ⟶ y) (p₂ : Quiver.Path x b),
      p = p₁.comp (g.toPath.comp ((Quiver.reverse g).toPath.comp p₂)) ∧ q = p₁.comp p₂ := by
  cases h with
  | intro p₁ g p₂ => exact ⟨_, _, p₁, g, p₂, rfl, rfl⟩

/-- Definitions used here live in `Submission.Work.ORLocInd.Howie.PathReduced`
(`Quiver.Path.EndsWith p f := ∃ p', p = p'.cons f`), and `Quiver.Path.IsReduced` is the
no-backtrack predicate of `Submission.Work.ORBassSerre.Tree.Basic`. -/
theorem isReduced_cons_iff {V : Type u} [Quiver V] [Quiver.HasReverse V] {a b c : V}
    {p : Quiver.Path a b} {e : b ⟶ c} :
    (p.cons e).IsReduced ↔
      p.IsReduced ∧ ∀ f : c ⟶ b, Quiver.Path.EndsWith p f → e ≠ Quiver.reverse f := by
  constructor
  · intro hred
    refine ⟨Quiver.Path.IsReduced.of_comp (q := e.toPath) hred, ?_⟩
    rintro f ⟨p', hp⟩ he
    have hdb : Quiver.Path.DeleteBacktrack (p.cons e) p' := by
      have h0 : Quiver.Path.DeleteBacktrack
          (p'.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp
            (Quiver.Path.nil : Quiver.Path c c))))
          (p'.comp Quiver.Path.nil) := Quiver.Path.DeleteBacktrack.intro p' f Quiver.Path.nil
      have heq : p'.comp (f.toPath.comp ((Quiver.reverse f).toPath.comp
            (Quiver.Path.nil : Quiver.Path c c))) = p.cons e := by
        rw [Quiver.Path.comp_nil, hp, he]
        simp
      rw [heq] at h0
      simpa using h0
    exact hred p' hdb
  · rintro ⟨hpred, hlast⟩ q hdb
    obtain ⟨x, y, p₁, g, p₂, hp, hq⟩ := deleteBacktrack_decomp hdb
    cases p₂ with
    | nil =>
      have hkey : p.cons e = (p₁.cons g).cons (Quiver.reverse g) := by
        rw [hp]; simp [Quiver.Path.comp_cons]
      obtain ⟨hyb, hph, heh⟩ := Quiver.Path.cons.inj hkey
      subst hyb
      exact hlast g ⟨p₁, eq_of_heq hph⟩ (eq_of_heq heh)
    | cons p₂' h =>
      have hkey : p.cons e
          = (p₁.comp (g.toPath.comp ((Quiver.reverse g).toPath.comp p₂'))).cons h := by
        rw [hp]; simp [Quiver.Path.comp_cons]
      obtain ⟨hbb, hph, -⟩ := Quiver.Path.cons.inj hkey
      subst hbb
      have hpeq : p = p₁.comp (g.toPath.comp ((Quiver.reverse g).toPath.comp p₂')) :=
        eq_of_heq hph
      refine hpred (p₁.comp p₂') ?_
      rw [hpeq]
      exact Quiver.Path.DeleteBacktrack.intro p₁ g p₂'

end Work.ORLocInd.Howie
