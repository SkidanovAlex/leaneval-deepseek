import Mathlib
import Submission.Work.ORLocInd.Howie.PathReduced

set_option autoImplicit false

universe u

namespace Work.ORLocInd.Howie

/-- Auxiliary combinatorial fact: if `p` is a non-empty path and the concatenation `p.comp q`
agrees with `e.toPath.comp r`, then already `p` itself begins with the arrow `e`.  Equivalently,
concatenating a path on the right does not change the first arrow of a non-empty path. -/
private theorem exists_eq_toPath_comp_of_comp_eq {V : Type u} [Quiver V] {a b y : V}
    (p : Quiver.Path a b) (hp : p.length ≠ 0) (e : a ⟶ y) :
    ∀ {c : V} (q : Quiver.Path b c) (r : Quiver.Path y c),
      p.comp q = e.toPath.comp r → ∃ p' : Quiver.Path y b, p = e.toPath.comp p' := by
  intro c q
  induction q with
  | nil =>
      intro r h
      exact ⟨r, h⟩
  | cons q₀ g ih =>
      intro r h
      cases r with
      | nil =>
          -- lengths force `p.length = 0`, contradicting `hp`
          exfalso
          have hlen := congrArg Quiver.Path.length h
          simp only [Quiver.Path.comp_cons, Quiver.Path.length_cons,
            Quiver.Path.length_comp, Quiver.Path.length_toPath,
            Quiver.Path.length_nil] at hlen
          omega
      | cons r₀ g' =>
          -- peel off the last arrow on both sides
          rw [Quiver.Path.comp_cons] at h
          have hbw := Quiver.Path.obj_eq_of_cons_eq_cons h
          subst hbw
          have h1 : p.comp q₀ = e.toPath.comp r₀ :=
            eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h)
          exact ih r₀ h1

/-- Definitions used here live in `Submission.Work.ORLocInd.Howie.PathReduced`:
`Quiver.Path.StartsWith p e := ∃ p', p = e.toPath.comp p'`.
(`p.length ≠ 0` is the well-typed way of saying `p` is not the empty path.) -/
theorem startsWith_comp {V : Type u} [Quiver V] {a b c y : V} {p : Quiver.Path a b}
    {q : Quiver.Path b c} (hp : p.length ≠ 0) (e : a ⟶ y) :
    Quiver.Path.StartsWith (p.comp q) e ↔ Quiver.Path.StartsWith p e := by
  constructor
  · rintro ⟨r, hr⟩
    exact exists_eq_toPath_comp_of_comp_eq p hp e q r hr
  · rintro ⟨p', hp'⟩
    exact ⟨p'.comp q, by rw [hp', Quiver.Path.comp_assoc]⟩

end Work.ORLocInd.Howie
