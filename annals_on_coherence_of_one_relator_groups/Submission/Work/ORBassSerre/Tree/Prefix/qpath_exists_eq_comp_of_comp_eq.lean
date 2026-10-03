import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic

namespace Work.ORBassSerre.Tree.Prefix

open Quiver

/-- The endpoint of a prefix of a path is determined by the length of that prefix:
if `p.comp q = p₁.comp q₁` and `p.length = p₁.length`, then `p` and `p₁` end at the
same vertex.  (The vertex in question is the one sitting at position `p.length` in the
vertex list of the common path.) -/
theorem eq_endpoint_of_comp_eq_comp_of_length_eq {V : Type*} [Quiver V] {a b c b₁ : V}
    (p : Path a b) (q : Path b c) (p₁ : Path a b₁) (q₁ : Path b₁ c)
    (h : p.comp q = p₁.comp q₁) (hl : p.length = p₁.length) : b = b₁ := by
  have h1get : (p.comp q).vertices.get ⟨p.length, by simp⟩ = b :=
    Path.vertices_comp_get_length_eq p q
  have h2get : (p₁.comp q₁).vertices.get ⟨p₁.length, by simp⟩ = b₁ :=
    Path.vertices_comp_get_length_eq p₁ q₁
  have h1 : (p.comp q).vertices[p.length]? = some b := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨by simp, h1get⟩
  have h2 : (p₁.comp q₁).vertices[p₁.length]? = some b₁ := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨by simp, h2get⟩
  have hw : (p.comp q).vertices = (p₁.comp q₁).vertices := by rw [h]
  have : some b = some b₁ := by
    calc some b = (p.comp q).vertices[p.length]? := h1.symm
      _ = (p₁.comp q₁).vertices[p.length]? := by rw [hw]
      _ = (p₁.comp q₁).vertices[p₁.length]? := by rw [hl]
      _ = some b₁ := h2
  exact Option.some.inj this

/-- One direction of the prefix dichotomy: if `u` is not longer than `u'`, then `u` is an
initial segment of `u'`. -/
theorem exists_comp_of_length_le {V : Type*} [Quiver V] {a b c b' : V}
    {u : Path a b} {v : Path b c} {u' : Path a b'} {v' : Path b' c}
    (h : u.comp v = u'.comp v') (hle : u.length ≤ u'.length) :
    ∃ r : Path b b', u' = u.comp r := by
  obtain ⟨bv, p₁, p₂, hp, hlen⟩ := u'.exists_eq_comp_of_le_length hle
  have h' : u.comp v = p₁.comp (p₂.comp v') := by
    rw [hp] at h
    simpa using h
  have hbb : b = bv := eq_endpoint_of_comp_eq_comp_of_length_eq u v p₁ (p₂.comp v') h' hlen.symm
  subst hbb
  have hup : u = p₁ := ((Path.comp_inj' hlen.symm).1 h').1
  exact ⟨p₂, by rw [hp, hup]⟩

/-- Two decompositions of a path as `(prefix).comp (suffix)` have prefixes which are nested:
one of them is an initial segment of the other. -/
theorem qpath_exists_eq_comp_of_comp_eq {V : Type*} [Quiver V] {a b c : V}
    {u : Quiver.Path a b} {v : Quiver.Path b c} {b' : V} {u' : Quiver.Path a b'}
    {v' : Quiver.Path b' c} (h : u.comp v = u'.comp v') :
    (∃ r : Quiver.Path b b', u' = u.comp r) ∨ (∃ r : Quiver.Path b' b, u = u'.comp r) := by
  rcases le_total u.length u'.length with hle | hle
  · exact Or.inl (exists_comp_of_length_le h hle)
  · exact Or.inr (exists_comp_of_length_le h.symm hle)

end Work.ORBassSerre.Tree.Prefix
