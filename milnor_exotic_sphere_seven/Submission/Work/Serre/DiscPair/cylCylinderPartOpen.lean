import Mathlib
import Submission.Work.Serre.C1Cyl

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The quotient map of the mapping cylinder is open away from the gluing locus

`cylMk f : (P × I) ⊕ Q → cyl f` is the quotient map presenting the mapping cylinder of `f`.  It is
not an open map: the image of an open neighbourhood of a point `(p, 1)` of the top circle is not
open, because `(p, 1)` is identified with `f p ∈ Q`.  But the *only* identifications made by the
quotient are the gluings `(p,1) ~ f p`:

`Work.Serre.eqvGen_inl_iff` says that if `a ~ b` and `a = Sum.inl (p, t)` with `t ≠ 1`, then
`b = a`.  Hence, on the part `{a | ∃ p t, t < 1 ∧ a = Sum.inl (p,t)}` of the disjoint union (the
cylinder minus its top circle), the quotient map is injective on equivalence classes, so the
preimage of the image of a subset `S` of that part is just `S` itself, and the quotient map is
open there. -/

open scoped Topology unitInterval

namespace Work.Serre.DiscPair

/-- **`cylMk` is open on the part of the cylinder below the top circle.**  For an open
`W ⊆ (P × I) ⊕ Q`, the image in `cyl f` of `W ∩ {t < 1}` is open: away from the top circle the
quotient map `cylMk f` makes no identifications. -/
theorem cylCylinderPartOpen {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    (f : C(P, Q)) (W : Set ((P × unitInterval) ⊕ Q)) (hW : IsOpen W) :
    IsOpen (Work.Serre.cylMk f ''
      (W ∩ {a | ∃ p : P, ∃ t : unitInterval, (t : ℝ) < 1 ∧ a = Sum.inl (p, t)})) := by
  classical
  -- The part of the disjoint union below the top circle.
  set S : Set ((P × unitInterval) ⊕ Q) :=
    {a | ∃ p : P, ∃ t : unitInterval, (t : ℝ) < 1 ∧ a = Sum.inl (p, t)} with hS
  -- It is open, being the `Sum.inl`-image of `univ ×ˢ {t | (t : ℝ) < 1}`.
  have hSopen : IsOpen S := by
    have hI : IsOpen {t : unitInterval | (t : ℝ) < 1} :=
      isOpen_lt continuous_subtype_val continuous_const
    have h : IsOpen (Sum.inl '' ((Set.univ : Set P) ×ˢ {t : unitInterval | (t : ℝ) < 1})) :=
      (isOpenMap_inl (X := P × unitInterval) (Y := Q)) _ (isOpen_univ.prod hI)
    convert h using 1
    ext a
    constructor
    · rintro ⟨p, t, ht, rfl⟩
      exact ⟨(p, t), ⟨trivial, ht⟩, rfl⟩
    · rintro ⟨⟨p, t⟩, ⟨-, ht⟩, rfl⟩
      exact ⟨p, t, ht, rfl⟩
  -- Away from the top circle, `cylMk f` is injective on equivalence classes: the preimage of the
  -- image of `W ∩ S` is `W ∩ S` itself.
  have hpre : Work.Serre.cylMk f ⁻¹' (Work.Serre.cylMk f '' (W ∩ S)) = W ∩ S := by
    ext b
    constructor
    · rintro ⟨a, ⟨haW, haS⟩, hab⟩
      obtain ⟨p, t, ht1, rfl⟩ := haS
      have ht : t ≠ 1 := by
        intro h
        rw [h] at ht1
        norm_num at ht1
      have heq : b = Sum.inl (p, t) :=
        (Work.Serre.eqvGen_inl_iff f ht (Quotient.exact hab)).mp rfl
      rw [heq]
      exact ⟨haW, ⟨p, t, ht1, rfl⟩⟩
    · intro hb
      exact ⟨b, hb, rfl⟩
  -- `cylMk f` is a quotient map, and `W ∩ S` is open.
  have hq : Topology.IsQuotientMap (Work.Serre.cylMk f) := isQuotientMap_quotient_mk'
  have h2 := hq.isOpen_preimage (s := Work.Serre.cylMk f '' (W ∩ S))
  rw [hpre] at h2
  exact h2.mp (hW.inter hSopen)

end Work.Serre.DiscPair
