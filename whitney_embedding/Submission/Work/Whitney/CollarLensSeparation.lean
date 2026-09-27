import Mathlib

/-!
# The lens separation of the two collars (brick (2.a) of `NOTES_S42` §13)

`NOTES_S42_LINEAR_COLLAR_AND_WALL_CONFINEMENT.md` §12 splits the confinement clause (iii) — the wall
scalar being non-positive off a compact core `K` — into a *fibre* statement (2.a) and a *sign*
statement (3).  This file states (2.a) as the **lens condition**

    (lens)   ∀ x ∈ U, ∀ y ∈ V,  β (f y) = β (f x) → β (f x) ∈ K,

for the finger collar `U` (of the arc `γ₂`) and the partner collar `V` (of the arc `γ₁`): *the two
collars' projected base images meet only inside the core `K`*.  The condition is what rules the
partner-collar partners out of (iii), and the two lemmas below are the interface

    (lens)  ⟹  no base is shared by `U` and `V` off `K`,
    (lens) + [the far partners satisfy the sign]  ⟹  the confinement (iii) for the zero section.

The *existence* of the lens separation (2.a) — a thin `U` and `V` whose projected images meet only
near the two crossing bases, plus `K` containing those bases and avoiding the base image of
`f '' frontier U` — is the remaining geometric obligation of (2.a); it is *not* asserted here.  Two
remarks from the sessions, recorded so that they are not lost:

* it is a statement about the *projected* arcs `β ∘ f ∘ γ₂`, `β ∘ f ∘ γ₁`, and `hγdisj`/`hγend`
  give only the *unprojected* separation (the two arcs' `f`-images meet exactly at the two
  crossings).  For a *linear* `β` the projected arcs need not be separated away from the crossings
  (the same nearly-closed-arc phenomenon as in §9), so (2.a) must either be proved for a suitable
  (nonlinear, collar-adapted) trivialisation or be replaced by the sign statement (3) applied to the
  partner-collar partners as well — the two routes differ only in how much (3) has to carry;
* the last clause of the *existence* statement, `K ∩ β '' (f '' frontier U) = ∅`, is what makes the
  amplitude's taper region (which lives near the frontier's bases) partner-free; it is the sharp form
  of "the partner's projected collar avoids the boundary of the finger's projected image".
## Route (B): the sign carries all the outside partners, and (2.a) becomes unnecessary

The alternative to proving the lens separation (2.a) is to *accept the crossing*: leave the partners
of the partner collar `V` inside the burden of the sign brick (3) instead of excluding them.  The
lemma `confinement_of_zero_section_and_sign` below shows that this is enough: with the collar as the
zero section, the *only* thing the confinement clause (iii) needs is the sign hypothesis on the
partners *outside the collar* — the partners inside the collar give height difference `0` for free.

Consequence, and the reason this is the route to take: **the projection genericity of (2.a) is not
needed at all.**  What remains of the collar-geometry input is only the *tube trivialisation* with
the collar as its zero section — a tubular-neighbourhood construction along the arc, with no
separation demand on the projected images — together with the sign statement on the outside partners
(brick (3)).  The lens lemmas above are then an *optimization* of (3)'s load, available if the
trivialisation happens to be well adapted, and droppable otherwise.
-/

open Set

namespace Work.Whitney

/-- **The lens condition rules out the partner-collar partners.**  If the two collars' projected
base images meet only inside `K`, then no source of `U` whose base is outside `K` shares its base
with a point of `V`. -/
theorem partner_notMem_of_lens {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (β : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin n))
    (U V : Set M) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hlens : ∀ x : M, x ∈ U → ∀ y : M, y ∈ V → β (f y) = β (f x) → β (f x) ∈ K) :
    ∀ x : M, x ∈ U → β (f x) ∉ K → ∀ y : M, y ∈ V → β (f y) ≠ β (f x) := by
  intro x hx hK y hy hcon
  exact hK (hlens x hx y hy hcon)

/-- **The confinement off `K` from the lens condition and the far partners.**  In the tube
coordinates (the collar is the zero section, `θ (f x) = 0` for `x ∈ U`), the confinement clause
(iii) follows from the lens condition together with the *far* case: the partners outside
`U ∪ V` whose height is parallel to `e` must have a non-positive `e`-component.

Thus (2.a) removes the partner collar from the burden of the sign brick (3), and (3) only has to
carry the far partners — the case of §9 of the note. -/
theorem hwall_of_lens_and_far {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (β θ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin n))
    (U V : Set M) (e : EuclideanSpace ℝ (Fin n)) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hlens : ∀ x : M, x ∈ U → ∀ y : M, y ∈ V → β (f y) = β (f x) → β (f x) ∈ K)
    (hzero : ∀ x : M, x ∈ U → θ (f x) = 0)
    (hfar : ∀ x : M, x ∈ U → β (f x) ∉ K → ∀ y : M, y ∉ U → y ∉ V →
      β (f y) = β (f x) → θ (f y) ∈ Submodule.span ℝ {e} → inner ℝ (θ (f y)) e ≤ 0) :
    ∀ x : M, x ∈ U → ∀ y : M, β (f y) = β (f x) → β (f x) ∉ K →
      θ (f y) - θ (f x) ∈ Submodule.span ℝ {e} →
      inner ℝ (θ (f y) - θ (f x)) e ≤ 0 := by
  intro x hx y hbase hK hspan
  by_cases hyU : y ∈ U
  · simp [hzero y hyU, hzero x hx]
  · by_cases hyV : y ∈ V
    · exact absurd (hlens x hx y hyV hbase) hK
    · rw [hzero x hx, sub_zero] at hspan ⊢
      exact hfar x hx hK y hyU hyV hbase hspan

/-- **The confinement off `K` from the zero section and the sign on the outside partners.**
In the tube coordinates, (iii) follows from the sign hypothesis on the partners *outside* the collar
alone: partners inside the collar have height difference `0` because the collar is the zero section.

This is route (B): **it makes the lens separation (2.a) unnecessary**, leaving as the collar-geometry
input only the tube trivialisation (zero section) — no projected-image separation — and handing all
the outside partners (partner collar included) to the sign brick (3). -/
theorem confinement_of_zero_section_and_sign {n : ℕ} {M : Type*}
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (β θ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin n))
    (U : Set M) (e : EuclideanSpace ℝ (Fin n)) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hzero : ∀ x : M, x ∈ U → θ (f x) = 0)
    (hsign : ∀ x : M, x ∈ U → β (f x) ∉ K → ∀ y : M, y ∉ U → β (f y) = β (f x) →
      θ (f y) ∈ Submodule.span ℝ {e} → inner ℝ (θ (f y)) e ≤ 0) :
    ∀ x : M, x ∈ U → ∀ y : M, β (f y) = β (f x) → β (f x) ∉ K →
      θ (f y) - θ (f x) ∈ Submodule.span ℝ {e} →
      inner ℝ (θ (f y) - θ (f x)) e ≤ 0 := by
  intro x hx y hbase hK hspan
  by_cases hyU : y ∈ U
  · simp [hzero y hyU, hzero x hx]
  · rw [hzero x hx, sub_zero] at hspan ⊢
    exact hsign x hx hK y hyU hbase hspan

end Work.Whitney
