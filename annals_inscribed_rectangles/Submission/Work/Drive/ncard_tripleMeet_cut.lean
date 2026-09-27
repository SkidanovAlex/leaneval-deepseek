import Mathlib

/-!
# The triple-parameter count and the cut-intersection count

In the chain route the count `n_P` of Hugelmeyer's Lemmas 3-4 is a count of *parameter triples*: the
tuples `(x, y, z)` at which the plane `P` (parametrised by `x`), the sweep `V_Q` (parametrised by `y`)
and the sweep `V_R` (parametrised by `z`) meet in one point of the capping space.  The paper's
multilinearity of the intersection pairing then identifies it with the mod-2 intersection number
`⟨[A_Q], [A_R]⟩` of the two *cut* `1`-cycles `A_Q = P ∩ V_Q`, `A_R = P ∩ V_R` inside the surface `P`.

The passage from the parameter triples to the cut intersections is pure bookkeeping, and this file
isolates it.  Writing `X` for the parameter space of the plane, `A ⊆ X × Y` for the pairs of plane and
sweep parameters that give the same point of the ambient space (the cut `A_Q`), and `B ⊆ X × Z` for
the analogous pairs of `A_R`, the parameter triples are

* `tripleCart A B = {(x,y,z) | (x,y) ∈ A ∧ (x,z) ∈ B}`, and the points of the plane carrying both
  cuts are
* `cutBase A B = {x | (∃ y, (x,y) ∈ A) ∧ (∃ z, (x,z) ∈ B)}`.

`Work.Drive.ncard_tripleCart_eq_ncard_cutBase` says that when the two *cuts are transverse* — which is
the generic case for the sweep construction, and the condition that makes the cut a smooth embedded
`1`-cycle parametrised once — the two counts are equal, not merely congruent (`Set.ncard_prod`,
`Set.InjOn.ncard_image`).

The general case (a cut hit with odd multiplicity, which is what the radial sweep produces: the ray
from the axis through a point meets a plane in an odd number of points) is the theorem
`Work.Drive.even_ncard_tripleCart_add_ncard_cutBase_of_odd_fibres`, delegated separately: the same
bijection argument gives `#(tripleCart) = Σ_x #(fibre_A x)·#(fibre_B x)` over the base, so
`#(tripleCart) ≡ #(cutBase)` as soon as every fibre product is odd.
-/

namespace Work.Drive

variable {X Y Z : Type*}

/-- **The parameter triples of the two cuts.**  `(x,y,z) ∈ tripleCart A B` says that the plane's
parameter `x` and the first sweep's parameter `y` give the same point (`(x,y) ∈ A`), and that the
plane's parameter `x` and the second sweep's parameter `z` give the same point (`(x,z) ∈ B`). -/
def tripleCart (A : Set (X × Y)) (B : Set (X × Z)) : Set (X × Y × Z) :=
  {p | (p.1, p.2.1) ∈ A ∧ (p.1, p.2.2) ∈ B}

/-- **The points of the plane that both cuts meet**: the base set over which both `A` and `B` have a
fibre.  It is the intersection of the two cut cycles, transported to the plane's parameter space. -/
def cutBase (A : Set (X × Y)) (B : Set (X × Z)) : Set X :=
  {x | (∃ y, (x, y) ∈ A) ∧ (∃ z, (x, z) ∈ B)}

/-- The `A`-fibre over a point of the base: the sweep parameters that produce the plane point `x`. -/
def fibreA (A : Set (X × Y)) (x : X) : Set Y := {y | (x, y) ∈ A}

/-- The `B`-fibre over a point of the base. -/
def fibreB (B : Set (X × Z)) (x : X) : Set Z := {z | (x, z) ∈ B}

/-- **The parameter triples project onto the cut intersection.** -/
theorem fst_image_tripleCart (A : Set (X × Y)) (B : Set (X × Z)) :
    Prod.fst '' tripleCart A B = cutBase A B := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p.2.1, hp.1⟩, ⟨p.2.2, hp.2⟩⟩
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    exact ⟨(x, y, z), ⟨hy, hz⟩, rfl⟩

/-- **The triple-parameter count is the cut-intersection count when the cuts are transverse.**  If
each fibre of `A` and of `B` over the base is a *singleton* (the transversality of the cut: the sweep
parametrises the cut point once), the projection `(x,y,z) ↦ x` is a bijection from the parameter
triples onto the base, so the two counts are equal. -/
theorem ncard_tripleCart_eq_ncard_cutBase (A : Set (X × Y)) (B : Set (X × Z))
    (hA : A.Finite) (hB : B.Finite)
    (hfibA : ∀ x ∈ cutBase A B, (fibreA A x).ncard = 1)
    (hfibB : ∀ x ∈ cutBase A B, (fibreB B x).ncard = 1) :
    (tripleCart A B).ncard = (cutBase A B).ncard := by
  have hinj : Set.InjOn Prod.fst (tripleCart A B) := by
    intro p hp q hq hpq
    have hpbase : p.1 ∈ cutBase A B := ⟨⟨p.2.1, hp.1⟩, ⟨p.2.2, hp.2⟩⟩
    have hq1 : q.1 = p.1 := hpq.symm
    have hy : p.2.1 = q.2.1 := by
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp (hfibA p.1 hpbase)
      have h1 : p.2.1 ∈ fibreA A p.1 := hp.1
      have h2 : q.2.1 ∈ fibreA A p.1 := by
        have hq' : (q.1, q.2.1) ∈ A := hq.1
        rwa [hq1] at hq'
      rw [ha] at h1 h2
      simp only [Set.mem_singleton_iff] at h1 h2
      exact h1.trans h2.symm
    have hz : p.2.2 = q.2.2 := by
      obtain ⟨b, hb⟩ := Set.ncard_eq_one.mp (hfibB p.1 hpbase)
      have h1 : p.2.2 ∈ fibreB B p.1 := hp.2
      have h2 : q.2.2 ∈ fibreB B p.1 := by
        have hq' : (q.1, q.2.2) ∈ B := hq.2
        rwa [hq1] at hq'
      rw [hb] at h1 h2
      simp only [Set.mem_singleton_iff] at h1 h2
      exact h1.trans h2.symm
    rw [show p = (p.1, p.2.1, p.2.2) from rfl, show q = (q.1, q.2.1, q.2.2) from rfl,
      hpq, hy, hz]
  rw [← fst_image_tripleCart A B, hinj.ncard_image]

end Work.Drive
