import Mathlib

/-!
# The "brick wall" tiling of the plane

Vocabulary for the planar lemma `Work.PlanarSC.exists_jordan_curve_of_gap`.

`bcell h (i,j)` is the closed rectangle `[h(2i+e), h(2i+e+2)] × [hj, h(j+1)]` where
`e = j % 2 ∈ {0,1}`: the bricks of a brick wall of mesh `h > 0`.  These bricks tile `ℂ` and
**every vertex of the tiling is incident with exactly three bricks**, which is what makes the
frontier of a finite union of bricks a union of pairwise disjoint simple closed polygonal curves
(no "pinch" points): the frontier is locally an arc at each of its points.
-/

namespace Work.PlanarSC.Brick

open Set

/-- The brick of the brick-wall tiling of `ℂ` of mesh `h > 0` at index `p = (i,j)`:
the closed rectangle `[h(2i + e), h(2i + e + 2)] × [h j, h (j+1)]` with `e = j % 2`. -/
def bcell (h : ℝ) (p : ℤ × ℤ) : Set ℂ :=
  {z | ((2 * p.1 + p.2 % 2 : ℤ) : ℝ) * h ≤ z.re ∧
        z.re ≤ ((2 * p.1 + p.2 % 2 + 2 : ℤ) : ℝ) * h ∧
        (p.2 : ℝ) * h ≤ z.im ∧ z.im ≤ ((p.2 : ℝ) + 1) * h}

/-- The union of the bricks indexed by a finite set `A`. -/
def bUnion (h : ℝ) (A : Finset (ℤ × ℤ)) : Set ℂ := ⋃ p ∈ A, bcell h p

@[simp] theorem mem_bcell {h : ℝ} {p : ℤ × ℤ} {z : ℂ} :
    z ∈ bcell h p ↔ ((2 * p.1 + p.2 % 2 : ℤ) : ℝ) * h ≤ z.re ∧
        z.re ≤ ((2 * p.1 + p.2 % 2 + 2 : ℤ) : ℝ) * h ∧
        (p.2 : ℝ) * h ≤ z.im ∧ z.im ≤ ((p.2 : ℝ) + 1) * h := Iff.rfl

@[simp] theorem mem_bUnion {h : ℝ} {A : Finset (ℤ × ℤ)} {z : ℂ} :
    z ∈ bUnion h A ↔ ∃ p ∈ A, z ∈ bcell h p := by
  simp only [bUnion, Set.mem_iUnion, exists_prop, mem_bcell]

theorem isClosed_bcell (h : ℝ) (p : ℤ × ℤ) : IsClosed (bcell h p) := by
  have h1 : IsClosed {z : ℂ | ((2 * p.1 + p.2 % 2 : ℤ) : ℝ) * h ≤ z.re} :=
    isClosed_le continuous_const Complex.continuous_re
  have h2 : IsClosed {z : ℂ | z.re ≤ ((2 * p.1 + p.2 % 2 + 2 : ℤ) : ℝ) * h} :=
    isClosed_le Complex.continuous_re continuous_const
  have h3 : IsClosed {z : ℂ | (p.2 : ℝ) * h ≤ z.im} :=
    isClosed_le continuous_const Complex.continuous_im
  have h4 : IsClosed {z : ℂ | z.im ≤ ((p.2 : ℝ) + 1) * h} :=
    isClosed_le Complex.continuous_im continuous_const
  have hset : bcell h p =
      {z : ℂ | ((2 * p.1 + p.2 % 2 : ℤ) : ℝ) * h ≤ z.re} ∩
      ({z : ℂ | z.re ≤ ((2 * p.1 + p.2 % 2 + 2 : ℤ) : ℝ) * h} ∩
      ({z : ℂ | (p.2 : ℝ) * h ≤ z.im} ∩ {z : ℂ | z.im ≤ ((p.2 : ℝ) + 1) * h})) := by
    ext z
    simp only [bcell, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [hset]
  exact h1.inter (h2.inter (h3.inter h4))

theorem bcell_subset_bUnion {h : ℝ} {A : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hp : p ∈ A) :
    bcell h p ⊆ bUnion h A := fun z hz => mem_bUnion.mpr ⟨p, hp, hz⟩

theorem bUnion_mono {h : ℝ} {A B : Finset (ℤ × ℤ)} (hAB : A ⊆ B) : bUnion h A ⊆ bUnion h B := by
  intro z hz
  obtain ⟨p, hp, hzp⟩ := mem_bUnion.mp hz
  exact mem_bUnion.mpr ⟨p, hAB hp, hzp⟩

end Work.PlanarSC.Brick
