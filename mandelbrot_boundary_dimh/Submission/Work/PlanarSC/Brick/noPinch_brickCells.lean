import Mathlib
import Submission.Work.HornSC.Cells

namespace Work.PlanarSC.Brick

/-- The "brick wall" doubling of a polyomino: the cell `(a, y)` of `A` is replaced by the two
horizontally adjacent cells `(2 a + y % 2, y)` and `(2 a + y % 2 + 1, y)`. The alternating offset
`y % 2` staggers successive rows, so that the resulting polyomino has no pinch points. -/
abbrev brickCells (A : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  A.biUnion fun p : ℤ × ℤ =>
    ({(2 * p.1 + p.2 % 2, p.2), (2 * p.1 + p.2 % 2 + 1, p.2)} : Finset (ℤ × ℤ))

/-- Membership in the brick-wall doubling: `(x, y)` is present iff it is one of the two cells
produced by some cell `(a, y)` of `A`. -/
lemma mem_brickCells {A : Finset (ℤ × ℤ)} {x y : ℤ} :
    (x, y) ∈ brickCells A ↔
      ∃ a : ℤ, (a, y) ∈ A ∧ (x = 2 * a + y % 2 ∨ x = 2 * a + y % 2 + 1) := by
  rw [brickCells]
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨p, hp, ⟨hx, hy⟩ | ⟨hx, hy⟩⟩
    · subst hy
      exact ⟨p.1, by simpa using hp, Or.inl hx⟩
    · subst hy
      exact ⟨p.1, by simpa using hp, Or.inr hx⟩
  · rintro ⟨a, ha, hx | hx⟩
    · exact ⟨(a, y), ha, Or.inl (by simp [hx])⟩
    · exact ⟨(a, y), ha, Or.inr (by simp [hx])⟩

/-- If the cell `(x-1, y)` is present but `(x, y)` is not, then `x - (y % 2)` is even: the two
horizontally adjacent positions of a row come in pairs `{2a + y%2, 2a + y%2 + 1}`, so a present
left cell with absent right cell forces `x` to sit one past the right end of a pair. -/
lemma even_sub_of_mem_pred_notMem {A : Finset (ℤ × ℤ)} {x y : ℤ}
    (hm : (x - 1, y) ∈ brickCells A) (hn : (x, y) ∉ brickCells A) :
    ∃ k : ℤ, x - y % 2 = 2 * k := by
  rw [mem_brickCells] at hm
  obtain ⟨a, ha, hx | hx⟩ := hm
  · exfalso
    apply hn
    rw [mem_brickCells]
    exact ⟨a, ha, Or.inr (by omega)⟩
  · exact ⟨a + 1, by omega⟩

/-- Symmetric version: if the cell `(x, y)` is present but `(x-1, y)` is not, then `x - (y % 2)`
is even. -/
lemma even_sub_of_mem_notMem_pred {A : Finset (ℤ × ℤ)} {x y : ℤ}
    (hm : (x, y) ∈ brickCells A) (hn : (x - 1, y) ∉ brickCells A) :
    ∃ k : ℤ, x - y % 2 = 2 * k := by
  rw [mem_brickCells] at hm
  obtain ⟨a, ha, hx | hx⟩ := hm
  · exact ⟨a, by omega⟩
  · exfalso
    apply hn
    rw [mem_brickCells]
    exact ⟨a, ha, Or.inl (by omega)⟩

theorem noPinch_brickCells (A : Finset (ℤ × ℤ)) :
    Work.HornSC.NoPinch
      (A.biUnion fun p : ℤ × ℤ =>
        ({(2 * p.1 + p.2 % 2, p.2), (2 * p.1 + p.2 % 2 + 1, p.2)} : Finset (ℤ × ℤ))) := by
  change Work.HornSC.NoPinch (brickCells A)
  simp only [Work.HornSC.NoPinch, Work.HornSC.noPinchAt]
  intro v
  rintro (⟨h00, h11, hn10, hn01⟩ | ⟨h01, h10, hn11, hn00⟩)
  · obtain ⟨k₀, hk₀⟩ := even_sub_of_mem_pred_notMem (x := v.1) (y := v.2 - 1) h00 hn10
    obtain ⟨k₁, hk₁⟩ := even_sub_of_mem_notMem_pred (x := v.1) (y := v.2) h11 hn01
    have hs : (v.2 - 1) % 2 + v.2 % 2 = 1 := by omega
    omega
  · obtain ⟨k₀, hk₀⟩ := even_sub_of_mem_notMem_pred (x := v.1) (y := v.2 - 1) h10 hn00
    obtain ⟨k₁, hk₁⟩ := even_sub_of_mem_pred_notMem (x := v.1) (y := v.2) h01 hn11
    have hs : (v.2 - 1) % 2 + v.2 % 2 = 1 := by omega
    omega

end Work.PlanarSC.Brick
