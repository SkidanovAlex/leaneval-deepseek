import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.CellFibreInterval

namespace Work.WilG4c

/-- **The fibre of a cell between its two ends.**

Let `κ ⊆ ℝ^{m+1}` be a `IsCell` all of whose values in the last coordinate lie in `(0,1)`, and
let `lo`, `hi : ℝ^m → ℝ` be functions whose graphs are the pointwise infimum resp. supremum of
the fibre `κ_l = {x | Fin.snoc l x ∈ κ}`: for every `l` with non-empty fibre, every element of
the fibre lies in `[lo l, hi l]`, and both ends are sharp (`∀ u > lo l` some fibre element is
`< u`, and `∀ u < hi l` some fibre element is `> u`).

Then, for every such `l`, both ends lie in `[0,1]`, their midpoint in `(0,1)`, their difference
in `[0,1]`, and — using order-convexity of the fibre — the fibre is *exactly* the interval
between the ends: it contains every point strictly between them, and in particular every affine
combination `lo l + t·(hi l - lo l)` with `t ∈ (0,1)`. -/
theorem FibreEndsInterval {m : ℕ} (κ : Set (Fin (m + 1) → ℝ))
    (hcell : WilkiesDesign.IsCell (m + 1) κ)
    (hI : ∀ z ∈ κ, z (Fin.last m) ∈ Set.Ioo (0 : ℝ) 1)
    (lo hi : (Fin m → ℝ) → ℝ)
    (hlo : ∀ l : Fin m → ℝ, (∃ x : ℝ, Fin.snoc l x ∈ κ) →
      (∀ x : ℝ, Fin.snoc l x ∈ κ → lo l ≤ x ∧ x ≤ hi l) ∧
      (∀ u : ℝ, lo l < u → ∃ x : ℝ, Fin.snoc l x ∈ κ ∧ x < u) ∧
      (∀ u : ℝ, u < hi l → ∃ x : ℝ, Fin.snoc l x ∈ κ ∧ u < x)) :
    ∀ l : Fin m → ℝ, (∃ x : ℝ, Fin.snoc l x ∈ κ) →
      0 ≤ lo l ∧ lo l ≤ 1 ∧ 0 ≤ hi l ∧ hi l ≤ 1 ∧
      0 < (lo l + hi l) / 2 ∧ (lo l + hi l) / 2 < 1 ∧
      0 ≤ hi l - lo l ∧ hi l - lo l ≤ 1 ∧
      (∀ x : ℝ, lo l < x → x < hi l → Fin.snoc l x ∈ κ) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, Fin.snoc l (lo l + t * (hi l - lo l)) ∈ κ) := by
  intro l hl
  -- the three defining properties of the two ends
  obtain ⟨hbnd, hlow, hhigh⟩ := hlo l hl
  -- a point of the fibre, whose fibre coordinate lies in `(0,1)`
  obtain ⟨x0, hx0κ⟩ := hl
  have hx0I : x0 ∈ Set.Ioo (0 : ℝ) 1 := by
    have h := hI (Fin.snoc l x0) hx0κ
    rwa [Fin.snoc_last] at h
  obtain ⟨hx0pos, hx0lt⟩ := hx0I
  obtain ⟨hlox0, hx0hi⟩ := hbnd x0 hx0κ
  -- the fibre is order-convex
  have hord := ordConnected_fibre_of_isCell hcell l
  -- `0 ≤ lo l`: a fibre point below `0` would contradict `hI`
  have hlo0 : 0 ≤ lo l := by
    by_contra h
    push Not at h
    obtain ⟨x, hxκ, hxu⟩ := hlow 0 h
    have hxI : x ∈ Set.Ioo (0 : ℝ) 1 := by
      have h2 := hI (Fin.snoc l x) hxκ
      rwa [Fin.snoc_last] at h2
    linarith [hxI.1]
  have hlo1 : lo l ≤ 1 := le_of_lt (lt_of_le_of_lt hlox0 hx0lt)
  have hhi0 : 0 ≤ hi l := le_of_lt (lt_of_lt_of_le hx0pos hx0hi)
  -- `hi l ≤ 1`: a fibre point above `1` would contradict `hI`
  have hhi1 : hi l ≤ 1 := by
    by_contra h
    push Not at h
    obtain ⟨x, hxκ, hxu⟩ := hhigh 1 h
    have hxI : x ∈ Set.Ioo (0 : ℝ) 1 := by
      have h2 := hI (Fin.snoc l x) hxκ
      rwa [Fin.snoc_last] at h2
    linarith [hxI.2]
  have hmid0 : 0 < (lo l + hi l) / 2 := by linarith
  have hmid1 : (lo l + hi l) / 2 < 1 := by linarith
  have hd0 : 0 ≤ hi l - lo l := by linarith
  have hd1 : hi l - lo l ≤ 1 := by linarith
  -- everything strictly between the ends is in the fibre, by order-convexity
  have hmid : ∀ x : ℝ, lo l < x → x < hi l → Fin.snoc l x ∈ κ := by
    intro x h1 h2
    obtain ⟨a, haκ, hax⟩ := hlow x h1
    obtain ⟨b, hbκ, hxb⟩ := hhigh x h2
    exact hord.out haκ hbκ ⟨le_of_lt hax, le_of_lt hxb⟩
  refine ⟨hlo0, hlo1, hhi0, hhi1, hmid0, hmid1, hd0, hd1, hmid, ?_⟩
  -- the affine combinations: degenerate fibre (a point) or strict interior
  intro t ht
  obtain ⟨ht0, ht1⟩ := ht
  by_cases hd : hi l - lo l = 0
  · have hx : lo l + t * (hi l - lo l) = lo l := by rw [hd]; ring
    rw [hx]
    have hx0eq : x0 = lo l := by linarith
    simpa [hx0eq] using hx0κ
  · have hdpos : 0 < hi l - lo l := lt_of_le_of_ne hd0 (Ne.symm hd)
    have hgt : lo l < lo l + t * (hi l - lo l) := by
      have : 0 < t * (hi l - lo l) := mul_pos ht0 hdpos
      linarith
    have hlt : lo l + t * (hi l - lo l) < hi l := by
      have h3 : t * (hi l - lo l) < 1 * (hi l - lo l) :=
        mul_lt_mul_of_pos_right ht1 hdpos
      linarith
    exact hmid _ hgt hlt

end Work.WilG4c
