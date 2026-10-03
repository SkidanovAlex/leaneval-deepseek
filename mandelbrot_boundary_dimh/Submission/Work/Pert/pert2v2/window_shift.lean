import Mathlib

/-!
# `Work.Pert.pert2v2.window_shift` — shifting a `DE`-point into a `Re`-window

`DR_sub` for the two-piece return map needs, for every `w ∈ K ∪ {y₁ ≤ |Im|}`, an integer translate
of `w` lying in the low chart `Ulow`.  The low chart must sit inside the datum's horn domain
`d.DE` (the crux is applied to a compact `Kb ⊆ d.DE`; nothing is known about `DE` below height
`η₀`, so `Ulow` cannot be a pure geometric window — see `NOTES_pert2v2_session26.md` §5).

The two ingredients are therefore:

* `d.DE` is closed under `w ↦ w + 1` (`Work.Pert.pert2v2.DE_add_one`), so *right* translates of a
  band/`K`-point stay in `DE`;
* the window `{|Re - x₀| < R1}` with `R1 > 1/2` meets every right half-line
  `{Re w + m : m ∈ ℕ}` of points with `Re w < x₀ + R1`.

This file proves the second (the arithmetic), parametrised by the closure property so that it can be
stated before `DE_add_one` lands.
-/

namespace Work.Pert.pert2v2

open Set

/-- **Shift a point of `DE` into the window `{|Re - x₀| < R1}` by a nonnegative integer.**  Requires
`DE` to be closed under `+1` (the forward half of the `T`-invariance, `Work.Pert.pert2v2.DE_add_one`)
and `1 / 2 < R1` (which makes the window wide enough that successive right shifts cannot jump over
it).  The imaginary part is untouched by a real shift, so the height hypothesis is inherited. -/
theorem exists_shift_mem_window {DE : Set ℂ} {x₀ R1 Hband : ℝ}
    (hDE : ∀ w : ℂ, w ∈ DE → w + 1 ∈ DE) (hR1 : 1 / 2 < R1)
    {w : ℂ} (hw : w ∈ DE) (him : |w.im| < Hband) (hre : w.re < x₀ + R1) :
    ∃ m : ℕ, w + (m : ℂ) ∈ DE ∧ |(w + (m : ℂ)).re - x₀| < R1 ∧ |(w + (m : ℂ)).im| < Hband := by
  classical
  -- the least `m` with `x₀ - R1 < w.re + m`
  have hex : ∃ m : ℕ, x₀ - R1 < w.re + (m : ℝ) := by
    obtain ⟨m, hm⟩ := exists_nat_gt (x₀ - R1 - w.re)
    exact ⟨m, by linarith⟩
  let m : ℕ := Nat.find hex
  have hm : x₀ - R1 < w.re + (m : ℝ) := Nat.find_spec hex
  have hmin : ∀ k : ℕ, k < m → ¬ (x₀ - R1 < w.re + (k : ℝ)) := fun k hk => Nat.find_min hex hk
  have hrew : (w + (m : ℂ)).re = w.re + (m : ℝ) := by simp
  have himw : (w + (m : ℂ)).im = w.im := by simp
  refine ⟨m, ?_, ?_, ?_⟩
  · -- `w + m ∈ DE`, by induction from `hw` using the `+1`-closure
    have hiter : ∀ k : ℕ, w + (k : ℂ) ∈ DE := by
      intro k
      induction k with
      | zero => simpa using hw
      | succ j ih =>
        have h1 : w + ((j + 1 : ℕ) : ℂ) = (w + (j : ℂ)) + 1 := by push_cast; ring
        rw [h1]; exact hDE _ ih
    exact hiter m
  · -- the real part: open the window at both ends
    have hlow : x₀ - R1 < (w + (m : ℂ)).re := by rw [hrew]; exact hm
    have hhigh : (w + (m : ℂ)).re < x₀ + R1 := by
      rw [hrew]
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · rw [hm0]
        push_cast
        linarith only [hre]
      · have hlt : m - 1 < m := Nat.sub_lt hmpos (by norm_num)
        have hnot : ¬ (x₀ - R1 < w.re + ((m - 1 : ℕ) : ℝ)) := hmin (m - 1) hlt
        have hle : w.re + ((m - 1 : ℕ) : ℝ) ≤ x₀ - R1 := not_lt.mp hnot
        have hcast : ((m : ℕ) : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by
          have h2 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
            rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hmpos)),
              Nat.cast_one]
          rw [h2]; ring
        rw [hcast]
        linarith only [hle, hR1]
    rw [abs_lt]
    exact ⟨by linarith only [hlow], by linarith only [hhigh]⟩
  · -- the imaginary part is unchanged
    rw [himw]; exact him

/-- **The `DR_sub` (low band) coverage step, wired to the glue.**  If the low chart contains the
window `{|Re - x₀| < R1} ∩ {|Im| < Hband}` inside `DE`, then every `DE`-point of that height with
`w.re < x₀ + R1` lies in the `ℤ`-saturation of the low chart — which is the conclusion the
`DR_sub` row needs, with `Ulow` the union of the two charts. -/
theorem mem_saturation_of_shift {DE Ulow : Set ℂ} {x₀ R1 Hband : ℝ}
    (hUlow : ∀ w : ℂ, w ∈ DE → |w.re - x₀| < R1 → |w.im| < Hband → w ∈ Ulow)
    (hDE : ∀ w : ℂ, w ∈ DE → w + 1 ∈ DE) (hR1 : 1 / 2 < R1)
    {w : ℂ} (hw : w ∈ DE) (him : |w.im| < Hband) (hre : w.re < x₀ + R1) :
    w ∈ ⋃ n : ℤ, (fun u => u + (n : ℂ)) '' Ulow := by
  obtain ⟨m, hmDE, hmre, hmim⟩ := exists_shift_mem_window hDE hR1 hw him hre
  refine Set.mem_iUnion.mpr ⟨-(m : ℤ), ?_⟩
  simp only [Set.mem_image]
  exact ⟨w + (m : ℂ), hUlow _ hmDE hmre hmim, by push_cast; ring⟩

end Work.Pert.pert2v2
