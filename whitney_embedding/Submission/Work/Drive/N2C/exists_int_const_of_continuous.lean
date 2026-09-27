import Mathlib

/-!
# A continuous function on `ℝ` with values in `2πℤ` is constant

If `s : ℝ → ℝ` is continuous and every value `s x` is an integral multiple of `2π`, then `s` is
constant: `∃ n : ℤ, ∀ x, s x = 2 * π * n`.

This is the discreteness of `2πℤ` inside `ℝ` together with the connectedness of `ℝ`.  The proof
shows that for `n` with `s 0 = 2πn` the set `s ⁻¹' {2πn}` is clopen (`closed` by continuity and
`open` because the interval `(2πn - 1, 2πn + 1)` contains no other multiple of `2π`), hence all of
`ℝ` by preconnectedness (`IsPreconnected.subset_isClopen`).

The two ingredients are packaged as `eq_of_mem_Ioo_two_pi` (the only multiple of `2π` in the unit
interval about `2πn` is `2πn` itself) and `int_eq_zero_of_abs_cast_lt_one` (an integer of absolute
value `< 1` is `0`).
-/

open scoped Topology

namespace Work.Drive.N2C

/-- A rational/integer whose real absolute value is `< 1` is `0`. -/
lemma int_eq_zero_of_abs_cast_lt_one {k : ℤ} (h : |((k : ℝ))| < 1) : k = 0 := by
  have h' := abs_lt.mp h
  have h1 : (-1 : ℤ) < k := by exact_mod_cast h'.1
  have h2 : k < (1 : ℤ) := by exact_mod_cast h'.2
  omega

/-- **Discreteness of `2πℤ`.**  If `2πm` lies in the open unit interval about `2πn`, then `m = n`.
Equivalently: `2π` is larger than `1`, so two distinct multiples of `2π` are at distance at least
`2π > 1`. -/
lemma eq_of_mem_Ioo_two_pi {m n : ℤ}
    (hlo : 2 * Real.pi * (n : ℝ) - 1 < 2 * Real.pi * (m : ℝ))
    (hhi : 2 * Real.pi * (m : ℝ) < 2 * Real.pi * (n : ℝ) + 1) : m = n := by
  have hdiff : 2 * Real.pi * ((m - n : ℤ) : ℝ) =
      2 * Real.pi * (m : ℝ) - 2 * Real.pi * (n : ℝ) := by
    push_cast; ring
  have hlt : |2 * Real.pi * ((m - n : ℤ) : ℝ)| < 1 := by
    rw [abs_lt, hdiff]
    constructor <;> linarith
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hgt1 : (1 : ℝ) < 2 * Real.pi := by have := Real.pi_gt_three; linarith
  have h6 : |((m - n : ℤ) : ℝ)| < 1 := by
    have hmul : 2 * Real.pi * |((m - n : ℤ) : ℝ)| = |2 * Real.pi * ((m - n : ℤ) : ℝ)| := by
      rw [abs_mul, abs_of_pos hpi]
    by_contra hcon
    rw [not_lt] at hcon
    have hle : 2 * Real.pi * 1 ≤ 2 * Real.pi * |((m - n : ℤ) : ℝ)| :=
      mul_le_mul_of_nonneg_left hcon (le_of_lt hpi)
    rw [hmul] at hle
    linarith
  have hzero : m - n = 0 := int_eq_zero_of_abs_cast_lt_one h6
  omega

theorem exists_int_const_of_continuous {s : ℝ → ℝ} (hs : Continuous s) (h : ∀ x, ∃ n : ℤ, s x = 2 * Real.pi * n) : ∃ n : ℤ, ∀ x, s x = 2 * Real.pi * n := by
  obtain ⟨n, hn⟩ := h 0
  refine ⟨n, fun x => ?_⟩
  -- the fibre of `s` over `2πn` is open
  have hopen : IsOpen (s ⁻¹' {2 * Real.pi * (n : ℝ)}) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hmem : Set.Ioo (s x - 1) (s x + 1) ∈ 𝓝 (s x) :=
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    refine Filter.mem_of_superset (hs.continuousAt.preimage_mem_nhds hmem) ?_
    intro y hy
    simp only [Set.mem_preimage, Set.mem_Ioo] at hy
    obtain ⟨m, hm⟩ := h y
    rw [hm, hx] at hy
    have hmn : m = n := eq_of_mem_Ioo_two_pi hy.1 hy.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [hm, hmn]
  have hcl : IsClosed (s ⁻¹' {2 * Real.pi * (n : ℝ)}) := isClosed_singleton.preimage hs
  -- a nonempty clopen set in the preconnected space `ℝ` is everything
  have hsub : Set.univ ⊆ s ⁻¹' {2 * Real.pi * (n : ℝ)} :=
    isPreconnected_univ.subset_isClopen (⟨hcl, hopen⟩ : IsClopen _) ⟨0, Set.mem_univ 0, hn⟩
  exact hsub (Set.mem_univ x)

end Work.Drive.N2C
