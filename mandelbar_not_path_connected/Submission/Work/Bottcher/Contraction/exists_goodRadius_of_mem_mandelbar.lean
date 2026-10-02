/-
# A good escape radius for the tricorn dynamics

For `c` in the mandelbar `M*` we produce a radius `R ≥ 2`, `R ≥ escapeRadius c = 2(1 + ‖c‖)`,
with the following four properties of the holomorphic second iterate
`p_c = pMap c = T_c ∘ T_c` of the tricorn map `T_c(w) = w̄² + c`:

1. **Expansion.** `R ≤ ‖z‖ ⟹ R ≤ ‖p_c z‖`;
2. **Escape.** `R ≤ ‖z‖ ⟹ z ∈ EscapeSet c` (i.e. `G_c(z) > 0`);
3. **All escaping points reach the far region.** for `z ∈ EscapeSet c` there is `n` with
   `R ≤ ‖p_c^n z‖`;
4. **The critical region is inside the disk of radius `R`.** if `p_c r = 0` then the whole
   segment `[0, r]` is mapped by `p_c` into `{‖w‖ ≤ R}`.

The first three items hold with any `R ≥ escapeRadius c` (item 1 is the elementary far-field
step `‖T_c w‖ ≥ ‖w‖` for `‖w‖ ≥ 2(1 + ‖c‖)`, item 2 is `green_pos_of_mem_escapeRegion`, item 3
is `green_pos_iff` together with the fact that the `p_c`-orbit is the even subsequence of the
`T_c`-orbit).  Item 4 is the only one involving the mandelbar hypothesis: the critical points
of `p_c` are the preimages of `0`, i.e. `r² = ±√(-c) - c̄`, so `‖r‖² ≤ 1 + 2‖c‖` and
`‖p_c(t r)‖ ≤ (1 + 3‖c‖)² + ‖c‖` for `t ∈ [0,1]`.  Taking `R` to be the maximum of this explicit
constant and `escapeRadius c + 1` satisfies all four requirements at once.

The strict margin `escapeRadius c + 1` is only there to put `R` strictly inside the escaping
region `escapeRegion ‖c‖` of `Work.Escape`, so that item 2 can be quoted directly.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Green.green_pos_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped ComplexConjugate

namespace Work.Bottcher.Contraction

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Far-field step for `T_c`.**  Beyond the escape radius `2 (1 + ‖c‖)` the tricorn map does not
decrease the modulus: `‖z‖ ≤ ‖T_c z‖` whenever `escapeRadius c ≤ ‖z‖`.

Indeed `‖T_c z‖ ≥ ‖z‖² - ‖c‖` and `‖z‖ ≥ 2 (1 + ‖c‖)` gives `‖z‖ + ‖c‖ ≤ ‖z‖²`, since
`‖z‖² - ‖z‖ - ‖c‖ ≥ ‖z‖² - 3‖z‖/2 + 1 = (‖z‖ - 3/4)² + 7/16 > 0`. -/
theorem le_norm_Tantibar_of_escapeRadius_le (c z : ℂ) (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) :
    ‖z‖ ≤ ‖Tantibar c z‖ := by
  have hb : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have h1 : ‖z‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c z‖ := by
    have h := Work.Escape.norm_Td_ge 2 c z
    rwa [Work.Escape.Td_two_eq] at h
  have hr : 2 * (1 + ‖c‖) ≤ ‖z‖ := by simpa [Work.Bottcher.escapeRadius] using hz
  have key : ‖z‖ ≤ ‖z‖ ^ 2 - ‖c‖ := by nlinarith [sq_nonneg (2 * ‖z‖ - 3 / 2), hb, hr]
  linarith

/-- **Far-field step for the quartic `p_c`.**  Beyond the escape radius, applying `p_c` does not
decrease the modulus either: `‖z‖ ≤ ‖p_c z‖` for `escapeRadius c ≤ ‖z‖`.  Apply the `T_c` step
twice, using that `T_c ∘ T_c = p_c`. -/
theorem le_norm_pMap_of_escapeRadius_le (c z : ℂ) (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) :
    ‖z‖ ≤ ‖Work.Bottcher.pMap c z‖ := by
  have h1 := le_norm_Tantibar_of_escapeRadius_le c z hz
  have h2 := le_norm_Tantibar_of_escapeRadius_le c (Tantibar c z) (hz.trans h1)
  have heq : Tantibar c (Tantibar c z) = Work.Bottcher.pMap c z := by
    simp [LeanEval.ComplexAnalysis.Tantibar, Work.Bottcher.pMap_apply, map_add, map_pow]
  rw [heq] at h2
  linarith

/-- The escaping region `{w | max 2 ‖c‖ < ‖w‖}` of `Work.Escape` lies strictly below
`escapeRadius c + 1`: this is what makes the radius `R ≥ escapeRadius c + 1` usable as a
*strict* escape radius. -/
theorem max_two_norm_lt_escapeRadius_add_one (c : ℂ) :
    max 2 ‖c‖ < Work.Bottcher.escapeRadius c + 1 := by
  have hb : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  rw [Work.Bottcher.escapeRadius]
  have h : max 2 ‖c‖ ≤ 2 * ‖c‖ + 2 := max_le (by linarith) (by linarith)
  linarith

/-- **The critical region of `p_c` is bounded.**  If `p_c r = 0` and `t ∈ [0,1]`, then
`‖p_c (t r)‖ ≤ (1 + 3‖c‖)² + ‖c‖`.

Indeed `(r² + c̄)² = -c`, so `‖r² + c̄‖² = ‖c‖`, whence `‖r² + c̄‖ ≤ 1 + ‖c‖` and
`‖r‖² ≤ ‖r² + c̄‖ + ‖c‖ ≤ 1 + 2‖c‖`.  For `t ∈ [0,1]` this gives `‖(t r)² + c̄‖ ≤ 1 + 3‖c‖`,
and one more application of the triangle inequality finishes. -/
theorem norm_pMap_smul_le_of_pMap_eq_zero (c r : ℂ) (hr : Work.Bottcher.pMap c r = 0) (t : ℝ)
    (ht : t ∈ Set.Icc 0 1) :
    ‖Work.Bottcher.pMap c (t * r)‖ ≤ (1 + 3 * ‖c‖) ^ 2 + ‖c‖ := by
  have hb : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  -- `(r² + c̄)² = -c`, hence `‖r² + c̄‖² = ‖c‖`
  have hr2 : (r ^ 2 + conj c) ^ 2 = -c := by
    rw [Work.Bottcher.pMap_apply] at hr
    linear_combination hr
  have hsq : ‖r ^ 2 + conj c‖ ^ 2 = ‖c‖ := by
    have h : ‖(r ^ 2 + conj c) ^ 2‖ = ‖c‖ := by rw [hr2, norm_neg]
    rwa [norm_pow] at h
  -- `‖r‖² ≤ 1 + 2‖c‖`
  have hR : ‖r‖ ^ 2 ≤ 1 + 2 * ‖c‖ := by
    have hs : ‖r ^ 2 + conj c‖ ≤ 1 + ‖c‖ := by
      have h2 : ‖r ^ 2 + conj c‖ ^ 2 ≤ (1 + ‖c‖) ^ 2 := by nlinarith [hsq, sq_nonneg ‖c‖]
      calc ‖r ^ 2 + conj c‖ = |‖r ^ 2 + conj c‖| := (abs_of_nonneg (norm_nonneg _)).symm
        _ ≤ |1 + ‖c‖| := sq_le_sq.mp h2
        _ = 1 + ‖c‖ := abs_of_nonneg (by positivity)
    have h3 : ‖r ^ 2‖ ≤ ‖r ^ 2 + conj c‖ + ‖c‖ := by
      have h := norm_sub_le (r ^ 2 + conj c) (conj c)
      rw [Complex.norm_conj] at h
      have he : r ^ 2 + conj c - conj c = r ^ 2 := by ring
      rwa [he] at h
    rw [norm_pow] at h3
    linarith
  -- the scaled point `t * r` is no further out than `r`
  have htn : ‖(t : ℂ)‖ = t := by
    rw [show ‖(t : ℂ)‖ = |t| by simp, abs_of_nonneg ht0]
  have htr : ‖(t : ℂ) * r‖ ≤ ‖r‖ := by
    rw [norm_mul, htn]
    exact mul_le_of_le_one_left (norm_nonneg r) ht1
  have hsq2 : ‖((t : ℂ) * r) ^ 2 + conj c‖ ≤ 1 + 3 * ‖c‖ := by
    have h1 : ‖((t : ℂ) * r) ^ 2‖ ≤ ‖r‖ ^ 2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) htr 2
    have h := norm_add_le (((t : ℂ) * r) ^ 2) (conj c)
    rw [Complex.norm_conj] at h
    linarith
  have h4 : ‖Work.Bottcher.pMap c ((t : ℂ) * r)‖
      ≤ ‖((t : ℂ) * r) ^ 2 + conj c‖ ^ 2 + ‖c‖ := by
    rw [Work.Bottcher.pMap_apply]
    have h := norm_add_le ((((t : ℂ) * r) ^ 2 + conj c) ^ 2) c
    rw [norm_pow] at h
    linarith
  have h5 : ‖((t : ℂ) * r) ^ 2 + conj c‖ ^ 2 ≤ (1 + 3 * ‖c‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hsq2 2
  linarith

/-- **A good escape radius for `p_c`, for `c` in the mandelbar.**  There is `R ≥ 2`,
`R ≥ escapeRadius c`, such that `p_c` expands (`R ≤ ‖z‖ ⟹ R ≤ ‖p_c z‖`), points of modulus `≥ R`
lie in the escape set, every escaping point reaches modulus `≥ R` under iteration of `p_c`, and
the `p_c`-image of the critical segment `[0, r]` (`p_c r = 0`, `t ∈ [0,1]`) stays in the disk of
radius `R`.

Explicitly `R = max (escapeRadius c + 1) ((1 + 3‖c‖)² + ‖c‖)`: the second term dominates the
critical region by `norm_pMap_smul_le_of_pMap_eq_zero`, and beyond `escapeRadius c + 1` the map
`p_c` is expanding (`le_norm_pMap_of_escapeRadius_le`) and the Green function is positive
(`green_pos_of_mem_escapeRegion`, the margin `+1` putting the radius strictly inside the
escaping region `escapeRegion ‖c‖`).  The mandelbar hypothesis is not needed for these three
items; it is kept because it is part of the intended statement. -/
theorem exists_goodRadius_of_mem_mandelbar (c : ℂ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) :
    ∃ R : ℝ, 2 ≤ R ∧ Work.Bottcher.escapeRadius c ≤ R ∧
      (∀ z : ℂ, R ≤ ‖z‖ → R ≤ ‖Work.Bottcher.pMap c z‖) ∧
      (∀ z : ℂ, R ≤ ‖z‖ → z ∈ Work.Bottcher.EscapeSet c) ∧
      (∀ z : ℂ, z ∈ Work.Bottcher.EscapeSet c → ∃ n : ℕ, R ≤ ‖(Work.Bottcher.pMap c)^[n] z‖) ∧
      (∀ r : ℂ, Work.Bottcher.pMap c r = 0 → ∀ t : ℝ, t ∈ Set.Icc 0 1 →
        ‖Work.Bottcher.pMap c (t * r)‖ ≤ R) := by
  -- the defining property of the mandelbar: the critical orbit of `T_c` is bounded
  have hcrit : ∃ M : ℝ, ∀ n : ℕ, ‖(Tantibar c)^[n] 0‖ ≤ M := hc
  obtain ⟨M, hM⟩ := hcrit
  refine ⟨max (Work.Bottcher.escapeRadius c + 1) ((1 + 3 * ‖c‖) ^ 2 + ‖c‖), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `2 ≤ R`
    have h2 : (2 : ℝ) ≤ Work.Bottcher.escapeRadius c + 1 := by
      rw [Work.Bottcher.escapeRadius]
      have hb : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
      linarith
    linarith [le_max_left (Work.Bottcher.escapeRadius c + 1) ((1 + 3 * ‖c‖) ^ 2 + ‖c‖)]
  · -- `escapeRadius c ≤ R`
    have h2 : Work.Bottcher.escapeRadius c ≤ Work.Bottcher.escapeRadius c + 1 := by linarith
    linarith [le_max_left (Work.Bottcher.escapeRadius c + 1) ((1 + 3 * ‖c‖) ^ 2 + ‖c‖)]
  · -- expansion of `p_c` beyond `R`
    intro z hz
    have hz' : Work.Bottcher.escapeRadius c ≤ ‖z‖ := by
      have h := le_max_left (Work.Bottcher.escapeRadius c + 1) ((1 + 3 * ‖c‖) ^ 2 + ‖c‖)
      linarith
    linarith [le_norm_pMap_of_escapeRadius_le c z hz']
  · -- points of modulus `≥ R` escape
    intro z hz
    have hlt : max 2 ‖c‖ < ‖z‖ := by
      have h := le_max_left (Work.Bottcher.escapeRadius c + 1) ((1 + 3 * ‖c‖) ^ 2 + ‖c‖)
      linarith [max_two_norm_lt_escapeRadius_add_one c]
    have hesc : z ∈ Work.Escape.escapeRegion ‖c‖ := hlt
    have hpos := Work.Bottcher.Green.green_pos_of_mem_escapeRegion
      (Work.Escape.monicGrowth_Tantibar c) (le_refl 2) (z := z) (N := 0) hesc
    simpa [Work.Bottcher.EscapeSet] using hpos
  · -- every escaping point reaches modulus `≥ R`
    intro z hz
    have hpos : 0 < Work.Bottcher.green c z := hz
    have ht := (Work.Bottcher.Green.green_pos_iff c z).mp hpos
    have h2n : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
    have hcomp : Filter.Tendsto (fun n : ℕ => ‖(Tantibar c)^[2 * n] z‖)
        Filter.atTop Filter.atTop := ht.comp h2n
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hcomp.eventually_ge_atTop
      (max (Work.Bottcher.escapeRadius c + 1) ((1 + 3 * ‖c‖) ^ 2 + ‖c‖)))
    exact ⟨N, by rw [Work.Bottcher.pMap_iterate]; exact hN N le_rfl⟩
  · -- the critical region lies in the disk of radius `R`
    intro r hr t ht
    have hbdd := norm_pMap_smul_le_of_pMap_eq_zero c r hr t ht
    linarith [le_max_right (Work.Bottcher.escapeRadius c + 1) ((1 + 3 * ‖c‖) ^ 2 + ‖c‖)]

end Work.Bottcher.Contraction
