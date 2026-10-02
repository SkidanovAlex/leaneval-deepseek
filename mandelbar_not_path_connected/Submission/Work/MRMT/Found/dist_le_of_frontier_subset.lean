import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- **Diameter bound from a frontier-covering curve.**

If `D` is an open bounded subset of `ℂ` whose frontier is contained in the image of a
curve `γ` all of whose pairwise distances are `≤ L`, then every two points of `D` are at
distance `≤ L`.  In particular, `diam D ≤ diam (range γ)`.

The proof picks the unit vector `u` pointing from `x` to `y` and minimises/maximises the
continuous real function `z ↦ ⟪z - x, u⟫_ℝ` on the compact set `closure D`.  The extremal
points cannot lie in the open set `D` (one could move slightly in the direction `∓u` and
decrease/increase the value), hence they lie on the frontier.  Chaining the elementary
estimates gives `‖x - y‖ ≤ ‖q - p‖ ≤ L`. -/
theorem dist_le_of_frontier_subset {D : Set ℂ} (hD : IsOpen D) (hb : Bornology.IsBounded D)
    {γ : ℝ → ℂ} (hfront : frontier D ⊆ Set.range γ) {L : ℝ} (hL : ∀ s t : ℝ, ‖γ s - γ t‖ ≤ L) :
    ∀ x ∈ D, ∀ y ∈ D, ‖x - y‖ ≤ L := by
  intro x hx y hy
  have hLnn : 0 ≤ L := by simpa using hL 0 0
  rcases eq_or_ne x y with hxy | hxy
  · subst hxy; simpa using hLnn
  set r : ℝ := ‖y - x‖ with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
  set u : ℂ := (y - x) / (r : ℂ) with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_div, show ‖(r:ℂ)‖ = |r| by simp, abs_of_pos hrpos, ← hrdef, div_self hrpos.ne']
  have hru : (r : ℂ) * u = y - x := by
    rw [hudef]; exact mul_div_cancel₀ (y - x) hrne
  have hrsmul : r • u = y - x := by rw [Complex.real_smul, hru]
  let φ : ℂ → ℝ := fun z => inner ℝ (z - x) u
  have hφcont : Continuous φ := by
    simp only [φ]; exact (continuous_id.sub continuous_const).inner continuous_const
  have hKcomp : IsCompact (closure D) := by
    rw [Metric.isCompact_iff_isClosed_bounded]; exact ⟨isClosed_closure, hb.closure⟩
  have hKne : (closure D).Nonempty := ⟨x, subset_closure hx⟩
  obtain ⟨p, hpK, hpmin⟩ := hKcomp.exists_isMinOn hKne hφcont.continuousOn
  obtain ⟨q, hqK, hqmax⟩ := hKcomp.exists_isMaxOn hKne hφcont.continuousOn
  -- `p` is a point of the frontier
  have hpnd : p ∉ D := by
    intro hpD
    obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hD p hpD
    set w : ℂ := p - (ε/2) • u with hwdef
    have hwmem : w ∈ D := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have hwp : w - p = -((ε/2) • u) := by rw [hwdef]; abel
      rw [hwp, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hu, mul_one]
      linarith
    have hφw : φ w = φ p - ε/2 := by
      have hwx : w - x = (p - x) - (ε/2) • u := by rw [hwdef]; abel
      simp only [φ]
      rw [hwx, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
      norm_num
    have hle : φ p ≤ φ w := hpmin (subset_closure hwmem)
    rw [hφw] at hle
    linarith
  have hqnd : q ∉ D := by
    intro hqD
    obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hD q hqD
    set w : ℂ := q + (ε/2) • u with hwdef
    have hwmem : w ∈ D := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have hwp : w - q = (ε/2) • u := by rw [hwdef]; abel
      rw [hwp, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), hu, mul_one]
      linarith
    have hφw : φ w = φ q + ε/2 := by
      have hwx : w - x = (q - x) + (ε/2) • u := by rw [hwdef]; abel
      simp only [φ]
      rw [hwx, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
      norm_num
    have hle : φ w ≤ φ q := hqmax (subset_closure hwmem)
    rw [hφw] at hle
    linarith
  have hpfront : p ∈ frontier D := by
    rw [frontier]; exact ⟨hpK, by rw [hD.interior_eq]; exact hpnd⟩
  have hqfront : q ∈ frontier D := by
    rw [frontier]; exact ⟨hqK, by rw [hD.interior_eq]; exact hqnd⟩
  obtain ⟨s, hs⟩ := hfront hpfront
  obtain ⟨t, ht⟩ := hfront hqfront
  have hpq : ‖q - p‖ ≤ L := by
    have hst := hL s t
    rw [hs, ht] at hst
    rwa [norm_sub_rev] at hst
  have h1 : φ y - φ x = ‖y - x‖ := by
    have hone : φ y - φ x = inner ℝ (y - x) u := by simp [φ]
    rw [hone, ← hrdef, ← hrsmul, real_inner_smul_left, real_inner_self_eq_norm_sq, hu, one_pow,
      mul_one]
  have h2 : φ q - φ p ≤ ‖q - p‖ := by
    have hqp : φ q - φ p = inner ℝ (q - p) u := by
      simp only [φ, inner_sub_left]
      ring
    rw [hqp]
    calc inner ℝ (q - p) u ≤ |inner ℝ (q - p) u| := le_abs_self _
      _ ≤ ‖q - p‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ = ‖q - p‖ := by rw [hu, mul_one]
  have hpx : φ p ≤ φ x := hpmin (subset_closure hx)
  have hyq : φ y ≤ φ q := hqmax (subset_closure hy)
  rw [norm_sub_rev, ← h1]
  calc φ y - φ x ≤ φ q - φ p := by linarith
    _ ≤ ‖q - p‖ := h2
    _ ≤ L := hpq

end Work.MRMT.Found
