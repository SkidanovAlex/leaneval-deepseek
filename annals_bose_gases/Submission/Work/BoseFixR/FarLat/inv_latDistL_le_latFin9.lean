import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.FarLatDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FarLat.inv_latDistL_le_latFin9`

The finite-window domination of the singular periodic kernel `1/latDistL`: on the double cell
`‖z‖ ≤ 2ℓ`, the *reciprocal* distance to the `ℓ`-lattice is dominated by the sum of the
reciprocals of the distances to the lattice points of the fixed window
`latFin9 = {-4,…,4}³`:

    (latDistL ℓ z)⁻¹ ≤ Σ_{p ∈ latFin9} ‖z - lat ℓ p‖⁻¹        (‖z‖ ≤ 2ℓ).

**Why it is true, and where `4` comes from.**  `latDistL ℓ z = infDist z (range (lat ℓ))` is the
minimal distance, so its *reciprocal* is the *maximum* of the reciprocals `‖z - lat ℓ p‖⁻¹`.
It therefore suffices to know that the *nearest* lattice point has label in the window `latFin9`:
if `p` is any label outside it, some coordinate satisfies `|p i| ≥ 5`, whence (using only
`|z i| ≤ ‖z‖ ≤ 2ℓ` and `ℓ > 0`)

    ‖z - lat ℓ p‖ ≥ |z i - ℓ p i| ≥ ℓ·5 - 2ℓ = 3ℓ ≥ ‖z‖ ≥ ‖z - lat ℓ 0‖,

so `p` is at least as far from `z` as the origin, and the minimum over *all* lattice points is
already attained in `latFin9` (whose elements therefore include an argmin).  The argument is
carried out here with the minimum `latFin9.inf' …

**How it is used.**  This is the step that turns the *singular periodic* kernel `1/latDistL` in
`Work.BoseFixR.farLatParseval` into a finite sum of *translation-invariant* Coulomb kernels
`‖· - lat ℓ p‖⁻¹`, `p ∈ latFin9`, each of which is then dominated pointwise by the Coulomb
potential of the localised kernel `wScaled ℓ (g0 v h)` (see `FarLatDefs`' header).

The estimate is *crude* on purpose: the right-hand side is a sum of 729 nonnegative terms, so it
is far bigger than `1/latDistL` in general.  Only the two facts used above (the argmin is in the
window; the sum dominates any single term) enter.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseFixR.FarLat

/-- The origin belongs to the window `latFin9`. -/
lemma zero_mem_latFin9 : (0 : Fin 3 → ℤ) ∈ Work.BoseFixR.latFin9 := by
  rw [Work.BoseFixR.latFin9, Fintype.mem_piFinset]
  intro i
  simp

/-- The window `latFin9` is nonempty. -/
lemma latFin9_nonempty : (Work.BoseFixR.latFin9).Nonempty := ⟨0, zero_mem_latFin9⟩

/-- The distance to the lattice point labelled `p`, as a function of `p` (the quantity whose
`inf'` over the window is the distance to the lattice). -/
private noncomputable def farF (ℓ : ℝ) (z : EuclideanSpace ℝ (Fin 3)) (p : Fin 3 → ℤ) : ℝ :=
  ‖z - Work.BoseFixR.lat ℓ p‖

/-- **The finite-window domination of `1/latDistL`.**  On the double cell `‖z‖ ≤ 2ℓ` the
reciprocal of the distance to the `ℓ`-lattice is at most the sum of the reciprocals of the
distances to the lattice points of the window `{-4,…,4}³`. -/
theorem inv_latDistL_le_latFin9 {ℓ : ℝ} (hℓ : 0 < ℓ) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : ‖z‖ ≤ 2 * ℓ) :
    (Work.BoseFixR.latDistL ℓ z)⁻¹
      ≤ ∑ p ∈ Work.BoseFixR.latFin9, (‖z - Work.BoseFixR.lat ℓ p‖)⁻¹ := by
  -- `m` is the minimum of the distance over the *window*; we show it equals the distance to the
  -- lattice.
  set m : ℝ := Work.BoseFixR.latFin9.inf' latFin9_nonempty (farF ℓ z) with hm
  -- Off the window, the distance is at least `3ℓ`.
  have hfar : ∀ p, p ∉ Work.BoseFixR.latFin9 → 3 * ℓ ≤ farF ℓ z p := by
    intro p hp
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, p i ∉ Finset.Icc (-4 : ℤ) 4 := by
      by_contra h
      exact hp (by
        rw [Work.BoseFixR.latFin9, Fintype.mem_piFinset]
        intro j
        exact not_not.mp (not_exists.mp h j))
    simp only [Finset.mem_Icc, not_and, not_le] at hi
    have h4 : (4 : ℤ) < p i ∨ p i < -4 := by
      by_cases h : (-4 : ℤ) ≤ p i
      · exact Or.inl (hi h)
      · exact Or.inr (by omega)
    have h5 : (5 : ℤ) ≤ |p i| := by
      rcases h4 with h | h
      · rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ p i)]; omega
      · rw [abs_of_nonpos (by omega : p i ≤ 0)]; omega
    have h5R : (5 : ℝ) ≤ |(p i : ℝ)| := by
      calc (5 : ℝ) = ((5 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|p i| : ℤ) : ℝ) := by exact_mod_cast h5
        _ = |((p i : ℤ) : ℝ)| := by rw [Int.cast_abs]
        _ = |(p i : ℝ)| := by norm_num
    -- the `i`-th coordinate of `z` is bounded by `‖z‖ ≤ 2ℓ`
    have hzi : |z i| ≤ 2 * ℓ := by
      have h := PiLp.norm_apply_le z i
      have h2 : |z i| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using h
      linarith
    have hcoord : 3 * ℓ ≤ |z i - (Work.BoseFixR.lat ℓ p) i| := by
      rw [Work.BoseFixR.lat_apply]
      have h2 : |ℓ * (p i : ℝ)| - |z i| ≤ |z i - ℓ * (p i : ℝ)| := by
        have h := abs_sub_abs_le_abs_sub (ℓ * (p i : ℝ)) (z i)
        rw [abs_sub_comm (ℓ * (p i : ℝ)) (z i)] at h
        exact h
      have h3 : |ℓ * (p i : ℝ)| = ℓ * |(p i : ℝ)| := by
        rw [abs_mul, abs_of_nonneg hℓ.le]
      rw [h3] at h2
      nlinarith [h2, h5R, hzi, hℓ]
    have hle : |z i - (Work.BoseFixR.lat ℓ p) i| ≤ ‖z - Work.BoseFixR.lat ℓ p‖ := by
      have h := PiLp.norm_apply_le (z - Work.BoseFixR.lat ℓ p) i
      simpa [Real.norm_eq_abs] using h
    exact le_trans hcoord hle
  -- `m` is a lower bound for *all* the distances.
  have hm_le : ∀ p, m ≤ farF ℓ z p := by
    intro p
    by_cases hp : p ∈ Work.BoseFixR.latFin9
    · have h := Finset.inf'_le (s := Work.BoseFixR.latFin9) (farF ℓ z) hp
      rw [← hm] at h
      exact h
    · have h1 := Finset.inf'_le (s := Work.BoseFixR.latFin9) (farF ℓ z) zero_mem_latFin9
      have h2 : farF ℓ z 0 = ‖z‖ := by
        show ‖z - Work.BoseFixR.lat ℓ 0‖ = ‖z‖
        rw [Work.BoseFixR.lat_zero, sub_zero]
      have h3 := hfar p hp
      rw [← hm] at h1
      rw [h2] at h1
      linarith
  -- hence `m` *is* the distance to the lattice
  have hdist : Work.BoseFixR.latDistL ℓ z = m := by
    refine le_antisymm ?_ ?_
    · -- the window contains an argmin, so the distance to the lattice is at most `m`
      rw [Work.BoseFixR.latDistL]
      obtain ⟨p0, _, hp0eq⟩ :=
        Finset.exists_mem_eq_inf' latFin9_nonempty (farF ℓ z)
      have hp0eq' : m = farF ℓ z p0 := by rw [hm, hp0eq]
      rw [hp0eq']
      have h := Metric.infDist_le_dist_of_mem
        (s := Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n)) (x := z) ⟨p0, rfl⟩
      simpa [farF, dist_eq_norm] using h
    · -- and `m` is a lower bound for all distances to lattice points
      rw [Work.BoseFixR.latDistL]
      rw [Metric.le_infDist (s := Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n))
        ⟨0, ⟨0, by simp [Work.BoseFixR.lat_zero]⟩⟩]
      intro y hy
      rcases hy with ⟨p, rfl⟩
      rw [dist_eq_norm]
      exact hm_le p
  rw [hdist]
  -- the maximum reciprocal is one of the summands, all of which are nonnegative
  obtain ⟨p0, hp0, hp0eq⟩ := Finset.exists_mem_eq_inf' latFin9_nonempty (farF ℓ z)
  have hp0eq' : m = farF ℓ z p0 := by rw [hm, hp0eq]
  rw [hp0eq']
  have h2 : (farF ℓ z p0)⁻¹
      ≤ ∑ p ∈ Work.BoseFixR.latFin9, (farF ℓ z p)⁻¹ :=
    Finset.single_le_sum (s := Work.BoseFixR.latFin9) (f := fun p => (farF ℓ z p)⁻¹)
      (fun i _ => inv_nonneg.mpr (norm_nonneg (z - Work.BoseFixR.lat ℓ i))) hp0
  simpa [farF] using h2

end Work.BoseFixR.FarLat
