import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.LatRiemann.Geom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.LatRiemann.nearCellsValueSum`

The *near-cell value sum* of the lattice-vs-continuum comparison
(`Submission/Work/BoseRowsFS/LatRiemann/lattice_riemann_core.lean`): the near cells
`‖latPt h m‖ < 2√3 h` are at most `7³ = 343` lattice points, and each of them
carries at most `A·h` of value, so

    `Σ_{m ∈ Kr} |h³ Φ(latPt h m)| / ‖latPt h m‖² ≤ 343 · A · h`.

Two elementary facts do all the work:

* `zvec_norm_ge_one` — a lattice point `m ≠ 0` has `‖zvec m‖ ≥ 1`, hence
  `‖latPt h m‖ = h‖zvec m‖ ≥ h` and the quotient is at worst
  `h³ A / ((1+h)⁴ h²) ≤ A h`;
* `zvec_coord_bound` — the near condition `‖zvec m‖ < 2√3` forces every coordinate
  of `m` into `[-3,3]`, so the near set sits inside the `7³ = 343` functions
  `Fin 3 → {-3,…,3} ⊂ ℤ`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowsFS.LatRiemann

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Coordinatewise domination by the norm.**  Every coordinate of the lattice
vector `zvec m` is in absolute value at most `‖zvec m‖` — the elementary
`|x_i| ≤ ‖x‖` for the Euclidean norm, proved here from
`‖zvec m‖² = Σ_i (m i)²`. -/
lemma zvec_abs_coord_le_norm (m : Fin 3 → ℤ) (i : Fin 3) :
    |(((m i : ℤ)) : ℝ)| ≤ ‖Work.BoseRowsFS.zvec m‖ := by
  have hsq : ‖Work.BoseRowsFS.zvec m‖ ^ 2 = ∑ j, (((m j : ℤ)) : ℝ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Work.BoseRowsFS.zvec, Real.norm_eq_abs, sq_abs]
  have hle : (((m i : ℤ)) : ℝ) ^ 2 ≤ ∑ j, (((m j : ℤ)) : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 3 => (((m j : ℤ)) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have h2 : (((m i : ℤ)) : ℝ) ^ 2 ≤ ‖Work.BoseRowsFS.zvec m‖ ^ 2 := by rw [hsq]; exact hle
  have := sq_le_sq.mp h2
  rwa [abs_of_nonneg (norm_nonneg _)] at this

/-- **A nonzero lattice point is at norm at least one.** -/
lemma zvec_norm_ge_one {m : Fin 3 → ℤ} (hm : m ≠ 0) : 1 ≤ ‖Work.BoseRowsFS.zvec m‖ := by
  have hex : ∃ i : Fin 3, m i ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (funext fun i => by simpa using h i)
  obtain ⟨i, hi⟩ := hex
  have hpos : 0 < |m i| := abs_pos.mpr hi
  have h1 : (1 : ℤ) ≤ |m i| := by omega
  have h2 : (1 : ℝ) ≤ |(((m i : ℤ)) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast h1
  exact h2.trans (zvec_abs_coord_le_norm m i)

/-- **The coordinate box of the near set.**  If `‖zvec m‖ < 2√3` then every
coordinate of `m` lies in `[-3,3]` (because `√3 < 2`, so `|m i| ≤ ‖zvec m‖ < 4`). -/
lemma zvec_coord_bound {m : Fin 3 → ℤ}
    (hz : ‖Work.BoseRowsFS.zvec m‖ < 2 * Real.sqrt 3) (i : Fin 3) :
    -(3 : ℤ) ≤ m i ∧ m i ≤ 3 := by
  have h3 : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h4 : |(((m i : ℤ)) : ℝ)| < 4 := by
    refine lt_of_le_of_lt (zvec_abs_coord_le_norm m i) ?_
    linarith
  have h4'' : (|m i| : ℤ) < 4 := by
    rw [← Int.cast_abs] at h4
    exact_mod_cast h4
  have := abs_lt.mp h4''
  constructor <;> omega

theorem nearCellsValueSum {h A : ℝ} (hh : 0 < h) (hA : 0 ≤ A)
    {Φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hΦ : ∀ p, |Φ p| ≤ A / (1 + ‖p‖) ^ 4)
    (Kr : Finset (Fin 3 → ℤ))
    (hKr : ∀ m ∈ Kr, m ≠ 0 ∧ ¬ (2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖)) :
    ∑ m ∈ Kr, |h ^ 3 * Φ (Work.BoseRowsFS.latPt h m) / ‖Work.BoseRowsFS.latPt h m‖ ^ 2|
      ≤ 343 * A * h := by
  -- The near set `Kr` sits in the coordinate box `{-3,…,3}³`, hence has at most `343` points.
  have hcard : Kr.card ≤ 343 := by
    let S : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-3 : ℤ) 3)
    have hsub : Kr ⊆ S := by
      intro m hm
      obtain ⟨hne, hnot⟩ := hKr m hm
      have hnorm : ‖Work.BoseRowsFS.latPt h m‖ = h * ‖Work.BoseRowsFS.zvec m‖ := by
        rw [Work.BoseRowsFS.zvec_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      have hlt : ‖Work.BoseRowsFS.latPt h m‖ < 2 * Real.sqrt 3 * h := not_le.mp hnot
      have hz : ‖Work.BoseRowsFS.zvec m‖ < 2 * Real.sqrt 3 := by
        have h2 : h * ‖Work.BoseRowsFS.zvec m‖ < h * (2 * Real.sqrt 3) := by
          rw [hnorm] at hlt; linarith
        exact lt_of_mul_lt_mul_left h2 (le_of_lt hh)
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      exact zvec_coord_bound hz i
    calc Kr.card ≤ S.card := Finset.card_le_card hsub
      _ = 343 := by simp [S, Fintype.card_piFinset]
  -- Each near cell contributes at most `A * h`.
  have hterm : ∀ m ∈ Kr, |h ^ 3 * Φ (Work.BoseRowsFS.latPt h m)
      / ‖Work.BoseRowsFS.latPt h m‖ ^ 2| ≤ A * h := by
    intro m hm
    obtain ⟨hne, _⟩ := hKr m hm
    set p := Work.BoseRowsFS.latPt h m with hp
    have hnorm : ‖p‖ = h * ‖Work.BoseRowsFS.zvec m‖ := by
      rw [hp, Work.BoseRowsFS.zvec_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    have hge : h ≤ ‖p‖ := by
      have h0 : 1 ≤ ‖Work.BoseRowsFS.zvec m‖ := zvec_norm_ge_one hne
      have := mul_le_mul_of_nonneg_left h0 (le_of_lt hh)
      rw [hnorm]; simpa using this
    have hΦle : |Φ p| ≤ A := by
      refine (hΦ p).trans ?_
      rw [div_le_iff₀ (by positivity)]
      have h1 : (1 : ℝ) ≤ (1 + ‖p‖) ^ 4 := by
        have h0 : (1 : ℝ) ≤ 1 + ‖p‖ := by have := norm_nonneg p; linarith
        exact one_le_pow₀ h0
      nlinarith [hA, h1]
    have h3 : (0 : ℝ) ≤ h ^ 3 := by positivity
    have hL : |h ^ 3 * Φ p / ‖p‖ ^ 2| = h ^ 3 * |Φ p| / ‖p‖ ^ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg h3, abs_of_nonneg (sq_nonneg ‖p‖)]
    rw [hL]
    calc h ^ 3 * |Φ p| / ‖p‖ ^ 2
        ≤ h ^ 3 * A / ‖p‖ ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΦle h3) (sq_nonneg _)
      _ ≤ h ^ 3 * A / h ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [hge])
      _ = A * h := by field_simp
  calc ∑ m ∈ Kr, |h ^ 3 * Φ (Work.BoseRowsFS.latPt h m) / ‖Work.BoseRowsFS.latPt h m‖ ^ 2|
      ≤ ∑ m ∈ Kr, A * h := Finset.sum_le_sum hterm
    _ = Kr.card * (A * h) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 343 * (A * h) := by
        have hc : (Kr.card : ℝ) ≤ 343 := by exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 343 * A * h := by ring

end Work.BoseRowsFS.LatRiemann
