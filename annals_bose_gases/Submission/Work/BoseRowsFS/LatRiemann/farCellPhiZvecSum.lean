import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowsFS.LatRiemann.Geom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.LatRiemann.farCellPhiZvecSum`

The *far-cell* `Φ`-weighted lattice sum of the Riemann comparison
(`Submission/Work/BoseRowsFS/FINDING_lattice_riemann_core.md`, Step 3b).

For a lattice `h·ℤ³` with `h > 0`, a `Φ` decaying like `(1 + ‖p‖)⁻⁴` and a finite set
`Kr` of lattice indices whose lattice points stay at distance `≥ 2√3 h` from the origin
(i.e. the "far" cells, where the second-order expansion of `1/‖p‖²` is controlled),

    `∑_{m ∈ Kr} |Φ (latPt h m)| · 16 h⁵ / ‖latPt h m‖⁴ ≤ 16 C4 A h`,

provided `∑_{m ∈ S} ‖zvec m‖⁻⁴ ≤ C4` for every finite set `S` of non-zero indices.

The proof is the explicit computation of the FINDING: on the far cells
`‖latPt h m‖ = h ‖zvec m‖ ≥ 2√3 h`, so `‖zvec m‖ ≥ 1` and

    16 h⁵ / ‖latPt h m‖⁴ = 16 h · (‖zvec m‖⁴)⁻¹ ,

while `|Φ (latPt h m)| ≤ A`.  Summing and applying the hypothesis `hC4b` gives the claim.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowsFS.LatRiemann

theorem farCellPhiZvecSum {h A C4 : ℝ} (hh : 0 < h) (hA : 0 ≤ A) (hC4 : 0 ≤ C4)
    {Φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hΦ : ∀ p, |Φ p| ≤ A / (1 + ‖p‖) ^ 4)
    (Kr : Finset (Fin 3 → ℤ))
    (hKr : ∀ m ∈ Kr, 2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖)
    (hC4b : ∀ S : Finset (Fin 3 → ℤ), (∀ m ∈ S, m ≠ 0) →
      ∑ m ∈ S, (‖Work.BoseRowsFS.zvec m‖ ^ 4)⁻¹ ≤ C4) :
    ∑ m ∈ Kr, |Φ (Work.BoseRowsFS.latPt h m)| * (16 * h ^ 5 / ‖Work.BoseRowsFS.latPt h m‖ ^ 4)
      ≤ 16 * C4 * A * h := by
  -- The far-cell hypothesis excludes the origin: `latPt h 0 = 0`.
  have hmem_ne : ∀ m ∈ Kr, m ≠ 0 := by
    intro m hm hm0
    have hzvec0 : Work.BoseRowsFS.zvec (0 : Fin 3 → ℤ) = 0 := by
      ext i
      simp [Work.BoseRowsFS.zvec]
    have hzero : ‖Work.BoseRowsFS.latPt h m‖ = 0 := by
      rw [norm_latPt_eq_of_nonneg (le_of_lt hh) m, hm0, hzvec0, norm_zero, mul_zero]
    have hs3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have hpos : (0 : ℝ) < 2 * Real.sqrt 3 * h := mul_pos (mul_pos (by norm_num) hs3) hh
    have := hKr m hm
    rw [hzero] at this
    linarith
  -- Per-term bound.
  have hterm : ∀ m ∈ Kr,
      |Φ (Work.BoseRowsFS.latPt h m)| * (16 * h ^ 5 / ‖Work.BoseRowsFS.latPt h m‖ ^ 4)
        ≤ 16 * h * A * (‖Work.BoseRowsFS.zvec m‖ ^ 4)⁻¹ := by
    intro m hm
    have hne := hmem_ne m hm
    have hz : 0 < ‖Work.BoseRowsFS.zvec m‖ :=
      lt_of_lt_of_le zero_lt_one (one_le_norm_zvec hne)
    have hhnorm : ‖Work.BoseRowsFS.latPt h m‖ = h * ‖Work.BoseRowsFS.zvec m‖ :=
      norm_latPt_eq_of_nonneg (le_of_lt hh) m
    -- `|Φ (latPt h m)| ≤ A`: the `Φ`-decay factor is `≤ 1`.
    have hPhi_le : |Φ (Work.BoseRowsFS.latPt h m)| ≤ A := by
      refine (hΦ _).trans ?_
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + ‖Work.BoseRowsFS.latPt h m‖) ^ 4)]
      calc A = A * 1 := by ring
        _ ≤ A * (1 + ‖Work.BoseRowsFS.latPt h m‖) ^ 4 :=
            mul_le_mul_of_nonneg_left
              (one_le_pow₀ (by linarith [norm_nonneg (Work.BoseRowsFS.latPt h m)])) hA
    -- The weight identity `16 h⁵ / ‖latPt‖⁴ = 16 h · ‖zvec‖⁻⁴`.
    have hratio : 16 * h ^ 5 / ‖Work.BoseRowsFS.latPt h m‖ ^ 4
        = 16 * h * (‖Work.BoseRowsFS.zvec m‖ ^ 4)⁻¹ := by
      rw [hhnorm, mul_pow]
      field_simp
    calc |Φ (Work.BoseRowsFS.latPt h m)| * (16 * h ^ 5 / ‖Work.BoseRowsFS.latPt h m‖ ^ 4)
        = |Φ (Work.BoseRowsFS.latPt h m)| * (16 * h * (‖Work.BoseRowsFS.zvec m‖ ^ 4)⁻¹) := by
          rw [hratio]
      _ ≤ A * (16 * h * (‖Work.BoseRowsFS.zvec m‖ ^ 4)⁻¹) := by
          refine mul_le_mul_of_nonneg_right hPhi_le ?_
          exact le_of_lt (mul_pos (by linarith : (0 : ℝ) < 16 * h)
            (inv_pos.mpr (pow_pos hz 4)))
      _ = 16 * h * A * (‖Work.BoseRowsFS.zvec m‖ ^ 4)⁻¹ := by ring
  calc ∑ m ∈ Kr, |Φ (Work.BoseRowsFS.latPt h m)| * (16 * h ^ 5 / ‖Work.BoseRowsFS.latPt h m‖ ^ 4)
      ≤ ∑ m ∈ Kr, 16 * h * A * (‖Work.BoseRowsFS.zvec m‖ ^ 4)⁻¹ := Finset.sum_le_sum hterm
    _ = 16 * h * A * ∑ m ∈ Kr, (‖Work.BoseRowsFS.zvec m‖ ^ 4)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 16 * h * A * C4 := by
        exact mul_le_mul_of_nonneg_left (hC4b Kr hmem_ne) (by positivity)
    _ = 16 * C4 * A * h := by ring

end Work.BoseRowsFS.LatRiemann
