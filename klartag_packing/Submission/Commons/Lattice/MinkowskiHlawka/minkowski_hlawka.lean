import Mathlib
import Submission.Commons.GeometryOfNumbers.Counting.card_int_points_ball_le_volume
import Submission.Commons.GeometryOfNumbers.Counting.exists_prime_radius
import Submission.Commons.Lattice.Counting.exists_qary_lattice_no_short_vector
import Submission.Commons.Lattice.MinkowskiHlawka.lattice_of_covector
import Submission.Commons.Analysis.InnerProductSpace.unitBall_volume_pos

namespace Commons.Lattice.MinkowskiHlawka

open MeasureTheory Metric MeasureTheory.Measure
open scoped ENNReal

/-- The Lebesgue volume of the ball of radius `t` in `ℝ^n` in terms of the unit ball. -/
lemma volume_ball_toReal {n : ℕ} {t : ℝ} (ht : 0 < t) :
    (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) t)).toReal
      = t ^ n * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
  have h := addHaar_ball_mul_of_pos MeasureTheory.volume (0 : EuclideanSpace ℝ (Fin n)) ht 1
  rw [mul_one] at h
  rw [h, finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg ht.le n)]

/-- **Minkowski–Hlawka** (existence of a lattice with controlled first minimum and covolume).

For every `d ≥ 2` there is a `ℤ`-lattice `Λ ⊆ ℝ^d` all of whose nonzero vectors have norm `≥ 1`
and whose covolume is at most four times the volume of the unit ball. -/
theorem minkowski_hlawka (d : ℕ) (hd : 2 ≤ d) :
    ∃ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (h₁ : DiscreteTopology Λ) (h₂ : IsZLattice ℝ Λ),
      (∀ v : Λ, v ≠ 0 → 1 ≤ ‖(v : EuclideanSpace ℝ (Fin d))‖) ∧
      ZLattice.covolume Λ
        ≤ 4 * ENNReal.toReal (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) := by
  have hd0 : 0 < d := by omega
  haveI : NeZero d := ⟨by omega⟩
  set ω : ℝ := ENNReal.toReal (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) with hωdef
  have hωpos : 0 < ω := by
    rw [hωdef]
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    have : Nontrivial (EuclideanSpace ℝ (Fin d)) := by infer_instance
    rw [← addHaar_closedBall_eq_addHaar_ball (MeasureTheory.volume) (0 : EuclideanSpace ℝ (Fin d)) 1]
    exact Commons.Analysis.InnerProductSpace.unitBall_volume_pos (E := EuclideanSpace ℝ (Fin d))
  -- choose a prime `q` and a radius `R`
  obtain ⟨q, hqprime, R, hRpos, hR1, hRq, hqeq, hineq⟩ :=
    Commons.GeometryOfNumbers.Counting.exists_prime_radius hd hωpos
  haveI : Fact q.Prime := ⟨hqprime⟩
  -- the counting hypothesis for the `q`-ary construction
  have hcard :
      (Nat.card {x : Fin d → ℤ // 0 < (∑ i, ((x i : ℝ)) ^ 2) ∧
        (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2} : ℝ) < 2 * (q : ℝ) ^ 1 := by
    have hfin : ({x : Fin d → ℤ | (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2}).Finite :=
      Commons.GeometryOfNumbers.Counting.finite_int_points_ball R
    have hsub : {x : Fin d → ℤ | 0 < (∑ i, ((x i : ℝ)) ^ 2) ∧ (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2}
        ⊆ {x : Fin d → ℤ | (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2} := fun x hx => hx.2
    have hmono : Nat.card {x : Fin d → ℤ // 0 < (∑ i, ((x i : ℝ)) ^ 2) ∧
          (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2}
        ≤ Nat.card {x : Fin d → ℤ // (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2} :=
      Nat.card_mono hfin hsub
    have h2 := Commons.GeometryOfNumbers.Counting.card_int_points_ball_le_volume hd0 hRpos
    have h3 := volume_ball_toReal (n := d) (t := R + Real.sqrt (d : ℝ) / 2) (by positivity)
    rw [h3] at h2
    calc (Nat.card {x : Fin d → ℤ // 0 < (∑ i, ((x i : ℝ)) ^ 2) ∧
            (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2} : ℝ)
        ≤ (Nat.card {x : Fin d → ℤ // (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2} : ℝ) := by exact_mod_cast hmono
      _ ≤ (R + Real.sqrt (d : ℝ) / 2) ^ d * ω := by rw [hωdef]; exact h2
      _ < 2 * (q : ℝ) := hineq
      _ = 2 * (q : ℝ) ^ 1 := by ring
  -- the `q`-ary lattice avoiding all short vectors
  obtain ⟨A, hA⟩ := Commons.Lattice.Counting.exists_qary_lattice_no_short_vector
    (q := q) (m := 1) (d := d) hRpos hRq hcard
  set a : Fin d → ZMod q := fun j => A 0 j with ha
  -- the first coordinate is nonzero, since `‖e₀‖ = 1 ≤ R`
  have ha0 : a 0 ≠ 0 := by
    intro h0
    have hxne : (Pi.single (0 : Fin d) (1 : ℤ) : Fin d → ℤ) ≠ 0 := by
      intro h
      have := congrFun h 0
      simp [Pi.single_eq_same] at this
    have hx2 : (∑ i, (((Pi.single (0 : Fin d) (1 : ℤ) : Fin d → ℤ) i : ℝ)) ^ 2) ≤ R ^ 2 := by
      have h1 : (∑ i, (((Pi.single (0 : Fin d) (1 : ℤ) : Fin d → ℤ) i : ℝ)) ^ 2) = 1 := by
        rw [Finset.sum_eq_single 0]
        · simp
        · intro b _ hb; simp [Pi.single_eq_of_ne hb]
        · intro h; exact absurd (Finset.mem_univ 0) h
      rw [h1]; nlinarith [hR1]
    have hcond := hA (Pi.single (0 : Fin d) (1 : ℤ)) hxne hx2
    apply hcond
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    have hsum : (∑ j, ((Pi.single (0 : Fin d) (1 : ℤ) : Fin d → ℤ) j : ZMod q) * a j) = a 0 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro h; exact absurd (Finset.mem_univ 0) h
    rw [hsum, h0]
  -- transfer the "no short vector" property to `a`
  have hno : ∀ x : Fin d → ℤ, x ≠ 0 → (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2 →
      (∑ i, (x i : ZMod q) * a i) ≠ 0 := by
    intro x hxne hx2 hsum
    have hcond := hA x hxne hx2
    apply hcond
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simpa [ha] using hsum
  -- build the lattice
  obtain ⟨Λ, h₁, h₂, hmin, hcov⟩ :=
    Commons.Lattice.MinkowskiHlawka.lattice_of_covector (d := d) (q := q) (R := R) hRpos a ha0 hno
  refine ⟨Λ, h₁, h₂, hmin, ?_⟩
  have hbd : (q : ℝ) / R ^ d = 4 * ω := by
    rw [← hqeq]
    field_simp
  calc ZLattice.covolume Λ ≤ (q : ℝ) / R ^ d := hcov
    _ = 4 * ω := hbd

end Commons.Lattice.MinkowskiHlawka
