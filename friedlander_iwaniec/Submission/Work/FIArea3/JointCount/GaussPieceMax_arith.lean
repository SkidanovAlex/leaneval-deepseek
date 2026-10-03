/-
# `Work.FIArea3.JointCount.GaussPieceMax_arith` — arithmetic of the maximal pieces

Let `{z : ℤ[i] | d ∣ |z|²}` be decomposed into the principal ideals `w·ℤ[i]` of the
*maximal* piece generators `w` (`GaussPieceMax d w`, from `pieces.lean`).  This file records
the two arithmetic facts about such a `w` that the covering argument needs:

* `d ≤ gnorm w`  (the index `gnorm w` of a maximal piece is at least `d`);
* `gnorm w ≤ d * d`.

The second is elementary: a piece generator is `lcm u (star (d/u))`, which divides
`u · star (d/u)`, and that product has Gaussian norm `gnorm u · gnorm (d/u) = gnorm (d) = d²`.

For the first, note that `w` is *itself* a point of its own piece `w·ℤ[i]`, so
`w ∈ {z | d ∣ |z|²}`: the covering statement `gaussPieceGen_dvd_gnorm` (applied to the
witnessing Gaussian divisor `u ∣ d` of `w` and to `z = w`) gives `d ∣ gnorm w`, hence
`d ≤ gnorm w` since `gnorm w ≠ 0` (a piece generator never vanishes for `d ≥ 1`).

The third component — monotonicity of `gnorm` along divisibility of maximal pieces — is the
elementary divisibility `gnorm w ∣ gnorm v ⇒ gnorm w ≤ gnorm v` together with `v ≠ 0`.
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.pieces
import Submission.Work.FIArea3.JointCount.gaussPieceGen_dvd_gnorm
import Submission.Work.FIArea3.JointCount.maximal_piece_cover

namespace Work.FIArea3.JointCount

open Work.FIPlan


attribute [local instance] Classical.propDecidable

/-- `gnorm` is invariant under conjugation. -/
lemma GaussPieceMax_arith_gnorm_star (z : GaussianInt) : gnorm (star z) = gnorm z := by
  simp [gnorm, Zsqrtd.norm_conj]

/-- The Gaussian norm of the lift of a natural number is its square: `gnorm (d : ℤ[i]) = d * d`. -/
lemma GaussPieceMax_arith_gnorm_natCast (n : ℕ) : gnorm (n : GaussianInt) = n * n := by
  rw [show (n : GaussianInt) = ((n : ℤ) : GaussianInt) by push_cast; ring,
    gnorm, Zsqrtd.norm_intCast]
  simp [Int.natAbs_mul]

/-- For a Gaussian divisor `u ∣ d` (`d ≥ 1`) the product `u · star (d/u)` has Gaussian norm
`d * d`. -/
lemma GaussPieceMax_arith_gnorm_mul_star_div (d : ℕ) (hd : 1 ≤ d) {u : GaussianInt}
    (hu : u ∣ (d : GaussianInt)) : gnorm (u * star ((d : GaussianInt) / u)) = d * d := by
  have hd0 : d ≠ 0 := by omega
  have hdc : (d : GaussianInt) ≠ 0 := by exact_mod_cast hd0
  have hu0 : u ≠ 0 := ne_zero_of_dvd_ne_zero hdc hu
  have hmul : u * ((d : GaussianInt) / u) = (d : GaussianInt) :=
    EuclideanDomain.mul_div_cancel' hu0 hu
  rw [gnorm_mul, GaussPieceMax_arith_gnorm_star, ← gnorm_mul, hmul,
    GaussPieceMax_arith_gnorm_natCast]

theorem GaussPieceMax_arith (d : ℕ) (hd : 1 ≤ d) :
    (∀ w : GaussianInt, Work.FIArea3.JointCount.GaussPieceMax d w → d ≤ Work.FIPlan.gnorm w)
    ∧ (∀ w : GaussianInt, Work.FIArea3.JointCount.GaussPieceMax d w →
        Work.FIPlan.gnorm w ≤ d * d)
    ∧ (∀ w v : GaussianInt, Work.FIArea3.JointCount.GaussPieceMax d w →
        Work.FIArea3.JointCount.GaussPieceMax d v →
        w ∣ v → Work.FIPlan.gnorm w ≤ Work.FIPlan.gnorm v) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `d ≤ gnorm w`: `w` lies in its own piece, so `d ∣ |w|²` and hence `d ≤ gnorm w`.
    intro w hw
    obtain ⟨u, hu, hwu⟩ := hw.1
    have hz : gaussPieceGen d u ∣ w := by rw [hwu]
    have hdvd : d ∣ gnorm w := gaussPieceGen_dvd_gnorm d hd hu hz
    have hw0 : w ≠ 0 := hwu.symm ▸ gaussPieceGen_ne_zero hd hu
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (fun h => hw0 ((gnorm_eq_zero_iff w).mp h))) hdvd
  · -- `gnorm w ≤ d * d`: `w = lcm u (star (d/u))` divides `u · star (d/u)`, of norm `d²`.
    intro w hw
    obtain ⟨u, hu, hwu⟩ := hw.1
    have hld : gaussPieceGen d u ∣ u * star ((d : GaussianInt) / u) := by
      rw [gaussPieceGen]
      exact EuclideanDomain.lcm_dvd_iff.mpr ⟨dvd_mul_right _ _, dvd_mul_left _ _⟩
    have hdv : gnorm (gaussPieceGen d u) ∣ gnorm (u * star ((d : GaussianInt) / u)) :=
      gnorm_dvd_of_dvd hld
    rw [GaussPieceMax_arith_gnorm_mul_star_div d hd hu] at hdv
    have hmain : gnorm (gaussPieceGen d u) ≤ d * d :=
      Nat.le_of_dvd (by nlinarith [hd]) hdv
    rw [hwu]; exact hmain
  · -- Monotonicity: `w ∣ v` gives `gnorm w ∣ gnorm v`, and `v ≠ 0`.
    intro w v hw hv hwv
    obtain ⟨u, hu, hwu⟩ := hw.1
    obtain ⟨u', hu', hv'⟩ := hv.1
    have hv0 : v ≠ 0 := hv'.symm ▸ gaussPieceGen_ne_zero hd hu'
    obtain ⟨t, rfl⟩ := hwv
    have ht : t ≠ 0 := fun h => hv0 (by rw [h, mul_zero])
    rw [gnorm_mul]
    exact Nat.le_mul_of_pos_right (gnorm w)
      (Nat.pos_of_ne_zero (fun h => ht ((gnorm_eq_zero_iff t).mp h)))

end Work.FIArea3.JointCount
