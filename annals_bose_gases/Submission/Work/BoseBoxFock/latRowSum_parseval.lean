import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.rowSumDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latRowSum_parseval` — Parseval for the difference `rowSum - ballSum`

The difference of the finite lattice row sum and the momentum-ball partial sum is a **finite
character sum indexed by the box** `cube N = [-N,N]³ ∩ ℤ³`, with coefficients `rhoCoef`:

    `rowSum ℓ fu N W z - ballSum ℓ N W z
        = ∑_{n ∈ cube N} rhoCoef ℓ fu N W n · e^{i⟪kmomInt ℓ n, z⟫}`,

so the finite lattice Parseval `Work.BoseBoxFock.latFinset_parseval_box` on the closed cube
`latBox ℓ = [0,ℓ]³` evaluates its `L²` norm in closed form:

    `∫_{latBox ℓ} ‖rowSum - ballSum‖² = ℓ³ · ∑_{n ∈ cube N} ‖rhoCoef n‖²`.

The two bookkeeping facts are:

* `labVec N : Lab N → Fin 3 → ℤ` maps the label group **bijectively onto** `cube N`
  (`Work.BoseRowQ2.image_labVec_eq_cube`, `Work.BoseRowQ2.labVec_inj'`), so the `Lab N`-indexed sum
  reindexes (`Finset.sum_image`);
* the momentum ball `latBall (N/4)` is **contained** in `cube N`
  (`latBall_div_four_subset_cube`), so cutting the `latFt`-sum off by the ball and cutting it off
  by the box indicator give the same number (`Finset.sum_subset`).

Both characters `latChr ℓ n z` are *definitionally* `e^{i⟪kmomInt ℓ n, z⟫}`, and
`kmomLab ℓ N k` is *definitionally* `kmomInt ℓ (labVec N k)`, so no character identity has to be
proved.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Every coordinate of a lattice point is dominated by its Euclidean norm, hence the momentum
ball `latBall (N/4)` (of lattice points of norm at most `N/4`) lies inside the box
`cube N = [-N,N]³`. -/
private lemma latBall_div_four_subset_cube (N : ℕ) :
    LatFourier.latBall ((N : ℝ) / 4) ⊆ Work.BoseRowQ2.cube N := by
  intro m hm
  rw [Work.BoseRowQ2.mem_cube]
  intro i
  rw [LatFourier.mem_latBall] at hm
  have h1 := LatFourier.abs_coord_le_norm_latVec m i
  have h2 : ((N : ℝ) / 4) ≤ (N : ℝ) := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have h3 : |((m i : ℤ) : ℝ)| ≤ (N : ℝ) := le_trans h1 (le_trans hm h2)
  rw [abs_le] at h3
  exact ⟨by exact_mod_cast h3.1, by exact_mod_cast h3.2⟩

/-- **The pointwise identity**: the difference of the row sum and the momentum-ball partial sum is
the box-indexed character sum with coefficients `rhoCoef`. -/
private lemma rowSum_sub_ballSum_eq (ℓ : ℝ) (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (W : E3 → ℝ) :
    ∀ z : E3, rowSum ℓ fu N W z - ballSum ℓ N W z
      = ∑ n ∈ Work.BoseRowQ2.cube N, rhoCoef ℓ fu N W n *
          Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ)) := by
  intro z
  -- the row sum, reindexed from the label group onto the box
  have hrow : rowSum ℓ fu N W z
      = ∑ n ∈ Work.BoseRowQ2.cube N,
          ((uvCut fu (uvRad ℓ N) (kmomInt ℓ n) : ℝ) : ℂ) * LatFourier.latFt ℓ W n
            * latChr ℓ n z := by
    rw [show rowSum ℓ fu N W z
        = ∑ k : Lab N, ((uvCut fu (uvRad ℓ N) (kmomInt ℓ (labVec N k)) : ℝ) : ℂ)
            * LatFourier.latFt ℓ W (labVec N k) * latChr ℓ (labVec N k) z from rfl]
    rw [← Work.BoseRowQ2.image_labVec_eq_cube N]
    rw [Finset.sum_image (Work.BoseRowQ2.labVec_inj' N).injOn]
  -- the momentum-ball partial sum, extended by `0` to the box
  have hball : ballSum ℓ N W z
      = ∑ n ∈ Work.BoseRowQ2.cube N,
          (if n ∈ LatFourier.latBall ((N : ℝ) / 4) then LatFourier.latFt ℓ W n else 0)
            * latChr ℓ n z := by
    rw [show ballSum ℓ N W z
        = ∑ n ∈ LatFourier.latBall ((N : ℝ) / 4),
            LatFourier.latFt ℓ W n * latChr ℓ n z from rfl]
    rw [← Finset.sum_subset (latBall_div_four_subset_cube N) (fun x _ hx => by
      rw [if_neg hx, zero_mul])]
    exact Finset.sum_congr rfl fun x hx => by rw [if_pos hx]
  rw [hrow, hball, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [rhoCoef, latChr]
  ring

theorem latRowSum_parseval {ℓ : ℝ} (hℓ : 0 < ℓ) {fu : Work.BoseBoxFix.LowCut} (N : ℕ)
    (W : EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∫ z in Work.BoseBoxFock.LatFourier.latBox ℓ,
        ‖Work.BoseBoxFock.rowSum ℓ fu N W z - Work.BoseBoxFock.ballSum ℓ N W z‖ ^ 2)
      = ℓ ^ 3 * ∑ n ∈ Work.BoseRowQ2.cube N, ‖Work.BoseBoxFock.rhoCoef ℓ fu N W n‖ ^ 2 := by
  rw [show (∫ z in LatFourier.latBox ℓ, ‖rowSum ℓ fu N W z - ballSum ℓ N W z‖ ^ 2)
      = ∫ z in LatFourier.latBox ℓ,
          ‖∑ n ∈ Work.BoseRowQ2.cube N, rhoCoef ℓ fu N W n *
            Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))‖ ^ 2 from
    setIntegral_congr_fun (LatFourier.measurableSet_latBox ℓ)
      (fun z _ => by rw [rowSum_sub_ballSum_eq ℓ fu N W z])]
  exact latFinset_parseval_box hℓ (Work.BoseRowQ2.cube N) (rhoCoef ℓ fu N W)

end Work.BoseBoxFock
