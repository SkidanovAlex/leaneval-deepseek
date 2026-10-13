/-
Copyright: work module for the Elgindi finite-time singularity project.

# The general mixed angular slot bound, assembled

`Work.FTS.EllSol.PkgK5.mixedSlotLevel` is the level-`i` mixed-slot estimate of
`Work.FTS.H2.DivSinQR.mixedSlotBoundIθ` (there proved only for `i ≤ 4`), obtained by the strong
induction whose step is `Work.FTS.EllSol.PkgK5.levelBnd_step`.

`Work.FTS.EllSol.PkgK5.mixedSlotBoundGenK` is the same statement in the exact shape required by
the per-slice division estimate `Work.FTS.EllSol.perSliceCmp`
(`Submission/Work/FTS/EllSol/DivSinOpenPerZGroup.lean`), i.e. the general-`k` form of
`Work.FTS.EllSol.mixedSlotBoundGen` with a single constant serving all levels `i ≤ k`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.PkgK5.mixedSlotGen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The bundled level-`i` bound holds for every `i ≥ 1`. -/
theorem levelBnd_all : ∀ i : ℕ, 1 ≤ i → LevelBnd i := by
  intro i
  refine Nat.strong_induction_on i ?_
  intro i ih hi
  rcases eq_or_lt_of_le hi with h1 | h2
  · subst h1
    exact levelBnd_one
  · have hi1 : 1 ≤ i - 1 := by omega
    exact levelBnd_step i (by omega) (ih (i - 1) (by omega) hi1)

/-- **The mixed angular slot bound at level `i`.** -/
theorem mixedSlotLevel (i : ℕ) (hi : 1 ≤ i) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2)) →
      Tendsto h (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (etaInt h) Work.Spaces.Iθ →
      (∀ m : ℕ, 1 ≤ m → m ≤ i → MeasureTheory.IntegrableOn (gamInt α m h) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (lhsInt α i h) Work.Spaces.Iθ ∧
      pLhs α i h ≤ C * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) := by
  obtain ⟨C, hCpos, hC⟩ := levelBnd_all i hi
  exact ⟨C, hCpos, fun α h hα hα1 hsm h0 hπ hD hG =>
    hC α h hα hα1 hsm h0 hπ hD hG i hi le_rfl⟩

/-- **The general-`k` mixed slot bound** in the shape required by the per-slice division
estimate: a single constant `C` serves all levels `i ≤ k`. -/
theorem mixedSlotBoundGenK (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto h (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        Work.Spaces.Iθ →
      ∀ i : ℕ, 1 ≤ i → i ≤ k →
        (∀ m : ℕ, 1 ≤ m → m ≤ i → MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter i (fun θ' => h θ' / Real.sin (2 * θ')) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  have hex : ∀ i : ℕ, 1 ≤ i → ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
        ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2)) →
        Tendsto h (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
        Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
        MeasureTheory.IntegrableOn (etaInt h) Work.Spaces.Iθ →
        (∀ m : ℕ, 1 ≤ m → m ≤ i → MeasureTheory.IntegrableOn (gamInt α m h) Work.Spaces.Iθ) →
        MeasureTheory.IntegrableOn (lhsInt α i h) Work.Spaces.Iθ ∧
        pLhs α i h ≤ C * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) :=
    fun i hi => mixedSlotLevel i hi
  let Kf : ℕ → ℝ := fun i => if hi : 1 ≤ i then (hex i hi).choose else 1
  have hKf : ∀ i (hi : 1 ≤ i), 0 < Kf i ∧
      ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
        ContDiffOn ℝ (↑(⊤ : ℕ∞)) h (Set.Ioo 0 (Real.pi / 2)) →
        Tendsto h (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
        Tendsto h (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
        MeasureTheory.IntegrableOn (etaInt h) Work.Spaces.Iθ →
        (∀ m : ℕ, 1 ≤ m → m ≤ i → MeasureTheory.IntegrableOn (gamInt α m h) Work.Spaces.Iθ) →
        MeasureTheory.IntegrableOn (lhsInt α i h) Work.Spaces.Iθ ∧
        pLhs α i h ≤ Kf i * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h) := by
    intro i hi
    have h1 : Kf i = (hex i hi).choose := by
      dsimp only [Kf]
      exact dif_pos hi
    rw [h1]
    exact (hex i hi).choose_spec
  have hnn : ∀ j ∈ Finset.Icc 1 k, 0 ≤ Kf j := fun j hj =>
    le_of_lt (hKf j (Finset.mem_Icc.mp hj).1).1
  have hSnn : 0 ≤ ∑ j ∈ Finset.Icc 1 k, Kf j := Finset.sum_nonneg hnn
  refine ⟨(∑ j ∈ Finset.Icc 1 k, Kf j) + 1, by linarith, ?_⟩
  intro α h hα hα1 hsm h0 hπ hD i hi1 hik hG
  obtain ⟨hpos, hb⟩ := hKf i hi1
  obtain ⟨hint, hbd⟩ := hb α h hα hα1 hsm h0 hπ hD hG
  have hle : Kf i ≤ (∑ j ∈ Finset.Icc 1 k, Kf j) + 1 := by
    have hsingle := Finset.single_le_sum hnn (Finset.mem_Icc.mpr ⟨hi1, hik⟩)
    linarith
  have hXnn : 0 ≤ pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h :=
    add_nonneg (pEta_nonneg h) (Finset.sum_nonneg (fun m _ => pGam_nonneg α m h))
  refine ⟨?_, ?_⟩
  · change MeasureTheory.IntegrableOn (lhsInt α i h) Work.Spaces.Iθ
    exact hint
  · change pLhs α i h ≤ ((∑ j ∈ Finset.Icc 1 k, Kf j) + 1)
        * (pEta h + ∑ m ∈ Finset.Icc 1 i, pGam α m h)
    exact hbd.trans (mul_le_mul_of_nonneg_right hle hXnn)

end Work.FTS.EllSol.PkgK5
