import Mathlib
import Submission.Work.Serre.ratSerrePairComparison
import Submission.Work.Stems.product_ratH_vanishing
import Submission.Work.Rat.U.EM
import Submission.Work.RatHurewicz.coverRangeTransfer
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.Defs

set_option synthInstance.maxHeartbeats 400000

namespace Work.Rat.RankOneC1

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false

noncomputable section

/-- Path connectedness transports along a homeomorphism. -/
private theorem pathConnectedSpace_of_homeomorph {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (h : PathConnectedSpace B) : PathConnectedSpace A := by
  rw [pathConnectedSpace_iff_univ] at h ⊢
  have hh := h.image e.symm.continuous
  rwa [Set.image_univ, Set.range_eq_univ.mpr e.symm.surjective] at hh

/-- The unit circle `S¹` is path connected (it is `0`-connected). -/
private theorem sphOne_pathConnected : PathConnectedSpace (Work.Serre.Sph 1) := by
  obtain ⟨s₀, hs₀⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 2))
    (x := (0 : EuclideanSpace ℝ (Fin 2))) (r := 1)).mpr (by norm_num : (0 : ℝ) ≤ 1)
  let p₀ : Work.Serre.Sph 1 := ⟨s₀, hs₀⟩
  exact Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero p₀
    (Work.Stems.sphereConnectivity 1 0 (by norm_num) p₀)

/-- **The vanishing for the swapped product `Y × S¹`.**  If `Y` is `(2N+2)`-connected then
`H_t(Y × S¹;ℚ) = 0` for `2 ≤ t ≤ N`.

The proof runs the stable-range rational pair comparison
(`Work.Serre.ratSerrePairComparison`) for the projection `Y × S¹ → Y` onto the *highly connected*
factor: its fibre is `S¹`, so with base parameter `b = 2N+3` and fibre parameter `f = 1` the
comparison identifies `H_t(Y × S¹, Y × {s₀};ℚ) ≅ H_t(Y, {y₀};ℚ)` for every `t < 2N+4`.  Both
outer terms of the long exact sequence of the pair `(Y × S¹, Y × {s₀})` then vanish in the range
`2 ≤ t ≤ N`: `H_t(Y × {s₀};ℚ) = H_t(S¹;ℚ) = 0`, and `H_t(Y, {y₀};ℚ) = 0` because `H_t(Y;ℚ) = 0`
by Serre's `E0` in range (the Hurewicz vanishing for a `(2N+2)`-connected space). -/
private theorem sphOneProdVanishing_swap {Y : Type} [TopologicalSpace Y] (y₀ : Y) (N : ℕ)
    (hYc : Work.Serre.Conn Y y₀ (2 * N + 3)) :
    ∀ t : ℕ, 2 ≤ t → t ≤ N →
      IsZero (Work.Serre.ratH (TopCat.of (Y × Work.Serre.Sph 1)) t) := by
  intro t ht2 htN
  haveI hpcS : PathConnectedSpace (Work.Serre.Sph 1) := sphOne_pathConnected
  haveI hpcY : PathConnectedSpace Y :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero y₀ (hYc 0 (by omega))
  haveI hpcE : PathConnectedSpace (Y × Work.Serre.Sph 1) := inferInstance
  -- the fibre of the projection onto `Y`, homeomorphic to `S¹`
  have hfib0 : PathConnectedSpace
      (Work.StemsB.fibre (ContinuousMap.fst : C(Y × Work.Serre.Sph 1, Y)) y₀) :=
    pathConnectedSpace_of_homeomorph
      (Work.Stems.fibreHomeo Y (Work.Serre.Sph 1) y₀) hpcS
  have hfib : ∀ j : ℕ, 0 < j → j < 1 →
      IsZero (Work.Serre.ratH
        (TopCat.of (Work.StemsB.fibre (ContinuousMap.fst : C(Y × Work.Serre.Sph 1, Y)) y₀)) j) :=
    fun _ hj hj1 => absurd hj1 (by omega)
  -- the stable-range rational pair comparison, with base parameter `2N+3` and fibre parameter `1`
  have hpair := (Work.Serre.ratSerrePairComparison
      (ContinuousMap.fst : C(Y × Work.Serre.Sph 1, Y))
      (Work.StemsB.IsHurewiczFibration.isSerreFibration
        (Work.Stems.isHurewiczFibration_fst Y (Work.Serre.Sph 1)))
      y₀ (2 * N + 3) 1 (by omega) (by omega) hpcE hpcY hYc hfib0 hfib).1 t (by omega)
  -- `H_t(Y;ℚ) = 0` by Serre's `E0` in range
  have hYt : IsZero (Work.Serre.ratH (TopCat.of Y) t) :=
    Work.Serre.serreE0Range Y y₀ (2 * N + 2) (fun i hi => hYc i (by omega)) t (by omega) (by omega)
  have hYrel : IsZero
      ((Work.StemsB.relChainsR ℚ (TopCat.of Y) ({y₀} : Set Y)).homology t) :=
    Work.Stems.isZero_relChainsR_homology_of_isZero_abs ℚ (TopCat.of Y) ({y₀} : Set Y) t
      (by omega) hYt (Work.Stems.isZero_ratH_singleton Y y₀ (j := t - 1) (by omega))
  -- hence the relative homology of `(Y × S¹, Y × {s₀})` vanishes in degree `t`
  have hrelE : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (Y × Work.Serre.Sph 1))
      ((ContinuousMap.fst : C(Y × Work.Serre.Sph 1, Y)) ⁻¹' ({y₀} : Set Y))).homology t) := by
    obtain ⟨e⟩ := hpair
    exact IsZero.of_iso hYrel e
  -- and `H_t(Y × {s₀};ℚ) = H_t(S¹;ℚ) = 0`
  have hfibH : IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of
      ↥(((ContinuousMap.fst : C(Y × Work.Serre.Sph 1, Y)) ⁻¹' ({y₀} : Set Y))))).homology t) :=
    Work.Stems.isZero_ratH_of_homeomorph (Work.Stems.fibreHomeo Y (Work.Serre.Sph 1) y₀) t
      (Work.RatHurewicz.isZero_ratH_sph_bottom (k := 1) (j := t)
        (by norm_num) (by omega) (by omega))
  -- the long exact sequence of the pair `(Y × S¹, Y × {s₀})` finishes the job
  have hS := Work.StemsB.relChainsR_exact₂ ℚ (TopCat.of (Y × Work.Serre.Sph 1))
    (((ContinuousMap.fst : C(Y × Work.Serre.Sph 1, Y)) ⁻¹' ({y₀} : Set Y))) t
  exact hS.isZero_X₂ (hfibH.eq_zero_of_src _) (hrelE.eq_zero_of_tgt _)

theorem sphOneProdVanishing {Y : Type} [TopologicalSpace Y] (y₀ : Y) (N : ℕ)
    (hYc : Work.Serre.Conn Y y₀ (2 * N + 3)) :
    ∀ t : ℕ, 2 ≤ t → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.Serre.Sph 1 × Y)) t) := by
  intro t ht2 htN
  exact Work.Stems.isZero_ratH_of_homeomorph (Homeomorph.prodComm (Work.Serre.Sph 1) Y) t
    (sphOneProdVanishing_swap y₀ N hYc t ht2 htN)

end

end Work.Rat.RankOneC1
