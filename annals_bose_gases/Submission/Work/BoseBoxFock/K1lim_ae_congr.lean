import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pinQLimDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1lim_ae_congr` — the a.e. congruence of the limit pair kernel

`K1lim ℓ W` (`pinQLimDefs.lean`) depends on the weight `W` in two ways:

* through the three lattice sums `pinQBl/pinQCl/pinQDl`, whose only `W`-dependence is via
  `Work.BoseFixR.chat W (kmomInt ℓ n) = ∫ e^{−i⟪k,y⟫}W y dy` — an integral, hence invariant under an
  a.e. change of `W`;
* through the periodisation `latPer3 ℓ W (w − y) = ℓ³∑_m W (w − y + ℓ•latVec m)` — a lattice sum, so
  the (countably many) shifts of the null set where `W₁ ≠ W₂` must be avoided.

The second point is the only measure-theoretic content: if `N` is null then
`{(w,y) : w − y + c ∈ N}` is null for the product measure.  This is proved by Fubini
(`Measure.prod_apply_symm`), using that the section at `y` is the translate `N − c + y` of a null set.
-/

set_option maxHeartbeats 1000000

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- If `N` is a null set of `E3` and `c : E3`, then `{(w,y) : w − y + c ∈ N}` is null for the
product measure `volume.prod volume`.  (Fubini; the section at fixed `y` is the translate
`N − c + y`.) -/
lemma measure_prod_sub_add_mem_null {N : Set E3} (hN : volume N = 0) (c : E3) :
    (volume.prod volume) {p : E3 × E3 | p.1 - p.2 + c ∈ N} = 0 := by
  have hN'm : MeasurableSet (toMeasurable volume N) := measurableSet_toMeasurable volume N
  have hN'sub : N ⊆ toMeasurable volume N := subset_toMeasurable volume N
  have hN'0 : volume (toMeasurable volume N) = 0 := by
    rw [measure_toMeasurable]; exact hN
  refine measure_mono_null (s := {p : E3 × E3 | p.1 - p.2 + c ∈ N})
    (t := {p : E3 × E3 | p.1 - p.2 + c ∈ toMeasurable volume N}) ?_ ?_
  · intro p hp; exact hN'sub hp
  · have hmeas : MeasurableSet {p : E3 × E3 | p.1 - p.2 + c ∈ toMeasurable volume N} :=
      hN'm.preimage (by fun_prop)
    rw [MeasureTheory.Measure.prod_apply_symm hmeas]
    have hsec : ∀ y : E3,
        volume ((fun x : E3 => (x, y)) ⁻¹' {p : E3 × E3 | p.1 - p.2 + c ∈
          toMeasurable volume N}) = 0 := by
      intro y
      have hset : (fun x : E3 => (x, y)) ⁻¹' {p : E3 × E3 | p.1 - p.2 + c ∈
            toMeasurable volume N}
          = (fun x : E3 => (c - y) + x) ⁻¹' (toMeasurable volume N) := by
        ext x
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        rw [show x - y + c = (c - y) + x by abel]
      rw [hset, MeasureTheory.measure_preimage_add]
      exact hN'0
    simp only [hsec, lintegral_zero]

/-- The periodisation only depends on the a.e. class of the weight, in the difference variable
`p ↦ p.1 − p.2`. -/
lemma latPer_ae_congr_sub {ℓ : ℝ} {W₁ W₂ : E3 → ℝ} (h : W₁ =ᵐ[volume] W₂) :
    (fun p : E3 × E3 => LatFourier.latPer ℓ W₁ (p.1 - p.2))
      =ᵐ[volume.prod volume]
    (fun p : E3 × E3 => LatFourier.latPer ℓ W₂ (p.1 - p.2)) := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h
  have hN'm : MeasurableSet (toMeasurable volume {x : E3 | ¬ (W₁ x = W₂ x)}) :=
    measurableSet_toMeasurable _ _
  have hN'sub : {x : E3 | ¬ (W₁ x = W₂ x)} ⊆ toMeasurable volume {x : E3 | ¬ (W₁ x = W₂ x)} :=
    subset_toMeasurable _ _
  have hN'0 : volume (toMeasurable volume {x : E3 | ¬ (W₁ x = W₂ x)}) = 0 := by
    rw [measure_toMeasurable]; exact h
  set Bad : Set (E3 × E3) :=
    ⋃ m : Fin 3 → ℤ, {p : E3 × E3 | p.1 - p.2 + ℓ • latVec m ∈
      toMeasurable volume {x : E3 | ¬ (W₁ x = W₂ x)}} with hBaddef
  have hBad0 : (volume.prod volume) Bad = 0 := by
    rw [hBaddef]
    apply measure_iUnion_null
    intro m
    exact measure_prod_sub_add_mem_null hN'0 (ℓ • latVec m)
  show ∀ᵐ p ∂(volume.prod volume),
    LatFourier.latPer ℓ W₁ (p.1 - p.2) = LatFourier.latPer ℓ W₂ (p.1 - p.2)
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (s := {p : E3 × E3 | ¬ (LatFourier.latPer ℓ W₁ (p.1 - p.2)
      = LatFourier.latPer ℓ W₂ (p.1 - p.2))}) (t := Bad) ?_ hBad0
  intro p hp
  by_contra hcon
  apply hp
  apply tsum_congr
  intro m
  have hval : W₁ (p.1 - p.2 + ℓ • latVec m) = W₂ (p.1 - p.2 + ℓ • latVec m) := by
    by_contra hne
    exact hcon (by rw [hBaddef]; exact Set.mem_iUnion.mpr ⟨m, hN'sub hne⟩)
  rw [hval]

/-- The `p`-convention Fourier transform `chat` only depends on the a.e. class of its argument. -/
lemma chat_congr {W₁ W₂ : E3 → ℝ} (h : W₁ =ᵐ[volume] W₂) (k : E3) :
    Work.BoseFixR.chat W₁ k = Work.BoseFixR.chat W₂ k := by
  simp only [Work.BoseFixR.chat, Submission.BoseGases.kinFT]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

theorem K1lim_ae_congr {ℓ : ℝ} {W₁ W₂ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hm : MeasureTheory.AEStronglyMeasurable W₁ MeasureTheory.volume)
    (hb : ∃ C : ℝ, ∀ x, ‖W₁ x‖ ≤ C) (hs : HasCompactSupport W₁)
    (h : W₁ =ᵐ[MeasureTheory.volume] W₂) :
    (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBoxFock.K1lim ℓ W₁ p.1 p.2)
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
    (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBoxFock.K1lim ℓ W₂ p.1 p.2) := by
  have hchat : ∀ k : E3, Work.BoseFixR.chat W₁ k = Work.BoseFixR.chat W₂ k :=
    fun k => chat_congr h k
  have hB : pinQBl ℓ W₁ = pinQBl ℓ W₂ := by
    funext w
    apply tsum_congr
    intro n
    rw [hchat (kmomInt ℓ n)]
  have hC : pinQCl ℓ W₁ = pinQCl ℓ W₂ := by
    funext y
    apply tsum_congr
    intro n
    rw [hchat (kmomInt ℓ n)]
  have hD : pinQDl ℓ W₁ = pinQDl ℓ W₂ := by
    apply tsum_congr
    intro n
    rw [hchat (kmomInt ℓ n)]
  filter_upwards [latPer_ae_congr_sub (ℓ := ℓ) h] with p hp
  simp only [K1lim, latPer3, hB, hC, hD, hp]

end Work.BoseBoxFock
