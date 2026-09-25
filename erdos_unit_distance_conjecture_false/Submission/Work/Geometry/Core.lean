import Mathlib
import Submission.Work.Defs.Basic
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts
import Submission.Work.Geometry.WindowScale
import Submission.Work.Geometry.volume_window_one
import Submission.Work.Geometry.volume_window_pos_ne_top
import Submission.Work.Geometry.finite_Xset
import Submission.Work.Geometry.lintegral_pointCount
import Submission.Work.Geometry.lintegral_pairCountOne
import Submission.Work.Geometry.pointCount_eq_coe_pointCard
import Submission.Work.Geometry.pairCount_eq_coe_pairCard
import Submission.Work.Geometry.ncard_PairSet_le
import Submission.Work.Geometry.aemeasurable_pointCount
import Submission.Work.Geometry.aemeasurable_pairCount
import Submission.Work.Geometry.exists_le_of_lintegral_le
import Submission.Work.Geometry.ncard_Xset_le
import Submission.Work.Geometry.volume_Window_sub_half_le_WindowShift
import Submission.Work.Geometry.two_mul_cDist
import Submission.Work.Geometry.exists_finset_cDist_le_of_Xset

/-!
# The geometric core of the unit-distance construction

This is Section 2 of *Planar Point Sets with Many Unit Distances*: given a CM field `K`, a
fractional ideal `I` of `𝓞 K` (playing the role of `D⁻¹𝒪_K`), a finite set `U ⊆ I` of
"norm one" elements (`u · conj u = 1`, so `|σ(u)| = 1` at every infinite place) and a
separation parameter `D ≥ 1/R`, there is a planar point set `P` obtained by projecting a
suitable coset of the lattice `Φ(I)` cut by the polydisc `B_R` to a complex coordinate, with

* `|P| ≤ (4 R D)^{[K:ℚ]}` points, and
* `2⁻¹ · |U| · (1 - 1/(2R))^{[K:ℚ]} · |P|` unit distances.

This packages Lemma 2.4 (averaging), Lemma 2.5 (projection) and Lemma 2.6 (packing) of the
paper.
-/

set_option linter.unusedSectionVars false

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Geometry

open scoped Pointwise

/-- The geometric core, with the additional information that the point set is nonempty
(indeed `1 ≤ P.card`).  This is the form used to deduce that the number of points tends to
infinity: averaging produces a coset whose point count is at least one. -/
theorem geometric_core_card_pos (K : Type*) [Field K] [NumberField K] [IsCMField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R D : ℝ) (hR : 1/2 < R) (hD : 0 < D) (hRD : 1 ≤ R * D)
    (U : Finset K) (hU : ∀ u ∈ U, u ∈ (I : Set K))
    (hU1 : ∀ u ∈ U, u * IsCMField.complexConj K u = 1)
    (hsep : ∀ β ∈ (I : Set K), β ≠ 0 →
      ∃ w : InfinitePlace K, 1/D ≤ mixedEmbedding.normAtPlace w (mixedEmbedding K β))
    (w₀ : InfinitePlace K) :
    ∃ P : Finset ℂ, 0 < P.card ∧ (P.card : ℝ) ≤ (4 * R * D) ^ (Module.finrank ℚ K) ∧
      2⁻¹ * (U.card : ℝ) * (1 - 1/(2*R)) ^ (Module.finrank ℚ K) * (P.card : ℝ)
        ≤ (Work.Defs.cDist P : ℝ) := by
  have hR0 : 0 < R := by linarith
  -- the constant `(1 - 1/(2R))^[K:ℚ]` and its nonnegativity
  have hρnn : 0 ≤ (1 - 1/(2*R)) ^ Module.finrank ℚ K := by
    apply pow_nonneg
    have : 1/(2*R) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hC : 0 ≤ (U.card : ℝ) * (1 - 1/(2*R)) ^ Module.finrank ℚ K :=
    mul_nonneg (Nat.cast_nonneg U.card) hρnn
  -- positivity and finiteness of the volume of the window
  have hVpos : 0 < volume (Window K R) := (volume_window_pos_ne_top K R hR0).1
  have hVtop : volume (Window K R) ≠ ⊤ := (volume_window_pos_ne_top K R hR0).2
  -- the unfolding identities and the conversion to cardinalities
  have hpoint : ∫⁻ a in Fund K I, pointCount K I R a = volume (Window K R) :=
    lintegral_pointCount K I R
  have hpc : ∀ a, pointCount K I R a = (pointCard K I R a : ENNReal) :=
    fun a => pointCount_eq_coe_pointCard K I R a (finite_Xset K I R a)
  have hpe : ∀ a, pairCount K I R U a = (pairCard K I R U a : ENNReal) :=
    fun a => pairCount_eq_coe_pairCard K I R U a (finite_Xset K I R a) hU
  have hpoint' : ∫⁻ a in Fund K I, (pointCard K I R a : ENNReal) = volume (Window K R) := by
    rw [← hpoint]
    exact lintegral_congr_ae (Filter.Eventually.of_forall (fun a => (hpc a).symm))
  -- measurability of the counts
  have hmeas_one : ∀ u : K, Measurable (fun a => pairCountOne K I R a u) := by
    intro u
    unfold pairCountOne
    apply Measurable.tsum
    intro l
    apply Measurable.mul
    · exact ((measurable_const.indicator (measurableSet_window R))).comp (measurable_add_const _)
    · exact ((measurable_const.indicator (measurableSet_window R))).comp
        ((measurable_add_const _).add_const _)
  have hae_pc : AEMeasurable (fun a => (pointCard K I R a : ENNReal))
      (volume.restrict (Fund K I)) :=
    ((aemeasurable_pointCount K I R).congr
      (Filter.Eventually.of_forall (fun a => hpc a))).restrict
  have hae_pe : AEMeasurable (fun a => (pairCard K I R U a : ENNReal))
      (volume.restrict (Fund K I)) :=
    ((aemeasurable_pairCount K I R U).congr
      (Filter.Eventually.of_forall (fun a => hpe a))).restrict
  -- the pair count is bounded below by `(1 - 1/(2R))^[K:ℚ]` times the volume of the window
  have hsummand : ∀ u ∈ U,
      ENNReal.ofReal ((1 - 1/(2*R)) ^ Module.finrank ℚ K) * volume (Window K R)
        ≤ ∫⁻ a in Fund K I, pairCountOne K I R a u := by
    intro u hu
    rw [lintegral_pairCountOne K I R u, volume_Window_sub_half (K := K) R hR]
    exact volume_Window_sub_half_le_WindowShift K hR
      (fun w => normAtPlace_eq_one_of_mul_complexConj u (hU1 u hu) w)
  have hpair_le : (U.card : ENNReal) *
      (ENNReal.ofReal ((1 - 1/(2*R)) ^ Module.finrank ℚ K) * volume (Window K R))
        ≤ ∑ u ∈ U, ∫⁻ a in Fund K I, pairCountOne K I R a u := by
    have h1 := Finset.sum_le_sum hsummand
    rwa [Finset.sum_const, nsmul_eq_mul] at h1
  have hpair : ENNReal.ofReal ((U.card : ℝ) * (1 - 1/(2*R)) ^ Module.finrank ℚ K) *
      (∫⁻ a in Fund K I, pointCount K I R a) ≤ ∫⁻ a in Fund K I, pairCount K I R U a := by
    rw [hpoint]
    have hunfold : ∫⁻ a in Fund K I, pairCount K I R U a
        = ∑ u ∈ U, ∫⁻ a in Fund K I, pairCountOne K I R a u := by
      simp only [pairCount]
      exact lintegral_finsetSum _ (fun u _ => hmeas_one u)
    rw [hunfold]
    have hLHS : ENNReal.ofReal ((U.card : ℝ) * (1 - 1/(2*R)) ^ Module.finrank ℚ K)
          * volume (Window K R)
        = (U.card : ENNReal) *
          (ENNReal.ofReal ((1 - 1/(2*R)) ^ Module.finrank ℚ K) * volume (Window K R)) := by
      rw [ENNReal.ofReal_mul (p := (U.card : ℝ))
        (q := (1 - 1/(2*R)) ^ Module.finrank ℚ K) (by positivity),
        ENNReal.ofReal_natCast, mul_assoc]
    rw [hLHS]
    exact hpair_le
  have hpair_card : ENNReal.ofReal ((U.card : ℝ) * (1 - 1/(2*R)) ^ Module.finrank ℚ K) *
      (∫⁻ a in Fund K I, (pointCard K I R a : ENNReal))
        ≤ ∫⁻ a in Fund K I, (pairCard K I R U a : ENNReal) := by
    have h1 : ∫⁻ a in Fund K I, (pointCard K I R a : ENNReal)
        = ∫⁻ a in Fund K I, pointCount K I R a :=
      lintegral_congr_ae (Filter.Eventually.of_forall (fun a => (hpc a).symm))
    have h2 : ∫⁻ a in Fund K I, (pairCard K I R U a : ENNReal)
        = ∫⁻ a in Fund K I, pairCount K I R U a :=
      lintegral_congr_ae (Filter.Eventually.of_forall (fun a => (hpe a).symm))
    rw [h1, h2]
    exact hpair
  -- pointwise bounds for the extraction step
  have hK0 : ∀ a ∈ Fund K I, pointCard K I R a
      ≤ Nat.ceil ((4 * R * D) ^ Module.finrank ℚ K) := by
    intro a _
    rw [pointCard]
    refine Nat.cast_le.mp (le_trans ?_ (Nat.le_ceil _))
    exact ncard_Xset_le K I R D hD hRD hsep a
  have heK : ∀ a ∈ Fund K I, pairCard K I R U a ≤ pointCard K I R a * pointCard K I R a := by
    intro a _
    rw [pairCard, pointCard]
    exact ncard_PairSet_le K I R U a (finite_Xset K I R a)
  have hpos : 0 < ∫⁻ a in Fund K I, (pointCard K I R a : ENNReal) := by
    rw [hpoint']; exact hVpos
  have hfin : ∫⁻ a in Fund K I, (pointCard K I R a : ENNReal) < ⊤ := by
    rw [hpoint']; exact lt_top_iff_ne_top.mpr hVtop
  -- averaging gives a coset where the pair count dominates
  obtain ⟨a, -, ha1, ha2⟩ := exists_le_of_lintegral_le volume (Fund K I)
    (pointCard K I R) (pairCard K I R U)
    ((U.card : ℝ) * (1 - 1/(2*R)) ^ Module.finrank ℚ K) hC
    (Nat.ceil ((4 * R * D) ^ Module.finrank ℚ K))
    hae_pc hae_pe hK0 heK hpos hfin hpair_card
  -- project the coset to the `w₀`-coordinate
  have hw₀ : w₀.IsComplex := (IsCMField.isTotallyComplex K).isComplex w₀
  obtain ⟨P, hPcard, hPle⟩ :=
    exists_finset_cDist_le_of_Xset K w₀ hw₀ I R U a hU hU1 (finite_Xset K I R a)
  refine ⟨P, ?_, ?_, ?_⟩
  · have : 1 ≤ P.card := by rw [hPcard]; exact ha1
    omega
  · rw [hPcard]
    exact ncard_Xset_le K I R D hD hRD hsep a
  · have hcast : (P.card : ℝ) = (pointCard K I R a : ℝ) := by
      rw [hPcard, pointCard]
    have hple : (pairCard K I R U a : ℝ) ≤ 2 * (Work.Defs.cDist P : ℝ) := by
      rw [pairCard]
      exact_mod_cast hPle
    have hmain : ((U.card : ℝ) * (1 - 1/(2*R)) ^ Module.finrank ℚ K) * (P.card : ℝ)
        ≤ 2 * (Work.Defs.cDist P : ℝ) := by
      calc ((U.card : ℝ) * (1 - 1/(2*R)) ^ Module.finrank ℚ K) * (P.card : ℝ)
          = ((U.card : ℝ) * (1 - 1/(2*R)) ^ Module.finrank ℚ K)
              * (pointCard K I R a : ℝ) := by rw [hcast]
        _ ≤ (pairCard K I R U a : ℝ) := ha2
        _ ≤ 2 * (Work.Defs.cDist P : ℝ) := hple
    linarith

/-- **The geometric core of the construction** (paper §2, Lemmas 2.4, 2.5, 2.6). -/
theorem geometric_core (K : Type*) [Field K] [NumberField K] [IsCMField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R D : ℝ) (hR : 1/2 < R) (hD : 0 < D) (hRD : 1 ≤ R * D)
    (U : Finset K) (hU : ∀ u ∈ U, u ∈ (I : Set K))
    (hU1 : ∀ u ∈ U, u * IsCMField.complexConj K u = 1)
    (hsep : ∀ β ∈ (I : Set K), β ≠ 0 →
      ∃ w : InfinitePlace K, 1/D ≤ mixedEmbedding.normAtPlace w (mixedEmbedding K β))
    (w₀ : InfinitePlace K) :
    ∃ P : Finset ℂ, (P.card : ℝ) ≤ (4 * R * D) ^ (Module.finrank ℚ K) ∧
      2⁻¹ * (U.card : ℝ) * (1 - 1/(2*R)) ^ (Module.finrank ℚ K) * (P.card : ℝ)
        ≤ (Work.Defs.cDist P : ℝ) := by
  obtain ⟨P, -, h1, h2⟩ := geometric_core_card_pos K I R D hR hD hRD U hU hU1 hsep w₀
  exact ⟨P, h1, h2⟩

end Geometry
end Work
