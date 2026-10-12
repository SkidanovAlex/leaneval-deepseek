import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.BoseBox.fsT_fibre_aemeasurable
import Submission.Work.BoseBox.tKinAmbFourierDecay
import Submission.Work.BoseBox.tKinAmbWordBound
import Submission.Work.BoseKinLoc.Volume.volume_coverU
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.tKinAmbIntegrable`

The localised kinetic word `tKinAmb` of the `C` node (FS's `𝒯_u`, the `N`-body lift
`Σᵢ(𝒯_u)^{(i)}` of the one-body word `Work.BoseKinLoc.fsT`) is `u`-integrable on the
localisation region `coverU ℓ L`.

The route (all pieces machine-checked in this file or imported):

1. `coverU ℓ L` is the coordinate box `[−1/2, L/ℓ+1/2]³` (`mem_coverU_iff_coord`), hence
   measurable (`measurableSet_coverU`) with finite volume (`volume_coverU_lt_top`);
2. `u ↦ tKinAmb … u Ψ` is a.e. strongly measurable (`tKinAmbAEMeasurable`);
3. it is bounded on `coverU ℓ L` (`tKinAmbWordBound`), from the uniform `(1+‖p‖)⁻³` Fourier decay
   of the windowed amplitude (`tKinAmbFourierDecay`);
4. `MeasureTheory.IntegrableOn.of_bound` assembles the three.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology

namespace Work.BoseBox

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1  The localisation region `coverU ℓ L` as a coordinate box -/

/-- **Coordinate description of the localisation region.**  For `ℓ > 0`, `u ∈ coverU ℓ L` iff
every coordinate of `u` lies in `[−1/2, L/ℓ + 1/2]`: the box `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` meets
`[0,L]³` exactly when `ℓu_k ∈ [−ℓ/2, L+ℓ/2]` for all `k`. -/
lemma mem_coverU_iff_coord {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (u : EuclideanSpace ℝ (Fin 3)) :
    u ∈ coverU ℓ L ↔
      ∀ k : Fin 3, u k ∈ Set.Icc (-(1 / 2 : ℝ)) (L / ℓ + 1 / 2) := by
  constructor
  · rintro ⟨x, hx, hxu⟩ k
    have hxk : 0 ≤ x k ∧ x k ≤ L := Set.mem_Icc.mp (hx k)
    have hk : -ℓ / 2 ≤ (x - ℓ • u) k ∧ (x - ℓ • u) k ≤ ℓ / 2 := Set.mem_Icc.mp (hxu k)
    rw [show (x - ℓ • u) k = x k - ℓ * u k by simp] at hk
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · have h1 : ℓ * (-(1 / 2)) ≤ ℓ * u k := by linarith [hk.2, hxk.1]
      exact le_of_mul_le_mul_left h1 hℓ
    · have h1 : ℓ * u k ≤ ℓ * (L / ℓ + 1 / 2) := by
        have he : ℓ * (L / ℓ + 1 / 2) = L + ℓ / 2 := by field_simp
        linarith [hk.1, hxk.2, he]
      exact le_of_mul_le_mul_left h1 hℓ
  · intro hu
    refine ⟨WithLp.toLp 2 (fun k : Fin 3 => max 0 (min L (ℓ * u k))), ?_, ?_⟩
    · intro k
      exact Set.mem_Icc.mpr ⟨le_max_left _ _, max_le hL.le (min_le_left _ _)⟩
    · intro k
      have huk : -(1 / 2) ≤ u k ∧ u k ≤ L / ℓ + 1 / 2 := hu k
      have htlo : -(ℓ / 2) ≤ ℓ * u k := by
        have := mul_le_mul_of_nonneg_left huk.1 hℓ.le
        linarith
      have hthi : ℓ * u k ≤ L + ℓ / 2 := by
        have h := mul_le_mul_of_nonneg_left huk.2 hℓ.le
        have he : ℓ * (L / ℓ + 1 / 2) = L + ℓ / 2 := by field_simp
        linarith [h, he]
      rw [Set.mem_Icc]
      rw [show (WithLp.toLp 2 (fun k : Fin 3 => max 0 (min L (ℓ * u k))) - ℓ • u) k
            = max 0 (min L (ℓ * u k)) - ℓ * u k by simp]
      by_cases h0 : ℓ * u k < 0
      · have hmin : min L (ℓ * u k) = ℓ * u k := min_eq_right (by linarith)
        have hmax : max 0 (ℓ * u k) = 0 := max_eq_left h0.le
        rw [hmin, hmax]
        constructor <;> linarith
      · by_cases hL' : L < ℓ * u k
        · have hmin : min L (ℓ * u k) = L := min_eq_left hL'.le
          have hmax : max 0 L = L := max_eq_right hL.le
          rw [hmin, hmax]
          constructor <;> linarith
        · have h0' : 0 ≤ ℓ * u k := le_of_not_gt h0
          have hL'' : ℓ * u k ≤ L := le_of_not_gt hL'
          have hmin : min L (ℓ * u k) = ℓ * u k := min_eq_right hL''
          have hmax : max 0 (ℓ * u k) = ℓ * u k := max_eq_right h0'
          rw [hmin, hmax]
          constructor <;> linarith

/-- **The localisation region is a closed coordinate box, hence measurable.** -/
lemma measurableSet_coverU {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) :
    MeasurableSet (coverU ℓ L) := by
  have hset : coverU ℓ L = WithLp.ofLp ⁻¹'
      (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-(1 / 2 : ℝ)) (L / ℓ + 1 / 2))) := by
    ext u
    rw [Set.mem_preimage, Set.mem_univ_pi]
    exact mem_coverU_iff_coord hℓ hL u
  rw [hset]
  exact (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)).preimage
    (by fun_prop)

/-- The volume of `coverU ℓ L` is finite (indeed `(L+ℓ)³/ℓ³`). -/
lemma volume_coverU_lt_top {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) (coverU ℓ L) < ⊤ := by
  have hEq : coverU ℓ L = Work.BoseKinLoc.coverU ℓ L := rfl
  rw [hEq, Work.BoseKinLoc.Volume.volume_coverU hℓ hL.le]
  exact ENNReal.ofReal_lt_top

/-! ## 2  A.e. strong measurability of the word in the translation parameter

`tKinAmb = kinForm = Σᵢ slotForm (fsT · u)` and the slot integral peels to the fibre integral
`slotForm (n+1) q ℓ u i Ψ = ∫_r q (z ↦ Ψ(kcInsN n i (z,r)))`
(`Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral`).  The fibre measurability of the one-body
word `fsT` (`Work.BoseBox.fsT_fibre_aemeasurable`) therefore gives the measurability of each slot,
and `AEStronglyMeasurable.integral_prod_right'` integrates out the remaining configuration. -/

/-- **A.e. strong measurability of `u ↦ tKinAmb … u Ψ`.** -/
theorem tKinAmb_aestronglyMeasurable {N : ℕ} {L ℓ d s eT b : ℝ} (hL : 0 < L) (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hsupp : tsupport Ψ ⊆ _root_.BoseGases.box N L) :
    MeasureTheory.AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseBox.tKinAmb N L ℓ d s eT b u Ψ)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  have hcs : HasCompactSupport Ψ :=
    HasCompactSupport.of_support_subset_isCompact (Submission.BoseGases.box_compact hL)
      ((subset_tsupport Ψ).trans hsupp)
  rcases N with _ | n
  · -- `N = 0`: the word is the empty sum
    have hzero : (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBox.tKinAmb 0 L ℓ d s eT b u Ψ) = fun _ => 0 := by
      funext u
      simp [Work.BoseBox.tKinAmb, Work.BoseBox.tKinWord, Work.BoseKinLoc.kinForm]
    rw [hzero]
    exact aestronglyMeasurable_const
  · -- `N = n + 1`: each slot is a fibre integral
    have hterm : ∀ i : Fin (n + 1), MeasureTheory.AEStronglyMeasurable
        (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s eT b u) ℓ u i Ψ)
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
      intro i
      have h1 : MeasureTheory.AEStronglyMeasurable
          (fun u : EuclideanSpace ℝ (Fin 3) => ∫ r : Submission.BoseGases.X n,
            Work.BoseKinLoc.fsT ℓ d s eT b u
              (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Submission.BoseGases.kcInsN n i (z, r))))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
        (Work.BoseBox.fsT_fibre_aemeasurable (d := d) (s := s) (eT := eT) (b := b)
          hℓ hΨ hcs i).integral_prod_right'
      refine h1.congr ?_
      filter_upwards with u
      exact (Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral hℓ
        (Work.BoseKinLoc.fsT ℓ d s eT b u) u i Ψ).symm
    have hsum : MeasureTheory.AEStronglyMeasurable
        (fun u : EuclideanSpace ℝ (Fin 3) => ∑ i : Fin (n + 1),
          Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s eT b u) ℓ u i Ψ)
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
      Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ => hterm i)
    refine hsum.congr ?_
    filter_upwards with u
    simp [Work.BoseBox.tKinAmb, Work.BoseBox.tKinWord, Work.BoseKinLoc.kinForm]

/-! ## 3  The target -/

theorem tKinAmbIntegrable {N : ℕ} {L ℓ d s eT b : ℝ} (hL : 0 < L) (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hsupp : tsupport Ψ ⊆ _root_.BoseGases.box N L) :
    MeasureTheory.IntegrableOn
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseBox.tKinAmb N L ℓ d s eT b u Ψ)
      (Work.BoseBox.coverU ℓ L) := by
  obtain ⟨K, hK0, hdec⟩ := tKinAmbFourierDecay hL hℓ hΨ hsupp
  obtain ⟨C, _hC0, hbound⟩ := tKinAmbWordBound hL hℓ hΨ hsupp hK0 hdec
  refine MeasureTheory.IntegrableOn.of_bound (volume_coverU_lt_top hℓ hL) ?_ C ?_
  · exact (tKinAmb_aestronglyMeasurable hL hℓ hΨ hsupp).mono_measure
      MeasureTheory.Measure.restrict_le_self
  · rw [MeasureTheory.ae_restrict_iff' (measurableSet_coverU hℓ hL)]
    exact Filter.Eventually.of_forall
      (fun u hu => by simpa [Real.norm_eq_abs] using hbound u hu)

end Work.BoseBox
