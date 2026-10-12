import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.PiCoordMeanL2
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.fibreMean_sq_integrableOn`

The squared *restricted* fibre mean of an `L²` (and a.e. strongly measurable) function `Ψ` on the
`N`-particle box is integrable on the box:

    x ↦ ((1/volA) * ∫_{z ∈ A} Ψ (x with the i-th coordinate replaced by z))²  ∈ L¹(abox N a),

where `A ⊆ acube a` is a measurable set of positive Lebesgue measure `volA`.

The proof is a reduction to the *unrestricted* coordinate-mean theory of
`Work.BoseFixB1S.PiCoordMeanL2`.  Put

    ΨA x := (A.indicator (fun _ => 1)) (x i) * Ψ x .

Since the `i`-th coordinate of `Function.update x i z` is `z`, the fibre integral of `ΨA` over the
whole cube equals the fibre integral of `Ψ` over `A`:

    ∫ z, ΨA (Function.update x i z) ∂(volume ↾ acube a) = ∫_{z ∈ A} Ψ (Function.update x i z) .

So `(1/volA) ∫_{z ∈ A} Ψ (update x i z)` is a constant times the coordinate mean of the `L²`
function `ΨA` (`ΨA = 1_A · Ψ` is again `L²`), and the conclusion follows from
`Work.BoseFixB1S.integrable_and_integral_sq_pi_coordMean_le` (the `L²`-contraction of the
coordinate mean) applied to `ΨA` with `ν = volume ↾ acube a`, together with the product identity
`Submission.BoseGases.restrict_abox_eq_pi` identifying `Measure.pi (fun _ => ν)` with the box
measure.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB1S

/-- The one-particle space (file-local, to avoid clashing with the many `local notation "E3"`
declarations elsewhere in the corpus). -/
private abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

theorem fibreMean_sq_integrableOn {a volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolApos : 0 < volA)
    (hA : MeasurableSet A) (hsub : A ⊆ Submission.BoseGases.acube a) {N : ℕ} (i : Fin N)
    (Ψ : Submission.BoseGases.X N → ℝ)
    (hΨm : MeasureTheory.AEStronglyMeasurable Ψ
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N a)))
    (hΨ2 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => (Ψ x) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N a))) :
    MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => ((1 / volA) * ∫ z in A, Ψ (Function.update x i z)) ^ 2)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N a)) := by
  classical
  -- `N ≥ 1`: write it as `n + 1` for the coordinate-mean lemma
  have hNne : N ≠ 0 := by
    intro h
    rw [h] at i
    exact i.elim0
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNne
  -- `A` is nonempty (it has positive volume), hence the cube `acube a` has nonnegative side
  have hane : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h0 : (MeasureTheory.volume A) = 0 := by rw [h]; exact MeasureTheory.measure_empty
    rw [h0, ENNReal.toReal_zero] at hvolA
    linarith
  obtain ⟨y, hyA⟩ := hane
  have ha : 0 ≤ a := by
    have h0 := (Submission.BoseGases.mem_acube_iff a y).mp (hsub hyA)
    have h1 := h0 0
    rw [Set.mem_Icc] at h1
    linarith [h1.1, h1.2]
  -- the (finite) one-particle cube measure
  set ν : Measure E3 := (MeasureTheory.volume : Measure E3).restrict
    (Submission.BoseGases.acube a) with hνdef
  haveI hνfin : IsFiniteMeasure ν :=
    ⟨by rw [hνdef, Measure.restrict_apply_univ]
        exact Submission.BoseGases.acube_lt_top a ha⟩
  have hvolAreal : 0 < (MeasureTheory.volume A).toReal := hvolA ▸ hvolApos
  have hνpos : 0 < (ν Set.univ).toReal := by
    rw [hνdef, Measure.restrict_apply_univ]
    exact lt_of_lt_of_le hvolAreal
      (ENNReal.toReal_mono (ne_of_lt (Submission.BoseGases.acube_lt_top a ha))
        (measure_mono hsub))
  -- restricting to `A` gives the honest Lebesgue measure on `A`
  have hrestr : ν.restrict A = (MeasureTheory.volume : Measure E3).restrict A := by
    rw [hνdef, Measure.restrict_restrict hA, Set.inter_eq_left.mpr hsub]
  -- the box measure is the product of the cube measures
  have hmeasure_eq : (MeasureTheory.volume : Measure (Submission.BoseGases.X (n + 1))).restrict
      (Submission.BoseGases.abox (n + 1) a) = Measure.pi (fun _ : Fin (n + 1) => ν) := by
    rw [hνdef]
    exact Submission.BoseGases.restrict_abox_eq_pi (n + 1) a
  have hΨm' : AEStronglyMeasurable Ψ (Measure.pi (fun _ : Fin (n + 1) => ν)) := by
    rw [← hmeasure_eq]
    exact hΨm
  have hΨ2' : Integrable (fun x : Fin (n + 1) → E3 => (Ψ x) ^ 2)
      (Measure.pi (fun _ : Fin (n + 1) => ν)) := by
    rw [← hmeasure_eq]
    exact hΨ2
  -- the auxiliary function `ΨA = 1_{x i ∈ A} · Ψ`
  let ΨA : (Fin (n + 1) → E3) → ℝ :=
    fun x => (A.indicator (fun _ : E3 => (1 : ℝ)) (x i)) * Ψ x
  have hmeas1 : Measurable
      (fun x : Fin (n + 1) → E3 => A.indicator (fun _ : E3 => (1 : ℝ)) (x i)) :=
    ((measurable_const : Measurable (fun _ : E3 => (1 : ℝ))).indicator hA).comp
      (measurable_pi_apply i)
  have hΨAm : AEStronglyMeasurable ΨA (Measure.pi (fun _ : Fin (n + 1) => ν)) :=
    hmeas1.aestronglyMeasurable.mul hΨm'
  have hbound : ∀ x : Fin (n + 1) → E3, (ΨA x) ^ 2 ≤ (Ψ x) ^ 2 := by
    intro x
    have h1 : |ΨA x| ≤ |Ψ x| := by
      have hind : |A.indicator (fun _ : E3 => (1 : ℝ)) (x i)| ≤ 1 := by
        by_cases h : x i ∈ A
        · rw [Set.indicator_of_mem h]; norm_num
        · rw [Set.indicator_of_notMem h]; norm_num
      calc |ΨA x| = |A.indicator (fun _ : E3 => (1 : ℝ)) (x i)| * |Ψ x| := by
            simp only [ΨA, abs_mul]
        _ ≤ 1 * |Ψ x| := mul_le_mul_of_nonneg_right hind (abs_nonneg _)
        _ = |Ψ x| := one_mul _
    calc (ΨA x) ^ 2 = |ΨA x| ^ 2 := (sq_abs _).symm
      _ ≤ |Ψ x| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (Ψ x) ^ 2 := sq_abs _
  have hΨA2 : Integrable (fun x : Fin (n + 1) → E3 => (ΨA x) ^ 2)
      (Measure.pi (fun _ : Fin (n + 1) => ν)) := by
    refine Integrable.mono' hΨ2' (hΨAm.pow 2) (Filter.Eventually.of_forall fun x => ?_)
    simpa using hbound x
  -- the fibre identity
  have hfibre : ∀ x : Fin (n + 1) → E3,
      (∫ z, ΨA (Function.update x i z) ∂ν) = ∫ z in A, Ψ (Function.update x i z) := by
    intro x
    have h1 : (∫ z, ΨA (Function.update x i z) ∂ν)
        = ∫ z, A.indicator (fun z : E3 => Ψ (Function.update x i z)) z ∂ν := by
      apply integral_congr_ae
      filter_upwards with z
      have hpt : ΨA (Function.update x i z)
          = A.indicator (fun z : E3 => Ψ (Function.update x i z)) z := by
        dsimp only [ΨA]
        rw [Function.update_self]
        by_cases hz : z ∈ A
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
      exact hpt
    rw [h1, MeasureTheory.integral_indicator (μ := ν) hA, hrestr]
  -- the `L²`-contraction of the coordinate mean of `ΨA`
  obtain ⟨hInt, -⟩ := integrable_and_integral_sq_pi_coordMean_le ν hνpos i hΨAm hΨA2
  rw [hmeasure_eq]
  refine (hInt.const_mul (((ν Set.univ).toReal / volA) ^ 2)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [← hfibre x]
  have hvolAne : volA ≠ 0 := ne_of_gt hvolApos
  have hνne : (ν Set.univ).toReal ≠ 0 := ne_of_gt hνpos
  field_simp

end Work.BoseFixB1S
