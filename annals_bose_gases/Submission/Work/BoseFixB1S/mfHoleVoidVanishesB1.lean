import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.mfBoxAbbrev
import Submission.Work.BoseFixB1S.mfManifestLowerV2B1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-- **The hole hypothesis forces the pair weight to vanish on the support.**  If a smooth state
has vanishing "manifest hole mass" (every summand of the pair sum integrates to `0`) and every
summand is integrable, then for a.e. `x` in the box: whenever the two particles of a pair both lie
in `boxA v μ u` and `Φ x ≠ 0`, the pair kernel `boxW h μ u` vanishes at that pair. -/
theorem mfHoleVoidVanishesB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : 0 ≤ v) (h : Work.UBB.ScatSol v)
    {μ : ℝ} {u : EuclideanSpace ℝ (Fin 3)} {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hint : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1)
          * ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
          * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2))
      (Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) MeasureTheory.volume)
    (h0 : (∑ p ∈ Submission.BoseGases.pairSet N,
              ∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1)
                  * ((Work.BoseFixB1S.boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2)
                      * Φ x)) ^ 2
                  * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2)) = 0) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
      ∀ p ∈ Submission.BoseGases.pairSet N,
        x p.1 ∈ Work.BoseFixB1S.boxA v μ u → x p.2 ∈ Work.BoseFixB1S.boxA v μ u →
          Φ x ≠ 0 → Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2) = 0 := by
  classical
  set A := Work.BoseFixB1S.boxA v μ u with hA
  set ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓ
  set F : Fin N × Fin N → Submission.BoseGases.X N → ℝ := fun p x =>
    ((A.indicator (fun _ => (1 : ℝ)) (x p.1)
        * (A.indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2)
      * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2) with hF
  -- `h0` in the abbreviated form
  have h0' : (∑ p ∈ Submission.BoseGases.pairSet N,
      ∫ x in Submission.BoseGases.abox N ℓ, F p x) = 0 := by
    rw [hF]; exact h0
  -- every summand is nonnegative
  have hFnn : ∀ p : Fin N × Fin N, ∀ x : Submission.BoseGases.X N, 0 ≤ F p x := by
    intro p x
    rw [hF]
    exact mul_nonneg (sq_nonneg _) (boxW_nonneg h hv μ u (x p.1) (x p.2))
  have hterm_nonneg : ∀ p ∈ Submission.BoseGases.pairSet N,
      0 ≤ ∫ x in Submission.BoseGases.abox N ℓ, F p x := by
    intro p _
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall (hFnn p))
  -- hence every summand vanishes
  have hterm_zero : ∀ p ∈ Submission.BoseGases.pairSet N,
      (∫ x in Submission.BoseGases.abox N ℓ, F p x) = 0 :=
    fun p hp => (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp h0' p hp
  -- hence every summand vanishes a.e.
  have hterm_ae : ∀ p ∈ Submission.BoseGases.pairSet N,
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)), F p x = 0 := by
    intro p hp
    have hfnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] F p :=
      Filter.Eventually.of_forall (hFnn p)
    have hfi : MeasureTheory.Integrable (F p)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
      rw [hF]; exact hint p hp
    exact (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hfnn hfi).mp (hterm_zero p hp)
  -- the "bad" set is contained in the finite union of the null sets `{F p ≠ 0}`
  have hbad : {x : Submission.BoseGases.X N |
      ¬ (∀ p ∈ Submission.BoseGases.pairSet N,
        x p.1 ∈ A → x p.2 ∈ A → Φ x ≠ 0 →
          Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2) = 0)}
      ⊆ {x : Submission.BoseGases.X N | ∃ p ∈ Submission.BoseGases.pairSet N, F p x ≠ 0} := by
    intro x hx
    push Not at hx
    obtain ⟨p, hp, hp1, hp2, hΦne, hWne⟩ := hx
    refine ⟨p, hp, ?_⟩
    have hval : F p x = (Φ x) ^ 2 * Work.BoseFixB1S.boxW h μ u (x p.1) (x p.2) := by
      rw [hF]
      simp only
      rw [Set.indicator_of_mem hp1 (fun _ => (1 : ℝ)),
        Set.indicator_of_mem hp2 (fun _ => (1 : ℝ))]
      ring
    rw [hval]
    exact mul_ne_zero (pow_ne_zero 2 hΦne) hWne
  have hnull : (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ))
      {x : Submission.BoseGases.X N |
        ∃ p ∈ Submission.BoseGases.pairSet N, F p x ≠ 0} = 0 := by
    have hsub : {x : Submission.BoseGases.X N |
          ∃ p ∈ Submission.BoseGases.pairSet N, F p x ≠ 0}
        ⊆ ⋃ p ∈ Submission.BoseGases.pairSet N,
            {x : Submission.BoseGases.X N | F p x ≠ 0} := by
      intro x hx
      obtain ⟨p, hp, hpx⟩ := hx
      exact Set.mem_biUnion hp hpx
    refine measure_mono_null hsub ?_
    refine le_antisymm ?_ (by simp)
    refine (measure_biUnion_finset_le (Submission.BoseGases.pairSet N)
      (fun p => {x : Submission.BoseGases.X N | F p x ≠ 0})).trans_eq ?_
    refine Finset.sum_eq_zero (fun p hp => ?_)
    exact MeasureTheory.ae_iff.mp (hterm_ae p hp)
  rw [MeasureTheory.ae_iff]
  exact measure_mono_null hbad hnull

end

end Work.BoseFixB1S
