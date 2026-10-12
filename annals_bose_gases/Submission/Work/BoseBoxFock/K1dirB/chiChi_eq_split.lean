import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.K1dirB.integrable_translate_mul
import Submission.Work.BoseBoxFock.L1Tails.kernelTail
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock.K1dirB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Splitting the box-squared pairing of the difference `q - (Wa + Wb)~` against a smooth,
box-supported kernel `H`: the two pieces can be integrated separately.

The only content is integrability of the pieces on the box squared:
* the `q`-piece is continuous and bounded on the compact box;
* the `latPer3`-piece is expanded with `latPer3_mul_expand` into the finite lattice sum whose
  summands are handled by `integrable_translate_mul`. -/
theorem chiChi_eq_split {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {Wa Wb : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWai : MeasureTheory.Integrable Wa) (hWbi : MeasureTheory.Integrable Wb)
    (hWas : ∀ x, R ≤ ‖x‖ → Wa x = 0) (hWbs : ∀ x, R ≤ ‖x‖ → Wb x = 0)
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ)
    (q : EuclideanSpace ℝ (Fin 3) → ℂ) (hq : Continuous q)
    (hqb : ∃ B : ℝ, ∀ z, ‖q z‖ ≤ B) :
    (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        (q (w - y) - Work.BoseBoxFock.latPer3 ℓ (Wa + Wb) (w - y)) * H w y)
      = (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          q (w - y) * H w y)
        - (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
            Work.BoseBoxFock.latPer3 ℓ (Wa + Wb) (w - y) * H w y) := by
  classical
  set S : Set E3 := Work.BoseK15.corpusBox.boxL ℓ with hSdef
  have hScomp : IsCompact S := Work.BoseK15.corpusBox.boxL_compact ℓ
  have hSprod : IsCompact (S ×ˢ S) := hScomp.prod hScomp
  have hfinS : IsFiniteMeasure (volume.restrict (S ×ˢ S)) :=
    isFiniteMeasure_restrict.mpr hSprod.measure_lt_top.ne
  haveI := hfinS
  -- ## a uniform bound for `H`
  have hHcont : Continuous (Function.uncurry H) := hH.continuous
  obtain ⟨CH, hCH⟩ := hSprod.exists_bound_of_continuousOn hH.continuous.continuousOn
  have hHbnd : ∀ w y, ‖H w y‖ ≤ max CH 0 := by
    intro w y
    by_cases hh : H w y = 0
    · rw [hh, norm_zero]; exact le_max_right _ _
    · obtain ⟨hw, hy⟩ := hHs w y hh
      exact le_trans (hCH (w, y) ⟨hw, hy⟩) (le_max_left _ _)
  obtain ⟨B, hB⟩ := hqb
  -- ## integrability of the `q`-row
  have hA : Integrable (fun p : E3 × E3 => q (p.1 - p.2) * H p.1 p.2)
      (volume.restrict (S ×ˢ S)) := by
    have hcont : Continuous (fun p : E3 × E3 => q (p.1 - p.2) * H p.1 p.2) :=
      (hq.comp (continuous_fst.sub continuous_snd)).mul hHcont
    refine Integrable.of_bound (hcont.aestronglyMeasurable.mono_measure
      Measure.restrict_le_self) (max B 0 * max CH 0) ?_
    filter_upwards with p
    rw [norm_mul]
    exact mul_le_mul (le_trans (hB _) (le_max_left _ _)) (hHbnd _ _) (norm_nonneg _)
      (le_max_right _ _)
  -- ## integrability of the `latPer3`-row
  have hW0i : Integrable (fun x : E3 => Wa x + Wb x) := hWai.add hWbi
  have hWstrict : ∀ x : E3, R < ‖x‖ → (Wa + Wb) x = 0 := by
    intro x hx
    rw [Pi.add_apply, hWas x hx.le, hWbs x hx.le, add_zero]
  have hHm : AEStronglyMeasurable (Function.uncurry H) (volume.prod volume) :=
    hHcont.aestronglyMeasurable
  have hterm : ∀ m : Fin 3 → ℤ, Integrable (fun p : E3 × E3 =>
      (((Wa + Wb) (p.1 - p.2 - ℓ • latVec m) : ℝ) : ℂ) * H p.1 p.2)
      (volume.prod volume) :=
    fun m => integrable_translate_mul hℓ hW0i m hHm ⟨max CH 0, hHbnd⟩ hHs
  have hBfull : Integrable (fun p : E3 × E3 =>
      latPer3 ℓ (Wa + Wb) (p.1 - p.2) * H p.1 p.2) (volume.prod volume) := by
    have hs : Integrable (fun p : E3 × E3 =>
        ∑ m ∈ LatFourier.latFinSet ℓ R,
          (((Wa + Wb) (p.1 - p.2 - ℓ • latVec m) : ℝ) : ℂ) * H p.1 p.2)
        (volume.prod volume) :=
      integrable_finsetSum _ (fun m _ => hterm m)
    have hcs : Integrable (fun p : E3 × E3 =>
        ((((ℓ ^ 3 : ℝ)) : ℂ) * (∑ m ∈ LatFourier.latFinSet ℓ R,
          (((Wa + Wb) (p.1 - p.2 - ℓ • latVec m) : ℝ) : ℂ))) * H p.1 p.2)
        (volume.prod volume) := by
      refine (hs.const_mul (((ℓ ^ 3 : ℝ)) : ℂ)).congr ?_
      filter_upwards with p
      rw [← Finset.sum_mul (s := LatFourier.latFinSet ℓ R)
        (f := fun m => (((Wa + Wb) (p.1 - p.2 - ℓ • latVec m) : ℝ) : ℂ))
        (a := H p.1 p.2)]
      ring
    refine hcs.congr ?_
    filter_upwards with p
    exact (latPer3_mul_expand hℓ hWstrict hHs p.1 p.2).symm
  have hB : Integrable (fun p : E3 × E3 =>
      latPer3 ℓ (Wa + Wb) (p.1 - p.2) * H p.1 p.2) (volume.restrict (S ×ˢ S)) :=
    hBfull.mono_measure Measure.restrict_le_self
  -- ## integrability of the difference
  have hC : Integrable (fun p : E3 × E3 =>
      (q (p.1 - p.2) - latPer3 ℓ (Wa + Wb) (p.1 - p.2)) * H p.1 p.2)
      (volume.restrict (S ×ˢ S)) := by
    refine (hA.sub hB).congr ?_
    filter_upwards with p
    show q (p.1 - p.2) * H p.1 p.2 - latPer3 ℓ (Wa + Wb) (p.1 - p.2) * H p.1 p.2
      = (q (p.1 - p.2) - latPer3 ℓ (Wa + Wb) (p.1 - p.2)) * H p.1 p.2
    ring
  -- ## the three set integrals as product integrals
  have eq_q : (∫ w in S, ∫ y in S, q (w - y) * H w y)
      = ∫ z in S ×ˢ S, q (z.1 - z.2) * H z.1 z.2 :=
    (setIntegral_prod (μ := (volume : Measure E3)) (ν := (volume : Measure E3))
      (fun p : E3 × E3 => q (p.1 - p.2) * H p.1 p.2) hA).symm
  have eq_L : (∫ w in S, ∫ y in S, latPer3 ℓ (Wa + Wb) (w - y) * H w y)
      = ∫ z in S ×ˢ S, latPer3 ℓ (Wa + Wb) (z.1 - z.2) * H z.1 z.2 :=
    (setIntegral_prod (μ := (volume : Measure E3)) (ν := (volume : Measure E3))
      (fun p : E3 × E3 => latPer3 ℓ (Wa + Wb) (p.1 - p.2) * H p.1 p.2) hB).symm
  have eq_s : (∫ w in S, ∫ y in S,
        (q (w - y) - latPer3 ℓ (Wa + Wb) (w - y)) * H w y)
      = ∫ z in S ×ˢ S, (q (z.1 - z.2) - latPer3 ℓ (Wa + Wb) (z.1 - z.2)) * H z.1 z.2 :=
    (setIntegral_prod (μ := (volume : Measure E3)) (ν := (volume : Measure E3))
      (fun p : E3 × E3 => (q (p.1 - p.2) - latPer3 ℓ (Wa + Wb) (p.1 - p.2)) * H p.1 p.2)
      hC).symm
  rw [eq_q, eq_L, eq_s]
  rw [show (∫ z in S ×ˢ S, (q (z.1 - z.2) - latPer3 ℓ (Wa + Wb) (z.1 - z.2)) * H z.1 z.2)
      = ∫ z in S ×ˢ S, (q (z.1 - z.2) * H z.1 z.2
          - latPer3 ℓ (Wa + Wb) (z.1 - z.2) * H z.1 z.2) from
    integral_congr_ae (Eventually.of_forall (fun z => by
      show (q (z.1 - z.2) - latPer3 ℓ (Wa + Wb) (z.1 - z.2)) * H z.1 z.2
        = q (z.1 - z.2) * H z.1 z.2 - latPer3 ℓ (Wa + Wb) (z.1 - z.2) * H z.1 z.2
      ring))]
  rw [MeasureTheory.integral_sub hA hB]

end Work.BoseBoxFock.K1dirB
