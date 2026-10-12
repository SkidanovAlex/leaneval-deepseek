import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.continuous_setIntegral_compact_gen_mul
import Submission.Work.BoseBoxFock.pairGCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGc13_continuous` — joint continuity of the clean `pairG13` fibre

The clean fibre `pairGc13 ℓ p hp Θ₀ A B` of `Work.BoseBoxFock.pairGCore` is the integral over the
compact product box `boxPiSet ({k // k ≠ p.2}) ℓ ×ˢ boxL ℓ` of

    star (Θ₀ (insertCoord p.2 w z.1)) * A (z.1 ⟨p.1, hp⟩) * star (B z.2) * Θ₀ (confY13 p y z.2 z.1) .

Only the two state factors `Θ₀ (insertCoord p.2 w z.1)` and `Θ₀ (confY13 p y z.2 z.1)` depend on
the parameters `(w, y)`; both are compositions of the smooth `Θ₀` with maps that are continuous in
`(w, y, z)`.  The factors `A`, `B` enter through the *bounded measurable weight*
`z ↦ A (z.1 ⟨p.1, hp⟩) · star (B z.2)`, which is why the parametric integral is handled by the
weighted dominated-convergence lemma `continuous_setIntegral_compact_gen_mul` rather than by
`contDiff_setIntegral_compact_gen` (that one would need `A`, `B` smooth, which they are not: they
are only measurable and bounded).

`sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- The insertion `insertCoord j w x'` is continuous in `(w, x')`. -/
private lemma continuous_insertCoord_uncurry {n : ℕ} (j : Fin n) :
    Continuous (fun r : E3 × ({k : Fin n // k ≠ j} → E3) => insertCoord j r.1 r.2) := by
  rw [continuous_pi_iff]
  intro k
  by_cases hk : k = j
  · have h1 : (fun r : E3 × ({k : Fin n // k ≠ j} → E3) =>
        insertCoord j r.1 r.2 k) = fun r => r.1 := by
      funext r
      rw [insertCoord_eq]
      simp [hk]
    rw [h1]
    exact continuous_fst
  · have h1 : (fun r : E3 × ({k : Fin n // k ≠ j} → E3) =>
        insertCoord j r.1 r.2 k) = fun r => r.2 ⟨k, hk⟩ := by
      funext r
      rw [insertCoord_eq]
      simp [hk]
    rw [h1]
    exact (continuous_apply (A := fun _ : {k : Fin n // k ≠ j} => E3) ⟨k, hk⟩).comp
      continuous_snd

/-- The `Y`-configuration `confY13 p y u x'` is continuous in `(y, u, x')`. -/
private lemma continuous_confY13_uncurry {n : ℕ} (p : Fin n × Fin n) :
    Continuous (fun r : E3 × (E3 × ({k : Fin n // k ≠ p.2} → E3)) =>
      confY13 p r.1 r.2.1 r.2.2) := by
  rw [continuous_pi_iff]
  intro k
  by_cases h1 : k = p.1
  · have hh : (fun r : E3 × (E3 × ({k : Fin n // k ≠ p.2} → E3)) =>
        confY13 p r.1 r.2.1 r.2.2 k) = fun r => r.1 := by
      funext r
      simp only [confY13, dif_pos h1]
    rw [hh]
    exact continuous_fst
  · by_cases h2 : k = p.2
    · have hh : (fun r : E3 × (E3 × ({k : Fin n // k ≠ p.2} → E3)) =>
          confY13 p r.1 r.2.1 r.2.2 k) = fun r => r.2.1 := by
        funext r
        simp only [confY13, dif_neg h1, dif_pos h2]
      rw [hh]
      exact continuous_fst.comp continuous_snd
    · have hh : (fun r : E3 × (E3 × ({k : Fin n // k ≠ p.2} → E3)) =>
          confY13 p r.1 r.2.1 r.2.2 k) = fun r => r.2.2 ⟨k, h2⟩ := by
        funext r
        simp only [confY13, dif_neg h1, dif_neg h2]
      rw [hh]
      exact (continuous_apply (A := fun _ : {k : Fin n // k ≠ p.2} => E3) ⟨k, h2⟩).comp
        (continuous_snd.comp continuous_snd)

theorem pairGc13_continuous {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) :
    Continuous (Function.uncurry (Work.BoseBoxFock.pairGc13 ℓ p hp Θ₀ A B)) := by
  have hBL : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseK15.corpusBox.boxL_compact ℓ
  have hScomp : IsCompact (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ
      ×ˢ Work.BoseK15.corpusBox.boxL ℓ) :=
    (isCompact_boxPiSet hℓ).prod hBL
  -- the bounded measurable weight
  have haesm : AEStronglyMeasurable
      (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => A (z.1 ⟨p.1, hp⟩) * star (B z.2))
      ((volume : Measure (({k : Fin n // k ≠ p.2} → E3) × E3)).restrict
        (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)) := by
    have h1 : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => z.1 ⟨p.1, hp⟩) :=
      ((continuous_apply (A := fun _ : {k : Fin n // k ≠ p.2} => E3) ⟨p.1, hp⟩).comp
        continuous_fst).measurable
    have h2 : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => A (z.1 ⟨p.1, hp⟩)) :=
      hA.comp h1
    have h3 : Measurable (fun z : ({k : Fin n // k ≠ p.2} → E3) × E3 => star (B z.2)) :=
      continuous_star.measurable.comp (hB.comp measurable_snd)
    exact (h2.mul h3).aestronglyMeasurable
  have hab : ∀ᵐ z ∂((volume : Measure (({k : Fin n // k ≠ p.2} → E3) × E3)).restrict
        (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)),
      ‖A (z.1 ⟨p.1, hp⟩) * star (B z.2)‖ ≤ max cA 0 * max cB 0 := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    calc ‖A (z.1 ⟨p.1, hp⟩) * star (B z.2)‖ = ‖A (z.1 ⟨p.1, hp⟩)‖ * ‖B z.2‖ := by
          rw [norm_mul, norm_star]
      _ ≤ max cA 0 * max cB 0 := mul_le_mul (le_trans (hAb _) (le_max_left _ _))
          (le_trans (hBb _) (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  -- the parametric factor
  have hgcont : Continuous (Function.uncurry (fun (q : E3 × E3)
      (z : ({k : Fin n // k ≠ p.2} → E3) × E3) =>
        star (Θ₀ (insertCoord p.2 q.1 z.1)) * Θ₀ (confY13 p q.2 z.2 z.1))) := by
    have h1 : Continuous (fun qz : (E3 × E3) × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
        Θ₀ (insertCoord p.2 qz.1.1 qz.2.1)) :=
      hΘ₀.continuous.comp (continuous_insertCoord_uncurry p.2 |>.comp
        ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)))
    have h2 : Continuous (fun qz : (E3 × E3) × (({k : Fin n // k ≠ p.2} → E3) × E3) =>
        Θ₀ (confY13 p qz.1.2 qz.2.2 qz.2.1)) :=
      hΘ₀.continuous.comp (continuous_confY13_uncurry p |>.comp
        ((continuous_snd.comp continuous_fst).prodMk
          ((continuous_snd.comp continuous_snd).prodMk (continuous_fst.comp continuous_snd))))
    exact h1.star.mul h2
  have hmain := continuous_setIntegral_compact_gen_mul
    (G := ({k : Fin n // k ≠ p.2} → E3) × E3) (P := E3 × E3) hScomp haesm hab hgcont
  have hfun : Function.uncurry (Work.BoseBoxFock.pairGc13 ℓ p hp Θ₀ A B)
      = fun q : E3 × E3 => ∫ z in (boxPiSet ({k : Fin n // k ≠ p.2}) ℓ
          ×ˢ Work.BoseK15.corpusBox.boxL ℓ),
          (A (z.1 ⟨p.1, hp⟩) * star (B z.2))
            * (star (Θ₀ (insertCoord p.2 q.1 z.1)) * Θ₀ (confY13 p q.2 z.2 z.1)) := by
    funext q
    rw [Function.uncurry_apply_pair]
    refine (MeasureTheory.setIntegral_congr_fun hScomp.measurableSet (fun z _hz => ?_)).symm
    ring
  rw [hfun]
  exact hmain

end Work.BoseBoxFock
