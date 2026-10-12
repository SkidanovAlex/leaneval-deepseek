import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairEnergy_pairGc13_le_chi
import Submission.Work.BoseBoxFock.pairEnergy_pairGc21_le_chi
import Submission.Work.BoseBoxFock.pairEnergy_pairGc23_le_chi
import Submission.Work.BoseBoxFock.pairG_dir_leB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairG_dir_leB_chi` — the **χ-weighted** `pairG` fibre estimate

`FINDING_PotPairRows_exists.md` §11 records that the plain D2 estimate `pairG_dir_leB` (which bounds
the row's Dirichlet energy by the **unweighted** state content `pinDir`) is not payable at the node
`PotPairRows_exists`: the corner family concentrates where the window `χ_ℓ` vanishes, so `pinDir`
is unbounded there while the row's kernels are blind to it.  The state content the row *can* see is
the `χ_ℓ`-weighted one, `pinDirChi` (`pairRowDirChi.lean`).

This module is the (W2) repair of §11.3: the same three fibre estimates with `pinDir` replaced by
`pinDirChi`, **given** the three χ-weighted slice inequalities

* `hsl13` : `∫_{boxL ℓ} χ_ℓ(w)²·dirX13 ℓ p Θ₀ w ≤ pinDirChi ℓ Θ₀`,
* `hsl23` : `∫∫ χ_ℓ(z.1)²·dirX23 ℓ p Θ₀ z.1 z.2 ≤ pinDirChi ℓ Θ₀`,
* `hsl21` : `∫∫ χ_ℓ(z.1)²·dirY21 ℓ p Θ₀ z.2 z.1 ≤ pinDirChi ℓ Θ₀`

(the three clauses of the separate node `pairDirChi_slices`, here *hypotheses*).

The transport is the χ-weighted assembly `pairGChiAux` (product rule with the weight kept), applied
to the same analytic cores `pairGc{13,23,21}_core` and the same slice identities; the passage from
the clean representatives to the honest fibres is `pairEnergy_congr_box`, exactly as in
`pairG_dir_leB`.

`sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

/-- The χ-weighted slice inequality of `dirX13`, restated with the complexified window `chiS`. -/
theorem pairGchi_slice13 {n : ℕ} {l : ℝ} {p : Fin n × Fin n} {Θ₀ : Work.BoseDict.Xn n → ℂ}
    (h : (∫ w in Work.BoseK15.corpusBox.boxL l,
        (Submission.BoseGases.chiScale l w) ^ 2 * dirX13 l p Θ₀ w) ≤ pinDirChi l Θ₀) :
    (∫ w in Work.BoseK15.corpusBox.boxL l, ‖chiS l w‖ ^ 2 * dirX13 l p Θ₀ w)
      ≤ pinDirChi l Θ₀ := by
  rw [show (∫ w in Work.BoseK15.corpusBox.boxL l, ‖chiS l w‖ ^ 2 * dirX13 l p Θ₀ w)
      = ∫ w in Work.BoseK15.corpusBox.boxL l,
          (Submission.BoseGases.chiScale l w) ^ 2 * dirX13 l p Θ₀ w from
    MeasureTheory.setIntegral_congr_fun
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox l)
      (fun w _ => by rw [chiS_sq])]
  exact h

/-- The two-variable χ-weighted slice inequality, restated with the complexified window `chiS`. -/
theorem pairGchi_slice2 {n : ℕ} {l : ℝ} {Θ₀ : Work.BoseDict.Xn n → ℂ}
    {D : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : (∫ z in Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l,
        (Submission.BoseGases.chiScale l z.1) ^ 2 * D z) ≤ pinDirChi l Θ₀) :
    (∫ z in Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l,
        ‖chiS l z.1‖ ^ 2 * D z) ≤ pinDirChi l Θ₀ := by
  rw [show (∫ z in Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l,
        ‖chiS l z.1‖ ^ 2 * D z)
      = ∫ z in Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l,
          (Submission.BoseGases.chiScale l z.1) ^ 2 * D z from
    MeasureTheory.setIntegral_congr_fun
      ((Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox l).prod
        (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox l))
      (fun z _ => by rw [chiS_sq])]
  exact h

theorem pairG_dir_leB_chi {n : ℕ} {l : ℝ} (hl : 0 < l)
    (hsl13 : ∀ (p : Fin n × Fin n) {Θ₀ : Work.BoseDict.Xn n → ℂ}, ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∫ w in Work.BoseK15.corpusBox.boxL l,
          (Submission.BoseGases.chiScale l w) ^ 2 * Work.BoseBoxFock.dirX13 l p Θ₀ w)
        ≤ Work.BoseBoxFock.pinDirChi l Θ₀)
    (hsl23 : ∀ (p : Fin n × Fin n), p.1 ≠ p.2 → ∀ {Θ₀ : Work.BoseDict.Xn n → ℂ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∫ z in Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l,
          (Submission.BoseGases.chiScale l z.1) ^ 2 * Work.BoseBoxFock.dirX23 l p Θ₀ z.1 z.2)
        ≤ Work.BoseBoxFock.pinDirChi l Θ₀)
    (hsl21 : ∀ (p : Fin n × Fin n), p.1 ≠ p.2 → ∀ {Θ₀ : Work.BoseDict.Xn n → ℂ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∫ z in Work.BoseK15.corpusBox.boxL l ×ˢ Work.BoseK15.corpusBox.boxL l,
          (Submission.BoseGases.chiScale l z.1) ^ 2 * Work.BoseBoxFock.dirY21 l p Θ₀ z.2 z.1)
        ≤ Work.BoseBoxFock.pinDirChi l Θ₀) :
    ∃ C : ℝ, 0 ≤ C ∧
    (∀ (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {Θ Θ₀ : Work.BoseDict.Xn n → ℂ}
        {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A → Measurable B →
      (∀ x, ‖A x‖ ≤ cA) → (∀ x, ‖B x‖ ≤ cB) → 0 ≤ cA → 0 ≤ cB →
      Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG13 p Θ A B)
        ≤ C * cA ^ 2 * cB ^ 2 * Work.BoseBoxFock.pinL2 l Θ₀
            * (Work.BoseBoxFock.pinDirChi l Θ₀ + Work.BoseBoxFock.pinL2 l Θ₀))
    ∧
    (∀ (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {Θ Θ₀ : Work.BoseDict.Xn n → ℂ}
        {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A → Measurable B →
      (∀ x, ‖A x‖ ≤ cA) → (∀ x, ‖B x‖ ≤ cB) → 0 ≤ cA → 0 ≤ cB →
      Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG23 p Θ A B)
        ≤ C * cA ^ 2 * cB ^ 2 * Work.BoseBoxFock.pinL2 l Θ₀
            * (Work.BoseBoxFock.pinDirChi l Θ₀ + Work.BoseBoxFock.pinL2 l Θ₀))
    ∧
    (∀ (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {Θ Θ₀ : Work.BoseDict.Xn n → ℂ}
        {A : EuclideanSpace ℝ (Fin 3) → ℂ} {cA : ℝ},
      ContDiff ℝ (⊤ : ℕ∞) Θ₀ →
      (∀ x, Θ x = Set.indicator (Submission.BoseGases.abox n l) Θ₀ x) →
      Measurable A →
      (∀ x, ‖A x‖ ≤ cA) → 0 ≤ cA →
      Work.BoseBoxFock.L1Tails.pairEnergy l (Work.BoseBoxFock.pairG21 p Θ A)
        ≤ C * cA ^ 4 * Work.BoseBoxFock.pinL2 l Θ₀
            * (Work.BoseBoxFock.pinDirChi l Θ₀ + Work.BoseBoxFock.pinL2 l Θ₀)) := by
  obtain ⟨C13, hC13₀, hC13⟩ := pairEnergy_pairGc13_le_chi (ℓ := l) hl
  obtain ⟨C23, hC23₀, hC23⟩ := pairEnergy_pairGc23_le_chi (ℓ := l) hl
  obtain ⟨C21, hC21₀, hC21⟩ := pairEnergy_pairGc21_le_chi (ℓ := l) hl
  refine ⟨max C13 (max C23 C21), le_trans hC13₀ (le_max_left _ _), ?_, ?_, ?_⟩
  · intro p hp Θ Θ₀ A B cA cB hΘ₀ hΘ hA hB hAb hBb hcA hcB
    obtain ⟨hEq, hcont, hder, hval, hdb⟩ :=
      pairGc13_core (ℓ := l) hl p hp hΘ₀ hΘ hA hB hAb hBb hcA hcB
    have hmain := hC13 p hp hΘ₀ hcA hcB hval hder hdb hcont
      (setIntegral_memX13 hl p hΘ₀) (setIntegral_memY13 hl p hp hΘ₀)
      (pairGchi_slice13 (hsl13 p hΘ₀))
    rw [pairEnergy_congr_box hl hEq]
    refine hmain.trans ?_
    have hpin0 : 0 ≤ pinL2 l Θ₀ := integral_nonneg fun x => by positivity
    have hpinD0 : 0 ≤ pinDirChi l Θ₀ := pinDirChi_nonneg l Θ₀
    refine mul_le_mul_of_nonneg_right ?_ (add_nonneg hpinD0 hpin0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg cA))
      (sq_nonneg cB)) hpin0
  · intro p hp Θ Θ₀ A B cA cB hΘ₀ hΘ hA hB hAb hBb hcA hcB
    obtain ⟨hEq, hcont, hder, hval, hdb⟩ :=
      pairGc23_core (ℓ := l) hl p hp hΘ₀ hΘ hA hB hAb hBb hcA hcB
    have hmain := hC23 p hp hΘ₀ hcA hcB hval hder hdb hcont
      (setIntegral_memX23 hl p hp hΘ₀)
      (pairGchi_slice2 (D := fun z => dirX23 l p Θ₀ z.1 z.2) (hsl23 p hp hΘ₀))
    rw [pairEnergy_congr_box hl hEq]
    refine hmain.trans ?_
    have hpin0 : 0 ≤ pinL2 l Θ₀ := integral_nonneg fun x => by positivity
    have hpinD0 : 0 ≤ pinDirChi l Θ₀ := pinDirChi_nonneg l Θ₀
    refine mul_le_mul_of_nonneg_right ?_ (add_nonneg hpinD0 hpin0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (le_trans (le_max_left C23 C21) (le_max_right C13 (max C23 C21)))
        (sq_nonneg cA)) (sq_nonneg cB)) hpin0
  · intro p hp Θ Θ₀ A cA hΘ₀ hΘ hA hAb hcA
    obtain ⟨hEq, hcont, hder, hval, hdb⟩ :=
      pairGc21_core (ℓ := l) hl p hp hΘ₀ hΘ hA hAb hcA
    have hmain := hC21 p hp hΘ₀ hcA hval hder hdb hcont
      (setIntegral_memY21 hl p hp hΘ₀)
      (pairGchi_slice2 (D := fun z => dirY21 l p Θ₀ z.2 z.1) (hsl21 p hp hΘ₀))
    rw [pairEnergy_congr_box hl hEq]
    refine hmain.trans ?_
    have hpin0 : 0 ≤ pinL2 l Θ₀ := integral_nonneg fun x => by positivity
    have hpinD0 : 0 ≤ pinDirChi l Θ₀ := pinDirChi_nonneg l Θ₀
    refine mul_le_mul_of_nonneg_right ?_ (add_nonneg hpinD0 hpin0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_trans (le_max_right C23 C21) (le_max_right C13 (max C23 C21)))
      (pow_nonneg hcA 4)) hpin0

end Work.BoseBoxFock
