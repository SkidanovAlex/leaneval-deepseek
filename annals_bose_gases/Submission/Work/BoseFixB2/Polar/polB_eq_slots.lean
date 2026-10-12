import ChallengeDeps
import Submission.Work.BoseFixB2.Polar.fsT_parallelogram
import Submission.Work.BoseFixB2.Polar.polB_eq_slots_of_nonpos
import Submission.Work.BoseFixB2.Polar.potBil_polar
import Submission.Work.BoseFixB2.Polar.slot_polar
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Polar.polB_eq_slots` — the polarised box word is the sum of its slot words

FS §6's polarised box word `polB` (`Work.BoseFixB2.polB`, the numerator `𝒜_{ij}` of
`lem:LocMatrices`) is by definition the polarisation of the frozen box word,

    `4·polB Φ Ψ = wordB (Φ+Ψ) − wordB (Φ−Ψ)`,

and the box word splits as `wordB = boxFormB = kinFormB + ∫_{abox} Φ²·potWordU`
(`Work.BoseKinLoc.Defs`).  The **slot decomposition** proved here says that the
polarisation of the full box word is the sum of the polarisations of its parts:

    `polB v h μ n Φ Ψ = Σ_{i< n} kinBilᵢ Φ Ψ + potBil Φ Ψ`.

* `kinBilᵢ Φ Ψ` (`Work.BoseFixB2.kinBilFS`) is the polarisation of the slot-`i` kinetic
  summand of `kinFormB`, i.e. `ℓ⁻³∫_{abox} 1_{Λ}(xᵢ)·fsTᵦ(fibreᵢ Φ x, fibreᵢ Ψ x)`, where
  `fsTbil` is the polarisation of the one-body localised word `fsT` (`eq:DefT`);
* `potBil Φ Ψ` (`Work.BoseFixB2.potBil`) is `∫_{abox} ΦΨ·potWordU`, the polarisation of
  the multiplicative part `∫ Φ²·potWordU`.

This is the identity FS use to pass from the polarised word to the *slot* forms on which
the band arguments of §6 (`Band/`, `Recomb/`) run: it converts every statement about
`polB` into a statement about the slot-`i` kinetic forms `kinBilᵢ` plus the potential form.

## Proof

`wordB` is defined as `boxFormB` at FS's parameters, so the identity is
`4·polB Φ Ψ = boxFormB (Φ+Ψ) − boxFormB (Φ−Ψ)` with

    `boxFormB Φ = kinFormB Φ + ∫_{abox} Φ²·potWordU`,

and the two summands are polarised separately:

* **kinetic** (`kinFormB_diff_polar_aux`): `kinFormB` is `ℓ⁻³` times the sum over the
  slots of the slot integrals.  For each slot the fibre is linear in the state
  (`fibreᵢ (Φ±Ψ) x = fibreᵢ Φ x ± fibreᵢ Ψ x`, definitionally), so the difference of the
  two slot integrals is the integral of the pointwise difference, `fsTbil` being *defined*
  as the quarter-difference of `fsT` (`slot_polar`); the integrands are integrable on the
  compact box because the fibres of smooth states are smooth
  (`Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth`).  The sum over the slots is pure
  finite-sum algebra (`sum_four_polar_aux`).
* **potential** (`potBil_polar`): the potential profile is independent of the state, so the
  identity is the pointwise `(f+g)² − (f−g)² = 4fg` together with integral additivity;
  integrability comes from the hypothesis on `potWordU` and the boundedness of `Φ±Ψ` on
  the compact box.

The single case that needs no analysis is the degenerate box `ℓ ≤ 0`, where both sides
vanish because the box is a null set (`polB_eq_slots_of_nonpos`, from
`Polar.wordB_box_local`).  Since `fsSide v μ = sideAt μ (a v)` carries no positivity
hypothesis in the statement, the proof splits on it.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB2.Polar

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The finite-sum step -/

/-- **The summation step of the slot decomposition.**  If the slot quantities `A i, B i, C i`
satisfy `(A i − B i)/4 = C i`, then the quarter-difference of the common multiple `c` of the
two sums is the sum of the `c·C i`.  (`c = ℓ⁻³` in the application.) -/
lemma sum_four_polar_aux {ι : Type*} [Fintype ι] (c : ℝ) (A B C : ι → ℝ)
    (h : ∀ i, (A i - B i) / 4 = C i) :
    (c * (∑ i, A i) - c * (∑ i, B i)) / 4 = ∑ i, c * C i := by
  rw [show (c * (∑ i, A i) - c * (∑ i, B i)) / 4
        = c * ((∑ i, A i - ∑ i, B i) / 4) by ring]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.mul_sum]

/-! ## 2. The kinetic part -/

/-- **The box kinetic word polarises slot by slot.**  The difference of the box kinetic words
of `Φ+Ψ` and `Φ−Ψ`, quartered, is the sum over the slots of the slot-`i` kinetic bilinear form
`kinBil`.  Slot by slot this is `slot_polar` (the fibre is linear in the state and `fsTbil` is
the polarisation of `fsT`), and the sum is `sum_four_polar_aux`. -/
lemma kinFormB_diff_polar_aux {n : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Φ Ψ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    (Work.BoseKinLoc.kinFormB n ℓ d s εT b (fun x => Φ x + Ψ x)
      - Work.BoseKinLoc.kinFormB n ℓ d s εT b (fun x => Φ x - Ψ x)) / 4
    = ∑ i : Fin n, Work.BoseFixB2.kinBil n ℓ d s εT b i Φ Ψ := by
  simp only [Work.BoseKinLoc.kinFormB, Work.BoseFixB2.kinBil]
  exact sum_four_polar_aux (ℓ ^ (-3 : ℤ))
    (fun i : Fin n => ∫ x in Submission.BoseGases.abox n ℓ,
      Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
        (Work.BoseKinLoc.fibre n i (fun y => Φ y + Ψ y) x))
    (fun i : Fin n => ∫ x in Submission.BoseGases.abox n ℓ,
      Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseKinLoc.fsT ℓ d s εT b 0
        (Work.BoseKinLoc.fibre n i (fun y => Φ y - Ψ y) x))
    (fun i : Fin n => ∫ x in Submission.BoseGases.abox n ℓ,
      Work.BoseKinLoc.indU ℓ 0 (x i) * Work.BoseFixB2.fsTbil ℓ d s εT b 0
        (Work.BoseKinLoc.fibre n i Φ x) (Work.BoseKinLoc.fibre n i Ψ x))
    (fun i => slot_polar (d := d) (s := s) (εT := εT) (b := b) hℓ i hΦ hΨ)

/-! ## 3. The two parts together -/

/-- **The polarised box form splits into its kinetic and potential parts.**  This is the
unfolded form of the target at FS's parameters, before `wordB` is substituted: for a positive
box side `ℓ`,

    `(boxFormB (Φ+Ψ) − boxFormB (Φ−Ψ))/4 = Σᵢ kinBilᵢ Φ Ψ + ∫_{abox} ΦΨ·potWordU`. -/
lemma boxFormB_diff_polar_aux {n : ℕ} {v g : ℝ³ → ℝ} {ℓ μ d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Φ Ψ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hw : IntegrableOn
      (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
      (Submission.BoseGases.abox n ℓ)) :
    (Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b (fun x => Φ x + Ψ x)
      - Work.BoseKinLoc.boxFormB n v g ℓ μ d s εT b (fun x => Φ x - Ψ x)) / 4
    = (∑ i : Fin n, Work.BoseFixB2.kinBil n ℓ d s εT b i Φ Ψ)
      + ∫ x in Submission.BoseGases.abox n ℓ,
          Φ x * Ψ x * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x := by
  have hk := kinFormB_diff_polar_aux (n := n) (ℓ := ℓ) (d := d) (s := s) (εT := εT)
    (b := b) hℓ hΦ hΨ
  have hp := potBil_polar (n := n) (v := v) (g := g) (ℓ := ℓ) (μ := μ) hℓ hΦ hΨ hw
  simp only [Work.BoseKinLoc.boxFormB]
  linarith [hk, hp]

/-! ## 4. The target: the slot decomposition of `polB` -/

theorem polB_eq_slots {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {n : ℕ} {Φ Ψ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hw : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h)
        (Work.BoseFixB2.fsSide v μ) μ 0 x)
      (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ))) :
    Work.BoseFixB2.polB v h μ n Φ Ψ =
      (∑ i : Fin n, Work.BoseFixB2.kinBilFS v μ i Φ Ψ)
        + Work.BoseFixB2.potBil n v (Submission.BoseGases.g0 v h)
            (Work.BoseFixB2.fsSide v μ) μ Φ Ψ := by
  simp only [Work.BoseFixB2.polB, Work.BoseBoxFix.wordB, Work.BoseFixB2.kinBilFS,
    Work.BoseFixB2.potBil, Work.BoseFixB2.fsSide]
  by_cases hpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
  · exact boxFormB_diff_polar_aux hpos hΦ hΨ hw
  · exact polB_eq_slots_of_nonpos (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) (Ψ := Ψ)
      (le_of_not_gt hpos)

end Work.BoseFixB2.Polar
