import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.bf3a_cnplus` — the peel identity `Σᵢ gapBareᵢ = cnPlus`

The gap column of the box word `H_Λ(μ)` is `bℓ⁻²·cnPlus`, where `cnPlus ℓ Φ` is the sum over
the particle slots of the box-restricted `L²`-norm of the slot mean-free projection `aQ ℓ i Φ`.
Writing the gap as a *one-body* form on the slot fibres (`gapWord ℓ b 0 ψ = bℓ⁻²·gapBare ℓ 0 ψ`,
`gapBare ℓ 0 ψ = ∫_{Λ(0)}(Q_0ψ)²`) and peeling the slot coordinate out of `abox n ℓ` gives the
identity proved here:

    `Σᵢ ∫_{abox n ℓ} 1_{Λ(0)}(xᵢ)·gapBare ℓ 0 (fibre n i Φ x) dx = ℓ³ · cnPlus ℓ Φ`,

i.e. `Σᵢ slotFormB n (gapBare ℓ 0) ℓ 0 i Φ = cnPlus ℓ Φ` (the `ℓ³` on the right is the volume
of the inserted slot absorbed by the `ℓ⁻³` peel prefactor of `slotFormB`).

This is the gap row of FS `prop:Hamilton2ndQuant` in the first-quantised form used by
`Work.BoseBoxFock.W2kinB` (the file header of `W2Defs.lean` lists `(b/2ℓ²)·cnPlus` as the
first-quantised gap row).

## Proof

The corpus already contains the general statement at one slot more, with the gap word and and
a free parameter `b`: `Work.BoseFixB1.slotSum_gapWord_eq_b_cnPlus`,

    `ℓ⁻³ Σᵢ ∫_{abox (m+1) ℓ} 1_{Λ(0)}(xᵢ)·gapWord ℓ b 0 (fibre (m+1) i Φ x) = b ℓ⁻² cnPlus ℓ Φ`.

At `b = ℓ²` the gap word collapses to the bare mean-free mass (`gapWord ℓ (ℓ²) 0 ψ =
ℓ²·ℓ⁻²·gapBare ℓ 0 ψ = gapBare ℓ 0 ψ`, `hgap` below), and the `b ℓ⁻²` prefactor collapses to
`1`; the remaining `ℓ⁻³` is absorbed by multiplying with `ℓ³`.  The `n = 0` case is degenerate
(both sides are `0`).
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false

/-- At the anchored box and with the gap coefficient `b = ℓ²`, the gap word `bℓ⁻²·gapBare` is
the bare mean-free box mass. -/
lemma gapWord_sq_eq_gapBare {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseKinLoc.gapWord ℓ (ℓ ^ 2) 0 ψ = Work.BoseKinLoc.gapBare ℓ 0 ψ := by
  have h : ℓ ^ 2 * ℓ ^ (-2 : ℤ) = 1 := by
    rw [← zpow_natCast ℓ 2, ← zpow_add₀ (ne_of_gt hℓ)]
    norm_num
  simp only [Work.BoseKinLoc.gapWord]
  rw [h, one_mul]

theorem bf3a_cnplus {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre n i Φ x))
      = ℓ ^ 3 * Submission.BoseGases.cnPlus ℓ Φ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Submission.BoseGases.cnPlus]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    -- the corpus peel identity at one slot more, with gap coefficient `b = ℓ²`
    have hId := Work.BoseFixB1.slotSum_gapWord_eq_b_cnPlus (n := m) (ℓ := ℓ) (b := ℓ ^ 2)
      hℓ Φ hΦ
    -- the gap word at `b = ℓ²` is the bare mean-free mass, slot by slot
    have hsum : (∑ i : Fin (m + 1), ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i)
            * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x))
        = ∑ i : Fin (m + 1), ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i)
              * Work.BoseKinLoc.gapWord ℓ (ℓ ^ 2) 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine MeasureTheory.setIntegral_congr_fun
        (Submission.BoseGases.abox_measurable (m + 1) ℓ) (fun x _ => ?_)
      rw [gapWord_sq_eq_gapBare hℓ]
    -- the volume factors cancel
    have hvol : ℓ ^ 2 * ℓ ^ (-2 : ℤ) = 1 := by
      rw [← zpow_natCast ℓ 2, ← zpow_add₀ (ne_of_gt hℓ)]
      norm_num
    have h3 : ℓ ^ (-3 : ℤ) * ℓ ^ 3 = 1 := by
      rw [← zpow_natCast ℓ 3, ← zpow_add₀ (ne_of_gt hℓ)]
      norm_num
    have key : ℓ ^ (-3 : ℤ) * (∑ i : Fin (m + 1),
          ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i)
              * Work.BoseKinLoc.gapWord ℓ (ℓ ^ 2) 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x))
        = Submission.BoseGases.cnPlus ℓ Φ := by
      rw [hId, hvol, one_mul]
    calc (∑ i : Fin (m + 1), ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i)
            * Work.BoseKinLoc.gapBare ℓ 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x))
        = ∑ i : Fin (m + 1), ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i)
              * Work.BoseKinLoc.gapWord ℓ (ℓ ^ 2) 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x) :=
          hsum
      _ = 1 * (∑ i : Fin (m + 1), ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i)
              * Work.BoseKinLoc.gapWord ℓ (ℓ ^ 2) 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x)) :=
          (one_mul _).symm
      _ = (ℓ ^ (-3 : ℤ) * ℓ ^ 3) * (∑ i : Fin (m + 1),
            ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              Work.BoseKinLoc.indU ℓ 0 (x i)
                * Work.BoseKinLoc.gapWord ℓ (ℓ ^ 2) 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x)) := by
          rw [h3]
      _ = ℓ ^ 3 * (ℓ ^ (-3 : ℤ) * (∑ i : Fin (m + 1),
            ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
              Work.BoseKinLoc.indU ℓ 0 (x i)
                * Work.BoseKinLoc.gapWord ℓ (ℓ ^ 2) 0 (Work.BoseKinLoc.fibre (m + 1) i Φ x))) :=
          by ring
      _ = ℓ ^ 3 * Submission.BoseGases.cnPlus ℓ Φ := by rw [key]

end Work.BoseBoxFock
