import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.LatticeModel.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBox.LatticeModel

open MeasureTheory
open scoped BigOperators

/-- **The cell Riemann sum identity.**  If the lattice cells of mesh `h` are
pairwise disjoint, each has volume `h³`, and together they fill the box, then
for any function `G` integrable on the box the difference between the
Riemann-type sum `h³ ∑_k G (centre k)` and the integral of `G` over the box is
the sum over the cells of the local discrepancy `G (centre k) − G x`. -/
theorem sum_sub_setIntegral_eq {h : ℝ} (hh : 0 < h) {N : ℕ} (hN : 0 < N) {G : (Fin 3 → ℝ) → ℝ}
    (hdisp : ∀ k k' : Fin 3 → Fin N, k ≠ k' → Disjoint (latticeCell h N k) (latticeCell h N k'))
    (hvol : ∀ k : Fin 3 → Fin N, MeasureTheory.volume (latticeCell h N k) = ENNReal.ofReal (h ^ 3))
    (hcover : (⋃ k : Fin 3 → Fin N, latticeCell h N k) = latticeBox h N)
    (hint : MeasureTheory.IntegrableOn G (latticeBox h N)) :
    h ^ 3 * (∑ k : Fin 3 → Fin N, G (latticeCenter h N k)) - ∫ x in latticeBox h N, G x
      = ∑ k : Fin 3 → Fin N, ∫ x in latticeCell h N k, (G (latticeCenter h N k) - G x) := by
  classical
  -- each cell is a product of intervals, hence measurable
  have hmeas : ∀ k : Fin 3 → Fin N, MeasurableSet (latticeCell h N k) := by
    intro k
    unfold latticeCell
    exact MeasurableSet.pi Set.countable_univ (fun j _ => measurableSet_Ico)
  -- each cell sits inside the box, so `G` is integrable on it
  have hsub : ∀ k : Fin 3 → Fin N, latticeCell h N k ⊆ latticeBox h N := by
    intro k
    rw [← hcover]
    exact Set.subset_iUnion _ k
  have hintc : ∀ k : Fin 3 → Fin N, MeasureTheory.IntegrableOn G (latticeCell h N k) :=
    fun k => hint.mono_set (hsub k)
  have hvolr : ∀ k : Fin 3 → Fin N, (MeasureTheory.volume (latticeCell h N k)).toReal = h ^ 3 := by
    intro k
    rw [hvol k, ENNReal.toReal_ofReal (by positivity)]
  -- the constant part of the integrand
  have hconst : ∀ k : Fin 3 → Fin N,
      MeasureTheory.IntegrableOn (fun _ : Fin 3 → ℝ => G (latticeCenter h N k))
        (latticeCell h N k) := by
    intro k
    exact MeasureTheory.integrableOn_const (by rw [hvol k]; exact ENNReal.ofReal_ne_top) (by simp)
  -- the integral of one local discrepancy
  have hterm : ∀ k : Fin 3 → Fin N,
      ∫ x in latticeCell h N k, (G (latticeCenter h N k) - G x)
        = G (latticeCenter h N k) * h ^ 3 - ∫ x in latticeCell h N k, G x := by
    intro k
    have hsplit : ∫ x in latticeCell h N k, (G (latticeCenter h N k) - G x)
        = (∫ x in latticeCell h N k, G (latticeCenter h N k))
            - ∫ x in latticeCell h N k, G x :=
      MeasureTheory.integral_sub
        (f := fun _ : Fin 3 → ℝ => G (latticeCenter h N k)) (g := G) (hconst k) (hintc k)
    have hconstval : (∫ x in latticeCell h N k, G (latticeCenter h N k))
        = G (latticeCenter h N k) * h ^ 3 := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, hvolr k, smul_eq_mul]
      ring
    rw [hsplit, hconstval]
  -- the disjoint-cell sum of the integrals is the integral over the box
  have hpart : ∫ x in latticeBox h N, G x = ∑ k : Fin 3 → Fin N, ∫ x in latticeCell h N k, G x := by
    rw [← hcover]
    rw [show (⋃ k : Fin 3 → Fin N, latticeCell h N k)
        = ⋃ i ∈ (Finset.univ : Finset (Fin 3 → Fin N)), latticeCell h N i from by simp]
    rw [MeasureTheory.integral_biUnion_finset Finset.univ (fun i _ => hmeas i)
      (fun i _ j _ hij => hdisp i j hij) (fun i _ => hintc i)]
  rw [hpart, Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

end Work.BoseBox.LatticeModel
