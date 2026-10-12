import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.PotAppPeel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.peel_const_le`

One-slot peel bound for the centred box: if the weight `A` is invariant in the
slot-`i` coordinate (`hAinv`), nonnegative on the box (`hAnn`) and integrable on
the box (`hAint`), and the kernel `k` has the first-argument fibre bound
`∫_y k y x ≤ C` (`hkC`), then

  `∫_{abox N ℓ} A x * k (x i) (x j) ≤ C * (ℓ³)⁻¹ * ∫_{abox N ℓ} A x`

for any two distinct slots `i ≠ j`. The peel isolates the slot-`i` coordinate
(`abox_integral_peel`, `kcInsN`), where `A` is constant, leaving the inner
integral `∫_{acube ℓ} k y (r j')`, bounded by `C`; the remaining integral of the
peeled weight is `(ℓ³)⁻¹` times the total integral of `A` because `A` does not
depend on the slot-`i` coordinate.
-/

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem peel_const_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {A : Submission.BoseGases.X N → ℝ}
    (hAinv : ∀ (x : Submission.BoseGases.X N) (z : EuclideanSpace ℝ (Fin 3)),
      A (Function.update x i z) = A x)
    (hAnn : ∀ x ∈ Submission.BoseGases.abox N ℓ, 0 ≤ A x)
    (hAint : MeasureTheory.IntegrableOn A (Submission.BoseGases.abox N ℓ))
    {k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ} {C : ℝ}
    (hkint : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => A x * k (x i) (x j)) (Submission.BoseGases.abox N ℓ))
    (hkC : ∀ x : EuclideanSpace ℝ (Fin 3),
      ∫ y in Submission.BoseGases.acube ℓ, k y x ≤ C) :
    ∫ x in Submission.BoseGases.abox N ℓ, A x * k (x i) (x j)
      ≤ C * (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N ℓ, A x := by
  cases N with
  | zero => exact i.elim0
  | succ n =>
    cases n with
    | zero =>
        exfalso
        have hi0 : i.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
        have hj0 : j.1 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)
        exact hij (Fin.ext (hi0.trans hj0.symm))
    | succ p =>
      rcases Fin.exists_succAbove_eq (x := j) (y := i) hij.symm with ⟨j', hj'⟩
      let A0 : Submission.BoseGases.X (p + 1) → ℝ :=
        fun r => A (Submission.BoseGases.kcInsN (p + 1) i (0, r))
      let F : Submission.BoseGases.X (p + 2) → ℝ := fun x => A x * k (x i) (x j)
      have hF_int : MeasureTheory.IntegrableOn F (Submission.BoseGases.abox (p + 2) ℓ) volume :=
        hkint
      have hzi : ∀ (r : Submission.BoseGases.X (p + 1)) (y : ℝ³),
          (Submission.BoseGases.kcInsN (p + 1) i (y, r)) i = y :=
        fun r y => Submission.BoseGases.kc_insN_apply_same (p + 1) i y r
      have hzj : ∀ (r : Submission.BoseGases.X (p + 1)) (y : ℝ³),
          (Submission.BoseGases.kcInsN (p + 1) i (y, r)) j = r j' := by
        intro r y
        rw [← hj']
        exact Submission.BoseGases.kc_insN_apply_succ (p + 1) i y r j'
      have hA0const : ∀ (r : Submission.BoseGases.X (p + 1)) (y : ℝ³),
          A (Submission.BoseGases.kcInsN (p + 1) i (y, r)) = A0 r := by
        intro r y
        dsimp only [A0]
        rw [Submission.BoseGases.kcInsN_update_zero i y r]
        exact hAinv _ y
      have hpoint : ∀ r : Submission.BoseGases.X (p + 1),
          (fun y : ℝ³ => F (Submission.BoseGases.kcInsN (p + 1) i (y, r))) =
            fun y : ℝ³ => A0 r * k y (r j') := by
        intro r
        funext y
        dsimp only [F]
        rw [hzi r y, hzj r y, hA0const r y]
      have hfib : ∀ r : Submission.BoseGases.X (p + 1),
          (∫ y in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN (p + 1) i (y, r))) =
            A0 r * (∫ y in Submission.BoseGases.acube ℓ, k y (r j')) := by
        intro r
        calc
          (∫ y in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN (p + 1) i (y, r)))
              = ∫ y in Submission.BoseGases.acube ℓ, A0 r * k y (r j') := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards with y
                exact congrFun (hpoint r) y
          _ = A0 r * (∫ y in Submission.BoseGases.acube ℓ, k y (r j')) := by
                rw [MeasureTheory.integral_const_mul]
      have hpeel := Submission.BoseGases.abox_integral_peel (n := p + 1) (i := i) (F := F) hF_int
      have hmain : (∫ x in Submission.BoseGases.abox (p + 2) ℓ, A x * k (x i) (x j))
          = ∫ r in Submission.BoseGases.abox (p + 1) ℓ,
              A0 r * (∫ y in Submission.BoseGases.acube ℓ, k y (r j')) := by
        calc
          (∫ x in Submission.BoseGases.abox (p + 2) ℓ, A x * k (x i) (x j))
              = ∫ r in Submission.BoseGases.abox (p + 1) ℓ,
                  (∫ y in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN (p + 1) i (y, r))) := by
                    change (∫ x in Submission.BoseGases.abox (p + 2) ℓ, F x)
                        = ∫ r in Submission.BoseGases.abox (p + 1) ℓ,
                            (∫ y in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN (p + 1) i (y, r)))
                    rw [hpeel]
          _ = ∫ r in Submission.BoseGases.abox (p + 1) ℓ,
                A0 r * (∫ y in Submission.BoseGases.acube ℓ, k y (r j')) := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with r
                  exact hfib r
      have hA0nonneg : ∀ r ∈ Submission.BoseGases.abox (p + 1) ℓ, 0 ≤ A0 r := by
        intro r hr
        have hmem : Submission.BoseGases.kcInsN (p + 1) i (0, r) ∈ Submission.BoseGases.abox (p + 2) ℓ := by
          intro m
          by_cases hm : m = i
          · subst hm
            rw [Submission.BoseGases.kc_insN_apply_same]
            exact Submission.BoseGases.zero_mem_acube hℓ.le
          · rcases Fin.exists_succAbove_eq hm with ⟨z, hz⟩
            rw [← hz, Submission.BoseGases.kc_insN_apply_succ]
            exact hr z
        exact hAnn _ hmem
      have hI1 : MeasureTheory.Integrable
          (fun r : Submission.BoseGases.X (p + 1) => ∫ y in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN (p + 1) i (y, r)))
          (volume.restrict (Submission.BoseGases.abox (p + 1) ℓ)) :=
        Submission.BoseGases.abox_peel_inner_integrable (n := p + 1) (i := i) (F := F) hF_int
      have hI1' : MeasureTheory.Integrable
          (fun r : Submission.BoseGases.X (p + 1) => A0 r * (∫ y in Submission.BoseGases.acube ℓ, k y (r j')))
          (volume.restrict (Submission.BoseGases.abox (p + 1) ℓ)) := by
        refine hI1.congr ?_
        filter_upwards with r
        exact hfib r
      have hG : MeasureTheory.Integrable
          (fun r : Submission.BoseGases.X (p + 1) => ∫ y in Submission.BoseGases.acube ℓ, A (Submission.BoseGases.kcInsN (p + 1) i (y, r)))
          (volume.restrict (Submission.BoseGases.abox (p + 1) ℓ)) :=
        Submission.BoseGases.abox_peel_inner_integrable (n := p + 1) (i := i) (F := A) hAint
      have hfibA : ∀ r : Submission.BoseGases.X (p + 1),
          (∫ y in Submission.BoseGases.acube ℓ, A (Submission.BoseGases.kcInsN (p + 1) i (y, r))) = (ℓ ^ 3) * A0 r := by
        intro r
        calc
          (∫ y in Submission.BoseGases.acube ℓ, A (Submission.BoseGases.kcInsN (p + 1) i (y, r)))
              = ∫ y in Submission.BoseGases.acube ℓ, A0 r := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards with y
                exact hA0const r y
          _ = (ℓ ^ 3) * A0 r := by
                rw [Submission.BoseGases.integral_const_acube ℓ hℓ]
                ring
      have hA0int : MeasureTheory.Integrable A0 (volume.restrict (Submission.BoseGases.abox (p + 1) ℓ)) := by
        have h1 : MeasureTheory.Integrable
            (fun r : Submission.BoseGases.X (p + 1) => (ℓ ^ 3)⁻¹ * (∫ y in Submission.BoseGases.acube ℓ, A (Submission.BoseGases.kcInsN (p + 1) i (y, r))))
            (volume.restrict (Submission.BoseGases.abox (p + 1) ℓ)) := hG.const_mul _
        refine h1.congr ?_
        filter_upwards with r
        rw [hfibA r]
        have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
        field_simp
      have hI2 : MeasureTheory.Integrable
          (fun r : Submission.BoseGases.X (p + 1) => A0 r * C)
          (volume.restrict (Submission.BoseGases.abox (p + 1) ℓ)) := hA0int.mul_const C
      have hbnd : (∫ r in Submission.BoseGases.abox (p + 1) ℓ, A0 r * (∫ y in Submission.BoseGases.acube ℓ, k y (r j')))
          ≤ ∫ r in Submission.BoseGases.abox (p + 1) ℓ, A0 r * C := by
        refine MeasureTheory.integral_mono_ae hI1' hI2 ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable (p + 1) ℓ)] with r hr
        exact mul_le_mul_of_nonneg_left (hkC (r j')) (hA0nonneg r hr)
      have hAvol : (∫ x in Submission.BoseGases.abox (p + 2) ℓ, A x)
          = (ℓ ^ 3) * ∫ r in Submission.BoseGases.abox (p + 1) ℓ, A0 r := by
        have hpeelA := Submission.BoseGases.abox_integral_peel (n := p + 1) (i := i) (F := A) hAint
        calc
          (∫ x in Submission.BoseGases.abox (p + 2) ℓ, A x)
              = ∫ r in Submission.BoseGases.abox (p + 1) ℓ, (∫ y in Submission.BoseGases.acube ℓ, A (Submission.BoseGases.kcInsN (p + 1) i (y, r))) := by
                  simpa using hpeelA
          _ = ∫ r in Submission.BoseGases.abox (p + 1) ℓ, (ℓ ^ 3) * A0 r := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards with r
                exact hfibA r
          _ = (ℓ ^ 3) * ∫ r in Submission.BoseGases.abox (p + 1) ℓ, A0 r := by
                rw [MeasureTheory.integral_const_mul]
      calc
        (∫ x in Submission.BoseGases.abox (p + 2) ℓ, A x * k (x i) (x j))
            = ∫ r in Submission.BoseGases.abox (p + 1) ℓ, A0 r * (∫ y in Submission.BoseGases.acube ℓ, k y (r j')) := hmain
        _ ≤ ∫ r in Submission.BoseGases.abox (p + 1) ℓ, A0 r * C := hbnd
        _ = C * ∫ r in Submission.BoseGases.abox (p + 1) ℓ, A0 r := by
              rw [MeasureTheory.integral_mul_const]
              ring
        _ = C * (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (p + 2) ℓ, A x := by
              rw [hAvol]
              have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
              field_simp

end Work.BoseFixB3.CS.Pieces
