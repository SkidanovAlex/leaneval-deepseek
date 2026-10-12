import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairRowGDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowFibreGen` — the pair-row fibre forms at an **arbitrary** kernel

The five integrand shapes of the FS `Q₂` row (`potPairRows_kernelExpanded`) are triple integrals of
the form

    ∫_x ∫_y ∫_u (state factor) · K (kernel arguments) · (state factor)

where `K` is either the truncated pair kernel `K1exp` or its limit `K1lim`.  To compare the two
(the step (S2) of `FINDING_PotPairRows_exists.md`) the integral has to be rewritten in the fibre
form `∫_w ∫_y K w y · G w y` with a **function** `G` of the two kernel variables — because the
comparison lemma `K1exp_sub_K1lim_pairing_le` is stated for an arbitrary `G`.

`block13_fibre` / `blockTwo3_fibre` provide that rewrite for `K1exp` only; this module provides
the *generic* versions, which is what the comparison consumes (apply them to `K1exp` and to
`K1lim`, subtract, and use `K1exp − K1lim` as the kernel).

Everything here is `sorry`-free.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The block I / III.1 shape at an arbitrary kernel.**  The kernel sits at the configuration
slot `p.2` and at the free variable `y` (which is substituted into slot `p.1`); the slot-`p.1`
state factor is `A`, and `B` is the free factor attached to the `u`-integral. -/
theorem block13_fibre_gen {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {K : E3 → E3 → ℂ} {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ}
    (hInt : MeasureTheory.Integrable (fun z : Work.BoseDict.Xn n × E3 =>
      K (z.1 p.2) z.2 *
        (∫ u : E3, star (Θ z.1) * A (z.1 p.1) * star (B u)
          * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)))) :
    (∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * A (x p.1) * K (x p.2) y * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      = ∫ w : E3, ∫ y : E3, K w y *
          (∫ x' : {k : Fin n // k ≠ p.2} → E3, ∫ u : E3,
            star (Θ (fun k => if h : k = p.2 then w else x' ⟨k, h⟩))
              * A ((fun k => if h : k = p.2 then w else x' ⟨k, h⟩) p.1)
              * star (B u)
              * Θ (Function.update (Function.update
                  (fun k => if h : k = p.2 then w else x' ⟨k, h⟩) p.1 y) p.2 u)) := by
  classical
  have hpt : ∀ x : Work.BoseDict.Xn n,
      (∫ y : E3, ∫ u : E3, star (Θ x) * A (x p.1) * K (x p.2) y * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
        = ∫ y : E3, K (x p.2) y *
            (∫ u : E3, star (Θ x) * A (x p.1) * star (B u)
              * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
    intro x
    rw [show (fun y : E3 => ∫ u : E3, star (Θ x) * A (x p.1) * K (x p.2) y
            * star (B u) * Θ (Function.update (Function.update x p.1 y) p.2 u))
          = fun y : E3 => K (x p.2) y *
              (∫ u : E3, star (Θ x) * A (x p.1) * star (B u)
                * Θ (Function.update (Function.update x p.1 y) p.2 u)) from by
        funext y
        rw [show (fun u : E3 => star (Θ x) * A (x p.1) * K (x p.2) y * star (B u)
                * Θ (Function.update (Function.update x p.1 y) p.2 u))
              = fun u : E3 => K (x p.2) y *
                  (star (Θ x) * A (x p.1) * star (B u)
                    * Θ (Function.update (Function.update x p.1 y) p.2 u)) from by
            funext u
            ring]
        exact MeasureTheory.integral_const_mul _ _]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [fibre_kernel_free (i := p.2)
    (K := fun w y => K w y)
    (M := fun x y => ∫ u : E3, star (Θ x) * A (x p.1) * star (B u)
      * Θ (Function.update (Function.update x p.1 y) p.2 u)) hInt]

/-- **The block II.2 shape at an arbitrary kernel.**  The kernel sits at the two configuration
slots `p.1`, `p.2`, and the free variables `y`, `u` carry the state factors `A`, `B`. -/
theorem blockTwo3_fibre_gen {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {K : E3 → E3 → ℂ} {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ}
    (hInt : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n =>
      K (x p.1) (x p.2) *
        (∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u)))) :
    (∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * K (x p.1) (x p.2) * star (A y) * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      = ∫ w₀ : E3, ∫ w₁ : E3, K w₀ w₁ *
          (∫ x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3, ∫ y : E3, ∫ u : E3,
            star (Θ (fun k => if h : k = p.1 then w₀
                              else if h' : k = p.2 then w₁ else x' ⟨k, h, h'⟩))
              * star (A y) * star (B u)
              * Θ (Function.update (Function.update
                  (fun k => if h : k = p.1 then w₀
                            else if h' : k = p.2 then w₁ else x' ⟨k, h, h'⟩) p.1 y) p.2 u)) := by
  classical
  have hpt : ∀ x : Work.BoseDict.Xn n,
      (∫ y : E3, ∫ u : E3, star (Θ x) * K (x p.1) (x p.2)
          * star (A y) * star (B u) * Θ (Function.update (Function.update x p.1 y) p.2 u))
        = K (x p.1) (x p.2) *
          (∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
            * Θ (Function.update (Function.update x p.1 y) p.2 u)) := by
    intro x
    rw [show (fun y : E3 => ∫ u : E3, star (Θ x) * K (x p.1) (x p.2)
            * star (A y) * star (B u) * Θ (Function.update (Function.update x p.1 y) p.2 u))
          = fun y : E3 => K (x p.1) (x p.2) *
              (∫ u : E3, star (Θ x) * star (A y) * star (B u)
                * Θ (Function.update (Function.update x p.1 y) p.2 u)) from by
        funext y
        rw [show (fun u : E3 => star (Θ x) * K (x p.1) (x p.2)
                * star (A y) * star (B u) * Θ (Function.update (Function.update x p.1 y) p.2 u))
              = fun u : E3 => K (x p.1) (x p.2) *
                  (star (Θ x) * star (A y) * star (B u)
                    * Θ (Function.update (Function.update x p.1 y) p.2 u)) from by
            funext u
            ring]
        exact MeasureTheory.integral_const_mul _ _]
    exact MeasureTheory.integral_const_mul _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [fibre_kernel_two (i := p.1) (j := p.2) hp
    (K := fun w w' => K w w')
    (H := fun x => ∫ y : E3, ∫ u : E3, star (Θ x) * star (A y) * star (B u)
      * Θ (Function.update (Function.update x p.1 y) p.2 u)) hInt]

/-- **The block II.1 shape at an arbitrary kernel**: both kernel arguments are free variables
`(u, y)`, and the state factor `A` sits at both configuration slots `p.1`, `p.2`. -/
theorem blockII1_fibre_gen {n : ℕ} (p : Fin n × Fin n) {K : E3 → E3 → ℂ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A : E3 → ℂ}
    (hx : ∀ x : Work.BoseDict.Xn n, MeasureTheory.Integrable
      (Function.uncurry (fun y u : E3 => K u y * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 y) p.2 u))))
      (volume : Measure (E3 × E3)))
    (hSwap : MeasureTheory.Integrable
      (Function.uncurry (fun x : Work.BoseDict.Xn n => fun z : E3 × E3 =>
        K z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))))
      (volume : Measure (Work.BoseDict.Xn n × (E3 × E3))))
    (hProd : MeasureTheory.Integrable
      (fun z : E3 × E3 => ∫ x : Work.BoseDict.Xn n, K z.1 z.2 * (star (Θ x) * A (x p.1)
        * A (x p.2) * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      (volume : Measure (E3 × E3))) :
    (∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * A (x p.1) * A (x p.2) * K u y
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      = ∫ u : E3, ∫ y : E3, K u y * pairG21 p Θ A u y := by
  classical
  have hstep1 : (∫ x : Work.BoseDict.Xn n, ∫ y : E3, ∫ u : E3,
        star (Θ x) * A (x p.1) * A (x p.2) * K u y
          * Θ (Function.update (Function.update x p.1 y) p.2 u))
      = ∫ x : Work.BoseDict.Xn n, ∫ z : E3 × E3,
          K z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2)) := by
    rw [show (fun x : Work.BoseDict.Xn n => ∫ y : E3, ∫ u : E3,
          star (Θ x) * A (x p.1) * A (x p.2) * K u y
            * Θ (Function.update (Function.update x p.1 y) p.2 u))
        = fun x : Work.BoseDict.Xn n => ∫ y : E3, ∫ u : E3,
          K u y * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 y) p.2 u)) from by
      funext x
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      ring]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact (MeasureTheory.integral_prod (fun z : E3 × E3 =>
      K z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2))) (hx x)).symm
  have hstep2 : (∫ x : Work.BoseDict.Xn n, ∫ z : E3 × E3,
        K z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2)))
      = ∫ z : E3 × E3, ∫ x : Work.BoseDict.Xn n,
          K z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2)) :=
    MeasureTheory.integral_integral_swap hSwap
  have hstep3 : (∫ z : E3 × E3, ∫ x : Work.BoseDict.Xn n,
        K z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2)))
      = ∫ z : E3 × E3, ∫ x : Work.BoseDict.Xn n,
          K z.1 z.2 * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)) :=
    (MeasureTheory.integral_prod_swap (f := fun z : E3 × E3 => ∫ x : Work.BoseDict.Xn n,
        K z.2 z.1 * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.1) p.2 z.2)))).symm
  have hstep4 : (∫ z : E3 × E3, ∫ x : Work.BoseDict.Xn n,
        K z.1 z.2 * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1)))
      = ∫ u : E3, ∫ y : E3, ∫ x : Work.BoseDict.Xn n,
          K u y * (star (Θ x) * A (x p.1) * A (x p.2)
            * Θ (Function.update (Function.update x p.1 y) p.2 u)) :=
    MeasureTheory.integral_prod (fun z : E3 × E3 => ∫ x : Work.BoseDict.Xn n,
      K z.1 z.2 * (star (Θ x) * A (x p.1) * A (x p.2)
        * Θ (Function.update (Function.update x p.1 z.2) p.2 z.1))) hProd
  have hstep5 : (∫ u : E3, ∫ y : E3, ∫ x : Work.BoseDict.Xn n,
        K u y * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 y) p.2 u)))
      = ∫ u : E3, ∫ y : E3, K u y * pairG21 p Θ A u y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (∫ x : Work.BoseDict.Xn n, K u y * (star (Θ x) * A (x p.1) * A (x p.2)
          * Θ (Function.update (Function.update x p.1 y) p.2 u)))
        = K u y * pairG21 p Θ A u y
    rw [pairG21, MeasureTheory.integral_const_mul]
  rw [hstep1, hstep2, hstep3, hstep4, hstep5]

/-- **The block III.2 (one-slot) shape at an arbitrary kernel.** -/
theorem slotKernel_fibre_gen {n : ℕ} (j : Fin n) {K : E3 → E3 → ℂ}
    {Θ : Work.BoseDict.Xn n → ℂ}
    (hInt : MeasureTheory.Integrable (fun z : Work.BoseDict.Xn n × E3 =>
      K (z.1 j) z.2 * (star (Θ z.1) * Θ (Function.update z.1 j z.2)))) :
    (∫ x : Work.BoseDict.Xn n, ∫ y : E3,
        star (Θ x) * K (x j) y * Θ (Function.update x j y))
      = ∫ w : E3, ∫ y : E3, K w y * slotG j Θ w y := by
  classical
  have hpt : ∀ x : Work.BoseDict.Xn n,
      (∫ y : E3, star (Θ x) * K (x j) y * Θ (Function.update x j y))
        = ∫ y : E3, K (x j) y * (star (Θ x) * Θ (Function.update x j y)) := by
    intro x
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [fibre_kernel_free (i := j)
    (K := fun w y => K w y)
    (M := fun x y => star (Θ x) * Θ (Function.update x j y)) hInt]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [slotG, insertCoord_eq]

end Work.BoseBoxFock
