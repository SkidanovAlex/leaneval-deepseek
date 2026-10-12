import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Word.fsT_const_mul
import Submission.Work.BoseKinLoc.Word.integral_prod_erase_mul_indU
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseKinLoc.Word.kinForm_prod` — the kinetic word on a product state

The `N`-body localised kinetic word `kinForm N ℓ d s εT b u` (FS `eq:DefT`/`eq:Def_HB`'s
`Σᵢ 𝒯_u^{(i)}`) is the sum of the slot liftings `slotForm N (fsT ℓ d s εT b u) ℓ u i`, and each
slot lifting integrates the *one*-body word `fsT` of the slot-`i` fibre
(`fibre N i Φ x = z ↦ Φ(x_{i←z})`).

On the **product state** `Φ x = ∏ i, θ (x i)` the fibre is a *scalar multiple* of `θ`,

    `fibre n i Φ x = (∏ j ∈ univ.erase i, θ (x j)) • θ`,

and `fsT` is a one-body quadratic form (`Word.fsT_const_mul`), so

    `fsT u (fibre n i Φ x) = (∏ j ∈ univ.erase i, θ (x j))² · fsT u θ`

is a number independent of the slot-`i` variable `x i`.  What remains is a pure
product-measure computation: the integrand becomes the per-slot product
`∏ j, g j (x j)` with `g i = indU ℓ u` and `g j = θ²` for `j ≠ i`, so Fubini
(`MeasureTheory.integral_fintype_prod_volume_eq_prod`) factors the integral and each slot
contributes its own one-particle integral.  Since `∫_{Λ(u)} 1 = ℓ³` and the window factor
`ℓ⁻³` of `slotForm` cancels it (`Word.integral_prod_erase_mul_indU`), every slot contributes
exactly `(∫ θ²)^{n-1} · fsT u θ`, and the sum over the `n` slots gives

    `kinForm n ℓ d s εT b u (∏ θ) = n · (∫ θ²)^{n-1} · fsT u θ`.

This is the identity that turns the `N`-body kinetic word of a product trial state into the
`n`-fold product of the one-body data.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Word

/-- **The slot-`i` fibre of a product state.**  Replacing the `i`-th coordinate by `z` leaves
the product `∏ j, θ (x j)` in the form `(∏_{j ≠ i} θ (x j)) · θ z`, i.e. the fibre is the
scalar multiple of `θ` by the product over the remaining coordinates. -/
lemma fibre_prod_eq {n : ℕ} (θ : EuclideanSpace ℝ (Fin 3) → ℝ) (i : Fin n)
    (x : Submission.BoseGases.X n) :
    Work.BoseKinLoc.fibre n i (fun y : Submission.BoseGases.X n => ∏ j : Fin n, θ (y j)) x
      = fun z => (∏ j ∈ Finset.univ.erase i, θ (x j)) * θ z := by
  funext z
  simp only [Work.BoseKinLoc.fibre]
  rw [← Finset.prod_erase_mul Finset.univ (fun j : Fin n => θ (Function.update x i z j))
      (Finset.mem_univ i), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem kinForm_prod {n : ℕ} {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) {θ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hθ : ContDiff ℝ (⊤ : ENat) θ) (hcs : HasCompactSupport θ) :
    Work.BoseKinLoc.kinForm n ℓ d s εT b u (fun x : Submission.BoseGases.X n => ∏ i : Fin n, θ (x i))
      = (n : ℝ) * (∫ z : EuclideanSpace ℝ (Fin 3), (θ z) ^ 2) ^ (n - 1)
          * Work.BoseKinLoc.fsT ℓ d s εT b u θ := by
  -- the one-body word `fsT` is a quadratic form in the one-body state
  have hscale : ∀ c : ℝ,
      Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => c * θ z)
        = c ^ 2 * Work.BoseKinLoc.fsT ℓ d s εT b u θ :=
    fun c => fsT_const_mul (c := c) u hθ hcs
  rw [Work.BoseKinLoc.kinForm]
  -- every slot contributes the same number `(∫θ²)^(n-1) · fsT θ`
  have hterm : ∀ i : Fin n, Work.BoseKinLoc.slotForm n (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i
      (fun x : Submission.BoseGases.X n => ∏ j : Fin n, θ (x j))
      = (∫ z : EuclideanSpace ℝ (Fin 3), (θ z) ^ 2) ^ (n - 1)
          * Work.BoseKinLoc.fsT ℓ d s εT b u θ := by
    intro i
    -- the fibre of the product state is a multiple of `θ`
    have hfib : ∀ x : Submission.BoseGases.X n,
        Work.BoseKinLoc.fibre n i (fun y : Submission.BoseGases.X n => ∏ j : Fin n, θ (y j)) x
          = fun z => (∏ j ∈ Finset.univ.erase i, θ (x j)) * θ z :=
      fun x => fibre_prod_eq θ i x
    -- hence the one-body word of the fibre is a number independent of `x`
    have hsc : ∀ x : Submission.BoseGases.X n,
        Work.BoseKinLoc.fsT ℓ d s εT b u
            (Work.BoseKinLoc.fibre n i (fun y : Submission.BoseGases.X n => ∏ j : Fin n, θ (y j)) x)
          = (∏ j ∈ Finset.univ.erase i, θ (x j)) ^ 2 * Work.BoseKinLoc.fsT ℓ d s εT b u θ := by
      intro x
      rw [hfib x]
      exact hscale _
    unfold Work.BoseKinLoc.slotForm
    -- pull the constant `fsT u θ` out of the integral, leaving the per-slot product
    have h1 : (∫ x : Submission.BoseGases.X n, Work.BoseKinLoc.indU ℓ u (x i)
          * Work.BoseKinLoc.fsT ℓ d s εT b u
              (Work.BoseKinLoc.fibre n i (fun y : Submission.BoseGases.X n => ∏ j : Fin n, θ (y j)) x))
        = (∫ x : Submission.BoseGases.X n, Work.BoseKinLoc.indU ℓ u (x i)
              * (∏ j ∈ Finset.univ.erase i, (θ (x j)) ^ 2))
            * Work.BoseKinLoc.fsT ℓ d s εT b u θ := by
      rw [show (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ u (x i)
              * Work.BoseKinLoc.fsT ℓ d s εT b u
                  (Work.BoseKinLoc.fibre n i (fun y : Submission.BoseGases.X n => ∏ j : Fin n, θ (y j)) x))
            = fun x => (Work.BoseKinLoc.indU ℓ u (x i)
                * ∏ j ∈ Finset.univ.erase i, (θ (x j)) ^ 2) * Work.BoseKinLoc.fsT ℓ d s εT b u θ from by
        funext x
        rw [hsc x, ← Finset.prod_pow]
        ring]
      rw [MeasureTheory.integral_mul_const]
    rw [h1, integral_prod_erase_mul_indU hℓ u i (fun z => (θ z) ^ 2)]
    -- the window factor `ℓ⁻³` of the slot lifting cancels the box volume `ℓ³`
    field_simp
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  ring

end Work.BoseKinLoc.Word
