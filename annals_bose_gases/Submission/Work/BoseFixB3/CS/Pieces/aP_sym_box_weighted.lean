import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.peel_weighted
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.aP_sym_box_weighted`

Weighted self-adjointness of the slot-`i` centred-box mean `aP ℓ i` over `abox N ℓ`,
against a weight `W` that is constant in the slot-`i` coordinate:

  `∫_{abox N ℓ} (PᵢΦ)·Ψ·W = ∫_{abox N ℓ} Φ·(PᵢΨ)·W`.

The unweighted case is `BoseGases.aP_sym_box` (`Submission/Q0Sector.lean`); here the extra
weight is handled by the one-slot peel: after peeling slot `i` out of `abox (n+1) ℓ`
(`BoseGases.abox_integral_peel`), the slot-`i` invariance of `W` makes the weight collapse to
`W (kcInsN n i (0,r))` on the fibre, and the fibre integral

  `∫_{y∈acube ℓ} (PᵢΦ)(kcInsN n i (y,r)) · Ψ (kcInsN n i (y,r)) · W (kcInsN n i (y,r))`

takes the *symmetric* form `(1/ℓ³)·(∫Φ) · ((∫Ψ) · W(0,r))`.  Applying the same computation
to the pair `(Ψ,Φ)` and comparing the two double integrals gives the claim.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Weighted one-slot peel of the `aP`-pairing.**  If the weight `W` is constant in slot `i`,
then the weighted pairing of `aP ℓ i Φ` with `Ψ` peels to the double integral whose fibre value
is `(1/ℓ³)·(∫_z Φ(kcInsN i (z,r))) · ((∫_y Ψ(kcInsN i (y,r))) · W(kcInsN i (0,r)))`. -/
theorem peel_aP_mul_weight {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1))
    {Φ Ψ W : Submission.BoseGases.X (n + 1) → ℝ}
    (hW : ∀ (x : Submission.BoseGases.X (n + 1)) (z : E3),
      W (Function.update x i z) = W x)
    (hΦc : Continuous Φ) (hΨc : Continuous Ψ) (hWc : Continuous W) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        Submission.BoseGases.aP ℓ i Φ x * Ψ x * W x)
      = ∫ r : Submission.BoseGases.X n,
          (1 / ℓ ^ 3)
            * (∫ z in Submission.BoseGases.acube ℓ, Φ (Submission.BoseGases.kcInsN n i (z, r)))
            * ((∫ y in Submission.BoseGases.acube ℓ, Ψ (Submission.BoseGases.kcInsN n i (y, r)))
                * W (Submission.BoseGases.kcInsN n i (0, r)))
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ)) := by
  -- Integrability of the integrand, from the corpus lemma `integrableOn_mul_aP` after commuting.
  have hInt' : IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
      (Ψ x * W x) * Submission.BoseGases.aP ℓ i Φ x)
      (Submission.BoseGases.abox (n + 1) ℓ) volume :=
    Submission.BoseGases.integrableOn_mul_aP hℓ i (hΨc.mul hWc) hΦc
  have hInt : IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
      Submission.BoseGases.aP ℓ i Φ x * Ψ x * W x)
      (Submission.BoseGases.abox (n + 1) ℓ) volume := by
    convert hInt' using 1
    ext x
    ring
  -- Slot-`i` invariance of `W` in inserted coordinates.
  have hWy : ∀ (y : E3) (r : Submission.BoseGases.X n),
      W (Submission.BoseGases.kcInsN n i (y, r)) = W (Submission.BoseGases.kcInsN n i (0, r)) := by
    intro y r
    rw [Submission.BoseGases.kcInsN_update_zero i y r]
    exact hW (Submission.BoseGases.kcInsN n i (0, r)) y
  have hP := Submission.BoseGases.abox_integral_peel (i := i)
    (F := fun x : Submission.BoseGases.X (n + 1) =>
      Submission.BoseGases.aP ℓ i Φ x * Ψ x * W x) hInt
  rw [hP]
  apply integral_congr_ae
  filter_upwards with r
  -- Fibre computation: `aP` is the mean `(1/ℓ³)∫Φ`, and `W` is constant in `y`.
  have h1 : (∫ y in Submission.BoseGases.acube ℓ,
      Submission.BoseGases.aP ℓ i Φ (Submission.BoseGases.kcInsN n i (y, r))
        * Ψ (Submission.BoseGases.kcInsN n i (y, r))
        * W (Submission.BoseGases.kcInsN n i (y, r)))
      = ∫ y in Submission.BoseGases.acube ℓ,
          ((1 / ℓ ^ 3) * (∫ z in Submission.BoseGases.acube ℓ,
            Φ (Submission.BoseGases.kcInsN n i (z, r))))
            * (Ψ (Submission.BoseGases.kcInsN n i (y, r))
                * W (Submission.BoseGases.kcInsN n i (0, r))) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [Submission.BoseGases.aP_kcInsN (ℓ := ℓ) (i := i) (Φ := Φ) y r, hWy y r]
    ring
  rw [h1, MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]

/-- **Weighted self-adjointness of `Pᵢ` over the centred box.**  For a weight `W` that is
constant in the slot-`i` coordinate, `∫ (PᵢΦ)·Ψ·W = ∫ Φ·(PᵢΨ)·W`. -/
theorem aP_sym_box_weighted {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {W : Submission.BoseGases.X N → ℝ}
    (hW : ∀ (x : Submission.BoseGases.X N) (z : EuclideanSpace ℝ (Fin 3)),
      W (Function.update x i z) = W x)
    (hWc : Continuous W)
    {Φ Ψ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aP ℓ i Φ x) * Ψ x * W x)
      = ∫ x in Submission.BoseGases.abox N ℓ, Φ x * (Submission.BoseGases.aP ℓ i Ψ x) * W x := by
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero i.val)
  | succ n =>
    have h1 := peel_aP_mul_weight (n := n) (ℓ := ℓ) hℓ i hW hΦc hΨc hWc
    have h2 := peel_aP_mul_weight (n := n) (ℓ := ℓ) hℓ i hW hΨc hΦc hWc
    have hRHS : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        Φ x * (Submission.BoseGases.aP ℓ i Ψ x) * W x)
        = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            Submission.BoseGases.aP ℓ i Ψ x * Φ x * W x := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [h1, hRHS, h2]
    apply integral_congr_ae
    filter_upwards with r
    ring

end Work.BoseFixB3.CS.Pieces
