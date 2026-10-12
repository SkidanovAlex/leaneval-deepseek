import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.peel_aP_g` — the one-body `Pᵢ`-slot peel against a general weight

Let `Λ(ℓ) = acube ℓ` be the centred cube and `abox (n+1) ℓ` the centred
`(n+1)`-particle box, and let `Pᵢ = aP ℓ i` be the projection onto the
functions constant in particle `i` (the mean over `Λ(ℓ)`).

Since `PᵢΦ` does not depend on the `i`-th coordinate, the measure-preserving
peel `abox (n+1) ℓ ≅ acube ℓ × abox n ℓ` (`kcInsN n i`) makes the whole
`g(xᵢ)`-weighted integral of `(PᵢΦ)²` factor:

`∫_{abox (n+1) ℓ} (PᵢΦ)² g(xᵢ) = (∫_{acube ℓ} g) · (∫_{abox n ℓ} (PᵢΦ)²(·,r))`

and, applying the same peel to the constant weight `1`,

`∫_{abox (n+1) ℓ} (PᵢΦ)² = ℓ³ · (∫_{abox n ℓ} (PᵢΦ)²(·,r))`.

Dividing gives the stated identity with `Tvol = ∫_{acube ℓ} g`.

The argument is the one-body mirror of `AeValue.one_value_aux_ae` (there the
weight was the fibre integral `∫_y w₁(xᵢ,y)`); the only extra ingredient is
the integrability of the pullback `g ∘ πᵢ` over the box, which is
`Q0Value.integrableOn_comp_coord` (supplied here by `hint`, i.e.
`IntegrableOn g (acube ℓ)`).  The hypotheses `hgm`, `hg`, `hKU` are kept for
the caller's convenience and are not needed by this argument.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real

namespace Work.BoseFixB1.WB

open Submission.BoseGases

theorem peel_aP_g {n : ℕ} {ℓ Tvol KU : ℝ} (hℓ : 0 < ℓ) (i : Fin (n + 1))
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : Continuous Φ)
    {g : ℝ³ → ℝ} (hgm : AEMeasurable g MeasureTheory.volume)
    (hint : MeasureTheory.IntegrableOn g (Submission.BoseGases.acube ℓ))
    (hg : ∀ z : ℝ³, 0 ≤ g z) (hTvol : (∫ z in Submission.BoseGases.acube ℓ, g z) = Tvol)
    (hKU : ∀ z : ℝ³, g z ≤ KU) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ, (Submission.BoseGases.aP ℓ i Φ x) ^ 2 * g (x i))
      = (Tvol / ℓ ^ 3) * ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Submission.BoseGases.aP ℓ i Φ x) ^ 2 := by
  have hint' : Integrable g ((volume : Measure ℝ³).restrict (acube ℓ)) := hint
  let G : X (n + 1) → ℝ := fun x => (aP ℓ i Φ x) ^ 2
  let T1 : ℝ := ∫ r in abox n ℓ, G (kcInsN n i ((0 : ℝ³), r))
  -- integrability of `(PᵢΦ)²`
  have hG : IntegrableOn G (abox (n + 1) ℓ) volume := by
    simpa [G] using integrableOn_sq_aP hℓ i hΦ
  -- integrability of the pullback `g ∘ πᵢ` over the box
  have hgi : IntegrableOn (fun x : X (n + 1) => g (x i)) (abox (n + 1) ℓ) volume :=
    integrableOn_comp_coord hℓ i hint'.aestronglyMeasurable hint'
  have hgabs : Integrable (fun x : X (n + 1) => |g (x i)|)
      (volume.restrict (abox (n + 1) ℓ)) := by
    have h := hgi.abs
    simpa [Real.norm_eq_abs] using h
  have hcG : Continuous G := by simpa [G] using aP_sq_continuous hℓ i hΦ
  obtain ⟨B, hB⟩ := (abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
    (s := abox (n + 1) ℓ) (f := G) hcG.continuousOn
  have hbnd : ∀ᵐ x ∂(volume.restrict (abox (n + 1) ℓ)),
      ‖G x * g (x i)‖ ≤ B * |g (x i)| := by
    rw [ae_restrict_iff' (abox_measurable (n + 1) ℓ)]
    apply ae_of_all
    intro x hx
    have hb' := hB x hx
    have hle : |G x| ≤ B := by simpa [Real.norm_eq_abs] using hb'
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have hmeas : AEStronglyMeasurable (fun x : X (n + 1) => G x * g (x i))
      (volume.restrict (abox (n + 1) ℓ)) :=
    (hcG.measurable.aestronglyMeasurable).mul (aem_comp_coord i hint'.aestronglyMeasurable)
  have hdomin : Integrable (fun x : X (n + 1) => B * |g (x i)|)
      (volume.restrict (abox (n + 1) ℓ)) := hgabs.const_mul B
  have hF0 : IntegrableOn (fun x : X (n + 1) => G x * g (x i)) (abox (n + 1) ℓ) volume :=
    Integrable.mono' hdomin hmeas hbnd
  -- the weighted integral factors
  have hpeel1 := abox_integral_peel (n := n) (i := i)
    (F := fun x : X (n + 1) => G x * g (x i)) hF0
  have hmain : (∫ x in abox (n + 1) ℓ, G x * g (x i))
      = (∫ z in acube ℓ, g z) * T1 := by
    calc
      (∫ x in abox (n + 1) ℓ, G x * g (x i))
          = ∫ r in abox n ℓ, ∫ t in acube ℓ, G (kcInsN n i (t, r)) * g t := by
            rw [hpeel1]
            apply integral_congr_ae
            filter_upwards with r
            apply integral_congr_ae
            filter_upwards with t
            rw [kc_insN_apply_same n i t r]
      _ = ∫ r in abox n ℓ, ∫ t in acube ℓ, G (kcInsN n i (0, r)) * g t := by
            apply integral_congr_ae
            filter_upwards with r
            apply integral_congr_ae
            filter_upwards with t
            have hGfib : G (kcInsN n i (t, r)) = G (kcInsN n i (0, r)) := by
              dsimp [G]
              exact congrArg (fun u : ℝ => u ^ 2) (aP_fiber_const_one hℓ i hΦ t r)
            rw [hGfib]
      _ = ∫ r in abox n ℓ, G (kcInsN n i (0, r)) * (∫ z in acube ℓ, g z) := by
            apply integral_congr_ae
            filter_upwards with r
            rw [MeasureTheory.integral_const_mul]
      _ = (∫ z in acube ℓ, g z) * T1 := by
            dsimp [T1]
            rw [MeasureTheory.integral_mul_const]
            ring
  -- the unweighted integral, by the same peel
  have hpeel2 := abox_integral_peel (n := n) (i := i) (F := G) hG
  have hGvol : (∫ x in abox (n + 1) ℓ, G x) = (ℓ ^ 3) * T1 := by
    calc
      (∫ x in abox (n + 1) ℓ, G x)
          = ∫ r in abox n ℓ, ∫ t in acube ℓ, G (kcInsN n i (t, r)) := hpeel2
      _ = ∫ r in abox n ℓ, ∫ t in acube ℓ, G (kcInsN n i (0, r)) := by
            apply integral_congr_ae
            filter_upwards with r
            apply integral_congr_ae
            filter_upwards with t
            have hGfib : G (kcInsN n i (t, r)) = G (kcInsN n i (0, r)) := by
              dsimp [G]
              exact congrArg (fun u : ℝ => u ^ 2) (aP_fiber_const_one hℓ i hΦ t r)
            rw [hGfib]
      _ = (ℓ ^ 3) * T1 := by
            dsimp [T1]
            calc
              (∫ r in abox n ℓ, ∫ t in acube ℓ, G (kcInsN n i (0, r)))
                  = ∫ r in abox n ℓ, (ℓ ^ 3) * G (kcInsN n i (0, r)) := by
                    apply integral_congr_ae
                    filter_upwards with r
                    rw [integral_const_acube ℓ hℓ]
                    ring
              _ = (ℓ ^ 3) * (∫ r in abox n ℓ, G (kcInsN n i (0, r))) := by
                    rw [MeasureTheory.integral_const_mul]
  calc
    (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2 * g (x i))
        = (∫ z in acube ℓ, g z) * T1 := by simpa [G] using hmain
    _ = Tvol * T1 := by rw [hTvol]
    _ = (Tvol / ℓ ^ 3) * ((ℓ ^ 3) * T1) := by
          have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
          field_simp
    _ = (Tvol / ℓ ^ 3) * (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2) := by
          have hvol : (∫ x in abox (n + 1) ℓ, (aP ℓ i Φ x) ^ 2) = (ℓ ^ 3) * T1 := by
            simpa [G] using hGvol
          rw [hvol]

end Work.BoseFixB1.WB
