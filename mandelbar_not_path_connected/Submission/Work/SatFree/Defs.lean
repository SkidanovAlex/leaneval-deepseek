/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SatFree team
-/
import Mathlib
import Submission.Work.FatouCoord.Flower.GermDefs
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `SatFree` — the vocabulary of sign-free half-plane saturation

This is the language layer of the area `Work.SatFree`.  The area replaces the numeric hypothesis
`Ha1 : Re((2/3)·F'''/F''²) < 1` (i.e. `Re (1 - a) > 0` for the Abel parameter `a` of the germ at
the parabolic point) that `Work.GATE2.PL.exists_flowerFix_saturating` uses in order to produce a
flower whose Fatou coordinate `φa` surjects onto a right half-plane from its invariant sub-petal
`Pg`.

The obstruction when `κ₀ = 1 - a` has non-positive real part is that the attractive chart
half-plane `{Re W > Mh}` is **not** mapped onto a right half-plane by the chart Fatou coordinate
`W ↦ W - (1-a) log W`: its image is the log-parabola `{Re τ ≳ |κ₀| log ‖τ‖}`.  What *is* true
without any sign hypothesis is the **log-slack** statement
(`SatFree.fatouCoordW_saturates_log`): every `τ` with `X + K (log (1 + ‖τ‖) + π) < Re τ` is
attained, with the preimage controlled from below in both coordinates.  Feeding `τ + m` into that
statement for `m = O(log ‖τ‖)` and pulling back `m` steps along the *wide* petal (which is
invariant for the chart dynamics and loses only `1 + O(1/‖W‖)` of `sgauge` per step) produces a
point of the petal whose `φa`-value is exactly `τ`.

Two definitions, used throughout the area:

* `SatHalfPlane g Pa φa` — the saturation certificate that GATE2 consumes: for all `τ` far to the
  right there is `z ∈ Pa` with `g z ∈ Pa` and `φa z = τ`.  (The extra condition `g z ∈ Pa` is
  what lets `FlowerFixOfWideSat.flowerFix_of_wideSat` take `Pg = {z ∈ Pa | g z ∈ Pa ∧
  X < Re φa z}`, which is automatically `g`-invariant, without knowing `φa` on `Pg`.)
* `logSlack K X τ = X + K * (log (1 + ‖τ‖) + π)` — the amount by which `Re τ` must beat the
  threshold in the sign-free saturation statement.
* `chartSector z₀ lam M` — the wide chart sector of level `M` transported to the dynamical plane
  by the affine chart `z ↦ -1/((z - z₀)/lam) = lam * (-1/(z - z₀))`.  This is the shape of the
  region that the `SatFree` flower's petal `Pa` contains (needed by PARIMPL2 for the restricted
  `hLB_h` of the wire note §A.4 R1).
-/

open scoped Topology
open Set Filter Metric Function

namespace Work.SatFree

noncomputable section

/-- **The saturation certificate of a Fatou coordinate.**  `φa` takes every value of a right
half-plane on `Pa`, at a point whose image under `g` is again in `Pa`.

This is `Work.GATE2.SaturatedFlower` without any reference to the `FlowerFix`: in the `SatFree`
development the half-petal `Pg` is *derived* from this property
(`SatFree.flowerFix_of_wideSat`), rather than being an input. -/
def SatHalfPlane (g : ℂ → ℂ) (Pa : Set ℂ) (φa : ℂ → ℂ) : Prop :=
  ∃ X : ℝ, ∀ τ : ℂ, X < τ.re → ∃ z : ℂ, z ∈ Pa ∧ g z ∈ Pa ∧ φa z = τ

/-- `SatHalfPlane` is monotone in the petal: a certificate on `Pa` is a certificate on any larger
set (the certificate only evaluates `φa` at points of `Pa`, and asks `g z` to stay in `Pa`). -/
theorem SatHalfPlane.mono {g : ℂ → ℂ} {Pa Pa' : Set ℂ} {φa : ℂ → ℂ}
    (h : SatHalfPlane g Pa φa) (hsub : Pa ⊆ Pa') : SatHalfPlane g Pa' φa := by
  obtain ⟨X, hX⟩ := h
  exact ⟨X, fun τ hτ => by
    obtain ⟨z, hz, hgz, hφ⟩ := hX τ hτ
    exact ⟨z, hsub hz, hsub hgz, hφ⟩⟩

/-- **The log slack** of a point `τ`: the threshold `X + K (log (1 + ‖τ‖) + π)` that `Re τ` has
to beat in the sign-free saturation statement `SatFree.fatouCoordW_saturates_log`.

Written as a definition because it occurs in the hypothesis and in both quantitative conclusions
of that theorem. -/
def logSlack (K X : ℝ) (τ : ℂ) : ℝ := X + K * (Real.log (1 + ‖τ‖) + Real.pi)

@[simp] theorem logSlack_apply (K X : ℝ) (τ : ℂ) :
    logSlack K X τ = X + K * (Real.log (1 + ‖τ‖) + Real.pi) := rfl

/-- **The wide chart sector at `z₀` with scale `lam`**, transported to the dynamical plane: a point
`z ≠ z₀` lies in it when its chart value `lam * (-1/(z - z₀))` has `sgauge > M`.

For the germ at `0` and `lam = 1` this is `Work.FatouCoord.Flower.WidePetal M` in the chart
`chart u = -1/u`.  In the affine normalization `z = z₀ + lam * u` of a parabolic germ, the germ's
wide petal becomes exactly `chartSector z₀ lam M` (`chartSector_eq_image`). -/
def chartSector (z₀ lam : ℂ) (M : ℝ) : Set ℂ :=
  {z : ℂ | z ≠ z₀ ∧ M < Work.FatouCoord.Flower.sgauge (lam * (-1 / (z - z₀)))}

@[simp] theorem mem_chartSector {z₀ lam : ℂ} {M : ℝ} {z : ℂ} :
    z ∈ chartSector z₀ lam M ↔
      z ≠ z₀ ∧ M < Work.FatouCoord.Flower.sgauge (lam * (-1 / (z - z₀))) := Iff.rfl

/-- **The wide chart sector is the image of the wide sector under the affine chart**: for
`lam ≠ 0`, `chartSector z₀ lam M = (fun W => z₀ - lam / W) '' {W | W ≠ 0 ∧ M < sgauge W}`.

This is the bridge between the germ statement `WidePetal Ms ⊆ fl.Pa` and the dynamical statement
`chartSector z₁ lam Ms ⊆ fl.Pa`. -/
theorem chartSector_eq_image {z₀ lam : ℂ} (hlam : lam ≠ 0) (M : ℝ) :
    chartSector z₀ lam M = (fun W : ℂ => z₀ - lam / W) '' {W : ℂ | W ≠ 0 ∧ M <
      Work.FatouCoord.Flower.sgauge W} := by
  ext z
  constructor
  · rintro ⟨hz, hM⟩
    refine ⟨lam * (-1 / (z - z₀)), ⟨?_, hM⟩, ?_⟩
    · intro h0
      have h1 : -1 / (z - z₀) = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hlam
        · exact h
      have h2 : (z - z₀)⁻¹ = 0 := by
        rw [neg_div, neg_eq_zero, one_div] at h1
        exact h1
      exact sub_ne_zero.mpr hz (inv_eq_zero.mp h2)
    · change z₀ - lam / (lam * (-1 / (z - z₀))) = z
      field_simp
      ring
  · rintro ⟨W, ⟨hW, hM⟩, rfl⟩
    have h1 : -1 / (z₀ - lam / W - z₀) = W / lam := by
      rw [sub_sub_cancel_left]
      field_simp
    have h2 : z₀ - lam / W ≠ z₀ := by
      intro h
      have h3 : lam / W = 0 := by linear_combination -h
      exact (div_ne_zero_iff.mpr ⟨hlam, hW⟩) h3
    refine ⟨h2, ?_⟩
    show M < Work.FatouCoord.Flower.sgauge (lam * (-1 / (z₀ - lam / W - z₀)))
    rw [h1]
    have h3 : lam * (W / lam) = W := by
      field_simp
    rw [h3]
    exact hM

end

end Work.SatFree
