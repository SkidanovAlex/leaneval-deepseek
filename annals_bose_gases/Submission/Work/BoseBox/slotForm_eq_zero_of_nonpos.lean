import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.slotForm_eq_zero_of_nonpos` — the slot lifting at a nonpositive box side

The slot-`i` lifting of a one-body form `q` (FS `eq:Def_HB`) is

    `slotForm N q ℓ u i Φ = ℓ⁻³ ∫_x 1_{Λ(u)}(xᵢ) · q(fibre N i Φ x)`,

integration over the `N`-body configuration space `X N` and with the moving box
`Λ(u) = ℓu + acube ℓ` (`bsBox ℓ u`).

For `ℓ ≤ 0` the whole expression is `0`, for two *different* reasons, one per case:

* `ℓ < 0`: the centred cube `acube ℓ = {y | ∀ m, y m ∈ Icc (−ℓ/2) (ℓ/2)}` is empty
  (its interval is `Icc` of a *larger* left endpoint than its right endpoint), hence
  `Λ(u) = ∅`, hence the indicator `1_{Λ(u)}` vanishes *pointwise*.  The integrand is
  then the zero function, so the integral is `0` and no integrability hypothesis is
  needed anywhere;
* `ℓ = 0`: here `acube 0 = {0}` is *not* empty (the box degenerates to the single point
  `0`, i.e. `Λ(u) = {0}` for every `u`), but the prefactor `0 ^ (−3 : ℤ) = (0³)⁻¹ = 0`
  already kills the product — this is `inv_zero`, not a limit statement.

This is the standard "degenerate box" lemma: it discharges the `ℓ ≤ 0` branch of the
box/kinetic localisation where the localisation scale is meaningless, and it needs no
regularity or support hypothesis on the state `Φ` (the vanishing is pointwise in the
first case and a pure algebraic zero in the second).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBox

/-- For a strictly negative side length the moving box `Λ(u)` is empty: the centred cube
`acube ℓ` is empty because `Icc (−ℓ/2) (ℓ/2)` has its endpoints in the wrong order. -/
lemma lamBox_eq_empty_of_neg {ℓ : ℝ} (hℓ : ℓ < 0) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseKinLoc.lamBox ℓ u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox, Set.mem_ofPred_eq] at hx
  rw [Submission.BoseGases.mem_acube_iff] at hx
  have h := hx 0
  simp only [Set.mem_Icc] at h
  linarith [h.1, h.2]

/-- For a strictly negative side length the box indicator `1_{Λ(u)}` is the zero function. -/
lemma indU_eq_zero_of_neg {ℓ : ℝ} (hℓ : ℓ < 0) (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseKinLoc.indU ℓ u = fun _ => (0 : ℝ) := by
  funext z
  rw [Work.BoseKinLoc.indU, Set.indicator_of_notMem (f := fun _ => (1 : ℝ))]
  rw [lamBox_eq_empty_of_neg hℓ u]
  exact Set.notMem_empty z

theorem slotForm_eq_zero_of_nonpos {N : ℕ} {ℓ : ℝ} (hℓ : ℓ ≤ 0)
    (q : (EuclideanSpace ℝ (Fin 3) → ℝ) → ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (i : Fin N) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.BoseKinLoc.slotForm N q ℓ u i Φ = 0 := by
  rw [Work.BoseKinLoc.slotForm]
  rcases lt_or_eq_of_le hℓ with hlt | heq
  · -- `ℓ < 0`: the indicator vanishes pointwise, so the integrand is the zero function.
    have hfun : (fun x : Submission.BoseGases.X N =>
        Work.BoseKinLoc.indU ℓ u (x i) * q (Work.BoseKinLoc.fibre N i Φ x)) = fun _ => 0 := by
      funext x
      rw [show Work.BoseKinLoc.indU ℓ u (x i) = 0 from
        congrFun (indU_eq_zero_of_neg hlt u) (x i), zero_mul]
    rw [hfun]
    simp
  · -- `ℓ = 0`: the prefactor `0 ^ (−3 : ℤ) = (0³)⁻¹` already vanishes.
    subst heq
    simp

end Work.BoseBox
