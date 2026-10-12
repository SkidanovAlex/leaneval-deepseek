import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBox.fibre_hasCompactSupport
import Submission.Work.BoseBox.fibre_kcDir_L2
import Submission.Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral
import Submission.Work.BoseKinLoc.Sector.fsT_bound_all
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.tKinAmbWordBound`

Boundedness of the localised kinetic word `𝒯_u` (`Work.BoseBox.tKinAmb`) as a function of the
translation parameter `u`, on the localisation region `coverU ℓ L`.

The word is the `N`-body lifting `Work.BoseKinLoc.kinForm N ℓ d s ε_T b u Ψ` of the one-body word
`fsT`, i.e. the sum of the slot liftings `Work.BoseKinLoc.slotForm`; each slot lifting peels
(`Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral`) to the integral of `fsT` over the fibre

`slotForm (n+1) q ℓ u i Ψ = ∫_r q (fun z => Ψ (kcInsN n i (z, r)))`.

The one-body word satisfies the uniform `H¹` bound of `Work.BoseKinLoc.Kinetic.fsT_H1_bound_all`
(the constant depends only on `(ℓ, d, s, ε_T, b)`, **not** on the translation parameter `u`).
Integrating the right-hand side over the remaining coordinates and undoing the peeling
(`Work.BoseKinLoc.Kinetic.integral_fibre_sq` for the `L²` term and `fibre_kcDir_L2` for the
`H¹` term) produces a bound which does not depend on `u` at all.

## Main result

`tKinAmbWordBound`: `|tKinAmb N L ℓ d s eT b u Ψ| ≤ C` on `coverU ℓ L`, for a constant `C`
depending only on `(N, L, ℓ, d, s, ε_T, b, Ψ)`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBox

/-- **The per-slot bound.**  For a smooth compactly supported state `Ψ` of the box `(n+1, L)`, the
`i`-th slot lifting of the kinetic word is bounded, uniformly in the translation parameter `u`, by
the `H¹` norm of `Ψ` in the slot `i` (times the one-body constant `C₀`). -/
private lemma slotForm_abs_bound {n : ℕ} {ℓ d s eT b L : ℝ} (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨcs : HasCompactSupport Ψ)
    (hsupp : tsupport Ψ ⊆ _root_.BoseGases.box (n + 1) L)
    (C₀ : ℝ)
    (hC₀ : ∀ (u : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        |Work.BoseKinLoc.fsT ℓ d s eT b u ψ| ≤
          C₀ * ((∫ z : EuclideanSpace ℝ (Fin 3), ψ z ^ 2)
            + ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
                (fderiv ℝ ψ z) (Submission.BoseGases.kcStdBasis k) ^ 2))
    (i : Fin (n + 1)) (u : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s eT b u) ℓ u i Ψ|
      ≤ C₀ * ((∫ x : Submission.BoseGases.X (n + 1), (Ψ x) ^ 2)
        + ∑ k : Fin 3, ∫ x : Submission.BoseGases.X (n + 1),
            (fderiv ℝ Ψ x) (Submission.BoseGases.kcDir (n + 1) i k) ^ 2) := by
  -- integrability and the values of the two fibral integrals
  have hE0 := Work.BoseKinLoc.Kinetic.integral_fibre_sq hΨ hΨcs i
  have hDsp_int : MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
      ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
        (fderiv ℝ Ψ (Submission.BoseGases.kcInsN n i (z, r)))
          (Submission.BoseGases.kcDir (n + 1) i k) ^ 2) :=
    MeasureTheory.integrable_finsetSum Finset.univ (fun k _ => (fibre_kcDir_L2 hΨ hsupp i k).1)
  have hDsp_eq : (∫ r : Submission.BoseGases.X n,
      ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
        (fderiv ℝ Ψ (Submission.BoseGases.kcInsN n i (z, r)))
          (Submission.BoseGases.kcDir (n + 1) i k) ^ 2)
      = ∑ k : Fin 3, ∫ x : Submission.BoseGases.X (n + 1),
          (fderiv ℝ Ψ x) (Submission.BoseGases.kcDir (n + 1) i k) ^ 2 := by
    rw [MeasureTheory.integral_finsetSum Finset.univ
      (fun k _ => (fibre_kcDir_L2 hΨ hsupp i k).1)]
    exact Finset.sum_congr rfl (fun k _ => (fibre_kcDir_L2 hΨ hsupp i k).2)
  -- the dominating function is integrable
  have hg_int : MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
      C₀ * ((∫ z : EuclideanSpace ℝ (Fin 3),
              (Ψ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2)
        + ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
            (fderiv ℝ Ψ (Submission.BoseGases.kcInsN n i (z, r)))
              (Submission.BoseGases.kcDir (n + 1) i k) ^ 2)) :=
    (hE0.1.add hDsp_int).const_mul C₀
  -- the pointwise bound on each fibre
  have hpt : ∀ r : Submission.BoseGases.X n,
      ‖Work.BoseKinLoc.fsT ℓ d s eT b u (fun z : EuclideanSpace ℝ (Fin 3) =>
          Ψ (Submission.BoseGases.kcInsN n i (z, r)))‖
        ≤ C₀ * ((∫ z : EuclideanSpace ℝ (Fin 3),
              (Ψ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2)
          + ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
              (fderiv ℝ Ψ (Submission.BoseGases.kcInsN n i (z, r)))
                (Submission.BoseGases.kcDir (n + 1) i k) ^ 2) := by
    intro r
    have h1 := hC₀ u (fun z : EuclideanSpace ℝ (Fin 3) =>
        Ψ (Submission.BoseGases.kcInsN n i (z, r)))
      (Submission.BoseGases.fiber_contDiff i hΨ r)
      (fibre_hasCompactSupport hsupp i r)
    have h2 : (∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
        (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) =>
          Ψ (Submission.BoseGases.kcInsN n i (z, r))) z)
          (Submission.BoseGases.kcStdBasis k) ^ 2)
        = ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
            (fderiv ℝ Ψ (Submission.BoseGases.kcInsN n i (z, r)))
              (Submission.BoseGases.kcDir (n + 1) i k) ^ 2 := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      exact congrArg (fun t : ℝ => t ^ 2) (Submission.BoseGases.fiber_fderiv_kcDir i hΨ r z k)
    rw [h2] at h1
    simpa [Real.norm_eq_abs] using h1
  -- the peeled slot integral, dominated by the integrable function above
  rw [Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral hℓ
    (Work.BoseKinLoc.fsT ℓ d s eT b u) u i Ψ]
  have hmain := MeasureTheory.norm_integral_le_of_norm_le hg_int
    (Filter.Eventually.of_forall hpt)
  have hgval : (∫ r : Submission.BoseGases.X n,
      C₀ * ((∫ z : EuclideanSpace ℝ (Fin 3),
              (Ψ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2)
        + ∑ k : Fin 3, ∫ z : EuclideanSpace ℝ (Fin 3),
            (fderiv ℝ Ψ (Submission.BoseGases.kcInsN n i (z, r)))
              (Submission.BoseGases.kcDir (n + 1) i k) ^ 2))
      = C₀ * ((∫ x : Submission.BoseGases.X (n + 1), (Ψ x) ^ 2)
        + ∑ k : Fin 3, ∫ x : Submission.BoseGases.X (n + 1),
            (fderiv ℝ Ψ x) (Submission.BoseGases.kcDir (n + 1) i k) ^ 2) := by
    have hsum := MeasureTheory.integral_add hE0.1 hDsp_int
    rw [MeasureTheory.integral_const_mul, hsum, hE0.2, hDsp_eq]
  rw [hgval] at hmain
  simpa using hmain

theorem tKinAmbWordBound {N : ℕ} {L ℓ d s eT b : ℝ} (hL : 0 < L) (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hsupp : tsupport Ψ ⊆ _root_.BoseGases.box N L)
    {K : ℝ} (hK : 0 ≤ K)
    (hdec : ∀ u ∈ Work.BoseBox.coverU ℓ L, ∀ x ∈ _root_.BoseGases.box N L, ∀ i : Fin N,
      ∀ p : EuclideanSpace ℝ (Fin 3),
      ‖Work.SmallBoxTBWord.tBamp (Work.BoseBox.chiBig ℓ u) p
        (Work.UBBInputs8.boxQInd (ℓ ^ 3) (Work.BoseBox.bigBox ℓ u) i Ψ) i x‖
        ≤ K / (1 + ‖p‖) ^ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Work.BoseBox.coverU ℓ L,
      |Work.BoseBox.tKinAmb N L ℓ d s eT b u Ψ| ≤ C := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := Work.BoseKinLoc.Kinetic.fsT_H1_bound_all (ℓ := ℓ) (d := d)
    (s := s) (εT := eT) (b := b) hℓ
  cases N with
  | zero =>
      refine ⟨0, le_refl 0, fun u _ => ?_⟩
      have hzero : Work.BoseBox.tKinAmb 0 L ℓ d s eT b u Ψ = 0 := by
        simp [Work.BoseBox.tKinAmb, Work.BoseBox.tKinWord, Work.BoseKinLoc.kinForm]
      rw [hzero, abs_zero]
  | succ n =>
      have hΨcs : HasCompactSupport Ψ :=
        IsCompact.of_isClosed_subset (Submission.BoseGases.box_compact hL) (isClosed_tsupport Ψ)
          (closure_minimal ((subset_tsupport Ψ).trans hsupp) (Submission.BoseGases.box_closed L))
      refine ⟨∑ i : Fin (n + 1), C₀ * ((∫ x : Submission.BoseGases.X (n + 1), (Ψ x) ^ 2)
          + ∑ k : Fin 3, ∫ x : Submission.BoseGases.X (n + 1),
              (fderiv ℝ Ψ x) (Submission.BoseGases.kcDir (n + 1) i k) ^ 2), ?_, ?_⟩
      · refine Finset.sum_nonneg (fun i _ => mul_nonneg hC₀0 (add_nonneg ?_ ?_))
        · exact integral_nonneg (fun x => sq_nonneg (Ψ x))
        · exact Finset.sum_nonneg (fun k _ => integral_nonneg (fun x => sq_nonneg _))
      · intro u _
        have hKin : Work.BoseBox.tKinAmb (n + 1) L ℓ d s eT b u Ψ
            = ∑ i : Fin (n + 1), Work.BoseKinLoc.slotForm (n + 1)
                (Work.BoseKinLoc.fsT ℓ d s eT b u) ℓ u i Ψ := by
          simp [Work.BoseBox.tKinAmb, Work.BoseBox.tKinWord, Work.BoseKinLoc.kinForm]
        rw [hKin]
        calc |∑ i : Fin (n + 1), Work.BoseKinLoc.slotForm (n + 1)
                (Work.BoseKinLoc.fsT ℓ d s eT b u) ℓ u i Ψ|
            ≤ ∑ i : Fin (n + 1), |Work.BoseKinLoc.slotForm (n + 1)
                (Work.BoseKinLoc.fsT ℓ d s eT b u) ℓ u i Ψ| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i : Fin (n + 1), C₀ * ((∫ x : Submission.BoseGases.X (n + 1), (Ψ x) ^ 2)
                + ∑ k : Fin 3, ∫ x : Submission.BoseGases.X (n + 1),
                    (fderiv ℝ Ψ x) (Submission.BoseGases.kcDir (n + 1) i k) ^ 2) :=
              Finset.sum_le_sum (fun i _ =>
                slotForm_abs_bound (n := n) (L := L) hℓ hΨ hΨcs hsupp C₀ hC₀ i u)

end Work.BoseBox
