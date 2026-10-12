import ChallengeDeps
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Compare.ham_expansion_v2`

The Hamiltonian expansion: for a smooth function `Φ` supported in the configuration
box `abox N L`, the diagonal matrix element of `𝓗 N v` splits into the kinetic sum
`∑ᵢ ∫ Φ·(−ΔᵢΦ)` and the potential integral `∫ Φ²·∑_{i<j} v(xᵢ − xⱼ)`.

The only hypothesis beyond smoothness and support is the integrability of the
potential integrand (`hint`); the kinetic integrands are continuous, hence
`IntegrableOn` the compact box `abox N L` (see
`Work.UBBInputs9.B.integrableOn_abox_of_continuous'`).
-/

namespace Work.BoseKinLoc.Compare

open MeasureTheory

set_option autoImplicit false
-- `hsupp` is part of the (fixed) statement but is not needed for the expansion.
set_option linter.unusedVariables false

/-- The pointwise expansion `Φ·𝓗 N v Φ = ∑ᵢ Φ·(−ΔᵢΦ) + Φ²·∑_{i<j} v(xᵢ−xⱼ)`. -/
private lemma ham_pt {N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Φ x * BoseGases.𝓗 N v Φ x
      = (∑ i : Fin N, Φ x * (- BoseGases.partialLaplacian i Φ x))
        + (Φ x) ^ 2 * (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
            v (x ij.1.1 - x ij.1.2)) := by
  have hunf : BoseGases.𝓗 N v Φ x
      = (∑ i : Fin N, - BoseGases.partialLaplacian i Φ x)
        + ∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
            v (x p.1 - x p.2) * Φ x := rfl
  have hsub : (∑ a ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
        Φ x * (v (x a.1 - x a.2) * Φ x))
      = ∑ a : {a : Fin N × Fin N // a.1 < a.2},
          Φ x * (v (x a.1.1 - x a.1.2) * Φ x) :=
    Finset.sum_subtype (s := Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2))
      (p := fun p : Fin N × Fin N => p.1 < p.2)
      (f := fun a => Φ x * (v (x a.1 - x a.2) * Φ x)) (by intro a; simp)
  rw [hunf, mul_add, Finset.mul_sum, Finset.mul_sum]
  rw [hsub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun ij _ => ?_)
  ring

theorem ham_expansion_v2 {N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {L : ℝ}
    {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L)
    (hint : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 *
        (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)))) :
    (∫ x in Submission.BoseGases.abox N L, (Φ x) * (BoseGases.𝓗 N v Φ x))
      = (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N L, (Φ x) *
            (- BoseGases.partialLaplacian i Φ x))
        + ∫ x in Submission.BoseGases.abox N L, (Φ x) ^ 2 *
            (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)) := by
  -- `Φ` is `C²`, so the partial Laplacian is a sum of second directional derivatives.
  have hcd : ContDiff ℝ 2 (Φ : Submission.BoseGases.X N → ℝ) :=
    hΦ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hsecond : ∀ i : Fin N,
      (fun x : Submission.BoseGases.X N => BoseGases.partialLaplacian i Φ x)
        = fun x => ∑ k : Fin 3,
            (fderiv ℝ (fun z : Submission.BoseGases.X N =>
              fderiv ℝ Φ z (Submission.BoseGases.coordDir N i k)) x)
              (Submission.BoseGases.coordDir N i k) := by
    intro i
    exact Submission.BoseGases.partialLaplacian_eq_sum_secondDir N i hcd
  -- ... hence continuous.
  have hΔcont : ∀ i : Fin N, Continuous (fun x : Submission.BoseGases.X N =>
      BoseGases.partialLaplacian i Φ x) := by
    intro i
    rw [hsecond i]
    exact continuous_finsetSum _ (fun k _ =>
      (Submission.BoseGases.secondDir_contDiff_u hΦ _).continuous)
  -- The kinetic integrands are continuous, hence integrable on the compact box.
  have hkin : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => Φ x * (- BoseGases.partialLaplacian i Φ x))
      (Submission.BoseGases.abox N L) MeasureTheory.volume := by
    intro i
    exact Work.UBBInputs9.B.integrableOn_abox_of_continuous'
      (hΦ.continuous.mul (hΔcont i).neg)
  have hkinSum : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N =>
        ∑ i : Fin N, Φ x * (- BoseGases.partialLaplacian i Φ x))
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N L)) :=
    MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hkin i)
  have hpotInt : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 *
        (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)))
      ((MeasureTheory.volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N L)) :=
    hint.integrableOn
  calc
    (∫ x in Submission.BoseGases.abox N L, (Φ x) * (BoseGases.𝓗 N v Φ x))
        = ∫ x in Submission.BoseGases.abox N L,
            ((∑ i : Fin N, Φ x * (- BoseGases.partialLaplacian i Φ x))
              + (Φ x) ^ 2 * (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
                  v (x ij.1.1 - x ij.1.2))) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          exact ham_pt Φ x
      _ = (∫ x in Submission.BoseGases.abox N L,
              ∑ i : Fin N, Φ x * (- BoseGases.partialLaplacian i Φ x))
            + ∫ x in Submission.BoseGases.abox N L, (Φ x) ^ 2 *
              (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
                v (x ij.1.1 - x ij.1.2)) :=
          MeasureTheory.integral_add hkinSum hpotInt
      _ = (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N L, (Φ x) *
              (- BoseGases.partialLaplacian i Φ x))
            + ∫ x in Submission.BoseGases.abox N L, (Φ x) ^ 2 *
              (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
                v (x ij.1.1 - x ij.1.2)) := by
          rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hkin i)]

end Work.BoseKinLoc.Compare
