import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.secondMomentPlancherelOne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.highModeTail` — (T2′) of the `L¹`-weight tail chapter

The **high-mode tail** of the lattice Dirichlet sum.  For `f ∈ C¹` with `tsupport f ⊆ boxL ℓ`
(the box `[−ℓ/2,ℓ/2]³` of side `ℓ`), every finite set `S` of lattice momenta whose norm is at
least `Λ` satisfies

    Σ_{n ∈ S} ‖f̂(κ_n)‖²  ≤  ℓ³/Λ² · (2π)⁻³ ∫_p ‖p‖² ‖f̂(p)‖² ,      κ_n = (2π/ℓ)·n .

Source: the design `sources/boseDCF/bose_L1tails.md` (T2′, which reads "from T2"): `(T2′)` is the
input that turns the *lattice* Dirichlet sum T2 into a statement about the modes above the cutoff
`Λ` alone, at the cost of the factor `Λ⁻²`.

## Route

*Per mode.*  `‖κ_n‖ ≥ Λ` gives `Λ²‖f̂(κ_n)‖² ≤ ‖κ_n‖²‖f̂(κ_n)‖²`, and the pointwise Fourier
derivative identity

    ‖k‖²‖kinFT f k‖² = Σ_{j} ‖kinFT (∂_j f) k‖²

(`Work.BoseFixB1.SectorAux.normSq_kinFT_eq_sum_normSq_fderiv_one`, valid for `C¹` compactly
supported `f`) rewrites the right-hand side as the sum over the three directional derivatives.

*The lattice.*  For each `j` the state `∂_j f` is `C¹` (indeed continuous) with compact support
contained in `tsupport f ⊆ boxL ℓ` (`tsupport_fderiv_apply_subset`), hence `L²` with support in the
box; the proved `L²` frame (Poisson/aliasing) identity `hasSum_kinFT_lattice_L2` at scale `ℓ` then
gives

    HasSum (fun n => ‖kinFT (∂_j f) (κ_n)‖²) (ℓ³ ∫_z ‖∂_j f z‖²),

so a finite partial sum is at most the total (`Summable.sum_le_tsum`, all terms nonnegative).

*The continuum.*  Summing the three lattice series and using the `C¹` second-moment Plancherel
identity `secondMomentPlancherelOne` (`(2π)⁻³∫_p ‖p‖²‖f̂(p)‖² = Σ_j ∫_z ‖∂_j f z‖²`, proved in the
sibling module from `kinFT_sq_of_memLp` and the same pointwise derivative identity) converts the
total into the target's right-hand side.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

theorem highModeTail {ℓ Λ : ℝ} (hℓ : 0 < ℓ) (hΛ : 0 < Λ)
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : ContDiff ℝ 1 f)
    (hs : tsupport f ⊆ Work.BoseK15.corpusBox.boxL ℓ) (S : Finset (Fin 3 → ℤ))
    (hS : ∀ n ∈ S, Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖) :
    ∑ n ∈ S, ‖Submission.BoseGases.kinFT f (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
      ≤ ℓ ^ 3 / Λ ^ 2 *
          (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT f p‖ ^ 2) := by
  classical
  have hΛ2 : (0 : ℝ) < Λ ^ 2 := pow_pos hΛ 2
  -- `f` is compactly supported, and so are its three directional derivatives
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
      (isClosed_tsupport f) hs
  have hcont : ∀ j : Fin 3, Continuous (fun z : E3 =>
      fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)) := fun j =>
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcsd : ∀ j : Fin 3, HasCompactSupport (fun z : E3 =>
      fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)) := fun j => hfc.fderiv_apply ℝ _
  have htsup : ∀ j : Fin 3, tsupport (fun z : E3 =>
      fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)) ⊆ Work.BoseK15.corpusBox.boxL ℓ :=
    fun j => (tsupport_fderiv_apply_subset ℝ (Submission.BoseGases.kcStdBasis j)).trans hs
  have hmem2 : ∀ j : Fin 3, MemLp (fun z : E3 =>
      fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)) 2 :=
    fun j => (hcont j).memLp_of_hasCompactSupport (hcsd j)
  -- the lattice frame identity for each directional derivative
  have hHas : ∀ j : Fin 3, HasSum (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT (fun z : E3 =>
        fderiv ℝ f z (Submission.BoseGases.kcStdBasis j))
        (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      (ℓ ^ 3 * ∫ z : E3, ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)‖ ^ 2) :=
    fun j => hasSum_kinFT_lattice_L2 hℓ (hmem2 j) (htsup j)
  -- per-mode: the weight `‖κ_n‖² ≥ Λ²` and the derivative identity
  have hterm : ∀ n ∈ S, ‖Submission.BoseGases.kinFT f (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
      ≤ (Λ ^ 2)⁻¹ * ∑ j : Fin 3, ‖Submission.BoseGases.kinFT (fun z : E3 =>
          fderiv ℝ f z (Submission.BoseGases.kcStdBasis j))
          (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 := by
    intro n hn
    have hge := hS n hn
    have hle : Λ ^ 2 * ‖Submission.BoseGases.kinFT f (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
        ≤ ∑ j : Fin 3, ‖Submission.BoseGases.kinFT (fun z : E3 =>
            fderiv ℝ f z (Submission.BoseGases.kcStdBasis j))
            (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 := by
      calc Λ ^ 2 * ‖Submission.BoseGases.kinFT f (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
          ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖ ^ 2
              * ‖Submission.BoseGases.kinFT f (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right
              (by nlinarith [hΛ, hge, norm_nonneg (Work.BoseBoxFock.kappaL ℓ n)]) (sq_nonneg _)
        _ = ∑ j : Fin 3, ‖Submission.BoseGases.kinFT (fun z : E3 =>
              fderiv ℝ f z (Submission.BoseGases.kcStdBasis j))
              (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 :=
            Work.BoseFixB1.SectorAux.normSq_kinFT_eq_sum_normSq_fderiv_one hf hfc _
    have h2 := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hΛ2.le)
    rwa [inv_mul_cancel_left₀ (ne_of_gt hΛ2)] at h2
  have hstep1 : ∑ n ∈ S, ‖Submission.BoseGases.kinFT f (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
      ≤ (Λ ^ 2)⁻¹ * ∑ n ∈ S, ∑ j : Fin 3, ‖Submission.BoseGases.kinFT (fun z : E3 =>
          fderiv ℝ f z (Submission.BoseGases.kcStdBasis j))
          (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hswap : ∑ n ∈ S, ∑ j : Fin 3, ‖Submission.BoseGases.kinFT (fun z : E3 =>
        fderiv ℝ f z (Submission.BoseGases.kcStdBasis j))
        (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
      = ∑ j : Fin 3, ∑ n ∈ S, ‖Submission.BoseGases.kinFT (fun z : E3 =>
        fderiv ℝ f z (Submission.BoseGases.kcStdBasis j))
        (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 := Finset.sum_comm
  -- each lattice series, restricted to `S`, is at most its total
  have hj : ∀ j : Fin 3, ∑ n ∈ S, ‖Submission.BoseGases.kinFT (fun z : E3 =>
        fderiv ℝ f z (Submission.BoseGases.kcStdBasis j))
        (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
      ≤ ℓ ^ 3 * ∫ z : E3, ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)‖ ^ 2 := by
    intro j
    calc ∑ n ∈ S, ‖Submission.BoseGases.kinFT (fun z : E3 =>
          fderiv ℝ f z (Submission.BoseGases.kcStdBasis j))
          (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
        ≤ ∑' n : Fin 3 → ℤ, ‖Submission.BoseGases.kinFT (fun z : E3 =>
            fderiv ℝ f z (Submission.BoseGases.kcStdBasis j))
            (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 :=
          Summable.sum_le_tsum S (fun n _ => by positivity) (hHas j).summable
      _ = ℓ ^ 3 * ∫ z : E3, ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)‖ ^ 2 :=
          (hHas j).tsum_eq
  calc ∑ n ∈ S, ‖Submission.BoseGases.kinFT f (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2
      ≤ (Λ ^ 2)⁻¹ * ∑ n ∈ S, ∑ j : Fin 3, ‖Submission.BoseGases.kinFT (fun z : E3 =>
          fderiv ℝ f z (Submission.BoseGases.kcStdBasis j))
          (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 := hstep1
    _ = (Λ ^ 2)⁻¹ * ∑ j : Fin 3, ∑ n ∈ S, ‖Submission.BoseGases.kinFT (fun z : E3 =>
          fderiv ℝ f z (Submission.BoseGases.kcStdBasis j))
          (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 := by rw [hswap]
    _ ≤ (Λ ^ 2)⁻¹ * ∑ j : Fin 3, ℓ ^ 3 * ∫ z : E3,
          ‖fderiv ℝ f z (Submission.BoseGases.kcStdBasis j)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hj j))
          (inv_nonneg.mpr hΛ2.le)
    _ = ℓ ^ 3 / Λ ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT f p‖ ^ 2) := by
        rw [← Finset.mul_sum, ← secondMomentPlancherelOne hf hfc]
        ring

end Work.BoseBoxFock.L1Tails
