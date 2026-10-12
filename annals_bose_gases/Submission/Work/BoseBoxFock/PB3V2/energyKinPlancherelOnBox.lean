import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiMf_tsupport_subset
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3V2.energyKinPlancherelOnBox`

The kinetic energy of a `C¹` state whose support lies in the corpus box `boxL ℓ`, written as a
Plancherel integral over momentum:

`(2π)⁻³ ∫_p ‖p‖²‖kinFT g p‖² = ∫_{boxL ℓ} Σ_j ‖∂_{e_j} g‖²`

(`e_j = kcStdBasis j`, `kinFT g p = ∫_y e^{−i⟪p,y⟫}g(y)dy`).

The mathematical content is *derivative Plancherel*: the Fourier transform turns `∂_{e_j}` into
multiplication by `i⟪p,e_j⟫`, so that `Σ_j ‖kinFT (∂_{e_j} g) p‖² = ‖p‖²‖kinFT g p‖²`, and
Plancherel for `L¹ ∩ L²` functions (used on each of the three compactly supported derivatives)
identifies `(2π)⁻³∫_p ‖kinFT (∂_{e_j}g) p‖²` with `∫_z ‖∂_{e_j}g z‖²`.  This is exactly the
corpus lemma `Work.BoseBoxFock.L1Tails.secondMomentPlancherelOne`, whose right-hand side is the
integral over all of `ℝ³`.

The only new ingredient here is the passage from the whole space to the box: the derivative
function `Σ_j ‖fderiv ℝ g z (e_j)‖²` vanishes off the topological support of `g`, hence off
`boxL ℓ` by hypothesis, so the two integrals agree
(`MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero`).  The pointwise vanishing is
`fderiv ℝ g z = 0` for `z ∉ tsupport g`, which holds because `g` is identically zero in a
neighbourhood of such a `z` (`Filter.EventuallyEq.fderiv_eq` against the zero function).
-/

namespace Work.BoseBoxFock.PB3V2

open MeasureTheory Filter
open scoped Topology

/-- Away from the topological support of `g`, the Fréchet derivative of `g` vanishes: `g` is
identically zero on a neighbourhood of any such point. -/
lemma fderiv_eq_zero_of_notMem_tsupport {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∉ tsupport g) : fderiv ℝ g z = 0 := by
  have hmem : (tsupport g)ᶜ ∈ 𝓝 z := (isClosed_tsupport g).isOpen_compl.mem_nhds hz
  have hev : g =ᶠ[𝓝 z] (Function.const (EuclideanSpace ℝ (Fin 3)) (0 : ℂ)) := by
    filter_upwards [hmem] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  have h := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hev
  simpa using h

theorem energyKinPlancherelOnBox {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ 1 g) (hs : tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 *
        ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      = ∫ z in Work.BoseK15.corpusBox.boxL ℓ,
          ∑ j : Fin 3, ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2 := by
  have hcs : HasCompactSupport g :=
    (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).of_isClosed_subset
      (isClosed_tsupport g) hs
  -- each summand of the Dirichlet energy is integrable (continuous, compactly supported)
  have hInt : ∀ j : Fin 3, Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2) := by
    intro j
    have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)) :=
      (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs' : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) =>
        fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)) :=
      hcs.fderiv_apply ℝ (Submission.BoseGases.kcStdBasis j)
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mp
      (hcont.memLp_of_hasCompactSupport hcs')
  -- the whole-space Plancherel identity, with the Dirichlet energy as a `Fin 3`-sum
  rw [Work.BoseBoxFock.L1Tails.secondMomentPlancherelOne hg hcs]
  -- the Dirichlet energy vanishes off the box, so the box integral is the whole-space integral
  have hvan : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Work.BoseK15.corpusBox.boxL ℓ →
      (∑ j : Fin 3, ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2) = 0 := by
    intro z hz
    have hz' : z ∉ tsupport g := fun h => hz (hs h)
    simp [fderiv_eq_zero_of_notMem_tsupport hz']
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hvan]
  -- and the sum comes out of the integral
  exact (MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin 3))
    (f := fun (j : Fin 3) (z : EuclideanSpace ℝ (Fin 3)) =>
      ‖fderiv ℝ g z (Submission.BoseGases.kcStdBasis j)‖ ^ 2)
    (fun j _ => hInt j)).symm

end Work.BoseBoxFock.PB3V2
