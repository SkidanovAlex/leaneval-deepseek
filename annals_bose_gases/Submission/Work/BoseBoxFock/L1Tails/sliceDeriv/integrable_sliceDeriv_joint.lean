import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.DefsC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Joint integrability of the `w`-slice derivative energy

The target `Work.BoseBoxFock.L1Tails.sliceDeriv.integrable_sliceDeriv_joint` is the finiteness of
the "slice derivative energy" of a smooth box-supported kernel `H`:

    `(w,y) ↦ Σ_j ‖∂_{w_j}(w' ↦ H w' y) w‖²`  is integrable for the product Lebesgue measure.

Both ingredients are elementary, and neither needs any `L²` theory:

* **continuity.**  `fderiv ℝ (Function.uncurry H)` is continuous because `Function.uncurry H` is
  `C^∞` (`ContDiff.continuous_fderiv`), and the slice derivative is by the chain rule the
  composition of that total derivative with `ContinuousLinearMap.inl ℝ E3 E3`
  (the linearisation of `w' ↦ (w', y)`, `hasFDerivAt_prodMk_left`); composition with a continuous
  linear map and evaluation are continuous operations (`Continuous.clm_apply`), and a finite sum
  of continuous functions is continuous;
* **compact support.**  `boxL ℓ` is compact (it is `ℓ • cell`, the image of the compact unit cell
  under `x ↦ ℓ • x`), so is the product `boxL ℓ ×ˢ boxL ℓ`.  Off that product the slice derivative
  *vanishes pointwise*: if `y ∉ boxL ℓ` then `hHs` makes the whole slice `w' ↦ H w' y` identically
  zero (hence its derivative is `0`), and if `w ∉ boxL ℓ` then `w` has an open neighbourhood (the
  complement of the compact `boxL ℓ`) on which `w' ↦ H w' y` vanishes, so its derivative at `w` is
  `0` (`Filter.EventuallyEq.fderiv_eq` and the derivative of a constant).  Hence the support is
  contained in the compact product and `Continuous.integrable_of_hasCompactSupport` applies.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Pointwise Topology

namespace Work.BoseBoxFock.L1Tails.sliceDeriv

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `boxL ℓ = ℓ • cell` is compact: the image of the compact unit cell under `x ↦ ℓ • x`. -/
private lemma isCompact_boxL (ℓ : ℝ) : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) := by
  have h := Work.BoseK15.corpusBox.cell_compact.image (continuous_const_smul (ℓ : ℝ))
  rwa [Set.image_smul] at h

/-- Chain rule for the `w`-slice of a smooth two-variable kernel: the `w`-derivative of the slice
`w' ↦ H w' y` is the total derivative of `Function.uncurry H` at `(w,y)` restricted to the first
factor.  This is `HasFDerivAt.comp` for `Function.uncurry H` with the linear map `w' ↦ (w', y)`
(`hasFDerivAt_prodMk_left`), whose derivative is `ContinuousLinearMap.inl ℝ E3 E3`. -/
private lemma fderiv_slice_eq_inl {H : E3 → E3 → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H)) (w y : E3) :
    fderiv ℝ (fun w' => H w' y) w
      = (fderiv ℝ (Function.uncurry H) (w, y)).comp (ContinuousLinearMap.inl ℝ E3 E3) := by
  have hdiff : Differentiable ℝ (Function.uncurry H) := hH.differentiable (by simp)
  have hφ : HasFDerivAt (fun w' : E3 => (w', y)) (ContinuousLinearMap.inl ℝ E3 E3) w :=
    hasFDerivAt_prodMk_left w y
  exact ((hdiff (w, y)).hasFDerivAt.comp w hφ).fderiv

/-- Joint integrability of the `w`-slice derivative energy of a smooth box-supported kernel `H`:
the function `(w,y) ↦ Σ_j ‖∂_{w_j} (w' ↦ H w' y) w‖²` is integrable for the product measure.  Route:
by the chain rule it equals `(w,y) ↦ Σ_j ‖fderiv ℝ (uncurry H) (w,y) (inl e_j)‖²`, which is
continuous (since `fderiv ℝ (uncurry H)` is) and supported in the compact set `boxL ℓ × boxL ℓ`
(by `tsupport_fderiv_apply_subset` and `hHs`); conclude with
`Continuous.integrable_of_hasCompactSupport`. -/
theorem integrable_sliceDeriv_joint {ℓ : ℝ}
    {H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H))
    (hHs : ∀ w y, H w y ≠ 0 →
      w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ∑ j : Fin 3, ‖fderiv ℝ (fun w' => H w' p.2) p.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      MeasureTheory.volume := by
  -- the compact set supporting everything
  have hKc : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) := isCompact_boxL ℓ
  have hKcl : IsClosed (Work.BoseK15.corpusBox.boxL ℓ) := hKc.isClosed
  have hS : IsCompact (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) :=
    hKc.prod hKc
  -- off the product, the slice is eventually (or identically) the zero function
  have hslice : ∀ p : E3 × E3,
      p ∉ Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ →
      (fun w' => H w' p.2) =ᶠ[nhds p.1] (fun _ => (0 : ℂ)) := by
    intro p hp
    rcases not_and_or.mp hp with hp1 | hp2
    · -- `p.1 ∉ boxL ℓ`: the slice vanishes on the open neighbourhood `(boxL ℓ)ᶜ` of `p.1`
      have hopen : IsOpen (Work.BoseK15.corpusBox.boxL ℓ)ᶜ := hKcl.isOpen_compl
      have hev : ∀ᶠ w' in nhds p.1, w' ∈ (Work.BoseK15.corpusBox.boxL ℓ)ᶜ :=
        hopen.mem_nhds hp1
      refine hev.mono (fun w' hw' => ?_)
      have hz : H w' p.2 = 0 := by
        by_contra hne
        exact hw' (hHs w' p.2 hne).1
      simp [hz]
    · -- `p.2 ∉ boxL ℓ`: the slice is identically zero, by `hHs`
      refine Filter.Eventually.of_forall (fun w' => ?_)
      have hz : H w' p.2 = 0 := by
        by_contra hne
        exact hp2 (hHs w' p.2 hne).2
      simp [hz]
  -- so the integrand vanishes pointwise off the product
  have hFzero : ∀ p : E3 × E3,
      p ∉ Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ →
      (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => H w' p.2) p.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) = 0 := by
    intro p hp
    have hder : fderiv ℝ (fun w' => H w' p.2) p.1 = 0 := by
      rw [(hslice p hp).fderiv_eq, fderiv_fun_const]
      simp
    rw [hder]
    simp
  -- continuity of the integrand, through the chain rule
  have hcontF : Continuous (fun p : E3 × E3 =>
      ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => H w' p.2) p.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
    have hfd : Continuous (fderiv ℝ (Function.uncurry H)) := hH.continuous_fderiv (by simp)
    have hGcont : Continuous (fun p : E3 × E3 => ∑ j : Fin 3,
        ‖(fderiv ℝ (Function.uncurry H) p)
          (ContinuousLinearMap.inl ℝ E3 E3 (EuclideanSpace.single j (1 : ℝ)))‖ ^ 2) := by
      refine continuous_finsetSum Finset.univ (fun j _ => ?_)
      exact ((hfd.clm_apply continuous_const).norm.pow 2)
    have hFeq : (fun p : E3 × E3 =>
        ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => H w' p.2) p.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        = (fun p : E3 × E3 => ∑ j : Fin 3,
          ‖(fderiv ℝ (Function.uncurry H) p)
            (ContinuousLinearMap.inl ℝ E3 E3 (EuclideanSpace.single j (1 : ℝ)))‖ ^ 2) := by
      funext p
      rw [fderiv_slice_eq_inl hH p.1 p.2]
      simp [ContinuousLinearMap.comp_apply]
    rw [hFeq]
    exact hGcont
  refine hcontF.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact hS (fun p hp => ?_)
  by_contra hne
  exact hp (hFzero p hne)

end Work.BoseBoxFock.L1Tails.sliceDeriv
