import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.RPAe.Defs
import Submission.Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW
import Submission.Work.FTS.EllSol.VopAux.sliceW_pthIter2_eq_sliceW_sliceV
import Submission.Work.FTS.EllSol.VopAux.sliceF_le_sliceV
import Submission.Work.FTS.EllSol.VopAux.TraceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.RPAe

/-!
# The per-`z` comparison of the slice groups of `f` and `∂_θ² f`

For `f` of class `C^∞` on the open quadrant, `z > 0` and `j ≤ 4`, the `j`-th slice group of `f`
is dominated by the `j`-th slice group of `∂_θ² f`, up to the universal constant `sliceCs`:

`∫_Iθ sliceGroup α 4 j f z θ ≤ sliceCs · ∫_Iθ sliceGroup α 4 j (∂_θ² f) z θ`.

ROUTE.  Both groups are, on the open interval, `(w z)²` times a *single-slice* functional of the
`j`-th radial slice of `f`:

* `sliceGroup α 4 j f z θ = (w z)² · sliceW (4-j) α u θ` where `u = θ' ↦ D_z^j f z θ'`
  (`VopAux.sliceGroup_eq_sliceW`), and
* `sliceGroup α 4 j (∂_θ² f) z θ = (w z)² · sliceW (4-j) α u'' θ`
  (`VopAux.sliceGroup_eq_sliceW` for `∂_θ²f` + `VopAux.sliceW_pthIter2_eq_sliceW_sliceV`).

Since `Iθ` and the open interval differ by the two null endpoints, the two integral identities
follow from the pointwise identities (`EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo`) and the
constant `(w z)²` comes out of the integral (`MeasureTheory.integral_const_mul`).  The remaining
inequality `sliceF (4-j) α u ≤ C · sliceF (4-j) α u''` is the one-dimensional `∂_θ²`-Poincaré
estimate with traces `VopAux.sliceF_le_sliceV_apply`, whose integrability hypotheses on the data
`u''` are supplied by `VopAux.integrableOn_sliceV_thEta` / `VopAux.integrableOn_sliceV_LopIter`
from the assumed integrability of `HkIntegrand α 4 (∂_θ² f)`.  Finally
`C = Classical.choose (VopAux.sliceF_le_sliceV (4-j)) ≤ sliceCs` (`RPAe.le_sliceCs_F`) and
`sliceF (4-j) α u'' ≥ 0` (`VopAux.sliceF_nonneg`) finish the estimate.
-/

theorem groupBoundF : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f →
    ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ 4 →
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 4 (Work.Spaces.pthIter 2 f) z θ) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j f z θ)
      ≤ Work.FTS.EllSol.RPAe.sliceCs * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ) := by
  intro α f hα0 hα1 hf z hz j hj hlim0 hlim1 hint
  -- the raw `∀ n` shape of the smoothness hypothesis, on the open quadrant
  have hfQ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hf.forall
  have hpth2Q : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h := hf.pth.pth.forall
    intro n
    exact h n
  -- the `j`-th radial slice of `f`, as a function of `θ`
  have hUsmooth : ∀ n : ℕ, ContDiffOn ℝ n (fun θ' => Work.Spaces.DzIter j f z θ')
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllSol.VopAux.contDiffOn_slice_of_smoothOpen (hf.DzIter j) hz
  -- integrability of the data `u''` and of its angular derivatives
  have hintV : MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    Work.FTS.EllSol.VopAux.integrableOn_sliceV_thEta (α := α) (k := 4) (f := f) hf hz hj hint
  have hintVm : ∀ m ∈ Finset.Icc 1 (4 - j), MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.LopIter m
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    exact Work.FTS.EllSol.VopAux.integrableOn_sliceV_LopIter (α := α) (k := 4) (f := f) hf hz
      hm1 (by omega) hint
  -- the one-dimensional `∂_θ²`-Poincaré estimate on the slice
  have hslice : Work.FTS.EllSol.VopAux.sliceF (4 - j) α
        (fun θ' => Work.Spaces.DzIter j f z θ')
      ≤ Classical.choose (Work.FTS.EllSol.VopAux.sliceF_le_sliceV (4 - j)) *
        Work.FTS.EllSol.VopAux.sliceF (4 - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
    (Work.FTS.EllSol.RPAe.sliceF_le_sliceV_apply (4 - j) α
      (fun θ' => Work.Spaces.DzIter j f z θ') hα0 hα1 hUsmooth hlim0 hlim1 hintV hintVm).2.2
  -- the two pointwise identities, on the open interval
  have hL : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j f z θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllSol.VopAux.sliceW (4 - j) α
              (fun θ' => Work.Spaces.DzIter j f z θ') θ :=
    Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo
      (f := fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j f z θ)
      (g := fun θ => (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW (4 - j) α
        (fun θ' => Work.Spaces.DzIter j f z θ') θ)
      (fun θ hθ => Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW α 4 j f hz hfQ θ hθ)
  have hR : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j
        (Work.Spaces.pthIter 2 f) z θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllSol.VopAux.sliceW (4 - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ :=
    Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo
      (f := fun θ => Work.FTS.EllipticEst.sliceGroup α 4 j (Work.Spaces.pthIter 2 f) z θ)
      (g := fun θ => (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceW (4 - j) α
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
      (fun θ hθ => by
        rw [Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW α 4 j (Work.Spaces.pthIter 2 f) hz
            hpth2Q θ hθ,
          Work.FTS.EllSol.VopAux.sliceW_pthIter2_eq_sliceW_sliceV α (4 - j) j f hz hfQ θ hθ])
  -- both integrals are `(w z)²` times the corresponding `sliceF`
  have hLint : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j f z θ)
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
          (fun θ' => Work.Spaces.DzIter j f z θ') := by
    rw [Work.FTS.EllSol.VopAux.sliceF, hL, MeasureTheory.integral_const_mul]
  have hRint : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α 4 j
        (Work.Spaces.pthIter 2 f) z θ)
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) := by
    rw [Work.FTS.EllSol.VopAux.sliceF, hR, MeasureTheory.integral_const_mul]
  -- the constant produced by the one-dimensional estimate is dominated by `sliceCs`
  have hC : Classical.choose (Work.FTS.EllSol.VopAux.sliceF_le_sliceV (4 - j)) ≤ sliceCs :=
    le_sliceCs_F (4 - j) (by omega)
  have hX0 : 0 ≤ (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
      (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) :=
    mul_nonneg (sq_nonneg _)
      (Work.FTS.EllSol.VopAux.sliceF_nonneg (4 - j) α
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')))
  rw [hLint, hRint]
  calc (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
        (fun θ' => Work.Spaces.DzIter j f z θ')
      ≤ (Work.Spaces.w z) ^ 2 *
          (Classical.choose (Work.FTS.EllSol.VopAux.sliceF_le_sliceV (4 - j)) *
            Work.FTS.EllSol.VopAux.sliceF (4 - j) α
              (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) :=
        mul_le_mul_of_nonneg_left hslice (sq_nonneg _)
    _ = Classical.choose (Work.FTS.EllSol.VopAux.sliceF_le_sliceV (4 - j)) *
          ((Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
            (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) := by
        ring
    _ ≤ sliceCs * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.VopAux.sliceF (4 - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))) :=
        mul_le_mul_of_nonneg_right hC hX0

end Work.FTS.EllSol.RPAe
