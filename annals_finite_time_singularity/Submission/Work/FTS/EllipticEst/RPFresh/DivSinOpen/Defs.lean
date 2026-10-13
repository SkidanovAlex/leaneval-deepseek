/-
Copyright: work module for the Elgindi finite-time singularity project.

# The summands of the two `ℋ^k`-integrands, for the *open quadrant* class

This module fixes the vocabulary for the proof of
`Work.FTS.EllipticEst.RPFresh.divSin_Hk_open` (the open-quadrant form of Elgindi's
`DivisionBySin`, `|Φ/sin 2θ|_{ℋ^k} ≤ C|∂_θΦ|_{ℋ^k}`):

* `LZ Φ z i`, `LM k α Φ z i j` — the pure-`D_z` and mixed summands of the `ℋ^k`-integrand of
  `Φ/sin 2θ`;
* `RZ Φ z i`, `RM k α Φ z i j` — the corresponding summands of the `ℋ^k`-integrand of `∂_θΦ`;
* `HkIntegrand_div_eq` / `HkIntegrand_pth_eq` — the (definitional) decompositions
  `HkIntegrand α k (Φ/sin 2θ) z θ = Σ_i LZ Φ z i θ + Σ_{i,j} LM k α Φ z i j θ`, and the same
  with `R` in place of `L`;
* `aesm_LZ`, `aesm_LM`, `aesm_RZ`, `aesm_RM` and the nonnegativity lemmas, which are what make
  the junk-tolerant integral comparisons available.

All declarations are `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.DivSinFactor
import Submission.Work.Elliptic.DivSinPerZ
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false

/-- The pure `D_z` summand of the `ℋ^k`-integrand of `Φ / sin(2θ)`. -/
def LZ (Φ : ℝ → ℝ → ℝ) (z : ℝ) (i : ℕ) (θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The mixed summand of the `ℋ^k`-integrand of `Φ / sin(2θ)`. -/
def LM (k : ℕ) (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z : ℝ) (i j : ℕ) (θ : ℝ) : ℝ :=
  if 1 ≤ i ∧ i + j ≤ k then
    (Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
      * Work.Spaces.Wt α z θ) ^ 2
  else 0

/-- The pure `D_z` summand of the `ℋ^k`-integrand of `∂_θΦ`. -/
def RZ (Φ : ℝ → ℝ → ℝ) (z : ℝ) (i : ℕ) (θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The mixed summand of the `ℋ^k`-integrand of `∂_θΦ`. -/
def RM (k : ℕ) (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z : ℝ) (i j : ℕ) (θ : ℝ) : ℝ :=
  if 1 ≤ i ∧ i + j ≤ k then
    (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2
  else 0

theorem HkIntegrand_div_eq (α : ℝ) (k : ℕ) (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
      = (∑ i ∈ Finset.range (k + 1), LZ Φ z i θ)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            LM k α Φ z i j θ := by
  simp only [Work.Spaces.HkIntegrand, LZ, LM]

theorem HkIntegrand_pth_eq (α : ℝ) (k : ℕ) (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (Work.Spaces.pth Φ) z θ
      = (∑ i ∈ Finset.range (k + 1), RZ Φ z i θ)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            RM k α Φ z i j θ := by
  simp only [Work.Spaces.HkIntegrand, RZ, RM]

theorem LZ_nonneg (Φ : ℝ → ℝ → ℝ) (z : ℝ) (i : ℕ) (θ : ℝ) : 0 ≤ LZ Φ z i θ :=
  sq_nonneg _

theorem LM_nonneg (k : ℕ) (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z : ℝ) (i j : ℕ) (θ : ℝ) :
    0 ≤ LM k α Φ z i j θ := by
  rw [LM]; split_ifs with h; exacts [sq_nonneg _, le_refl 0]

theorem RZ_nonneg (Φ : ℝ → ℝ → ℝ) (z : ℝ) (i : ℕ) (θ : ℝ) : 0 ≤ RZ Φ z i θ :=
  sq_nonneg _

theorem RM_nonneg (k : ℕ) (α : ℝ) (Φ : ℝ → ℝ → ℝ) (z : ℝ) (i j : ℕ) (θ : ℝ) :
    0 ≤ RM k α Φ z i j θ := by
  rw [RM]; split_ifs with h; exacts [sq_nonneg _, le_refl 0]

/-- `sin(2θ) > 0` on the open angular interval. -/
theorem sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- `Φ / sin(2θ)` is `C^∞` on the open quadrant when `Φ` is. -/
theorem smoothOpen_div_sin {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φ z θ / Real.sin (2 * θ)) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hnum : ContDiffOn ℝ n (Function.uncurry Φ) Work.FTS.EllipticEst.Q0 := hΦ.forall n
  have hden : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by fun_prop
  refine hnum.div hden (fun p hp => ?_)
  obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (sin_two_pos_Ioo ⟨h1, h2⟩)

/-- The slice of the uncurried `F` at a positive radius is `C^∞` on the open angular interval. -/
theorem contDiffOn_slice_uncurry {F : ℝ → ℝ → ℝ} (hF : ∀ m : ℕ,
    ContDiffOn ℝ m (Function.uncurry F) Work.FTS.EllipticEst.Q0) {z : ℝ} (hz : 0 < z)
    (n : ℕ) : ContDiffOn ℝ n (fun θ => F z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hg : ContDiffOn ℝ n (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (contDiffOn_const (c := z)).prodMk (contDiffOn_id : ContDiffOn ℝ n (fun θ : ℝ => θ) _)
  have hmap : Set.MapsTo (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) (Set.Ioo 0 (Real.pi / 2))
      Work.FTS.EllipticEst.Q0 :=
    fun θ hθ => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hcomp := (hF n).comp hg hmap
  simpa [Function.comp_def, Function.uncurry] using hcomp

/-- The slice of `D_z^j Φ` at a positive radius is `C^∞` on the open angular interval. -/
theorem contDiffOn_slice_DzIter {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (j : ℕ) {z : ℝ} (hz : 0 < z) (n : ℕ) :
    ContDiffOn ℝ n (fun θ => Work.Spaces.DzIter j Φ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
  contDiffOn_slice_uncurry (hΦ.DzIter j).forall hz n

theorem aesm_LZ {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) {z : ℝ}
    (hz : 0 < z) (i : ℕ) :
    AEStronglyMeasurable (LZ Φ z i) (volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn
      (fun θ => Work.Spaces.DzIter i Φ z θ / Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    ((contDiffOn_slice_DzIter hΦ i hz 0).continuousOn).div (by fun_prop)
      (fun θ hθ => ne_of_gt (sin_two_pos_Ioo hθ))
  refine Work.Elliptic.pz_aesm_of_cont ?_
  refine ((hcont.mul (Work.Elliptic.pz_cont_weight z)).pow 2).congr ?_
  intro θ hθ
  simp only [Pi.pow_apply, Pi.mul_apply, LZ]
  rw [Work.Elliptic.DivSinFactor Φ i z θ hθ]

theorem aesm_LM {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) {z : ℝ}
    (hz : 0 < z) (k : ℕ) (α : ℝ) (i j : ℕ) :
    AEStronglyMeasurable (LM k α Φ z i j) (volume.restrict Work.Spaces.Iθ) := by
  by_cases hc : 1 ≤ i ∧ i + j ≤ k
  · have hSO : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φ z θ / Real.sin (2 * θ)) :=
      smoothOpen_div_sin hΦ
    have hcont : ContinuousOn
        (fun θ => Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (contDiffOn_slice_uncurry (hSO.mixed j i).forall hz 0).continuousOn
    refine Work.Elliptic.pz_aesm_of_cont
      (((hcont.mul (Work.Elliptic.pz_cont_Wt α z)).pow 2).congr ?_)
    intro θ hθ
    simp only [Pi.pow_apply, Pi.mul_apply, LM, if_pos hc]
  · have : LM k α Φ z i j = fun _ : ℝ => (0 : ℝ) := by
      funext θ; simp only [LM, if_neg hc]
    rw [this]
    exact Work.Elliptic.pz_aesm_of_cont continuousOn_const

theorem aesm_RZ {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) {z : ℝ}
    (hz : 0 < z) (i : ℕ) :
    AEStronglyMeasurable (RZ Φ z i) (volume.restrict Work.Spaces.Iθ) := by
  have hcont : ContinuousOn (fun θ => Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (contDiffOn_slice_uncurry (hΦ.pth.DzIter i).forall hz 0).continuousOn
  refine Work.Elliptic.pz_aesm_of_cont ?_
  refine ((hcont.mul (Work.Elliptic.pz_cont_weight z)).pow 2).congr ?_
  intro θ hθ
  simp only [Pi.pow_apply, Pi.mul_apply, RZ]

theorem aesm_RM {Φ : ℝ → ℝ → ℝ} (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) {z : ℝ}
    (hz : 0 < z) (k : ℕ) (α : ℝ) (i j : ℕ) :
    AEStronglyMeasurable (RM k α Φ z i j) (volume.restrict Work.Spaces.Iθ) := by
  by_cases hc : 1 ≤ i ∧ i + j ≤ k
  · have hcont : ContinuousOn (fun θ => Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (contDiffOn_slice_uncurry (hΦ.pth.mixed j i).forall hz 0).continuousOn
    refine Work.Elliptic.pz_aesm_of_cont
      (((hcont.mul (Work.Elliptic.pz_cont_Wt α z)).pow 2).congr ?_)
    intro θ hθ
    simp only [Pi.pow_apply, Pi.mul_apply, RM, if_pos hc]
  · have : RM k α Φ z i j = fun _ : ℝ => (0 : ℝ) := by
      funext θ; simp only [RM, if_neg hc]
    rw [this]
    exact Work.Elliptic.pz_aesm_of_cont continuousOn_const

end Work.FTS.EllipticEst.RPFresh
