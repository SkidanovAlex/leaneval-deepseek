/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg/mixedHdom` — the domination functions of the `δ ↓ 0` limit

The generic limit lemmas `Deleg.psiDIntegralLimit` and `Deleg.psiDLayerLimit` need, for each of
the four angular integrands `σ V²`, `σ U²`, `σ (z²∂_zzu)(∂_θθu)` and `σ U(∂_θθu)` of the
cut-off chain, the radial integrability of the absolute marginal

  `A ↦ |c A| · ∫_θ |G A θ|`

(`c = χ_n w²` for the first three, `c = (χ_n w² z²)'/z` for the fourth).  This module proves the
four statements from `AeData`, `HkMem α 0 (grad u)` and the a.e. mixed honesty `MixedHon`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Deleg.mixedPairAux2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- The `θ`-integral of `|σ θ · V z θ²|` equals the `θ`-integral of `σ θ · V z θ²` (the
integrand is nonnegative on `(0,π/2)`). -/
private theorem abs_setIntegral_eq_of_nonneg {V : ℝ → ℝ} (hV : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    0 ≤ Work.FTS.EllipticEst.AeColl.sigθ θ * V θ) (z : ℝ) :
    (∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * V θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * V θ := by
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [abs_of_nonneg (hV θ hθ)]

/-- **Domination for the `V`-slot** (`Ptr`, `Col`). -/
theorem hdom_Vz {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hM : MixedHon u) (n : ℕ) :
    Integrable (fun z => |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z| *
      ∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hdom0 : Integrable (fun z => Work.FTS.EllipticEst.AeColl.wtB n
      * ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
          * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrableOn_marginal_Vz_of_MixedHon hM n
  have hmarg : AEStronglyMeasurable (fun z => ∫ θ,
      |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    aesm_marginal (aesm_abs (aesm_joint_Vz hA))
  refine Integrable.mono' hdom0 ((aesm_abs (aesm_cut_mul_wt n)).mul hmarg) ?_
  filter_upwards [hM.1, ae_restrict_mem measurableSet_Ioi] with z hzint hz
  have hIθ : Integrable (fun θ => Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) := hzint
  have hnnθ : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ =>
      Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.sigθ θ) :=
    ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sigθ_nonneg_of_mem_Iθ hθ))
  have hmono : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.sigθ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
        * Work.FTS.EllipticEst.AeColl.sigθ θ :=
    setIntegral_mono_set hIθ hnnθ (Filter.Eventually.of_forall (fun θ hθ =>
      show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
  have hIabs : |∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))|
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2 := by
    rw [abs_of_nonneg (integral_nonneg (fun θ => abs_nonneg _))]
    exact abs_setIntegral_eq_of_nonneg (fun θ hθ => mul_nonneg
      (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
      (sq_nonneg _)) z
  have hnnI : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo (fun θ hθ => mul_nonneg
      (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
      (sq_nonneg _))
  rw [Real.norm_eq_abs, abs_mul, abs_abs, hIabs]
  calc |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z|
        * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2)
      ≤ Work.FTS.EllipticEst.AeColl.wtB n
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
              * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2) :=
        mul_le_mul_of_nonneg_right (Work.FTS.EllipticEst.AeColl.cut_mul_wt_bdd n z) hnnI
    _ = Work.FTS.EllipticEst.AeColl.wtB n
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
                * Work.FTS.EllipticEst.AeColl.sigθ θ) := by
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
        ring
    _ ≤ Work.FTS.EllipticEst.AeColl.wtB n
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.sigθ θ) :=
        mul_le_mul_of_nonneg_left hmono (wtB_nonneg n)

/-- **Domination for the `U`-slot** (`Atr`). -/
theorem hdom_Uz {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) (n : ℕ) :
    Integrable (fun z => |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z| *
      ∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hdom0 : Integrable (fun z => Work.FTS.EllipticEst.AeColl.wtB n
      * ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
          * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrableOn_marginal_Ioi_of_HkMem α hU).const_mul _
  have hmarg : AEStronglyMeasurable (fun z => ∫ θ,
      |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    aesm_marginal (aesm_abs (aesm_joint_Uz hA))
  refine Integrable.mono' hdom0 ((aesm_abs (aesm_cut_mul_wt n)).mul hmarg) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hIθ : Integrable (fun θ => Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
      * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hU (mem_Iz_of_pos hz)
  have hIθ' : Integrable (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ
      * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_mul_sq_Iθ_of_HkMem α hU hz
  have hIabs : |∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))|
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 := by
    rw [abs_of_nonneg (integral_nonneg (fun θ => abs_nonneg _))]
    exact abs_setIntegral_eq_of_nonneg (fun θ hθ => mul_nonneg
      (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
      (sq_nonneg _)) z
  have hnnI : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo (fun θ hθ => mul_nonneg
      (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
      (sq_nonneg _))
  -- the pointwise comparison `σ U² ≤ U² wt σ` on the open interval
  have hpt : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2)
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
          * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ := by
    refine integral_mono_of_nonneg ?_ (MeasureTheory.IntegrableOn.mono_set hIθ (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact mul_nonneg
        (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
        (sq_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hs0 := sigθ_nonneg_of_mem_Iθ
        (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      have hw1 := one_le_wt_of_pos hz
      have h1 : Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
          ≤ Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z := by
        simpa using mul_le_mul_of_nonneg_left hw1
          (sq_nonneg (Work.FTS.EllipticEst.AeColl.Uz u z θ))
      calc Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
          = Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.sigθ θ := by ring
        _ ≤ (Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z)
              * Work.FTS.EllipticEst.AeColl.sigθ θ := mul_le_mul_of_nonneg_right h1 hs0
        _ = Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ := by ring
  have hmono : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
        * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ :=
    setIntegral_mono_set hIθ (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (wt_nonneg z)) (sigθ_nonneg_of_mem_Iθ hθ)))
      (Filter.Eventually.of_forall (fun θ hθ =>
        show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
  rw [Real.norm_eq_abs, abs_mul, abs_abs, hIabs]
  calc |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z|
        * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2)
      ≤ Work.FTS.EllipticEst.AeColl.wtB n
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
              * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2) :=
        mul_le_mul_of_nonneg_right (Work.FTS.EllipticEst.AeColl.cut_mul_wt_bdd n z) hnnI
    _ ≤ Work.FTS.EllipticEst.AeColl.wtB n
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ) :=
        mul_le_mul_of_nonneg_left (le_trans hpt hmono) (wtB_nonneg n)

/-- **Domination for the mixed radial/angular slot** (`Dtr`). -/
theorem hdom_AzB {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (n : ℕ) :
    Integrable (fun z => |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z| *
      ∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
        * Work.Spaces.pthIter 2 u z θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hAz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.AeColl.Az u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioi (0 : ℝ)) :=
    integrableOn_marginal_Ioi_of_HkMem α (Work.FTS.EllipticEst.H2W.Ae.AeData.memRad2 hA)
  have hB : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.pthIter 2 u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioi (0 : ℝ)) :=
    integrableOn_marginal_Ioi_of_HkMem α (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA)
  have hdom0 : Integrable (fun z => Work.FTS.EllipticEst.AeColl.wtB n *
      ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Az u z θ ^ 2
            * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.pthIter 2 u z θ ^ 2
            * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hAz.add hB).const_mul _
  have hmarg : AEStronglyMeasurable (fun z => ∫ θ,
      |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
        * Work.Spaces.pthIter 2 u z θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    aesm_marginal (aesm_abs (aesm_prod_of_continuousOn_Q0 (continuousOn_joint_AzB hA)))
  refine Integrable.mono' hdom0 ((aesm_abs (aesm_cut_mul_wt n)).mul hmarg) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hIabs : |∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
        * Work.Spaces.pthIter 2 u z θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))|
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), |Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Az u z θ * Work.Spaces.pthIter 2 u z θ| := by
    rw [abs_of_nonneg (integral_nonneg (fun θ => abs_nonneg _))]
  have hnnI : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
        * Work.Spaces.pthIter 2 u z θ| :=
    setIntegral_nonneg measurableSet_Ioo (fun θ _ => abs_nonneg _)
  rw [Real.norm_eq_abs, abs_mul, abs_abs]
  calc |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z|
        * |∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
            * Work.Spaces.pthIter 2 u z θ|
            ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))|
      = |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z|
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
                * Work.Spaces.pthIter 2 u z θ|) := by rw [hIabs]
    _ ≤ Work.FTS.EllipticEst.AeColl.wtB n
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
                * Work.Spaces.pthIter 2 u z θ|) :=
        mul_le_mul_of_nonneg_right (Work.FTS.EllipticEst.AeColl.cut_mul_wt_bdd n z) hnnI
    _ ≤ Work.FTS.EllipticEst.AeColl.wtB n *
          ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Az u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.pthIter 2 u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)) :=
        mul_le_mul_of_nonneg_left
          (abs_mixed_slice_le α (Work.FTS.EllipticEst.H2W.Ae.AeData.memRad2 hA)
            (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA) hz) (wtB_nonneg n)

/-- **Domination for the transfer slot** (`Trtr`). -/
theorem hdom_UzB {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) (n : ℕ) :
    Integrable (fun z => |deriv (fun z' => Work.FTS.EllipticEst.cut n z'
        * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z| *
      ∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
        * Work.Spaces.pthIter 2 u z θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  obtain ⟨C, hCpos, hCbd⟩ := trtr_coef_bound n
  have hU' : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioi (0 : ℝ)) :=
    integrableOn_marginal_Ioi_of_HkMem α hU
  have hB : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.pthIter 2 u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioi (0 : ℝ)) :=
    integrableOn_marginal_Ioi_of_HkMem α (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA)
  have hdom0 : Integrable (fun z => C *
      ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
            * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.pthIter 2 u z θ ^ 2
            * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hU'.add hB).const_mul _
  have hmarg : AEStronglyMeasurable (fun z => ∫ θ,
      |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
        * Work.Spaces.pthIter 2 u z θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    aesm_marginal (aesm_abs (aesm_prod_of_continuousOn_Q0 (continuousOn_joint_UzB hA)))
  refine Integrable.mono' hdom0 ((aesm_abs (aesm_trtr_coef n)).mul hmarg) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hIabs : |∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
        * Work.Spaces.pthIter 2 u z θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))|
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), |Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Uz u z θ * Work.Spaces.pthIter 2 u z θ| := by
    rw [abs_of_nonneg (integral_nonneg (fun θ => abs_nonneg _))]
  have hnnI : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
        * Work.Spaces.pthIter 2 u z θ| :=
    setIntegral_nonneg measurableSet_Ioo (fun θ _ => abs_nonneg _)
  rw [Real.norm_eq_abs, abs_mul, abs_abs, hIabs]
  calc |deriv (fun z' => Work.FTS.EllipticEst.cut n z' * Work.FTS.EllipticEst.AeColl.wt z'
          * z' ^ 2) z / z|
        * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
              * Work.Spaces.pthIter 2 u z θ|)
      ≤ (C * Work.FTS.EllipticEst.AeColl.wt z)
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
                * Work.Spaces.pthIter 2 u z θ|) :=
        mul_le_mul_of_nonneg_right (hCbd z hz) hnnI
    _ = C * (Work.FTS.EllipticEst.AeColl.wt z
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
                * Work.Spaces.pthIter 2 u z θ|)) := by ring
    _ ≤ C * ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.pthIter 2 u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)) :=
        mul_le_mul_of_nonneg_left
          (abs_mixed_slice_wt_le α hU (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA) hz)
          (le_of_lt hCpos)

end

end Work.FTS.EllipticEst.Deleg
