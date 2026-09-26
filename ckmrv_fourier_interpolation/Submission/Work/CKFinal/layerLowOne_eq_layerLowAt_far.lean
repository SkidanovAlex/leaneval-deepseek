import Mathlib
import Submission.Work.LayerCont.LowDouble
import Submission.Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far
import Submission.Work.LayerCont.Coinc.layerLowCoinc_eq_layerLow_far
import Submission.Work.LayerCont.Coinc.DetourCoinc
import Submission.Work.LayerCont.Coinc.CoincClean
import Submission.Work.LayerCont.DetourNoOrbit
import Submission.Work.Asymptotics.contourLeftAux

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.CKFinal

/-- **Far-side twin of `Work.LayerCont.layerLowOne_eq_layerLowAt`** (`1 < τ.re` instead of
`τ.re < 1`), at the coincidence height `t₀ = 1`.

On the near side (`Submission/Work/LayerCont/LowDouble.lean`, sorry-free) the continued low piece
`layerLowOne ℓ d p t₀ A ξ r` satisfies `layerLowOne = layerLowAt` for `τ.re < 1`, the removed
interval integral being recovered by the *pole-side* identity
`Work.Asymptotics.detourLeftC_eq_interval_sub_residue` (whose residue correction is then cancelled
by the `resCorr` term built into `layerLowOne`).

On the far side (`1 < τ.re`) the swept rectangle `[-ξ,0] × [1-A,1+A]` contains only the removable
coincidence `S • (-1 +ᵥ τ)` (hypotheses `hcl`, `hcoinc`), so the detour identity is residue-free:
`Work.LayerCont.Coinc.detourLeftC_eq_interval_of_coinc_pointwise` gives
`detourLeftC ℓ d r 1 A ξ τ = ∫_{I} edgeV`, and the `resCorr` term of `layerLowOne` is *not*
cancelled.  Hence
`layerLowOne = sinSqC r * ∫_{(0,p]} K·gauss + sinSqC r * resCorr = layerLowAt + sinSqC r * resCorr`.

Cleanliness of the removed interval `I` is derived from `hcl` + `hcoinc`
(`Work.LayerCont.Coinc.jInvariantFun_ne_imagAxis_of_coinc`); combined with `hcleanAll` off `I` this
gives cleanliness of the whole extended contour `(0,p]`, so `KaxisBoundedIocBall` dominates every
piece and the split `∫_{(0,p]} = ∫_{(0,p]\I} + ∫_I` goes through as in the near-side proof. -/
theorem layerLowOne_eq_layerLowAt_far (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {p A ξ ε r : ℝ} (hA : 0 < A) (hξ : 0 < ξ) (hε : 0 < ε)
    (hlo : 0 < 1 - A) (hhi : 1 + A ≤ p)
    (hcl : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 one_pos) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect 1 A ξ z →
          (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ)))
    (hcoinc : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 one_pos) < ε → 1 < τ.re →
      Work.LayerCont.Coinc.coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ 1 A ξ)
    (hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 one_pos) < ε → 1 < τ.re →
      Work.Residues.jprime τ ≠ 0)
    (hcleanAll : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 one_pos) < ε → 1 < τ.re →
      ∀ (t : ℝ) (ht : 0 < t), t ∈ (Set.Ioc (0 : ℝ) p) \ Set.Ioo (1 - A) (1 + A) →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∀ (τ : UpperHalfPlane), dist τ (Work.Asymptotics.onePlusI 1 one_pos) < ε → 1 < τ.re →
      Work.LayerCont.layerLowOne ℓ d p 1 A ξ r τ
        = Work.LayerCont.layerLowAt ℓ d p r τ
          + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ := by
  intro τ hτ hτre
  have hp0 : 0 < p := by linarith
  -- ### the detour identity (residue-free, at the removable coincidence)
  have hres : Work.Asymptotics.detourLeftC ℓ d r 1 A ξ τ
      = (∫ v in Set.Ioo (1 - A) (1 + A), Work.Asymptotics.edgeV ℓ d r τ 0 v) :=
    Work.LayerCont.Coinc.detourLeftC_eq_interval_of_coinc_pointwise ℓ d hd
      (r := r) (c := 1) (A := A) (ξ := ξ) hA hξ hlo τ
      (Work.LayerCont.Coinc.dlcc_clean_coinc τ 1 A ξ hlo (hcl τ hτ hτre))
      (hcoinc τ hτ hτre) (hdeg τ hτ hτre)
  -- ### the axis integrand is the contour integrand
  have hedge : (∫ v in Set.Ioo (1 - A) (1 + A), Work.Asymptotics.edgeV ℓ d r τ 0 v)
      = ∫ v in Set.Ioo (1 - A) (1 + A),
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      (fun v hv => Work.LayerCont.edgeV_zero_eq ℓ d r τ (by linarith [hv.1, hlo]))
  -- ### far-side cleanliness of the removed interval
  have hcleanI : ∀ (s : ℝ) (hs : 0 < s), s ∈ Set.Icc (1 - A) (1 + A) →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) :=
    fun s hs hsI => Work.LayerCont.Coinc.jInvariantFun_ne_imagAxis_of_coinc τ (hcl τ hτ hτre)
      (Work.LayerCont.Coinc.coincℂ_re_neg_of_mem_openLeftRectℂ (hcoinc τ hτ hτre)) hs
      (Work.LayerCont.Coinc.imagAxis_mem_leftRect hs hξ hsI)
  -- ### cleanliness of the whole extended contour `(0,p]`
  have hcleanFull : ∀ (t : ℝ) (ht : 0 < t), t ∈ Set.Ioc (0 : ℝ) p →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    intro t ht htI
    by_cases hmem : t ∈ Set.Ioo (1 - A) (1 + A)
    · exact hcleanI t ht ⟨hmem.1.le, hmem.2.le⟩
    · exact hcleanAll τ hτ hτre t ht ⟨htI, hmem⟩
  -- ### integrability from the uniform bound on the extended contour
  have hmeasmal : Measurable
      (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Work.Asymptotics.gaussWeight r t) :=
    (Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).mul
      (by unfold Work.Asymptotics.gaussWeight; fun_prop)
  obtain ⟨C, hCnn, hCb⟩ := Work.LayerCont.KaxisBoundedIocBall ℓ d hd τ hp0 hcleanFull
  have hIntF : IntegrableOn
      (fun v : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
        * Work.Asymptotics.gaussWeight r v) (Set.Ioc (0 : ℝ) p) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ hmeasmal.aestronglyMeasurable (C * 1) ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      rw [norm_mul]
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v‖
            * ‖Work.Asymptotics.gaussWeight r v‖
          ≤ C * 1 := mul_le_mul (hCb v hv) (Work.LayerCont.norm_gaussWeight_le_one r v
              (le_of_lt hv.1)) (norm_nonneg _) hCnn
        _ = C * 1 := rfl
  -- ### the interval lies in `(0,p]`
  have hIsub : Set.Ioo (1 - A) (1 + A) ⊆ Set.Ioc (0 : ℝ) p := fun x hx =>
    ⟨lt_trans hlo hx.1, le_of_lt (lt_of_lt_of_le hx.2 hhi)⟩
  have hInt1 : IntegrableOn
      (fun v : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
        * Work.Asymptotics.gaussWeight r v) (Set.Ioo (1 - A) (1 + A)) :=
    hIntF.mono_set hIsub
  have hIntE₁ : IntegrableOn
      (fun v : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v
        * Work.Asymptotics.gaussWeight r v)
      ((Set.Ioc (0 : ℝ) p) \ Set.Ioo (1 - A) (1 + A)) :=
    hIntF.mono_set (fun x hx => hx.1)
  -- ### the splitting of the extended contour
  have hsplit₁ : (∫ t in Set.Ioc (0 : ℝ) p,
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t)
      = (∫ t in (Set.Ioc (0 : ℝ) p) \ Set.Ioo (1 - A) (1 + A),
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t)
        + ∫ v in Set.Ioo (1 - A) (1 + A),
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v := by
    have hset : Set.Ioc (0 : ℝ) p
        = ((Set.Ioc (0 : ℝ) p) \ Set.Ioo (1 - A) (1 + A)) ∪ Set.Ioo (1 - A) (1 + A) := by
      rw [Set.sdiff_union_self, Set.union_eq_left.mpr hIsub]
    have h2 := MeasureTheory.setIntegral_union
      (s := (Set.Ioc (0 : ℝ) p) \ Set.Ioo (1 - A) (1 + A))
      (t := Set.Ioo (1 - A) (1 + A))
      (Set.disjoint_left.mpr (fun x hx hx' => hx.2 hx')) measurableSet_Ioo hIntE₁ hInt1
    rw [← hset] at h2
    exact h2
  -- ### `layerLowAt` unfolded
  have hlow : Work.LayerCont.layerLowAt ℓ d p r τ
      = Work.Asymptotics.sinSqC r * (∫ t in Set.Ioc (0 : ℝ) p,
          Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t) := by
    rw [Work.LayerCont.layerLowAt, intervalIntegral.integral_of_le hp0.le]
  -- ### assembly
  have hdet : Work.Asymptotics.detourLeftC ℓ d r 1 A ξ τ
      = (∫ v in Set.Ioo (1 - A) (1 + A),
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v) := by
    rw [hres, hedge]
  simp only [Work.LayerCont.layerLowOne, Work.LayerCont.layerLowPieceAt]
  rw [hdet]
  have halg : Work.Asymptotics.sinSqC r
        * ((∫ t in (Set.Ioc (0 : ℝ) p) \ Set.Ioo (1 - A) (1 + A),
              Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t)
          + ∫ v in Set.Ioo (1 - A) (1 + A),
              Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ v * Work.Asymptotics.gaussWeight r v)
      = Work.Asymptotics.sinSqC r
        * (∫ t in Set.Ioc (0 : ℝ) p,
            Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Work.Asymptotics.gaussWeight r t) := by
    rw [hsplit₁]
  rw [halg, hlow]

end Work.CKFinal
