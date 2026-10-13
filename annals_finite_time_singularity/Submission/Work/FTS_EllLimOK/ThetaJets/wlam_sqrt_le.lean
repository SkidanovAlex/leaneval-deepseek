import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ThetaJets

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The radial Cauchy–Schwarz inequality against the weight `Wlam s = s/(1+s)²`

`Wlam` is square-integrable on `(0,∞)` (with `∫ Wlam² = W2`) and is nonnegative there, so
for any nonnegative integrable `F` the pairing `∫_{(0,∞)} Wlam·√F` is dominated by the
`L²`-norms of the two factors:

  `∫_{(0,∞)} Wlam s · √(F s) ds ≤ √W2 · √(∫_{(0,∞)} F)`.

Both the finiteness of the left-hand side (through `2ab ≤ a² + b²`) and the sharp constant
(pure Cauchy–Schwarz) are recorded below.  The consumer only ever instantiates `F` with the
angular marginal `s ↦ ∫_θ HkIntegrand α k g s θ` (see `wlam_sqrt_le`), but the statement is
kept general so that it can be reused for other radial profiles. -/
theorem wlam_mul_sqrt_le {F : ℝ → ℝ} (hF_int : MeasureTheory.IntegrableOn F (Set.Ioi 0))
    (hF_nn : ∀ s, 0 ≤ F s) :
    MeasureTheory.IntegrableOn (fun s : ℝ => Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (F s))
        (Set.Ioi 0) ∧
      (0 ≤ ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (F s)) ∧
      (∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (F s))
        ≤ Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), F s) := by
  -- `A = √F` is `L²` on `(0,∞)`, because `A² = F` is integrable
  have hA_aesm : AEStronglyMeasurable (fun s : ℝ => Real.sqrt (F s))
      (volume.restrict (Set.Ioi 0)) :=
    (hF_int.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hA2_int : MeasureTheory.IntegrableOn (fun s : ℝ => (Real.sqrt (F s)) ^ 2)
      (Set.Ioi 0) := by
    refine hF_int.congr ?_
    filter_upwards with s
    exact (Real.sq_sqrt (hF_nn s)).symm
  have hA_memLp : MemLp (fun s : ℝ => Real.sqrt (F s)) 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hA_aesm).mpr hA2_int
  -- `Wlam` is a.e. strongly measurable on `(0,∞)`
  have hWlam_aesm : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam
      (volume.restrict (Set.Ioi 0)) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi 0))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_) measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  -- and its square is integrable, by `Work.Elliptic.psi_sq_integrable_aux`
  have hWlam_sq_int : MeasureTheory.IntegrableOn
      (fun s : ℝ => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi 0) := by
    simpa only [Work.FTS.GalBasis.cc.Wlam] using Work.Elliptic.psi_sq_integrable_aux
  have hWlam_memLp : MemLp Work.FTS.GalBasis.cc.Wlam 2 (volume.restrict (Set.Ioi 0)) :=
    (memLp_two_iff_integrable_sq hWlam_aesm).mpr hWlam_sq_int
  -- `∫_{(0,∞)} A² = ∫_{(0,∞)} F`
  have hA2sq : ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt (F s)) ^ 2
      = ∫ s in Set.Ioi (0 : ℝ), F s :=
    setIntegral_congr_fun measurableSet_Ioi fun s _ => Real.sq_sqrt (hF_nn s)
  have hnn : 0 ≤ ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (F s) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    show ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)),
      (0 : ℝ) ≤ Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (F s)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun s hs =>
      mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt hs)) (Real.sqrt_nonneg _)
  -- Cauchy–Schwarz in the radial variable
  have hCS : ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (F s)
      ≤ Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (∫ s in Set.Ioi (0 : ℝ), F s) := by
    have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
      (u := Work.FTS.GalBasis.cc.Wlam) (v := fun s : ℝ => Real.sqrt (F s)) (s := Set.Ioi 0)
      hWlam_memLp hA_memLp
    rw [hA2sq] at hcs
    have hW2eq : (∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s ^ 2)
        = Work.FTS.GalBasis.cc.W2 := rfl
    rw [hW2eq] at hcs
    rwa [abs_of_nonneg hnn] at hcs
  -- integrability of the product, from `2ab ≤ a² + b²`
  have hint : MeasureTheory.IntegrableOn
      (fun s : ℝ => Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (F s)) (Set.Ioi 0) := by
    have hAMGM : ∀ s ∈ Set.Ioi (0 : ℝ),
        Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (F s)
          ≤ Work.FTS.GalBasis.cc.Wlam s ^ 2 + (Real.sqrt (F s)) ^ 2 :=
      fun s _ => by nlinarith [sq_nonneg (Work.FTS.GalBasis.cc.Wlam s - Real.sqrt (F s))]
    have hsum_int : MeasureTheory.IntegrableOn
        (fun s : ℝ => Work.FTS.GalBasis.cc.Wlam s ^ 2 + (Real.sqrt (F s)) ^ 2)
        (Set.Ioi 0) :=
      hWlam_sq_int.add hA2_int
    refine hsum_int.mono' (hWlam_aesm.mul hA_aesm) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hnn' : 0 ≤ Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (F s) :=
      mul_nonneg (Work.FTS.GalBasis.cc.Wlam_nonneg (le_of_lt hs)) (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn']
    exact hAMGM s hs
  exact ⟨hint, hnn, hCS⟩

theorem wlam_sqrt_le (α : ℝ) (k : ℕ) {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α k g) :
    MeasureTheory.IntegrableOn
        (fun s : ℝ => Work.FTS.GalBasis.cc.Wlam s
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ))
        (Set.Ioi 0) ∧
      (0 ≤ ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ)) ∧
      (∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ))
        ≤ Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α k g) := by
  -- the angular marginal `s ↦ ∫_θ HkIntegrand α k g s θ` is nonnegative and integrable on `(0,∞)`
  have hF_int : MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ)
      (Set.Ioi 0) :=
    hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hF_nn : ∀ s, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g s θ
  obtain ⟨h1, h2, h3⟩ := wlam_mul_sqrt_le
    (F := fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ) hF_int hF_nn
  -- `HkSq` integrates over `Iz = [0,∞)`, which differs from `(0,∞)` by the null set `{0}`
  have hHk : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ)
      = Work.Spaces.HkSq α k g := by
    have h2' : ∫ s in Set.Ioi (0 : ℝ),
          (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ) s
        = ∫ s in Work.Spaces.Iz,
          (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ) s :=
      MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici' (MeasureTheory.measure_singleton 0))
    have h3' : ∫ s in Work.Spaces.Iz,
          (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ) s
        = Work.Spaces.HkSq α k g := rfl
    exact h2'.trans h3'
  refine ⟨h1, h2, ?_⟩
  calc ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ)
      = ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s
          * Real.sqrt ((fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k g s θ) s) := rfl
    _ ≤ Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (∫ s in Set.Ioi (0 : ℝ),
          (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ) s) := h3
    _ = Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α k g) := by rw [hHk]

end Work.FTS_EllLimOK.ThetaJets
