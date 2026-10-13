import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.GalBasis.cc.integral_abs_L12dens_le
import Submission.Work.Elliptic.L12densFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc

open MeasureTheory Filter

/-- Monotonicity of the set integral over the half-line: since `(z,∞) ⊆ (0,∞)` for `0 ≤ z`,
a nonnegative function integrable on `(0,∞)` has a smaller integral on `(z,∞)`. -/
lemma setIntegral_Ioi_le_Ioi_zero {f : ℝ → ℝ} {z : ℝ} (hz : 0 ≤ z)
    (hint : IntegrableOn f (Set.Ioi 0)) (hnn : ∀ s, 0 ≤ f s) :
    ∫ s in Set.Ioi z, f s ≤ ∫ s in Set.Ioi 0, f s :=
  setIntegral_mono_set hint (Filter.Eventually.of_forall hnn)
    (Filter.Eventually.of_forall fun x hx => by
      simp only [Set.mem_Ioi] at hx ⊢
      linarith)

/-- **The integrated pointwise bound on the `L₁₂`-density, on the tail `(z,∞)`.**
If `|L12dens h s| ≤ Wlam s · (BK · √(∫_θ HkIntegrand α k h s θ))` for every `s > z` and
`h ∈ ℋ^k_α`, then the same bound holds after integrating in `s` over `(z,∞)`, with a constant
that does not depend on `k` or on `z`:

`∫_{s>z} |L12dens h s| ≤ BK · √W2 · √(HkSq α k h)`.

This is Cauchy–Schwarz in the radial variable: the weight `Wlam` is square-integrable on
`(0,∞)` with `∫_{(0,∞)} Wlam² = W2`, and
`∫_{(z,∞)} (√(∫_θ HkIntegrand))² ≤ ∫_{(0,∞)} (√(∫_θ HkIntegrand))² = HkSq α k h`
(the sets `(0,∞)` and `ℤ = [0,∞)` differ by the null set `{0}`, and `(z,∞) ⊆ (0,∞)` for
`z ≥ 0`, where both integrands are nonnegative). -/
theorem integral_abs_L12dens_le_Ioi (α : ℝ) (k : ℕ) (h : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α k h) {z : ℝ} (hz : 0 ≤ z)
    (hbd : ∀ s ∈ Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h s θ))) :
    ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2
        * Real.sqrt (Work.Spaces.HkSq α k h) := by
  -- the angular marginal `H` and its square root `A`
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k h s θ
  have hAnn : ∀ s, 0 ≤ A s := fun s => Real.sqrt_nonneg _
  -- integrability of `H = A²` on `[0,∞)` and hence on `(z,∞)`
  have hH_int_Iz : IntegrableOn H Work.Spaces.Iz := by
    simpa only [hH] using hmem.2
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := by
    intro x hx
    simp only [Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith
  have hsub0 : Set.Ioi (0 : ℝ) ⊆ Work.Spaces.Iz := fun x hx => by
    simp only [Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    exact le_of_lt hx
  have hzle : ∀ s ∈ Set.Ioi z, (0 : ℝ) ≤ s := fun s hs => by
    simp only [Set.mem_Ioi] at hs
    linarith
  have hH_int : IntegrableOn H (Set.Ioi z) := hH_int_Iz.mono_set hsub
  have hH_int0 : IntegrableOn H (Set.Ioi 0) := hH_int_Iz.mono_set hsub0
  have hH_aesm : AEStronglyMeasurable H (volume.restrict (Set.Ioi z)) :=
    hH_int.aestronglyMeasurable
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi z)) := by
    rw [hA]
    exact (hH_aesm.aemeasurable.sqrt).aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi z) := by
    refine hH_int.congr ?_
    filter_upwards with s
    rw [hA]
    exact (Real.sq_sqrt (hHnn s)).symm
  have hA_memLp : MemLp A 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hA_aesm).mpr hA2_int
  -- the radial weight `Wlam` is square-integrable
  have hWlam_aesm : AEStronglyMeasurable Wlam (volume.restrict (Set.Ioi z)) := by
    change AEStronglyMeasurable (fun s : ℝ => s / (1 + s) ^ 2)
      (volume.restrict (Set.Ioi z))
    refine ContinuousOn.aestronglyMeasurable (μ := volume)
      (continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2) ?_)
      measurableSet_Ioi
    intro s hs
    have hne : (1 : ℝ) + s ≠ 0 := by
      simp only [Set.mem_Ioi] at hs
      linarith
    exact pow_ne_zero 2 hne
  have hWlam_sq_int : IntegrableOn (fun s => Wlam s ^ 2) (Set.Ioi z) :=
    Work.Elliptic.psi_sq_integrable_aux.mono_set (fun x hx => by
      simp only [Set.mem_Ioi] at hx ⊢
      linarith)
  have hWlam_memLp : MemLp Wlam 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hWlam_aesm).mpr hWlam_sq_int
  -- `∫_{(z,∞)} A² ≤ HkSq α k h`
  have hIz_eq : ∫ s in Work.Spaces.Iz, H s = Work.Spaces.HkSq α k h := by
    rw [hH]
    rfl
  have hA2sq_le : ∫ s in Set.Ioi z, A s ^ 2 ≤ Work.Spaces.HkSq α k h := by
    have h1 : ∫ s in Set.Ioi z, A s ^ 2 = ∫ s in Set.Ioi z, H s :=
      setIntegral_congr_fun measurableSet_Ioi fun s _ => by
        rw [hA]
        exact Real.sq_sqrt (hHnn s)
    have h2 : ∫ s in Set.Ioi z, H s ≤ ∫ s in Set.Ioi 0, H s :=
      setIntegral_Ioi_le_Ioi_zero hz hH_int0 hHnn
    have h3 : ∫ s in Set.Ioi 0, H s = ∫ s in Work.Spaces.Iz, H s :=
      MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici' (MeasureTheory.measure_singleton 0))
    calc ∫ s in Set.Ioi z, A s ^ 2 = ∫ s in Set.Ioi z, H s := h1
      _ ≤ ∫ s in Set.Ioi 0, H s := h2
      _ = ∫ s in Work.Spaces.Iz, H s := h3
      _ = Work.Spaces.HkSq α k h := hIz_eq
  -- Cauchy–Schwarz in the radial variable
  have hCS : ∫ s in Set.Ioi z, Wlam s * A s
      ≤ Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α k h) := by
    have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
      (u := Wlam) (v := A) (s := Set.Ioi z) hWlam_memLp hA_memLp
    have hnn : 0 ≤ ∫ s in Set.Ioi z, Wlam s * A s := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      show ∀ᵐ s ∂(volume.restrict (Set.Ioi z)), (0 : ℝ) ≤ Wlam s * A s
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun s hs => mul_nonneg (Wlam_nonneg (hzle s hs)) (hAnn s)
    rw [abs_of_nonneg hnn] at hcs
    refine le_trans hcs (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · refine Real.sqrt_le_sqrt ?_
      show ∫ s in Set.Ioi z, Wlam s ^ 2 ≤ W2
      exact setIntegral_Ioi_le_Ioi_zero hz Work.Elliptic.psi_sq_integrable_aux
        (fun s => sq_nonneg _)
    · exact Real.sqrt_le_sqrt hA2sq_le
  -- AM–GM, giving integrability of the majorant
  have hAMGM : ∀ s ∈ Set.Ioi z, Wlam s * A s ≤ Wlam s ^ 2 + A s ^ 2 := by
    intro s _
    nlinarith [sq_nonneg (Wlam s - A s)]
  have hsum_int : IntegrableOn (fun s => Wlam s ^ 2 + A s ^ 2) (Set.Ioi z) :=
    hWlam_sq_int.add hA2_int
  have hdom_int : IntegrableOn (fun s => BK * (Wlam s * A s)) (Set.Ioi z) := by
    refine Integrable.mono' (hsum_int.const_mul BK) ?_ ?_
    · exact (hWlam_aesm.mul hA_aesm).const_mul BK
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
      have hnn : 0 ≤ BK * (Wlam s * A s) :=
        mul_nonneg BK_nonneg (mul_nonneg (Wlam_nonneg (hzle s hs)) (hAnn s))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hAMGM s hs) BK_nonneg
  have h2 : ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi z, BK * (Wlam s * A s) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun s => abs_nonneg _) hdom_int ?_
    show ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      |Work.Construction.L12dens h s| ≤ BK * (Wlam s * A s)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hb := hbd s hs
    have hbA : |Work.Construction.L12dens h s| ≤ Wlam s * (BK * A s) := by
      simpa only [hA, hH] using hb
    calc |Work.Construction.L12dens h s| ≤ Wlam s * (BK * A s) := hbA
      _ = BK * (Wlam s * A s) := by ring
  have h3 : ∫ s in Set.Ioi z, BK * (Wlam s * A s)
      = BK * ∫ s in Set.Ioi z, Wlam s * A s :=
    MeasureTheory.integral_const_mul BK _
  have h4 : BK * ∫ s in Set.Ioi z, Wlam s * A s
      ≤ BK * (Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α k h)) :=
    mul_le_mul_of_nonneg_left hCS BK_nonneg
  calc ∫ s in Set.Ioi z, |Work.Construction.L12dens h s|
      ≤ ∫ s in Set.Ioi z, BK * (Wlam s * A s) := h2
    _ = BK * ∫ s in Set.Ioi z, Wlam s * A s := h3
    _ ≤ BK * (Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α k h)) := h4
    _ = BK * Real.sqrt W2 * Real.sqrt (Work.Spaces.HkSq α k h) := by ring

end Work.FTS.GalBasis.cc
