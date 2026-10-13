import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.Vocab
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Blocks.IMC.cs_integral_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# `gSlots`: the six `z`-slot bounds for a perturbation `g ∈ ℛ⁴(α)`

This file proves the six conjuncts of `gSlots`, the `z`-slots of the nonlinear estimates
for the perturbation `g` of the self-similar profile.

* The first three conjuncts are the *unweighted* `L²`-masses
  `∫ w(z) · ∫_θ (·)²` of `g`, `D_θ g` and `D_z g`: each is dominated by a single summand
  of the `ℋ⁴`-integrand (`g²` by the `D_z⁰`-slot, `(D_θg)²` by the mixed `(i,j) = (1,0)`-slot
  and `(D_zg)²` by the `D_z¹`-slot), whence by `HkSq α 4 g`.

* The last three conjuncts are the *weighted* `1/z`-masses
  `∫ z⁻¹ · A(z)` with `A = √(∫_θ g²)`, `A = ∫_θ |D_θ g|`, `A = ∫_θ |∂_θ g|`.
  Here the sharp machinery is needed: an *angular* Cauchy–Schwarz
  (`∫_θ |∂_θ g| ≤ √(∫_θ (D_θ g)² sin(2θ)^{-γ}) · √(∫_θ sin(2θ)^{γ-2})`, where the fact that
  `γ - 1 = α/10` is what produces the constant `√(10/α)`), followed by a *radial*
  Cauchy–Schwarz against the square-integrable weight `z ↦ z/(1+z)² = 1/(z·w(z))`
  (with `∫_0^∞ (z/(1+z)²)² dz = 1/3 ≤ 1`), which converts `∫ z⁻¹ A` into `√(HkSq α 4 g)`.

All constants are deliberately crude: the statements only need `1 ≤ 20`, `√(π/2) ≤ 20` and
`10 ≤ 300`, so every loss of a factor is harmless.
-/

/-! ## Elementary facts about the weight and the angular interval -/

lemma w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; exact div_nonneg (sq_nonneg _) (sq_nonneg _)

lemma w_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

lemma one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : (0:ℝ) < z ^ 2 := by positivity
  rw [Work.Spaces.w, one_le_div hz2]
  nlinarith [sq_nonneg z]

/-- The two endpoints `0` and `π/2` of `Iθ` are null: the angular measure of `Iθ` is that of
the open interval. -/
lemma restrict_Iθ_eq_Ioo : volume.restrict Work.Spaces.Iθ
    = volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2)) := by
  rw [Work.Spaces.Iθ]
  exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm

lemma ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
  rw [restrict_Iθ_eq_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)

lemma sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) : 0 < Real.sin (2*θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `HkSq` is the iterated integral over `(0,∞)`: the `z = 0` slice is irrelevant. -/
lemma HkSq_eq_integral_Ioi (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 4 g = ∫ z in Set.Ioi (0:ℝ), ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 g z θ := by
  rw [Work.Spaces.HkSq, Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]

/-- The elementary amplification behind every slot bound: for `w₀ ≥ 1`, `0 < s ≤ 1`,
`p ≥ 0` the `w₀`-weighted square is dominated by the `w₀/s^{p/2}`-weighted one. -/
lemma w_mul_sq_le (x w0 s p : ℝ) (hw : 1 ≤ w0) (hs : 0 < s) (hs1 : s ≤ 1) (hp : 0 ≤ p) :
    w0 * x ^ 2 ≤ (x * (w0 / s ^ (p / 2))) ^ 2 := by
  have hsp : 0 < s ^ (p/2) := Real.rpow_pos_of_pos hs _
  have hsp1 : s ^ (p/2) ≤ 1 := Real.rpow_le_one hs.le hs1 (by linarith)
  have hsp2 : (s ^ (p/2)) ^ 2 ≤ w0 := by
    have h2 : (s^(p/2)) * (s^(p/2)) ≤ 1 * 1 := mul_self_le_mul_self hsp.le hsp1
    nlinarith [h2, hw, sq_nonneg (s^(p/2))]
  have hwpos : 0 < w0 := lt_of_lt_of_le zero_lt_one hw
  have hcoef : w0 ≤ (w0 / s ^ (p/2)) ^ 2 := by
    have hsp2pos : 0 < (s^(p/2))^2 := pow_pos hsp 2
    have h := div_le_div_of_nonneg_left (sq_nonneg w0) hsp2pos hsp2
    have hw0 : w0 = w0 ^ 2 / w0 := by field_simp
    calc w0 = w0 ^ 2 / w0 := hw0
      _ ≤ w0 ^ 2 / (s ^ (p/2)) ^ 2 := h
      _ = (w0 / s ^ (p/2)) ^ 2 := by rw [div_pow]
  calc w0 * x^2 ≤ (w0 / s^(p/2))^2 * x^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg x)
    _ = (x * (w0 / s^(p/2)))^2 := by ring

/-! ## The pointwise slot bounds -/

lemma slot_g (α : ℝ) {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    Work.Spaces.w z * (g z θ)^2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs := sin_two_pos hθ
  have hs1 : Real.sin (2*θ) ≤ 1 := Real.sin_le_one _
  have h1 := w_mul_sq_le (g z θ) (Work.Spaces.w z) (Real.sin (2*θ)) Work.Spaces.eta
    (one_le_w_of_pos hz) hs hs1 (by norm_num [Work.Spaces.eta])
  have h2 := Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 0 (by norm_num)
  simpa using le_trans h1 h2

lemma slot_Dth (α : ℝ) (hα : 0 < α) {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    Work.Spaces.w z * (Work.Spaces.Dth g z θ)^2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs := sin_two_pos hθ
  have hs1 : Real.sin (2*θ) ≤ 1 := Real.sin_le_one _
  have h1 := w_mul_sq_le (Work.Spaces.Dth g z θ) (Work.Spaces.w z) (Real.sin (2*θ))
    (Work.Spaces.gam α) (one_le_w_of_pos hz) hs hs1 (by unfold Work.Spaces.gam; linarith)
  have hWt : Work.Spaces.Wt α z θ
      = Work.Spaces.w z / Real.sin (2*θ) ^ (Work.Spaces.gam α / 2) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, Real.rpow_neg hs.le]
    rfl
  have h2 := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 0 (by norm_num) (by norm_num)
  rw [hWt] at h2
  simpa [Work.Spaces.Dth, Work.Spaces.mixed_zero_left] using le_trans h1 h2

lemma slot_Dz (α : ℝ) {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    Work.Spaces.w z * (Work.Spaces.Dz g z θ)^2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs := sin_two_pos hθ
  have hs1 : Real.sin (2*θ) ≤ 1 := Real.sin_le_one _
  have h1 := w_mul_sq_le (Work.Spaces.DzIter 1 g z θ) (Work.Spaces.w z) (Real.sin (2*θ))
    Work.Spaces.eta (one_le_w_of_pos hz) hs hs1 (by norm_num [Work.Spaces.eta])
  have h2 := Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 1 (by norm_num)
  simpa [Work.Spaces.Dz] using le_trans h1 h2

/-! ## The three unweighted slots -/

/-- Common form of the first three conjuncts of `gSlots`: if a nonnegative angular density `r`
satisfies the pointwise slot bound `w(z)·r(z,θ) ≤ HkIntegrand α 4 g z θ` on the open quadrant,
then `∫_z w(z)·∫_θ r ≤ ∫_z ∫_θ HkIntegrand α 4 g`.  Both integrals are compared with
`MeasureTheory.integral_mono_of_nonneg`, which needs only the *majorant* to be integrable; the
pointwise comparison is only needed away from the null angular endpoints. -/
lemma wsSlot_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 g)
    {r : ℝ → ℝ → ℝ} (hrnn : ∀ z θ, 0 ≤ r z θ)
    (hpt : ∀ z, 0 < z → ∀ θ, θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) →
      Work.Spaces.w z * r z θ ≤ Work.Spaces.HkIntegrand α 4 g z θ) :
    ∫ z in Set.Ioi (0:ℝ), Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, r z θ)
      ≤ ∫ z in Set.Ioi (0:ℝ), ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  have h1 : (∫ z in Set.Ioi (0:ℝ), Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, r z θ))
      = ∫ z in Set.Ioi (0:ℝ), ∫ θ in Work.Spaces.Iθ, Work.Spaces.w z * r z θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    rw [← MeasureTheory.integral_const_mul]
  rw [h1]
  refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun z => ?_)
    (hmem.2.mono_set (fun z hz => le_of_lt (Set.mem_Ioi.mp hz))) ?_
  · exact MeasureTheory.integral_nonneg fun θ => mul_nonneg (w_nonneg z) (hrnn z θ)
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ =>
      mul_nonneg (w_nonneg z) (hrnn z θ)) (hmem.1 z (le_of_lt (Set.mem_Ioi.mp hz))) ?_
    rw [restrict_Iθ_eq_Ioo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => hpt z (Set.mem_Ioi.mp hz) θ hθ)

/-! ## The radial weight `z ↦ z/(1+z)² = 1/(z·w(z))` and its integrals -/

lemma integrableOn_one_div_one_add_sq : IntegrableOn (fun z : ℝ => 1/(1+z)^2) (Set.Ioi 0) := by
  have h := integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := 0) (m := 1)
    (by norm_num) (by norm_num : (-1:ℝ) < 0)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx1 : (0:ℝ) < x + 1 := by linarith [Set.mem_Ioi.mp hx]
  simp only []
  rw [Real.rpow_neg hx1.le, Real.rpow_two, one_div]
  ring_nf

lemma integral_one_div_one_add_sq : ∫ z in Set.Ioi (0:ℝ), 1/(1+z)^2 = 1 := by
  have hint : IntegrableOn (fun x : ℝ => ((1+x)^2)⁻¹) (Set.Ioi 0) :=
    integrableOn_one_div_one_add_sq.congr_fun (fun x _ => by simp only []; rw [one_div])
      measurableSet_Ioi
  have hderiv : ∀ x ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun z : ℝ => -((1+z)⁻¹)) (((1+x)^2)⁻¹) x := by
    intro x hx
    have hx1 : (0:ℝ) < 1 + x := by linarith [Set.mem_Ici.mp hx]
    have h2 := ((hasDerivAt_id x).const_add (1:ℝ)).inv (by simpa using hx1.ne')
    have h3 : HasDerivAt (fun z : ℝ => -((1+z)⁻¹)) (-(-1/(1+x)^2)) x := h2.neg
    convert h3 using 1
    ring
  have hlim : Tendsto (fun z : ℝ => -((1+z)⁻¹)) atTop (𝓝 0) := by
    have h : Tendsto (fun z : ℝ => (1+z)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop (1:ℝ) tendsto_id)
    simpa using h.neg
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  simp only [show ((1:ℝ)+0)⁻¹ = 1 by norm_num, zero_sub, neg_neg] at hval
  have hcongr : ∫ z in Set.Ioi (0:ℝ), 1/(1+z)^2
      = ∫ z in Set.Ioi (0:ℝ), ((1+z)^2)⁻¹ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => by
      show 1/(1+z)^2 = ((1+z)^2)⁻¹; rw [one_div])
  rw [hcongr, hval]

/-- `z ↦ z/(1+z)²` is dominated by `z ↦ 1/(1+z)²` on `(0,∞)`. -/
lemma G_bound {z : ℝ} (hz : 0 < z) : (z/(1+z)^2)^2 ≤ 1/(1+z)^2 := by
  have hz2 : (0:ℝ) < (1+z)^2 := by positivity
  have hkey : z^2 ≤ (1+z)^2 := by
    have h : (1+z)^2 = z^2 + (1 + 2*z) := by ring
    linarith
  rw [div_pow, div_le_div_iff₀ (by positivity : (0:ℝ) < ((1+z)^2)^2) hz2]
  nlinarith [mul_le_mul_of_nonneg_right hkey (show (0:ℝ) ≤ (1+z)^2 by positivity)]

lemma integrableOn_G_sq : IntegrableOn (fun z : ℝ => (z/(1+z)^2)^2) (Set.Ioi 0) := by
  refine Integrable.mono' integrableOn_one_div_one_add_sq ?_ ?_
  · have hden : ContinuousOn (fun z : ℝ => (1+z)^2) (Set.Ioi 0) :=
      ((continuous_const.add continuous_id).pow 2).continuousOn
    have hcont : ContinuousOn (fun z : ℝ => z/(1+z)^2) (Set.Ioi 0) :=
      ContinuousOn.div continuousOn_id hden (fun z hz => by
        have h1 : (0:ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
        positivity)
    exact (hcont.pow 2).aestronglyMeasurable measurableSet_Ioi
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact G_bound (Set.mem_Ioi.mp hz)

lemma integral_G_sq_le_one : ∫ z in Set.Ioi (0:ℝ), (z/(1+z)^2)^2 ≤ 1 := by
  have h := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => sq_nonneg (z/(1+z)^2)) integrableOn_one_div_one_add_sq
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => G_bound (Set.mem_Ioi.mp hz)))
  rwa [integral_one_div_one_add_sq] at h

/-- **The radial `1/z` Cauchy–Schwarz step.**

If `A z ≤ c·√(E z)` and `w(z)²·E z ≤ H z` for `z > 0`, with `H ≥ 0` and integrable on `(0,∞)`,
then `∫_0^∞ z⁻¹ A z ≤ c·√(∫_0^∞ H z)`.

The proof is the Cauchy–Schwarz inequality for the two `L²`-functions
`z ↦ √(H z)` and `z ↦ z/(1+z)² = 1/(z·w(z))`:
`z⁻¹ √(E z) = (z/(1+z)²)·(w z · √(E z)) ≤ (z/(1+z)²)·√(H z)` because `w z·√(E z) = √(w z²·E z)`,
and `∫_0^∞ (z/(1+z)²)² = 1/3 ≤ 1`.  Only the majorant has to be integrable (the AM–GM
inequality `|F·G| ≤ (F²+G²)/2` gives that), so no measurability of `A` is required. -/
lemma z_inv_integral_le_sqrt {A E H : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hnnA : ∀ z, 0 < z → 0 ≤ A z)
    (hA : ∀ z, 0 < z → A z ≤ c * Real.sqrt (E z))
    (hcomp : ∀ z, 0 < z → (Work.Spaces.w z) ^ 2 * E z ≤ H z)
    (hH : IntegrableOn H (Set.Ioi (0 : ℝ)))
    (hHnn : ∀ z, 0 < z → 0 ≤ H z) :
    ∫ z in Set.Ioi (0 : ℝ), z⁻¹ * A z ≤ c * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), H z) := by
  have hGcont : ContinuousOn (fun z : ℝ => z/(1+z)^2) (Set.Ioi 0) := by
    refine ContinuousOn.div continuousOn_id ?_ ?_
    · exact ((continuous_const.add continuous_id).pow 2).continuousOn
    · intro z hz
      have h1 : (0:ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
      positivity
  have hGsm : AEStronglyMeasurable (fun z : ℝ => z/(1+z)^2) (volume.restrict (Set.Ioi 0)) :=
    hGcont.aestronglyMeasurable measurableSet_Ioi
  have hGae : AEMeasurable (fun z : ℝ => z/(1+z)^2) (volume.restrict (Set.Ioi 0)) :=
    hGsm.aemeasurable
  have hFsm : AEStronglyMeasurable (fun z : ℝ => Real.sqrt (H z))
      (volume.restrict (Set.Ioi 0)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hH.aestronglyMeasurable
  have hFae : AEMeasurable (fun z : ℝ => Real.sqrt (H z)) (volume.restrict (Set.Ioi 0)) :=
    hFsm.aemeasurable
  have hF2eq : (fun z : ℝ => (Real.sqrt (H z))^2) =ᵐ[volume.restrict (Set.Ioi 0)] H :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => Real.sq_sqrt (hHnn z (Set.mem_Ioi.mp hz)))
  have hF2int : Integrable (fun z => (Real.sqrt (H z))^2) (volume.restrict (Set.Ioi 0)) :=
    hH.congr hF2eq.symm
  have hFGint : Integrable (fun z => Real.sqrt (H z) * (z/(1+z)^2))
      (volume.restrict (Set.Ioi 0)) := by
    refine Integrable.mono'
      (g := fun z => ((Real.sqrt (H z))^2 + (z/(1+z)^2)^2) / 2)
      ?_ (hFsm.mul hGsm) ?_
    · simpa [div_eq_mul_inv] using (hF2int.add integrableOn_G_sq).mul_const ((1:ℝ)/2)
    · refine Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have h := two_mul_le_add_sq |Real.sqrt (H z)| |z/(1+z)^2|
      rw [sq_abs, sq_abs] at h
      linarith
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict (Set.Ioi 0)) hFsm hGsm
    hF2int integrableOn_G_sq
  have hG2sqrt : Real.sqrt (∫ z in Set.Ioi 0, (z/(1+z)^2)^2) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact integral_G_sq_le_one
  have hF2val : ∫ z in Set.Ioi 0, (Real.sqrt (H z))^2 = ∫ z in Set.Ioi 0, H z :=
    MeasureTheory.integral_congr_ae hF2eq
  have habs : ∫ z in Set.Ioi 0, Real.sqrt (H z) * (z/(1+z)^2)
      ≤ Real.sqrt (∫ z in Set.Ioi 0, H z) := by
    have hnn : 0 ≤ ∫ z in Set.Ioi 0, Real.sqrt (H z) * (z/(1+z)^2) :=
      MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz =>
          mul_nonneg (Real.sqrt_nonneg _)
            (div_nonneg (le_of_lt (Set.mem_Ioi.mp hz)) (by positivity))))
    calc ∫ z in Set.Ioi 0, Real.sqrt (H z) * (z/(1+z)^2)
        ≤ |∫ z in Set.Ioi 0, Real.sqrt (H z) * (z/(1+z)^2)| := le_abs_self _
      _ ≤ Real.sqrt (∫ z in Set.Ioi 0, (Real.sqrt (H z))^2)
            * Real.sqrt (∫ z in Set.Ioi 0, (z/(1+z)^2)^2) := hcs
      _ = Real.sqrt (∫ z in Set.Ioi 0, H z)
            * Real.sqrt (∫ z in Set.Ioi 0, (z/(1+z)^2)^2) := by rw [hF2val]
      _ ≤ Real.sqrt (∫ z in Set.Ioi 0, H z) * 1 :=
            mul_le_mul_of_nonneg_left hG2sqrt (Real.sqrt_nonneg _)
      _ = Real.sqrt (∫ z in Set.Ioi 0, H z) := mul_one _
  have hmono : ∫ z in Set.Ioi 0, z⁻¹ * A z
      ≤ ∫ z in Set.Ioi 0, c * (Real.sqrt (H z) * (z/(1+z)^2)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt (Set.mem_Ioi.mp hz)))
        (hnnA z (Set.mem_Ioi.mp hz))
    · exact hFGint.const_mul c
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
      have hz0 : (0:ℝ) < z := Set.mem_Ioi.mp hz
      have hw : 0 < Work.Spaces.w z := w_pos_of_pos hz0
      have hzw : z⁻¹ = Work.Spaces.w z * (z/(1+z)^2) := by
        rw [Work.Spaces.w, inv_eq_one_div]
        field_simp
      have hwx : Work.Spaces.w z * Real.sqrt (E z) ≤ Real.sqrt (H z) := by
        have h1 : Real.sqrt ((Work.Spaces.w z)^2 * E z)
            = Work.Spaces.w z * Real.sqrt (E z) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hw)]
        rw [← h1]
        exact Real.sqrt_le_sqrt (hcomp z hz0)
      calc z⁻¹ * A z ≤ z⁻¹ * (c * Real.sqrt (E z)) :=
            mul_le_mul_of_nonneg_left (hA z hz0) (inv_nonneg.mpr (le_of_lt hz0))
        _ = c * (z⁻¹ * Real.sqrt (E z)) := by ring
        _ = c * ((z/(1+z)^2) * (Work.Spaces.w z * Real.sqrt (E z))) := by rw [hzw]; ring
        _ ≤ c * ((z/(1+z)^2) * Real.sqrt (H z)) := by
            refine mul_le_mul_of_nonneg_left ?_ hc
            exact mul_le_mul_of_nonneg_left hwx (by positivity)
        _ = c * (Real.sqrt (H z) * (z/(1+z)^2)) := by ring
  calc ∫ z in Set.Ioi 0, z⁻¹ * A z
      ≤ ∫ z in Set.Ioi 0, c * (Real.sqrt (H z) * (z/(1+z)^2)) := hmono
    _ = c * ∫ z in Set.Ioi 0, Real.sqrt (H z) * (z/(1+z)^2) := MeasureTheory.integral_const_mul c _
    _ ≤ c * Real.sqrt (∫ z in Set.Ioi 0, H z) := mul_le_mul_of_nonneg_left habs hc

/-! ## The weighted angular slots and the angular Cauchy–Schwarz estimates -/

/-- `w₀²·x² ≤ (x·(w₀/s^{p/2}))²` for `w₀ > 0`, `0 < s ≤ 1`, `p ≥ 0`: stripping the weight
`w₀` costs only the integrable factor `s^{-p}`. -/
lemma wsq_mul_sq_le (x w0 s p : ℝ) (hw : 0 < w0) (hs : 0 < s) (hs1 : s ≤ 1) (hp : 0 ≤ p) :
    w0 ^ 2 * x ^ 2 ≤ (x * (w0 / s ^ (p / 2))) ^ 2 := by
  have hsp : 0 < s ^ (p/2) := Real.rpow_pos_of_pos hs _
  have hsp1 : s ^ (p/2) ≤ 1 := Real.rpow_le_one hs.le hs1 (by linarith)
  have hsp2 : (s ^ (p/2)) ^ 2 ≤ 1 := by
    have h2 : (s^(p/2)) * (s^(p/2)) ≤ 1 * 1 := mul_self_le_mul_self hsp.le hsp1
    linarith
  have hcoef : w0 ^ 2 ≤ (w0 / s ^ (p/2)) ^ 2 := by
    rw [div_pow]
    have hsp2pos : 0 < (s^(p/2))^2 := pow_pos hsp 2
    calc w0 ^ 2 = w0 ^ 2 / 1 := by ring
      _ ≤ w0 ^ 2 / (s ^ (p/2)) ^ 2 := div_le_div_of_nonneg_left (sq_nonneg w0) hsp2pos hsp2
  calc w0^2 * x^2 ≤ (w0 / s^(p/2))^2 * x^2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg x)
    _ = (x * (w0 / s^(p/2)))^2 := by ring

/-- The mixed weight squared: `Wt² = w²·sin(2θ)^{-γ}`. -/
lemma Wt_sq (α : ℝ) {z θ : ℝ} (hs : 0 ≤ Real.sin (2*θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * Real.sin (2*θ) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  congr 1
  rw [← Real.rpow_two, ← Real.rpow_mul hs]
  congr 1
  ring

/-- `w(z)²·g² ≤ HkIntegrand α 4 g`: the `D_z⁰`-slot dominates the `w²`-weighted square. -/
lemma w2_sq_le_HkIntegrand (α : ℝ) {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    (Work.Spaces.w z)^2 * (g z θ)^2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs := sin_two_pos hθ
  have hs1 : Real.sin (2*θ) ≤ 1 := Real.sin_le_one _
  have h1 := wsq_mul_sq_le (g z θ) (Work.Spaces.w z) (Real.sin (2*θ)) Work.Spaces.eta
    (w_pos_of_pos hz) hs hs1 (by norm_num [Work.Spaces.eta])
  exact le_trans h1 (Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 0 (by norm_num))

/-- `w(z)²·(D_θ g)²·sin(2θ)^{-γ} ≤ HkIntegrand α 4 g`: the mixed `(i,j) = (1,0)`-slot. -/
lemma w2_Dth_sq_le_HkIntegrand (α : ℝ) (hα : 0 < α) {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    (Work.Spaces.w z)^2
        * ((Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α)))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs := sin_two_pos hθ
  have hWt2 := Wt_sq α (z := z) (θ := θ) hs.le
  have h2 : ((Work.Spaces.Dth g z θ) * Work.Spaces.Wt α z θ)^2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    simpa using Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 0 (by norm_num) (by norm_num)
  have heq : ((Work.Spaces.Dth g z θ) * Work.Spaces.Wt α z θ)^2
      = (Work.Spaces.w z)^2
        * ((Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α))) := by
    rw [mul_pow, hWt2]; ring
  rwa [heq] at h2

/-- `(D_θ g)²·sin(2θ)^{-γ} ≤ HkIntegrand α 4 g`: the same slot without the `w²`. -/
lemma Dth_sq_le_HkIntegrand (α : ℝ) (hα : 0 < α) {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    (Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs := sin_two_pos hθ
  have hWt2 := Wt_sq α (z := z) (θ := θ) hs.le
  have h2 : ((Work.Spaces.Dth g z θ) * Work.Spaces.Wt α z θ)^2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    simpa using Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 0 (by norm_num) (by norm_num)
  have heq : ((Work.Spaces.Dth g z θ) * Work.Spaces.Wt α z θ)^2
      = (Work.Spaces.w z)^2
        * ((Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α))) := by
    rw [mul_pow, hWt2]; ring
  rw [heq] at h2
  have hw2 : 1 ≤ (Work.Spaces.w z)^2 := by
    nlinarith [one_le_w_of_pos hz, w_nonneg z]
  have hx : 0 ≤ (Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
  calc (Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α))
      = 1 * ((Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α))) :=
        (one_mul _).symm
    _ ≤ (Work.Spaces.w z)^2
          * ((Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_right hw2 hx
    _ ≤ Work.Spaces.HkIntegrand α 4 g z θ := h2

lemma wsq_mul_slice_le (α : ℝ) (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z →
      (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hmem.1 z (le_of_lt hz)) ?_
  rw [restrict_Iθ_eq_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => w2_sq_le_HkIntegrand α hz hθ)

lemma wsq_mul_slice_Dth_le (α : ℝ) (hα : 0 < α) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z →
      (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z hz
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z (le_of_lt hz)) ?_
  · rw [restrict_Iθ_eq_Ioo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos hθ)) _)))
  · rw [restrict_Iθ_eq_Ioo]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => w2_Dth_sq_le_HkIntegrand α hα hz hθ)

/-- `D_θ g = sin(2θ)·∂_θ g` and `sin(2θ) > 0` on the open interval. -/
lemma abs_Dth_eq {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    |Work.Spaces.Dth g z θ| = Real.sin (2*θ) * |Work.Spaces.pth g z θ| := by
  rw [Work.Spaces.Dth, abs_mul, abs_of_pos (sin_two_pos hθ)]

/-- The `θ`-slice of `D_θ g` is continuous on the open interval. -/
lemma continuousOn_Dth_slice {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ => Work.Spaces.Dth g z θ) (Set.Ioo (0:ℝ) (Real.pi/2)) := by
  have hcd := Work.FTS.LocData.contDiffOn_slice_θ
    (Work.FTS.LocData.contDiffOn_DthIter (isOpen_Ioi.prod isOpen_Ioo) hsm 1)
    (show z ∈ Set.Ioi (-1) by simp only [Set.mem_Ioi]; linarith)
  have hcont : ContinuousOn (fun θ => Work.Spaces.DthIter 1 g z θ) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    ContDiffOn.continuousOn hcd
  simpa using hcont

/-- Angular Cauchy–Schwarz for `D_θ g`. -/
lemma slice_Dth_abs_le_sqrt (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth g z θ|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.gam α)) := by
  intro z hz
  have hm : ∀ f : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in Set.Ioo 0 (Real.pi/2), f θ :=
    fun f => by rw [restrict_Iθ_eq_Ioo]
  rw [hm (fun θ => |Work.Spaces.Dth g z θ|),
    hm (fun θ => (Work.Spaces.Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))),
    hm (fun θ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α))]
  set u : ℝ → ℝ := fun θ =>
    |Work.Spaces.Dth g z θ| * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)/2) with hu
  set v : ℝ → ℝ := fun θ => (Real.sin (2*θ)) ^ ((Work.Spaces.gam α)/2) with hv
  have hsin_c : ContinuousOn (fun θ : ℝ => Real.sin (2*θ)) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hDth_c := continuousOn_Dth_slice hsm hz
  have hcontU : ContinuousOn u (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    hDth_c.abs.mul (hsin_c.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ))))
  have hcontV : ContinuousOn v (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    hsin_c.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))
  have huv : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), u θ * v θ = |Work.Spaces.Dth g z θ| := by
    intro θ hθ
    have hs := sin_two_pos hθ
    have h1 : (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)/2) * (Real.sin (2*θ)) ^ ((Work.Spaces.gam α)/2)
        = 1 := by
      rw [← Real.rpow_add hs, show -(Work.Spaces.gam α)/2 + Work.Spaces.gam α/2 = 0 by ring,
        Real.rpow_zero]
    rw [hu, hv]
    show (|Work.Spaces.Dth g z θ| * _) * _ = _
    rw [mul_assoc, h1, mul_one]
  have hu2 : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      (u θ)^2 = (Work.Spaces.Dth g z θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) := by
    intro θ hθ
    have hs := sin_two_pos hθ
    rw [hu]
    have h2 : ((Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)/2))^2
        = (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hs.le]
      congr 1
      ring
    rw [mul_pow, sq_abs, h2]
  have hv2 : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      (v θ)^2 = (Real.sin (2*θ)) ^ (Work.Spaces.gam α) := by
    intro θ hθ
    have hs := sin_two_pos hθ
    rw [hv]
    rw [← Real.rpow_two, ← Real.rpow_mul hs.le]
    congr 1
    ring
  have hU2 : Integrable (fun θ => (u θ)^2) (volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))) := by
    have hHm : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
        (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      (hmem.1 z (le_of_lt hz)).mono_set (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    refine Integrable.mono' hHm ((hcontU.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hu2 θ hθ]
    exact Dth_sq_le_HkIntegrand α hα hz hθ
  have hV2 : Integrable (fun θ => (v θ)^2) (volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))) := by
    have hconst : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))) :=
      MeasureTheory.integrableOn_const (μ := volume) (s := Set.Ioo (0:ℝ) (Real.pi/2))
        (C := (1:ℝ)) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    refine Integrable.mono' hconst ((hcontV.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hv2 θ hθ]
    exact Real.rpow_le_one (le_of_lt (sin_two_pos hθ)) (Real.sin_le_one _)
      (by unfold Work.Spaces.gam; linarith)
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2)))
    (hcontU.aestronglyMeasurable measurableSet_Ioo)
    (hcontV.aestronglyMeasurable measurableSet_Ioo) hU2 hV2
  have hcongr : ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), |Work.Spaces.Dth g z θ|
      = ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), u θ * v θ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => (huv θ hθ).symm)
  have hu2eq : ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (u θ)^2
      = ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2),
          (Work.Spaces.Dth g z θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => hu2 θ hθ)
  have hv2eq : ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (v θ)^2
      = ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (Real.sin (2*θ)) ^ (Work.Spaces.gam α) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => hv2 θ hθ)
  rw [hcongr]
  calc ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), u θ * v θ
      ≤ |∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), u θ * v θ| := le_abs_self _
    _ ≤ Real.sqrt (∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (u θ)^2)
          * Real.sqrt (∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (v θ)^2) := hcs
    _ = Real.sqrt (∫ θ in Set.Ioo (0:ℝ) (Real.pi/2),
            (Work.Spaces.Dth g z θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)))
          * Real.sqrt (∫ θ in Set.Ioo (0:ℝ) (Real.pi/2),
            (Real.sin (2*θ)) ^ (Work.Spaces.gam α)) := by rw [hu2eq, hv2eq]

/-- Angular Cauchy–Schwarz for `∂_θ g`. -/
lemma slice_pth_abs_le_sqrt (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → ∫ θ in Work.Spaces.Iθ, |Work.Spaces.pth g z θ|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) := by
  intro z hz
  have hm : ∀ f : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, f θ) = ∫ θ in Set.Ioo 0 (Real.pi/2), f θ :=
    fun f => by rw [restrict_Iθ_eq_Ioo]
  rw [hm (fun θ => |Work.Spaces.pth g z θ|),
    hm (fun θ => (Work.Spaces.Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))),
    hm (fun θ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2))]
  set u : ℝ → ℝ := fun θ =>
    |Work.Spaces.Dth g z θ| * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)/2) with hu
  set v : ℝ → ℝ := fun θ => (Real.sin (2*θ)) ^ ((Work.Spaces.gam α)/2 - 1) with hv
  have hsin_c : ContinuousOn (fun θ : ℝ => Real.sin (2*θ)) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hDth_c := continuousOn_Dth_slice hsm hz
  have hcontU : ContinuousOn u (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    hDth_c.abs.mul (hsin_c.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ))))
  have hcontV : ContinuousOn v (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    hsin_c.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))
  have huv : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), u θ * v θ = |Work.Spaces.pth g z θ| := by
    intro θ hθ
    have hs := sin_two_pos hθ
    have h1 : (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)/2) * (Real.sin (2*θ)) ^ ((Work.Spaces.gam α)/2 - 1)
        = (Real.sin (2*θ)) ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hs]
      congr 1
      ring
    rw [hu, hv, mul_assoc, h1, abs_Dth_eq hθ, Real.rpow_neg_one]
    rw [mul_comm (Real.sin (2*θ)) (|Work.Spaces.pth g z θ|), mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hs), mul_one]
  have hu2 : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      (u θ)^2 = (Work.Spaces.Dth g z θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) := by
    intro θ hθ
    have hs := sin_two_pos hθ
    rw [hu]
    have h2 : ((Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)/2))^2
        = (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hs.le]
      congr 1
      ring
    rw [mul_pow, sq_abs, h2]
  have hv2 : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      (v θ)^2 = (Real.sin (2*θ)) ^ (Work.Spaces.gam α - 2) := by
    intro θ hθ
    have hs := sin_two_pos hθ
    rw [hv]
    rw [← Real.rpow_two, ← Real.rpow_mul hs.le]
    congr 1
    ring
  have hU2 : Integrable (fun θ => (u θ)^2) (volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))) := by
    have hHm : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
        (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      (hmem.1 z (le_of_lt hz)).mono_set (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    refine Integrable.mono' hHm ((hcontU.pow 2).aestronglyMeasurable measurableSet_Ioo) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hu2 θ hθ]
    exact Dth_sq_le_HkIntegrand α hα hz hθ
  have hV2 : Integrable (fun θ => (v θ)^2) (volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2))) := by
    have hgamgt : -1 < Work.Spaces.gam α - 2 := by unfold Work.Spaces.gam; linarith
    have hgamle : Work.Spaces.gam α - 2 ≤ 0 := by unfold Work.Spaces.gam; linarith
    have hS : IntegrableOn (fun θ => (Real.sin (2*θ)) ^ (Work.Spaces.gam α - 2))
        (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      ((Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2) hgamgt hgamle).1).mono_set
        (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    refine hS.congr ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => (hv2 θ hθ).symm)
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2)))
    (hcontU.aestronglyMeasurable measurableSet_Ioo)
    (hcontV.aestronglyMeasurable measurableSet_Ioo) hU2 hV2
  have hcongr : ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), |Work.Spaces.pth g z θ|
      = ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), u θ * v θ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => (huv θ hθ).symm)
  have hu2eq : ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (u θ)^2
      = ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2),
          (Work.Spaces.Dth g z θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => hu2 θ hθ)
  have hv2eq : ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (v θ)^2
      = ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (Real.sin (2*θ)) ^ (Work.Spaces.gam α - 2) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => hv2 θ hθ)
  rw [hcongr]
  calc ∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), u θ * v θ
      ≤ |∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), u θ * v θ| := le_abs_self _
    _ ≤ Real.sqrt (∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (u θ)^2)
          * Real.sqrt (∫ θ in Set.Ioo (0:ℝ) (Real.pi/2), (v θ)^2) := hcs
    _ = Real.sqrt (∫ θ in Set.Ioo (0:ℝ) (Real.pi/2),
            (Work.Spaces.Dth g z θ)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α)))
          * Real.sqrt (∫ θ in Set.Ioo (0:ℝ) (Real.pi/2),
            (Real.sin (2*θ)) ^ (Work.Spaces.gam α - 2)) := by rw [hu2eq, hv2eq]

/-- The angular volume: `∫_θ 1 = π/2`. -/
lemma setIntegral_one_Icc : ∫ θ in Set.Icc (0:ℝ) (Real.pi/2), (1:ℝ) = Real.pi/2 := by
  rw [MeasureTheory.setIntegral_const]
  rw [smul_eq_mul, mul_one, MeasureTheory.measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

lemma setIntegral_one_Iθ : ∫ θ in Work.Spaces.Iθ, (1:ℝ) = Real.pi/2 := setIntegral_one_Icc

theorem gSlots {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hreg : Work.FTS.Nonlin.RegQ α 4 g) :
    (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 g) ∧
    (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g z θ) ^ 2) ≤ Work.Spaces.HkSq α 4 g) ∧
    (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz g z θ) ^ 2) ≤ Work.Spaces.HkSq α 4 g) ∧
    (∫ z in Set.Ioi (0 : ℝ), z⁻¹
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) ≤ 20 * Work.FTS.Nonlin.Xn α g) ∧
    (∫ z in Set.Ioi (0 : ℝ), z⁻¹
        * (∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth g z θ|) ≤ 20 * Work.FTS.Nonlin.Xn α g) ∧
    (∫ z in Set.Ioi (0 : ℝ), z⁻¹
        * (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pth g z θ|)
        ≤ 300 * Real.sqrt (10 / α) * Work.FTS.Nonlin.Xn α g) := by
  have hmem := hreg.2.1
  have hsm := hreg.1
  have hHnn : ∀ z, 0 < z → 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ :=
    fun z hz => MeasureTheory.integral_nonneg fun θ => by
      rw [Work.Spaces.HkIntegrand]
      exact add_nonneg (Work.Spaces.hkZSum_nonneg α 4 g z θ)
        (Work.Spaces.hkMixedSum_nonneg α 4 g z θ)
  have hHint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
      (Set.Ioi (0:ℝ)) := hmem.2.mono_set (fun z hz => le_of_lt (Set.mem_Ioi.mp hz))
  -- the two weighted angular densities of the last three conjuncts
  have hc4 : Real.sqrt (∫ θ in Work.Spaces.Iθ, Real.sin (2*θ)^(Work.Spaces.gam α)) ≤ 20 := by
    have hle1 : ∀ θ ∈ Work.Spaces.Iθ, Real.sin (2*θ)^(Work.Spaces.gam α) ≤ 1 := by
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (0:ℝ) (Real.pi/2) := hθ
      exact Real.rpow_le_one
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ'.1])
          (by linarith [hθ'.2, Real.pi_pos])) (Real.sin_le_one _)
        (by unfold Work.Spaces.gam; linarith)
    have hint : ∫ θ in Work.Spaces.Iθ, Real.sin (2*θ)^(Work.Spaces.gam α) ≤ Real.pi/2 := by
      have h := MeasureTheory.integral_mono_of_nonneg
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
          Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos])) _))
        (MeasureTheory.integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (1:ℝ))
          (by rw [show Work.Spaces.Iθ = Set.Icc (0:ℝ) (Real.pi/2) from rfl, Real.volume_Icc];
              exact ENNReal.ofReal_ne_top))
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hle1)
      rwa [setIntegral_one_Icc] at h
    have h0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Real.sin (2*θ)^(Work.Spaces.gam α) :=
      MeasureTheory.integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])) _))
    nlinarith [Real.sq_sqrt h0, hint, Real.pi_le_four, Real.pi_pos,
      Real.sqrt_nonneg (∫ θ in Work.Spaces.Iθ, Real.sin (2*θ)^(Work.Spaces.gam α))]
  have hc6 : Real.sqrt (∫ θ in Work.Spaces.Iθ, Real.sin (2*θ)^(Work.Spaces.gam α - 2))
      ≤ 300 * Real.sqrt (10/α) := by
    have hgamgt : -1 < Work.Spaces.gam α - 2 := by unfold Work.Spaces.gam; linarith
    have hgamle : Work.Spaces.gam α - 2 ≤ 0 := by unfold Work.Spaces.gam; linarith
    have hK1 : ∫ θ in Work.Spaces.Iθ, Real.sin (2*θ)^(Work.Spaces.gam α - 2)
        ≤ 100 * (10/α) := by
      have h := (Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2) hgamgt hgamle).2
      have hE : (100:ℝ) / (Work.Spaces.gam α - 2 + 1) = 100 * (10/α) := by
        rw [show Work.Spaces.gam α - 2 + 1 = Work.Spaces.gam α - 1 by ring,
          Work.Spaces.gam_sub_one α]
        field_simp
      rwa [hE] at h
    have h2 : Real.sqrt (100 * (10/α)) = 10 * Real.sqrt (10/α) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 100),
        show Real.sqrt (100:ℝ) = 10 from by
          rw [show (100:ℝ) = 10^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have h3 := Real.sqrt_le_sqrt hK1
    rw [h2] at h3
    nlinarith [h3, Real.sqrt_nonneg (10/α)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [HkSq_eq_integral_Ioi]
    exact wsSlot_le hmem (r := fun z θ => (g z θ)^2) (fun z θ => sq_nonneg _)
      (fun z hz θ hθ => slot_g α hz hθ)
  · rw [HkSq_eq_integral_Ioi]
    exact wsSlot_le hmem (r := fun z θ => (Work.Spaces.Dth g z θ)^2) (fun z θ => sq_nonneg _)
      (fun z hz θ hθ => slot_Dth α hα hz hθ)
  · rw [HkSq_eq_integral_Ioi]
    exact wsSlot_le hmem (r := fun z θ => (Work.Spaces.Dz g z θ)^2) (fun z θ => sq_nonneg _)
      (fun z hz θ hθ => slot_Dz α hz hθ)
  · have hmain := z_inv_integral_le_sqrt
        (A := fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ)^2))
        (E := fun z => ∫ θ in Work.Spaces.Iθ, (g z θ)^2)
        (H := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        (c := 1) (by norm_num) (fun z hz => Real.sqrt_nonneg _)
        (fun z hz => by rw [one_mul])
        (fun z hz => wsq_mul_slice_le α hα hsm hmem z hz) hHint hHnn
    refine le_trans hmain ?_
    rw [one_mul, ← HkSq_eq_integral_Ioi α g]
    simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
    nlinarith [Real.sqrt_nonneg (Work.Spaces.HkSq α 4 g)]
  · have hmain := z_inv_integral_le_sqrt
        (A := fun z => ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dth g z θ|)
        (E := fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α)))
        (H := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        (c := Real.sqrt (∫ θ in Work.Spaces.Iθ, Real.sin (2*θ)^(Work.Spaces.gam α)))
        (Real.sqrt_nonneg _)
        (fun z hz => MeasureTheory.integral_nonneg fun θ => abs_nonneg _)
        (fun z hz => (slice_Dth_abs_le_sqrt α hα hα1 hsm hmem z hz).trans
          (le_of_eq (mul_comm _ _)))
        (fun z hz => wsq_mul_slice_Dth_le α hα hsm hmem z hz) hHint hHnn
    have hX : Real.sqrt (∫ z in Set.Ioi (0:ℝ),
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) = Work.FTS.Nonlin.Xn α g := by
      rw [← HkSq_eq_integral_Ioi α g]
      simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
    rw [hX] at hmain
    refine le_trans hmain ?_
    exact mul_le_mul_of_nonneg_right hc4 (Work.Spaces.HkNorm_nonneg α 4 g)
  · have hmain := z_inv_integral_le_sqrt
        (A := fun z => ∫ θ in Work.Spaces.Iθ, |Work.Spaces.pth g z θ|)
        (E := fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dth g z θ)^2 * Real.sin (2*θ)^(-(Work.Spaces.gam α)))
        (H := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
        (c := Real.sqrt (∫ θ in Work.Spaces.Iθ, Real.sin (2*θ)^(Work.Spaces.gam α - 2)))
        (Real.sqrt_nonneg _)
        (fun z hz => MeasureTheory.integral_nonneg fun θ => abs_nonneg _)
        (fun z hz => (slice_pth_abs_le_sqrt α hα hα1 hsm hmem z hz).trans
          (le_of_eq (mul_comm _ _)))
        (fun z hz => wsq_mul_slice_Dth_le α hα hsm hmem z hz) hHint hHnn
    have hX : Real.sqrt (∫ z in Set.Ioi (0:ℝ),
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) = Work.FTS.Nonlin.Xn α g := by
      rw [← HkSq_eq_integral_Ioi α g]
      simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
    rw [hX] at hmain
    refine le_trans hmain ?_
    exact mul_le_mul_of_nonneg_right hc6 (Work.Spaces.HkNorm_nonneg α 4 g)

end Work.FTS.Nonlinear.Pieces.rl1Tools
