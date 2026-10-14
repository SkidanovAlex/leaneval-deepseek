import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 0

/-! ## `SmoothNbhd` implies `SmoothInt` -/


/-! ## The angular weight integral is bounded -/

theorem sin_two_nonneg' {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])


theorem angular_weight_integral_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ θ in Iθ, (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) ≤ 700 := by
  have hp1_2 : (-1 : ℝ) < 2 * α / 5 - gam α := by rw [gam]; linarith
  have hp0_2 : 2 * α / 5 - gam α ≤ 0 := by rw [gam]; nlinarith
  have hne : (2 * α / 5 - gam α) + 1 = 3 * α / 10 := by rw [gam]; ring
  have hvolIθ : (volume.real Iθ) = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def, Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hpt : ∀ θ ∈ Iθ,
      (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
        ≤ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) + 2 := by
    intro θ hθ
    have hs0 := sin_two_nonneg' hθ
    have hs1 := Real.sin_le_one (2 * θ)
    have hpow_nn : 0 ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) := Real.rpow_nonneg hs0 _
    have hsplit : (α + Real.sin (2 * θ)) ^ 2
        ≤ 2 * α ^ 2 + 2 * (Real.sin (2 * θ)) ^ 2 := by
      nlinarith [sq_nonneg (α - Real.sin (2 * θ))]
    have hs2le : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by nlinarith [hs0, hs1]
    have hprod : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) ≤ 1 := by
      have h2 : (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ ((2:ℝ)) :=
        (Real.rpow_natCast (Real.sin (2 * θ)) 2).symm
      rw [h2, ← Real.rpow_add' hs0 (by rw [gam]; intro h; linarith)]
      exact Real.rpow_le_one hs0 hs1 (by rw [gam]; linarith)
    calc (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
        ≤ (2 * α ^ 2 + 2 * (Real.sin (2 * θ)) ^ 2)
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) :=
          mul_le_mul_of_nonneg_right hsplit hpow_nn
      _ = 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
            + 2 * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) := by ring
      _ ≤ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) + 2 * 1 := by linarith
      _ = 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) + 2 := by ring
  have hInt2 : IntegrableOn (fun θ : ℝ => 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
      + 2) Iθ :=
    ((sin_two_rpow (2 * α / 5 - gam α) hp1_2 hp0_2).1.const_mul (2 * α ^ 2)).add
      (integrableOn_const (s := Iθ) (C := (2:ℝ))
        (by rw [Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  calc ∫ θ in Iθ, (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
      ≤ ∫ θ in Iθ, (2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) + 2) :=
        MeasureTheory.setIntegral_mono_of_nonneg
          (fun θ _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' (by assumption)) _))
          hpt hInt2
    _ = 2 * α ^ 2 * (∫ θ in Iθ, (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) + 2 * (Real.pi / 2) := by
        rw [MeasureTheory.integral_add ((sin_two_rpow (2 * α / 5 - gam α) hp1_2 hp0_2).1.const_mul _)
          (integrableOn_const (by rw [Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)),
          MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const]
        simp only [smul_eq_mul, hvolIθ]
        ring
    _ ≤ 700 := by
        have hb := (sin_two_rpow (2 * α / 5 - gam α) hp1_2 hp0_2).2
        rw [hne] at hb
        have h3 : (0:ℝ) < 3 * α / 10 := by linarith
        have hkey : 2 * α ^ 2 * (100 / (3 * α / 10)) = 2000 * α / 3 := by
          field_simp; ring
        have hαnn : (0:ℝ) ≤ α := le_of_lt hα
        nlinarith [hb, hαnn, hα1, Real.pi_le_four, hkey,
          mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sq_nonneg α)) (sub_nonneg.mpr hb)]





/-! ## Differentiability of the iterated `z`-derivatives and the `D_z`-versus-`∂_z` expansion -/







/-! ## Bounds for the `f`-factors, from the `𝒲^{4,∞}` norm -/

private theorem WlInf_nonneg_prv {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : WlInfMem α 4 f) :
    0 ≤ WlInf α 4 f := by
  rw [WlInf]
  exact add_nonneg (wlZSum_nonneg α 4 f hmem) (wlThSum_nonneg α 4 f hmem)

/-- `|z ^ j ∂_z^j f| ≤ |f|_𝒲` for `j ≤ 4`. -/
theorem zpz_le_WlInf {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : WlInfMem α 4 f)
    {j : ℕ} (hj : j ≤ 4) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |z ^ j * pzIter j f z θ| ≤ WlInf α 4 f := by
  have hz0 : (0:ℝ) ≤ z := hz
  have hz1 : (0:ℝ) < z + 1 := by linarith
  have h := pz_sup_bound α 4 f hmem j hj z θ hz hθ
  have hW := WlInf_nonneg_prv hmem
  rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 j)]
  calc z ^ j * |pzIter j f z θ| ≤ z ^ j * (WlInf α 4 f / (z+1)^j) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hz0 j)
    _ = WlInf α 4 f * (z / (z+1))^j := by rw [div_pow]; ring
    _ ≤ WlInf α 4 f * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hW
        exact pow_le_one₀ (div_nonneg hz0 (by linarith)) (by rw [div_le_one hz1]; linarith)
    _ = WlInf α 4 f := mul_one _

/-- `|z ^ j ∂_z^j (D_θ^a f)| ≤ |f|_𝒲 · sin(2θ)^{α/5}(α+sin 2θ)` for `1 ≤ a`, `j+a ≤ 4`. -/
theorem zpz_Dth_le_WlInf {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (hmem : WlInfMem α 4 f)
    {a : ℕ} (ha : 1 ≤ a) {j : ℕ} (hja : j + a ≤ 4) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |z ^ j * pzIter j (DthIter a f) z θ| ≤
      WlInf α 4 f * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5)) := by
  have hz0 : (0:ℝ) ≤ z := hz
  have hz1 : (0:ℝ) < z + 1 := by linarith
  have h := pz_Dth_sup_bound α hα 4 f hmem a j ha hja z θ hz hθ
  have hW := WlInf_nonneg_prv hmem
  have hnn : 0 ≤ (α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5) :=
    mul_nonneg (by linarith [sin_two_nonneg' hθ]) (Real.rpow_nonneg (sin_two_nonneg' hθ) _)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 j)]
  have hle1 : (z/(z+1))^j ≤ 1 :=
    pow_le_one₀ (div_nonneg hz0 (by linarith)) (by rw [div_le_one hz1]; linarith)
  calc z ^ j * |pzIter j (DthIter a f) z θ|
      ≤ z ^ j * (WlInf α 4 f / (z+1)^j
          * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5))) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hz0 j)
    _ = WlInf α 4 f * ((z/(z+1))^j * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5))) := by
        rw [div_pow]; ring
    _ ≤ WlInf α 4 f * (1 * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle1 hnn) hW
    _ = WlInf α 4 f * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5)) := by ring






/-! ## The `θ`-Hardy step with the `(α+sin 2θ)²` weight -/

theorem angular_weight_pointwise {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Iθ) :
    (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
      ≤ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) + 2 := by
  have hp0_2 : 2 * α / 5 - gam α ≤ 0 := by rw [gam]; nlinarith
  have hs0 := sin_two_nonneg' hθ
  have hs1 := Real.sin_le_one (2 * θ)
  have hpow_nn : 0 ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) := Real.rpow_nonneg hs0 _
  have hsplit : (α + Real.sin (2 * θ)) ^ 2
      ≤ 2 * α ^ 2 + 2 * (Real.sin (2 * θ)) ^ 2 := by
    nlinarith [sq_nonneg (α - Real.sin (2 * θ))]
  have hs2le : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by nlinarith [hs0, hs1]
  have hprod : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) ≤ 1 := by
    rw [show (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ ((2:ℝ)) from
        (Real.rpow_natCast (Real.sin (2 * θ)) 2).symm,
      ← Real.rpow_add' hs0 (by rw [gam]; intro h; linarith)]
    exact Real.rpow_le_one hs0 hs1 (by rw [gam]; linarith)
  calc (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
      ≤ (2 * α ^ 2 + 2 * (Real.sin (2 * θ)) ^ 2)
          * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) :=
        mul_le_mul_of_nonneg_right hsplit hpow_nn
    _ = 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
          + 2 * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) := by ring
    _ ≤ 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) + 2 * 1 := by linarith
    _ = 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) + 2 := by ring

theorem integrableOn_angular_weight {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) Iθ := by
  have hp1_2 : (-1 : ℝ) < 2 * α / 5 - gam α := by rw [gam]; linarith
  have hp0_2 : 2 * α / 5 - gam α ≤ 0 := by rw [gam]; nlinarith
  have hInt2 : IntegrableOn (fun θ : ℝ => 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
      + 2) Iθ :=
    ((sin_two_rpow (2 * α / 5 - gam α) hp1_2 hp0_2).1.const_mul (2 * α ^ 2)).add
      (integrableOn_const (s := Iθ) (C := (2:ℝ))
        (by rw [Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  refine hInt2.mono' ?_ ?_
  · have hm1 : Measurable (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2) := by fun_prop
    have hm2 : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) :=
      (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _
    exact (hm1.mul hm2).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    have hnn : 0 ≤ (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' hθ) _)
    rw [Real.norm_of_nonneg hnn]
    exact angular_weight_pointwise hα hα1 hθ



/-! ## The angular Hardy bound for the `D_z`-iterates of `g` -/

/-- The weighted `L²`-integral of `∂_θ (D_z^d g)` on the angular interval. -/
noncomputable def Btil (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ) (z : ℝ) : ℝ :=
  ∫ σ in Iθ, (pth (DzIter d g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)






/-! ## Pointwise bounds for the two families of summands -/



/-- `binom n k ≤ 16` for `k ≤ n ≤ 4`, hence its square is at most `256`. -/
theorem choose_sq_le_256 (n k : ℕ) (hkn : k ≤ n) (hn : n ≤ 4) :
    (n.choose k : ℝ) ^ 2 ≤ 256 := by
  have h1 : n.choose k ≤ 2 ^ n := by
    have h := Finset.single_le_sum (f := fun j => n.choose j) (fun j _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn))
    rwa [Nat.sum_range_choose] at h
  have h2 : n.choose k ≤ 16 := by
    calc n.choose k ≤ 2 ^ n := h1
      _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hn
      _ = 16 := by norm_num
  have h3 : (n.choose k : ℝ) ≤ 16 := by exact_mod_cast h2
  have h4 : (0:ℝ) ≤ (n.choose k : ℝ) := by positivity
  nlinarith [h3, h4]


/-- `x² ≤ y²` from `|x| ≤ y`. -/
theorem sq_le_sq_of_abs_le {x y : ℝ} (h : |x| ≤ y) : x ^ 2 ≤ y ^ 2 :=
  calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    _ ≤ y ^ 2 := pow_le_pow_left₀ (abs_nonneg x) h 2



/-! ## The majorant and the product rule -/

/-- The pointwise majorant for the product rule. -/
noncomputable def Gmaj (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  HkIntegrand α 4 g z θ + (gam α - 1)⁻¹ * (∑ d ∈ Finset.range 4, Btil α g d z)
    * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) * (w z) ^ 2)







end Work.Spaces
