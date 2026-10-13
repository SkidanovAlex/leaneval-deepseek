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
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.HardyTheta
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.Spaces.aesm_mixed_Wt_sq_prod

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

theorem SmoothInt.of_SmoothNbhd {g : ℝ → ℝ → ℝ} (h : SmoothNbhd g) : SmoothInt g := by
  refine ⟨h.mono ?_, ?_⟩
  · rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    exact ⟨hz, by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  · intro θ hθ
    have hθ' : θ ∈ Set.Ioo (-1) (π / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (-1))
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun z hz => ⟨hz, hθ'⟩
    exact h.comp (contDiffOn_id.prodMk contDiffOn_const) hmap

/-! ## The angular weight integral is bounded -/

theorem sin_two_nonneg' {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private lemma integrableOn_sin_rpow_nonneg {p : ℝ} (hp : 0 ≤ p) :
    IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) ^ p) Iθ := by
  refine Integrable.mono' (integrableOn_const (s := Iθ) (C := (1:ℝ))
    (by rw [Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) ?_ ?_
  · exact ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const p)
      |>.aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    have hs0 := sin_two_nonneg' hθ
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hs0 p)]
    exact Real.rpow_le_one hs0 (Real.sin_le_one _) hp

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

theorem pzIter_differentiableAt_Ioi {h : ℝ → ℝ → ℝ} (j : ℕ)
    (hsmooth : ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => h z θ) (Set.Ioi (-1)))
    {z θ : ℝ} (hz : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Iθ) :
    DifferentiableAt ℝ (fun z' => pzIter j h z' θ) z := by
  have hs : ContDiffAt ℝ ⊤ (fun z' => h z' θ) z :=
    (hsmooth θ hθ).contDiffAt (isOpen_Ioi.mem_nhds hz)
  have hcd : ContDiffAt ℝ ⊤ (iteratedDeriv j (fun z' => h z' θ)) z := by
    induction j with
    | zero => simpa using hs
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.derivWithin (m := ⊤) (by simp)
  have hfun : (fun z' => pzIter j h z' θ) = iteratedDeriv j (fun z' => h z' θ) := by
    funext z'; exact pzIter_eq_iteratedDeriv j h z' θ
  rw [hfun]; exact hcd.differentiableAt (by simp)

theorem pzIter_step (j : ℕ) (h : ℝ → ℝ → ℝ) (t θ : ℝ) :
    deriv (fun s => pzIter j h s θ) t = pzIter (j+1) h t θ := by
  simp only [pzIter_succ, pz]

/-- `deriv (t ↦ t²) x = 2x`. -/
theorem deriv_sq (x : ℝ) : deriv (fun t : ℝ => t ^ 2) x = 2 * x := by
  rw [show (fun t : ℝ => t ^ 2) = (fun t : ℝ => t) ^ 2 from rfl,
    deriv_pow differentiableAt_id, deriv_id'']
  ring

/-- The expansion `D_z^2 = z ∂_z + z² ∂_z²`. -/
theorem DzIter_two_pt {h : ℝ → ℝ → ℝ}
    (hsmooth : ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => h z θ) (Set.Ioi (-1)))
    {z θ : ℝ} (hz : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Iθ) :
    DzIter 2 h z θ = z * pzIter 1 h z θ + z ^ 2 * pzIter 2 h z θ := by
  have hdiff1 : DifferentiableAt ℝ (fun t => pzIter 1 h t θ) z :=
    pzIter_differentiableAt_Ioi 1 hsmooth hz hθ
  have hfun : (fun t => DzIter 1 h t θ) =ᶠ[𝓝 z] fun t => t * pzIter 1 h t θ :=
    Filter.Eventually.of_forall fun t => rfl
  have hpz : pz (DzIter 1 h) z θ = deriv (fun t => t * pzIter 1 h t θ) z := by
    show deriv (fun t => DzIter 1 h t θ) z = _
    exact hfun.deriv_eq
  have hd1 : deriv (fun t => t * pzIter 1 h t θ) z
      = deriv (fun t : ℝ => t) z * pzIter 1 h z θ
        + z * deriv (fun t => pzIter 1 h t θ) z := by
    exact deriv_mul differentiableAt_id hdiff1
  rw [show DzIter 2 h z θ = z * pz (DzIter 1 h) z θ from rfl, hpz, hd1, deriv_id'',
    pzIter_step 1 h z θ]
  ring

/-- The expansion `D_z^3 = z ∂_z + 3 z² ∂_z² + z³ ∂_z³`. -/
theorem DzIter_three_pt {h : ℝ → ℝ → ℝ}
    (hsmooth : ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => h z θ) (Set.Ioi (-1)))
    {z θ : ℝ} (hz : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Iθ) :
    DzIter 3 h z θ = z * pzIter 1 h z θ + 3 * z ^ 2 * pzIter 2 h z θ
      + z ^ 3 * pzIter 3 h z θ := by
  have hdiff1 : DifferentiableAt ℝ (fun t => pzIter 1 h t θ) z :=
    pzIter_differentiableAt_Ioi 1 hsmooth hz hθ
  have hdiff2 : DifferentiableAt ℝ (fun t => pzIter 2 h t θ) z :=
    pzIter_differentiableAt_Ioi 2 hsmooth hz hθ
  have hfun : (fun t => DzIter 2 h t θ) =ᶠ[𝓝 z]
      fun t => t * pzIter 1 h t θ + t ^ 2 * pzIter 2 h t θ := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    exact DzIter_two_pt hsmooth ht hθ
  have hpz : pz (DzIter 2 h) z θ
      = deriv (fun t => t * pzIter 1 h t θ + t ^ 2 * pzIter 2 h t θ) z := by
    show deriv (fun t => DzIter 2 h t θ) z = _
    exact hfun.deriv_eq
  have hd1 : deriv (fun t => t * pzIter 1 h t θ) z
      = deriv (fun t : ℝ => t) z * pzIter 1 h z θ
        + z * deriv (fun t => pzIter 1 h t θ) z := by
    exact deriv_mul differentiableAt_id hdiff1
  have hd2 : deriv (fun t => t ^ 2 * pzIter 2 h t θ) z
      = deriv (fun t : ℝ => t ^ 2) z * pzIter 2 h z θ
        + z ^ 2 * deriv (fun t => pzIter 2 h t θ) z := by
    exact deriv_mul (differentiableAt_id.pow 2) hdiff2
  have hadd : deriv (fun t => t * pzIter 1 h t θ + t ^ 2 * pzIter 2 h t θ) z
      = deriv (fun t => t * pzIter 1 h t θ) z
        + deriv (fun t => t ^ 2 * pzIter 2 h t θ) z := by
    exact deriv_add (differentiableAt_id.mul hdiff1) ((differentiableAt_id.pow 2).mul hdiff2)
  rw [show DzIter 3 h z θ = z * pz (DzIter 2 h) z θ from rfl, hpz, hadd, hd1, hd2,
    deriv_sq, deriv_id'', pzIter_step 1 h z θ, pzIter_step 2 h z θ]
  ring

/-- The expansion `D_z^4 = z ∂_z + 7 z² ∂_z² + 6 z³ ∂_z³ + z⁴ ∂_z⁴`. -/
theorem DzIter_four_pt {h : ℝ → ℝ → ℝ}
    (hsmooth : ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => h z θ) (Set.Ioi (-1)))
    {z θ : ℝ} (hz : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Iθ) :
    DzIter 4 h z θ = z * pzIter 1 h z θ + 7 * z ^ 2 * pzIter 2 h z θ
      + 6 * z ^ 3 * pzIter 3 h z θ + z ^ 4 * pzIter 4 h z θ := by
  have hdiff1 : DifferentiableAt ℝ (fun t => pzIter 1 h t θ) z :=
    pzIter_differentiableAt_Ioi 1 hsmooth hz hθ
  have hdiff2 : DifferentiableAt ℝ (fun t => pzIter 2 h t θ) z :=
    pzIter_differentiableAt_Ioi 2 hsmooth hz hθ
  have hdiff3 : DifferentiableAt ℝ (fun t => pzIter 3 h t θ) z :=
    pzIter_differentiableAt_Ioi 3 hsmooth hz hθ
  have hfun : (fun t => DzIter 3 h t θ) =ᶠ[𝓝 z]
      fun t => t * pzIter 1 h t θ + 3 * t ^ 2 * pzIter 2 h t θ + t ^ 3 * pzIter 3 h t θ := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    exact DzIter_three_pt hsmooth ht hθ
  have hpz : pz (DzIter 3 h) z θ
      = deriv (fun t => t * pzIter 1 h t θ + 3 * t ^ 2 * pzIter 2 h t θ
          + t ^ 3 * pzIter 3 h t θ) z := by
    show deriv (fun t => DzIter 3 h t θ) z = _
    exact hfun.deriv_eq
  have hd1 : deriv (fun t => t * pzIter 1 h t θ) z
      = deriv (fun t : ℝ => t) z * pzIter 1 h z θ
        + z * deriv (fun t => pzIter 1 h t θ) z := by
    exact deriv_mul differentiableAt_id hdiff1
  have hd2 : deriv (fun t => 3 * t ^ 2 * pzIter 2 h t θ) z
      = deriv (fun t : ℝ => 3 * t ^ 2) z * pzIter 2 h z θ
        + (3 * z ^ 2) * deriv (fun t => pzIter 2 h t θ) z := by
    exact deriv_mul ((differentiableAt_id.pow 2).const_mul 3) hdiff2
  have hd3 : deriv (fun t => t ^ 3 * pzIter 3 h t θ) z
      = deriv (fun t : ℝ => t ^ 3) z * pzIter 3 h z θ
        + z ^ 3 * deriv (fun t => pzIter 3 h t θ) z := by
    exact deriv_mul (differentiableAt_id.pow 3) hdiff3
  have hdA : deriv (fun t => t * pzIter 1 h t θ + 3 * t ^ 2 * pzIter 2 h t θ) z
      = deriv (fun t => t * pzIter 1 h t θ) z
        + deriv (fun t => 3 * t ^ 2 * pzIter 2 h t θ) z := by
    exact deriv_add (differentiableAt_id.mul hdiff1) (((differentiableAt_id.pow 2).const_mul 3).mul hdiff2)
  have hadd : deriv (fun t => t * pzIter 1 h t θ + 3 * t ^ 2 * pzIter 2 h t θ
        + t ^ 3 * pzIter 3 h t θ) z
      = deriv (fun t => t * pzIter 1 h t θ + 3 * t ^ 2 * pzIter 2 h t θ) z
        + deriv (fun t => t ^ 3 * pzIter 3 h t θ) z := by
    exact deriv_add ((differentiableAt_id.mul hdiff1).add (((differentiableAt_id.pow 2).const_mul 3).mul hdiff2))
      ((differentiableAt_id.pow 3).mul hdiff3)
  have hd3' : deriv (fun t : ℝ => t ^ 3) z = 3 * z ^ 2 := by
    rw [show (fun t : ℝ => t ^ 3) = (fun t : ℝ => t) ^ 3 from rfl,
      deriv_pow differentiableAt_id, deriv_id'']
    ring
  have hd2' : deriv (fun t : ℝ => 3 * t ^ 2) z = 6 * z := by
    rw [deriv_const_mul]
    · rw [deriv_sq]; ring
    · exact differentiableAt_id.pow 2
  rw [show DzIter 4 h z θ = z * pz (DzIter 3 h) z θ from rfl, hpz, hadd, hdA,
    hd1, hd2, hd3, hd2', hd3', deriv_id'', pzIter_step 1 h z θ, pzIter_step 2 h z θ,
    pzIter_step 3 h z θ]
  ring

/-! ## Bounds for the `f`-factors, from the `𝒲^{4,∞}` norm -/

private theorem WlInf_nonneg {α : ℝ} {f : ℝ → ℝ → ℝ} (hmem : WlInfMem α 4 f) :
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
  have hW := WlInf_nonneg hmem
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
  have hW := WlInf_nonneg hmem
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


/-- The `z`-slices of `D_θ^a f` are smooth on `(-1,∞)` for every `θ ∈ Iθ`. -/
theorem DthIter_contDiffOn_slice {f : ℝ → ℝ → ℝ} (hf : SmoothInt f) (a : ℕ) :
    ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => DthIter a f z θ) (Set.Ioi (-1)) := by
  intro θ hθ
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using hf.2 θ hθ
  · obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp ha)
    by_cases hθi : θ ∈ Ioo 0 (π/2)
    · refine isOpen_Ioi.contDiffOn_iff.mpr (fun z' hz' => ?_)
      exact contDiffAt_slice_left (DthIter_contDiffAt f (a'+1) (hf.contDiffAt_uncurry hz' hθi))
    · have hsin := sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
      have hzero : (fun z => DthIter (a'+1) f z θ) = fun _ => (0:ℝ) :=
        funext (fun z => DthIter_succ_eq_zero_of_sin_eq_zero a' f hsin)
      rw [hzero]; exact contDiffOn_const

/-- `|D_z^b f| ≤ 15 |f|_𝒲` for `b ≤ 4`. -/
theorem DzIter_le_WlInf {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (hf : SmoothInt f)
    (hmem : WlInfMem α 4 f) {b : ℕ} (hb : b ≤ 4) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |DzIter b f z θ| ≤ 15 * WlInf α 4 f := by
  have hz' : z ∈ Set.Ioi (-1) := by rw [Iz, Set.mem_Ici] at hz; rw [Set.mem_Ioi]; linarith
  have hW := WlInf_nonneg hmem
  have hsmooth : ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => f z θ) (Set.Ioi (-1)) := hf.2
  obtain rfl | rfl | rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
  · have h0 := zpz_le_WlInf hmem (j := 0) (by norm_num) hz hθ
    simp only [pow_zero, one_mul, pzIter_zero] at h0
    change |f z θ| ≤ 15 * WlInf α 4 f
    linarith
  · have h1 := zpz_le_WlInf hmem (j := 1) (by norm_num) hz hθ
    simp only [pow_one] at h1
    change |z * pzIter 1 f z θ| ≤ 15 * WlInf α 4 f
    linarith
  · have h1 := zpz_le_WlInf hmem (j := 1) (by norm_num) hz hθ
    have h2 := zpz_le_WlInf hmem (j := 2) (by norm_num) hz hθ
    simp only [pow_one] at h1
    rw [DzIter_two_pt hsmooth hz' hθ]
    calc |z * pzIter 1 f z θ + z ^ 2 * pzIter 2 f z θ|
        ≤ |z * pzIter 1 f z θ| + |z ^ 2 * pzIter 2 f z θ| := abs_add_le _ _
      _ ≤ WlInf α 4 f + WlInf α 4 f := add_le_add h1 h2
      _ ≤ 15 * WlInf α 4 f := by linarith
  · have h1 := zpz_le_WlInf hmem (j := 1) (by norm_num) hz hθ
    have h2 := zpz_le_WlInf hmem (j := 2) (by norm_num) hz hθ
    have h3 := zpz_le_WlInf hmem (j := 3) (by norm_num) hz hθ
    simp only [pow_one] at h1
    rw [DzIter_three_pt hsmooth hz' hθ]
    have e3 : |(3:ℝ) * z ^ 2 * pzIter 2 f z θ| = 3 * |z ^ 2 * pzIter 2 f z θ| := by
      rw [show (3:ℝ) * z^2 * pzIter 2 f z θ = 3 * (z^2 * pzIter 2 f z θ) by ring, abs_mul,
        abs_of_nonneg (by norm_num)]
    calc |z * pzIter 1 f z θ + 3 * z ^ 2 * pzIter 2 f z θ + z ^ 3 * pzIter 3 f z θ|
        ≤ |z * pzIter 1 f z θ + 3 * z ^ 2 * pzIter 2 f z θ| + |z ^ 3 * pzIter 3 f z θ| :=
          abs_add_le _ _
      _ ≤ (|z * pzIter 1 f z θ| + |3 * z ^ 2 * pzIter 2 f z θ|) + |z ^ 3 * pzIter 3 f z θ| := by
          gcongr; exact abs_add_le _ _
      _ ≤ (WlInf α 4 f + 3 * WlInf α 4 f) + WlInf α 4 f := by rw [e3]; linarith
      _ ≤ 15 * WlInf α 4 f := by linarith
  · have h1 := zpz_le_WlInf hmem (j := 1) (by norm_num) hz hθ
    have h2 := zpz_le_WlInf hmem (j := 2) (by norm_num) hz hθ
    have h3 := zpz_le_WlInf hmem (j := 3) (by norm_num) hz hθ
    have h4 := zpz_le_WlInf hmem (j := 4) (by norm_num) hz hθ
    simp only [pow_one] at h1
    rw [DzIter_four_pt hsmooth hz' hθ]
    have e7 : |(7:ℝ) * z ^ 2 * pzIter 2 f z θ| = 7 * |z ^ 2 * pzIter 2 f z θ| := by
      rw [show (7:ℝ) * z^2 * pzIter 2 f z θ = 7 * (z^2 * pzIter 2 f z θ) by ring, abs_mul,
        abs_of_nonneg (by norm_num)]
    have e6 : |(6:ℝ) * z ^ 3 * pzIter 3 f z θ| = 6 * |z ^ 3 * pzIter 3 f z θ| := by
      rw [show (6:ℝ) * z^3 * pzIter 3 f z θ = 6 * (z^3 * pzIter 3 f z θ) by ring, abs_mul,
        abs_of_nonneg (by norm_num)]
    calc |z * pzIter 1 f z θ + 7 * z ^ 2 * pzIter 2 f z θ + 6 * z ^ 3 * pzIter 3 f z θ
          + z ^ 4 * pzIter 4 f z θ|
        ≤ |z * pzIter 1 f z θ + 7 * z ^ 2 * pzIter 2 f z θ + 6 * z ^ 3 * pzIter 3 f z θ|
            + |z ^ 4 * pzIter 4 f z θ| := abs_add_le _ _
      _ ≤ (|z * pzIter 1 f z θ + 7 * z ^ 2 * pzIter 2 f z θ| + |6 * z ^ 3 * pzIter 3 f z θ|)
            + |z ^ 4 * pzIter 4 f z θ| := by gcongr; exact abs_add_le _ _
      _ ≤ ((|z * pzIter 1 f z θ| + |7 * z ^ 2 * pzIter 2 f z θ|) + |6 * z ^ 3 * pzIter 3 f z θ|)
            + |z ^ 4 * pzIter 4 f z θ| := by gcongr; exact abs_add_le _ _
      _ ≤ ((WlInf α 4 f + 7 * WlInf α 4 f) + 6 * WlInf α 4 f) + WlInf α 4 f := by
          rw [e7, e6]; linarith
      _ ≤ 15 * WlInf α 4 f := by linarith

/-- `|D_z^b D_θ^a f| ≤ 15 |f|_𝒲 sin(2θ)^{α/5}(α+sin 2θ)` for `1 ≤ a`, `a+b ≤ 4`. -/
theorem mixed_le_WlInf {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ} (hf : SmoothInt f)
    (hmem : WlInfMem α 4 f) {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 4)
    {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |mixed b a f z θ| ≤ 15 * (WlInf α 4 f
      * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5))) := by
  have hz' : z ∈ Set.Ioi (-1) := by rw [Iz, Set.mem_Ici] at hz; rw [Set.mem_Ioi]; linarith
  have hW := WlInf_nonneg hmem
  have hΦ : 0 ≤ (α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5) :=
    mul_nonneg (by linarith [sin_two_nonneg' hθ]) (Real.rpow_nonneg (sin_two_nonneg' hθ) _)
  set P : ℝ := WlInf α 4 f * ((α + Real.sin (2*θ)) * (Real.sin (2*θ)) ^ (α/5)) with hP
  have hPnn : 0 ≤ P := by rw [hP]; exact mul_nonneg hW hΦ
  have hsmooth : ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => DthIter a f z θ) (Set.Ioi (-1)) :=
    DthIter_contDiffOn_slice hf a
  obtain rfl | rfl | rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
  · have h0 : |z ^ 0 * pzIter 0 (DthIter a f) z θ| ≤ P := by
      rw [hP]; exact zpz_Dth_le_WlInf hα hmem ha (by omega) hz hθ
    simp only [pow_zero, one_mul, pzIter_zero] at h0
    change |DthIter a f z θ| ≤ 15 * P
    linarith
  · have h1 : |z ^ 1 * pzIter 1 (DthIter a f) z θ| ≤ P := by
      rw [hP]; exact zpz_Dth_le_WlInf hα hmem ha (by omega) hz hθ
    simp only [pow_one] at h1
    change |z * pzIter 1 (DthIter a f) z θ| ≤ 15 * P
    linarith
  · have h1 : |z ^ 1 * pzIter 1 (DthIter a f) z θ| ≤ P := by
      rw [hP]; exact zpz_Dth_le_WlInf hα hmem ha (by omega) hz hθ
    have h2 : |z ^ 2 * pzIter 2 (DthIter a f) z θ| ≤ P := by
      rw [hP]; exact zpz_Dth_le_WlInf hα hmem ha (by omega) hz hθ
    simp only [pow_one] at h1
    change |DzIter 2 (DthIter a f) z θ| ≤ 15 * P
    rw [DzIter_two_pt hsmooth hz' hθ]
    calc |z * pzIter 1 (DthIter a f) z θ + z ^ 2 * pzIter 2 (DthIter a f) z θ|
        ≤ |z * pzIter 1 (DthIter a f) z θ| + |z ^ 2 * pzIter 2 (DthIter a f) z θ| := abs_add_le _ _
      _ ≤ P + P := add_le_add h1 h2
      _ ≤ 15 * P := by linarith
  · have h1 : |z ^ 1 * pzIter 1 (DthIter a f) z θ| ≤ P := by
      rw [hP]; exact zpz_Dth_le_WlInf hα hmem ha (by omega) hz hθ
    have h2 : |z ^ 2 * pzIter 2 (DthIter a f) z θ| ≤ P := by
      rw [hP]; exact zpz_Dth_le_WlInf hα hmem ha (by omega) hz hθ
    have h3 : |z ^ 3 * pzIter 3 (DthIter a f) z θ| ≤ P := by
      rw [hP]; exact zpz_Dth_le_WlInf hα hmem ha (by omega) hz hθ
    simp only [pow_one] at h1
    change |DzIter 3 (DthIter a f) z θ| ≤ 15 * P
    rw [DzIter_three_pt hsmooth hz' hθ]
    have e3 : |(3:ℝ) * z ^ 2 * pzIter 2 (DthIter a f) z θ|
        = 3 * |z ^ 2 * pzIter 2 (DthIter a f) z θ| := by
      rw [show (3:ℝ) * z^2 * pzIter 2 (DthIter a f) z θ
          = 3 * (z^2 * pzIter 2 (DthIter a f) z θ) by ring, abs_mul, abs_of_nonneg (by norm_num)]
    calc |z * pzIter 1 (DthIter a f) z θ + 3 * z ^ 2 * pzIter 2 (DthIter a f) z θ
          + z ^ 3 * pzIter 3 (DthIter a f) z θ|
        ≤ |z * pzIter 1 (DthIter a f) z θ + 3 * z ^ 2 * pzIter 2 (DthIter a f) z θ|
            + |z ^ 3 * pzIter 3 (DthIter a f) z θ| := abs_add_le _ _
      _ ≤ (|z * pzIter 1 (DthIter a f) z θ| + |3 * z ^ 2 * pzIter 2 (DthIter a f) z θ|)
            + |z ^ 3 * pzIter 3 (DthIter a f) z θ| := by gcongr; exact abs_add_le _ _
      _ ≤ (P + 3 * P) + P := by rw [e3]; linarith
      _ ≤ 15 * P := by linarith
  · exact absurd (by omega : ¬ (1 ≤ a ∧ a + 4 ≤ 4)) (by omega)


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

/-- **The angular Hardy step.** -/
theorem angular_hardy {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {h : ℝ → ℝ → ℝ}
    (hsm : SmoothNbhd h) {z : ℝ} (hz : z ∈ Iz) (h0 : h z 0 = 0)
    (hint : IntegrableOn (fun θ => (pth h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)) Iθ) :
    ∫ θ in Iθ, (h z θ) ^ 2 * ((α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))
      ≤ (100 / (gam α - 1)) * 700 *
        (∫ θ in Iθ, (pth h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)) := by
  have hγ1 : (0:ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hpt := HardyTheta α hα hα1 h z hsm hz h0 hint
  have hI : 0 ≤ ∫ θ in Iθ, (pth h z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α) :=
    setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' hθ) _)
  have hcoef : 0 ≤ 100 / (gam α - 1) := by positivity
  have hcI : 0 ≤ 100 / (gam α - 1)
      * (∫ σ in Iθ, (pth h z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := mul_nonneg hcoef hI
  have hμint := integrableOn_angular_weight hα hα1
  have hμnn : ∀ θ ∈ Iθ, 0 ≤ (α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) := fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' hθ) _)
  have hIntR : IntegrableOn (fun θ => (100 / (gam α - 1)
      * (∫ σ in Iθ, (pth h z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)))
      * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) Iθ :=
    hμint.const_mul _
  calc ∫ θ in Iθ, (h z θ) ^ 2 * ((α + Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))
      ≤ ∫ θ in Iθ, (100 / (gam α - 1)
          * (∫ σ in Iθ, (pth h z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)))
          * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) :=
        setIntegral_mono_of_nonneg
          (fun θ hθ => mul_nonneg (sq_nonneg _) (hμnn θ hθ))
          (fun θ hθ => mul_le_mul_of_nonneg_right (hpt θ hθ) (hμnn θ hθ))
          hIntR
    _ = (100 / (gam α - 1) * (∫ σ in Iθ, (pth h z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)))
          * (∫ θ in Iθ, (α + Real.sin (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (100 / (gam α - 1) * (∫ σ in Iθ, (pth h z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)))
          * 700 := mul_le_mul_of_nonneg_left (angular_weight_integral_bound hα hα1) hcI
    _ = (100 / (gam α - 1)) * 700
          * (∫ σ in Iθ, (pth h z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)) := by ring


/-! ## The angular Hardy bound for the `D_z`-iterates of `g` -/

/-- The weighted `L²`-integral of `∂_θ (D_z^d g)` on the angular interval. -/
noncomputable def Btil (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ) (z : ℝ) : ℝ :=
  ∫ σ in Iθ, (pth (DzIter d g) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α)

theorem sin_pow_split {θ : ℝ} (hθ : θ ∈ Iθ) (p : ℝ) (hp : 2 + p ≠ 0) :
    (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ p = (Real.sin (2 * θ)) ^ (2 + p) := by
  have hs := sin_two_nonneg' hθ
  rw [show (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ ((2:ℝ)) from
      (Real.rpow_natCast (Real.sin (2 * θ)) 2).symm,
    ← Real.rpow_add' hs hp]

/-- **The `θ`-Hardy bound for `D_z^d g`.** -/
theorem hardy_slice {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : SmoothNbhd g) (hgm : HkMem α 4 g) (hvt : VanishTheta g)
    {d : ℕ} (hd : d ≤ 3) {z : ℝ} (hz : z ∈ Iz) (hzpos : 0 < z) :
    ∀ θ ∈ Iθ, (DzIter d g z θ) ^ 2 ≤ (100 / (gam α - 1)) * Btil α g d z := by
  have hwz : (0:ℝ) < w z := by rw [w]; positivity
  have hEq : ∀ θ ∈ Iθ, (pth (DzIter d g) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α)
      = (mixed d 1 g z θ * Wt α z θ) ^ 2 / (w z) ^ 2 := by
    intro θ hθ
    have hcomm : Dth (DzIter d g) z θ = mixed d 1 g z θ :=
      Dth_DzIter_comm_eqOn hg d (mem_nbhU hz hθ)
    have hWt := bt_Wt_sq α z θ hα hθ
    have hsp := sin_pow_split hθ (-(gam α)) (by rw [gam]; intro h; linarith)
    have hne : (w z) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hwz)
    have key : (pth (DzIter d g) z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - gam α) * (w z) ^ 2
        = (mixed d 1 g z θ * Wt α z θ) ^ 2 := by
      rw [show mixed d 1 g z θ = Dth (DzIter d g) z θ from hcomm.symm, Dth, mul_pow,
        show (Real.sin (2 * θ)) ^ (2 - gam α)
          = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) from hsp.symm, hWt]
      ring
    rw [eq_div_iff hne, key]
  have hbig : IntegrableOn (fun θ => (mixed d 1 g z θ * Wt α z θ) ^ 2) Iθ :=
    mixed_sq_integrableOn hg hgm 1 d le_rfl (by omega) hz
  have hint : IntegrableOn (fun θ => (pth (DzIter d g) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - gam α)) Iθ :=
    (hbig.div_const ((w z) ^ 2)).congr
      (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => (hEq θ hθ).symm))
  exact HardyTheta α hα hα1 (DzIter d g) z (SmoothNbhd.DzIter hg d) hz
    ((bt_DzIter_vanish hvt d).1 z) hint

/-- The identity `(w z)² · Btil d z = ∫_θ (D_z^d D_θ g · W)²` for `z ∈ Iz`. -/
theorem wsq_Btil_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ} (hg : SmoothNbhd g)
    (d : ℕ) {z : ℝ} (hz : z ∈ Iz) :
    (w z) ^ 2 * Btil α g d z
      = ∫ θ in Iθ, (mixed d 1 g z θ * Wt α z θ) ^ 2 := by
  rw [Btil, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  have hcomm : Dth (DzIter d g) z θ = mixed d 1 g z θ :=
    Dth_DzIter_comm_eqOn hg d (mem_nbhU hz hθ)
  have hWt := bt_Wt_sq α z θ hα hθ
  have hsp := sin_pow_split hθ (-(gam α)) (by rw [gam]; intro h; linarith)
  rw [show mixed d 1 g z θ = Dth (DzIter d g) z θ from hcomm.symm, Dth, mul_pow,
    show (Real.sin (2 * θ)) ^ (2 - gam α)
      = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) from hsp.symm, hWt]
  ring

/-- The `z`-integral of `w² · Btil d z` is controlled by the `z`-integral of the `H⁴`
integrand of `g`, hence integrable. -/
theorem integrableOn_Btil_w {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ} (hg : SmoothNbhd g)
    (hgm : HkMem α 4 g) {d : ℕ} (hd : d ≤ 3) :
    IntegrableOn (fun z => (w z) ^ 2 * Btil α g d z) Iz := by
  have hsummand : ∀ z ∈ Iz, ∀ θ ∈ Iθ, (mixed d 1 g z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 4 g z θ :=
    fun z hz θ hθ => sq_le_HkIntegrand_mixed α 4 g z θ 1 d le_rfl (by omega)
  have hmajor : IntegrableOn (fun z => ∫ θ in Iθ, HkIntegrand α 4 g z θ) Iz := hgm.2
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Iθ, (mixed d 1 g z θ * Wt α z θ) ^ 2)
      (volume.restrict Iz) := by
    have h := (aesm_mixed_Wt_sq_prod α g hg d 1).integral_prod_right'
    have heq : (fun z => ∫ θ, (mixed d 1 g z θ * Wt α z θ) ^ 2 ∂(volume.restrict Iθ))
        = (fun z => ∫ θ in Iθ, (mixed d 1 g z θ * Wt α z θ) ^ 2) := by
      funext z; rfl
    rw [← heq]; exact h
  have hfslice : IntegrableOn (fun z => ∫ θ in Iθ, (mixed d 1 g z θ * Wt α z θ) ^ 2) Iz := by
    refine Integrable.mono' hmajor haesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz'
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) (hgm.1 z hz')
      (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hsummand z hz' θ hθ))
  exact hfslice.congr (ae_restrict_of_forall_mem measurableSet_Ici
    (fun z hz' => (wsq_Btil_eq hα hα1 hg d hz').symm))


/-! ## Pointwise bounds for the two families of summands -/

set_option maxHeartbeats 0 in
/-- The pure `D_z`-summand of `HkIntegrand α 4 (f·g)` is bounded by the `H⁴`-integrand of `g`. -/
theorem z_term_le {α : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ} (hf : SmoothInt f)
    (hg : SmoothNbhd g) (hfm : WlInfMem α 4 f)
    {i : ℕ} (hi : i ≤ 4) {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    (DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
      ≤ 10 ^ 7 * (WlInf α 4 f) ^ 2 * HkIntegrand α 4 g z θ := by
  have hW := WlInf_nonneg hfm
  set Hv : ℝ := w z / (Real.sin (2 * θ)) ^ (eta / 2) with hHv
  have heq := DzIter_mul i f g hz (hf.2 θ hθ) (hardyZ_contDiffOn_slice g hg hθ)
  have hsplit : (DzIter i (fun z θ => f z θ * g z θ) z θ * Hv) ^ 2
      = (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * DzIter b f z θ) * (DzIter (i - b) g z θ * Hv)) ^ 2 := by
    rw [heq, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [hsplit]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => ((i.choose b : ℝ) * DzIter b f z θ) * (DzIter (i - b) g z θ * Hv))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hper : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℝ) * DzIter b f z θ) * (DzIter (i - b) g z θ * Hv)) ^ 2
        ≤ 57600 * (WlInf α 4 f) ^ 2 * (DzIter (i - b) g z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDf : |DzIter b f z θ| ≤ 15 * WlInf α 4 f := DzIter_le_WlInf hα hf hfm (by omega) hz hθ
    have hx : (DzIter b f z θ) ^ 2 ≤ (15 * WlInf α 4 f) ^ 2 := by
      have hB : (0:ℝ) ≤ 15 * WlInf α 4 f := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDf).1
      have h2 := (abs_le.mp hDf).2
      nlinarith [hB, h1, h2]
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 256 := by
      have h1 : i.choose b ≤ 2 ^ i := by
        have h := Finset.single_le_sum (f := fun k => i.choose k) (fun k _ => Nat.zero_le _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hbi))
        rwa [Nat.sum_range_choose] at h
      have h2 : i.choose b ≤ 16 := by
        calc i.choose b ≤ 2 ^ i := h1
          _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hi
          _ = 16 := by norm_num
      have h3 : (i.choose b : ℝ) ≤ 16 := by exact_mod_cast h2
      have h4 : (0:ℝ) ≤ (i.choose b : ℝ) := by positivity
      nlinarith [h3, h4]
    calc (((i.choose b : ℝ) * DzIter b f z θ) * (DzIter (i - b) g z θ * Hv)) ^ 2
        = ((i.choose b : ℝ)) ^ 2 * (DzIter b f z θ) ^ 2
            * (DzIter (i - b) g z θ * Hv) ^ 2 := by ring
      _ ≤ 256 * (15 * WlInf α 4 f) ^ 2 * (DzIter (i - b) g z θ * Hv) ^ 2 := by
          gcongr
      _ = 57600 * (WlInf α 4 f) ^ 2 * (DzIter (i - b) g z θ * Hv) ^ 2 := by ring
  have hsumsq : ∑ b ∈ Finset.range (i + 1), (DzIter (i - b) g z θ * Hv) ^ 2
      ≤ 5 * HkIntegrand α 4 g z θ := by
    calc ∑ b ∈ Finset.range (i + 1), (DzIter (i - b) g z θ * Hv) ^ 2
        ≤ ∑ b ∈ Finset.range (i + 1), HkIntegrand α 4 g z θ :=
          Finset.sum_le_sum (fun b hb => sq_le_HkIntegrand_z α 4 g z θ (i - b) (by omega))
      _ = ((i : ℝ) + 1) * HkIntegrand α 4 g z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 5 * HkIntegrand α 4 g z θ := by
          have hnn := HkIntegrand_nonneg α 4 g z θ
          have hI2 : (i : ℝ) + 1 ≤ 5 := by exact_mod_cast (by omega : i + 1 ≤ 5)
          nlinarith
  calc (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * DzIter b f z θ) * (DzIter (i - b) g z θ * Hv)) ^ 2
      ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) *
          ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℝ) * DzIter b f z θ) * (DzIter (i - b) g z θ * Hv)) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (57600 * (WlInf α 4 f) ^ 2 * (DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 57600 * (WlInf α 4 f) ^ 2 * (((i : ℝ) + 1)
          * ∑ b ∈ Finset.range (i + 1), (DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 57600 * (WlInf α 4 f) ^ 2 * (5 * (5 * HkIntegrand α 4 g z θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hI2 : (i : ℝ) + 1 ≤ 5 := by exact_mod_cast (by omega : i + 1 ≤ 5)
        exact mul_le_mul hI2 hsumsq (Finset.sum_nonneg (fun b _ => sq_nonneg _)) (by norm_num)
    _ ≤ 10 ^ 7 * (WlInf α 4 f) ^ 2 * HkIntegrand α 4 g z θ := by
        have hnn := HkIntegrand_nonneg α 4 g z θ
        have h2 : 0 ≤ (WlInf α 4 f) ^ 2 := sq_nonneg _
        have hh : 57600 * (WlInf α 4 f) ^ 2 * (5 * (5 * HkIntegrand α 4 g z θ))
            = 1440000 * ((WlInf α 4 f) ^ 2 * HkIntegrand α 4 g z θ) := by ring
        rw [hh, show (10:ℝ)^7 * (WlInf α 4 f)^2 * HkIntegrand α 4 g z θ
            = 10^7 * ((WlInf α 4 f)^2 * HkIntegrand α 4 g z θ) from by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg h2 hnn)


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

set_option maxHeartbeats 0 in
/-- The mixed summand of `HkIntegrand α 4 (f·g)` is bounded by `Gg`. -/
theorem m_term_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hf : SmoothInt f) (hg : SmoothNbhd g) (hfm : WlInfMem α 4 f) (hvt : VanishTheta g)
    (hgm : HkMem α 4 g) {I J : ℕ} (hI : 1 ≤ I) (hIJ : I + J ≤ 4)
    {z θ : ℝ} (hz : z ∈ Iz) (hzpos : 0 < z) (hθ : θ ∈ Iθ) :
    (mixed J I (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
      ≤ 10 ^ 12 * (WlInf α 4 f) ^ 2 * (HkIntegrand α 4 g z θ + (gam α - 1)⁻¹
          * (∑ d ∈ Finset.range 4, Btil α g d z)
          * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
              * (w z) ^ 2)) := by
  have hW := WlInf_nonneg hfm
  have hW2 : 0 ≤ (WlInf α 4 f) ^ 2 := sq_nonneg _
  have hγ1 : (0:ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγinv : 0 ≤ (gam α - 1)⁻¹ := by positivity
  have hs0 := sin_two_nonneg' hθ
  set Psi2 : ℝ := (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)
    with hPsi2def
  have hPsi2nn : 0 ≤ Psi2 := by
    rw [hPsi2def]; exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  have hPsi2le : Psi2 ≤ 4 := by
    rw [hPsi2def]
    have h1 : (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 1 :=
      Real.rpow_le_one hs0 (Real.sin_le_one _) (by linarith)
    have h2 : (α + Real.sin (2 * θ)) ^ 2 ≤ 4 := by
      nlinarith [hs0, Real.sin_le_one (2 * θ), hα, hα1]
    nlinarith [h1, h2, Real.rpow_nonneg hs0 (2 * α / 5)]
  have hPhi2 : ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = Psi2 := by
    rw [hPsi2def, mul_pow]
    have hss : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
      rw [show ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
            = ((Real.sin (2 * θ)) ^ (α / 5)) ^ ((2:ℝ)) from (Real.rpow_natCast _ 2).symm,
        ← Real.rpow_mul hs0,
        show (α / 5) * (2:ℝ) = 2 * α / 5 by ring]
    rw [hss]
  set Thw : ℝ := (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
    * (w z) ^ 2 with hThwdef
  have hThwnn : 0 ≤ Thw := by
    rw [hThwdef]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)) (sq_nonneg _)
  have hWt_eq : Psi2 * (Wt α z θ) ^ 2 = Thw := by
    rw [hPsi2def, hThwdef, Wt, wTheta, mul_pow]
    have hA : ((Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(gam α)) := by
      rw [show ((Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ 2
            = ((Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ ((2:ℝ)) from (Real.rpow_natCast _ 2).symm,
        ← Real.rpow_mul hs0,
        show (-(gam α / 2)) * (2:ℝ) = -(gam α) by ring]
    have hB : (Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (-(gam α))
        = (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) := by
      rw [← Real.rpow_add' hs0 (by rw [gam]; intro hh; linarith),
        show 2 * α / 5 + (-(gam α)) = 2 * α / 5 - gam α by ring]
    rw [hA]
    calc (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)
          * (w z ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)))
        = (α + Real.sin (2 * θ)) ^ 2
            * ((Real.sin (2 * θ)) ^ (2 * α / 5) * (Real.sin (2 * θ)) ^ (-(gam α))) * w z ^ 2 := by
          ring
      _ = (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) * w z ^ 2 := by
          rw [hB]
  set Bsum : ℝ := ∑ d ∈ Finset.range 4, Btil α g d z with hBsumdef
  have hBtil_nn : ∀ d, 0 ≤ Btil α g d z := fun d => by
    rw [Btil]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' hσ) _)
  have hBsum_nn : 0 ≤ Bsum := by
    rw [hBsumdef]; exact Finset.sum_nonneg fun d _ => hBtil_nn d
  set Gg : ℝ := HkIntegrand α 4 g z θ + (gam α - 1)⁻¹ * Bsum * Thw with hGgdef
  have hGgnn : 0 ≤ Gg := by
    rw [hGgdef]
    exact add_nonneg (HkIntegrand_nonneg α 4 g z θ)
      (mul_nonneg (mul_nonneg hγinv hBsum_nn) hThwnn)
  have hGg_Hk : HkIntegrand α 4 g z θ ≤ Gg := by
    rw [hGgdef]; exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hγinv hBsum_nn) hThwnn)
  have hGg_d : ∀ d ≤ 3, (gam α - 1)⁻¹ * Btil α g d z * Thw ≤ Gg := by
    intro d hd
    have hBle : Btil α g d z ≤ Bsum := by
      rw [hBsumdef]
      exact Finset.single_le_sum (fun e _ => hBtil_nn e) (Finset.mem_range.mpr (by omega))
    have h1 : (gam α - 1)⁻¹ * Btil α g d z * Thw ≤ (gam α - 1)⁻¹ * Bsum * Thw :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBle hγinv) hThwnn
    rw [hGgdef]; linarith [HkIntegrand_nonneg α 4 g z θ]
  -- Leibniz
  have heq := mixed_mul_eq J I f g hf (SmoothInt.of_SmoothNbhd hg)
  set Y : ℕ → ℕ → ℝ := fun a b => (I.choose a : ℝ) * (J.choose b : ℝ)
    * ((mixed b a f z θ) * (mixed (J - b) (I - a) g z θ * Wt α z θ)) with hYdef
  have hYsplit : (mixed J I (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2 := by
    have hkey : (mixed J I (fun z θ => f z θ * g z θ) z θ) * Wt α z θ
        = ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b := by
      rw [heq z hz θ hθ, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hYdef]; ring
    rw [hkey]
  have hper : ∀ a ∈ Finset.range (I + 1), ∀ b ∈ Finset.range (J + 1),
      (Y a b) ^ 2 ≤ 1500000000 * (WlInf α 4 f) ^ 2 * Gg := by
    intro a ha b hb
    have haI : a ≤ I := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbJ : b ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hJb : J - b ≤ 3 := by have h1 := hIJ; have h2 := hI; have h3 := hbJ; omega
    have hcha : (I.choose a : ℝ) ^ 2 ≤ 256 := choose_sq_le_256 I a (by omega) (by omega)
    have hchb : (J.choose b : ℝ) ^ 2 ≤ 256 := choose_sq_le_256 J b (by omega) (by omega)
    have hch : (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 65536 :=
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 256 * 256 :=
            mul_le_mul hcha hchb (by positivity) (by norm_num)
        _ = 65536 := by norm_num
    have hY : (Y a b) ^ 2 = (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
        * ((mixed b a f z θ) * (mixed (J - b) (I - a) g z θ * Wt α z θ)) ^ 2 := by
      rw [hYdef]; ring
    rw [hY]
    by_cases hlt : a < I
    · have hIa : 1 ≤ I - a := by omega
      have hma : (mixed b a f z θ) ^ 2 ≤ 5 * (15 * WlInf α 4 f) ^ 2 := by
        rcases eq_or_ne a 0 with ha0 | ha0
        · subst ha0
          have h := DzIter_le_WlInf hα hf hfm (b := b)
            (by have h1 := hIJ; have h2 := hbJ; omega) hz hθ
          have h1 : (DzIter b f z θ) ^ 2 ≤ (15 * WlInf α 4 f) ^ 2 := sq_le_sq_of_abs_le h
          show (DzIter b f z θ) ^ 2 ≤ 5 * (15 * WlInf α 4 f) ^ 2
          nlinarith [h1, sq_nonneg (15 * WlInf α 4 f)]
        · have ha1 : 1 ≤ a := by omega
          have h := mixed_le_WlInf hα hf hfm (a := a) (b := b) ha1 (by omega) hz hθ
          calc (mixed b a f z θ) ^ 2
              ≤ (15 * (WlInf α 4 f
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
                sq_le_sq_of_abs_le h
            _ = (15 * WlInf α 4 f) ^ 2 * Psi2 := by rw [mul_pow, mul_pow, hPhi2]; ring
            _ ≤ (15 * WlInf α 4 f) ^ 2 * 4 := mul_le_mul_of_nonneg_left hPsi2le (sq_nonneg _)
            _ ≤ 5 * (15 * WlInf α 4 f) ^ 2 := by nlinarith [sq_nonneg (WlInf α 4 f)]
      have hmg : (mixed (J - b) (I - a) g z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 4 g z θ :=
        sq_le_HkIntegrand_mixed α 4 g z θ (I - a) (J - b) hIa
          (by have h1 := hIJ; have h2 := haI; have h3 := hbJ; omega)
      have hbase2 : ((mixed b a f z θ) * (mixed (J - b) (I - a) g z θ * Wt α z θ)) ^ 2
          ≤ (5 * (15 * WlInf α 4 f) ^ 2) * HkIntegrand α 4 g z θ := by
        rw [mul_pow]
        exact mul_le_mul hma hmg (sq_nonneg _) (by positivity)
      exact le_trans
        (mul_le_mul hch hbase2 (sq_nonneg _) (by norm_num))
        (by
          have hA : (0:ℝ) ≤ (WlInf α 4 f) ^ 2 * HkIntegrand α 4 g z θ :=
            mul_nonneg hW2 (HkIntegrand_nonneg α 4 g z θ)
          have hB : (WlInf α 4 f) ^ 2 * HkIntegrand α 4 g z θ ≤ (WlInf α 4 f) ^ 2 * Gg :=
            mul_le_mul_of_nonneg_left hGg_Hk hW2
          nlinarith [hA, hB, sq_nonneg (WlInf α 4 f)])
    · have hac : a = I := by omega
      have hsub : I - a = 0 := by omega
      have hmb : (mixed b a f z θ) ^ 2 ≤ (15 * WlInf α 4 f) ^ 2 * Psi2 := by
        rw [hac]
        have h := mixed_le_WlInf hα hf hfm (a := I) (b := b) hI (by omega) hz hθ
        calc (mixed b I f z θ) ^ 2
            ≤ (15 * (WlInf α 4 f
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
              sq_le_sq_of_abs_le h
          _ = (15 * WlInf α 4 f) ^ 2 * Psi2 := by rw [mul_pow, mul_pow, hPhi2]; ring
      have hmg : (mixed (J - b) (I - a) g z θ * Wt α z θ) ^ 2
          ≤ (100 / (gam α - 1)) * Btil α g (J - b) z * (Wt α z θ) ^ 2 := by
        rw [hsub, show mixed (J - b) 0 g z θ = DzIter (J - b) g z θ from rfl, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (hardy_slice hα hα1 hg hgm hvt hJb hz hzpos θ hθ) (sq_nonneg _)
      have hbase2 : ((mixed b a f z θ) * (mixed (J - b) (I - a) g z θ * Wt α z θ)) ^ 2
          ≤ ((15 * WlInf α 4 f) ^ 2 * Psi2)
              * ((100 / (gam α - 1)) * Btil α g (J - b) z * (Wt α z θ) ^ 2) := by
        rw [mul_pow]
        exact mul_le_mul hmb hmg (sq_nonneg _) (by positivity)
      exact le_trans
        (mul_le_mul hch hbase2 (sq_nonneg _) (by norm_num))
        (by
          have hA : (0:ℝ) ≤ (gam α - 1)⁻¹ * Btil α g (J - b) z * Thw :=
            mul_nonneg (mul_nonneg hγinv (hBtil_nn _)) hThwnn
          have hB : (gam α - 1)⁻¹ * Btil α g (J - b) z * Thw ≤ Gg := hGg_d (J - b) hJb
          have hfac : (65536:ℝ) * (((15 * WlInf α 4 f) ^ 2 * Psi2)
                * ((100 / (gam α - 1)) * Btil α g (J - b) z * (Wt α z θ) ^ 2))
              = 1474560000 * ((WlInf α 4 f) ^ 2
                * ((gam α - 1)⁻¹ * Btil α g (J - b) z * Thw)) := by
            rw [← hWt_eq]; ring_nf
          rw [hfac]
          calc 1474560000 * ((WlInf α 4 f) ^ 2
                * ((gam α - 1)⁻¹ * Btil α g (J - b) z * Thw))
              ≤ 1474560000 * ((WlInf α 4 f) ^ 2 * Gg) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hW2) (by norm_num)
            _ ≤ 1500000000 * ((WlInf α 4 f) ^ 2 * Gg) :=
                mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hW2 hGgnn)
            _ = 1500000000 * (WlInf α 4 f) ^ 2 * Gg := by ring)
  -- Cauchy-Schwarz
  have hcardI : (((Finset.range (I + 1)).card : ℕ) : ℝ) = (I : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (J + 1)).card : ℕ) : ℝ) = (J : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hIJ5 : ((I : ℝ) + 1) * ((J : ℝ) + 1) ≤ 25 := by
    have hI4 : (I : ℝ) ≤ 4 := by exact_mod_cast (by omega : I ≤ 4)
    have hJ4 : (J : ℝ) ≤ 4 := by exact_mod_cast (by omega : J ≤ 4)
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
          (1500000000 * (WlInf α 4 f) ^ 2 * Gg) :=
    Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hper a ha b hb
  have hsumconst : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
        (1500000000 * (WlInf α 4 f) ^ 2 * Gg)
      = ((I : ℝ) + 1) * ((J : ℝ) + 1) * (1500000000 * (WlInf α 4 f) ^ 2 * Gg) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast; ring
  rw [hYsplit]
  calc (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
      ≤ ((I : ℝ) + 1) * ∑ a ∈ Finset.range (I + 1),
          ((J : ℝ) + 1) * ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (I + 1))
          (f := fun a => ∑ b ∈ Finset.range (J + 1), Y a b)
        rw [hcardI] at hcs
        refine hcs.trans ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ?_)) (by positivity)
        have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (J + 1)) (f := fun b => Y a b)
        rwa [hcardJ] at hcs2
    _ = ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
              (1500000000 * (WlInf α 4 f) ^ 2 * Gg) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2 * (1500000000 * (WlInf α 4 f) ^ 2 * Gg) := by
        rw [hsumconst]; ring_nf
    _ ≤ 625 * (1500000000 * (WlInf α 4 f) ^ 2 * Gg) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h0 : (0:ℝ) ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1) := by positivity
        nlinarith [hIJ5, h0]
    _ = 937500000000 * ((WlInf α 4 f) ^ 2 * Gg) := by ring
    _ ≤ 10 ^ 12 * (WlInf α 4 f) ^ 2 * Gg := by
        rw [show (10:ℝ)^12 * (WlInf α 4 f)^2 * Gg = 10^12 * ((WlInf α 4 f)^2 * Gg) from by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hW2 hGgnn)


/-! ## The majorant and the product rule -/

/-- The pointwise majorant for the product rule. -/
noncomputable def Gmaj (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  HkIntegrand α 4 g z θ + (gam α - 1)⁻¹ * (∑ d ∈ Finset.range 4, Btil α g d z)
    * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) * (w z) ^ 2)

/-- `(w z)² · Σ_d Btil d z` is integrable in `z`. -/
theorem integrableOn_bSum_w {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : SmoothNbhd g) (hgm : HkMem α 4 g) :
    IntegrableOn (fun z => (w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z) Iz := by
  have h0 := integrableOn_Btil_w hα hα1 hg hgm (d := 0) (by norm_num)
  have h1 := integrableOn_Btil_w hα hα1 hg hgm (d := 1) (by norm_num)
  have h2 := integrableOn_Btil_w hα hα1 hg hgm (d := 2) (by norm_num)
  have h3 := integrableOn_Btil_w hα hα1 hg hgm (d := 3) (by norm_num)
  have hsum : (fun z => (w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z)
      = fun z => ((w z) ^ 2 * Btil α g 0 z + (w z) ^ 2 * Btil α g 1 z)
          + ((w z) ^ 2 * Btil α g 2 z + (w z) ^ 2 * Btil α g 3 z) := by
    funext z
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    ring
  rw [hsum]
  exact ((h0.add h1).add (h2.add h3))

/-- The inner integral of `Gmaj`, written in closed form. -/
theorem Gmaj_theta_sum {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : SmoothNbhd g) (hgm : HkMem α 4 g) {z : ℝ} (hz : z ∈ Iz) :
    ∫ θ in Iθ, Gmaj α g z θ
      = (∫ θ in Iθ, HkIntegrand α 4 g z θ)
        + (gam α - 1)⁻¹ * (∫ θ in Iθ, (α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))
          * ((w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z) := by
  have hμw : IntegrableOn (fun θ => (α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) * (w z) ^ 2) Iθ :=
    (integrableOn_angular_weight hα hα1).mul_const ((w z) ^ 2)
  have hsecond : IntegrableOn (fun θ => ((gam α - 1)⁻¹ * (∑ d ∈ Finset.range 4, Btil α g d z))
      * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) * (w z) ^ 2)) Iθ :=
    hμw.const_mul _
  simp only [Gmaj]
  rw [MeasureTheory.integral_add (hgm.1 z hz) hsecond,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
  ring

/-- `G` is integrable in `z`, with the closed form of its `z`-integral controlled. -/
theorem integrableOn_Gmaj {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : SmoothNbhd g) (hgm : HkMem α 4 g) :
    IntegrableOn (fun z => ∫ θ in Iθ, Gmaj α g z θ) Iz := by
  have hbsum := integrableOn_bSum_w hα hα1 hg hgm
  have hmain : IntegrableOn (fun z => (∫ θ in Iθ, HkIntegrand α 4 g z θ)
      + (gam α - 1)⁻¹ * (∫ θ in Iθ, (α + Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))
        * ((w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z)) Iz :=
    hgm.2.add (hbsum.const_mul _)
  exact hmain.congr (ae_restrict_of_forall_mem measurableSet_Ici
    (fun z hz => (Gmaj_theta_sum hα hα1 hg hgm hz).symm))


/-- The pointwise bound `HkIntegrand α 4 (f·g) ≤ 10^14 |f|_𝒲² Gmaj`. -/
theorem HkIntegrand_mul_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hf : SmoothInt f) (hg : SmoothNbhd g) (hfm : WlInfMem α 4 f) (hvt : VanishTheta g)
    (hgm : HkMem α 4 g) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ, HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ
      ≤ 10 ^ 14 * (WlInf α 4 f) ^ 2 * Gmaj α g z θ := by
  intro z hz θ hθ
  have hW := WlInf_nonneg hfm
  have hW2 : 0 ≤ (WlInf α 4 f) ^ 2 := sq_nonneg _
  have hHk := HkIntegrand_nonneg α 4 g z θ
  have hγ1 : (0:ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hBtil : ∀ d, 0 ≤ Btil α g d z := fun d => by
    rw [Btil]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' hσ) _)
  have hGmnn : 0 ≤ Gmaj α g z θ := by
    simp only [Gmaj]
    exact add_nonneg hHk (mul_nonneg (mul_nonneg (inv_nonneg.mpr hγ1.le)
      (Finset.sum_nonneg (fun d _ => hBtil d)))
      (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' hθ) _))
        (sq_nonneg _)))
  have hGm : HkIntegrand α 4 g z θ ≤ Gmaj α g z θ := by
    simp only [Gmaj]
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (inv_nonneg.mpr hγ1.le)
      (Finset.sum_nonneg (fun d _ => hBtil d)))
      (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' hθ) _))
        (sq_nonneg _)))
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    have h0 : HkIntegrand α 4 (fun z θ => f z θ * g z θ) 0 θ = 0 := by
      simp [HkIntegrand, w, Wt]
    have h1 : Gmaj α g 0 θ = 0 := by
      simp only [Gmaj]
      rw [show HkIntegrand α 4 g 0 θ = 0 from by simp [HkIntegrand, w, Wt]]
      simp [w, Wt]
    rw [h0, h1]; simp
  · have hsum_z : ∑ i ∈ Finset.range 5,
        (DzIter i (fun z θ => f z θ * g z θ) z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        ≤ 5 * (10 ^ 7 * (WlInf α 4 f) ^ 2 * HkIntegrand α 4 g z θ) := by
      calc ∑ i ∈ Finset.range 5,
            (DzIter i (fun z θ => f z θ * g z θ) z θ
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
          ≤ ∑ i ∈ Finset.range 5, (10 ^ 7 * (WlInf α 4 f) ^ 2 * HkIntegrand α 4 g z θ) :=
            Finset.sum_le_sum (fun i hi =>
              z_term_le hα hf hg hfm (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hz hθ)
        _ = 5 * (10 ^ 7 * (WlInf α 4 f) ^ 2 * HkIntegrand α 4 g z θ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    have hsum_m : ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ 25 * (10 ^ 12 * (WlInf α 4 f) ^ 2 * Gmaj α g z θ) := by
      calc ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
          ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (10 ^ 12 * (WlInf α 4 f) ^ 2 * Gmaj α g z θ) := by
            refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
            by_cases hc : 1 ≤ i ∧ i + j ≤ 4
            · rw [if_pos hc]
              exact m_term_le hα hα1 hf hg hfm hvt hgm hc.1 hc.2 hz hzpos hθ
            · rw [if_neg hc]
              exact mul_nonneg (mul_nonneg (by norm_num) hW2) hGmnn
        _ = 25 * (10 ^ 12 * (WlInf α 4 f) ^ 2 * Gmaj α g z θ) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    rw [HkIntegrand]
    have hcomb : 5 * (10 ^ 7 * (WlInf α 4 f) ^ 2 * HkIntegrand α 4 g z θ)
        + 25 * (10 ^ 12 * (WlInf α 4 f) ^ 2 * Gmaj α g z θ)
        ≤ 10 ^ 14 * (WlInf α 4 f) ^ 2 * Gmaj α g z θ := by
      have hA : (0:ℝ) ≤ (WlInf α 4 f) ^ 2 * HkIntegrand α 4 g z θ := mul_nonneg hW2 hHk
      have hB : (0:ℝ) ≤ (WlInf α 4 f) ^ 2 * Gmaj α g z θ := mul_nonneg hW2 hGmnn
      have hBG : (WlInf α 4 f) ^ 2 * HkIntegrand α 4 g z θ
          ≤ (WlInf α 4 f) ^ 2 * Gmaj α g z θ := mul_le_mul_of_nonneg_left hGm hW2
      nlinarith [hA, hB, hBG]
    linarith [hsum_z, hsum_m, hcomb]

theorem WProductRule : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.Spaces.SmoothInt f → Work.Spaces.SmoothNbhd g →
    Work.Spaces.WlInfMem α 4 f → Work.Spaces.VanishTheta g →
    Work.Spaces.DecayInZ 4 g → Work.Spaces.HkMem α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ) ≤
        C / (Work.Spaces.gam α - 1) * (Work.Spaces.WlInf α 4 f) ^ 2
          * Work.Spaces.HkSq α 4 g := by
  refine ⟨10 ^ 18, by norm_num, ?_⟩
  intro α f g hα hα1 hf hg hfm hvt hdec hgm
  set fg : ℝ → ℝ → ℝ := fun z θ => f z θ * g z θ with hfg
  have hW := WlInf_nonneg hfm
  have hW2 : 0 ≤ (WlInf α 4 f) ^ 2 := sq_nonneg _
  have hγ1 : (0:ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγle : gam α - 1 ≤ 1 := by rw [gam_sub_one]; linarith
  have hfg_sm : ContDiffOn ℝ ⊤ (Function.uncurry fg) quadU := by
    have h1 : ContDiffOn ℝ ⊤ (Function.uncurry f) quadU := hf.1
    have h2 : ContDiffOn ℝ ⊤ (Function.uncurry g) quadU :=
      hg.mono fun p hp => ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩
    have hmul : Function.uncurry fg = Function.uncurry f * Function.uncurry g := rfl
    rw [hmul]; exact h1.mul h2
  have hpbi := HkIntegrand_mul_le hα hα1 hf hg hfm hvt hgm
  have hGθ : ∀ z ∈ Iz, IntegrableOn (fun θ => Gmaj α g z θ) Iθ := fun z hz => by
    have hμw : IntegrableOn (fun θ => (α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) * (w z) ^ 2) Iθ :=
      (integrableOn_angular_weight hα hα1).mul_const _
    have h2 : IntegrableOn (fun θ => ((gam α - 1)⁻¹ * (∑ d ∈ Finset.range 4, Btil α g d z))
        * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
          * (w z) ^ 2)) Iθ := hμw.const_mul _
    simp only [Gmaj]
    exact (hgm.1 z hz).add h2
  have hGint := integrableOn_Gmaj hα hα1 hg hgm
  have hmaj_outer : IntegrableOn
      (fun z => ∫ θ in Iθ, 10 ^ 14 * (WlInf α 4 f) ^ 2 * Gmaj α g z θ) Iz := by
    have heq : (fun z => ∫ θ in Iθ, 10 ^ 14 * (WlInf α 4 f) ^ 2 * Gmaj α g z θ)
        = fun z => 10 ^ 14 * (WlInf α 4 f) ^ 2 * (∫ θ in Iθ, Gmaj α g z θ) := by
      funext z; rw [MeasureTheory.integral_const_mul]
    rw [heq]; exact hGint.const_mul _
  have hmem : HkMem α 4 fg := by
    obtain ⟨hslice_aesm, huncurry_aesm⟩ := aesm_HkIntegrand_quad α fg hfg_sm
    constructor
    · intro z hz
      refine Integrable.mono' ((hGθ z hz).const_mul (10 ^ 14 * (WlInf α 4 f) ^ 2))
        (hslice_aesm z hz) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_of_nonneg (HkIntegrand_nonneg α 4 fg z θ)]
      exact hpbi z hz θ hθ
    · have haesm_int : AEStronglyMeasurable
          (fun z => ∫ θ in Iθ, HkIntegrand α 4 fg z θ) (volume.restrict Iz) := by
        have h := huncurry_aesm.integral_prod_right'
        have : (fun z => ∫ θ, HkIntegrand α 4 fg z θ ∂(volume.restrict Iθ))
            = (fun z => ∫ θ in Iθ, HkIntegrand α 4 fg z θ) := rfl
        rw [← this]; exact h
      refine Integrable.mono' hmaj_outer haesm_int ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_of_nonneg (integral_nonneg fun θ => HkIntegrand_nonneg α 4 fg z θ)]
      exact integral_mono_of_nonneg (Eventually.of_forall fun θ => HkIntegrand_nonneg α 4 fg z θ)
        ((hGθ z hz).const_mul _)
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpbi z hz θ hθ))
  refine ⟨hmem, ?_⟩
  -- The `H^4` estimate
  set K : ℝ := ∫ θ in Iθ, (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)
    with hKdef
  have hK700 : K ≤ 700 := angular_weight_integral_bound hα hα1
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' hθ) _)
  have hbsum_int : ∫ z in Iz, (w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z
      ≤ 4 * HkSq α 4 g := by
    have hsum : (fun z => (w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z)
        = fun z => ∑ d ∈ Finset.range 4, (w z) ^ 2 * Btil α g d z := by
      funext z; rw [Finset.mul_sum]
    rw [hsum]
    have hIntSum := MeasureTheory.integral_finsetSum (μ := volume.restrict Iz)
      (s := Finset.range 4) (f := fun d z => (w z) ^ 2 * Btil α g d z)
      (fun d hd => integrableOn_Btil_w hα hα1 hg hgm (Nat.le_of_lt_succ (Finset.mem_range.mp hd)))
    rw [hIntSum]
    have heach : ∀ d ∈ Finset.range 4, ∫ z in Iz, (w z) ^ 2 * Btil α g d z ≤ HkSq α 4 g := by
      intro d hd
      have hd3 : d ≤ 3 := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
      have heq : (∫ z in Iz, (w z) ^ 2 * Btil α g d z)
          = ∫ z in Iz, ∫ θ in Iθ, (mixed d 1 g z θ * Wt α z θ) ^ 2 := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici
          (fun z hz => wsq_Btil_eq hα hα1 hg d hz)
      rw [heq]
      exact L2Sq_mixed_le_HkSq α 4 g hgm 1 d le_rfl (by omega)
    calc ∑ d ∈ Finset.range 4, ∫ z in Iz, (w z) ^ 2 * Btil α g d z
        ≤ ∑ d ∈ Finset.range 4, HkSq α 4 g := Finset.sum_le_sum (fun d hd => heach d hd)
      _ = 4 * HkSq α 4 g := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  have hbsum_int_nn : 0 ≤ ∫ z in Iz, (w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z :=
    setIntegral_nonneg measurableSet_Ici fun z _ =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun d _ => by
        rw [Btil]
        exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
          mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg' hσ) _)))
  have hGval : (∫ z in Iz, ∫ θ in Iθ, Gmaj α g z θ)
      = HkSq α 4 g + (gam α - 1)⁻¹ * K
          * (∫ z in Iz, (w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z) := by
    have hcongr : ∀ z ∈ Iz, (∫ θ in Iθ, Gmaj α g z θ)
        = (∫ θ in Iθ, HkIntegrand α 4 g z θ) + (gam α - 1)⁻¹ * K
            * ((w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z) := by
      intro z hz
      rw [Gmaj_theta_sum hα hα1 hg hgm hz, hKdef]
    refine (MeasureTheory.setIntegral_congr_fun (s := Iz) measurableSet_Ici hcongr).trans ?_
    rw [MeasureTheory.integral_add hgm.2 ((integrableOn_bSum_w hα hα1 hg hgm).const_mul _),
      MeasureTheory.integral_const_mul, HkSq]
  have step3 : (∫ z in Iz, ∫ θ in Iθ, Gmaj α g z θ)
      ≤ HkSq α 4 g + (gam α - 1)⁻¹ * 700 * (4 * HkSq α 4 g) := by
    rw [hGval]
    have hcoef : 0 ≤ (gam α - 1)⁻¹ := by positivity
    have hHKnn : 0 ≤ HkSq α 4 g := HkSq_nonneg α 4 g
    have h1 : K * (∫ z in Iz, (w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z)
        ≤ 700 * (4 * HkSq α 4 g) :=
      calc K * (∫ z in Iz, (w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z)
          ≤ 700 * (∫ z in Iz, (w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z) :=
            mul_le_mul_of_nonneg_right hK700 hbsum_int_nn
        _ ≤ 700 * (4 * HkSq α 4 g) := mul_le_mul_of_nonneg_left hbsum_int (by norm_num)
    have hm1 : (gam α - 1)⁻¹ * K
        * (∫ z in Iz, (w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z)
        ≤ (gam α - 1)⁻¹ * 700 * (4 * HkSq α 4 g) :=
      calc (gam α - 1)⁻¹ * K
            * (∫ z in Iz, (w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z)
          = (gam α - 1)⁻¹ * (K * (∫ z in Iz, (w z) ^ 2 * ∑ d ∈ Finset.range 4, Btil α g d z)) := by
            ring
        _ ≤ (gam α - 1)⁻¹ * (700 * (4 * HkSq α 4 g)) := mul_le_mul_of_nonneg_left h1 hcoef
        _ = (gam α - 1)⁻¹ * 700 * (4 * HkSq α 4 g) := by ring
    linarith [hm1]
  have step1 : HkSq α 4 fg ≤ ∫ z in Iz, ∫ θ in Iθ,
      10 ^ 14 * (WlInf α 4 f) ^ 2 * Gmaj α g z θ := by
    rw [HkSq]
    refine setIntegral_mono_of_nonneg
      (fun z hz => integral_nonneg fun θ => HkIntegrand_nonneg α 4 fg z θ)
      (fun z hz => integral_mono_of_nonneg
        (Eventually.of_forall fun θ => HkIntegrand_nonneg α 4 fg z θ)
        ((hGθ z hz).const_mul _)
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpbi z hz θ hθ)))
      hmaj_outer
  have step2 : (∫ z in Iz, ∫ θ in Iθ, 10 ^ 14 * (WlInf α 4 f) ^ 2 * Gmaj α g z θ)
      = 10 ^ 14 * (WlInf α 4 f) ^ 2 * (∫ z in Iz, ∫ θ in Iθ, Gmaj α g z θ) := by
    have heq : (fun z => ∫ θ in Iθ, 10 ^ 14 * (WlInf α 4 f) ^ 2 * Gmaj α g z θ)
        = fun z => 10 ^ 14 * (WlInf α 4 f) ^ 2 * (∫ θ in Iθ, Gmaj α g z θ) := by
      funext z; rw [MeasureTheory.integral_const_mul]
    rw [heq, MeasureTheory.integral_const_mul]
  have hfinal : 10 ^ 14 * (WlInf α 4 f) ^ 2
        * (HkSq α 4 g + (gam α - 1)⁻¹ * 700 * (4 * HkSq α 4 g))
      ≤ 10 ^ 18 / (gam α - 1) * (WlInf α 4 f) ^ 2 * HkSq α 4 g := by
    have hHKnn : 0 ≤ HkSq α 4 g := HkSq_nonneg α 4 g
    have hkey : (1:ℝ) + (gam α - 1)⁻¹ * 700 * 4 ≤ 10 ^ 4 / (gam α - 1) := by
      have he : (1:ℝ) + (gam α - 1)⁻¹ * 700 * 4
          = ((gam α - 1) + 2800) / (gam α - 1) := by
        field_simp; ring
      rw [he]
      apply div_le_div_of_nonneg_right _ hγ1.le
      linarith
    have hWHS : 10 ^ 14 * (WlInf α 4 f) ^ 2
          * (HkSq α 4 g + (gam α - 1)⁻¹ * 700 * (4 * HkSq α 4 g))
        = 10 ^ 14 * ((WlInf α 4 f) ^ 2 * HkSq α 4 g)
            * (1 + (gam α - 1)⁻¹ * 700 * 4) := by ring
    have hRHS : 10 ^ 18 / (gam α - 1) * (WlInf α 4 f) ^ 2 * HkSq α 4 g
        = 10 ^ 14 * ((WlInf α 4 f) ^ 2 * HkSq α 4 g) * (10 ^ 4 / (gam α - 1)) := by
      field_simp
    calc 10 ^ 14 * (WlInf α 4 f) ^ 2
          * (HkSq α 4 g + (gam α - 1)⁻¹ * 700 * (4 * HkSq α 4 g))
        = 10 ^ 14 * ((WlInf α 4 f) ^ 2 * HkSq α 4 g)
            * (1 + (gam α - 1)⁻¹ * 700 * 4) := hWHS
      _ ≤ 10 ^ 14 * ((WlInf α 4 f) ^ 2 * HkSq α 4 g) * (10 ^ 4 / (gam α - 1)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 10 ^ 18 / (gam α - 1) * (WlInf α 4 f) ^ 2 * HkSq α 4 g := hRHS.symm
  calc HkSq α 4 fg
      ≤ 10 ^ 14 * (WlInf α 4 f) ^ 2 * (∫ z in Iz, ∫ θ in Iθ, Gmaj α g z θ) :=
        step2 ▸ step1
    _ ≤ 10 ^ 14 * (WlInf α 4 f) ^ 2
          * (HkSq α 4 g + (gam α - 1)⁻¹ * 700 * (4 * HkSq α 4 g)) :=
        mul_le_mul_of_nonneg_left step3 (by positivity)
    _ ≤ 10 ^ 18 / (gam α - 1) * (WlInf α 4 f) ^ 2 * HkSq α 4 g := hfinal

end Work.Spaces
