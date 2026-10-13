import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS_StreamBdry.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB4.psiP_lipschitz`

The `U`-slot part `psiP αG Ψ = -(s2 θ/αG)·∫₀¹ v^{3/αG-1}·U'(Ψ)(zv,θ) dv` of the stream function
inherits the `z`-Lipschitz regularity of the slot `U'(Ψ)` on `Ioc 0 1`, with the sharp constant:

if `|U'(Ψ)(z,θ) - U'(Ψ)(z',θ)| ≤ C·|z - z'|` for `z, z' ∈ (0,1]` and `θ ∈ Iθ`, then

`|psiP(z,θ) - psiP(z',θ)| ≤ (s2 θ · C/(3 + αG))·|z - z'|`.

The engine (lemma `rpow_mul_lip_integral_le` below) is the elementary estimate
`|∫₀¹ v^{p-1}(g(zv) - g(z'v)) dv| ≤ C·|z-z'|/(p+1)` for a `C`-Lipschitz `g` on `Ioc 0 1` and
`p > 0`: extend `g` to a globally Lipschitz `G` (`LipschitzOnWith.extend_real`), so that the
integrands are dominated by `v^{p-1}` and one may apply `integral_sub` and
`norm_integral_le_of_norm_le`; the arithmetic is `∫₀¹ v^p = 1/(p+1)` and
`(s2/αG)·(1/(3/αG + 1)) = s2/(3 + αG)`.
-/

noncomputable section

open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB4

/-- **The integral Lipschitz estimate.**  If `g` is `C`-Lipschitz on `Ioc 0 1` and `p > 0`, then the
parameter-dependent integrals `z ↦ ∫₀¹ v^{p-1}·g(z·v) dv` are Lipschitz with constant
`C/(p+1)` on `Ioc 0 1`. -/
lemma rpow_mul_lip_integral_le {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C) {g : ℝ → ℝ}
    (hg : ∀ x ∈ Set.Ioc 0 1, ∀ y ∈ Set.Ioc 0 1, |g x - g y| ≤ C * |x - y|)
    {z z' : ℝ} (hz : z ∈ Set.Ioc 0 1) (hz' : z' ∈ Set.Ioc 0 1) :
    |(∫ v in (0:ℝ)..1, v ^ (p - 1) * g (z * v))
        - (∫ v in (0:ℝ)..1, v ^ (p - 1) * g (z' * v))|
      ≤ C * |z - z'| / (p + 1) := by
  have hp1 : -1 < p - 1 := by linarith
  have hp1' : -1 < p := by linarith
  set K : ℝ≥0 := Real.toNNReal C with hKdef
  have hK : (K : ℝ) = C := Real.coe_toNNReal C hC
  have hLip : LipschitzOnWith K g (Set.Ioc 0 1) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq, hK]
    exact hg x hx y hy
  -- extend `g` to a globally Lipschitz function, so that the integrands are dominated by `v^{p-1}`
  obtain ⟨G, hGlip, hGeq⟩ := hLip.extend_real
  have hGdiff : ∀ x y : ℝ, |G x - G y| ≤ C * |x - y| := by
    intro x y
    have h := hGlip.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq, hK] at h
    exact h
  have integrable_G : ∀ {w : ℝ},
      IntervalIntegrable (fun v : ℝ => v ^ (p - 1) * G (w * v)) volume 0 1 := by
    intro w
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    refine MeasureTheory.Integrable.mono'
      (g := fun v : ℝ => v ^ (p - 1) * (|G 0| + C * |w|)) ?_ ?_ ?_
    · have h1 : IntervalIntegrable (fun v : ℝ => v ^ (p - 1)) volume 0 1 :=
        intervalIntegral.intervalIntegrable_rpow' hp1
      have h2 : IntervalIntegrable (fun v : ℝ => v ^ (p - 1) * (|G 0| + C * |w|))
          volume 0 1 := h1.mul_const _
      rwa [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h2
    · refine ContinuousOn.aestronglyMeasurable (μ := volume) ?_ measurableSet_Ioc
      refine ContinuousOn.mul ?_ ?_
      · exact fun v hv =>
          (Real.continuousAt_rpow_const v (p - 1) (Or.inl (ne_of_gt hv.1))).continuousWithinAt
      · exact (hGlip.continuous.comp (continuous_const.mul continuous_id)).continuousOn
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun v hv => ?_
      have hv0 : 0 ≤ v := le_of_lt hv.1
      have hrpow : 0 ≤ v ^ (p - 1) := Real.rpow_nonneg hv0 _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow]
      have hb : |G (w * v)| ≤ |G 0| + C * |w| := by
        have h1 : |G (w * v) - G 0| ≤ C * |w * v| := by
          have h := hGdiff (w * v) 0
          simpa using h
        have h2 : |w * v| ≤ |w| := by
          rw [abs_mul]
          calc |w| * |v| ≤ |w| * 1 :=
                mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg hv0]; exact hv.2) (abs_nonneg w)
            _ = |w| := mul_one _
        calc |G (w * v)| = |G (w * v) - G 0 + G 0| := by ring_nf
          _ ≤ |G (w * v) - G 0| + |G 0| := abs_add_le _ _
          _ ≤ C * |w| + |G 0| :=
              add_le_add (le_trans h1 (mul_le_mul_of_nonneg_left h2 hC)) le_rfl
          _ = |G 0| + C * |w| := by ring
      exact mul_le_mul_of_nonneg_left hb hrpow
  have hInt_z := integrable_G (w := z)
  have hInt_z' := integrable_G (w := z')
  have hmem : ∀ v ∈ Set.Ioc 0 1, z * v ∈ Set.Ioc 0 1 := fun v hv =>
    ⟨mul_pos hz.1 hv.1, by nlinarith [hz.1, hz.2, hv.1, hv.2]⟩
  have hmem' : ∀ v ∈ Set.Ioc 0 1, z' * v ∈ Set.Ioc 0 1 := fun v hv =>
    ⟨mul_pos hz'.1 hv.1, by nlinarith [hz'.1, hz'.2, hv.1, hv.2]⟩
  -- replace `g` by its extension `G` in the two integrals
  have hcz : (∫ v in (0:ℝ)..1, v ^ (p - 1) * g (z * v))
      = ∫ v in (0:ℝ)..1, v ^ (p - 1) * G (z * v) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine Filter.Eventually.of_forall fun v hv => ?_
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    have hxv : g (z * v) = G (z * v) := hGeq (hmem v hv)
    rw [hxv]
  have hcz' : (∫ v in (0:ℝ)..1, v ^ (p - 1) * g (z' * v))
      = ∫ v in (0:ℝ)..1, v ^ (p - 1) * G (z' * v) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine Filter.Eventually.of_forall fun v hv => ?_
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
    have hxv : g (z' * v) = G (z' * v) := hGeq (hmem' v hv)
    rw [hxv]
  rw [hcz, hcz', ← intervalIntegral.integral_sub hInt_z hInt_z']
  have hint_g : IntervalIntegrable (fun v : ℝ => C * |z - z'| * v ^ p) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hp1').const_mul _
  have hbound : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Set.Ioc 0 1 →
      ‖v ^ (p - 1) * G (z * v) - v ^ (p - 1) * G (z' * v)‖ ≤ C * |z - z'| * v ^ p := by
    refine Filter.Eventually.of_forall fun v hv => ?_
    have hv0 : 0 ≤ v := le_of_lt hv.1
    have hrpow : 0 ≤ v ^ (p - 1) := Real.rpow_nonneg hv0 _
    rw [Real.norm_eq_abs]
    have hkey : v ^ (p - 1) * G (z * v) - v ^ (p - 1) * G (z' * v)
        = v ^ (p - 1) * (G (z * v) - G (z' * v)) := by ring
    rw [hkey, abs_mul, abs_of_nonneg hrpow]
    have h1 : |G (z * v) - G (z' * v)| ≤ C * |z * v - z' * v| := hGdiff _ _
    have h2 : |z * v - z' * v| = |z - z'| * v := by
      rw [← sub_mul, abs_mul, abs_of_nonneg hv0]
    rw [h2] at h1
    have h3 : v ^ p = v ^ (p - 1) * v := by
      have h := Real.rpow_add_one (x := v) (ne_of_gt hv.1) (p - 1)
      rw [sub_add_cancel] at h
      exact h
    rw [h3]
    calc v ^ (p - 1) * |G (z * v) - G (z' * v)| ≤ v ^ (p - 1) * (C * (|z - z'| * v)) :=
          mul_le_mul_of_nonneg_left h1 hrpow
      _ = C * |z - z'| * (v ^ (p - 1) * v) := by ring
  have hstep : |∫ v in (0:ℝ)..1, (v ^ (p - 1) * G (z * v) - v ^ (p - 1) * G (z' * v))|
      ≤ ∫ v in (0:ℝ)..1, C * |z - z'| * v ^ p := by
    have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := 0) (b := 1)
      (by norm_num) (f := fun v => v ^ (p - 1) * G (z * v) - v ^ (p - 1) * G (z' * v))
      (g := fun v => C * |z - z'| * v ^ p) hbound hint_g
    simpa only [Real.norm_eq_abs] using h
  have hval : (∫ v in (0:ℝ)..1, C * |z - z'| * v ^ p) = C * |z - z'| / (p + 1) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hp1')]
    rw [Real.one_rpow, Real.zero_rpow (by linarith : p + 1 ≠ 0), sub_zero]
    rw [mul_one_div]
  exact hstep.trans (le_of_eq hval)

theorem psiP_lipschitz {αG : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hU : ∀ z ∈ Set.Ioc 0 1, ∀ z' ∈ Set.Ioc 0 1, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.StreamBdryIface.Uprime αG Ψ z θ - Work.FTS.StreamBdryIface.Uprime αG Ψ z' θ|
        ≤ C * |z - z'|) :
    ∃ K : ℝ → NNReal, ∀ θ ∈ Work.Spaces.Iθ,
      (K θ : ℝ) = Work.Construction.s2 θ * C / (3 + αG) ∧
      LipschitzOnWith (K θ) (fun z => Work.FTS.StreamBdryIface.psiP αG Ψ z θ) (Set.Ioc 0 1) := by
  refine ⟨fun θ => Real.toNNReal (Work.Construction.s2 θ * C / (3 + αG)), ?_⟩
  intro θ hθ
  have hs2 : 0 ≤ Work.Construction.s2 θ := by
    rw [Work.Construction.s2_eq]
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hKval : ((Real.toNNReal (Work.Construction.s2 θ * C / (3 + αG))) : ℝ)
      = Work.Construction.s2 θ * C / (3 + αG) := Real.coe_toNNReal _ (by positivity)
  refine ⟨hKval, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro z hz z' hz'
  rw [Real.dist_eq, Real.dist_eq, hKval]
  have hα3 : 0 < 3 / αG := by positivity
  have hkey := rpow_mul_lip_integral_le (p := 3 / αG) (C := C) hα3 hC
    (g := fun v => Work.FTS.StreamBdryIface.Uprime αG Ψ v θ)
    (fun x hx y hy => hU x hx y hy θ hθ) hz hz'
  have hpsi : ∀ w : ℝ, Work.FTS.StreamBdryIface.psiP αG Ψ w θ
      = -(Work.Construction.s2 θ / αG) *
        (∫ v in (0:ℝ)..1, v ^ (3 / αG - 1)
          * Work.FTS.StreamBdryIface.Uprime αG Ψ (w * v) θ) :=
    fun w => Work.FTS_StreamBdry.psiP_eq_Iint αG Ψ w θ
  have hcoef : (0:ℝ) ≤ Work.Construction.s2 θ / αG := by positivity
  set Iz : ℝ := ∫ v in (0:ℝ)..1, v ^ (3 / αG - 1)
    * Work.FTS.StreamBdryIface.Uprime αG Ψ (z * v) θ with hIz
  set Iz' : ℝ := ∫ v in (0:ℝ)..1, v ^ (3 / αG - 1)
    * Work.FTS.StreamBdryIface.Uprime αG Ψ (z' * v) θ with hIz'
  have hkey' : |Iz - Iz'| ≤ C * |z - z'| / (3 / αG + 1) := by
    rw [hIz, hIz']
    exact hkey
  have hfin : (Work.Construction.s2 θ / αG) * (C * |z - z'| / (3 / αG + 1))
      = Work.Construction.s2 θ * C / (3 + αG) * |z - z'| := by
    have hz1 : (3:ℝ) / αG + 1 = (3 + αG) / αG := by
      have hαne : αG ≠ 0 := ne_of_gt hαG
      field_simp
    have h3ne : (3 + αG) ≠ 0 := by positivity
    have hαne : αG ≠ 0 := ne_of_gt hαG
    rw [hz1]
    field_simp
  rw [hpsi z, hpsi z']
  rw [show -(Work.Construction.s2 θ / αG) * Iz - -(Work.Construction.s2 θ / αG) * Iz'
      = -(Work.Construction.s2 θ / αG) * (Iz - Iz') from by ring]
  rw [abs_mul, abs_neg, abs_of_nonneg hcoef]
  exact le_trans (mul_le_mul_of_nonneg_left hkey' hcoef) (le_of_eq hfin)

end Work.FTS_StreamBdry.SB4
