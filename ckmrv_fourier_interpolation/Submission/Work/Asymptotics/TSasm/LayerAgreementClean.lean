import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.paperLayer_agreement
import Submission.Work.HFN.cuspExpansionKernel

/-!
# Clash-free (branch-`KPlusXiDefs` compatible) copy of the cusp-`\pm1` layer agreement

`Work.Asymptotics.layer_agreement_cuspTile` lives in the `MiddleRange` import branch; the tile
seminorm bound `Work.Asymptotics.Tile.tileLayerSeminorm` lives in the `KPlusXiDefs` branch, and the
two branches cannot be imported into one module (they both declare
`Work.Asymptotics.continuous_jInvariantFun`).  This module re-proves the agreement using the
clash-free cusp-expansion input `Submission.Work.HFN.cuspExpansionKernel` (a verbatim copy of
`Submission.Work.Asymptotics.cuspExpansionKernel` whose `MiddleRange` dependencies are shared with
`KPlusXiDefs`), so that the agreement can be combined with the tile seminorm bound.

The inputs copied verbatim from
`Submission/Work/Asymptotics/kernelTransform_eq_zero_d24_tail.lean` are
`Work.Asymptotics.norm_exp_contour`, `Work.Asymptotics.Aexp_expansion_point` (both axiom-clean
there: `Aexp_expansion_point`'s proof only uses `Work.Asymptotics.kernel_axis_bound`) and
`Work.Asymptotics.norm_add_mul_I_ge_of_pair_ne_zeroTS`; from
`Submission/Work/Asymptotics/kernelTransform_eq_zero_d24_small_r.lean` the helper
`Work.Asymptotics.exists_poly_exp_le`; from `Submission/Work/Asymptotics/tail_domination_exp.lean`
the theorem `Work.Asymptotics.tail_domination_exp`; and everything from
`Submission/Work/Asymptotics/layer_agreement_cuspTile.lean` is copied verbatim.
-/
noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology ENNReal

namespace Work.Asymptotics

/-- The modulus of the contour exponential `e^{-πr²t}` (for real `r`, `t`). -/
lemma norm_exp_contour (r t : ℝ) :
    ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ = Real.exp (-(Real.pi * r ^ 2 * t)) := by
  have h : -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = ((-(Real.pi * r ^ 2 * t) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, Complex.norm_exp, Complex.ofReal_re]

/-- **The cusp-`i∞` expansion at a single point, with no fundamental-domain restriction.**
Instantiation of the (proved) `kernel_axis_bound` at `K = {τ}`: for fixed `τ` the cusp threshold
`max {Im w : w ∈ SL(2,ℤ)·τ}` is finite, so the expansion of `z ↦ K^{(24)}(τ,z)` at `i∞` applies
at every `τ : ℍ`. -/
theorem Aexp_expansion_point (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    ∃ C M T : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  obtain ⟨C, M, T, hC, hM, hT, hb⟩ :=
    Work.HFN.kernel_axis_bound ℓ 24 (Or.inr rfl) (K := {τ}) isCompact_singleton
  exact ⟨C, M, T, hC, hM, le_of_lt hT,
    fun t ht => hb τ (Set.mem_singleton τ) t ht⟩



/-- **The `e^{2πt}`-part never decays under the pair gate.**  If `(a, b) ≠ (0, 0)` then
`t ↦ ‖a + it·b‖` is bounded below by a positive constant on a tail: if `b ≠ 0` the linear term
`t‖b‖` dominates, and if `b = 0` then `a ≠ 0`.  This is the estimate that converts the pair gate
`(G_{1,0}, G_{1,1}) ≠ (0,0)` into the exponential lower bound on the kernel. -/
lemma norm_add_mul_I_ge_of_pair_ne_zeroTS (a b : ℂ) (h : (a, b) ≠ (0, 0)) :
    ∃ c : ℝ, 0 < c ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t → c ≤ ‖a + (t : ℂ) * Complex.I * b‖ := by
  by_cases hb : b = 0
  · have ha : a ≠ 0 := fun ha => h (by simp [ha, hb])
    refine ⟨‖a‖ / 2, by positivity, 0, fun t _ => ?_⟩
    have : a + (t : ℂ) * Complex.I * b = a := by rw [hb]; ring
    rw [this]
    linarith [norm_pos_iff.mpr ha]
  · have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
    refine ⟨‖b‖ / 2, by positivity, (‖a‖ + ‖b‖) / ‖b‖, fun t ht => ?_⟩
    have htnn : 0 ≤ t := le_trans (by positivity) ht
    have hnorm : ‖(t : ℂ) * Complex.I * b‖ = t * ‖b‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg htnn]
    have hkey : ‖(t : ℂ) * Complex.I * b‖ - ‖a‖ ≤ ‖a + (t : ℂ) * Complex.I * b‖ := by
      have := norm_sub_norm_le ((t : ℂ) * Complex.I * b) (-a)
      simpa [sub_neg_eq_add, add_comm, norm_neg] using this
    have htb : ‖a‖ + ‖b‖ ≤ t * ‖b‖ := by
      rw [div_le_iff₀ hbpos] at ht
      linarith [ht]
    rw [hnorm] at hkey
    linarith




/-- **Polynomials are dominated by exponentials on a tail.**  For `δ > 0` there is `T` with
`K (1+t)^N e^{-δt} ≤ c` for `t ≥ T`. -/
lemma exists_poly_exp_le (K N δ c : ℝ) (_hN : 0 ≤ N) (hK : 0 < K) (hδ : 0 < δ) (hc : 0 < c) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → K * (1 + t) ^ N * Real.exp (-(δ * t)) ≤ c := by
  set n : ℕ := Nat.ceil N with hn
  have hNn : N ≤ (n : ℝ) := Nat.le_ceil N
  have hlit : (fun x : ℝ => x ^ n) =o[atTop] (fun x : ℝ => Real.exp ((δ/4) * x)) :=
    isLittleO_pow_exp_pos_mul_atTop n (by positivity)
  have hev1 : ∀ᶠ x : ℝ in atTop, x ^ n ≤ Real.exp ((δ/4) * x) := by
    filter_upwards [hlit.def one_pos, eventually_ge_atTop (0:ℝ)] with x hx hx0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (pow_nonneg hx0 n),
      abs_of_nonneg (Real.exp_nonneg _)] at hx
    exact hx
  have hcomp : Tendsto (fun t : ℝ => Real.exp (-((3*δ/4) * t))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by positivity))
  have hev2 : ∀ᶠ t : ℝ in atTop, Real.exp (-((3*δ/4) * t)) ≤ c / (K * Real.exp (δ/4)) :=
    hcomp.eventually_le_const (by positivity)
  have hshift : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_id
  have hev3 : ∀ᶠ t : ℝ in atTop, (1 + t) ^ n ≤ Real.exp ((δ/4) * (1 + t)) :=
    hshift.eventually hev1
  have hevall : ∀ᶠ t : ℝ in atTop,
      ((1 + t) ^ n ≤ Real.exp ((δ/4) * (1 + t))) ∧
      (Real.exp (-((3*δ/4) * t)) ≤ c / (K * Real.exp (δ/4))) := hev3.and hev2
  obtain ⟨T, hT⟩ := eventually_atTop.1 hevall
  refine ⟨max T 0, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hT t (le_trans (le_max_left T 0) ht)
  have ht0 : (0:ℝ) ≤ t := le_trans (le_max_right T 0) ht
  have hbase : (1:ℝ) ≤ 1 + t := by linarith
  have hstep : (1 + t) ^ N ≤ (1 + t) ^ n := by
    rw [← Real.rpow_natCast (1 + t) n]
    exact Real.rpow_le_rpow_of_exponent_le hbase hNn
  have hexp : K * Real.exp ((δ/4) * (1 + t)) * Real.exp (-(δ * t))
      = K * Real.exp (δ/4) * Real.exp (-((3*δ/4) * t)) := by
    rw [mul_assoc, ← Real.exp_add,
      show (δ/4)*(1+t) + -(δ*t) = δ/4 + -((3*δ/4)*t) by ring, Real.exp_add]
    ring
  calc K * (1 + t) ^ N * Real.exp (-(δ * t))
      ≤ K * (1 + t) ^ n * Real.exp (-(δ * t)) := by
        have h := mul_le_mul_of_nonneg_left hstep hK.le
        exact mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
    _ ≤ K * Real.exp ((δ/4) * (1 + t)) * Real.exp (-(δ * t)) := by
        have h := mul_le_mul_of_nonneg_left h1 hK.le
        exact mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
    _ = K * Real.exp (δ/4) * Real.exp (-((3*δ/4) * t)) := hexp
    _ ≤ K * Real.exp (δ/4) * (c / (K * Real.exp (δ/4))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = c := by field_simp

/-- **Exponential beats polynomial (domination ingredient of the `d = 24` tail assembly).**
For `K > 0`, `N ≥ 0`, `c > 0` and a real `b` with `2π + b > 0`, there is a tail on which
`K * (1 + t) ^ N * Real.exp (-(b * t)) ≤ Real.exp (2 * Real.pi * t) * c`, i.e.
`K (1+t)^N ≤ exp((2π + b) t) c`.  (The rate hypothesis `2π + b > 0` is necessary: with `b = -2π`
the right-hand side is the constant `c` and the claim fails for `N ≥ 1`; it holds in the intended
use `b = π`.)  With `b = π` this is the only analytic input missing from the assembly
`kernelTransform_eq_zero_d24_of_cusp_ne_zero`: it dominates both `‖G₀₀‖ + t‖G₀₁‖`
(`K = ‖G₀₀‖+‖G₀₁‖`, `N = 1`) and the error `C(1+t)^M e^{-πt}` of `Aexp_expansion_point` by
`e^{2πt}·c/4`, after which `norm_add_mul_I_ge_of_pair_ne_zeroTS` and
`kernelTransform_eq_zero_of_exp_lower` finish the job.

Route: `(fun t => (1+t)^N) =O[atTop] (fun t => t^N)` and `(fun t => t^N) =o[atTop]
(fun t => Real.exp ((2π+b)/2 * t))` (rpow-vs-exp), hence eventually
`K (1+t)^N ≤ exp((2π+b)/2 * t)`; then `exp((2π+b)/2 * t) ≤ exp((2π+b) * t) * c` eventually;
combine with `Filter.Eventually` / `eventually_atTop`. -/
theorem tail_domination_exp (K N : ℝ) (hK : 0 < K) (hN : 0 ≤ N) (b c : ℝ) (hc : 0 < c)
    (hb : 0 < 2 * Real.pi + b) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      K * (1 + t) ^ N * Real.exp (-(b * t)) ≤ Real.exp (2 * Real.pi * t) * c := by
  set a : ℝ := 2 * Real.pi + b with ha_def
  have ha : 0 < a := hb
  have ha2 : 0 < a / 2 := by linarith
  -- Polynomial growth is `o` of the exponential of half the rate.
  have hO : (fun x : ℝ => x ^ N) =o[atTop] (fun x : ℝ => Real.exp ((a / 2) * x)) :=
    isLittleO_rpow_exp_pos_mul_atTop N ha2
  have hbound := hO.bound one_pos
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp hbound
  have hpoly : ∀ x : ℝ, max X₁ 0 ≤ x → x ^ N ≤ Real.exp ((a / 2) * x) := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hx
    have h1 : ‖x ^ N‖ ≤ 1 * ‖Real.exp ((a / 2) * x)‖ :=
      hX₁ x (le_trans (le_max_left _ _) hx)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0 N),
        Real.norm_of_nonneg (Real.exp_pos _).le, one_mul] at h1
    exact h1
  -- Eventually the exponential of half the rate dominates the constant `K * 2^N / c`.
  have hlin : Tendsto (fun t : ℝ => Real.exp ((a / 2) * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ha2)
  obtain ⟨X₃, hX₃⟩ := eventually_atTop.mp (hlin.eventually_ge_atTop (K * 2 ^ N / c))
  refine ⟨max (max X₁ 0) (max 1 X₃), ?_⟩
  intro t ht
  have ht1 : (1 : ℝ) ≤ t :=
    le_trans (le_max_left 1 X₃) (le_trans (le_max_right (max X₁ 0) (max 1 X₃)) ht)
  have htx1 : max X₁ 0 ≤ t := le_trans (le_max_left (max X₁ 0) (max 1 X₃)) ht
  have htx3 : X₃ ≤ t :=
    le_trans (le_max_right 1 X₃) (le_trans (le_max_right (max X₁ 0) (max 1 X₃)) ht)
  have htN : t ^ N ≤ Real.exp ((a / 2) * t) := hpoly t htx1
  have ht0 : 0 ≤ t := by linarith
  have hexpnn : 0 ≤ Real.exp ((a / 2) * t) := (Real.exp_pos _).le
  have hK2 : K * 2 ^ N ≤ c * Real.exp ((a / 2) * t) := by
    have h := (div_le_iff₀ hc).mp (hX₃ t htx3)
    rw [mul_comm (Real.exp ((a / 2) * t)) c] at h
    exact h
  -- `(1+t)^N ≤ 2^N t^N` on the tail `t ≥ 1`.
  have hpow : (1 + t) ^ N ≤ 2 ^ N * t ^ N := by
    have h1 : 0 ≤ 1 + t := by linarith
    have h2 : 1 + t ≤ 2 * t := by linarith
    have h3 : (1 + t) ^ N ≤ (2 * t) ^ N := Real.rpow_le_rpow h1 h2 hN
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht0] at h3
    exact h3
  have hstep1 : K * (1 + t) ^ N ≤ (K * 2 ^ N) * t ^ N := by
    have h := mul_le_mul_of_nonneg_left hpow hK.le
    rwa [← mul_assoc] at h
  have hstep2 : (K * 2 ^ N) * t ^ N ≤
      (c * Real.exp ((a / 2) * t)) * Real.exp ((a / 2) * t) :=
    mul_le_mul hK2 htN (Real.rpow_nonneg ht0 N) (mul_nonneg hc.le hexpnn)
  have hEq : (c * Real.exp ((a / 2) * t)) * Real.exp ((a / 2) * t) = c * Real.exp (a * t) := by
    rw [mul_assoc, ← Real.exp_add, show (a / 2) * t + (a / 2) * t = a * t by ring]
  have hmain : K * (1 + t) ^ N ≤ c * Real.exp (a * t) :=
    le_trans hstep1 (le_trans hstep2 (le_of_eq hEq))
  -- Multiply by `exp (-(b*t))` and identify the two sides.
  have hfin : K * (1 + t) ^ N * Real.exp (-(b * t)) ≤
      c * Real.exp (a * t) * Real.exp (-(b * t)) :=
    mul_le_mul_of_nonneg_right hmain (Real.exp_pos _).le
  have hRHS : c * Real.exp (a * t) * Real.exp (-(b * t)) = Real.exp (2 * Real.pi * t) * c := by
    have harg : a * t + (-(b * t)) = 2 * Real.pi * t := by rw [ha_def]; ring
    rw [mul_assoc, ← Real.exp_add, harg]
    exact mul_comm _ _
  rw [hRHS] at hfin
  exact hfin


/-! ## Non-integrability of the contour integrand from an exponential lower bound

This is the norm argument inside `Work.Asymptotics.kernelTransform_eq_zero_of_exp_lower`,
isolated in the form needed below (non-integrability rather than the junk value `0`). -/

lemma not_integrableOn_kernelIntegrand_of_exp_lower {K : UpperHalfPlane → UpperHalfPlane → ℂ}
    {r : ℝ} (hr : r ≠ 0) (hr2 : r ^ 2 ≤ 2) {τ : UpperHalfPlane} {c T : ℝ} (hc : 0 < c)
    (h : ∀ t : ℝ, T ≤ t → c * Real.exp (2 * Real.pi * t) ≤ ‖Work.Kernels.Kaxis K τ t‖) :
    ¬ MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis K τ t *
      Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) := by
  set f : ℝ → ℂ := fun t => Work.Kernels.Kaxis K τ t *
    Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hf
  intro hint
  set T' : ℝ := max T 0 with hT'
  have hT'0 : 0 ≤ T' := le_max_right _ _
  have hfin : (∫⁻ t, ‖f t‖₊ ∂(volume.restrict (Set.Ioi (0 : ℝ)))) < ∞ := hint.2
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioi T')), (ENNReal.ofReal c) ≤ ‖f t‖₊ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htT : T ≤ t := le_trans (le_max_left T (0 : ℝ)) (Set.mem_Ioi.mp ht).le
    have ht0 : 0 ≤ t := le_trans hT'0 (Set.mem_Ioi.mp ht).le
    have h1 := h t htT
    have h5 : (1 : ℝ) ≤ Real.exp (Real.pi * (2 - r ^ 2) * t) := by
      rw [Real.one_le_exp_iff]
      have h6 : 0 ≤ 2 - r ^ 2 := by linarith
      positivity
    have hsum : Real.exp (Real.pi * (2 - r ^ 2) * t)
        = Real.exp (2 * Real.pi * t) * Real.exp (-(Real.pi * r ^ 2 * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 : c * Real.exp (2 * Real.pi * t) * Real.exp (-(Real.pi * r ^ 2 * t))
        ≤ ‖Work.Kernels.Kaxis K τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t)) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    have h2 : c ≤ ‖Work.Kernels.Kaxis K τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t)) := by
      calc c = c * 1 := (mul_one c).symm
        _ ≤ c * (Real.exp (2 * Real.pi * t) * Real.exp (-(Real.pi * r ^ 2 * t))) := by
            rw [← hsum]
            exact mul_le_mul_of_nonneg_left h5 hc.le
        _ = c * Real.exp (2 * Real.pi * t) * Real.exp (-(Real.pi * r ^ 2 * t)) := by ring
        _ ≤ ‖Work.Kernels.Kaxis K τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t)) := h3
    have hnorm : ‖f t‖ = ‖Work.Kernels.Kaxis K τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t)) := by
      rw [hf, norm_mul, norm_exp_contour]
    rw [show ‖f t‖₊ = ENNReal.ofReal ‖f t‖ from by rw [← enorm_eq_nnnorm, ofReal_norm]]
    exact ENNReal.ofReal_le_ofReal (by rw [hnorm]; exact h2)
  have hmono : (∫⁻ _t : ℝ, (ENNReal.ofReal c) ∂(volume.restrict (Set.Ioi T')))
      ≤ ∫⁻ t : ℝ, ‖f t‖₊ ∂(volume.restrict (Set.Ioi 0)) := by
    calc (∫⁻ _t : ℝ, (ENNReal.ofReal c) ∂(volume.restrict (Set.Ioi T')))
        ≤ ∫⁻ t : ℝ, ‖f t‖₊ ∂(volume.restrict (Set.Ioi T')) := lintegral_mono_ae hbound
      _ ≤ ∫⁻ t : ℝ, ‖f t‖₊ ∂(volume.restrict (Set.Ioi 0)) :=
            lintegral_mono_set (fun t ht => lt_of_le_of_lt hT'0 (Set.mem_Ioi.mp ht))
  have htop : (∫⁻ _t : ℝ, (ENNReal.ofReal c) ∂(volume.restrict (Set.Ioi T'))) = ⊤ := by
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Ioi]
    exact ENNReal.mul_top (by simpa using (ENNReal.ofReal_pos.mpr hc).ne')
  have htop_le : (⊤ : ENNReal) ≤ ∫⁻ t : ℝ, ‖f t‖₊ ∂(volume.restrict (Set.Ioi 0)) :=
    le_of_eq_of_le htop.symm hmono
  exact absurd (lt_of_le_of_lt htop_le hfin) (lt_irrefl ⊤)

/-! ## The exponential growth of the kernel under the pair gate

This is the growth derivation inside `Work.Asymptotics.kernelTransform_eq_zero_d24_of_pair_ne_zero`,
isolated as a statement about the kernel alone. -/

/-- **Growth `e^{2πt}` on a tail from the pair gate.**  If the two leading cusp coefficients of
the dimension-`24` kernel at `τ` do not vanish simultaneously, then `‖K^{(24)}(τ,it)‖ ≥ c e^{2πt}`
on a tail. -/
lemma exists_exp_lower_of_pair_ne_zero (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane)
    (hgate : (Work.Asymptotics.Gcusp ℓ 24 1 0 τ, Work.Asymptotics.Gcusp ℓ 24 1 1 τ) ≠ (0, 0)) :
    ∃ c : ℝ, 0 < c ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      c * Real.exp (2 * Real.pi * t) ≤ ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t‖ := by
  obtain ⟨C, M, T, hC, hM, hT, hbd⟩ := Aexp_expansion_point ℓ τ
  obtain ⟨c, hc, T₁, hc₁⟩ :=
    norm_add_mul_I_ge_of_pair_ne_zeroTS (Work.Asymptotics.Gcusp ℓ 24 1 0 τ)
      (Work.Asymptotics.Gcusp ℓ 24 1 1 τ) hgate
  obtain ⟨Ta, hTa⟩ := exists_poly_exp_le (4 * (‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ‖
      + ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖ + 1) / c) 1 (2 * Real.pi) 1
    (by norm_num) (by positivity) (by positivity) (by norm_num)
  obtain ⟨Tb, hTb⟩ := exists_poly_exp_le (4 * C / c) M (3 * Real.pi) 1
    hM (by positivity) (by positivity) (by norm_num)
  refine ⟨c / 2, by positivity, max (max T T₁) (max Ta Tb), ?_⟩
  intro t ht
  have htT : T ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htT₁ : T₁ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htTa : Ta ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htTb : Tb ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht0 : 0 ≤ t := le_trans hT htT
  -- the two "dominated by `e^{2πt} c/4`" facts
  have hA' : ‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ‖ + t * ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖
      ≤ Real.exp (2 * Real.pi * t) * (c / 4) := by
    have h1 : ‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ‖ + t * ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖
        ≤ (‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ‖ + ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖ + 1)
          * (1 + t) := by
      nlinarith [norm_nonneg (Work.Asymptotics.Gcusp ℓ 24 0 0 τ),
        norm_nonneg (Work.Asymptotics.Gcusp ℓ 24 0 1 τ), ht0]
    have hA0 : (4 * (‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ‖
        + ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖ + 1) / c) * (1 + t)
        * Real.exp (-(2 * Real.pi * t)) ≤ 1 := by
      simpa [Real.rpow_one] using hTa t htTa
    have hmul := mul_le_mul_of_nonneg_right hA0
      (by positivity : (0:ℝ) ≤ c / 4 * Real.exp (2 * Real.pi * t))
    have hid : (4 * (‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ‖
        + ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖ + 1) / c) * (1 + t)
        * Real.exp (-(2 * Real.pi * t)) * (c / 4 * Real.exp (2 * Real.pi * t))
        = (‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ‖ + ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖ + 1)
          * (1 + t) := by
      have h1 : Real.exp (-(2 * Real.pi * t)) * Real.exp (2 * Real.pi * t) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have h2 : (4 * (‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ‖
          + ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖ + 1) / c) * (c / 4)
          = ‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ‖ + ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖ + 1 := by
        field_simp
      calc (4 * (‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ‖
              + ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖ + 1) / c) * (1 + t)
            * Real.exp (-(2 * Real.pi * t)) * (c / 4 * Real.exp (2 * Real.pi * t))
          = (4 * (‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ‖
              + ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖ + 1) / c) * (c / 4)
            * ((1 + t) * (Real.exp (-(2 * Real.pi * t)) * Real.exp (2 * Real.pi * t))) := by
              ring
        _ = (‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ‖ + ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖ + 1)
            * (1 + t) := by rw [h1, h2]; ring
    rw [hid, one_mul] at hmul
    linarith
  have hB' : C * (1 + t) ^ M * Real.exp (-(Real.pi * t))
      ≤ Real.exp (2 * Real.pi * t) * (c / 4) := by
    have hB0 : (4 * C / c) * (1 + t) ^ M * Real.exp (-(3 * Real.pi * t)) ≤ 1 := hTb t htTb
    have hmul := mul_le_mul_of_nonneg_right hB0
      (by positivity : (0:ℝ) ≤ c / 4 * Real.exp (3 * Real.pi * t))
    have hid : (4 * C / c) * (1 + t) ^ M * Real.exp (-(3 * Real.pi * t))
        * (c / 4 * Real.exp (3 * Real.pi * t)) = C * (1 + t) ^ M := by
      have h1 : Real.exp (-(3 * Real.pi * t)) * Real.exp (3 * Real.pi * t) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have h2 : (4 * C / c) * (c / 4) = C := by field_simp
      calc (4 * C / c) * (1 + t) ^ M * Real.exp (-(3 * Real.pi * t))
            * (c / 4 * Real.exp (3 * Real.pi * t))
          = (4 * C / c) * (c / 4)
            * ((1 + t) ^ M * (Real.exp (-(3 * Real.pi * t)) * Real.exp (3 * Real.pi * t))) := by
              ring
        _ = C * (1 + t) ^ M := by rw [h1, h2]; ring
    rw [hid, one_mul] at hmul
    calc C * (1 + t) ^ M * Real.exp (-(Real.pi * t))
        ≤ c / 4 * Real.exp (3 * Real.pi * t) * Real.exp (-(Real.pi * t)) :=
          mul_le_mul_of_nonneg_right hmul (Real.exp_nonneg _)
      _ = Real.exp (2 * Real.pi * t) * (c / 4) := by
          rw [mul_assoc, ← Real.exp_add,
            show 3 * Real.pi * t + -(Real.pi * t) = 2 * Real.pi * t by ring]
          ring
  -- the exponential lower bound
  have hlead := hc₁ t htT₁
  have hnorm1 : ‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ
      + ((t : ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖
      ≤ ‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ‖ + t * ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0]
  have hnorm2 : ‖Complex.exp (2 * Real.pi * t) * (Work.Asymptotics.Gcusp ℓ 24 1 0 τ
      + ((t : ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 1 1 τ)‖
      = Real.exp (2 * Real.pi * t) * ‖Work.Asymptotics.Gcusp ℓ 24 1 0 τ
          + ((t : ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 1 1 τ‖ := by
    rw [norm_mul, Complex.norm_exp]
    congr 1
    simp
  have hB : Real.exp (2 * Real.pi * t) * c
      ≤ ‖Complex.exp (2 * Real.pi * t) * (Work.Asymptotics.Gcusp ℓ 24 1 0 τ
          + ((t : ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 1 1 τ)‖ := by
    rw [hnorm2]
    exact mul_le_mul_of_nonneg_left hlead (Real.exp_nonneg _)
  have hAB : ‖Complex.exp (2 * Real.pi * t) * (Work.Asymptotics.Gcusp ℓ 24 1 0 τ
        + ((t : ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 1 1 τ)‖
      - ‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ
          + ((t : ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖
      ≤ ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t‖ := by
    have h := norm_add_le (Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t)
      (-(Work.Asymptotics.Gcusp ℓ 24 0 0 τ
        + ((t : ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 0 1 τ))
    have heq : Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t
        + -(Work.Asymptotics.Gcusp ℓ 24 0 0 τ
          + ((t : ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 0 1 τ)
        = Complex.exp (2 * Real.pi * t) * (Work.Asymptotics.Gcusp ℓ 24 1 0 τ
          + ((t : ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 1 1 τ) := by
      simp only [Work.Asymptotics.Aexp]; ring
    rw [heq] at h
    linarith [h, norm_neg (Work.Asymptotics.Gcusp ℓ 24 0 0 τ
      + ((t : ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 0 1 τ)]
  have hb := hbd t htT
  have hD : ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t
      - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t‖
      ≤ Real.exp (2 * Real.pi * t) * (c / 4) := by
    rw [norm_sub_rev]
    exact le_trans hb hB'
  have hKA : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t‖
      ≥ ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t‖
        - ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t
            - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t‖ := by
    have h := norm_add_le (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t)
      (Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t
        - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t)
    simp only [add_sub_cancel] at h
    linarith [h]
  have hgoal : c / 2 * Real.exp (2 * Real.pi * t)
      ≤ ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t‖ := by
    have h2 : Real.exp (2 * Real.pi * t) * c / 2
        = c / 2 * Real.exp (2 * Real.pi * t) := by ring
    rw [← h2]
    linarith [hKA, hAB, hB, hnorm1, hA', hD]
  exact hgoal

/-! ## Integrability of the `Aexp` tail from convergence of the contour integral -/

/-- **The `Aexp` tail converges whenever the contour integral does.**  If
`t ↦ K^{(d)}(τ,it)e^{-πr²t}` is integrable on `(0,∞)`, then so is its non-decaying part
`t ↦ Aexp (Gcusp ℓ d) τ t · e^{-πr²t}` on `(1,∞)`.

Indeed, writing `L = πr²` and `Mu = L - 2π`, the `Aexp`-tail splits as `P + Q` with
`P = (G_{0,0} + it G_{0,1})e^{-Lt}` (always integrable, `L > 0`) and
`Q = (G_{1,0} + it G_{1,1})e^{-Mu t}`.  If the `Aexp` tail were not integrable then `Q` would not
be either, hence `Mu ≤ 0` (so `r² ≤ 2`) and `(G_{1,0}, G_{1,1}) ≠ (0,0)`.  This forces `d = 24`,
and the pair gate together with the (unconditional) cusp expansion `Aexp_expansion_point` gives
`‖K^{(24)}(τ,it)‖ ≥ c e^{2πt}` on a tail; then `‖Kaxis e^{-πr²t}‖ ≥ c e^{(2π-L)t} ≥ c` on a tail of
infinite measure, so the contour integrand is not integrable — contradicting the hypothesis. -/
lemma integrableOn_Aexp_of_contour_integrable (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (r : ℝ) (hr : r ≠ 0)
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      Aexp (Gcusp ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 1) := by
  set L : ℝ := Real.pi * r ^ 2 with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  set Mu : ℝ := L - 2 * Real.pi with hMu
  have hargE : ∀ t : ℝ, Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    intro t
    congr 1
    rw [hL]; push_cast; ring
  set P : ℝ → ℂ := fun t => (Gcusp ℓ d 0 0 τ + (t : ℂ) * Complex.I * Gcusp ℓ d 0 1 τ)
      * Complex.exp (-(L : ℂ) * (t : ℂ)) with hP
  set Q : ℝ → ℂ := fun t => (Gcusp ℓ d 1 0 τ + (t : ℂ) * Complex.I * Gcusp ℓ d 1 1 τ)
      * Complex.exp (-(Mu : ℂ) * (t : ℂ)) with hQ
  have hAe_eq : ∀ t : ℝ, Aexp (Gcusp ℓ d) τ t * Complex.exp (-(L : ℂ) * (t : ℂ)) = P t + Q t := by
    intro t
    have hexp : Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))
        = Complex.exp (-(Mu : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hMu, hL]
      push_cast
      ring
    simp only [Aexp, hP, hQ]
    rw [add_mul, add_mul]
    rw [show (Complex.exp (2 * Real.pi * t) * (Gcusp ℓ d 1 0 τ + (t : ℂ) * Complex.I * Gcusp ℓ d 1 1 τ))
          * Complex.exp (-(L : ℂ) * (t : ℂ))
        = (Gcusp ℓ d 1 0 τ + (t : ℂ) * Complex.I * Gcusp ℓ d 1 1 τ)
          * (Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))) from by ring,
      hexp]
  have hPint : IntegrableOn P (Set.Ioi 1) := by
    rw [hP]
    exact integrableOn_affine_mul_exp_neg_mul_complex L hLpos _ _
  have key : IntegrableOn (fun t : ℝ => Aexp (Gcusp ℓ d) τ t
      * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi 1) := by
    by_cases hMu_pos : 0 < Mu
    · have hQint : IntegrableOn Q (Set.Ioi 1) := by
        rw [hQ]
        exact integrableOn_affine_mul_exp_neg_mul_complex Mu hMu_pos _ _
      refine IntegrableOn.congr_fun (hPint.add hQint) (fun t _ => ?_) measurableSet_Ioi
      rw [hAe_eq t, Pi.add_apply]
    · have hMu_nonpos : Mu ≤ 0 := not_lt.mp hMu_pos
      by_cases hpair : (Gcusp ℓ d 1 0 τ, Gcusp ℓ d 1 1 τ) = (0, 0)
      · have hQzero : Q = fun _ => (0 : ℂ) := by
          funext t
          rw [hQ]
          have h10 : Gcusp ℓ d 1 0 τ = 0 := congrArg Prod.fst hpair
          have h11 : Gcusp ℓ d 1 1 τ = 0 := congrArg Prod.snd hpair
          rw [h10, h11]
          simp
        have hQint : IntegrableOn Q (Set.Ioi 1) := by
          rw [hQzero]
          exact integrable_zero ℝ ℂ _
        refine IntegrableOn.congr_fun (hPint.add hQint) (fun t _ => ?_) measurableSet_Ioi
        rw [hAe_eq t, Pi.add_apply]
      · exfalso
        have hd24 : d = 24 := by
          rcases hd with h8 | h24
          · exact absurd (by
              have h10 : Gcusp ℓ d 1 0 τ = 0 := by rw [h8]; simp [Gcusp, Gcusp8]
              have h11 : Gcusp ℓ d 1 1 τ = 0 := by rw [h8]; simp [Gcusp, Gcusp8]
              rw [h10, h11]) hpair
          · exact h24
        have hgate : (Gcusp ℓ 24 1 0 τ, Gcusp ℓ 24 1 1 τ) ≠ (0, 0) := by
          rw [← hd24]
          exact hpair
        obtain ⟨c, hc, T, hgr⟩ := exists_exp_lower_of_pair_ne_zero ℓ τ hgate
        have hr2 : r ^ 2 ≤ 2 := by
          have hle : L ≤ 2 * Real.pi := by
            have h0 := hMu_nonpos
            rw [hMu] at h0
            linarith
          rw [hL] at hle
          have hp := Real.pi_pos
          nlinarith [hle, hp]
        have hni := not_integrableOn_kernelIntegrand_of_exp_lower
          (K := Work.Kernels.Kfun ℓ 24) hr hr2 hc hgr
        rw [hd24] at hint
        exact hni hint
  refine IntegrableOn.congr_fun key (fun t _ => ?_) measurableSet_Ioi
  rw [hargE t]

/-! ## The general agreement lemma (no tail or flatness hypotheses) -/

/-- **The layer is the naive contour integral, given convergence of both.**  If the contour
integrand `t ↦ K(τ,it)e^{-πr²t}` is integrable on `(0,∞)` and the `Aexp` tail
`t ↦ Aexp G τ t · e^{-πr²t}` is integrable on `(1,∞)`, then the CKMRV layer
`paperLayer G ℓ d τ r = layerLow + layerTrunc + highPart` equals
`kernelTransform K τ r = sinSq r ∫_0^∞ K(τ,it)e^{-πr²t}dt`.

The proof is the telescoping `∫_0^∞ = ∫_0^1 + ∫_1^∞ = ∫_0^1 + ∫_1^∞(K - A) + ∫_1^∞ A` together
with the closed form of `∫_1^∞ A(τ,it)e^{-πr²t}dt`, which is `highPart`. -/
theorem paperLayer_eq_kernelTransform_of_integrable
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) (r : ℝ) (hr : r ≠ 0)
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0))
    (hAexp : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Aexp G τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 1)) :
    paperLayer G ℓ d τ r = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r := by
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  set L : ℝ := Real.pi * r ^ 2 with hL
  set Mu : ℝ := L - 2 * Real.pi with hMu
  have hLpos : 0 < L := by rw [hL]; positivity
  have hLne : L ≠ 0 := hLpos.ne'
  have hcosL : sinSq r = ((2 - 2 * Real.cos L : ℝ) : ℂ) := by
    rw [sinSq_eq_two_sub_two_cos r, hL]
  have hcosMu : sinSq r = ((2 - 2 * Real.cos Mu : ℝ) : ℂ) := by
    have h : Real.cos Mu = Real.cos (Real.pi * r ^ 2 - 2 * Real.pi) := by rw [hMu, hL]
    rw [sinSq_eq_two_sub_two_cos_sub r, h]
  set F : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hF
  have hargE : ∀ t : ℝ, Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    intro t
    congr 1
    rw [hL]; push_cast; ring
  have hF_eq : F = fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    funext t
    simp only [hF]
    rw [hargE t]
  have hAeq : (fun t : ℝ => Aexp G τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = fun t : ℝ => Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    funext t
    rw [hargE t]
  set P : ℝ → ℂ := fun t => (G 0 0 τ + (t : ℂ) * Complex.I * G 0 1 τ)
      * Complex.exp (-(L : ℂ) * (t : ℂ)) with hP
  set Q : ℝ → ℂ := fun t => (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
      * Complex.exp (-(Mu : ℂ) * (t : ℂ)) with hQ
  have hAe_eq : ∀ t : ℝ, Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)) = P t + Q t := by
    intro t
    have hexp : Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))
        = Complex.exp (-(Mu : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hMu, hL]
      push_cast
      ring
    simp only [Aexp, hP, hQ]
    rw [add_mul, add_mul]
    rw [show (Complex.exp (2 * Real.pi * t) * (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ))
          * Complex.exp (-(L : ℂ) * (t : ℂ))
        = (G 1 0 τ + (t : ℂ) * Complex.I * G 1 1 τ)
          * (Complex.exp (2 * Real.pi * t) * Complex.exp (-(L : ℂ) * (t : ℂ))) from by ring,
      hexp]
  have hFint : IntegrableOn F (Set.Ioi 0) := by rw [hF]; exact hint
  have hFint1 : IntegrableOn F (Set.Ioi 1) := hFint.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have hFint01 : IntegrableOn F (Set.Ioc 0 1) := hFint.mono_set Set.Ioc_subset_Ioi_self
  have hFint1L : IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi 1) := by
    refine IntegrableOn.congr_fun hFint1 (fun t _ => ?_) measurableSet_Ioi
    rw [hF_eq]
  have hAeInt : IntegrableOn (fun t : ℝ => Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)))
      (Set.Ioi 1) := by
    rw [← hAeq]
    exact hAexp
  have hDiffInt : IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi (1 : ℝ)) := by
    have hsub : IntegrableOn (fun t : ℝ =>
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t * Complex.exp (-(L : ℂ) * (t : ℂ))
          - Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi 1) :=
      hFint1L.sub hAeInt
    refine IntegrableOn.congr_fun hsub (fun t _ => ?_) measurableSet_Ioi
    ring
  -- the two moment integrals
  have hPint : IntegrableOn P (Set.Ioi 1) := by
    rw [hP]
    exact integrableOn_affine_mul_exp_neg_mul_complex L hLpos (G 0 0 τ) (G 0 1 τ)
  have hPval : ∫ t in Set.Ioi (1 : ℝ), P t
      = G 0 0 τ * (Complex.exp (-(L : ℂ)) / (L : ℂ))
        + (Complex.I * G 0 1 τ)
          * (Complex.exp (-(L : ℂ)) * ((L : ℂ) + 1) / (L : ℂ) ^ 2) := by
    rw [hP]
    exact integral_affine_mul_exp_neg_mul_Ioi_one hLpos (G 0 0 τ) (G 0 1 τ)
  have hmain : sinSq r * (∫ t in Set.Ioi (1 : ℝ),
        Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))) = highPart G τ r := by
    by_cases hMu_pos : 0 < Mu
    · have hQint : IntegrableOn Q (Set.Ioi 1) := by
        rw [hQ]
        exact integrableOn_affine_mul_exp_neg_mul_complex Mu hMu_pos (G 1 0 τ) (G 1 1 τ)
      have hQval : ∫ t in Set.Ioi (1 : ℝ), Q t
          = G 1 0 τ * (Complex.exp (-(Mu : ℂ)) / (Mu : ℂ))
            + (Complex.I * G 1 1 τ)
              * (Complex.exp (-(Mu : ℂ)) * ((Mu : ℂ) + 1) / (Mu : ℂ) ^ 2) := by
        rw [hQ]
        exact integral_affine_mul_exp_neg_mul_Ioi_one hMu_pos (G 1 0 τ) (G 1 1 τ)
      have hAeval : ∫ t in Set.Ioi (1 : ℝ), Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))
          = (∫ t in Set.Ioi (1 : ℝ), P t) + ∫ t in Set.Ioi (1 : ℝ), Q t := by
        rw [← integral_add hPint hQint]
        exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => hAe_eq t)
      rw [hAeval, hPval, hQval, mul_add,
        sinSq_mul_closed hLne hcosL (Complex.exp (-(L : ℂ))) (G 0 0 τ) (Complex.I * G 0 1 τ),
        sinSq_mul_closed hMu_pos.ne' hcosMu (Complex.exp (-(Mu : ℂ))) (G 1 0 τ)
          (Complex.I * G 1 1 τ),
        highPart_eq_closed, hMu, hL]
      ring
    · have hMu_nonpos : Mu ≤ 0 := not_lt.mp hMu_pos
      have hQint : IntegrableOn Q (Set.Ioi 1) := by
        have h1 : IntegrableOn (fun t : ℝ =>
            Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)) - P t) (Set.Ioi 1) :=
          Integrable.sub hAeInt hPint
        refine IntegrableOn.congr_fun h1 (fun t _ => ?_) measurableSet_Ioi
        rw [hAe_eq t]
        ring
      have hG10 : G 1 0 τ = 0 ∧ G 1 1 τ = 0 :=
        eq_zero_of_integrableOn_affine_mul_exp_neg hMu_nonpos hQint
      have hAevalP : ∫ t in Set.Ioi (1 : ℝ), Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ))
          = ∫ t in Set.Ioi (1 : ℝ), P t := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        rw [hAe_eq t, hQ, hG10.1, hG10.2]
        ring
      rw [hAevalP, hPval,
        sinSq_mul_closed hLne hcosL (Complex.exp (-(L : ℂ))) (G 0 0 τ) (Complex.I * G 0 1 τ),
        highPart_eq_closed, hG10.1, hG10.2, hL]
      ring
  -- the telescoping
  have hsplit0 : ∫ t in Set.Ioi (0 : ℝ), F t
      = (∫ t in (0 : ℝ)..1, F t) + ∫ t in Set.Ioi (1 : ℝ), F t := by
    have hunion : ∫ t in Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ), F t
        = (∫ t in Set.Ioc (0 : ℝ) 1, F t) + ∫ t in Set.Ioi (1 : ℝ), F t :=
      setIntegral_union (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx1.2 (not_le.mpr hx2)))
        measurableSet_Ioi hFint01 hFint1
    have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, h2⟩ | h3)
        · exact h1
        · exact lt_trans zero_lt_one h3
      · intro h1
        by_cases h2 : x ≤ 1
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (lt_of_not_ge h2)
    rw [hset] at hunion
    rw [hunion, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hsplit1 : ∫ t in Set.Ioi (1 : ℝ), F t
      = (∫ t in Set.Ioi (1 : ℝ), Aexp G τ t * Complex.exp (-(L : ℂ) * (t : ℂ)))
        + ∫ t in Set.Ioi (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    rw [← integral_add hAeInt hDiffInt]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by rw [hF_eq]; ring)
  have htruncIoi : ∫ t in Set.Ici (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ))
      = ∫ t in Set.Ioi (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ)) :=
    setIntegral_congr_set (Ioi_ae_eq_Ici' (by simp : volume ({(1 : ℝ)} : Set ℝ) = 0)).symm
  have hlow : layerLow ℓ d τ r = sinSq r * ∫ t in (0 : ℝ)..1, F t := by
    rw [layerLow, hF]
  have htrunc : layerTrunc G ℓ d τ r
      = sinSq r * ∫ t in Set.Ici (1 : ℝ), (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Aexp G τ t) * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    rw [layerTrunc]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ici (fun t _ => by rw [hargE t])
  rw [show Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r
      = sinSq r * ∫ t in Set.Ioi (0 : ℝ), F t from by
        rw [Work.Kernels.kernelTransform, sinSq, hF]]
  rw [paperLayer, hlow, htrunc, htruncIoi, ← hmain, hsplit0, hsplit1]
  ring

/-! ## The target -/

theorem layer_agreement_cuspTile (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (w : UpperHalfPlane) (n : ℤ) (hn : n = 1 ∨ n = -1) (hw : w ∈ Work.Asymptotics.KEpsilon)
    (r : ℝ) (hr : r ≠ 0)
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((n : ℝ) +ᵥ w) r
      = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) r := by
  rw [Work.Asymptotics.layer, if_neg hr]
  exact paperLayer_eq_kernelTransform_of_integrable ℓ d (Gcusp ℓ d) ((n : ℝ) +ᵥ w) r hr hint
    (integrableOn_Aexp_of_contour_integrable ℓ d hd ((n : ℝ) +ᵥ w) r hr hint)


end Work.Asymptotics
