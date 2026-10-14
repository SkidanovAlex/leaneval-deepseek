import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzAux
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzDefs
import Submission.Work.FTS.CoercivityFix.Assembly.ProdDeriv
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.AnsatzAsym =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-! ## `∫_1^2 (χ')² ≥ 1` -/

theorem differentiableAt_chi (x : ℝ) : DifferentiableAt ℝ Work.Stability.chi x :=
  (Work.Stability.chi_contDiff.differentiable (by simp)).differentiableAt

theorem continuous_deriv_chi : Continuous (deriv Work.Stability.chi) :=
  Work.Stability.chi_contDiff.continuous_deriv (by simp)

/-- `1 ≤ ∫_1^2 (χ')²`: the cut-off drops from `1` to `0` across `[1,2]`, so the fundamental
theorem of calculus gives `∫_1^2 χ' = -1`, and `|y| ≤ (y²+1)/2` turns that into the bound. -/
theorem one_le_integral_deriv_chi_sq :
    (1 : ℝ) ≤ ∫ x in (1 : ℝ)..2, (deriv Work.Stability.chi x) ^ 2 := by
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) 2, DifferentiableAt ℝ Work.Stability.chi x :=
    fun x _ => differentiableAt_chi x
  have hint : IntervalIntegrable (deriv Work.Stability.chi) volume 1 2 :=
    continuous_deriv_chi.intervalIntegrable 1 2
  have hFTC : (∫ x in (1 : ℝ)..2, deriv Work.Stability.chi x)
      = Work.Stability.chi 2 - Work.Stability.chi 1 :=
    intervalIntegral.integral_deriv_eq_sub hderiv hint
  have hval : (∫ x in (1 : ℝ)..2, deriv Work.Stability.chi x) = -1 := by
    rw [hFTC, Work.Stability.chi_eq_zero (by norm_num), Work.Stability.chi_eq_one (by norm_num)]
    norm_num
  have habs : (1 : ℝ) ≤ ∫ x in (1 : ℝ)..2, |deriv Work.Stability.chi x| := by
    have h := intervalIntegral.abs_integral_le_integral_abs (f := deriv Work.Stability.chi)
      (a := (1 : ℝ)) (b := 2) (μ := volume) (by norm_num : (1 : ℝ) ≤ 2)
    rw [hval] at h
    simpa using h
  have hpt : ∀ x : ℝ,
      |deriv Work.Stability.chi x| ≤ ((deriv Work.Stability.chi x) ^ 2 + 1) / 2 := by
    intro x
    have h2 : (|deriv Work.Stability.chi x|) ^ 2 = (deriv Work.Stability.chi x) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|deriv Work.Stability.chi x| - 1),
      abs_nonneg (deriv Work.Stability.chi x)]
  have hIntA : IntervalIntegrable (fun x => |deriv Work.Stability.chi x|) volume 1 2 :=
    continuous_deriv_chi.abs.intervalIntegrable 1 2
  have hIntB : IntervalIntegrable (fun x => (deriv Work.Stability.chi x) ^ 2) volume 1 2 :=
    (continuous_deriv_chi.pow 2).intervalIntegrable 1 2
  have hIntC : IntervalIntegrable
      (fun x => ((deriv Work.Stability.chi x) ^ 2 + 1) / 2) volume 1 2 :=
    (hIntB.add intervalIntegrable_const).div_const 2
  have hmono : (∫ x in (1 : ℝ)..2, |deriv Work.Stability.chi x|)
      ≤ ∫ x in (1 : ℝ)..2, ((deriv Work.Stability.chi x) ^ 2 + 1) / 2 :=
    intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2) hIntA hIntC (fun x _ => hpt x)
  have hvalC : (∫ x in (1 : ℝ)..2, ((deriv Work.Stability.chi x) ^ 2 + 1) / 2)
      = ((∫ x in (1 : ℝ)..2, (deriv Work.Stability.chi x) ^ 2) + 1) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add hIntB intervalIntegrable_const,
      intervalIntegral.integral_const]
    norm_num
  have hfin := habs.trans (hmono.trans_eq hvalC)
  linarith

/-! ## The region of concentration and the angular bounds on it -/

/-- The support region of every `hA δ` with `δ ≤ 1/8`. -/
def acidJ : Set ℝ := Set.Icc (1 / 4) (3 / 4)

theorem mem_acidJ_of_mem_Icc (δ : ℝ) (hδ1 : δ ≤ 1 / 8) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) : θ ∈ acidJ := by
  simp only [acidJ, Set.mem_Icc, th0] at hθ ⊢
  constructor <;> linarith [hθ.1, hθ.2]

theorem acidJ_pos {θ : ℝ} (hθ : θ ∈ acidJ) : 0 < θ := by
  have := hθ.1; linarith

theorem acidJ_lt_pi {θ : ℝ} (hθ : θ ∈ acidJ) : θ < Real.pi / 2 := by
  have := hθ.2; have := Real.pi_gt_three; linarith


theorem sin_two_bounds {θ : ℝ} (hθ : θ ∈ acidJ) :
    Real.sin (1 / 2) ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ Real.sin (3 / 2) := by
  have h1 : -(Real.pi / 2) ≤ (1 : ℝ) / 2 := by have := Real.pi_gt_three; linarith
  have h2 : (3 : ℝ) / 2 ≤ Real.pi / 2 := by have := Real.pi_gt_three; linarith
  have h3 : (1 : ℝ) / 2 ≤ 2 * θ := by linarith [hθ.1]
  have h4 : 2 * θ ≤ (3 : ℝ) / 2 := by linarith [hθ.2]
  exact ⟨Real.sin_le_sin_of_le_of_le_pi_div_two h1 (by linarith) h3,
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hθ.1]) h2 h4⟩

theorem sin_two_pos {θ : ℝ} (hθ : θ ∈ acidJ) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [acidJ_pos hθ]) (by
    have := acidJ_lt_pi hθ; have := Real.pi_pos; linarith)

theorem sin_half_pos : 0 < Real.sin (1 / 2 : ℝ) :=
  Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by have := Real.pi_gt_three; linarith)

theorem sin_one_pos : 0 < Real.sin (1 : ℝ) :=
  Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by have := Real.pi_gt_three; linarith)

theorem sin_three_halves_lt_one : Real.sin (3 / 2 : ℝ) < 1 := by
  have h1 : -(Real.pi / 2) ≤ (3 : ℝ) / 2 := by have := Real.pi_gt_three; linarith
  have h2 : (3 : ℝ) / 2 < Real.pi / 2 := by have := Real.pi_gt_three; linarith
  have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two h1 le_rfl h2
  rwa [Real.sin_pi_div_two] at h

theorem sin_three_halves_pos : 0 < Real.sin (3 / 2 : ℝ) :=
  Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by have := Real.pi_gt_three; linarith)

/-! ## The `(·)^{-η} - (·)^{-γ}` gap -/

/-- **Monotonicity of the weight gap**: for `0 < x ≤ s ≤ 1` with `γ ≤ η` and `0 < η`, the
difference `x^{-η} - x^{-γ}` dominates `s^{-η} - s^{-γ}`.  (Proof: factor out `x^{-η}`; the
identities `x^{-η}(1 - x^{η-γ}) = x^{-η} - x^{-γ}` and `s^{-η}(1 - s^{η-γ}) = s^{-η} - s^{-γ}`
reduce the claim to a product of two monotonicities.) -/
theorem rpow_sub_mono {x s η γ : ℝ} (hx : 0 < x) (hxs : x ≤ s) (hs1 : s ≤ 1)
    (hηγ : γ ≤ η) (hη : 0 < η) :
    s ^ (-η) - s ^ (-γ) ≤ x ^ (-η) - x ^ (-γ) := by
  have hs : 0 ≤ s := le_trans (le_of_lt hx) hxs
  have hs0 : 0 < s := lt_of_lt_of_le hx hxs
  have hxη : 0 < x ^ η := Real.rpow_pos_of_pos hx η
  have hsη : 0 < s ^ η := Real.rpow_pos_of_pos hs0 η
  have h1 : s ^ (-η) ≤ x ^ (-η) := by
    rw [Real.rpow_neg (le_of_lt hx) η, Real.rpow_neg hs η]
    exact (inv_le_inv₀ hsη hxη).mpr (Real.rpow_le_rpow (le_of_lt hx) hxs (le_of_lt hη))
  have h2 : x ^ (η - γ) ≤ s ^ (η - γ) :=
    Real.rpow_le_rpow (le_of_lt hx) hxs (by linarith)
  have h3 : 1 - s ^ (η - γ) ≤ 1 - x ^ (η - γ) := by linarith
  have h4 : 0 ≤ 1 - s ^ (η - γ) := by
    have hle : s ^ (η - γ) ≤ 1 := by
      have h := Real.rpow_le_rpow hs hs1 (show (0 : ℝ) ≤ η - γ by linarith)
      rwa [Real.one_rpow] at h
    linarith
  have hxs1 : x ^ (-η) * x ^ (η - γ) = x ^ (-γ) := by
    rw [← Real.rpow_add hx (-η) (η - γ)]
    congr 1
    ring
  have hss1 : s ^ (-η) * s ^ (η - γ) = s ^ (-γ) := by
    rw [← Real.rpow_add hs0 (-η) (η - γ)]
    congr 1
    ring
  have h5 : s ^ (-η) * (1 - s ^ (η - γ)) ≤ x ^ (-η) * (1 - x ^ (η - γ)) :=
    mul_le_mul h1 h3 h4 (Real.rpow_nonneg (le_of_lt hx) _)
  have h6 : s ^ (-η) * (1 - s ^ (η - γ)) = s ^ (-η) - s ^ (-γ) := by
    rw [mul_sub, mul_one, hss1]
  have h7 : x ^ (-η) * (1 - x ^ (η - γ)) = x ^ (-η) - x ^ (-γ) := by
    rw [mul_sub, mul_one, hxs1]
  linarith [h5, h6.symm.le, h7.symm.le]

/-- The gap is positive for `α < -1/10`. -/
theorem gap_pos (α : ℝ) (hα : α < -(1 / 10 : ℝ)) :
    0 < Real.sin (3 / 2 : ℝ) ^ (-(Work.Spaces.eta))
        - Real.sin (3 / 2 : ℝ) ^ (-(Work.Spaces.gam α)) := by
  have hγη : Work.Spaces.gam α < Work.Spaces.eta := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  have hs0 : 0 < Real.sin (3 / 2 : ℝ) := sin_three_halves_pos
  have h1 : Real.sin (3 / 2 : ℝ) ^ (Work.Spaces.eta - Work.Spaces.gam α) < 1 := by
    have h := Real.rpow_lt_rpow (le_of_lt hs0) sin_three_halves_lt_one
      (show (0 : ℝ) < Work.Spaces.eta - Work.Spaces.gam α by linarith)
    rwa [Real.one_rpow] at h
  have h2 : Real.sin (3 / 2 : ℝ) ^ (-(Work.Spaces.eta))
      * (1 - Real.sin (3 / 2 : ℝ) ^ (Work.Spaces.eta - Work.Spaces.gam α))
      = Real.sin (3 / 2 : ℝ) ^ (-(Work.Spaces.eta))
        - Real.sin (3 / 2 : ℝ) ^ (-(Work.Spaces.gam α)) := by
    rw [mul_sub, mul_one, ← Real.rpow_add hs0]
    congr 1
    ring_nf
  rw [← h2]
  exact mul_pos (Real.rpow_pos_of_pos hs0 _) (by linarith)

/-! ## The upper bound on the `i = 0` slot -/

theorem Sc_zero_bound (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    Sc (hA δ) 0 Work.Spaces.eta
      ≤ 4 * Real.sin (1 / 2 : ℝ) ^ (-(Work.Spaces.eta)) * δ := by
  set C : ℝ := Real.sin (1 / 2 : ℝ) ^ (-(Work.Spaces.eta)) with hC
  have hCpos : 0 < C := by rw [hC]; exact Real.rpow_pos_of_pos sin_half_pos _
  set K : Set ℝ := Set.Icc (th0 - 2 * δ) (th0 + 2 * δ) with hK
  have hKmeas : MeasurableSet K := by rw [hK]; exact measurableSet_Icc
  have hsupp : ∀ θ, θ ∉ K →
      (vthIter 0 (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 0 := by
    intro θ hθ
    rw [hK] at hθ
    rw [vthIter_hA_eq_zero hδ0 hθ]
    simp
  have hnn : ∀ θ, 0 ≤ (vthIter 0 (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    intro θ
    by_cases hθK : θ ∈ K
    · rw [vthIter_zero]
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (mem_acidJ_of_mem_Icc δ hδ1 hθK))) _)
    · rw [hsupp θ hθK]
  have hpt : ∀ θ, (vthIter 0 (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ C * K.indicator (fun _ => (1 : ℝ)) θ := by
    intro θ
    by_cases hθK : θ ∈ K
    · rw [Set.indicator_of_mem hθK, mul_one, vthIter_zero]
      have hmem := mem_acidJ_of_mem_Icc δ hδ1 hθK
      have h1 : (hA δ θ) ^ 2 ≤ 1 := by
        have hle := Work.Stability.chi_le_one ((θ - th0) / δ)
        have hge := Work.Stability.chi_nonneg ((θ - th0) / δ)
        rw [hA]
        nlinarith
      have h2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ C := by
        rw [hC, Real.rpow_neg (le_of_lt (sin_two_pos hmem)) (Work.Spaces.eta),
          Real.rpow_neg (le_of_lt sin_half_pos)]
        exact (inv_le_inv₀ (Real.rpow_pos_of_pos (sin_two_pos hmem) _)
          (Real.rpow_pos_of_pos sin_half_pos _)).mpr
          (Real.rpow_le_rpow (le_of_lt sin_half_pos) (sin_two_bounds hmem).1
            (le_of_lt Work.Spaces.eta_pos))
      have h3 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        Real.rpow_nonneg (le_of_lt (sin_two_pos hmem)) _
      nlinarith
    · rw [Set.indicator_of_notMem hθK, mul_zero]
      exact le_of_eq (hsupp θ hθK)
  have hIntK : IntegrableOn (fun θ => K.indicator (fun _ => (1 : ℝ)) θ) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.indicator
      (integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (1 : ℝ))
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) hKmeas
  have hInt : IntegrableOn (fun θ => C * K.indicator (fun _ => (1 : ℝ)) θ)
      Work.Spaces.Iθ := hIntK.const_mul C
  have hmono : (∫ θ in Work.Spaces.Iθ,
        (vthIter 0 (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ ∫ θ in Work.Spaces.Iθ, C * K.indicator (fun _ => (1 : ℝ)) θ :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hInt
      (Filter.Eventually.of_forall hpt)
  have hconst : (∫ θ in Work.Spaces.Iθ, C * K.indicator (fun _ => (1 : ℝ)) θ)
      = C * (volume (Work.Spaces.Iθ ∩ K)).toReal := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator hKmeas,
      MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def]
    simp
  have hmeas : (volume (Work.Spaces.Iθ ∩ K)).toReal ≤ 4 * δ := by
    have h1 : volume (Work.Spaces.Iθ ∩ K) ≤ volume K := measure_mono (Set.inter_subset_right)
    have h2 : volume K = ENNReal.ofReal (4 * δ) := by
      rw [hK, Real.volume_Icc]
      congr 1
      ring
    have h3 : (volume K).toReal = 4 * δ := by
      rw [h2, ENNReal.toReal_ofReal (by linarith)]
    calc (volume (Work.Spaces.Iθ ∩ K)).toReal ≤ (volume K).toReal :=
          ENNReal.toReal_mono (by rw [h2]; exact ENNReal.ofReal_ne_top) h1
      _ = 4 * δ := h3
  rw [Sc]
  calc (∫ θ in Work.Spaces.Iθ,
        (vthIter 0 (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ ∫ θ in Work.Spaces.Iθ, C * K.indicator (fun _ => (1 : ℝ)) θ := hmono
    _ = C * (volume (Work.Spaces.Iθ ∩ K)).toReal := hconst
    _ ≤ C * (4 * δ) := mul_le_mul_of_nonneg_left hmeas (le_of_lt hCpos)
    _ = 4 * Real.sin (1 / 2 : ℝ) ^ (-(Work.Spaces.eta)) * δ := by rw [hC]; ring

end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.AnsatzEval =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-! ## Powers of the angular weight -/

/-- `(s^{a/2})² = s^a` for `s ≥ 0` (the degenerate case `s = 0` is consistent with Lean's
`rpow` convention). -/
theorem rpow_half_sq (a s : ℝ) (hs : 0 ≤ s) : (s ^ (a / 2)) ^ 2 = s ^ a := by
  have h2 : (s ^ (a / 2)) ^ ((2 : ℕ) : ℝ) = s ^ a := by
    rw [← Real.rpow_mul hs (a / 2) ((2 : ℕ) : ℝ)]
    congr 1
    push_cast
    ring
  rwa [Real.rpow_natCast] at h2

/-- The light-weight square: `(w / s^{a/2})² = w² s^{-a}`. -/
theorem div_rpow_half_sq (a w s : ℝ) (hs : 0 ≤ s) :
    (w / s ^ (a / 2)) ^ 2 = w ^ 2 * s ^ (-a) := by
  rw [div_pow, rpow_half_sq a s hs, div_eq_mul_inv, ← Real.rpow_neg hs a]

/-- The heavy-weight square: `(x · (w s^{-c/2}))² = x² w² s^{-c}`. -/
theorem mul_rpow_half_sq (c x w s : ℝ) (hs : 0 ≤ s) :
    (x * (w * s ^ (-(c / 2)))) ^ 2 = x ^ 2 * (w ^ 2 * s ^ (-c)) := by
  have h : (s ^ (-(c / 2))) ^ 2 = s ^ (-c) := by
    have hh : ((s ^ ((-c) / 2)) ^ 2 : ℝ) = s ^ (-c) := rpow_half_sq (-c) s hs
    rwa [neg_div] at hh
  rw [mul_pow, mul_pow, h]

/-! ## The slot index set and the slot families -/


/-- The `z`-factor of a slot. -/
noncomputable def SlotU (ψ : ℝ → ℝ) (k : ℕ) (p : ℕ ⊕ (ℕ × ℕ)) : ℝ → ℝ :=
  p.elim (fun i => fun z => (vzIter i ψ z * Work.Spaces.w z) ^ 2)
    (fun q => fun z =>
      if 1 ≤ q.1 ∧ q.1 + q.2 ≤ k then (vzIter q.2 ψ z * Work.Spaces.w z) ^ 2 else 0)

/-- The `θ`-factor of a slot. -/
noncomputable def SlotV (α : ℝ) (g : ℝ → ℝ) (p : ℕ ⊕ (ℕ × ℕ)) : ℝ → ℝ :=
  p.elim (fun _ => fun θ => (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (fun q => fun θ => (vthIter q.1 g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))

@[simp] theorem SlotU_inl (ψ : ℝ → ℝ) (k i : ℕ) (z : ℝ) :
    SlotU ψ k (Sum.inl i) z = (vzIter i ψ z * Work.Spaces.w z) ^ 2 := rfl

@[simp] theorem SlotU_inr (ψ : ℝ → ℝ) (k : ℕ) (q : ℕ × ℕ) (z : ℝ) :
    SlotU ψ k (Sum.inr q) z
      = if 1 ≤ q.1 ∧ q.1 + q.2 ≤ k then (vzIter q.2 ψ z * Work.Spaces.w z) ^ 2 else 0 := rfl

@[simp] theorem SlotV_inl (α : ℝ) (g : ℝ → ℝ) (i : ℕ) (θ : ℝ) :
    SlotV α g (Sum.inl i) θ = (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl

@[simp] theorem SlotV_inr (α : ℝ) (g : ℝ → ℝ) (q : ℕ × ℕ) (θ : ℝ) :
    SlotV α g (Sum.inr q) θ
      = (vthIter q.1 g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := rfl

/-! ## The product-sum iterated integral -/


/-! ## The pointwise expansion of the `ℋ^k`-integrand -/


/-! ## The evaluated (triangular) form -/







/-! ## The level shift -/




end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.C0_sq_le_EDthW_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OClass

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Measurability of `D_θ f · w` for `SmoothOpen` data -/

/-- `(z,θ) ↦ D_θ f z θ · w(z)` is continuous on the open quadrant for `SmoothOpen` data:
`D_θ` preserves `C^∞` on the open quadrant (`SmoothOpen.Dth`), and there the weight `w` is
continuous with no singularity. -/
theorem continuousOn_dth_mul_w_O {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hD : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dth f)) Work.FTS.EllipticEst.Q0 := hso.Dth
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hD.continuousOn
  exact hcont.mul Work.Coercivity.continuousOn_w_quad

/-- A.e. strong measurability of `D_θ f · w` with respect to the product of the restrictions of
Lebesgue measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`, for `SmoothOpen` data. -/
theorem aesm_dth_mul_w_O {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_dth_mul_w_O hso)

/-! ## The bound -/

/-- `L₁₂(Transport f)(0)` is a linear functional of `D_θ f · w` whose kernel
`3 K(θ) z/(1+z)³` has `L²`-norm at most `1`; hence `(C₀ f)² ≤ EDthW f`, in the open-quadrant
class `SmoothOpen`. -/
theorem C0_sq_le_EDthW_O {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    (Work.Coercivity.C0 f) ^ 2 ≤ Work.Coercivity.EDthW f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ) with hP
  set u : ℝ × ℝ → ℝ := fun p => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1 with hu
  set v : ℝ × ℝ → ℝ := fun p => 3 * Work.Spaces.K p.2 * p.1 / (1 + p.1) ^ 3 with hv
  have hu2 : Integrable (fun p : ℝ × ℝ => u p ^ 2) P := by
    have h := Work.Coercivity.integrableOn_prod
      (g := fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
      * Work.Spaces.w z ^ 2) hint
    exact h.congr (Eventually.of_forall fun p => by simp only [hu]; ring)
  have hv2 : Integrable (fun p : ℝ × ℝ => v p ^ 2) P := by
    have hran : Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Work.Spaces.Iz) :=
      Work.Coercivity.integrable_Iz_zsq_div_six.const_mul 9
    have hmul : Integrable (fun p : ℝ × ℝ =>
        (9 * (p.1 ^ 2 / (1 + p.1) ^ 6)) * ((Work.Spaces.K p.2) ^ 2)) P :=
      hran.mul_prod Work.Coercivity.integrableOn_Kθ_sq
    refine hmul.congr ?_
    filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
    have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0:ℝ) < p.1 from hp])
    simp only [hv]
    field_simp
    ring
  have huA : MemLp u 2 P := by
    refine (memLp_two_iff_integrable_sq ?_).2 hu2
    rw [hu, hP]
    exact aesm_dth_mul_w_O hso
  have hvA : MemLp v 2 P := by
    refine (memLp_two_iff_integrable_sq ?_).2 hv2
    rw [hv]
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.K]
    fun_prop
  have hC0id : Work.Coercivity.C0 f = ∫ p, u p * v p ∂P := by
    have hdef : Work.Coercivity.C0 f = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s := by
      simp only [Work.Coercivity.C0, Work.Coercivity.L12f, Work.FM.L12, Work.FM.L12dens,
        Work.Spaces.Iθ]
    rw [hdef]
    have h1 : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s)
        = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ, u (s, θ) * v (s, θ) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [hu, hv, Work.Coercivity.Transport, Work.Spaces.w]
      have hs0 : s ≠ 0 := ne_of_gt hs
      have hs1 : 1 + s ≠ 0 := ne_of_gt (by linarith [show (0:ℝ) < s from hs])
      field_simp
    rw [h1]
    rw [MeasureTheory.setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => u p * v p)
      (huA.integrable_mul hvA)).symm
  have hunorm : ∫ p, u p ^ 2 ∂P = Work.Coercivity.EDthW f := by
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => u p ^ 2) hu2]
    rw [Work.Coercivity.EDthW, Work.Coercivity.wip]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hu]; ring
  have hsep : ∫ p, v p ^ 2 ∂P
      = (∫ z in Work.Spaces.Iz, 9 * (z ^ 2 / (1 + z) ^ 6))
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) := by
    have hcongr : (fun p : ℝ × ℝ => v p ^ 2)
        =ᵐ[P] fun p : ℝ × ℝ => (9 * (p.1 ^ 2 / (1 + p.1) ^ 6))
          * ((Work.Spaces.K p.2) ^ 2) := by
      filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
      have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0:ℝ) < p.1 from hp])
      simp only [hv]; field_simp; ring
    rw [MeasureTheory.integral_congr_ae hcongr]
    have hran : Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Work.Spaces.Iz) :=
      Work.Coercivity.integrable_Iz_zsq_div_six.const_mul 9
    exact Work.Coercivity.integral_prod_sep _ _
      hran Work.Coercivity.integrableOn_Kθ_sq
  have hvnorm : ∫ p, v p ^ 2 ∂P ≤ 1 := by
    rw [hsep]
    have h1 : (∫ z in Work.Spaces.Iz, 9 * (z ^ 2 / (1 + z) ^ 6)) = 3 / 10 := by
      rw [MeasureTheory.integral_const_mul, Work.Coercivity.integral_Iz_zsq_div_six]
      norm_num
    have h2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) ≤ 9 / 4 :=
      Work.Coercivity.integral_Iθ_Ksq_le
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2 :=
      integral_nonneg fun θ => sq_nonneg _
    rw [h1]
    nlinarith [h2, hnn]
  calc (Work.Coercivity.C0 f) ^ 2 = (∫ p, u p * v p ∂P) ^ 2 := by rw [hC0id]
    _ ≤ (∫ p, u p ^ 2 ∂P) * (∫ p, v p ^ 2 ∂P) :=
        Work.Coercivity.cs_integral_mul huA hvA
    _ ≤ Work.Coercivity.EDthW f * 1 := by
        rw [hunorm]
        exact mul_le_mul_of_nonneg_left hvnorm
          (by rw [← hunorm]; exact integral_nonneg fun p => sq_nonneg _)
    _ = Work.Coercivity.EDthW f := mul_one _

end Work.FTS.StrongEps.EpsE4Thr.OClass
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ZDecay_of_decay_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

/-! ## The interior of the quadrant: the squeeze -/


/-! ## The main statement -/


end Work.FTS_EllLimOK
end
end
