import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.liftF_lower_translation
import Submission.Work.Pert.one_add_tauC_mul_u_ne_zero
import Submission.Work.Pert.Qm_slice

namespace Work.Pert

open MandelDim Complex

noncomputable section

set_option maxHeartbeats 1000000

/-- From the `1/32` near-translation bound on the gate: `1 - sfun u σ α w` stays within
distance `exp (33π/1024) < 2` of `0`, i.e. `‖1 - sfun u σ α w‖ ≤ 2`.

Indeed `liftF u σ α w - (w+1) = log (1 - sfun)/(2πiα) - 1`, so
`‖log (1 - sfun)‖ ≤ 2π‖α‖·33/32 ≤ 33π/1024`, and `1 - sfun = exp (log (1 - sfun))`. -/
private lemma sfun_one_sub_bound {u : ℂ → ℂ} {σ α : ℂ} {Ξ : ℝ}
    (hα64 : ‖α‖ ≤ 1 / 64)
    (hval : ∀ z ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32) :
    ∀ z ∈ Work.Pert.Qm Ξ α, ‖1 - Work.Pert.sfun u σ α z‖ ≤ 2 := by
  intro z hz
  set X : ℂ := 1 - Work.Pert.sfun u σ α z with hXdef
  set L : ℂ := Complex.log X with hLdef
  set c : ℂ := 1 / (2 * Real.pi * I * α) with hcdef
  have hrel : Work.Pert.liftF u σ α z - (z + 1) = c * L - 1 := by
    simp only [Work.Pert.liftF]
    rw [← hXdef, ← hLdef, ← hcdef]; ring
  have h32 : ‖c * L - 1‖ ≤ 1 / 32 := by
    have h := hval z hz
    rwa [hrel] at h
  have hne : c * L ≠ 0 := by
    intro h
    have hh := h32
    rw [h] at hh
    norm_num at hh
  have hc : c ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have hL : L ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have h2pia : 2 * Real.pi * I * α ≠ 0 := by
    intro h; exact hc (by rw [hcdef, h, div_zero])
  have hmul : (2 * Real.pi * I * α) * c = 1 := by
    rw [hcdef, mul_one_div_cancel h2pia]
  have hLeq : L = (2 * Real.pi * I * α) * (c * L) := by
    rw [← mul_assoc, hmul, one_mul]
  have hnormc : ‖(2 * Real.pi * I * α : ℂ)‖ = 2 * Real.pi * ‖α‖ := by
    rw [show (2 * Real.pi * I * α : ℂ) = ((2 : ℂ) * (Real.pi : ℂ) * I) * α by ring]
    rw [norm_mul, norm_mul, norm_mul]
    simp
  have h3 : ‖c * L‖ ≤ 33 / 32 := by
    have h : c * L = (c * L - 1) + 1 := by ring
    calc ‖c * L‖ = ‖(c * L - 1) + 1‖ := congrArg norm h
      _ ≤ ‖c * L - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖c * L - 1‖ + 1 := by simp
      _ ≤ 1 / 32 + 1 := add_le_add h32 le_rfl
      _ = 33 / 32 := by norm_num
  have hLb : ‖L‖ ≤ 33 * Real.pi / 1024 := by
    rw [hLeq]
    calc ‖(2 * Real.pi * I * α) * (c * L)‖
          = ‖(2 * Real.pi * I * α : ℂ)‖ * ‖c * L‖ := norm_mul _ _
      _ ≤ (2 * Real.pi * (1 / 64)) * (33 / 32) := by
            apply mul_le_mul
            · rw [hnormc]; exact mul_le_mul_of_nonneg_left hα64 (by positivity)
            · exact h3
            · positivity
            · positivity
      _ = 33 * Real.pi / 1024 := by ring
  have hX0 : X ≠ 0 := fun h => hL (by rw [hLdef, h, Complex.log_zero])
  have hX : X = Complex.exp L := by rw [hLdef]; exact (Complex.exp_log hX0).symm
  have hexp2 : Real.exp (33 * Real.pi / 1024) ≤ 2 := by
    have ht0 : (0 : ℝ) ≤ 33 * Real.pi / 1024 := by positivity
    have ht1 : 33 * Real.pi / 1024 < 1 := by nlinarith [Real.pi_lt_four]
    calc Real.exp (33 * Real.pi / 1024) ≤ 1 / (1 - 33 * Real.pi / 1024) :=
          Real.exp_bound_div_one_sub_of_interval ht0 ht1
      _ ≤ 2 := by
          rw [div_le_iff₀ (by linarith)]; nlinarith [Real.pi_lt_four]
  rw [hX, Complex.norm_exp]
  calc Real.exp L.re ≤ Real.exp ‖L‖ := Real.exp_le_exp.mpr (Complex.re_le_norm L)
    _ ≤ Real.exp (33 * Real.pi / 1024) := Real.exp_le_exp.mpr hLb
    _ ≤ 2 := hexp2

/-- The lower gate `Qm Ξ α` is unbounded below: for every real `T` it contains a point of
imaginary part `< -T`.  (`Qm_mem_iff'` reduces membership to the two cone inequalities
`Ξ - (1/α).re - |t + (1/α).im| < x < |t| - Ξ`, and the abscissa `((1/α).im - (1/α).re)/2` is the
midpoint of the slice interval, so `t → -∞` makes both inequalities hold.) -/
private lemma Qm_witness {Ξ : ℝ} {α : ℂ} (T : ℝ) :
    ∃ z ∈ Work.Pert.Qm Ξ α, z.im < -T := by
  set p : ℝ := (1 / α).re with hp
  set q : ℝ := (1 / α).im with hq
  set c : ℝ := (q - p) / 2 with hc
  set L : ℝ := |c - Ξ + p - q| + |q| + |T| + 2 with hL
  set t : ℝ := -L with ht
  have hcΞ : c - Ξ + p - q = (p - q) / 2 - Ξ := by rw [hc]; ring
  have hL1 : |(p - q) / 2 - Ξ| + 2 ≤ L := by
    rw [hL, ← hcΞ]; linarith [abs_nonneg q, abs_nonneg T]
  have hL2 : |q| + 2 ≤ L := by
    rw [hL]; linarith [abs_nonneg (c - Ξ + p - q), abs_nonneg T]
  have hL3 : |T| + 2 ≤ L := by
    rw [hL]; linarith [abs_nonneg (c - Ξ + p - q), abs_nonneg q]
  have ht0 : t < 0 := by rw [ht]; linarith [abs_nonneg T]
  have htT : t < -T := by
    have h1 : T ≤ |T| := le_abs_self T
    rw [ht]; linarith
  have htq : t + q < 0 := by
    have h1 : q ≤ |q| := le_abs_self q
    rw [ht]; linarith
  have htmid : t < (p - q) / 2 - Ξ := by
    have h2 : (p - q) / 2 - Ξ ≤ |(p - q) / 2 - Ξ| := le_abs_self _
    have h3 : -|(p - q) / 2 - Ξ| ≤ (p - q) / 2 - Ξ := neg_abs_le _
    rw [ht]; linarith
  refine ⟨(c : ℂ) + (t : ℂ) * Complex.I, ?_, ?_⟩
  · rw [Qm_mem_iff']
    refine ⟨?_, ?_⟩
    · rw [← hq, abs_of_neg htq, ← hp]
      linarith
    · rw [abs_of_neg ht0, hc]
      linarith
  · have him : ((c : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [him]; exact htT

/-- `1/X - 1/D = (D - X)/(X·D)` for `X, D ≠ 0`. -/
private lemma recip_sub_recip (X D : ℂ) (hX : X ≠ 0) (hD : D ≠ 0) :
    1 / X - 1 / D = (D - X) / (X * D) := by
  rw [eq_div_iff (mul_ne_zero hX hD), sub_mul]
  rw [show 1 / X * (X * D) = D by rw [← mul_assoc, div_mul_cancel₀ 1 hX, one_mul]]
  rw [show 1 / D * (X * D) = X by
    rw [mul_comm X D, ← mul_assoc, div_mul_cancel₀ 1 hD, one_mul]]

/-- `b/a - d = (b - d·a)/a` for `a ≠ 0`. -/
private lemma div_sub_eq (b a d : ℂ) (ha : a ≠ 0) : b / a - d = (b - d * a) / a := by
  rw [eq_div_iff ha, sub_mul, div_mul_cancel₀ b ha]

/-- `c - s/B = (c·B - s)/B` for `B ≠ 0`. -/
private lemma sub_div_eq (c s B : ℂ) (hB : B ≠ 0) : c - s / B = (c * B - s) / B := by
  rw [eq_div_iff hB, sub_mul, div_mul_cancel₀ s hB]

/-- **PERT · the lower end of the lower gate.**  Inside the gate `Qm Ξ α`, as `z.im → -∞`,
`1 - sfun u σ α z = 1/(1 + τ_f z · u(τ_f z))` tends to `1/(1 + σ u σ) = 1/f'(σ)`
exponentially fast.

The ingredients are: the exponential convergence `τ_f z → σ` (`tauC_lower_decay`), the `1/32`
near-translation hypothesis in the shape `1/2 ≤ ‖1 - sfun‖ ≤ 2` (`one_sub_sfun_norm_le_two`,
the lower bound used only to be able to invert), the Lipschitz bound on `u` at `σ`, and the
existence of points of the gate with arbitrarily negative imaginary part. -/
theorem sfun_lower_exp_bound {Ξ rr C δ : ℝ} {α σ : ℂ} {u : ℂ → ℂ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α) (hα64 : ‖α‖ ≤ 1 / 64)
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hrr : 0 < rr) (hσr : ‖σ‖ < rr)
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hC : 0 < C) (hδ : 0 < δ)
    (huL : ∀ ζ : ℂ, ‖ζ - σ‖ ≤ δ → ‖u ζ - u σ‖ ≤ C * ‖ζ - σ‖)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hval : ∀ z ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32) :
    ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧
      ∀ z ∈ Work.Pert.Qm Ξ α, z.im < -Y →
        ‖(1 - Work.Pert.sfun u σ α z) - 1 / (1 + σ * u σ)‖ ≤ M * Real.exp (κ * z.im) := by
  obtain ⟨K, κ, Yd, hKpos, hκpos, hdec⟩ :=
    tauC_lower_decay (σ := σ) (α := α) hΞ hInF1
  have hbnd : ∀ z ∈ Work.Pert.Qm Ξ α, ‖1 - Work.Pert.sfun u σ α z‖ ≤ 2 :=
    sfun_one_sub_bound (u := u) (σ := σ) (α := α) (Ξ := Ξ) hα64 hval
  have hσmem : σ ∈ Metric.ball (0 : ℂ) rr := by
    rw [Metric.mem_ball, dist_zero_right]; exact hσr
  have huσ2 : ‖u σ‖ ≤ 2 := (hu2 σ hσmem).2
  -- ## constants
  set M' : ℝ := 2 * (‖σ‖ * (C + 4) * K) with hM'def
  have hM'pos : 0 < M' := by rw [hM'def]; positivity
  set U : ℝ := max (K / δ) (max (4 * K) (4 * M')) with hUdef
  have hUpos : 0 < U := by rw [hUdef]; positivity
  set Y : ℝ := max (max Yd 0) ((Real.log U + 1) / κ) with hYdef
  have hYd_le : Yd ≤ Y := by
    rw [hYdef]; exact le_trans (le_max_left Yd 0) (le_max_left _ _)
  have h4K : 4 * K ≤ U := by
    rw [hUdef]; exact le_trans (le_max_left (4 * K) (4 * M')) (le_max_right (K / δ) _)
  have h4M' : 4 * M' ≤ U := by
    rw [hUdef]; exact le_trans (le_max_right (4 * K) (4 * M')) (le_max_right (K / δ) _)
  have hKδ : K / δ ≤ U := by rw [hUdef]; exact le_max_left _ _
  have hK_le : K ≤ δ * U := by
    have h := mul_le_mul_of_nonneg_left hKδ (le_of_lt hδ)
    rwa [mul_div_cancel₀ K (ne_of_gt hδ)] at h
  have hexp_le : ∀ y : ℝ, y < -Y → Real.exp (κ * y) ≤ 1 / U := by
    intro y hy
    have h1 : (Real.log U + 1) / κ ≤ Y := by rw [hYdef]; exact le_max_right _ _
    have h2 : Real.log U + 1 ≤ κ * Y := by
      have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt hκpos)
      rwa [mul_div_cancel₀ _ (ne_of_gt hκpos)] at h3
    have h4 : κ * y < κ * (-Y) := mul_lt_mul_of_pos_left hy hκpos
    have h5 : κ * y < -Real.log U := by nlinarith [h4, h2]
    have h6 : Real.exp (κ * y) < Real.exp (-Real.log U) := Real.exp_lt_exp.mpr h5
    rw [Real.exp_neg, Real.exp_log hUpos] at h6
    exact le_of_lt (by simpa using h6)
  -- ## the per-point estimate inside the gate
  have hmain : ∀ z ∈ Work.Pert.Qm Ξ α, z.im < -Y →
      ‖1 / (1 - Work.Pert.sfun u σ α z) - (1 + σ * u σ)‖ ≤ M' * Real.exp (κ * z.im) ∧
      1 / 2 ≤ ‖1 / (1 - Work.Pert.sfun u σ α z)‖ := by
    intro z hz hzy
    have hexpU : Real.exp (κ * z.im) ≤ 1 / U := hexp_le z.im hzy
    have hydec : z.im < -Yd := by linarith
    have hd0 : ‖Work.Pert.tauC σ α z - σ‖ ≤ K * Real.exp (κ * z.im) := hdec z hz hydec
    have he1 : K * Real.exp (κ * z.im) ≤ 1 / 4 := by
      have h2 : K * Real.exp (κ * z.im) ≤ K * (1 / U) :=
        mul_le_mul_of_nonneg_left hexpU (le_of_lt hKpos)
      have h3 : K * (1 / U) ≤ 1 / 4 := by
        rw [mul_one_div, div_le_iff₀ hUpos]; linarith
      linarith
    have heδ : K * Real.exp (κ * z.im) ≤ δ := by
      have h2 : K * Real.exp (κ * z.im) ≤ K * (1 / U) :=
        mul_le_mul_of_nonneg_left hexpU (le_of_lt hKpos)
      have h3 : K * (1 / U) ≤ δ := by
        rw [mul_one_div, div_le_iff₀ hUpos]; linarith
      linarith
    -- the covering map at this point
    set τ : ℂ := Work.Pert.tauC σ α z with hτdef
    have hτQz : τ ∈ Metric.ball (0 : ℂ) rr := by rw [hτdef]; exact hτQ z hz
    have huτ2 : ‖u τ‖ ≤ 2 := (hu2 τ hτQz).2
    set d : ℂ := τ - σ with hddef
    have hdn : ‖d‖ ≤ K * Real.exp (κ * z.im) := by
      rw [hddef, hτdef]; exact hd0
    have huLip : ‖u τ - u σ‖ ≤ C * ‖d‖ := by
      have h : ‖τ - σ‖ ≤ δ := by rw [← hddef]; linarith
      exact huL τ h
    set A : ℂ := 1 + d * u τ with hAdef
    set B : ℂ := 1 + τ * u τ with hBdef
    have hBne' : (1 : ℂ) + τ * u τ ≠ 0 := by
      have h := one_add_tauC_mul_u_ne_zero (u := u) (σ := σ) (α := α) (w := z) (hval z hz)
      rwa [← hτdef] at h
    have hBne : B ≠ 0 := by rw [hBdef]; exact hBne'
    have hA1 : ‖A - 1‖ ≤ 1 / 2 := by
      have h1 : A - 1 = d * u τ := by rw [hAdef]; ring
      rw [h1, norm_mul]
      calc ‖d‖ * ‖u τ‖ ≤ (K * Real.exp (κ * z.im)) * 2 :=
            mul_le_mul hdn huτ2 (norm_nonneg _) (by positivity)
        _ ≤ (1 / 4) * 2 := by linarith
        _ = 1 / 2 := by norm_num
    have hAge : 1 / 2 ≤ ‖A‖ := by
      have h1 : ‖(1 : ℂ)‖ - ‖A‖ ≤ ‖(1 : ℂ) - A‖ := norm_sub_norm_le _ _
      rw [norm_one] at h1
      have h2 : ‖(1 : ℂ) - A‖ = ‖A - 1‖ := norm_sub_rev _ _
      linarith
    have hAne : A ≠ 0 := by
      intro h; rw [h, norm_zero] at hAge; norm_num at hAge
    -- the elementary identities
    have hsfuneq : 1 - Work.Pert.sfun u σ α z = A / B := by
      rw [Work.Pert.sfun, ← hτdef, hAdef, hBdef, hddef]
      rw [sub_div_eq 1 (σ * u τ) (1 + τ * u τ) hBne']
      congr 1
      ring
    have hXeq : 1 / (1 - Work.Pert.sfun u σ α z) = B / A := by
      rw [hsfuneq, one_div_div]
    have hid : B - (1 + σ * u σ) * A = σ * (u τ - u σ) - d * u τ * (σ * u σ) := by
      rw [hAdef, hBdef, hddef]
      ring
    have hkey : ‖B - (1 + σ * u σ) * A‖ ≤ ‖σ‖ * (C + 4) * ‖d‖ := by
      rw [hid]
      have h2 : ‖d * u τ * (σ * u σ)‖ ≤ ‖d‖ * 2 * (‖σ‖ * 2) := by
        rw [norm_mul, norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left huτ2 (norm_nonneg d))
          (mul_le_mul_of_nonneg_left huσ2 (norm_nonneg σ)) (by positivity) (by positivity)
      have h1 : ‖σ * (u τ - u σ)‖ ≤ ‖σ‖ * (C * ‖d‖) := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left huLip (norm_nonneg σ)
      calc ‖σ * (u τ - u σ) - d * u τ * (σ * u σ)‖
          ≤ ‖σ * (u τ - u σ)‖ + ‖d * u τ * (σ * u σ)‖ := norm_sub_le _ _
        _ ≤ ‖σ‖ * (C * ‖d‖) + ‖d‖ * 2 * (‖σ‖ * 2) := add_le_add h1 h2
        _ = ‖σ‖ * (C + 4) * ‖d‖ := by ring
    have hXD : ‖1 / (1 - Work.Pert.sfun u σ α z) - (1 + σ * u σ)‖ ≤ M' * Real.exp (κ * z.im) := by
      rw [hXeq]
      have hid2 : B / A - (1 + σ * u σ) = (B - (1 + σ * u σ) * A) / A :=
        div_sub_eq B A (1 + σ * u σ) hAne
      rw [hid2, norm_div]
      have h1 : ‖B - (1 + σ * u σ) * A‖ / ‖A‖
          ≤ (‖σ‖ * (C + 4) * ‖d‖) / (1 / 2) :=
        div_le_div₀ (by positivity) hkey (by norm_num) hAge
      have h2 : ‖σ‖ * (C + 4) * ‖d‖ ≤ ‖σ‖ * (C + 4) * (K * Real.exp (κ * z.im)) :=
        mul_le_mul_of_nonneg_left hdn (by positivity)
      calc ‖B - (1 + σ * u σ) * A‖ / ‖A‖
          ≤ (‖σ‖ * (C + 4) * ‖d‖) / (1 / 2) := h1
        _ = 2 * (‖σ‖ * (C + 4) * ‖d‖) := by ring
        _ ≤ 2 * (‖σ‖ * (C + 4) * (K * Real.exp (κ * z.im))) := by linarith
        _ = M' * Real.exp (κ * z.im) := by rw [hM'def]; ring
    refine ⟨hXD, ?_⟩
    have h1sne : 1 - Work.Pert.sfun u σ α z ≠ 0 := by
      rw [hsfuneq]; exact div_ne_zero hAne hBne
    have hnormpos : 0 < ‖(1 : ℂ) - Work.Pert.sfun u σ α z‖ := norm_pos_iff.mpr h1sne
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hnormpos (hbnd z hz)
  -- ## the limit value `1 + σ u σ` is nonzero
  have hDge : 1 / 4 ≤ ‖1 + σ * u σ‖ := by
    obtain ⟨z₀, hz₀Q, hz₀y⟩ := Qm_witness (Ξ := Ξ) (α := α) Y
    obtain ⟨h1, h2⟩ := hmain z₀ hz₀Q hz₀y
    have h3 : M' * Real.exp (κ * z₀.im) ≤ 1 / 4 := by
      have h4 := hexp_le z₀.im hz₀y
      have h5 : M' * Real.exp (κ * z₀.im) ≤ M' * (1 / U) :=
        mul_le_mul_of_nonneg_left h4 (le_of_lt hM'pos)
      have h6 : M' * (1 / U) ≤ 1 / 4 := by
        rw [mul_one_div, div_le_iff₀ hUpos]; linarith
      linarith
    have h7 : ‖1 + σ * u σ‖ ≥ ‖1 / (1 - Work.Pert.sfun u σ α z₀)‖
        - ‖1 / (1 - Work.Pert.sfun u σ α z₀) - (1 + σ * u σ)‖ := by
      have := norm_sub_norm_le (1 / (1 - Work.Pert.sfun u σ α z₀)) (1 + σ * u σ)
      linarith
    linarith
  refine ⟨8 * M', κ, Y, by linarith, hκpos, ?_⟩
  intro z hz hzy
  obtain ⟨h1, h2⟩ := hmain z hz hzy
  have hDne : (1 : ℂ) + σ * u σ ≠ 0 := by
    intro h; rw [h, norm_zero] at hDge; norm_num at hDge
  have hXne : 1 / (1 - Work.Pert.sfun u σ α z) ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; norm_num at h2
  have hkey3 : 1 / (1 / (1 - Work.Pert.sfun u σ α z)) - 1 / (1 + σ * u σ)
      = ((1 + σ * u σ) - 1 / (1 - Work.Pert.sfun u σ α z))
        / ((1 / (1 - Work.Pert.sfun u σ α z)) * (1 + σ * u σ)) :=
    recip_sub_recip _ _ hXne hDne
  have hident : (1 - Work.Pert.sfun u σ α z) = 1 / (1 / (1 - Work.Pert.sfun u σ α z)) := by
    rw [one_div_div, div_one]
  rw [hident, hkey3, norm_div, norm_mul]
  have h4 : ‖(1 + σ * u σ) - 1 / (1 - Work.Pert.sfun u σ α z)‖ ≤ M' * Real.exp (κ * z.im) := by
    rw [norm_sub_rev]; exact h1
  have h5 : (1 / 2) * (1 / 4) ≤ ‖1 / (1 - Work.Pert.sfun u σ α z)‖ * ‖1 + σ * u σ‖ :=
    mul_le_mul h2 hDge (by norm_num) (norm_nonneg _)
  have h6 : ‖(1 + σ * u σ) - 1 / (1 - Work.Pert.sfun u σ α z)‖
      / (‖1 / (1 - Work.Pert.sfun u σ α z)‖ * ‖1 + σ * u σ‖)
      ≤ (M' * Real.exp (κ * z.im)) / ((1 / 2) * (1 / 4)) :=
    div_le_div₀ (by positivity) h4 (by norm_num) h5
  calc ‖(1 + σ * u σ) - 1 / (1 - Work.Pert.sfun u σ α z)‖
        / (‖1 / (1 - Work.Pert.sfun u σ α z)‖ * ‖1 + σ * u σ‖)
      ≤ (M' * Real.exp (κ * z.im)) / ((1 / 2) * (1 / 4)) := h6
    _ = 8 * M' * Real.exp (κ * z.im) := by ring

end

end Work.Pert
