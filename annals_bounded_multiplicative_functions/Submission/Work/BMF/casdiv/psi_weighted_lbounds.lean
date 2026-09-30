import Mathlib
import Submission.Work.BMF.Psi1_L2_bound
import Submission.Work.BMF.Psi2_L2_bound
import Submission.Work.BMF.Psi_continuous
import Submission.Work.BMF.window_weighted_integral_bound
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.casdiv.psi_window_l2_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Weighted `L²` bounds for the log-derivative `Ψ` of the Euler product

For a `1`-bounded `f : ℕ → ℂ` with `f 1 = 1` and `0 < α ≤ 1`, the log-derivative
`Ψ f s = Σ_p g_p'(s)/g_p(s)` of the (formal) Euler product satisfies

* `∫_{-T}^{T} ‖Ψ f (1+α+iτ)‖² / ‖1+α+iτ‖² dτ ≤ C/α`,
* `∫_{|τ| > T} ‖Ψ f (1+α+iτ)‖² / ‖1+α+iτ‖² dτ ≤ C/(αT)`   (`T ≥ 1`),

with an absolute constant `C`; here `‖1+α+iτ‖² = (1+α)² + τ²`, so the weight provides the decay
in the frequency `τ`.

Both estimates are *mean-square* statements.  The input is the unit-window bound
`∫_c^{c+1} ‖Ψ f (1+α+iτ)‖² dτ ≤ C/α`, uniform in the window position `c`
(`Work.BMF.casdiv.psi_window_l2_bound`, obtained from the corresponding bounds for the prime part
`Ψ₁` and the remainder `Ψ₂`); the summation of the unit windows against the decaying weight is
`Work.BMF.window_weighted_integral_bound` for the middle range `|τ| ≤ T` and, for the two tails,
the window decomposition of `(-∞,-T] ∪ [T,∞)` carried out here (with the elementary series bound
`Σ_k 1/(T+k)² ≤ 2/T` for `T ≥ 1`).
-/

namespace Work.BMF.casdiv

open MeasureTheory intervalIntegral
open scoped BigOperators Topology

/-! ## Bridge between set integrals and lintegrals -/

/-- Bridge between the Lebesgue integral of a nonnegative function over a set and the lintegral of
its `ENNReal.ofReal` image. -/
private lemma psi_wl_lintegral_ofReal_eq_ofReal_setIntegral {s : Set ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g s volume) (hnn : ∀ x, 0 ≤ g x) :
    (∫⁻ x in s, ENNReal.ofReal (g x)) = ENNReal.ofReal (∫ x in s, g x) :=
  (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict s) hg
    (Filter.Eventually.of_forall hnn)).symm

/-- The middle-range bound in lintegral form: a continuous nonnegative `F` whose unit windows all
have integral at most `B` has weighted lintegral over `[-T,T]` at most `ENNReal.ofReal R`, whenever
the corresponding real interval integral is at most `R`. -/
private lemma psi_wl_Icc_le_of_real {F : ℝ → ℝ} (hFc : Continuous F) (hFnn : ∀ τ, 0 ≤ F τ)
    {a T R : ℝ} (ha : 1 ≤ a) (hT : 1 ≤ T)
    (hR : (∫ τ in (-T)..T, F τ / (a ^ 2 + τ ^ 2)) ≤ R) :
    (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2))) ≤ ENNReal.ofReal R := by
  set g : ℝ → ℝ := fun τ => F τ / (a ^ 2 + τ ^ 2) with hg
  have hgnn : ∀ τ, 0 ≤ g τ := by
    intro τ; rw [hg]
    exact div_nonneg (hFnn τ) (by nlinarith [ha, sq_nonneg τ])
  have hgcont : Continuous g := by
    rw [hg]
    refine Continuous.div hFc (by continuity) (fun τ => ?_)
    exact ne_of_gt (by nlinarith [ha, sq_nonneg τ] : 0 < a ^ 2 + τ ^ 2)
  have hI : IntegrableOn g (Set.Icc (-T) T) volume :=
    (hgcont.continuousOn).integrableOn_compact isCompact_Icc
  rw [psi_wl_lintegral_ofReal_eq_ofReal_setIntegral hI hgnn]
  apply ENNReal.ofReal_le_ofReal
  have hIcc : (∫ x in Set.Icc (-T) T, g x) = ∫ x in Set.Ioc (-T) T, g x := by
    rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc (μ := volume) (a := -T) (b := T)]
  have hIoc : (∫ x in Set.Ioc (-T) T, g x) = ∫ x in (-T)..T, g x := by
    rw [intervalIntegral.integral_of_le (by linarith)]
  rw [hIcc, hIoc]
  exact hR

/-- `‖1+α+iτ‖² = (1+α)² + τ²`. -/
private lemma psi_wl_denom (α τ : ℝ) :
    ‖(((1 + α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2 = (1 + α) ^ 2 + τ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-! ## The tail bound: window decomposition of the two half-lines -/

/-- `(T,∞)` is covered by the unit windows `[T+k, T+k+1]`, `k ∈ ℕ`. -/
private lemma psi_wl_tail_cover_pos (T : ℝ) :
    Set.Ioi T ⊆ ⋃ k : ℕ, Set.Icc (T + k) (T + k + 1) := by
  intro x hx
  rw [Set.mem_Ioi] at hx
  have hpos : 0 < x - T := by linarith
  have hceil : 0 < ⌈x - T⌉₊ := Nat.ceil_pos.mpr hpos
  refine Set.mem_iUnion.mpr ⟨⌈x - T⌉₊ - 1, ?_⟩
  have hcast : ((⌈x - T⌉₊ - 1 : ℕ) : ℝ) = (⌈x - T⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ⌈x - T⌉₊)]
    simp
  have hlt : (⌈x - T⌉₊ : ℝ) - 1 < x - T := by
    have h := Nat.ceil_lt_add_one hpos.le
    linarith
  have hle : x - T ≤ (⌈x - T⌉₊ : ℝ) := Nat.le_ceil (x - T)
  rw [Set.mem_Icc]
  constructor <;> rw [hcast] <;> linarith

/-- `(-∞,-T)` is covered by the reflected unit windows `[-(T+k+1), -(T+k)]`, `k ∈ ℕ`. -/
private lemma psi_wl_tail_cover_neg (T : ℝ) :
    Set.Iio (-T) ⊆ ⋃ k : ℕ, Set.Icc (-((T + (k:ℝ)) + 1)) (-((T + (k:ℝ)) + 1) + 1) := by
  intro w hw
  rw [Set.mem_Iio] at hw
  have hw' : -w ∈ Set.Ioi T := by rw [Set.mem_Ioi]; linarith
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (psi_wl_tail_cover_pos T hw')
  rw [Set.mem_Icc] at hk
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  rw [Set.mem_Icc]
  refine ⟨by linarith [hk.2], ?_⟩
  have heq : -((T + (k:ℝ)) + 1) + 1 = -(T + (k:ℝ)) := by ring
  rw [heq]
  linarith [hk.1]

/-- `Σ_k B/(T+k)² ≤ 2B/T` for `B ≥ 0`, `T ≥ 1`. -/
private lemma psi_wl_tsum_window_weight (B T : ℝ) (hB : 0 ≤ B) (hT : 1 ≤ T) :
    (∑' k : ℕ, ENNReal.ofReal (B / (T + k) ^ 2)) ≤ ENNReal.ofReal (2 * B / T) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => div_nonneg hB (by positivity))]
  apply ENNReal.ofReal_le_ofReal
  have hper : ∀ k : ℕ,
      B / (T + (k:ℝ)) ^ 2 ≤ B * (2 / (T + (k:ℝ)) - 2 / (T + (k:ℝ) + 1)) := by
    intro k
    have hTk : (1:ℝ) ≤ T + (k:ℝ) := by
      have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      linarith
    have hpos : 0 < T + (k:ℝ) := by linarith
    have hkey : 1 / (T + (k:ℝ)) ^ 2 ≤ 2 / (T + (k:ℝ)) - 2 / (T + (k:ℝ) + 1) := by
      have h2 : 2 / (T + (k:ℝ)) - 2 / (T + (k:ℝ) + 1)
          = 2 / ((T + (k:ℝ)) * (T + (k:ℝ) + 1)) := by
        field_simp
        try ring
      rw [h2, le_div_iff₀ (by positivity : (0:ℝ) < (T + (k:ℝ)) * (T + (k:ℝ) + 1))]
      have hx : (1 / (T + (k:ℝ)) ^ 2) * ((T + (k:ℝ)) * (T + (k:ℝ) + 1))
          = ((T + (k:ℝ)) + 1) / (T + (k:ℝ)) := by
        field_simp
        try ring
      rw [hx, div_le_iff₀ hpos]
      linarith
    calc B / (T + (k:ℝ)) ^ 2 = B * (1 / (T + (k:ℝ)) ^ 2) := by ring
      _ ≤ B * (2 / (T + (k:ℝ)) - 2 / (T + (k:ℝ) + 1)) := mul_le_mul_of_nonneg_left hkey hB
  have htel : ∀ N : ℕ, (∑ k ∈ Finset.range N, (2 / (T + (k:ℝ)) - 2 / (T + (k:ℝ) + 1)))
      = 2 / T - 2 / (T + (N:ℝ)) := by
    intro N
    have h := Finset.sum_range_sub (f := fun i : ℕ => -(2:ℝ) / (T + (i:ℝ))) N
    have hcongr : (∑ k ∈ Finset.range N, (2 / (T + (k:ℝ)) - 2 / (T + (k:ℝ) + 1)))
        = ∑ i ∈ Finset.range N,
            ((-(2:ℝ) / (T + ((i + 1 : ℕ) : ℝ))) - (-(2:ℝ) / (T + ((i:ℕ) : ℝ)))) := by
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring
    rw [hcongr, h]
    push_cast
    ring
  calc ∑ k ∈ Finset.range N, B / (T + (k:ℝ)) ^ 2
      ≤ ∑ k ∈ Finset.range N, B * (2 / (T + (k:ℝ)) - 2 / (T + (k:ℝ) + 1)) :=
        Finset.sum_le_sum (fun k _ => hper k)
    _ = B * ∑ k ∈ Finset.range N, (2 / (T + (k:ℝ)) - 2 / (T + (k:ℝ) + 1)) := by
        rw [Finset.mul_sum]
    _ = B * (2 / T - 2 / (T + (N:ℝ))) := by rw [htel N]
    _ ≤ 2 * B / T := by
        have h1 : (0:ℝ) ≤ 2 / (T + (N:ℝ)) := by positivity
        have h2 : 2 / T - 2 / (T + (N:ℝ)) ≤ 2 / T := by linarith
        calc B * (2 / T - 2 / (T + (N:ℝ))) ≤ B * (2 / T) := mul_le_mul_of_nonneg_left h2 hB
          _ = 2 * B / T := by ring

/-- The weighted lintegral of `F τ/(a²+τ²)` over a unit window `[c,c+1]`, given the weight
`M² ≤ a²+τ²` on that window and the window bound `∫_c^{c+1} F ≤ B`. -/
private lemma psi_wl_window_term (F : ℝ → ℝ) (hFc : Continuous F) (hFnn : ∀ τ, 0 ≤ F τ)
    (B a c M : ℝ) (hB : 0 ≤ B) (hMpos : 0 < M)
    (hweight : ∀ τ ∈ Set.Icc c (c+1), M ^ 2 ≤ a ^ 2 + τ ^ 2)
    (hwin : (∫ τ in c..(c+1), F τ) ≤ B) :
    (∫⁻ τ in Set.Icc c (c+1), ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
      ≤ ENNReal.ofReal (B / M ^ 2) := by
  have hM2pos : 0 < M ^ 2 := by positivity
  have hpt : ∀ τ ∈ Set.Icc c (c+1), F τ / (a ^ 2 + τ ^ 2) ≤ F τ / M ^ 2 := by
    intro τ hτ
    exact div_le_div_of_nonneg_left (hFnn τ) hM2pos (hweight τ hτ)
  have hmmeas : Measurable fun τ : ℝ => ENNReal.ofReal (F τ / M ^ 2) :=
    ((hFc.measurable.div measurable_const)).ennreal_ofReal
  have hFmeas : Measurable fun τ : ℝ => ENNReal.ofReal (F τ) := hFc.measurable.ennreal_ofReal
  have hstep : (∫⁻ τ in Set.Icc c (c+1), ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
      ≤ ∫⁻ τ in Set.Icc c (c+1), ENNReal.ofReal (F τ / M ^ 2) :=
    setLIntegral_mono hmmeas (fun τ hτ => ENNReal.ofReal_le_ofReal (hpt τ hτ))
  have hI : IntegrableOn F (Set.Icc c (c+1)) volume :=
    (hFc.continuousOn).integrableOn_compact isCompact_Icc
  have hbridge : (∫⁻ τ in Set.Icc c (c+1), ENNReal.ofReal (F τ))
      = ENNReal.ofReal (∫ τ in Set.Icc c (c+1), F τ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := volume.restrict (Set.Icc c (c+1))) hI (Filter.Eventually.of_forall hFnn)).symm
  have hwinle : (∫ τ in Set.Icc c (c+1), F τ) ≤ B := by
    rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc (μ := volume) (a := c) (b := c+1)]
    rw [← intervalIntegral.integral_of_le (by linarith : c ≤ c + 1)]
    exact hwin
  calc (∫⁻ τ in Set.Icc c (c+1), ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
      ≤ ∫⁻ τ in Set.Icc c (c+1), ENNReal.ofReal (F τ / M ^ 2) := hstep
    _ = ∫⁻ τ in Set.Icc c (c+1), ENNReal.ofReal ((M ^ 2)⁻¹) * ENNReal.ofReal (F τ) := by
        apply lintegral_congr
        intro τ
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (M ^ 2)⁻¹)]
        congr 1
        rw [inv_mul_eq_div]
    _ = ENNReal.ofReal ((M ^ 2)⁻¹) * ∫⁻ τ in Set.Icc c (c+1), ENNReal.ofReal (F τ) :=
        lintegral_const_mul _ hFmeas
    _ = ENNReal.ofReal ((M ^ 2)⁻¹) * ENNReal.ofReal (∫ τ in Set.Icc c (c+1), F τ) := by
        rw [hbridge]
    _ ≤ ENNReal.ofReal ((M ^ 2)⁻¹) * ENNReal.ofReal B :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hwinle) (by positivity)
    _ = ENNReal.ofReal (B / M ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (M ^ 2)⁻¹)]
        congr 1
        rw [inv_mul_eq_div]

/-- **Tail bound.**  If `F ≥ 0` is continuous and every unit-window integral `∫_c^{c+1} F` is at
most `B`, then the weighted lintegrals of `F τ / (a² + τ²)` over the two half-lines `|τ| > T` are
together `O(B/T)`, uniformly in `a ≥ 1` and `T ≥ 1`.  Companion of
`Work.BMF.window_weighted_integral_bound`, which handles the range `|τ| ≤ T`. -/
private lemma psi_wl_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ → ℝ), Continuous F → (∀ τ, 0 ≤ F τ) →
      ∀ B a T : ℝ, 1 ≤ a → 1 ≤ T → (∀ c : ℝ, (∫ τ in c..(c+1), F τ) ≤ B) →
        (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2))) +
          (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
          ≤ ENNReal.ofReal (C * B / T) := by
  refine ⟨4, by norm_num, ?_⟩
  intro F hFc hFnn B a T ha hT hwin
  have hB : 0 ≤ B := by
    have h0 : (0:ℝ) ≤ ∫ τ in (0:ℝ)..1, F τ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun u _ => hFnn u)
    have h1 : (∫ τ in (0:ℝ)..1, F τ) ≤ B := by
      have h := hwin 0
      simpa using h
    linarith
  have hpos : (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
      ≤ ENNReal.ofReal (2 * B / T) := by
    have hterms : ∀ k : ℕ,
        (∫⁻ τ in Set.Icc (T + (k:ℝ)) (T + (k:ℝ) + 1), ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
          ≤ ENNReal.ofReal (B / (T + (k:ℝ)) ^ 2) := by
      intro k
      have hTk : (1:ℝ) ≤ T + (k:ℝ) := by
        have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      refine psi_wl_window_term F hFc hFnn B a (T + (k:ℝ)) (T + (k:ℝ)) hB (by linarith) ?_ ?_
      · intro τ hτ
        have h1 : (T + (k:ℝ)) ≤ τ := hτ.1
        have h2 : (T + (k:ℝ)) ^ 2 ≤ τ ^ 2 := by nlinarith [hTk, h1]
        nlinarith [h2, sq_nonneg a]
      · exact hwin (T + (k:ℝ))
    calc (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
        ≤ ∫⁻ τ in (⋃ k : ℕ, Set.Icc (T + (k:ℝ)) (T + (k:ℝ) + 1)),
            ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)) :=
          lintegral_mono_set (psi_wl_tail_cover_pos T)
      _ ≤ ∑' k : ℕ, ∫⁻ τ in Set.Icc (T + (k:ℝ)) (T + (k:ℝ) + 1),
            ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)) := lintegral_iUnion_le _ _
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (B / (T + (k:ℝ)) ^ 2) := ENNReal.tsum_le_tsum hterms
      _ ≤ ENNReal.ofReal (2 * B / T) := psi_wl_tsum_window_weight B T hB hT
  have hneg : (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
      ≤ ENNReal.ofReal (2 * B / T) := by
    have hterms : ∀ k : ℕ,
        (∫⁻ τ in Set.Icc (-((T + (k:ℝ)) + 1)) (-((T + (k:ℝ)) + 1) + 1),
            ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
          ≤ ENNReal.ofReal (B / (T + (k:ℝ)) ^ 2) := by
      intro k
      have hTk : (1:ℝ) ≤ T + (k:ℝ) := by
        have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      refine psi_wl_window_term F hFc hFnn B a (-((T + (k:ℝ)) + 1)) (T + (k:ℝ)) hB
        (by linarith) ?_ ?_
      · intro τ hτ
        have h1 : τ ≤ -(T + (k:ℝ)) := by
          have := hτ.2
          have he : -((T + (k:ℝ)) + 1) + 1 = -(T + (k:ℝ)) := by ring
          rw [he] at this
          exact this
        have h2 : (T + (k:ℝ)) ^ 2 ≤ τ ^ 2 := by nlinarith [hTk, h1]
        nlinarith [h2, sq_nonneg a]
      · exact hwin (-((T + (k:ℝ)) + 1))
    calc (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
        ≤ ∫⁻ τ in (⋃ k : ℕ, Set.Icc (-((T + (k:ℝ)) + 1)) (-((T + (k:ℝ)) + 1) + 1)),
            ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)) :=
          lintegral_mono_set (psi_wl_tail_cover_neg T)
      _ ≤ ∑' k : ℕ, ∫⁻ τ in Set.Icc (-((T + (k:ℝ)) + 1)) (-((T + (k:ℝ)) + 1) + 1),
            ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)) := lintegral_iUnion_le _ _
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (B / (T + (k:ℝ)) ^ 2) := ENNReal.tsum_le_tsum hterms
      _ ≤ ENNReal.ofReal (2 * B / T) := psi_wl_tsum_window_weight B T hB hT
  calc (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2))) +
        (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
      ≤ ENNReal.ofReal (2 * B / T) + ENNReal.ofReal (2 * B / T) := add_le_add hpos hneg
    _ = ENNReal.ofReal (2 * B / T + 2 * B / T) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ = ENNReal.ofReal (4 * B / T) := by
        congr 1
        ring

/-! ## The main theorem -/

theorem psi_weighted_lbounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ n, ‖f n‖ ≤ 1) →
      ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ T : ℝ, 1 ≤ T →
        (∫⁻ τ in Set.Icc (-T) T,
            ENNReal.ofReal (‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
              ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)) ≤ ENNReal.ofReal (C / α) ∧
        (∫⁻ τ in Set.Ioi T,
            ENNReal.ofReal (‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
              ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)) +
        (∫⁻ τ in Set.Iio (-T),
            ENNReal.ofReal (‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
              ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)) ≤ ENNReal.ofReal (C / (α * T)) := by
  obtain ⟨Cp, hCppos, hpsi⟩ := psi_window_l2_bound
  obtain ⟨Ct, hCtpos, htail⟩ := psi_wl_tail_bound
  obtain ⟨CW, hCWpos, hCW⟩ := window_weighted_integral_bound
  refine ⟨max CW Ct * Cp, mul_pos (lt_max_of_lt_left hCWpos) hCppos, ?_⟩
  intro f hf1 hb α hα0 hα1 T hT
  have ha1 : (1 : ℝ) ≤ 1 + α := by linarith
  have ha1' : (1 : ℝ) < 1 + α := by linarith
  set F : ℝ → ℝ := fun τ => ‖Work.BMF.Psi f ((((1 + α : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
    with hFdef
  have hFc : Continuous F := by
    rw [hFdef]; exact Work.BMF.Psi_continuous f hf1 hb (1 + α) ha1'
  have hFnn : ∀ τ, 0 ≤ F τ := by intro τ; rw [hFdef]; positivity
  have hwin : ∀ c : ℝ, (∫ τ in c..(c+1), F τ) ≤ Cp / α := by
    intro c; rw [hFdef]; exact hpsi f hf1 hb α hα0 hα1 c
  have hden := psi_wl_denom α
  have hR : (∫ τ in (-T)..T, F τ / ((1 + α) ^ 2 + τ ^ 2)) ≤ CW * (Cp / α) :=
    hCW F hFc hFnn (Cp / α) (1 + α) T ha1 hT hwin
  constructor
  · have h1 : (∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (F τ / ((1 + α) ^ 2 + τ ^ 2)))
        ≤ ENNReal.ofReal (CW * (Cp / α)) := psi_wl_Icc_le_of_real hFc hFnn ha1 hT hR
    have hcong : (∫⁻ τ in Set.Icc (-T) T,
          ENNReal.ofReal (‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
            ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2))
        = ∫⁻ τ in Set.Icc (-T) T, ENNReal.ofReal (F τ / ((1 + α) ^ 2 + τ ^ 2)) := by
      apply lintegral_congr
      intro τ
      rw [hFdef, hden]
    rw [hcong]
    refine le_trans h1 ?_
    apply ENNReal.ofReal_le_ofReal
    rw [show CW * (Cp / α) = CW * Cp / α by ring]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left CW Ct) hCppos.le) hα0.le
  · have h2 : (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (F τ / ((1 + α) ^ 2 + τ ^ 2))) +
        (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (F τ / ((1 + α) ^ 2 + τ ^ 2)))
        ≤ ENNReal.ofReal (Ct * (Cp / α) / T) := htail F hFc hFnn (Cp / α) (1 + α) T ha1 hT hwin
    have hcongT : (∫⁻ τ in Set.Ioi T,
          ENNReal.ofReal (‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
            ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2))
        = ∫⁻ τ in Set.Ioi T, ENNReal.ofReal (F τ / ((1 + α) ^ 2 + τ ^ 2)) := by
      apply lintegral_congr
      intro τ
      rw [hFdef, hden]
    have hcongI : (∫⁻ τ in Set.Iio (-T),
          ENNReal.ofReal (‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 /
            ‖(((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2))
        = ∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (F τ / ((1 + α) ^ 2 + τ ^ 2)) := by
      apply lintegral_congr
      intro τ
      rw [hFdef, hden]
    rw [hcongT, hcongI]
    refine le_trans h2 ?_
    apply ENNReal.ofReal_le_ofReal
    rw [show Ct * (Cp / α) / T = Ct * Cp / (α * T) by rw [← mul_div_assoc, div_div]]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right CW Ct) hCppos.le) (by positivity)

end Work.BMF.casdiv
