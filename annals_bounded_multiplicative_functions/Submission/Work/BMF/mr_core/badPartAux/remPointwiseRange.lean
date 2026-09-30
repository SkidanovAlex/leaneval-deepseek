import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.remPointwise_defs
import Submission.Work.BMF.mr_core.badPartAux.remPointwise_le
import Submission.Work.BMF.mr_core.badPartAux.omega_sum_eq_integral_range
import Submission.Work.BMF.mr_direct.halasz_window_range_gen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pointwise remainder bound on a general range

`Work.BMF.mr_direct.remPointwiseRange` is the general-range form of
`Work.BMF.mr_direct.remPointwise_le`: the weighted remainder sum

`Σ_{m ∈ ℕ ∩ [X₁,X₂]} g m · (ω(m;P,Q)+1)^{-1} · m^{-(1+it)}`

is `≤ C (log Q / log P) ((1+B²)e^{-B²/4} + 1/√T₀)` for every range with `X/4 ≤ X₁ ≤ X₂ ≤ 4X`,
provided `g` is `B`-far from every twist `n ↦ n^{iu}`, `|u| ≤ 4T₀`, at every scale
`x ∈ [X^{1/4}/16, 16X]`.

**Route.**  The weight is linearised by the integral identity
`(ω+1)^{-1} = ∫_0^1 x^ω dx` (`Work.BMF.mr_direct.omega_sum_eq_integral_range`), which turns the
sum into the integral over `x ∈ [0,1]` of the *multiplicative* weight `x^{ω(m;P,Q)}` times `g m`.
For fixed `x` the map `m ↦ x^{ω(m;P,Q)} g m` is multiplicative and `1`-bounded, so the general
range Halász bound `Work.BMF.mr_direct.halasz_window_range_gen` applies to it: the hypothesis
that `g` is `B`-far from every twist at scales `y ≥ X^{1/4}/16` transfers to `x^{ω} g` by
`omegaWeighted_dist_lower`, with `M₀ = 7B²/8` in place of `B²` and at scales
`y ∈ [X₁/4, X₂] ⊆ [X/16, 4X] ⊆ [X^{1/4}/16, 16X]`.  The Halász bound carries the factor
`X₂/X₁ ≤ 16` (because `X/4 ≤ X₁` and `X₂ ≤ 4X`), which is absorbed into the constant, and the
bracket `(1+M₀)e^{-M₀} ≤ (1+B²)e^{-B²/4}` together with `1 ≤ log Q / log P` finishes the proof.

The small range `X₁ < 16` forces `X < 64`, hence `X^{1/4}/16 < 2`: the distance hypothesis at
that scale reads `B ≤ 𝔻 g (n^{iu}) (X^{1/4}/16) = 0`, contradicting `B ≥ 1`, so the claim is
vacuous.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open BoundedMultiplicativeFunctions
open MeasureTheory intervalIntegral
open scoped BigOperators ComplexConjugate

noncomputable section

/-- `𝔻 f g x = 0` for `x < 2`: no prime is `≤ x`. -/
lemma D_eq_zero_of_lt_two {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 2) (f g : ℕ → ℂ) :
    BoundedMultiplicativeFunctions.𝔻 f g x = 0 := by
  unfold BoundedMultiplicativeFunctions.𝔻
  have hx1 : ⌊x⌋₊ ≤ 1 := by
    have h2 : ⌊x⌋₊ < 2 := (Nat.floor_lt (n := 2) hx0).mpr hx
    omega
  have hempty : ⌊x⌋₊.primesLE = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [Nat.mem_primesLE] at hp
    have : 2 ≤ p := hp.2.two_le
    omega
  rw [hempty, Finset.sum_empty]
  exact Real.zero_rpow (by norm_num)

/-- The main assembly: `remPointwiseRange` from a general-range Halász bound and the integral
identity `(ω+1)^{-1} = ∫_0^1 x^ω dx`. -/
theorem remPointwiseRange_of
    (Cw : ℝ) (hCw : 0 < Cw)
    (hw : ∀ (f : ℕ → ℂ) (X₁ X₂ M₀ T₀ t : ℝ),
      f 1 = 1 → (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) →
      (∀ n, ‖f n‖ ≤ 1) → 16 ≤ X₁ → X₁ ≤ X₂ → 0 < M₀ → 1 ≤ T₀ → |t| ≤ 2 * T₀ →
      (∀ y : ℝ, X₁ / 4 ≤ y → y ≤ X₂ → ∀ w : ℝ, |w| ≤ 4 * T₀ →
        M₀ ≤ BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * w)) y ^ 2) →
      ‖∑ m ∈ Work.BMF.natIcc X₁ X₂, f m * (m : ℂ) ^ (-(1 + Complex.I * t))‖
        ≤ Cw * (X₂ / X₁) * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 1 ≤ B →
      ∀ (g : ℕ → ℂ) (P Q X X₁ X₂ T₀ t : ℝ),
        g 1 = 1 → (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) →
        (∀ n, ‖g n‖ ≤ 1) → 2 ≤ P → P ≤ Q → 16 ≤ X → X / 4 ≤ X₁ → X₁ ≤ X₂ → X₂ ≤ 4 * X → 1 ≤ T₀ →
        (∀ (x : ℝ), X ^ (1/4:ℝ) / 16 ≤ x → x ≤ 16 * X → ∀ u : ℝ, |u| ≤ 4 * T₀ →
          B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) x) →
        (∑ p ∈ Work.BMF.primesIn P Q, 1 / (p : ℝ)) ≤ B ^ 2 / 8 →
        |t| ≤ 2 * T₀ →
        ‖∑ m ∈ Work.BMF.natIcc X₁ X₂,
            g m * (((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
              (m : ℂ) ^ (-(1 + Complex.I * t))‖
          ≤ C * (Real.log Q / Real.log P) *
              ((1 + B ^ 2) * Real.exp (-(B ^ 2 / 4)) + 1 / Real.sqrt T₀) := by
  refine ⟨16 * Cw, by positivity, ?_⟩
  intro B hB1 g P Q X X₁ X₂ T₀ t hg1 hgmul hgb hP hPQ hX hX1 hX12 hX2 hT0 hdist hL ht
  have hXpos : 0 < X := by linarith
  by_cases hX₁16 : 16 ≤ X₁
  · -- ===== the range is long enough for the general range Halász bound =====
    have hX₁pos : 0 < X₁ := by linarith
    have hlogP : 0 < Real.log P := Real.log_pos (by linarith : 1 < P)
    have hlog1 : 1 ≤ Real.log Q / Real.log P := by
      rw [one_le_div hlogP]
      exact Real.log_le_log (by linarith : 0 < P) hPQ
    have hXge1 : (1 : ℝ) ≤ X := by linarith
    have hquarter : X ^ (1/4:ℝ) / 16 ≤ X₁ / 4 := by
      have h := Real.rpow_le_self_of_one_le hXge1 (by norm_num : (1/4:ℝ) ≤ 1)
      linarith
    have hX₂16 : X₂ ≤ 16 * X := by linarith
    set M₀ : ℝ := 7 * B ^ 2 / 8 with hM₀
    have hM0pos : 0 < M₀ := by rw [hM₀]; nlinarith [sq_nonneg B]
    have hfac : (1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀ ≤
        (Real.log Q / Real.log P) *
          ((1 + B ^ 2) * Real.exp (-(B ^ 2 / 4)) + 1 / Real.sqrt T₀) := by
      have hexp : Real.exp (-M₀) ≤ Real.exp (-(B ^ 2 / 4)) := by
        apply Real.exp_le_exp.mpr
        rw [hM₀]; nlinarith
      have h1M : 1 + M₀ ≤ 1 + B ^ 2 := by rw [hM₀]; nlinarith
      have hbase : (1 + M₀) * Real.exp (-M₀) ≤ (1 + B ^ 2) * Real.exp (-(B ^ 2 / 4)) :=
        mul_le_mul h1M hexp (Real.exp_pos _).le (by nlinarith)
      have hbase_nn : 0 ≤ (1 + B ^ 2) * Real.exp (-(B ^ 2 / 4)) := by positivity
      have hA : (1 + M₀) * Real.exp (-M₀) ≤
          (Real.log Q / Real.log P) * ((1 + B ^ 2) * Real.exp (-(B ^ 2 / 4))) := by
        have hh : (1 + B ^ 2) * Real.exp (-(B ^ 2 / 4)) ≤
            (Real.log Q / Real.log P) * ((1 + B ^ 2) * Real.exp (-(B ^ 2 / 4))) := by
          have h := mul_le_mul_of_nonneg_right hlog1 hbase_nn
          rwa [one_mul] at h
        exact le_trans hbase hh
      have hsT_nn : 0 ≤ 1 / Real.sqrt T₀ := by positivity
      have hB' : 1 / Real.sqrt T₀ ≤ (Real.log Q / Real.log P) * (1 / Real.sqrt T₀) := by
        have hh := mul_le_mul_of_nonneg_right hlog1 hsT_nn
        rwa [one_mul] at hh
      rw [mul_add]
      exact add_le_add hA hB'
    have hF : ∀ x ∈ Set.Icc (0:ℝ) 1,
        ‖∑ m ∈ Work.BMF.natIcc X₁ X₂,
            omegaWeighted g P Q (x : ℂ) m * (m : ℂ) ^ (-(1 + Complex.I * t))‖
          ≤ Cw * (X₂ / X₁) * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) := by
      intro x hx
      have hr0 : 0 ≤ x := hx.1
      have hr1 : x ≤ 1 := hx.2
      have hdistx : ∀ y : ℝ, X₁ / 4 ≤ y → y ≤ X₂ → ∀ w : ℝ, |w| ≤ 4 * T₀ →
          M₀ ≤ BoundedMultiplicativeFunctions.𝔻 (omegaWeighted g P Q (x : ℂ))
            (fun n ↦ (n : ℂ) ^ (Complex.I * w)) y ^ 2 := by
        intro y hy1 hy2 w hw'
        have hy1' : X ^ (1/4:ℝ) / 16 ≤ y := by linarith
        have hy2' : y ≤ 16 * X := by linarith
        rw [hM₀]
        exact omegaWeighted_dist_lower g P Q B x y w hgb (by linarith) hr0 hr1 hL
          (hdist y hy1' hy2' w hw')
      exact hw (omegaWeighted g P Q (x : ℂ)) X₁ X₂ M₀ T₀ t
        (omegaWeighted_one g P Q (x : ℂ) hg1)
        (omegaWeighted_mul g P Q (x : ℂ) hgmul)
        (omegaWeighted_oneBounded g P Q hr0 hr1 hgb)
        hX₁16 hX12 hM0pos hT0 ht hdistx
    have hInt : ‖∫ x in (0:ℝ)..1,
        ∑ m ∈ Work.BMF.natIcc X₁ X₂,
          omegaWeighted g P Q (x : ℂ) m * (m : ℂ) ^ (-(1 + Complex.I * t))‖
        ≤ Cw * (X₂ / X₁) * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun x : ℝ => ∑ m ∈ Work.BMF.natIcc X₁ X₂,
          omegaWeighted g P Q (x : ℂ) m * (m : ℂ) ^ (-(1 + Complex.I * t)))
        (a := (0:ℝ)) (b := 1)
        (C := Cw * (X₂ / X₁) * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀))
        (fun x hx => by
          rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
          exact hF x ⟨le_of_lt hx.1, hx.2⟩)
      rwa [sub_zero, abs_one, mul_one] at h
    rw [omega_sum_eq_integral_range g P Q X₁ X₂ t]
    refine le_trans hInt ?_
    -- the growth factor `X₂/X₁ ≤ 16` is absorbed into the constant
    have hR16 : X₂ / X₁ ≤ 16 := by
      rw [div_le_iff₀ hX₁pos]
      linarith
    have hφnn : 0 ≤ (1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀ := by positivity
    have hstep1 : Cw * (X₂ / X₁) * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀)
        ≤ 16 * Cw * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) := by
      have h1 : (X₂ / X₁) * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀)
          ≤ 16 * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) :=
        mul_le_mul_of_nonneg_right hR16 hφnn
      calc Cw * (X₂ / X₁) * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀)
          = Cw * ((X₂ / X₁) * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀)) := by ring
        _ ≤ Cw * (16 * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀)) :=
              mul_le_mul_of_nonneg_left h1 hCw.le
        _ = 16 * Cw * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) := by ring
    calc Cw * (X₂ / X₁) * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀)
        ≤ 16 * Cw * ((1 + M₀) * Real.exp (-M₀) + 1 / Real.sqrt T₀) := hstep1
      _ ≤ 16 * Cw * ((Real.log Q / Real.log P) *
            ((1 + B ^ 2) * Real.exp (-(B ^ 2 / 4)) + 1 / Real.sqrt T₀)) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = 16 * Cw * (Real.log Q / Real.log P) *
            ((1 + B ^ 2) * Real.exp (-(B ^ 2 / 4)) + 1 / Real.sqrt T₀) := by ring
  · -- ===== vacuous: `X₁ < 16` forces `X < 64` and the distance hypothesis at a scale `< 2` =====
    exfalso
    have hXlt64 : X < 64 := by linarith
    set x₀ : ℝ := X ^ (1/4:ℝ) / 16 with hx₀
    have hx₀_nonneg : 0 ≤ x₀ := by
      rw [hx₀]
      exact div_nonneg (Real.rpow_nonneg hXpos.le _) (by norm_num)
    have hlt4 : X ^ (1/4:ℝ) < 4 := by
      have hpow : (X ^ (1/4:ℝ)) ^ 4 = X := by
        rw [← Real.rpow_natCast (X ^ (1/4:ℝ)) 4, ← Real.rpow_mul hXpos.le]
        norm_num
      have h4 : (X ^ (1/4:ℝ)) ^ 4 < (4 : ℝ) ^ 4 := by rw [hpow]; norm_num; linarith
      exact (pow_lt_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num : (4:ℕ) ≠ 0)).mp h4
    have hx₀_lt2 : x₀ < 2 := by rw [hx₀]; linarith
    have hx₀_ge : X ^ (1/4:ℝ) / 16 ≤ x₀ := by rw [hx₀]
    have hx₀_le : x₀ ≤ 16 * X := by rw [hx₀]; nlinarith
    have hBle : B ≤ BoundedMultiplicativeFunctions.𝔻 g
        (fun n ↦ (n : ℂ) ^ (Complex.I * (0:ℝ))) x₀ :=
      hdist x₀ hx₀_ge hx₀_le 0 (by rw [abs_zero]; linarith)
    have hD0 : BoundedMultiplicativeFunctions.𝔻 g
        (fun n ↦ (n : ℂ) ^ (Complex.I * (0:ℝ))) x₀ = 0 :=
      D_eq_zero_of_lt_two hx₀_nonneg hx₀_lt2 _ _
    rw [hD0] at hBle
    linarith

theorem remPointwiseRange :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 1 ≤ B →
      ∀ (g : ℕ → ℂ) (P Q X X₁ X₂ T₀ t : ℝ),
        g 1 = 1 → (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) →
        (∀ n, ‖g n‖ ≤ 1) → 2 ≤ P → P ≤ Q → 16 ≤ X → X / 4 ≤ X₁ → X₁ ≤ X₂ → X₂ ≤ 4 * X → 1 ≤ T₀ →
        (∀ (x : ℝ), X ^ (1/4:ℝ) / 16 ≤ x → x ≤ 16 * X → ∀ u : ℝ, |u| ≤ 4 * T₀ →
          B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) x) →
        (∑ p ∈ Work.BMF.primesIn P Q, 1 / (p : ℝ)) ≤ B ^ 2 / 8 →
        |t| ≤ 2 * T₀ →
        ‖∑ m ∈ Work.BMF.natIcc X₁ X₂,
            g m * (((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
              (m : ℂ) ^ (-(1 + Complex.I * t))‖
          ≤ C * (Real.log Q / Real.log P) *
              ((1 + B ^ 2) * Real.exp (-(B ^ 2 / 4)) + 1 / Real.sqrt T₀) := by
  obtain ⟨Cw, hCw, hw⟩ := Work.BMF.mr_direct.halasz_window_range_gen
  exact remPointwiseRange_of Cw hCw hw

end

end Work.BMF.mr_direct
