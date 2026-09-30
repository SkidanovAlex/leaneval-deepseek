import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.norm_cpow_neg_I_mul
import Submission.Work.BMF.norm_cpow_I_sub_one_le
import Submission.Work.BMF.HL.primeRecips_loglog_split_all
import Submission.Work.BMF.HL.sum_log_div_prime_le
import Submission.Work.BMF.HL.sum_inv_p_log_p_le
import Submission.Work.BMF.HL.tail_average
import Submission.Work.BMF.HL.min_weight_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Slow variation of the minimised pretentious distance (`Work.BMF.halasz_lipschitz`)

`mHal f x T = min_{|t| ≤ T} Σ_{p ≤ x} (1 - Re (f p · p^{-it}))/p`; the theorem says that raising
the scale from `y` to `x ≥ y` can only increase this minimum by `log (log x / log y) + O(1)`,
with an absolute constant.

The proof is the standard "escape the nearest resonance" argument.  Let `t` be (the minimiser
at scale `y`, or any admissible frequency), `δ = min 1 (1/log y)`, and let
`Δ(θ) = Re Σ_{y < p ≤ x} f p · p^{-(t+θ)i}/p`.  Averaging `Δ` over `θ ∈ [0,δ]` and using
`|(1/δ)∫_0^δ p^{-iθ}dθ| ≤ min(1, 2/(δ log p))` produces `θ` with
`Δ(θ) ≥ -Σ_{y<p≤x} min(1,2/(δ log p))/p ≥ -K`; the weighted mass here is `O(1)` because the
`p ≤ y²` part costs `log 2 + O(1)` (Mertens) and the `p > y²` part is
`(2/δ)Σ 1/(p log p) = O(1)` by the sharp Mertens-type bound `Σ_{a<p≤b} 1/(p log p) ≤ C/log a`.
At that `θ` the head sum has grown by at most `|θ|·Σ_{p≤y}(log p)/p ≤ C`, and the tail has lost at
most `Σ_{y<p≤x} 1/p ≤ log(log x/log y) + O(1)` (Mertens), which is exactly the stated gain.

The three analytic inputs are proved in `Submission/Work/BMF/HL/` and imported above.
-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.BMF

namespace HLip

open Finset Real Complex

noncomputable def psum (f : ℕ → ℂ) (z t : ℝ) : ℝ :=
  ∑ p ∈ (⌊z⌋₊).primesLE, (1 - (f p * (p : ℂ) ^ (-(Complex.I * t))).re) / p

lemma mHal_eq_psum (f : ℕ → ℂ) (z T : ℝ) :
    mHal f z T = ⨅ (t : {t : ℝ // |t| ≤ T}), psum f z t.1 := rfl

lemma psum_nonneg {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (z t : ℝ) : 0 ≤ psum f z t := by
  rw [psum]
  apply Finset.sum_nonneg
  intro p hp
  have hpr : p.Prime := Nat.prime_of_mem_primesLE hp
  have hnorm : ‖f p * (p : ℂ) ^ (-(Complex.I * t))‖ ≤ 1 := by
    rw [norm_mul, norm_cpow_neg_I_mul t hpr.one_le, mul_one]
    exact hf p
  have hre : (f p * (p : ℂ) ^ (-(Complex.I * t))).re ≤ 1 := by
    have h := Complex.re_le_norm (f p * (p : ℂ) ^ (-(Complex.I * t)))
    linarith
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpr.pos
  exact div_nonneg (by linarith) hpR.le

lemma mHal_le_psum {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {z T t : ℝ} (ht : |t| ≤ T) :
    mHal f z T ≤ psum f z t := by
  rw [mHal_eq_psum]
  have hbd : BddBelow (Set.range (fun u : {u : ℝ // |u| ≤ T} => psum f z u.1)) :=
    ⟨0, by rintro y ⟨u, rfl⟩; exact psum_nonneg hf z u.1⟩
  exact ciInf_le (f := fun u : {u : ℝ // |u| ≤ T} => psum f z u.1) hbd ⟨t, ht⟩

lemma psum_sdiff {f : ℕ → ℂ} {y x t : ℝ} (hyx : y ≤ x) :
    psum f x t = psum f y t +
      ∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE,
        (1 - (f p * (p : ℂ) ^ (-(Complex.I * t))).re) / p := by
  rw [psum, psum, ← Finset.sum_sdiff (s₁ := (⌊y⌋₊).primesLE) (s₂ := (⌊x⌋₊).primesLE)
    (f := fun p => (1 - (f p * (p : ℂ) ^ (-(Complex.I * t))).re) / (p : ℝ))
    (Nat.primesLE_mono (Nat.floor_mono hyx))]
  ring

lemma cpow_ofReal_add (p : ℕ) (a b : ℝ) :
    (p : ℂ) ^ (-(Complex.I * ↑(a + b))) = (p : ℂ) ^ (-(Complex.I * (↑a + ↑b))) := by
  rw [Complex.ofReal_add]

lemma norm_cpow_neg_I_sub_one_le (θ s : ℝ) (hs : 1 ≤ s) :
    ‖(s : ℂ) ^ (-(Complex.I * θ)) - 1‖ ≤ |θ| * Real.log s := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs0
  rw [Complex.cpow_def_of_ne_zero hsne, ← Complex.ofReal_log hs0.le]
  have harg : (↑(Real.log s) : ℂ) * (-(Complex.I * ↑θ)) = Complex.I * ↑(-(Real.log s * θ)) := by
    push_cast; ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs]
  calc |2 * Real.sin (↑(-(Real.log s * θ)) / 2)| ≤ |-(Real.log s * θ)| := abs_two_mul_sin_half_le _
    _ = |θ| * Real.log s := by
        rw [abs_neg, abs_mul, abs_of_nonneg (Real.log_nonneg hs)]
        ring

lemma psum_head_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {y t θ : ℝ} :
    psum f y (t + θ) ≤ psum f y t + |θ| * ∑ p ∈ (⌊y⌋₊).primesLE, Real.log p / (p : ℝ) := by
  rw [psum, psum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hpr : p.Prime := Nat.prime_of_mem_primesLE hp
  have hp1 : 1 ≤ p := hpr.one_le
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpr.pos
  have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hpr.pos)
  have hsp : -(Complex.I * ↑(t + θ)) = -(Complex.I * ↑t) + -(Complex.I * ↑θ) := by
    push_cast; ring
  have hpow : (p : ℂ) ^ (-(Complex.I * ↑(t + θ))) =
      (p : ℂ) ^ (-(Complex.I * ↑t)) * (p : ℂ) ^ (-(Complex.I * ↑θ)) := by
    rw [hsp, Complex.cpow_add _ _ hpne]
  have hnt : ‖(p : ℂ) ^ (-(Complex.I * ↑t))‖ = 1 := norm_cpow_neg_I_mul t hp1
  have hbnd : ‖(1 : ℂ) - (p : ℂ) ^ (-(Complex.I * ↑θ))‖ ≤ |θ| * Real.log p := by
    rw [norm_sub_rev]
    exact norm_cpow_neg_I_sub_one_le θ (p : ℝ) (by exact_mod_cast hp1)
  have haux : |(f p * (p : ℂ) ^ (-(Complex.I * ↑t)) * (1 - (p : ℂ) ^ (-(Complex.I * ↑θ)))).re|
      ≤ |θ| * Real.log p := by
    calc |(f p * (p : ℂ) ^ (-(Complex.I * ↑t)) * (1 - (p : ℂ) ^ (-(Complex.I * ↑θ)))).re|
        ≤ ‖f p * (p : ℂ) ^ (-(Complex.I * ↑t)) * (1 - (p : ℂ) ^ (-(Complex.I * ↑θ)))‖ :=
          Complex.abs_re_le_norm _
      _ = ‖f p‖ * ‖(p : ℂ) ^ (-(Complex.I * ↑t))‖ * ‖(1 : ℂ) - (p : ℂ) ^ (-(Complex.I * ↑θ))‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ |θ| * Real.log p := by
          rw [hnt]
          calc ‖f p‖ * 1 * ‖(1 : ℂ) - (p : ℂ) ^ (-(Complex.I * ↑θ))‖
              = ‖f p‖ * ‖(1 : ℂ) - (p : ℂ) ^ (-(Complex.I * ↑θ))‖ := by ring
            _ ≤ 1 * (|θ| * Real.log p) :=
                mul_le_mul (hf p) hbnd (norm_nonneg _) (by positivity)
            _ = |θ| * Real.log p := by ring
  have hre : (f p * (p : ℂ) ^ (-(Complex.I * ↑t))).re -
      (f p * (p : ℂ) ^ (-(Complex.I * ↑(t + θ)))).re ≤ |θ| * Real.log p := by
    have heq : (f p * (p : ℂ) ^ (-(Complex.I * ↑t))).re -
        (f p * (p : ℂ) ^ (-(Complex.I * ↑(t + θ)))).re =
        (f p * (p : ℂ) ^ (-(Complex.I * ↑t)) * (1 - (p : ℂ) ^ (-(Complex.I * ↑θ)))).re := by
      rw [hpow, ← Complex.sub_re]
      congr 1
      ring
    rw [heq]
    exact le_trans (le_abs_self _) haux
  have hdiv : (1 - (f p * (p : ℂ) ^ (-(Complex.I * ↑(t + θ)))).re) / (p : ℝ) ≤
      (1 - (f p * (p : ℂ) ^ (-(Complex.I * ↑t))).re) / (p : ℝ) + |θ| * (Real.log p / (p : ℝ)) := by
    have h3 : ((f p * (p : ℂ) ^ (-(Complex.I * ↑t))).re -
        (f p * (p : ℂ) ^ (-(Complex.I * ↑(t + θ)))).re) / (p : ℝ) ≤
        |θ| * (Real.log p / (p : ℝ)) := by
      rw [div_le_iff₀ hpR]
      rw [show |θ| * (Real.log p / (p : ℝ)) * (p : ℝ) = |θ| * Real.log p by field_simp]
      exact hre
    have h4 : (1 - (f p * (p : ℂ) ^ (-(Complex.I * ↑(t + θ)))).re) / (p : ℝ) =
        (1 - (f p * (p : ℂ) ^ (-(Complex.I * ↑t))).re) / (p : ℝ) +
        ((f p * (p : ℂ) ^ (-(Complex.I * ↑t))).re -
         (f p * (p : ℂ) ^ (-(Complex.I * ↑(t + θ)))).re) / (p : ℝ) := by
      field_simp
      ring
    rw [h4]
    linarith
  simpa using hdiv

/-- Core inequality, with the three analytic inputs as hypotheses. -/
theorem core {CM CL K : ℝ} (hCM : 0 < CM) (hCL : 0 < CL) (hK : 0 < K)
    (hMert : ∀ x y : ℝ, 2 ≤ y → y ≤ x →
      (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE, (1 : ℝ) / p) ≤
        Real.log (Real.log x / Real.log y) + CM)
    (hHead : ∀ y : ℝ, 2 ≤ y →
      (∑ p ∈ (⌊y⌋₊).primesLE, Real.log p / (p : ℝ)) ≤ CL * Real.log y)
    (hTail : ∀ (g : ℕ → ℂ), (∀ n, ‖g n‖ ≤ 1) → ∀ (u y x : ℝ), 2 ≤ y → y ≤ x →
      ∃ θ ∈ Set.Icc (0 : ℝ) (min 1 (1 / Real.log y)),
        -K ≤ ∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE,
            (g p * (p : ℂ) ^ (-(Complex.I * (u + θ)))).re / (p : ℝ)) :
    ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ x y T : ℝ, 2 ≤ y → y ≤ x → 1 ≤ T →
      mHal f x (T + 1) ≤ mHal f y T + Real.log (Real.log x / Real.log y) + (CL + CM + K + 1) := by
  intro f hf x y T hy2 hyx hT
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  set δ : ℝ := min 1 (1 / Real.log y) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min one_pos (by positivity)
  have hδle1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδlog : δ * Real.log y ≤ 1 := by
    rw [hδdef]
    calc min 1 (1 / Real.log y) * Real.log y ≤ (1 / Real.log y) * Real.log y :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hlogy.le
      _ = 1 := by field_simp
  have key : ∀ t : ℝ, |t| ≤ T →
      mHal f x (T + 1) ≤ psum f y t + Real.log (Real.log x / Real.log y) + (CL + CM + K + 1) := by
    intro t ht
    obtain ⟨θ, hθ, hΔ⟩ := hTail f hf t y x hy2 hyx
    have heqexp : (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE,
        (f p * (p : ℂ) ^ (-(Complex.I * (↑t + ↑θ)))).re / (p : ℝ)) =
        (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE,
        (f p * (p : ℂ) ^ (-(Complex.I * ↑(t + θ)))).re / (p : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [cpow_ofReal_add]
    rw [heqexp] at hΔ
    have hθ0 : 0 ≤ θ := hθ.1
    have hθδ : θ ≤ δ := by rw [hδdef]; exact hθ.2
    have habsθ : |θ| = θ := abs_of_nonneg hθ0
    have htθ : |t + θ| ≤ T + 1 := by
      calc |t + θ| ≤ |t| + |θ| := abs_add_le _ _
        _ = |t| + θ := by rw [habsθ]
        _ ≤ T + 1 := by linarith
    have h1 : mHal f x (T + 1) ≤ psum f x (t + θ) := mHal_le_psum hf htθ
    have h2 := psum_sdiff (f := f) hyx (t := t + θ)
    have h4 : (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE,
          (1 - (f p * (p : ℂ) ^ (-(Complex.I * ↑(t + θ)))).re) / (p : ℝ)) =
        (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE, (1 : ℝ) / p) -
        ∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE,
          (f p * (p : ℂ) ^ (-(Complex.I * ↑(t + θ)))).re / (p : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    have h5 := hMert x y hy2 hyx
    have h3 := psum_head_le (f := f) hf (y := y) (t := t) (θ := θ)
    have hsum_nonneg : 0 ≤ ∑ p ∈ (⌊y⌋₊).primesLE, Real.log p / (p : ℝ) := by
      apply Finset.sum_nonneg
      intro p hp
      have hpr : p.Prime := Nat.prime_of_mem_primesLE hp
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpr.pos
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpr.one_le)) hpR.le
    have h6 : psum f y (t + θ) ≤ psum f y t + CL := by
      refine le_trans h3 ?_
      have hH : (∑ p ∈ (⌊y⌋₊).primesLE, Real.log p / (p : ℝ)) ≤ CL * Real.log y := hHead y hy2
      have hstep : |θ| * (∑ p ∈ (⌊y⌋₊).primesLE, Real.log p / (p : ℝ)) ≤
          δ * (CL * Real.log y) := by
        rw [habsθ]
        exact mul_le_mul hθδ hH hsum_nonneg hδpos.le
      have hd : δ * (CL * Real.log y) ≤ CL := by nlinarith [hδlog, hCL]
      linarith
    linarith
  haveI : Nonempty {t : ℝ // |t| ≤ T} := ⟨⟨0, by simp; linarith⟩⟩
  have hfin : mHal f x (T + 1) - (Real.log (Real.log x / Real.log y) + (CL + CM + K + 1)) ≤
      mHal f y T := by
    refine le_ciInf (f := fun u : {t : ℝ // |t| ≤ T} => psum f y u.1) ?_
    intro u
    linarith [key u.1 u.2]
  linarith

end HLip

/-- Slow variation (Lipschitz in the scale) of the minimised pretentious distance: if `f` is
1-bounded then the minimum of `Σ_{p ≤ y} (1 - Re (f p · p^{-it}))/p` over `|t| ≤ T` can only grow by
`log (log x / log y) + O(1)` when the scale `y ≤ x` is increased. The constant is ABSOLUTE. -/
theorem halasz_lipschitz :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ x y T : ℝ, 2 ≤ y → y ≤ x → 1 ≤ T →
        Work.BMF.mHal f x (T + 1) ≤ Work.BMF.mHal f y T + Real.log (Real.log x / Real.log y) + C := by
  obtain ⟨CM, hCMpos, hCM⟩ := Work.BMF.HL.primeRecips_loglog_split_all
  obtain ⟨CL, hCLpos, hCL⟩ := Work.BMF.HL.sum_log_div_prime_le
  obtain ⟨CI, hCIpos, hCI⟩ := Work.BMF.HL.sum_inv_p_log_p_le
  have hCM11 : ∀ x y : ℝ, 11 ≤ y → y ≤ x →
      (∑ p ∈ (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE, (1 : ℝ) / p) ≤
        Real.log (Real.log x / Real.log y) + CM :=
    fun x y hy hyx => hCM x y (by linarith) hyx
  obtain ⟨K, hKpos, hK⟩ := Work.BMF.HL.min_weight_bound hCMpos hCIpos hCM11 hCI
  have hTail := Work.BMF.HL.tail_average hKpos hK
  refine ⟨CL + CM + K + 1, by positivity, ?_⟩
  exact HLip.core hCMpos hCLpos hKpos hCM hCL hTail

end Work.BMF
