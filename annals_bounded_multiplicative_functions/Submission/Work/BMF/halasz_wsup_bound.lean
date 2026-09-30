import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_basic
import Submission.Work.BMF.halasz_lipschitz
import Submission.Work.BMF.halasz_mertens_aux
import Submission.Work.BMF.cross_sum_le
import Submission.Work.BMF.halasz_head_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open scoped BigOperators
open Finset Real Complex

/-! ## Elementary decomposition of `Re vF`

The real part of the truncated prime sum `vF f x (1+α+iτ)` factorises as
`Σ_{p ≤ x} p^{-(1+α)} Re (f p · p^{-iτ})`: the real factor `p^{-(1+α)}` pulls out of the
real part. -/

lemma vF_re_eq (f : ℕ → ℂ) (x α τ : ℝ) :
    (vF f x ((1 + α : ℝ) + τ * Complex.I)).re
      = ∑ p ∈ (⌊x⌋₊).primesLE,
          (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * τ))).re := by
  have hL : (vF f x ((1 + α : ℝ) + τ * Complex.I)).re
      = ∑ p ∈ (⌊x⌋₊).primesLE, (f p * (p : ℂ) ^ (-((1 + α : ℝ) + τ * Complex.I))).re := by
    unfold vF
    exact map_sum Complex.reAddGroupHom _ _
  rw [hL]
  apply Finset.sum_congr rfl
  intro p hp
  have hpr : p.Prime := Nat.prime_of_mem_primesLE hp
  have hp0 : (p : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast]; exact_mod_cast (ne_of_gt hpr.pos)
  have hsplit : -((1 + α : ℝ) + τ * Complex.I)
      = -(((1 + α : ℝ)) : ℂ) + (-(τ * Complex.I)) := by push_cast; ring
  rw [hsplit, Complex.cpow_add _ _ hp0]
  have hpos : (0:ℝ) ≤ (p:ℝ) := by positivity
  have hre : (p : ℂ) ^ (-(((1+α:ℝ)) : ℂ)) = ↑((p:ℝ) ^ (-(1+α))) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hpos (-(1 + α)), Complex.ofReal_neg]
  rw [hre]
  rw [show (p:ℂ) ^ (-(τ * Complex.I)) = (p:ℂ) ^ (-(Complex.I * τ)) from by ring_nf]
  rw [show f p * (↑((p:ℝ) ^ (-(1+α))) * (p:ℂ) ^ (-(Complex.I * τ)))
      = ↑((p:ℝ) ^ (-(1+α))) * (f p * (p:ℂ) ^ (-(Complex.I * τ))) by ring,
    Complex.re_ofReal_mul]

/-- Splitting a sum over the primes `≤ x` at the real cut-off `y ≤ x`. -/
lemma sum_primesLE_split {y x : ℝ} (hyx : y ≤ x) (g : ℕ → ℝ) :
    (∑ p ∈ (⌊x⌋₊).primesLE, g p)
      = (∑ p ∈ (⌊y⌋₊).primesLE, g p)
        + ∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))), g p := by
  have hB : (⌊y⌋₊).primesLE ⊆ (⌊x⌋₊).primesLE :=
    Nat.primesLE_mono (Nat.floor_mono hyx)
  have hfil : (⌊x⌋₊).primesLE \ (⌊y⌋₊).primesLE
      = (⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ)) := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨hpA, hpB⟩
      refine ⟨hpA, ?_⟩
      have hp := Nat.mem_primesLE.mp hpA
      have hlt : ⌊y⌋₊ < p := by
        by_contra h
        exact hpB (Nat.mem_primesLE.mpr ⟨not_lt.mp h, hp.2⟩)
      have hcast : ((⌊y⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hlt
      linarith [Nat.lt_floor_add_one y]
    · rintro ⟨hpA, hyp⟩
      refine ⟨hpA, ?_⟩
      intro hpB
      have hp := Nat.mem_primesLE.mp hpB
      have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.2.two_le
      have h1 : (p : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hp.1
      have hy0 : 0 ≤ y := by
        have h2' : (2:ℕ) ≤ ⌊y⌋₊ := by
          have : (2:ℝ) ≤ ((⌊y⌋₊:ℕ) : ℝ) := by linarith
          exact_mod_cast this
        have h1y : (1:ℝ) ≤ y := (Nat.floor_pos (a := y)).mp (by omega)
        linarith
      have hpy : (p : ℝ) ≤ y := le_trans h1 (Nat.floor_le hy0)
      linarith
  rw [← hfil]
  have hsd := Finset.sum_sdiff (s₁ := (⌊y⌋₊).primesLE) (s₂ := (⌊x⌋₊).primesLE)
    (f := g) hB
  linarith

/-- `Σ_{p ≤ y} p^{-(1+α)} Re (f p p^{-iτ}) ≤ Zrcp y` for `1`-bounded `f` and `α ≥ 0`. -/
lemma sum_head_le_Zrcp (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (y α τ : ℝ) (hα : 0 ≤ α) :
    (∑ p ∈ (⌊y⌋₊).primesLE,
        (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * τ))).re) ≤ Zrcp y := by
  calc ∑ p ∈ (⌊y⌋₊).primesLE,
        (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * τ))).re
      ≤ ∑ p ∈ (⌊y⌋₊).primesLE, (p : ℝ) ^ (-(1 + α)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpr : p.Prime := Nat.prime_of_mem_primesLE hp
        have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpr.pos
        have hnorm : ‖f p * (p:ℂ)^(-(Complex.I * τ))‖ ≤ 1 := by
          rw [norm_mul, norm_cpow_neg_I_mul τ hpr.one_le, mul_one]; exact hb p
        have hre : (f p * (p:ℂ)^(-(Complex.I * τ))).re ≤ 1 :=
          le_trans (Complex.re_le_norm _) hnorm
        calc (p:ℝ)^(-(1+α)) * (f p * (p:ℂ)^(-(Complex.I * τ))).re
            ≤ (p:ℝ)^(-(1+α)) * 1 := mul_le_mul_of_nonneg_left hre (rpow_nonneg hp0.le _)
          _ = (p:ℝ)^(-(1+α)) := mul_one _
    _ ≤ ∑ p ∈ (⌊y⌋₊).primesLE, (1:ℝ) / p := by
        apply Finset.sum_le_sum
        intro p hp
        have hpr : p.Prime := Nat.prime_of_mem_primesLE hp
        have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpr.one_le
        have hexp : -(1+α) ≤ -(1:ℝ) := by linarith
        calc (p:ℝ)^(-(1+α)) ≤ (p:ℝ)^(-(1:ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hp1 hexp
          _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
    _ = Zrcp y := rfl

/-- `Wsup f x α T ≤ Zrcp x` for `α ≥ 0` (trivial bound). -/
lemma Wsup_le_Zrcp (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x α T : ℝ) (hα : 0 ≤ α)
    (hT : 0 ≤ T) : Wsup f x α T ≤ Zrcp x := by
  haveI : Nonempty {t : ℝ // |t| ≤ T} := ⟨⟨0, by rw [abs_zero]; exact hT⟩⟩
  unfold Wsup
  refine ciSup_le (fun t => ?_)
  rw [vF_re_eq]
  exact sum_head_le_Zrcp f hb x α t.1 hα

/-! ## Comparison of `Zrcp` with two-sided Mertens -/

lemma Zrcp_sub_loglog_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 2 ≤ t → Zrcp t - Real.log (Real.log t) ≤ K := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  refine ⟨max C₀ (Zrcp 11 - Real.log (Real.log 2)), ?_, ?_⟩
  · exact lt_of_lt_of_le hC₀pos (le_max_left _ _)
  · intro t ht
    rcases le_or_gt 11 t with h11 | h11
    · have h : Zrcp t - Real.log (Real.log t) ≤ C₀ := by
        simpa only [Zrcp] using (abs_le.mp (hC₀ t h11)).2
      exact le_trans h (le_max_left _ _)
    · have hZt : Zrcp t ≤ Zrcp 11 := Zrcp_mono (le_of_lt h11)
      have h2t : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
      have hlog : Real.log (Real.log 2) ≤ Real.log (Real.log t) :=
        Real.log_le_log (Real.log_pos (by norm_num)) h2t
      have : Zrcp t - Real.log (Real.log t) ≤ Zrcp 11 - Real.log (Real.log 2) := by linarith
      exact le_trans this (le_max_right _ _)

lemma Zrcp_sub_loglog_lower :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 3 ≤ t → -K ≤ Zrcp t - Real.log (Real.log t) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  refine ⟨max C₀ (Real.log (Real.log 11) - Zrcp 3), ?_, ?_⟩
  · exact lt_of_lt_of_le hC₀pos (le_max_left _ _)
  · intro t ht
    rcases le_or_gt 11 t with h11 | h11
    · have h : -C₀ ≤ Zrcp t - Real.log (Real.log t) := by
        simpa only [Zrcp] using (abs_le.mp (hC₀ t h11)).1
      have hm : C₀ ≤ max C₀ (Real.log (Real.log 11) - Zrcp 3) := le_max_left _ _
      linarith
    · have hZt : Zrcp 3 ≤ Zrcp t := Zrcp_mono ht
      have hlog : Real.log (Real.log t) ≤ Real.log (Real.log 11) :=
        Real.log_le_log (Real.log_pos (by linarith))
          (Real.log_le_log (by linarith) (le_of_lt h11))
      have hm : Real.log (Real.log 11) - Zrcp 3
          ≤ max C₀ (Real.log (Real.log 11) - Zrcp 3) := le_max_right _ _
      linarith

/-- `Zrcp y - Zrcp x + log(log x / log y) ≤ C` for `2 ≤ y ≤ x`, `3 ≤ x`. -/
lemma Zrcp_loglog_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ, 2 ≤ y → y ≤ x → 3 ≤ x →
      Zrcp y - Zrcp x + Real.log (Real.log x / Real.log y) ≤ C := by
  obtain ⟨K, hKpos, hK⟩ := Zrcp_sub_loglog_upper
  obtain ⟨K', hK'pos, hK'⟩ := Zrcp_sub_loglog_lower
  refine ⟨K + K' + 1, by linarith, ?_⟩
  intro x y hy hyx hx3
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogdiv : Real.log (Real.log x / Real.log y)
      = Real.log (Real.log x) - Real.log (Real.log y) :=
    Real.log_div (ne_of_gt hlogx) (ne_of_gt hlogy)
  have h1 := hK y hy
  have h2 := hK' x hx3
  rw [hlogdiv]
  linarith

/-- Raising the window `T → 2T` at scale `x` against scale `y` costs `log(log x / log y) + O(1)`. -/
theorem mHal_window_lipschitz :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ x y T : ℝ, 2 ≤ y → y ≤ x → 1 ≤ T →
        mHal f x (2 * T) ≤ mHal f y T + Real.log (Real.log x / Real.log y) + C := by
  obtain ⟨C, hCpos, hC⟩ := halasz_lipschitz
  refine ⟨C, hCpos, ?_⟩
  intro f hf x y T hy hyx hT
  have h1 : mHal f x (2 * T) ≤ mHal f x (T + 1) :=
    mHal_anti f hf x (T + 1) (2 * T) (by linarith) (by linarith)
  have h2 : mHal f x (T + 1) ≤ mHal f y T + Real.log (Real.log x / Real.log y) + C :=
    hC f hf x y T hy hyx hT
  linarith

/-! ## The main statement -/

/-- Pointwise bounds for `Wsup` used in the Halász crossover.

(i) **Sharp bound**: for `3 ≤ x`, `1 ≤ T`, `1/log x ≤ α ≤ 1` and every `1`-bounded `f`,
`sup_{|t|≤T} Re Σ_{p≤x} f p p^{-1-α-it} ≤ Σ_{p≤x} 1/p - min_{|t|≤2T} Σ_{p≤x}(1-Re(f p p^{-it}))/p + O(1)`.
Route: put `y := exp (1/α)` (so `2 < y ≤ x`). For `|τ| ≤ T`,
`Re vF f x (1+α+iτ) = Σ_{p≤x} Re(f p p^{-1-α-iτ})`; splitting at `y` and using `|f p| ≤ 1`,
`Σ_{p≤y} Re(f p p^{-1-α-iτ}) ≤ Σ_{p≤y} Re(f p p^{-iτ})/p + Σ_{p≤y}(1-p^{-α})/p`, and
`Σ_{p≤y}(1-p^{-α})/p = O(α log y) = O(1)` since `α log y = 1`; while
`Σ_{y<p≤x} p^{-1-α} ≤ Σ_{y<p≤x} p^{-1-1/log y} ≤ C₂` by `halasz_mertens_aux`(iii). Since `|τ| ≤ T`,
`Σ_{p≤y}(1-Re(f p p^{-iτ}))/p ≥ mHal f y T`, so `Re vF f x (1+α+iτ) ≤ Zrcp y - mHal f y T + C₂ + O(1)`.
Finally
`Zrcp y - mHal f y T = (Zrcp y - Zrcp x) + (mHal f x (2T) - mHal f y T) + (Zrcp x - mHal f x (2T))`
with `Zrcp y - Zrcp x ≤ -log (α log x) + C₃` (two-sided Mertens,
`Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound`) and
`mHal f x (2T) ≤ mHal f x (T+1) ≤ mHal f y T + log (α log x) + C₁`
(`halasz_lipschitz` + `mHal_anti`, since `T + 1 ≤ 2T`). Finish with `ciSup_le`.

(ii) **Trivial bound** (Mertens): `Re vF f x (1+α+iτ) ≤ Σ_{p≤y} 1/p + Σ_{y<p≤x} p^{-1-α} ≤ Zrcp y + C₂
≤ Zrcp x - log (α log x) + C` with the same `y = exp (1/α)`. -/
theorem halasz_wsup_bound :
    (∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ x α T : ℝ, 3 ≤ x → 1 ≤ T →
        1 / Real.log x ≤ α → α ≤ 1 →
        Work.BMF.Wsup f x α T ≤ Work.BMF.Zrcp x - Work.BMF.mHal f x (2 * T) + C) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ x α T : ℝ, 3 ≤ x → 1 ≤ T →
        1 / Real.log x ≤ α → α ≤ 1 →
        Work.BMF.Wsup f x α T ≤ Work.BMF.Zrcp x - Real.log (α * Real.log x) + C) := by
  obtain ⟨C_A, hC_Apos, hC_A⟩ := cross_sum_le
  obtain ⟨C_Z, hC_Zpos, hC_Z⟩ := Zrcp_loglog_le
  obtain ⟨C_D, hC_Dpos, hC_D⟩ := mHal_window_lipschitz
  obtain ⟨C₂, hC₂pos, hC₂⟩ := halasz_mertens_aux.2.2
  have hZ11 : 0 ≤ Zrcp 11 := Zrcp_nonneg 11
  have hmax0 : (0:ℝ) ≤ max 0 (Real.log (Real.log 11)) := le_max_left _ _
  have hmax1 : Real.log (Real.log 11) ≤ max 0 (Real.log (Real.log 11)) := le_max_right _ _
  refine ⟨?_, ?_⟩
  · -- (i) sharp bound
    refine ⟨C_A + C_Z + C_D + C₂ + (2 * Zrcp 11 + 1), by linarith, ?_⟩
    intro f hb x α T hx3 hT hαlo hα1
    have hx1 : (1:ℝ) < x := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos hx1
    have hxpos : (0:ℝ) < x := by linarith
    have hαpos : 0 < α := lt_of_lt_of_le (one_div_pos.mpr hlogx_pos) hαlo
    have hαnn : 0 ≤ α := le_of_lt hαpos
    have hT0 : 0 ≤ T := by linarith
    rcases le_or_gt 11 x with hx11 | hx11
    · -- x ≥ 11
      set y : ℝ := Real.exp (1 / α) with hy_def
      have hlogy : Real.log y = 1 / α := by rw [hy_def, Real.log_exp]
      have hy2 : 2 < y := by
        rw [hy_def]
        have h1 : (1:ℝ) ≤ 1 / α := (one_le_div hαpos).mpr hα1
        calc (2:ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
          _ ≤ Real.exp (1 / α) := Real.exp_le_exp.mpr h1
      have hyx : y ≤ x := by
        rw [hy_def]
        have hylog : 1 / α ≤ Real.log x := by
          rw [div_le_iff₀ hαpos]
          have h' := (div_le_iff₀ hlogx_pos).mp hαlo
          linarith
        calc Real.exp (1 / α) ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hylog
          _ = x := Real.exp_log hxpos
      have hαlogy : α * Real.log y = 1 := by
        rw [hlogy, mul_one_div, div_self (ne_of_gt hαpos)]
      have hlogeq : Real.log (Real.log x / Real.log y) = Real.log (α * Real.log x) := by
        have h : Real.log x / Real.log y = α * Real.log x := by
          rw [hlogy, one_div, div_inv_eq_mul, mul_comm]
        rw [h]
      have hkey : ∀ t : {t : ℝ // |t| ≤ T},
          (vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re
            ≤ Zrcp x - mHal f x (2 * T) + (C_A + C_Z + C_D + C₂ + (2 * Zrcp 11 + 1)) := by
        intro t
        rw [vF_re_eq]
        have hsplit := sum_primesLE_split (y := y) (x := x) hyx
          (fun p => (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * t.1))).re)
        rw [hsplit]
        have hhead := halasz_head_bound f hb (y := y) (α := α) (T := T) (τ := t.1) hαnn t.2
        have hcross : (∑ p ∈ (⌊y⌋₊).primesLE, (1 - (p : ℝ) ^ (-α)) / p) ≤ C_A :=
          hC_A α y hαpos (le_of_lt hy2) (le_of_eq hαlogy)
        have htail : (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))),
              (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * t.1))).re) ≤ C₂ := by
          calc (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))),
                (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * t.1))).re)
              ≤ ∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))),
                  (p : ℝ) ^ (-(1 + α)) := by
                apply Finset.sum_le_sum
                intro p hp
                have hp1 : p ∈ (⌊x⌋₊).primesLE := Finset.mem_of_mem_filter p hp
                have hpr : p.Prime := Nat.prime_of_mem_primesLE hp1
                have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpr.pos
                have hnorm : ‖f p * (p:ℂ)^(-(Complex.I * t.1))‖ ≤ 1 := by
                  rw [norm_mul, norm_cpow_neg_I_mul t.1 hpr.one_le, mul_one]; exact hb p
                have hre : (f p * (p:ℂ)^(-(Complex.I * t.1))).re ≤ 1 :=
                  le_trans (Complex.re_le_norm _) hnorm
                calc (p:ℝ)^(-(1+α)) * (f p * (p:ℂ)^(-(Complex.I * t.1))).re
                    ≤ (p:ℝ)^(-(1+α)) * 1 :=
                      mul_le_mul_of_nonneg_left hre (rpow_nonneg hp0.le _)
                  _ = (p:ℝ)^(-(1+α)) := mul_one _
            _ ≤ ∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))),
                  (1:ℝ) / (p : ℝ) ^ (1 + α) := by
                apply Finset.sum_le_sum
                intro p hp
                have hp1 : p ∈ (⌊x⌋₊).primesLE := Finset.mem_of_mem_filter p hp
                have hpr : p.Prime := Nat.prime_of_mem_primesLE hp1
                have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpr.pos
                rw [one_div, Real.rpow_neg hp0.le]
            _ ≤ C₂ := hC₂ α y x hαpos hα1 hy2 hx11 (le_of_eq hαlogy.symm)
        have hZ : Zrcp y - Zrcp x ≤ -Real.log (α * Real.log x) + C_Z := by
          have h := hC_Z x y (le_of_lt hy2) hyx hx3
          rw [hlogeq] at h
          linarith
        have hD : mHal f x (2 * T) - mHal f y T ≤ Real.log (α * Real.log x) + C_D := by
          have h := hC_D f hb x y T (le_of_lt hy2) hyx hT
          rw [hlogeq] at h
          linarith
        linarith [hhead, hcross, htail, hZ, hD, hZ11]
      haveI : Nonempty {t : ℝ // |t| ≤ T} := ⟨⟨0, by rw [abs_zero]; exact hT0⟩⟩
      unfold Wsup
      exact ciSup_le hkey
    · -- x < 11
      have hx11le : x ≤ 11 := le_of_lt hx11
      have hW : Wsup f x α T ≤ Zrcp x := Wsup_le_Zrcp f hb x α T hαnn hT0
      have hm : mHal f x (2 * T) ≤ 2 * Zrcp x := mHal_le_two_Zrcp f hb x (2 * T) (by linarith)
      have hZx : Zrcp x ≤ Zrcp 11 := Zrcp_mono hx11le
      have hfin : Zrcp x ≤ Zrcp x - mHal f x (2 * T)
          + (C_A + C_Z + C_D + C₂ + (2 * Zrcp 11 + 1)) := by linarith
      exact le_trans hW hfin
  · -- (ii) trivial bound
    refine ⟨C_Z + C₂ + (max 0 (Real.log (Real.log 11)) + 1), by linarith, ?_⟩
    intro f hb x α T hx3 hT hαlo hα1
    have hx1 : (1:ℝ) < x := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos hx1
    have hxpos : (0:ℝ) < x := by linarith
    have hαpos : 0 < α := lt_of_lt_of_le (one_div_pos.mpr hlogx_pos) hαlo
    have hαnn : 0 ≤ α := le_of_lt hαpos
    have hT0 : 0 ≤ T := by linarith
    rcases le_or_gt 11 x with hx11 | hx11
    · set y : ℝ := Real.exp (1 / α) with hy_def
      have hlogy : Real.log y = 1 / α := by rw [hy_def, Real.log_exp]
      have hy2 : 2 < y := by
        rw [hy_def]
        have h1 : (1:ℝ) ≤ 1 / α := (one_le_div hαpos).mpr hα1
        calc (2:ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
          _ ≤ Real.exp (1 / α) := Real.exp_le_exp.mpr h1
      have hyx : y ≤ x := by
        rw [hy_def]
        have hylog : 1 / α ≤ Real.log x := by
          rw [div_le_iff₀ hαpos]
          have h' := (div_le_iff₀ hlogx_pos).mp hαlo
          linarith
        calc Real.exp (1 / α) ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hylog
          _ = x := Real.exp_log hxpos
      have hαlogy : α * Real.log y = 1 := by
        rw [hlogy, mul_one_div, div_self (ne_of_gt hαpos)]
      have hlogeq : Real.log (Real.log x / Real.log y) = Real.log (α * Real.log x) := by
        have h : Real.log x / Real.log y = α * Real.log x := by
          rw [hlogy, one_div, div_inv_eq_mul, mul_comm]
        rw [h]
      have hkey : ∀ t : {t : ℝ // |t| ≤ T},
          (vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re
            ≤ Zrcp x - Real.log (α * Real.log x)
              + (C_Z + C₂ + (max 0 (Real.log (Real.log 11)) + 1)) := by
        intro t
        rw [vF_re_eq]
        have hsplit := sum_primesLE_split (y := y) (x := x) hyx
          (fun p => (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * t.1))).re)
        rw [hsplit]
        have hhead : (∑ p ∈ (⌊y⌋₊).primesLE,
              (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * t.1))).re) ≤ Zrcp y :=
          sum_head_le_Zrcp f hb y α t.1 hαnn
        have htail : (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))),
              (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * t.1))).re) ≤ C₂ := by
          calc (∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))),
                (p : ℝ) ^ (-(1 + α)) * (f p * (p : ℂ) ^ (-(Complex.I * t.1))).re)
              ≤ ∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))),
                  (p : ℝ) ^ (-(1 + α)) := by
                apply Finset.sum_le_sum
                intro p hp
                have hp1 : p ∈ (⌊x⌋₊).primesLE := Finset.mem_of_mem_filter p hp
                have hpr : p.Prime := Nat.prime_of_mem_primesLE hp1
                have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpr.pos
                have hnorm : ‖f p * (p:ℂ)^(-(Complex.I * t.1))‖ ≤ 1 := by
                  rw [norm_mul, norm_cpow_neg_I_mul t.1 hpr.one_le, mul_one]; exact hb p
                have hre : (f p * (p:ℂ)^(-(Complex.I * t.1))).re ≤ 1 :=
                  le_trans (Complex.re_le_norm _) hnorm
                calc (p:ℝ)^(-(1+α)) * (f p * (p:ℂ)^(-(Complex.I * t.1))).re
                    ≤ (p:ℝ)^(-(1+α)) * 1 :=
                      mul_le_mul_of_nonneg_left hre (rpow_nonneg hp0.le _)
                  _ = (p:ℝ)^(-(1+α)) := mul_one _
            _ ≤ ∑ p ∈ ((⌊x⌋₊).primesLE.filter (fun p : ℕ => y < (p : ℝ))),
                  (1:ℝ) / (p : ℝ) ^ (1 + α) := by
                apply Finset.sum_le_sum
                intro p hp
                have hp1 : p ∈ (⌊x⌋₊).primesLE := Finset.mem_of_mem_filter p hp
                have hpr : p.Prime := Nat.prime_of_mem_primesLE hp1
                have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpr.pos
                rw [one_div, Real.rpow_neg hp0.le]
            _ ≤ C₂ := hC₂ α y x hαpos hα1 hy2 hx11 (le_of_eq hαlogy.symm)
        have hZ : Zrcp y ≤ Zrcp x - Real.log (α * Real.log x) + C_Z := by
          have h := hC_Z x y (le_of_lt hy2) hyx hx3
          rw [hlogeq] at h
          linarith
        linarith [hhead, htail, hZ, hmax0]
      haveI : Nonempty {t : ℝ // |t| ≤ T} := ⟨⟨0, by rw [abs_zero]; exact hT0⟩⟩
      unfold Wsup
      exact ciSup_le hkey
    · -- x < 11
      have hx11le : x ≤ 11 := le_of_lt hx11
      have hW : Wsup f x α T ≤ Zrcp x := Wsup_le_Zrcp f hb x α T hαnn hT0
      have hlogx11 : Real.log x ≤ Real.log 11 :=
        Real.log_le_log hxpos hx11le
      have hαlogx_le : α * Real.log x ≤ Real.log 11 := by
        have : α * Real.log x ≤ 1 * Real.log x :=
          mul_le_mul_of_nonneg_right hα1 hlogx_pos.le
        linarith
      have h1x : 1 ≤ α * Real.log x := (div_le_iff₀ hlogx_pos).mp hαlo
      have hlogle : Real.log (α * Real.log x) ≤ Real.log (Real.log 11) :=
        Real.log_le_log (by linarith) hαlogx_le
      have hfin : Zrcp x ≤ Zrcp x - Real.log (α * Real.log x)
          + (C_Z + C₂ + (max 0 (Real.log (Real.log 11)) + 1)) := by
        linarith [hC_Zpos, hC₂pos, hmax0, hmax1]
      exact le_trans hW hfin

end Work.BMF
