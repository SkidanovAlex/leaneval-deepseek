import Mathlib
import Submission.Work.FIChain.s3RemPlus_maj
import Submission.Work.FIChain.s3Rem_fibre_pt_le
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.zc_sharp_bounds
import Submission.Work.FIChain.s3RemMaj
import Submission.Work.FIChain.s3RemPlus_maj_le_defs
import Submission.Work.FIChain.remTerm_zavg_le_rect
import Submission.Work.FIChain.sum_rect_Fsub_le
import Submission.Work.FIChain.Ksub_rect_zavg_le

namespace Work.FIChain

open Finset MeasureTheory Filter
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The `z`-average of the REM majorant against `(R′)` (companion's (8.4))

This is the analytic piece of the companion's (8.4).  The `y`-average is NOT involved: it is
already disposed of by `Work.FIChain.rem_yavg_le` (PROVED in `s3RemPlus_maj`), and the reduction
from the target `Work.FIChain.s3RemPlus_zavg_le` to the statement below is
`Work.FIChain.s3RemPlus_zavg_le_of_maj` (PROVED in `Submission/Work/FIChain/s3RemPlus_zavg_le`).

MACHINERY ALREADY PROVED (in `Submission.Work.FIChain.s3RemPlus_maj`; import it, do NOT re-prove):
* scale facts: `Cm_ge_rpow : ∀ᶠ x, x^{3/10} ≤ ⌊(zc x B)^{1-η}⌋₊` and
  `x_div_Cm_le : ∀ᶠ x, x/⌊(zc x B)^{1-η}⌋₊ ≤ ⌈x^{7/10}⌉`.
* `remTerm` (the `ℓ`-th summand of `remMajU`), `remMajU_eq_sum_remTerm`,
  `remMajU_zavg_eq_sum : ∫_z remMajU/z = Σ_{ℓ ∈ Icc 1 x} ∫_z remTerm ℓ/z`,
  `remMajU_eq_sum_remTerm'` (the `ℓ`-sum restricted to `Icc 1 ⌊x/Cm⌋₊`, where `remTerm ≠ 0`),
  `remMaj1`, `remTerm_le_remMaj1`, `measurable_remMaj1`, `intervalIntegrable_remMaj1`,
  `intervalIntegrable_remTerm`, `measurable_remTerm`, `abs_int_maj_le`, `abs_remTerm_le`,
  `remMaj_int_abs_le`, `eventually_restrict_Icc`, `intervalIntegrable_const_div`, `sc_pos`.
* **`remTerm_zavg_le_sub`** (the §8.4 substitution, per `ℓ`):
  `∫_z remTerm ℓ/z ≤ τ(ℓ)² · ∫_{v=ℓ·zc}^{ℓ·e·zc} ∫_{w=ℓ}^{min (sc v/Cm) (x/Cm)}
     (if v ≤ x then s3RemSub x Cm ℓ (sc x B) v w else 0)/(v·w)`;
  after it the two `(1.7)`-scales are `⌊min (sc v) x⌋₊`, `⌊max v (Cm w)⌋₊` — `ℓ`-FREE.
* `Ksub x Cm B v w` — the `ℓ`-summed substituted integrand with the indicators
  `ℓ·zc ≤ v ≤ ℓ·e·zc`, `ℓ ≤ w`, `v ≤ x`.
* **`Ksub_le`** — the pointwise `(R′)` bound: for `v ≤ x`, `0 ≤ w ≤ x/Cm`,
  `⌊w⌋₊ ≤ ⌈x^{7/10}⌉`, `Ksub x Cm B v w ≤ 2·Ã(x)·(log x)^{-3}` (from
  `Work.FIChain.s3Rem_fibre_pt_le`).  Use it as the POINTWISE input.
* `Work.FIChain.s3Rem_fibre_pt_le` (the engine):
  `∃X₀, ∀x ≥ X₀, ∀N m₁ m₂, N ≤ ⌈x^{7/10}⌉ → m₁ ≤ x → m₂ ≤ x → ∀w, (∀ℓ, 0 ≤ w ℓ) →
   (∀ℓ, w ℓ ≤ τ(ℓ)²) → Σ_{ℓ≤x}Σ_{d≤x}[ℓ d ≤ N] w ℓ (|cfR (ℓ d) m₁| + |cfR (ℓ d) m₂|)
     ≤ 2·Ã(x)·(log x)^{-3}`.

ROUTE — everything left is `Finset`/measure bookkeeping, no new analysis.
1. `remMajU_eq_sum_remTerm'` and `remMajU_zavg_eq_sum` restrict the `ℓ`-sum to
   `Icc 1 ⌊x/Cm⌋₊` (choose `M := ⌊x/Cm⌋₊`), so `remTerm_zavg_le_sub` applies to every `ℓ` in it.
2. Sum the per-`ℓ` bound: `Σ_{ℓ ≤ M} τ(ℓ)² D_ℓ`.
3. Relax the ranges to the COMMON rectangle `[zc, V] × [1, x/Cm]` with `V := M · e · zc`
   (so `[ℓ zc, ℓ e zc] ⊆ [zc, V]` for `ℓ ≤ M`), keeping the indicators
   `1_{ℓ zc ≤ v ≤ ℓ e zc}`, `1_{ℓ ≤ w}` inside.  `v`-side: `MeasureTheory.setIntegral_mono_set`
   (or `intervalIntegral.integral_mono_interval`); `w`-side: the integrand is nonnegative and
   `ℓ ≤ T(v) := min (sc v/Cm) (x/Cm)` holds on the region because `Cm ≤ sc·zc` and `ℓ ≤ M`.
   The `v`- and `w`-integrals of the sum are interchanged with
   `intervalIntegral.integral_finsetSum`; the result is `∫_{zc}^{V} dv/v · ∫_1^{x/Cm} dw/w · Ksub`.
4. Apply `Ksub_le` pointwise (`N := ⌊w⌋₊`, `m₁ := ⌊min (sc v) x⌋₊ ≤ x`, `m₂ := ⌊max v (Cm w)⌋₊ ≤ x`
   from `v ≤ x`, `Cm w ≤ x`; `⌊w⌋₊ ≤ ⌈x^{7/10}⌉` from `w ≤ x/Cm ≤ ⌈x^{7/10}⌉`).
5. Measure: `∫_{zc}^{V} dv/v = log(V/zc) ≤ 1 + log M ≤ 2 log x`,
   `∫_1^{x/Cm} dw/w = log(x/Cm) ≤ log x`; total `≤ 2·Ã(x)(log x)^{-3}·2(log x)² = 4·Ã(x)(log x)^{-1}`.
   Take `C = 4`.

The three remaining pieces are the delegated lemmas
`Work.FIChain.remTerm_zavg_le_rect` (step 2–3, per `ℓ`),
`Work.FIChain.sum_rect_Fsub_le` (the `ℓ`-sum/interchange/domination by `Ksub`) and
`Work.FIChain.Ksub_rect_zavg_le` (steps 4–5); the definitions they share are in
`Submission.Work.FIChain.s3RemPlus_maj_le_defs`. -/

/-- The scale facts of the final assembly, collected for a single `x`:
`Cm := ⌊(zc x B)^{1-η}⌋₊` is `≥ 1` and `≤ sc x B · zc x B`, the inner length
`c := x/Cm ≥ 1` with `M := ⌊c⌋₊ ≤ x`, `zc x B` is positive with `zc ≤ e·zc`, the rectangle
`[zc, M·e·zc]` is nondegenerate, and `x ≥ e`. -/
private lemma scale_setup (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      1 ≤ ⌊(zc x B) ^ (1 - etac)⌋₊ ∧
      0 < zc x B ∧ zc x B ≤ Real.exp 1 * zc x B ∧
      ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) ≤ sc x B * zc x B ∧
      1 ≤ (x : ℝ) / ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) ∧
      (x : ℝ) / ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ)
        ≤ ((⌈(x : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℕ) : ℝ) ∧
      zc x B ≤ ((⌊(x : ℝ) / ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ)⌋₊ : ℕ) : ℝ)
        * (Real.exp 1 * zc x B) ∧
      ⌊(x : ℝ) / ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ)⌋₊ ≤ x ∧
      1 ≤ (x : ℝ) ∧ 1 ≤ Real.log (x : ℝ) := by
  filter_upwards [zc_sharp_bounds B hB, scale_factsC B hB, Cm_ge_rpow B hB, x_div_Cm_le B hB,
    Filter.eventually_ge_atTop 64] with x hsh hsf hCmg hxc hx64
  obtain ⟨-, -⟩ := hsh
  obtain ⟨-, -, -, -, -, -, -, -, hzcx, hZc1, -⟩ := hsf
  have hx64R : (64 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx64
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hx1ltR : (1 : ℝ) < (x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hlog1 : 1 ≤ Real.log (x : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
  have hzc1 : (1 : ℝ) ≤ zc x B := by
    have h : (1 : ℝ) ≤ (Zc x B : ℝ) := by exact_mod_cast hZc1
    simpa [zc] using h
  have hzcpos : 0 < zc x B := lt_of_lt_of_le zero_lt_one hzc1
  have hzcle : zc x B ≤ Real.exp 1 * zc x B :=
    le_mul_of_one_le_left hzcpos.le (Real.one_le_exp (by norm_num))
  have hCm1_nat : 1 ≤ ⌊(zc x B) ^ (1 - etac)⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((3 : ℝ) / 10) := Real.one_le_rpow hx1R (by norm_num)
    have h2 : (1 : ℝ) ≤ ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) := le_trans h1 hCmg
    have h3 : ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) ≤ (zc x B) ^ (1 - etac) :=
      Nat.floor_le (Real.rpow_nonneg hzcpos.le _)
    have h4 := le_trans h2 h3
    simpa using h4
  have hCm1R : (1 : ℝ) ≤ ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hCm1_nat
  have hCmpos : (0 : ℝ) < ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) := by linarith
  have hCm_le_zc : ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) ≤ zc x B := by
    refine le_trans (Nat.floor_le (Real.rpow_nonneg hzcpos.le _)) ?_
    exact Real.rpow_le_self_of_one_le hzc1 (by norm_num [etac])
  have hsc1 : (1 : ℝ) ≤ sc x B := by rw [sc]; exact one_le_pow₀ (by norm_num)
  have hCmzc : ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) ≤ sc x B * zc x B := by
    calc ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) ≤ zc x B := hCm_le_zc
      _ = 1 * zc x B := (one_mul _).symm
      _ ≤ sc x B * zc x B := mul_le_mul_of_nonneg_right hsc1 hzcpos.le
  have hCmx : ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) := le_trans hCm_le_zc hzcx
  have hc1 : 1 ≤ (x : ℝ) / ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) := by
    rw [le_div_iff₀ hCmpos, one_mul]
    exact hCmx
  have hM1 : 1 ≤ ⌊(x : ℝ) / ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ)⌋₊ := by
    refine Nat.le_floor ?_
    simpa using hc1
  have hMx : ⌊(x : ℝ) / ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ)⌋₊ ≤ x := by
    have h1 : (x : ℝ) / ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) := by
      rw [div_le_iff₀ hCmpos]
      exact le_mul_of_one_le_right hxpos.le hCm1R
    calc ⌊(x : ℝ) / ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ)⌋₊ ≤ ⌊(x : ℝ)⌋₊ := Nat.floor_mono h1
      _ = x := Nat.floor_natCast x
  have hV : zc x B ≤ ((⌊(x : ℝ) / ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ)⌋₊ : ℕ) : ℝ)
      * (Real.exp 1 * zc x B) := by
    have hMe : (1 : ℝ) ≤
        ((⌊(x : ℝ) / ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast hM1
    calc zc x B ≤ Real.exp 1 * zc x B := hzcle
      _ = 1 * (Real.exp 1 * zc x B) := (one_mul _).symm
      _ ≤ ((⌊(x : ℝ) / ((⌊(zc x B) ^ (1 - etac)⌋₊ : ℕ) : ℝ)⌋₊ : ℕ) : ℝ)
            * (Real.exp 1 * zc x B) :=
          mul_le_mul_of_nonneg_right hMe (by positivity)
  exact ⟨hCm1_nat, hzcpos, hzcle, hCmzc, hc1, hxc, hV, hMx, hx1R, hlog1⟩

theorem s3RemPlus_maj_le :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ) →
      2 ≤ Work.FIChain.sc x B →
      (∫ z in Work.FIChain.zc x B..(Real.exp 1 * Work.FIChain.zc x B),
          Work.FIChain.remMajU x ⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊
            (Work.FIChain.sc x B) z / z)
        ≤ C * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) := by
  obtain ⟨Xf, hf⟩ := s3Rem_fibre_pt_le
  refine ⟨4, by norm_num, fun B hB => ?_⟩
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.mp (scale_setup B hB)
  refine ⟨max Xf x1 + 1, fun x hx hYc hsc2 => ?_⟩
  have hXfx : Xf ≤ x := by omega
  have hx1x : x1 ≤ x := by omega
  obtain ⟨hCm1, hzcp, hzle, hCmzc, hc1, hxc, hV, hMx, hx1R, hlog1⟩ := hx1 x hx1x
  set Cm : ℕ := ⌊(zc x B) ^ (1 - etac)⌋₊ with hCmdef
  set M : ℕ := ⌊(x : ℝ) / (Cm : ℝ)⌋₊ with hMdef
  have hstep1 : (∫ z in zc x B..(Real.exp 1 * zc x B), remMajU x Cm (sc x B) z / z)
      = ∑ ℓ ∈ Finset.Icc 1 M, ∫ z in zc x B..(Real.exp 1 * zc x B),
          remTerm x Cm (sc x B) ℓ z / z := by
    have hfun : (fun z : ℝ => remMajU x Cm (sc x B) z / z)
        = fun z : ℝ => ∑ ℓ ∈ Finset.Icc 1 M, remTerm x Cm (sc x B) ℓ z / z := by
      funext z
      rw [remMajU_eq_sum_remTerm' x Cm (sc x B) z hCm1, Finset.sum_div]
    rw [hfun]
    exact intervalIntegral.integral_finsetSum (s := Finset.Icc 1 M)
      (fun ℓ hℓ => intervalIntegrable_remTerm x Cm B ℓ hCm1 (Finset.mem_Icc.mp hℓ).1
        (sc_pos x B).le hzcp hzle)
  have hstep2 : (∑ ℓ ∈ Finset.Icc 1 M, ∫ z in zc x B..(Real.exp 1 * zc x B),
          remTerm x Cm (sc x B) ℓ z / z)
      ≤ ∑ ℓ ∈ Finset.Icc 1 M, ∫ v in zc x B..((M : ℝ) * (Real.exp 1 * zc x B)),
          ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), Fsub x Cm B ℓ v w / (v * w) := by
    refine Finset.sum_le_sum (fun ℓ hℓ => ?_)
    rw [Finset.mem_Icc] at hℓ
    exact remTerm_zavg_le_rect x Cm B ℓ hCm1 hℓ.1 (by exact_mod_cast hℓ.2) hCmzc hzcp hzle hc1
  have hstep3 : (∑ ℓ ∈ Finset.Icc 1 M, ∫ v in zc x B..((M : ℝ) * (Real.exp 1 * zc x B)),
          ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), Fsub x Cm B ℓ v w / (v * w))
      ≤ ∫ v in zc x B..((M : ℝ) * (Real.exp 1 * zc x B)),
          ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), Ksub x Cm B v w / (v * w) :=
    sum_rect_Fsub_le x Cm B hCm1 hzcp hc1 hV hMx
  have hstep4 : (∫ v in zc x B..((M : ℝ) * (Real.exp 1 * zc x B)),
          ∫ w in (1 : ℝ)..((x : ℝ) / (Cm : ℝ)), Ksub x Cm B v w / (v * w))
      ≤ 4 * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(1 : ℤ)) :=
    Ksub_rect_zavg_le Xf x Cm B hf hXfx hxc hc1 hCm1 hzcp hV hx1R hlog1
  exact le_trans (le_trans (le_trans (le_of_eq hstep1) hstep2) hstep3) hstep4

end

end Work.FIChain
