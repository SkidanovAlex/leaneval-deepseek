import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_core_defs
import Submission.Work.BMF.mr_direct.coprime_primesIn_iff
import Submission.Work.BMF.mr_core.coprime_prod_iff
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary arithmetic lemmas for `Work.BMF.mr_core.badPart_le2`

The assembly of `badPart_le2` (proved in `Submission/Work/BMF/mr_core/badPart_le2.lean`)
is reduced to a handful of self-contained arithmetic/analytic statements, collected here:

* `badPart_le2_pieceC`, `badPart_le2_pieceB`-style splitting of the per-cell bound: the
  `log (2T) (log Y)^{-199}` term (`pieceC`), the trivial Buchstab error term (`pieceD`),
  and the size of `(2T + 3Y)/Y` (`div_le`);
* `badPart_le2_invPrimes_lower`: the Mertens lower bound for `Σ_{p ∈ [P_c, Q_c]} 1/p`;
* `badPart_le2_coprime_recip`: the Turán–Kubilius bound for the reciprocal sum over the
  integers coprime to all primes of `[P,Q]` (no sieve, a second-moment argument).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Finset MeasureTheory intervalIntegral Filter
open scoped BigOperators

namespace Work.BMF.mr_core


private lemma rpow_47_48_sq (L : ℝ) (hL : 0 ≤ L) :
    (L ^ (47 / 48 : ℝ)) ^ 2 = L ^ (47 / 24 : ℝ) := by
  rw [← Real.rpow_natCast (L ^ (47 / 48 : ℝ)) 2, ← Real.rpow_mul hL]
  norm_num

private lemma rpow_one_mul_neg199 (L : ℝ) (hL : 0 < L) :
    L * L ^ (-(199 : ℝ)) = L ^ (-(198 : ℝ)) := by
  nth_rewrite 1 [show L = L ^ (1 : ℝ) by rw [Real.rpow_one]]
  rw [← Real.rpow_add hL]
  norm_num

private lemma rpow_47_24_mul_neg198 (L : ℝ) (hL : 0 < L) :
    L ^ (47 / 24 : ℝ) * L ^ (-(198 : ℝ)) = L ^ (-(198 - 47 / 24 : ℝ)) := by
  rw [← Real.rpow_add hL]
  congr 1
  ring

private lemma rpow_47_48_mul_neg198 (L : ℝ) (hL : 0 < L) :
    L ^ (47 / 48 : ℝ) * L ^ (-(198 : ℝ)) = L ^ (-(198 - 47 / 48 : ℝ)) := by
  rw [← Real.rpow_add hL]
  congr 1
  ring

theorem badPart_le2_pieceC (ε Cbs Cm K Ac B Y T : ℝ)
    (hε : 0 < ε) (hCbs : 0 < Cbs) (hCm : 0 < Cm) (hK : 2 ≤ K) (hAc : 1 ≤ Ac)
    (hY : 1 ≤ Y) (hT : 0 < T)
    (hlog : Real.log (2 * T) ≤ 2 * Real.log Y)
    (hev : 2 * Cbs * Cm * (K ^ 2 * Ac ^ 2 * (Real.log Y) ^ (-(198 - 47 / 24 : ℝ))
        + 2 * K * Ac * (Real.log Y) ^ (-(198 - 47 / 48 : ℝ))) ≤ ε / 32) :
    Cbs * (K * (Ac - 1) * Work.BMF.mrCore.logPc Y) *
        (K * (Ac - 1) * Work.BMF.mrCore.logPc Y + 2) *
        (Cm * Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)))
      ≤ ε / 32 := by
  set L : ℝ := Real.log Y with hLdef
  have hLnn : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg hY
  have hlogPc_eq : Work.BMF.mrCore.logPc Y = L ^ (47 / 48 : ℝ) := by
    rw [Work.BMF.mrCore.logPc, hLdef]
  have hAnn : 0 ≤ Ac - 1 := by linarith
  by_cases hL0 : L = 0
  · have hlp : Work.BMF.mrCore.logPc Y = 0 := by
      rw [hlogPc_eq, hL0]
      exact Real.zero_rpow (by norm_num : (47 / 48 : ℝ) ≠ 0)
    rw [hlp]
    have hz : Cbs * (K * (Ac - 1) * 0) * (K * (Ac - 1) * 0 + 2) *
        (Cm * Real.log (2 * T) * L ^ (-(199 : ℝ))) = 0 := by ring
    rw [hz]
    linarith only [hε]
  · have hLpos : 0 < L := lt_of_le_of_ne hLnn (Ne.symm hL0)
    set Lp : ℝ := L ^ (47 / 48 : ℝ) with hLpdef
    have hLpnn : 0 ≤ Lp := by rw [hLpdef]; exact Real.rpow_nonneg hLnn _
    set a : ℝ := K * (Ac - 1) * Work.BMF.mrCore.logPc Y with hadef
    have ha_eq : a = K * (Ac - 1) * Lp := by rw [hadef, hlogPc_eq, hLpdef]
    have hA : a * (a + 2) ≤ K ^ 2 * Ac ^ 2 * Lp ^ 2 + 2 * K * Ac * Lp := by
      rw [ha_eq]
      have hle : K * (Ac - 1) ≤ K * Ac := by nlinarith only [hAnn, hK]
      have h1 : K * (Ac - 1) * Lp ≤ K * Ac * Lp :=
        mul_le_mul_of_nonneg_right hle hLpnn
      have h1nn : 0 ≤ K * (Ac - 1) * Lp := mul_nonneg (mul_nonneg (by linarith) hAnn) hLpnn
      have h2 : (K * (Ac - 1) * Lp) ^ 2 ≤ (K * Ac * Lp) ^ 2 :=
        pow_le_pow_left₀ h1nn h1 2
      have h3 : (K * (Ac - 1) * Lp) * 2 ≤ (K * Ac * Lp) * 2 :=
        mul_le_mul_of_nonneg_right h1 (by norm_num)
      have e1 : (K * (Ac - 1) * Lp) * ((K * (Ac - 1) * Lp) + 2)
          = (K * (Ac - 1) * Lp) ^ 2 + (K * (Ac - 1) * Lp) * 2 := by ring
      have e2 : (K * Ac * Lp) ^ 2 + (K * Ac * Lp) * 2
          = K ^ 2 * Ac ^ 2 * Lp ^ 2 + 2 * K * Ac * Lp := by ring
      rw [e1]
      calc (K * (Ac - 1) * Lp) ^ 2 + (K * (Ac - 1) * Lp) * 2
          ≤ (K * Ac * Lp) ^ 2 + (K * Ac * Lp) * 2 := add_le_add h2 h3
        _ = K ^ 2 * Ac ^ 2 * Lp ^ 2 + 2 * K * Ac * Lp := e2
    have hLp2 : Lp ^ 2 = L ^ (47 / 24 : ℝ) := by
      rw [hLpdef]; exact rpow_47_48_sq L hLnn
    have hU : Real.log (2 * T) * L ^ (-(199 : ℝ)) ≤ (2 * L) * L ^ (-(199 : ℝ)) :=
      mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hLnn _)
    have hstep1 : Cbs * a * (a + 2) * (Cm * Real.log (2 * T) * L ^ (-(199 : ℝ)))
        ≤ Cbs * (a * (a + 2)) * (Cm * ((2 * L) * L ^ (-(199 : ℝ)))) := by
      have h2 : Cm * Real.log (2 * T) * L ^ (-(199 : ℝ))
          ≤ Cm * ((2 * L) * L ^ (-(199 : ℝ))) := by
        calc Cm * Real.log (2 * T) * L ^ (-(199 : ℝ))
            = Cm * (Real.log (2 * T) * L ^ (-(199 : ℝ))) := by ring
          _ ≤ Cm * ((2 * L) * L ^ (-(199 : ℝ))) := mul_le_mul_of_nonneg_left hU hCm.le
      have h3 : 0 ≤ Cbs * (a * (a + 2)) := by positivity
      calc Cbs * a * (a + 2) * (Cm * Real.log (2 * T) * L ^ (-(199 : ℝ)))
          = Cbs * (a * (a + 2)) * (Cm * Real.log (2 * T) * L ^ (-(199 : ℝ))) := by ring
        _ ≤ Cbs * (a * (a + 2)) * (Cm * ((2 * L) * L ^ (-(199 : ℝ)))) :=
              mul_le_mul_of_nonneg_left h2 h3
    have hstep2 : Cbs * (a * (a + 2)) * (Cm * ((2 * L) * L ^ (-(199 : ℝ))))
        ≤ Cbs * (K ^ 2 * Ac ^ 2 * Lp ^ 2 + 2 * K * Ac * Lp) *
            (Cm * ((2 * L) * L ^ (-(199 : ℝ)))) := by
      have h4 : 0 ≤ Cm * ((2 * L) * L ^ (-(199 : ℝ))) := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hCbs.le) h4
    have hstep3 : Cbs * (K ^ 2 * Ac ^ 2 * Lp ^ 2 + 2 * K * Ac * Lp) *
            (Cm * ((2 * L) * L ^ (-(199 : ℝ))))
        = 2 * Cbs * Cm * (K ^ 2 * Ac ^ 2 * L ^ (-(198 - 47 / 24 : ℝ))
            + 2 * K * Ac * L ^ (-(198 - 47 / 48 : ℝ))) := by
      have hL198 : 2 * L * L ^ (-(199 : ℝ)) = 2 * L ^ (-(198 : ℝ)) := by
        have h := rpow_one_mul_neg199 L hLpos
        calc 2 * L * L ^ (-(199 : ℝ)) = 2 * (L * L ^ (-(199 : ℝ))) := by ring
          _ = 2 * L ^ (-(198 : ℝ)) := by rw [h]
      have hX : L ^ (47 / 24 : ℝ) * L ^ (-(198 : ℝ)) = L ^ (-(198 - 47 / 24 : ℝ)) :=
        rpow_47_24_mul_neg198 L hLpos
      have hY' : L ^ (47 / 48 : ℝ) * L ^ (-(198 : ℝ)) = L ^ (-(198 - 47 / 48 : ℝ)) :=
        rpow_47_48_mul_neg198 L hLpos
      rw [hLp2, hLpdef, hL198]
      rw [show Cbs * (K ^ 2 * Ac ^ 2 * L ^ (47 / 24 : ℝ) + 2 * K * Ac * L ^ (47 / 48 : ℝ)) *
              (Cm * (2 * L ^ (-(198 : ℝ))))
            = Cbs * Cm * 2 * ((K ^ 2 * Ac ^ 2 * L ^ (47 / 24 : ℝ) + 2 * K * Ac * L ^ (47 / 48 : ℝ))
                * L ^ (-(198 : ℝ))) by ring]
      rw [show 2 * Cbs * Cm * (K ^ 2 * Ac ^ 2 * L ^ (-(198 - 47 / 24 : ℝ))
              + 2 * K * Ac * L ^ (-(198 - 47 / 48 : ℝ)))
            = Cbs * Cm * 2 * (K ^ 2 * Ac ^ 2 * L ^ (-(198 - 47 / 24 : ℝ))
              + 2 * K * Ac * L ^ (-(198 - 47 / 48 : ℝ))) by ring]
      congr 1
      rw [add_mul]
      rw [show K ^ 2 * Ac ^ 2 * L ^ (47 / 24 : ℝ) * L ^ (-(198 : ℝ))
          = K ^ 2 * Ac ^ 2 * (L ^ (47 / 24 : ℝ) * L ^ (-(198 : ℝ))) by ring, hX]
      rw [show 2 * K * Ac * L ^ (47 / 48 : ℝ) * L ^ (-(198 : ℝ))
          = 2 * K * Ac * (L ^ (47 / 48 : ℝ) * L ^ (-(198 : ℝ))) by ring, hY']
    have hmain : 2 * Cbs * Cm * (K ^ 2 * Ac ^ 2 * L ^ (-(198 - 47 / 24 : ℝ))
        + 2 * K * Ac * L ^ (-(198 - 47 / 48 : ℝ)))
        = 2 * Cbs * Cm * (K ^ 2 * Ac ^ 2 * (Real.log Y) ^ (-(198 - 47 / 24 : ℝ))
        + 2 * K * Ac * (Real.log Y) ^ (-(198 - 47 / 48 : ℝ))) := by rw [hLdef]
    calc Cbs * (K * (Ac - 1) * Work.BMF.mrCore.logPc Y) *
            (K * (Ac - 1) * Work.BMF.mrCore.logPc Y + 2) *
            (Cm * Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)))
        = Cbs * a * (a + 2) * (Cm * Real.log (2 * T) * L ^ (-(199 : ℝ))) := by
          rw [← hadef, ← hLdef]
      _ ≤ Cbs * (a * (a + 2)) * (Cm * ((2 * L) * L ^ (-(199 : ℝ)))) := hstep1
      _ ≤ Cbs * (K ^ 2 * Ac ^ 2 * Lp ^ 2 + 2 * K * Ac * Lp) *
            (Cm * ((2 * L) * L ^ (-(199 : ℝ)))) := hstep2
      _ = 2 * Cbs * Cm * (K ^ 2 * Ac ^ 2 * L ^ (-(198 - 47 / 24 : ℝ))
            + 2 * K * Ac * L ^ (-(198 - 47 / 48 : ℝ))) := hstep3
      _ = 2 * Cbs * Cm * (K ^ 2 * Ac ^ 2 * (Real.log Y) ^ (-(198 - 47 / 24 : ℝ))
            + 2 * K * Ac * (Real.log Y) ^ (-(198 - 47 / 48 : ℝ))) := hmain
      _ ≤ ε / 32 := hev

theorem badPart_le2_pieceD (ε Cbs K Pc Sc D : ℝ)
    (hε : 0 < ε) (hCbs : 0 < Cbs) (hK : 0 < K) (hPc : 0 < Pc) (hSc : 0 ≤ Sc)
    (hD : 0 ≤ D)
    (h1 : Cbs * D / K ≤ ε / 96) (h2 : Cbs * D / Pc ≤ ε / 96) (h3 : Cbs * D * Sc ≤ ε / 96) :
    Cbs * D * (1 / K + 1 / Pc + Sc) ≤ ε / 32 := by
  have h : Cbs * D * (1 / K + 1 / Pc + Sc) = Cbs * D / K + Cbs * D / Pc + Cbs * D * Sc := by
    ring
  rw [h]
  linarith only [h1, h2, h3]

theorem badPart_le2_div_le (C₀ ε θ Y H T : ℝ)
    (hε : 0 < ε) (hC₀ : 0 < C₀) (hθ : 0 < θ) (hY : 1 ≤ Y)
    (hHθ : Y ^ θ ≤ H) (hH : H ≤ Y) (hT : T ≤ 2 * C₀ / ε * (Y / H)) :
    (2 * T + 3 * Y) / Y ≤ 3 + 4 * C₀ / ε := by
  have hYpos : 0 < Y := by linarith
  have hH1 : 1 ≤ H := le_trans (Real.one_le_rpow hY hθ.le) hHθ
  have hHpos : 0 < H := by linarith
  have hCnn : 0 ≤ 2 * C₀ / ε := by positivity
  have h1H : 1 / H ≤ 1 := by
    rw [div_le_one hHpos]; linarith
  have hTY : T / Y ≤ 2 * C₀ / ε := by
    have h : T * (1 / Y) ≤ (2 * C₀ / ε) * (Y / H) * (1 / Y) :=
      mul_le_mul_of_nonneg_right hT (by positivity)
    have heq : (2 * C₀ / ε) * (Y / H) * (1 / Y) = (2 * C₀ / ε) * (1 / H) := by
      field_simp
    have h2 : (2 * C₀ / ε) * (1 / H) ≤ 2 * C₀ / ε := by
      have := mul_le_mul_of_nonneg_left h1H hCnn
      simpa using this
    have h3 : T * (1 / Y) = T / Y := by ring
    linarith only [h, h3, heq, h2]
  have h2TY : 2 * (T / Y) ≤ 4 * C₀ / ε := by
    have h1 : 2 * (T / Y) ≤ 2 * (2 * C₀ / ε) := by linarith only [hTY]
    have h2 : 2 * (2 * C₀ / ε) = 4 * C₀ / ε := by ring
    linarith only [h1, h2]
  have hmain : (2 * T + 3 * Y) / Y = 2 * (T / Y) + 3 := by
    field_simp
    try ring
  rw [hmain]
  linarith only [h2TY]



theorem badPart_le2_invPrimes_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 256 * C ≤ B ^ 2 →
      ∀ᶠ Y in Filter.atTop,
        B ^ 2 / 128 ≤ (∑ p ∈ Work.BMF.primesIn (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y),
            1 / (p : ℝ)) := by
  obtain ⟨Cm, hCmpos, hCm⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  refine ⟨Cm + 1, by linarith, fun B hB => ?_⟩
  have hBC : 256 * Cm ≤ B ^ 2 := by linarith [hB]
  have hlogPc_tend : Filter.Tendsto (fun Y : ℝ => Work.BMF.mrCore.logPc Y)
      Filter.atTop Filter.atTop := by
    show Filter.Tendsto (fun Y : ℝ => (Real.log Y) ^ (47 / 48 : ℝ)) Filter.atTop Filter.atTop
    exact (tendsto_rpow_atTop (y := (47 / 48 : ℝ)) (by norm_num)).comp Real.tendsto_log_atTop
  have hPctend : Filter.Tendsto (fun Y : ℝ => Work.BMF.mrCore.Pc Y) Filter.atTop Filter.atTop := by
    show Filter.Tendsto (fun Y : ℝ => Real.exp (Work.BMF.mrCore.logPc Y)) Filter.atTop Filter.atTop
    exact Real.tendsto_exp_atTop.comp hlogPc_tend
  filter_upwards [hPctend.eventually (Filter.eventually_ge_atTop (11 : ℝ)),
      Filter.eventually_gt_atTop (1 : ℝ)] with Y hPc11 hYgt
  have hPcpos : (0:ℝ) < Work.BMF.mrCore.Pc Y := by linarith
  have hAcpos : 0 < Work.BMF.mrCore.Ac B := by
    rw [Work.BMF.mrCore.Ac]; exact Real.exp_pos _
  have hAc1 : 1 ≤ Work.BMF.mrCore.Ac B := by
    rw [Work.BMF.mrCore.Ac]; exact Real.one_le_exp (by positivity)
  have hlogPcpos : 0 < Work.BMF.mrCore.logPc Y := by
    rw [Work.BMF.mrCore.logPc]
    exact Real.rpow_pos_of_pos (Real.log_pos hYgt) _
  have hPcleQc : Work.BMF.mrCore.Pc Y ≤ Work.BMF.mrCore.Qc B Y := by
    rw [Work.BMF.mrCore.Pc, Work.BMF.mrCore.Qc]
    apply Real.exp_le_exp.mpr
    rw [Work.BMF.mrCore.logQc]
    nlinarith only [hlogPcpos, hAc1]
  have hQc11 : (11:ℝ) ≤ Work.BMF.mrCore.Qc B Y := le_trans hPc11 hPcleQc
  have hlogQcpos : 0 < Work.BMF.mrCore.logQc B Y := by
    rw [Work.BMF.mrCore.logQc]; exact mul_pos hAcpos hlogPcpos
  -- Mertens at the two endpoints
  have hQ := hCm (Work.BMF.mrCore.Qc B Y) hQc11
  have hP := hCm (Work.BMF.mrCore.Pc Y) hPc11
  have hQ' : Real.log (Real.log (Work.BMF.mrCore.Qc B Y)) - Cm
      ≤ (∑ p ∈ Nat.primesLE ⌊Work.BMF.mrCore.Qc B Y⌋₊, 1 / (p : ℝ)) := by
    have h := (abs_le.mp hQ).1
    linarith only [h]
  have hP' : (∑ p ∈ Nat.primesLE ⌊Work.BMF.mrCore.Pc Y⌋₊, 1 / (p : ℝ))
      ≤ Real.log (Real.log (Work.BMF.mrCore.Pc Y)) + Cm := by
    have h := (abs_le.mp hP).2
    linarith only [h]
  -- the log identity
  have hlogQc : Real.log (Real.log (Work.BMF.mrCore.Qc B Y))
      = Real.log (Work.BMF.mrCore.logQc B Y) := by
    rw [Work.BMF.mrCore.Qc, Real.log_exp]
  have hlogPc : Real.log (Real.log (Work.BMF.mrCore.Pc Y))
      = Real.log (Work.BMF.mrCore.logPc Y) := by
    rw [Work.BMF.mrCore.Pc, Real.log_exp]
  have hratio : Work.BMF.mrCore.logQc B Y / Work.BMF.mrCore.logPc Y = Work.BMF.mrCore.Ac B := by
    rw [Work.BMF.mrCore.logQc]; field_simp
  have hlogid : Real.log (Real.log (Work.BMF.mrCore.Qc B Y))
      - Real.log (Real.log (Work.BMF.mrCore.Pc Y)) = B ^ 2 / 64 := by
    rw [hlogQc, hlogPc]
    calc Real.log (Work.BMF.mrCore.logQc B Y) - Real.log (Work.BMF.mrCore.logPc Y)
        = Real.log (Work.BMF.mrCore.logQc B Y / Work.BMF.mrCore.logPc Y) :=
          (Real.log_div (ne_of_gt hlogQcpos) (ne_of_gt hlogPcpos)).symm
      _ = Real.log (Work.BMF.mrCore.Ac B) := by rw [hratio]
      _ = B ^ 2 / 64 := by rw [Work.BMF.mrCore.Ac, Real.log_exp]
  -- the sum comparison
  have hmono : (⌊Work.BMF.mrCore.Pc Y⌋₊ : ℕ) ≤ ⌊Work.BMF.mrCore.Qc B Y⌋₊ :=
    Nat.floor_mono hPcleQc
  have hsub : Nat.primesLE ⌊Work.BMF.mrCore.Pc Y⌋₊ ⊆ Nat.primesLE ⌊Work.BMF.mrCore.Qc B Y⌋₊ := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 hmono, hp.2⟩
  have hdiff : (∑ p ∈ Nat.primesLE ⌊Work.BMF.mrCore.Qc B Y⌋₊, 1 / (p : ℝ))
        - (∑ p ∈ Nat.primesLE ⌊Work.BMF.mrCore.Pc Y⌋₊, 1 / (p : ℝ))
      = ∑ p ∈ Nat.primesLE ⌊Work.BMF.mrCore.Qc B Y⌋₊ \ Nat.primesLE ⌊Work.BMF.mrCore.Pc Y⌋₊,
          1 / (p : ℝ) := by
    have h := Finset.sum_sdiff hsub (f := fun p : ℕ => 1 / (p : ℝ))
    linarith only [h]
  have hsub2 : Nat.primesLE ⌊Work.BMF.mrCore.Qc B Y⌋₊ \ Nat.primesLE ⌊Work.BMF.mrCore.Pc Y⌋₊
      ⊆ Work.BMF.primesIn (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y) := by
    intro p hp
    rw [Finset.mem_sdiff, Nat.mem_primesLE] at hp
    obtain ⟨⟨hpQ, hpprime⟩, hpP⟩ := hp
    rw [Nat.mem_primesLE] at hpP
    have hgt : ⌊Work.BMF.mrCore.Pc Y⌋₊ < p := by
      by_contra h
      exact hpP ⟨not_lt.mp h, hpprime⟩
    rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, hpQ⟩, hpprime⟩
    have hceil := Nat.ceil_le_floor_add_one (Work.BMF.mrCore.Pc Y)
    omega
  have hScmp : (∑ p ∈ Nat.primesLE ⌊Work.BMF.mrCore.Qc B Y⌋₊, 1 / (p : ℝ))
        - (∑ p ∈ Nat.primesLE ⌊Work.BMF.mrCore.Pc Y⌋₊, 1 / (p : ℝ))
      ≤ (∑ p ∈ Work.BMF.primesIn (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y),
            1 / (p : ℝ)) := by
    rw [hdiff]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun x _ _ => by positivity)
  -- conclude
  have h1 : B ^ 2 / 64 - 2 * Cm
      ≤ (∑ p ∈ Nat.primesLE ⌊Work.BMF.mrCore.Qc B Y⌋₊, 1 / (p : ℝ))
        - (∑ p ∈ Nat.primesLE ⌊Work.BMF.mrCore.Pc Y⌋₊, 1 / (p : ℝ)) := by
    linarith only [hQ', hP', hlogid]
  have h2 : B ^ 2 / 128 ≤ B ^ 2 / 64 - 2 * Cm := by nlinarith only [hBC]
  linarith only [h1, h2, hScmp]



/-- For naturals, `(a : ℝ) / m - 1 ≤ a / m`. -/
private lemma floor_div_lower (a m : ℕ) (hm : 0 < m) :
    (a : ℝ) / m - 1 ≤ ((a / m : ℕ) : ℝ) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hnat : a < (a / m + 1) * m := by
    calc a = a / m * m + a % m := (Nat.div_add_mod' a m).symm
      _ < a / m * m + m := Nat.add_lt_add_left (Nat.mod_lt a hm) _
      _ = (a / m + 1) * m := by ring
  have hR : (a : ℝ) < (((a / m : ℕ) : ℝ) + 1) * (m : ℝ) := by
    exact_mod_cast hnat
  have htarget : (a : ℝ) / m < ((a / m : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hmR]
    exact hR
  linarith

theorem badPart_le2_coprime_recip (P Q X₁ X₂ : ℝ) (hP2 : 2 ≤ P) (hPQ : P ≤ Q)
    (hX1 : 1 ≤ X₁) (hX12 : X₁ ≤ X₂) (hX24 : X₂ ≤ 4 * X₁) (hQ2 : Q ^ 2 ≤ X₁)
    (hS : 1 ≤ ∑ p ∈ Work.BMF.primesIn P Q, 1 / (p : ℝ)) :
    (∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter
        (fun n => n.Coprime (∏ p ∈ Work.BMF.primesIn P Q, p)), 1 / (n : ℝ))
      ≤ 100 / (∑ p ∈ Work.BMF.primesIn P Q, 1 / (p : ℝ)) := by
  set S' : Finset ℕ := Work.BMF.primesIn P Q with hS'def
  set Sp : ℝ := ∑ p ∈ S', 1 / (p : ℝ) with hSpdef
  have hSp1 : 1 ≤ Sp := hS
  have hSppos : 0 < Sp := lt_of_lt_of_le zero_lt_one hSp1
  have hQpos : 0 < Q := by linarith
  have hX2pos : 0 < X₂ := by linarith
  have hX1pos : 0 < X₁ := by linarith
  have hprime : ∀ p ∈ S', p.Prime := by
    intro p hp
    rw [hS'def] at hp
    exact (Work.BMF.mr_direct.mem_primesIn_iff.mp hp).1
  set om : ℕ → ℝ := fun n => ∑ p ∈ S', (if p ∣ n then (1:ℝ) else 0) with homdef
  have homdef' : ∀ n : ℕ, om n = ∑ p ∈ S', (if p ∣ n then (1:ℝ) else 0) := fun n => rfl
  have homzero : ∀ n : ℕ, om n = 0 ↔ n.Coprime (∏ p ∈ S', p) := by
    intro n
    rw [homdef', coprime_prod_iff S' hprime n]
    constructor
    · intro h p hp
      by_contra hdiv
      have hpos : 0 < ∑ q ∈ S', (if q ∣ n then (1:ℝ) else 0) := by
        refine Finset.sum_pos' (fun q _ => ?_) ⟨p, hp, ?_⟩
        · split <;> norm_num
        · rw [if_pos hdiv]; norm_num
      linarith
    · intro h
      apply Finset.sum_eq_zero
      intro p hp
      rw [if_neg (h p hp)]
  set Y₂ : ℕ := ⌊X₂⌋₊ with hY₂def
  set T : Finset ℕ := Finset.Ioc 0 Y₂ with hTdef
  have hTcard : ((T.card : ℝ)) = (Y₂ : ℝ) := by
    rw [hTdef, Nat.card_Ioc, tsub_zero]
  have hY₂le : (Y₂ : ℝ) ≤ X₂ := Nat.floor_le (le_of_lt hX2pos)
  have hX₂leY₂ : X₂ - 1 ≤ (Y₂ : ℝ) := le_of_lt (Nat.sub_one_lt_floor X₂)
  have hπnn : (0:ℝ) ≤ (S'.card : ℝ) := by positivity
  -- first moment
  have hsum1 : ∑ n ∈ T, om n = ∑ p ∈ S', ((T.filter (fun n => p ∣ n)).card : ℝ) := by
    simp only [homdef']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun n hn => ?_)
    split <;> norm_num
  have hcard_eq1 : ∀ p ∈ S', ((T.filter (fun n => p ∣ n)).card : ℝ) = ((Y₂ / p : ℕ) : ℝ) := by
    intro p hp
    congr 1
    rw [hTdef]
    exact Nat.Ioc_filter_dvd_card_eq_div Y₂ p
  have hsum1_lb : X₂ * Sp - 2 * (S'.card : ℝ) ≤ ∑ n ∈ T, om n := by
    rw [hsum1]
    have hpt : ∀ p ∈ S', X₂ / (p:ℝ) - 2 ≤ ((T.filter (fun n => p ∣ n)).card : ℝ) := by
      intro p hp
      have hpR : (0:ℝ) < p := by
        have := (hprime p hp).pos; exact_mod_cast this
      have hp1 : (1:ℝ) ≤ p := by
        have := (hprime p hp).one_le; exact_mod_cast this
      rw [hcard_eq1 p hp]
      have h1 : (Y₂ : ℝ)/p - 1 ≤ ((Y₂ / p : ℕ) : ℝ) := floor_div_lower Y₂ p (hprime p hp).pos
      have h2 : (X₂ - 1)/p ≤ (Y₂ : ℝ)/p := div_le_div_of_nonneg_right hX₂leY₂ hpR.le
      have h3 : X₂/p ≤ (X₂ - 1)/p + 1/p := le_of_eq (by ring)
      have h4 : 1/(p:ℝ) ≤ 1 := by
        rw [div_le_one hpR]; exact hp1
      linarith
    have hsplit : ∑ p ∈ S', (X₂ / (p:ℝ) - 2) = X₂ * Sp - 2 * (S'.card : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      have h : ∑ p ∈ S', X₂ / (p:ℝ) = X₂ * Sp := by
        rw [hSpdef, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        ring
      rw [h]
      ring
    rw [← hsplit]
    exact Finset.sum_le_sum hpt
  -- second moment
  have hsum2 : ∑ n ∈ T, (om n)^2
      = ∑ p ∈ S', ∑ q ∈ S', ((T.filter (fun n => p ∣ n ∧ q ∣ n)).card : ℝ) := by
    have hpt : ∀ n, (om n)^2 = ∑ p ∈ S', ∑ q ∈ S',
        (if p ∣ n then (1:ℝ) else 0) * (if q ∣ n then (1:ℝ) else 0) := by
      intro n
      show (∑ p ∈ S', (if p ∣ n then (1:ℝ) else 0))^2 = _
      rw [sq, Finset.sum_mul_sum]
    calc ∑ n ∈ T, (om n)^2
        = ∑ n ∈ T, ∑ p ∈ S', ∑ q ∈ S',
            (if p ∣ n then (1:ℝ) else 0) * (if q ∣ n then (1:ℝ) else 0) :=
          Finset.sum_congr rfl (fun n _ => hpt n)
      _ = ∑ p ∈ S', ∑ q ∈ S', ∑ n ∈ T,
            (if p ∣ n then (1:ℝ) else 0) * (if q ∣ n then (1:ℝ) else 0) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [Finset.sum_comm]
      _ = ∑ p ∈ S', ∑ q ∈ S', ((T.filter (fun n => p ∣ n ∧ q ∣ n)).card : ℝ) := by
          refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
          rw [Finset.card_filter]
          push_cast
          refine Finset.sum_congr rfl (fun n hn => ?_)
          by_cases h1 : p ∣ n <;> by_cases h2 : q ∣ n <;> simp [h1, h2]
  have hcard_eq2 : ∀ p ∈ S', ∀ q ∈ S',
      ((T.filter (fun n => p ∣ n ∧ q ∣ n)).card : ℝ) = ((Y₂ / Nat.lcm p q : ℕ) : ℝ) := by
    intro p hp q hq
    congr 1
    have hset : T.filter (fun n => p ∣ n ∧ q ∣ n) = T.filter (fun n => Nat.lcm p q ∣ n) := by
      apply Finset.filter_congr
      intro n hn
      rw [Nat.lcm_dvd_iff]
    rw [hset, hTdef]
    exact Nat.Ioc_filter_dvd_card_eq_div Y₂ (Nat.lcm p q)
  have hlcm_ub : ∑ p ∈ S', ∑ q ∈ S', 1/((Nat.lcm p q : ℕ) : ℝ) ≤ Sp + Sp * Sp := by
    have hstep : ∀ p ∈ S', ∑ q ∈ S', 1/((Nat.lcm p q : ℕ) : ℝ)
        ≤ 1/(p:ℝ) + ∑ q ∈ S', 1/((p:ℝ)*(q:ℝ)) := by
      intro p hp
      have hdiag : 1/((Nat.lcm p p : ℕ) : ℝ) = 1/(p:ℝ) := by
        rw [Nat.lcm_self]
      have herase : ∑ q ∈ S'.erase p, 1/((Nat.lcm p q : ℕ) : ℝ)
          ≤ ∑ q ∈ S'.erase p, 1/((p:ℝ)*(q:ℝ)) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        have hmem := Finset.mem_erase.mp hq
        have hne : p ≠ q := hmem.1.symm
        have hqp : q.Prime := hprime q hmem.2
        have hcop : Nat.Coprime p q := (Nat.coprime_primes (hprime p hp) hqp).mpr hne
        rw [hcop.lcm_eq_mul, Nat.cast_mul]
      rw [← Finset.add_sum_erase S' (fun q => 1/((Nat.lcm p q : ℕ) : ℝ)) hp, hdiag]
      refine add_le_add le_rfl ?_
      refine le_trans herase (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset p S') (fun q _ _ => by positivity))
    calc ∑ p ∈ S', ∑ q ∈ S', 1/((Nat.lcm p q : ℕ) : ℝ)
        ≤ ∑ p ∈ S', (1/(p:ℝ) + ∑ q ∈ S', 1/((p:ℝ)*(q:ℝ))) := Finset.sum_le_sum hstep
      _ = Sp + Sp * Sp := by
          rw [Finset.sum_add_distrib, hSpdef]
          congr 1
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
          rw [div_mul_div_comm]; norm_num
  have hsum2_ub : ∑ n ∈ T, (om n)^2 ≤ (Y₂:ℝ) * (Sp + Sp^2) := by
    rw [hsum2]
    calc ∑ p ∈ S', ∑ q ∈ S', ((T.filter (fun n => p ∣ n ∧ q ∣ n)).card : ℝ)
        = ∑ p ∈ S', ∑ q ∈ S', ((Y₂ / Nat.lcm p q : ℕ) : ℝ) :=
          Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => hcard_eq2 p hp q hq))
      _ ≤ ∑ p ∈ S', ∑ q ∈ S', (Y₂:ℝ) / ((Nat.lcm p q : ℕ) : ℝ) :=
          Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => Nat.cast_div_le))
      _ = (Y₂:ℝ) * (∑ p ∈ S', ∑ q ∈ S', 1/((Nat.lcm p q : ℕ) : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun q hq => ?_)
          ring
      _ ≤ (Y₂:ℝ) * (Sp + Sp * Sp) := mul_le_mul_of_nonneg_left hlcm_ub (by positivity)
      _ = (Y₂:ℝ) * (Sp + Sp^2) := by ring
  -- the variance bound
  have hvar : ((T.filter (fun n => n.Coprime (∏ p ∈ S', p))).card : ℝ) * Sp^2
      ≤ ∑ n ∈ T, (om n - Sp)^2 := by
    calc ((T.filter (fun n => n.Coprime (∏ p ∈ S', p))).card : ℝ) * Sp^2
        = ∑ n ∈ T.filter (fun n => n.Coprime (∏ p ∈ S', p)), Sp^2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ T.filter (fun n => n.Coprime (∏ p ∈ S', p)), (om n - Sp)^2 := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          rw [Finset.mem_filter] at hn
          have hz : om n = 0 := (homzero n).mpr hn.2
          rw [hz]
          nlinarith [sq_nonneg Sp]
      _ ≤ ∑ n ∈ T, (om n - Sp)^2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun n _ _ => sq_nonneg _)
  have hexp : ∑ n ∈ T, (om n - Sp)^2
      = (∑ n ∈ T, (om n)^2) - 2 * Sp * (∑ n ∈ T, om n) + (T.card : ℝ) * Sp^2 := by
    have h1 : ∑ n ∈ T, (om n - Sp)^2 = ∑ n ∈ T, ((om n)^2 - 2 * Sp * om n + Sp^2) :=
      Finset.sum_congr rfl (fun n _ => by ring)
    have h2 : ∑ n ∈ T, ((om n)^2 - 2 * Sp * om n + Sp^2)
        = (∑ n ∈ T, (om n)^2) - (∑ n ∈ T, 2 * Sp * om n) + (∑ n ∈ T, Sp^2) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h3 : ∑ n ∈ T, 2 * Sp * om n = 2 * Sp * (∑ n ∈ T, om n) := by
      rw [Finset.mul_sum T (fun n => om n) (2 * Sp)]
    have h4 : ∑ n ∈ T, Sp^2 = (T.card : ℝ) * Sp^2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h1, h2, h3, h4]
  -- the count bound
  have hmain : ((T.filter (fun n => n.Coprime (∏ p ∈ S', p))).card : ℝ)
      ≤ ((Y₂:ℝ) + 4 * (S'.card : ℝ)) / Sp := by
    rw [hexp, hTcard] at hvar
    have hkey : ((T.filter (fun n => n.Coprime (∏ p ∈ S', p))).card : ℝ) * Sp^2
        ≤ ((Y₂:ℝ) + 4 * (S'.card : ℝ)) * Sp := by
      nlinarith [hvar, hsum2_ub, hsum1_lb, hY₂le, hSppos, hSp1, hπnn]
    rw [le_div_iff₀ hSppos]
    nlinarith [hkey, hSppos]
  -- final assembly
  have hπub : (S'.card : ℝ) ≤ X₁ := by
    have h1 : ((S'.card : ℕ) : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ) := by
      rw [hS'def]
      have hsub : Work.BMF.primesIn P Q ⊆ Finset.Ioc 0 ⌊Q⌋₊ := by
        intro p hp
        rw [Work.BMF.mr_direct.mem_primesIn_iff] at hp
        rw [Finset.mem_Ioc]
        exact ⟨by have := hp.1.two_le; omega, Nat.le_floor hp.2.2⟩
      have hc := Finset.card_le_card hsub
      rw [Nat.card_Ioc, tsub_zero] at hc
      exact_mod_cast hc
    have h2 : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le (le_of_lt hQpos)
    have h3 : Q ≤ X₁ := by nlinarith [hQ2, hQpos, hX1]
    linarith
  have hsubset : (Work.BMF.natIcc X₁ X₂).filter (fun n => n.Coprime (∏ p ∈ S', p))
      ⊆ T.filter (fun n => n.Coprime (∏ p ∈ S', p)) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨?_, hn.2⟩
    rw [Work.BMF.natIcc, Finset.mem_Icc] at hn
    rw [hTdef, Finset.mem_Ioc]
    have h1 : (1:ℕ) ≤ ⌈X₁⌉₊ := Nat.one_le_ceil_iff.mpr hX1pos
    exact ⟨by omega, hn.1.2⟩
  have hcard_le : ((Work.BMF.natIcc X₁ X₂).filter
        (fun n => n.Coprime (∏ p ∈ S', p))).card
      ≤ (T.filter (fun n => n.Coprime (∏ p ∈ S', p))).card :=
    Finset.card_le_card hsubset
  have hsum_bound : (∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter
        (fun n => n.Coprime (∏ p ∈ S', p)), 1 / (n : ℝ))
      ≤ ((T.filter (fun n => n.Coprime (∏ p ∈ S', p))).card : ℝ) * (1 / X₁) := by
    calc (∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter
          (fun n => n.Coprime (∏ p ∈ S', p)), 1 / (n : ℝ))
        ≤ ∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter (fun n => n.Coprime (∏ p ∈ S', p)),
            1 / X₁ := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          rw [Finset.mem_filter] at hn
          rw [Work.BMF.natIcc, Finset.mem_Icc] at hn
          exact one_div_le_one_div_of_le hX1pos (le_trans (Nat.le_ceil X₁) (by exact_mod_cast hn.1.1))
      _ = ((Work.BMF.natIcc X₁ X₂).filter
            (fun n => n.Coprime (∏ p ∈ S', p))).card * (1 / X₁) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((T.filter (fun n => n.Coprime (∏ p ∈ S', p))).card : ℝ) * (1 / X₁) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) (by positivity)
  refine le_trans hsum_bound ?_
  have hY4 : (Y₂:ℝ) + 4 * (S'.card : ℝ) ≤ 8 * X₁ := by nlinarith [hY₂le, hX24, hπub]
  have h1 : ((Y₂:ℝ) + 4 * (S'.card : ℝ))/Sp * (1/X₁)
      = ((Y₂:ℝ) + 4 * (S'.card : ℝ))/(Sp * X₁) := by
    field_simp
  have h2 : ((Y₂:ℝ) + 4 * (S'.card : ℝ))/(Sp * X₁) ≤ 8/Sp := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < Sp * X₁) hSppos]
    nlinarith [hY4]
  have h3 : (8:ℝ)/Sp ≤ 100/Sp := by
    rw [div_le_div_iff₀ hSppos hSppos]; linarith
  calc ((T.filter (fun n => n.Coprime (∏ p ∈ S', p))).card : ℝ) * (1 / X₁)
      ≤ ((Y₂:ℝ) + 4 * (S'.card : ℝ))/Sp * (1/X₁) :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = ((Y₂:ℝ) + 4 * (S'.card : ℝ))/(Sp * X₁) := h1
    _ ≤ 8/Sp := h2
    _ ≤ 100/Sp := h3


end Work.BMF.mr_core
