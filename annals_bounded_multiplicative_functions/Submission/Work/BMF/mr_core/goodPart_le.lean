import Mathlib
import Submission.Work.BMF.mr_core_defs
import Submission.Work.BMF.mr_direct.buchstab_set
import Submission.Work.BMF.mr_direct.goodSet_bound_range
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
import Submission.Work.BMF.mr_core.coprimeRecipSum_tk
import Submission.Work.BMF.mr_core.tendsto_loglog_exp_neg_mul
import Submission.Work.BMF.mr_core.tendsto_polylog_exp_decay_div
import Submission.Work.BMF.mr_core.fineParams_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.mr_core.goodPart_le`

The *good-set* half of the critical regime of `Work.BMF.CoreInput`: for all sufficiently large
`Y`, every `1`-bounded multiplicative `g` and all `H, T` in the critical range
`Y^θ ≤ H ≤ Y`, `3 ≤ T`, `Y/H ≤ T ≤ 2C₀/ε · (Y/H)`, the squared `L²` mass of the Dirichlet
polynomial `dirPolyD g Y` restricted to the *fine* good set `mrCore.goodSet ε g Y (2T)`
satisfies

  `(Y/H)/T · ∫_{goodSet} ‖dirPolyD g Y t‖² ≤ ε/8`.

The proof is the one-scale Buchstab/Ramaré decomposition `mr_direct.buchstab_set` on the good
set, followed by

* the good-set mean-value bound `mr_direct.goodSet_bound_range` for the main term, and
* the Turán–Kubilius density bound `coprimeRecipSum_tk` for the coprime part (which replaces the
  fundamental lemma of the sieve; it is exactly what makes the argument independent of the
  Selberg-sieve subtree),

and then pure asymptotic bookkeeping with the *fine* parameters
`K_f = (log Y)^{1/4}/ε`, `P_f = exp(384 log log Y)`, `Q_f = exp(384 (log Y)^{1/8} log log Y/ε)`
of `mr_core_defs`: every term of the bound is a fixed real times a `Y`-decaying function, so
each is `≤ ε/40` eventually.  The asymptotic inputs are
`tendsto_polylog_exp_decay_div`, `tendsto_loglog_exp_neg_mul` and the size conditions
`fineParams_le`; the reciprocal prime sum `Σ_{P_f<p≤Q_f} 1/p → ∞` needed for the coprime term
comes from Mertens' second theorem (`primesIn_fine_recip_ge` below).
-/

namespace Work.BMF.mr_core

open MeasureTheory intervalIntegral Filter
open scoped BigOperators
open Work.BMF.mrCore

set_option maxHeartbeats 8000000

/-- The reciprocal prime sum over the *fine* interval `[Pf Y, Qf ε Y]` is eventually at least any
prescribed constant; the proof is Mertens' second theorem applied at `Pf` and at `Qf`:

`Σ_{Pf<p≤Qf} 1/p ≥ log log Qf − log log Pf − 2Cm = (1/8) log log Y − log ε − 2Cm`. -/
lemma primesIn_fine_recip_ge (ε Cm C : ℝ) (hε : 0 < ε)
    (hM : ∀ x : ℝ, 11 ≤ x →
      |(∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log x)| ≤ Cm) :
    ∀ᶠ Y in Filter.atTop, C ≤ ∑ p ∈ Work.BMF.primesIn (Pf Y) (Qf ε Y), 1 / (p : ℝ) := by
  have hCmnn : 0 ≤ Cm := by
    have h := hM 11 (le_refl 11)
    have := abs_nonneg ((∑ p ∈ (⌊(11 : ℝ)⌋₊).primesLE, (1 : ℝ) / (p : ℝ))
      - Real.log (Real.log 11))
    linarith
  set Y₀ : ℝ := max (max (Real.exp (Real.exp 11))
      (Real.exp (Real.exp (Real.exp (8 * (C + 2 * Cm + |Real.log ε| + 11))))))
      (Real.exp (ε ^ 8)) with hY₀
  filter_upwards [Filter.eventually_ge_atTop Y₀] with Y hY
  have hY1 : Real.exp (Real.exp 11) ≤ Y :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hY2 : Real.exp (Real.exp (Real.exp (8 * (C + 2 * Cm + |Real.log ε| + 11)))) ≤ Y :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hY3 : Real.exp (ε ^ 8) ≤ Y := le_trans (le_max_right _ _) hY
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos (Real.exp 11)) hY1
  -- `log Y ≥ exp 11` and `log log Y ≥ 11`
  have hL1 : Real.exp 11 ≤ Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 11)) hY1
    rwa [Real.log_exp] at h
  have hLL1 : 11 ≤ Real.log (Real.log Y) := by
    have hexp11 : (0 : ℝ) < Real.exp 11 := Real.exp_pos _
    have h := Real.log_le_log hexp11 hL1
    rwa [Real.log_exp] at h
  have hLL2 : 8 * (C + 2 * Cm + |Real.log ε| + 11) ≤ Real.log (Real.log Y) := by
    have hL2 : Real.exp (Real.exp (8 * (C + 2 * Cm + |Real.log ε| + 11))) ≤ Real.log Y := by
      have h := Real.log_le_log
        (Real.exp_pos (Real.exp (Real.exp (8 * (C + 2 * Cm + |Real.log ε| + 11))))) hY2
      rwa [Real.log_exp] at h
    have h := Real.log_le_log (Real.exp_pos (Real.exp (8 * (C + 2 * Cm + |Real.log ε| + 11)))) hL2
    rw [Real.log_exp] at h
    linarith [h, Real.add_one_le_exp (8 * (C + 2 * Cm + |Real.log ε| + 11))]
  have hLpos : 0 < Real.log Y := lt_of_lt_of_le (Real.exp_pos 11) hL1
  have hLLpos : 0 < Real.log (Real.log Y) := by linarith
  -- the fine parameters
  have hPf_eq : Pf Y = Real.exp (384 * Real.log (Real.log Y)) := by rw [Pf, logPf]
  have hLε : ε ≤ (Real.log Y) ^ ((1 : ℝ) / 8) := by
    have hlogε : ε ^ (8 : ℕ) ≤ Real.log Y := by
      have h := Real.log_le_log (Real.exp_pos (ε ^ 8)) hY3
      rwa [Real.log_exp] at h
    have h1 : (ε ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) ≤ ((Real.log Y)) ^ ((1 : ℝ) / 8) :=
      Real.rpow_le_rpow (by positivity) hlogε (by norm_num)
    have h2 : (ε ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) = ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hε)]
      rw [show ((8 : ℕ) : ℝ) * ((1 : ℝ) / 8) = 1 by norm_num, Real.rpow_one]
    linarith [h1, h2.symm.le, h2.le]
  have hAf1 : 1 ≤ (Real.log Y) ^ ((1 : ℝ) / 8) / ε := (one_le_div hε).mpr hLε
  have hPf11 : 11 ≤ Pf Y := by
    rw [hPf_eq]
    have h1 : (11 : ℝ) ≤ Real.exp 11 := by
      have := Real.add_one_le_exp (11 : ℝ); linarith
    have h2 : Real.exp 11 ≤ Real.exp (384 * Real.log (Real.log Y)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hQf_eq : Qf ε Y = Real.exp ((Real.log Y) ^ ((1 : ℝ) / 8) / ε * (384 * Real.log (Real.log Y))) := by
    rw [Qf, logQf, Af, logPf]
  have hQf11 : 11 ≤ Qf ε Y := by
    rw [hQf_eq]
    have h384 : 0 ≤ 384 * Real.log (Real.log Y) := by linarith
    have h1 : 384 * Real.log (Real.log Y) ≤
        (Real.log Y) ^ ((1 : ℝ) / 8) / ε * (384 * Real.log (Real.log Y)) :=
      le_mul_of_one_le_left h384 hAf1
    calc (11 : ℝ) ≤ Pf Y := hPf11
      _ = Real.exp (384 * Real.log (Real.log Y)) := hPf_eq
      _ ≤ Real.exp ((Real.log Y) ^ ((1 : ℝ) / 8) / ε * (384 * Real.log (Real.log Y))) :=
          Real.exp_le_exp.mpr h1
  -- Mertens at `Qf` and at `Pf`
  have hMQ := hM (Qf ε Y) hQf11
  have hMP := hM (Pf Y) hPf11
  have hQsum : (∑ p ∈ (⌊Pf Y⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log (Pf Y)) + Cm := by
    have h := abs_le.mp hMP
    linarith [h.2]
  have hQsum' : Real.log (Real.log (Qf ε Y)) - Cm ≤
      (∑ p ∈ (⌊Qf ε Y⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) := by
    have h := abs_le.mp hMQ
    linarith [h.1]
  -- the set containment
  set A : Finset ℕ := (⌊Qf ε Y⌋₊).primesLE with hA
  set B : Finset ℕ := (⌊Pf Y⌋₊).primesLE with hB
  set Cset : Finset ℕ := Work.BMF.primesIn (Pf Y) (Qf ε Y) with hC
  have hsub : A ⊆ B ∪ Cset := by
    intro p hp
    rw [hA, Nat.mem_primesLE] at hp
    rw [Finset.mem_union]
    by_cases hple : p ≤ ⌊Pf Y⌋₊
    · exact Or.inl (by rw [hB, Nat.mem_primesLE]; exact ⟨hple, hp.2⟩)
    · push_neg at hple
      have hceil : ⌈Pf Y⌉₊ ≤ p := by
        have hpfpos : (0 : ℝ) < Pf Y := Real.exp_pos _
        have hfloor : (⌊Pf Y⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by
          have : ⌊Pf Y⌋₊ < p := hple
          have := Nat.lt_iff_add_one_le.mp this
          exact_mod_cast this
        have hfl : Pf Y ≤ ((⌊Pf Y⌋₊ + 1 : ℕ) : ℝ) := by
          have := Nat.lt_floor_add_one (Pf Y)
          push_cast
          linarith
        have hc : ⌈Pf Y⌉₊ ≤ ⌊Pf Y⌋₊ + 1 := Nat.ceil_le.mpr hfl
        exact le_trans hc (Nat.lt_iff_add_one_le.mp hple)
      exact Or.inr (by
        rw [hC, Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hceil, hp.1⟩, hp.2⟩)
  have hle : (∑ p ∈ A, 1 / (p : ℝ)) ≤ (∑ p ∈ B, 1 / (p : ℝ)) + ∑ p ∈ Cset, 1 / (p : ℝ) := by
    have h1 : (∑ p ∈ A, 1 / (p : ℝ)) ≤ ∑ p ∈ B ∪ Cset, 1 / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    have h2 : (∑ p ∈ B ∪ Cset, 1 / (p : ℝ)) ≤
        (∑ p ∈ B, 1 / (p : ℝ)) + ∑ p ∈ Cset, 1 / (p : ℝ) := by
      have hdisj : Disjoint B (Cset \ B) := Finset.disjoint_sdiff
      have hunion : B ∪ Cset = B ∪ (Cset \ B) := by
        ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
      rw [hunion, Finset.sum_union hdisj]
      have h3 : (∑ x ∈ Cset \ B, 1 / (x : ℝ)) ≤ ∑ x ∈ Cset, 1 / (x : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i _ _ => by positivity)
      linarith
    linarith
  -- the analytic comparison
  have hQfpos : 0 < Qf ε Y := Real.exp_pos _
  have hlogPf : Real.log (Pf Y) = 384 * Real.log (Real.log Y) := by rw [hPf_eq, Real.log_exp]
  have hlogQf : Real.log (Qf ε Y) =
      (Real.log Y) ^ ((1 : ℝ) / 8) / ε * (384 * Real.log (Real.log Y)) := by
    rw [hQf_eq, Real.log_exp]
  have hlogPfpos : 0 < Real.log (Pf Y) := by rw [hlogPf]; linarith
  have hlogQfpos : 0 < Real.log (Qf ε Y) := by
    rw [hlogQf]
    exact mul_pos (div_pos (Real.rpow_pos_of_pos hLpos _) hε) (by linarith)
  have hratio : Real.log (Qf ε Y) / Real.log (Pf Y) = (Real.log Y) ^ ((1 : ℝ) / 8) / ε := by
    rw [hlogQf, hlogPf]
    field_simp
  have hlogs : Real.log (Real.log (Qf ε Y)) - Real.log (Real.log (Pf Y))
      = Real.log ((Real.log Y) ^ ((1 : ℝ) / 8) / ε) := by
    rw [← Real.log_div (ne_of_gt hlogQfpos) (ne_of_gt hlogPfpos), hratio]
  have hlogdiv : Real.log ((Real.log Y) ^ ((1 : ℝ) / 8) / ε)
      = Real.log (Real.log Y) / 8 - Real.log ε := by
    rw [Real.log_div (by positivity) (ne_of_gt hε), Real.log_rpow hLpos]
    ring
  have hLL2' : 8 * (C + 2 * Cm + Real.log ε + 11) ≤ Real.log (Real.log Y) := by
    have h2 : Real.log ε ≤ |Real.log ε| := le_abs_self _
    linarith
  have hkey2 : Real.log (Real.log Y) / 8 - Real.log ε - 2 * Cm ≥ C := by
    have h3 : (8 * (C + 2 * Cm + Real.log ε + 11)) / 8 ≤ Real.log (Real.log Y) / 8 :=
      div_le_div_of_nonneg_right hLL2' (by norm_num)
    rw [mul_div_cancel_left₀ _ (by norm_num : (8 : ℝ) ≠ 0)] at h3
    linarith
  have hfinal : C ≤ ∑ p ∈ Cset, 1 / (p : ℝ) := by
    have := hQsum
    have := hQsum'
    linarith [hlogs, hlogdiv, hkey2, hle, hQsum, hQsum']
  rw [hC] at hfinal
  exact hfinal


theorem goodPart_le (ε C₀ θ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC₀ : 0 < C₀)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∀ᶠ Y in Filter.atTop, ∀ (g : ℕ → ℂ) (H T : ℝ),
      g 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
      Y ^ θ ≤ H → H ≤ Y → 3 ≤ T → Y / H ≤ T → T ≤ 2 * C₀ / ε * (Y / H) →
      (Y / H) / T * (∫ t in Work.BMF.mrCore.goodSet ε g Y (2 * T),
          ‖Work.BMF.dirPolyD g Y t‖ ^ 2) ≤ ε / 8 := by
  obtain ⟨C₁, hC₁pos, hdec⟩ := Work.BMF.mr_direct.buchstab_set
  obtain ⟨C₂, hC₂pos, hg2⟩ := Work.BMF.mr_direct.goodSet_bound_range
  obtain ⟨Y₀, hY₀1, hY₀⟩ := fineParams_le ε hε hε1
  obtain ⟨Cm, hCmpos, hMert⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  have hSbig : ∀ᶠ Y in Filter.atTop,
      max 1 (1600 * C₁ / ε) ≤ ∑ p ∈ Work.BMF.primesIn (Pf Y) (Qf ε Y), 1 / (p : ℝ) :=
    primesIn_fine_recip_ge ε Cm (max 1 (1600 * C₁ / ε)) hε hMert
  -- the five eventual arithmetic estimates
  have hE1 : ∀ᶠ Y in Filter.atTop,
      (2 * (C₁ * C₂ * (1 + 1 / alphaF))) * (Real.log Y) ^ ((5 : ℝ) / 2) *
        (Real.log (Real.log Y)) ^ (2 : ℝ) *
        Real.exp (((1 - 2 * alphaF) * 384 / ε) * (Real.log Y) ^ ((1 : ℝ) / 8) *
          Real.log (Real.log Y)) / Y ^ θ ≤ ε / 40 := by
    have h := (tendsto_order.1 (tendsto_polylog_exp_decay_div (2 * (C₁ * C₂ * (1 + 1 / alphaF))) (5 / 2) 2
      ((1 - 2 * alphaF) * 384 / ε) θ hθ₀)).2 (ε / 40) (by linarith)
    filter_upwards [h] with Y hY
    exact le_of_lt hY
  have hE2 : ∀ᶠ Y in Filter.atTop,
      (3 * (C₁ * C₂ * (1 + 1 / alphaF))) * (Real.log Y) ^ ((5 : ℝ) / 2) *
        (Real.log (Real.log Y)) ^ (2 : ℝ) *
        Real.exp (-(768 * alphaF) * Real.log (Real.log Y)) ≤ ε / 40 := by
    have h := (tendsto_order.1 (tendsto_loglog_exp_neg_mul (3 * (C₁ * C₂ * (1 + 1 / alphaF))) (5 / 2) 2
      (768 * alphaF) (by norm_num [alphaF, etaF]) (by norm_num [alphaF, etaF]))).2
      (ε / 40) (by linarith)
    filter_upwards [h] with Y hY
    exact le_of_lt hY
  have hE3 : ∀ᶠ Y in Filter.atTop,
      5 * C₁ * ε * Real.exp (-(1 / 4) * Real.log (Real.log Y)) ≤ ε / 40 := by
    have h := (tendsto_order.1 (tendsto_loglog_exp_neg_mul (5 * C₁ * ε) 0 0 (1 / 4) (by norm_num) (by norm_num))).2
      (ε / 40) (by linarith)
    filter_upwards [h] with Y hY
    exact le_of_lt (by simpa using hY)
  have hE4 : ∀ᶠ Y in Filter.atTop,
      5 * C₁ * Real.exp (-(384) * Real.log (Real.log Y)) ≤ ε / 40 := by
    have h := (tendsto_order.1 (tendsto_loglog_exp_neg_mul (5 * C₁) 0 0 (384) (by norm_num) (by norm_num))).2
      (ε / 40) (by linarith)
    filter_upwards [h] with Y hY
    exact le_of_lt (by simpa using hY)
  filter_upwards [Filter.eventually_atTop.mpr ⟨Y₀, hY₀⟩, hE1, hE2, hE3, hE4, hSbig] with
    Y hYel hE1' hE2' hE3' hE4' hSlow'
  obtain ⟨hYexp, hlog1, hM1, hPf2, hKf3, hPfQf, hQf2, hAineq, hQineq, hPineq⟩ := hYel
  intro g H T hg1 hgmul hgb hHθ hHY hT3 hρT hTle
  have hY1 : 1 ≤ Y := le_trans (Real.one_le_exp (by norm_num)) hYexp
  have hYpos : 0 < Y := lt_of_lt_of_le one_pos hY1
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hYpos θ) hHθ
  have hTpos : 0 < T := by linarith
  -- measurability / subset of the good set
  have hu_meas : MeasurableSet (Work.BMF.mrCore.goodSet ε g Y (2 * T)) :=
    measurableSet_goodSet ε g Y (2 * T)
  have hu_sub : Work.BMF.mrCore.goodSet ε g Y (2 * T) ⊆ Set.Icc (-(2 * T)) (2 * T) :=
    fun t ht => ht.1
  have hgood : ∀ t ∈ Work.BMF.mrCore.goodSet ε g Y (2 * T),
      ∀ j ∈ Work.BMF.mrDirect.indexSet (Kf ε Y) (Pf Y) (Qf ε Y),
      ‖Work.BMF.mrDirect.primePoly g (Kf ε Y) j t‖ ≤
        Real.exp (-(alphaF * (j : ℝ) / (Kf ε Y))) := by
    intro t ht j hj
    exact ((mem_goodSet_iff ε g Y (2 * T) t).mp ht).2 j hj
  -- the multiplicativity hypothesis in the form used by the Buchstab decomposition
  have hmul : ∀ m p : ℕ, Nat.Prime p → Pf Y ≤ (p : ℝ) → (p : ℝ) ≤ Qf ε Y → ¬ p ∣ m →
      g (m * p) = g m * g p := by
    intro m p hp _ _ hnp
    exact hgmul m p (((Nat.Prime.coprime_iff_not_dvd hp).mpr hnp).symm)
  -- Buchstab decomposition
  have hdec' := hdec Y (3 * Y) (Kf ε Y) (Pf Y) (Qf ε Y) (2 * T) g g g
    (Work.BMF.mrCore.goodSet ε g Y (2 * T))
    hY1 (by linarith) (by linarith) (by linarith) hPf2 hPfQf (by linarith)
    hu_meas hu_sub hgb hgb hgb hmul
  -- good-set bound
  have hgb2 := hg2 Y (3 * Y) (Kf ε Y) (Pf Y) (Qf ε Y) (2 * T) alphaF g g
    (Work.BMF.mrCore.goodSet ε g Y (2 * T))
    hY1 (by linarith) (by linarith) (by linarith) hPf2 hPfQf (by linarith)
    (by norm_num [alphaF, etaF]) (by norm_num [alphaF, etaF]) hgb hgb hu_sub hgood
  -- ### abbreviations for the final arithmetic
  set K : ℝ := Kf ε Y with hKdef
  set P : ℝ := Pf Y with hPdef
  set Q : ℝ := Qf ε Y with hQdef
  set Sig : ℝ := ∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
      ∫ t in Work.BMF.mrCore.goodSet ε g Y (2 * T),
        ‖Work.BMF.mrDirect.primePoly g K j t *
          Work.BMF.mrDirect.remPolyR g P Q K Y (3 * Y) j t‖ ^ 2 with hSigdef
  set Ecop : ℝ := ∑ n ∈ (Work.BMF.natIcc Y (3 * Y)).filter
        (fun n => n.Coprime (∏ p ∈ Work.BMF.primesIn P Q, p)),
        ‖g n‖ ^ 2 / (n : ℝ) with hEcopdef
  set w : ℝ := (Y / H) / T with hwdef
  set A : ℝ := C₂ * (1 + 1 / alphaF) * (K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2 with hAdef
  set Ssum : ℝ := ∑ p ∈ Work.BMF.primesIn P Q, 1 / (p : ℝ) with hSsum

  have hterm : ∀ n ∈ (Work.BMF.natIcc Y (3 * Y)).filter
        (fun n => n.Coprime (∏ p ∈ Work.BMF.primesIn P Q, p)),
      ‖g n‖ ^ 2 / (n : ℝ) ≤ 1 / (n : ℝ) := by
    intro n hn
    have hnI : n ∈ Work.BMF.natIcc Y (3 * Y) := (Finset.mem_filter.mp hn).1
    rw [Work.BMF.natIcc, Finset.mem_Icc] at hnI
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have h : Y ≤ (n : ℝ) := le_trans (Nat.le_ceil Y) (by exact_mod_cast hnI.1)
      linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hgn : ‖g n‖ ^ 2 ≤ 1 := by
      have := hgb n
      nlinarith [norm_nonneg (g n)]
    exact div_le_div_of_nonneg_right hgn hnpos.le
  have hEcop : Ecop ≤ 8 / Ssum := by
    have hS1 : 1 ≤ Ssum := (max_le_iff.mp hSlow').1
    rw [hEcopdef]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    exact coprimeRecipSum_tk P Q Y (3 * Y) hPf2 hPfQf hY1 (by linarith) (by linarith) hQf2 hS1
  -- basic positivity
  have hαpos : 0 < alphaF := by norm_num [alphaF, etaF]
  have hKpos : 0 < K := by rw [hKdef]; exact lt_of_lt_of_le (by norm_num) hKf3
  have hPpos : 0 < P := by rw [hPdef]; exact Real.exp_pos _
  have hQpos : 0 < Q := by rw [hQdef]; exact Real.exp_pos _
  have hlogpos : 0 < Real.log Y := by linarith
  have hLnn : 0 ≤ Real.log (Q / P) := by
    apply Real.log_nonneg
    rw [one_le_div hPpos]
    exact hPfQf
  have hcoef : (0 : ℝ) ≤ C₂ * (1 + 1 / alphaF) := by
    have h : (0 : ℝ) < 1 + 1 / alphaF := by
      have := one_div_pos.mpr hαpos
      linarith
    exact mul_nonneg hC₂pos.le h.le
  have hwnn : 0 ≤ w := by rw [hwdef]; positivity
  have hwle1 : w ≤ 1 := by
    rw [hwdef, div_le_one hTpos]
    exact hρT
  have hwt : w * ((2 * T) / Y) = 2 / H := by
    rw [hwdef]; field_simp
  have h3YY : (3 * Y) / Y = 3 := by field_simp
  have hH1 : 1 ≤ H := le_trans (Real.one_le_rpow hY1 hθ₀.le) hHθ
  have hwsec : w * ((2 * T + 3 * Y) / Y) ≤ 5 := by
    have h2 : (2 * T + 3 * Y) / Y = (2 * T) / Y + 3 := by field_simp
    have h3 : 2 / H ≤ 2 := by
      rw [div_le_iff₀ hHpos]; linarith
    have h4 : 3 * w ≤ 3 := by linarith
    calc w * ((2 * T + 3 * Y) / Y) = w * ((2 * T) / Y + 3) := by rw [h2]
      _ = w * ((2 * T) / Y) + w * 3 := by ring
      _ = 2 / H + 3 * w := by rw [hwt]; ring
      _ ≤ 5 := by linarith
  have hAnn : 0 ≤ 1 / K + 1 / P + Ecop := by
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact div_nonneg zero_le_one hKpos.le
    · exact div_nonneg zero_le_one hPpos.le
    · rw [hEcopdef]
      exact Finset.sum_nonneg (fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n))
  have hAnnA : 0 ≤ A := by
    rw [hAdef]
    have h1 : (0 : ℝ) ≤ (K + 1) ^ 4 := by positivity
    have h2 : (0 : ℝ) ≤ (Real.log (Q / P) + 1) ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg hcoef h1) h2
  -- ### step 1: the decomposition on the good set
  have hRbound : (∫ t in Work.BMF.mrCore.goodSet ε g Y (2 * T), ‖Work.BMF.dirPolyD g Y t‖ ^ 2)
      ≤ C₁ * (K * Real.log (Q / P) * Sig + (2 * T + 3 * Y) / Y * (1 / K + 1 / P + Ecop)) := by
    rw [show (∫ t in Work.BMF.mrCore.goodSet ε g Y (2 * T), ‖Work.BMF.dirPolyD g Y t‖ ^ 2)
        = ∫ t in Work.BMF.mrCore.goodSet ε g Y (2 * T),
            ‖Work.BMF.mrDirect.dirPolyR g Y (3 * Y) t‖ ^ 2 from rfl]
    exact hdec'
  -- ### step 2: multiply by w
  have hab : w * (∫ t in Work.BMF.mrCore.goodSet ε g Y (2 * T), ‖Work.BMF.dirPolyD g Y t‖ ^ 2)
      ≤ C₁ * (w * (K * Real.log (Q / P) * Sig)
          + w * ((2 * T + 3 * Y) / Y * (1 / K + 1 / P + Ecop))) := by
    calc w * (∫ t in Work.BMF.mrCore.goodSet ε g Y (2 * T), ‖Work.BMF.dirPolyD g Y t‖ ^ 2)
        ≤ w * (C₁ * (K * Real.log (Q / P) * Sig + (2 * T + 3 * Y) / Y * (1 / K + 1 / P + Ecop))) :=
          mul_le_mul_of_nonneg_left hRbound hwnn
      _ = C₁ * (w * (K * Real.log (Q / P) * Sig)
            + w * ((2 * T + 3 * Y) / Y * (1 / K + 1 / P + Ecop))) := by ring
  -- ### step 3: the main term
  have h1 : w * (K * Real.log (Q / P) * Sig)
      ≤ A * (2 / H * Q ^ (1 - 2 * alphaF) + 3 * P ^ (-(2 * alphaF))) := by
    have hPt : 0 ≤ P ^ (-(2 * alphaF)) := Real.rpow_nonneg hPpos.le _
    have h3w : 3 * w ≤ 3 := by linarith
    calc w * (K * Real.log (Q / P) * Sig)
        ≤ w * (A * ((2 * T) / Y * Q ^ (1 - 2 * alphaF) + (3 * Y) / Y * P ^ (-(2 * alphaF)))) :=
          mul_le_mul_of_nonneg_left hgb2 hwnn
      _ = A * (w * ((2 * T) / Y) * Q ^ (1 - 2 * alphaF)
            + w * ((3 * Y) / Y) * P ^ (-(2 * alphaF))) := by ring
      _ = A * (2 / H * Q ^ (1 - 2 * alphaF) + 3 * w * P ^ (-(2 * alphaF))) := by
          rw [hwt, h3YY]; ring
      _ ≤ A * (2 / H * Q ^ (1 - 2 * alphaF) + 3 * P ^ (-(2 * alphaF))) := by
          apply mul_le_mul_of_nonneg_left _ hAnnA
          have := mul_le_mul_of_nonneg_right h3w hPt
          linarith
  -- ### step 4: the coprime part
  have h2 : w * ((2 * T + 3 * Y) / Y * (1 / K + 1 / P + Ecop))
      ≤ 5 * (1 / K + 1 / P + Ecop) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hwsec hAnn
  -- ### step 5: combine
  have h5 : w * (∫ t in Work.BMF.mrCore.goodSet ε g Y (2 * T), ‖Work.BMF.dirPolyD g Y t‖ ^ 2)
      ≤ C₁ * A * (2 / H * Q ^ (1 - 2 * alphaF) + 3 * P ^ (-(2 * alphaF)))
        + 5 * C₁ * (1 / K + 1 / P + Ecop) := by
    calc w * (∫ t in Work.BMF.mrCore.goodSet ε g Y (2 * T), ‖Work.BMF.dirPolyD g Y t‖ ^ 2)
        ≤ C₁ * (w * (K * Real.log (Q / P) * Sig)
            + w * ((2 * T + 3 * Y) / Y * (1 / K + 1 / P + Ecop))) := hab
      _ ≤ C₁ * (A * (2 / H * Q ^ (1 - 2 * alphaF) + 3 * P ^ (-(2 * alphaF)))
            + 5 * (1 / K + 1 / P + Ecop)) := by
          apply mul_le_mul_of_nonneg_left _ hC₁pos.le
          linarith [h1, h2]
      _ = C₁ * A * (2 / H * Q ^ (1 - 2 * alphaF) + 3 * P ^ (-(2 * alphaF)))
            + 5 * C₁ * (1 / K + 1 / P + Ecop) := by ring
  -- ### step 6: the five pieces
  have hAh : C₂ * (1 + 1 / alphaF) * (K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2
      ≤ C₂ * (1 + 1 / alphaF) *
          ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ)) := by
    have hin : (K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2
        ≤ (Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ) := by
      have heq : (Real.log (Real.log Y)) ^ (2 : ℝ) = (Real.log (Real.log Y)) ^ 2 :=
        Real.rpow_natCast _ 2
      rw [heq]
      exact hAineq
    calc C₂ * (1 + 1 / alphaF) * (K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2
        = C₂ * (1 + 1 / alphaF) * ((K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2) := by ring
      _ ≤ C₂ * (1 + 1 / alphaF) *
            ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hin hcoef
  have hP1 : 2 * (C₁ * A) * Q ^ (1 - 2 * alphaF) / H ≤ ε / 40 := by
    rw [hAdef]
    have hA2 : 2 * (C₁ * (C₂ * (1 + 1 / alphaF) * (K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2))
        ≤ 2 * (C₁ * (C₂ * (1 + 1 / alphaF) *
            ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ)))) := by
      have hC1A : C₁ * (C₂ * (1 + 1 / alphaF) * (K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2)
          ≤ C₁ * (C₂ * (1 + 1 / alphaF) *
              ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hAh hC₁pos.le
      exact mul_le_mul_of_nonneg_left hC1A (by norm_num)
    have hQ2 : (0 : ℝ) ≤ Q ^ (1 - 2 * alphaF) := Real.rpow_nonneg hQpos.le _
    have h1r : (0 : ℝ) ≤ (Real.log Y) ^ ((5 : ℝ) / 2) := Real.rpow_nonneg hlogpos.le _
    have h2r : (0 : ℝ) ≤ (Real.log (Real.log Y)) ^ (2 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hX : (0 : ℝ) ≤ C₁ * (C₂ * (1 + 1 / alphaF) *
        ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ))) :=
      mul_nonneg hC₁pos.le (mul_nonneg hcoef (mul_nonneg h1r h2r))
    have hbb : (0 : ℝ) ≤ 2 * (C₁ * (C₂ * (1 + 1 / alphaF) *
        ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ)))) := by
      linarith [hX]
    have hbb' : (0 : ℝ) ≤ 2 * (C₁ * (C₂ * (1 + 1 / alphaF) *
        ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ)))) *
        Real.exp (((1 - 2 * alphaF) * 384 / ε) * (Real.log Y) ^ ((1 : ℝ) / 8) *
          Real.log (Real.log Y)) := mul_nonneg hbb (Real.exp_pos _).le
    have hstep : 2 * (C₁ * (C₂ * (1 + 1 / alphaF) * (K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2)) *
          Q ^ (1 - 2 * alphaF)
        ≤ 2 * (C₁ * (C₂ * (1 + 1 / alphaF) *
            ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ)))) *
          Real.exp (((1 - 2 * alphaF) * 384 / ε) * (Real.log Y) ^ ((1 : ℝ) / 8) *
            Real.log (Real.log Y)) :=
      mul_le_mul hA2 hQineq hQ2 hbb
    calc 2 * (C₁ * (C₂ * (1 + 1 / alphaF) * (K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2)) *
          Q ^ (1 - 2 * alphaF) / H
        ≤ 2 * (C₁ * (C₂ * (1 + 1 / alphaF) *
              ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ)))) *
            Real.exp (((1 - 2 * alphaF) * 384 / ε) * (Real.log Y) ^ ((1 : ℝ) / 8) *
              Real.log (Real.log Y)) / H :=
          div_le_div_of_nonneg_right hstep hHpos.le
      _ ≤ 2 * (C₁ * (C₂ * (1 + 1 / alphaF) *
              ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ)))) *
            Real.exp (((1 - 2 * alphaF) * 384 / ε) * (Real.log Y) ^ ((1 : ℝ) / 8) *
              Real.log (Real.log Y)) / Y ^ θ :=
          div_le_div_of_nonneg_left hbb' (Real.rpow_pos_of_pos hYpos θ) hHθ
      _ = (2 * (C₁ * C₂ * (1 + 1 / alphaF))) * (Real.log Y) ^ ((5 : ℝ) / 2) *
            (Real.log (Real.log Y)) ^ (2 : ℝ) *
            Real.exp (((1 - 2 * alphaF) * 384 / ε) * (Real.log Y) ^ ((1 : ℝ) / 8) *
              Real.log (Real.log Y)) / Y ^ θ := by ring
      _ ≤ ε / 40 := hE1'
  have hP2 : 3 * (C₁ * A) * P ^ (-(2 * alphaF)) ≤ ε / 40 := by
    rw [hAdef]
    have hA3 : 3 * (C₁ * (C₂ * (1 + 1 / alphaF) * (K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2))
        ≤ 3 * (C₁ * (C₂ * (1 + 1 / alphaF) *
            ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ)))) := by
      have hC1A : C₁ * (C₂ * (1 + 1 / alphaF) * (K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2)
          ≤ C₁ * (C₂ * (1 + 1 / alphaF) *
              ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hAh hC₁pos.le
      exact mul_le_mul_of_nonneg_left hC1A (by norm_num)
    have hPt2 : (0 : ℝ) ≤ P ^ (-(2 * alphaF)) := Real.rpow_nonneg hPpos.le _
    have h1r : (0 : ℝ) ≤ (Real.log Y) ^ ((5 : ℝ) / 2) := Real.rpow_nonneg hlogpos.le _
    have h2r : (0 : ℝ) ≤ (Real.log (Real.log Y)) ^ (2 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hX : (0 : ℝ) ≤ C₁ * (C₂ * (1 + 1 / alphaF) *
        ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ))) :=
      mul_nonneg hC₁pos.le (mul_nonneg hcoef (mul_nonneg h1r h2r))
    have hbb : (0 : ℝ) ≤ 3 * (C₁ * (C₂ * (1 + 1 / alphaF) *
        ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ)))) := by
      linarith [hX]
    have hstep : 3 * (C₁ * (C₂ * (1 + 1 / alphaF) * (K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2)) *
          P ^ (-(2 * alphaF))
        ≤ 3 * (C₁ * (C₂ * (1 + 1 / alphaF) *
            ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ)))) *
          Real.exp (-(768 * alphaF) * Real.log (Real.log Y)) :=
      mul_le_mul hA3 hPineq hPt2 hbb
    calc 3 * (C₁ * (C₂ * (1 + 1 / alphaF) * (K + 1) ^ 4 * (Real.log (Q / P) + 1) ^ 2)) *
          P ^ (-(2 * alphaF))
        ≤ 3 * (C₁ * (C₂ * (1 + 1 / alphaF) *
              ((Real.log Y) ^ ((5 : ℝ) / 2) * (Real.log (Real.log Y)) ^ (2 : ℝ)))) *
            Real.exp (-(768 * alphaF) * Real.log (Real.log Y)) := hstep
      _ = (3 * (C₁ * C₂ * (1 + 1 / alphaF))) * (Real.log Y) ^ ((5 : ℝ) / 2) *
            (Real.log (Real.log Y)) ^ (2 : ℝ) *
            Real.exp (-(768 * alphaF) * Real.log (Real.log Y)) := by ring
      _ ≤ ε / 40 := hE2'
  have hP3 : 5 * (C₁ / K) ≤ ε / 40 := by
    have h3 : 5 * (C₁ / K) = 5 * C₁ * ε * Real.exp (-(1 / 4) * Real.log (Real.log Y)) := by
      rw [hKdef, Work.BMF.mrCore.Kf, Real.rpow_def_of_pos hlogpos]
      have hexpn : (Real.exp (Real.log (Real.log Y) * (1 / 4)))⁻¹
          = Real.exp (-(1 / 4) * Real.log (Real.log Y)) := by
        rw [show -(1 / 4 : ℝ) * Real.log (Real.log Y)
            = -(Real.log (Real.log Y) * (1 / 4)) by ring]
        rw [Real.exp_neg]
      rw [div_div_eq_mul_div, div_eq_mul_inv, hexpn]
      ring
    rw [h3]
    exact hE3'
  have hP4 : 5 * (C₁ / P) ≤ ε / 40 := by
    have h4 : 5 * (C₁ / P) = 5 * C₁ * Real.exp (-(384) * Real.log (Real.log Y)) := by
      rw [hPdef, Work.BMF.mrCore.Pf, Work.BMF.mrCore.logPf]
      have hexpn : (Real.exp (384 * Real.log (Real.log Y)))⁻¹
          = Real.exp (-(384) * Real.log (Real.log Y)) := by
        rw [show -(384 : ℝ) * Real.log (Real.log Y)
            = -(384 * Real.log (Real.log Y)) by ring]
        rw [Real.exp_neg]
      rw [div_eq_mul_inv, hexpn]
      ring
    rw [h4]
    exact hE4'
  have hP5 : 5 * (C₁ * Ecop) ≤ ε / 40 := by
    have hSpos : 0 < Ssum := by
      have := (max_le_iff.mp hSlow').1
      linarith
    calc 5 * (C₁ * Ecop) ≤ 5 * (C₁ * (8 / Ssum)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEcop hC₁pos.le) (by norm_num)
      _ = 40 * C₁ / Ssum := by ring
      _ ≤ ε / 40 := by
          rw [div_le_iff₀ hSpos]
          have h1 : 1600 * C₁ ≤ Ssum * ε := by
            have hs := (max_le_iff.mp hSlow').2
            rw [div_le_iff₀ hε] at hs
            linarith
          nlinarith [h1]
  -- ### step 7: finish
  have h5' : w * (∫ t in Work.BMF.mrCore.goodSet ε g Y (2 * T), ‖Work.BMF.dirPolyD g Y t‖ ^ 2)
      ≤ 2 * (C₁ * A) * Q ^ (1 - 2 * alphaF) / H + 3 * (C₁ * A) * P ^ (-(2 * alphaF))
        + (5 * (C₁ / K) + 5 * (C₁ / P) + 5 * (C₁ * Ecop)) := by
    calc w * (∫ t in Work.BMF.mrCore.goodSet ε g Y (2 * T), ‖Work.BMF.dirPolyD g Y t‖ ^ 2)
        ≤ C₁ * A * (2 / H * Q ^ (1 - 2 * alphaF) + 3 * P ^ (-(2 * alphaF)))
            + 5 * C₁ * (1 / K + 1 / P + Ecop) := h5
      _ = 2 * (C₁ * A) * Q ^ (1 - 2 * alphaF) / H + 3 * (C₁ * A) * P ^ (-(2 * alphaF))
            + (5 * (C₁ / K) + 5 * (C₁ / P) + 5 * (C₁ * Ecop)) := by ring
  have hb5 : 2 * (C₁ * A) * Q ^ (1 - 2 * alphaF) / H + 3 * (C₁ * A) * P ^ (-(2 * alphaF))
      + (5 * (C₁ / K) + 5 * (C₁ / P) + 5 * (C₁ * Ecop)) ≤ 5 * (ε / 40) := by
    have hsum : 5 * (C₁ / K) + 5 * (C₁ / P) + 5 * (C₁ * Ecop) ≤ 3 * (ε / 40) := by
      linarith [hP3, hP4, hP5]
    have h123 := add_le_add (add_le_add hP1 hP2) hsum
    calc 2 * (C₁ * A) * Q ^ (1 - 2 * alphaF) / H + 3 * (C₁ * A) * P ^ (-(2 * alphaF))
          + (5 * (C₁ / K) + 5 * (C₁ / P) + 5 * (C₁ * Ecop))
        = (2 * (C₁ * A) * Q ^ (1 - 2 * alphaF) / H + 3 * (C₁ * A) * P ^ (-(2 * alphaF)))
          + (5 * (C₁ / K) + 5 * (C₁ / P) + 5 * (C₁ * Ecop)) := by ring
      _ ≤ (ε / 40 + ε / 40) + 3 * (ε / 40) := h123
      _ = 5 * (ε / 40) := by ring
  have hfin : 5 * (ε / 40) ≤ ε / 8 := by linarith
  exact le_trans h5' (le_trans hb5 hfin)


end Work.BMF.mr_core
