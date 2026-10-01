/-
# ZeroFreeTables — `OtherLamCountLeK_all`

**The parametric family zero count `OtherLamCountLeK K` for every `K > 0`** — Heath-Brown's
Lemma 6.1 with the level restricted *below an arbitrary fixed constant* `K` rather than below `3`.

```
OtherLamCountLeK K  :=  ∃ C > 0, ∃ Q, ∀ q ≥ Q, ∀ [NeZero q] (χ₁) (Λ H),
                          Λ ≤ K → H ≤ 10 log q → otherLamCount χ₁ Λ H ≤ C
```

## Why this is the right statement

`Work.ZeroFreeTables.OtherLamCountBounded` is the special case `K = 3`: the multiplicity-weighted
number of zeros `ρ` of the characters `χ ∉ {1, χ₁, χ₁⁻¹}` with `λ(ρ) ≤ Λ ≤ 3` and
`|Im ρ| ≤ H ≤ 10 log q` is bounded by an absolute constant, uniformly in `q` and in the excluded
character `χ₁`.  The §6 pigeonhole (`Work.ZeroFreeTables.PairParam`) needs the same statement with
`λ(ρ) < K` for an arbitrary prescribed height `K` (the "second number" of Table 7 is consumed at
level `K`), so the bound must be available for every `K > 0` — at the cost of a constant that may
depend on `K` (as it must: the count grows with `K`).

## The reduction (this file)

The proof is the parametric version of the reduction in
`Submission/Work/ZeroFreeTables/OtherLamCountBounded_of_logFreeNP.lean`.  Let

* `σ := 1 - max Λ 0 / log q`,  `T := max H 1`.

Then `λ(ρ) ≤ Λ` implies `Re ρ ≥ σ` (`one_sub_max_div_log_le_re_np`), every `zeroMult`-zero has
`Re ρ < 1`, and `H ≤ 10 log q` gives `T ≤ 10 log q`, so the counting lemma
`otherLamCount_le_zeroCountSumNP` bounds the `λ`-count by the non-principal family count

`otherLamCount χ₁ Λ H ≤ Σ_{χ ≠ 1} N(σ, T, χ)`.

A log-free non-principal family zero-density estimate with exponent coefficient `c` and range
parameter `σ₀` (the hypothesis `h` below, of which `Work.LinnikAreas.FamilyZeroDensityJutilaNP`
is the instance `σ₀ = 4/5`, `c = 2`) then gives, at `ε = 1`,

`Σ_{χ ≠ 1} N(σ,T,χ) ≤ C₁ (qT)^{(c+1)(1-σ)} = C₁ exp((c+1)·(1-σ)·log(qT))`,

and for `log q ≥ max 15 (K/(1-σ₀))` (i.e. `q ≥ Q`) both the range condition `σ ≥ σ₀` and the
exponent bound are uniform in `q`:

`(1-σ)·log(qT) ≤ (K/log q)·log(q·10 log q) ≤ (K/log q)·(2 log q) = 2K`,

hence `otherLamCount χ₁ Λ H ≤ C₁ · exp(2K(c+1))` for **all** `Λ ≤ K`, `H ≤ 10 log q`.

The two elementary inputs are:

* the threshold `Q` (`exists_Q_log_ge_exp`, private): `log q ≥ max 15 (K/(1-σ₀))` for `q ≥ Q`,
  via `Real.log_exp` and `Real.log_le_log`;
* the exponent bound `log(q · 10 log q) ≤ 2 log q` for `log q ≥ 8` (`log_mul_ten_log_le`, private),
  from `log 10 ≤ log q/2` and `log log q ≤ log q/2`.

Instantiating `h` with the workspace's **unconditional** instance
`Work.ZeroDensity.LogFree.logFreeNP_3979_5000_four` — turned into the `(4+ε)`-form by
`Work.ZeroFreeTables.logFreeNP4_countHyp` (`0 < ε`, `1 ≤ qT`) — yields `OtherLamCountLeK K` for
every `K > 0`, and in particular the `Λ ≤ 3` statement `OtherLamCountBounded`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HB88Defs
import Submission.Work.ZeroDensity.LogFree.logFreeNPInstances
import Submission.Work.ZeroFreeTables.OtherLamCountBounded_of_logFreeNP
import Submission.Work.ZeroFreeTables.logFreeNP4_countHyp

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-! ## 1. Elementary real analysis of the exponent -/

private lemma log_ten_le_half {L : ℝ} (hL : 8 ≤ L) : Real.log 10 ≤ L / 2 := by
  have h1 : Real.log 10 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have h3 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  linarith

private lemma log_self_le_half {L : ℝ} (hL : 2 ≤ L) : Real.log L ≤ L / 2 := by
  have h2 : (0 : ℝ) < L / 2 := by linarith
  have hsplit : Real.log L = Real.log 2 + Real.log (L / 2) := by
    calc Real.log L = Real.log (2 * (L / 2)) := by rw [show 2 * (L / 2) = L by ring]
      _ = Real.log 2 + Real.log (L / 2) := Real.log_mul (by norm_num) (ne_of_gt h2)
  have h3 : Real.log (L / 2) ≤ L / 2 - 1 := Real.log_le_sub_one_of_pos h2
  have h4 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  linarith

/-- `log (q · 10 log q) ≤ 2 log q` for `q > 0` with `log q ≥ 8`. -/
private lemma log_mul_ten_log_le {q : ℝ} (hqpos : 0 < q) (hq : 8 ≤ Real.log q) :
    Real.log (q * (10 * Real.log q)) ≤ 2 * Real.log q := by
  set L := Real.log q with hL
  have hLpos : 0 < L := by linarith
  have h1 : Real.log (q * (10 * L)) = Real.log q + Real.log (10 * L) :=
    Real.log_mul (ne_of_gt hqpos) (by positivity)
  have h2 : Real.log (10 * L) = Real.log 10 + Real.log L :=
    Real.log_mul (by norm_num) (ne_of_gt hLpos)
  have h3 : Real.log 10 ≤ L / 2 := log_ten_le_half (by linarith)
  have h4 : Real.log L ≤ L / 2 := log_self_le_half (by linarith)
  rw [h1, h2, ← hL]
  linarith

/-- **The threshold for the parametric reduction.**  For `σ₀ < 1` and `K > 0` there is `Q ≥ 2`
with `max 15 (K/(1-σ₀)) ≤ log q` for all `q ≥ Q`.  (Take `Q ≥ exp (max 15 (K/(1-σ₀)))`.)

This is `private` and named so as not to collide with the existing
`Work.ZeroFreeTables.exists_Q_log_ge` of `second_pair_wide.lean`, which has a different
statement (and whose name is already in this file's import closure). -/
private theorem exists_Q_log_ge_exp (σ₀ K : ℝ) (hσ₀ : σ₀ < 1) (hK : 0 < K) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ q : ℕ, Q ≤ q → max 15 (K / (1 - σ₀)) ≤ Real.log (q : ℝ) := by
  obtain ⟨Q, hQ⟩ := exists_nat_ge (Real.exp (max 15 (K / (1 - σ₀))))
  have hQ2 : 2 ≤ Q := by
    have hexp2 : (2 : ℝ) < Real.exp (max 15 (K / (1 - σ₀))) := by
      have h : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
      have h2 : Real.exp 1 ≤ Real.exp (max 15 (K / (1 - σ₀))) :=
        Real.exp_le_exp.mpr (le_trans (by norm_num) (le_max_left _ _))
      linarith
    have h2le : (2 : ℝ) ≤ (Q : ℝ) := le_of_lt (lt_of_lt_of_le hexp2 hQ)
    exact_mod_cast h2le
  refine ⟨Q, hQ2, ?_⟩
  intro q hq
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    have h2le : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2
    linarith
  have hqQ : (Q : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  calc max 15 (K / (1 - σ₀))
      = Real.log (Real.exp (max 15 (K / (1 - σ₀)))) := (Real.log_exp _).symm
    _ ≤ Real.log (Q : ℝ) := Real.log_le_log (Real.exp_pos _) hQ
    _ ≤ Real.log (q : ℝ) := Real.log_le_log hQpos hqQ

/-! ## 2. The parametric reduction from a log-free non-principal family estimate -/

/-- **The parametric family zero count from a log-free non-principal family estimate.**

Given a non-principal family zero-density estimate with exponent coefficient `c > 0` on the range
`σ ≥ σ₀` (`σ₀ < 1`) — the hypothesis `h`, whose canonical instance is
`Work.LinnikAreas.FamilyZeroDensityJutilaNP` (`σ₀ = 4/5`, `c = 2`) — the multiplicity-weighted
near-line count of the non-principal characters is bounded **uniformly in `q`** at every fixed
level `K > 0`: `OtherLamCountLeK K`.

The constant produced is `C₁ · exp (2K(c+1))`, where `C₁` is the constant of `h` at `ε = 1`. -/
theorem OtherLamCountLeK_of_logFreeNP (σ₀ c : ℝ) (hσ₀ : σ₀ < 1) (hc : 0 < c)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), σ₀ ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((c + ε) * (1 - σ)))
    (K : ℝ) (hK : 0 < K) :
    OtherLamCountLeK K := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := h 1 (by norm_num)
  have hσ01 : 0 < 1 - σ₀ := by linarith
  obtain ⟨Q, hQ2, hQlog⟩ := exists_Q_log_ge_exp σ₀ K hσ₀ hK
  refine ⟨C₁ * Real.exp (2 * K * (c + 1)), mul_pos hC₁pos (Real.exp_pos _), Q, ?_⟩
  intro q hQ _inst χ₁ Λ H hΛ hH
  have hq2 : 2 ≤ q := le_trans hQ2 hQ
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hlogmax := hQlog q hQ
  have hL15 : 15 ≤ Real.log (q : ℝ) := le_trans (le_max_left _ _) hlogmax
  have hLbig : K / (1 - σ₀) ≤ Real.log (q : ℝ) := le_trans (le_max_right _ _) hlogmax
  have hLpos : 0 < Real.log (q : ℝ) := by linarith
  -- the rectangle `(σ, T)` on which the hypothesis is applied
  set σ : ℝ := 1 - max Λ 0 / Real.log (q : ℝ) with hσdef
  set T : ℝ := max H 1 with hTdef
  have h1σ : 1 - σ = max Λ 0 / Real.log (q : ℝ) := by rw [hσdef]; ring
  have hmaxΛ : max Λ 0 ≤ K := max_le hΛ (le_of_lt hK)
  have hσlo : σ₀ ≤ σ := by
    have h3 : max Λ 0 ≤ (1 - σ₀) * Real.log (q : ℝ) := by
      have h4 := (div_le_iff₀ hσ01).mp hLbig
      nlinarith
    have h5 : max Λ 0 / Real.log (q : ℝ) ≤ 1 - σ₀ := (div_le_iff₀ hLpos).mpr h3
    rw [hσdef]; linarith
  have hσhi : σ ≤ 1 := by
    have h : 0 ≤ max Λ 0 / Real.log (q : ℝ) := div_nonneg (le_max_right _ _) hLpos.le
    rw [hσdef]; linarith
  have hT1 : 1 ≤ T := by rw [hTdef]; exact le_max_right _ _
  have hTq : T ≤ 10 * Real.log (q : ℝ) := by
    rw [hTdef]
    exact max_le hH (by linarith)
  -- the hypothesis at `(σ, T)` and the counting lemma
  have hbound := hC₁ q hq2 σ T hσlo hσhi hT1
  have hcount := otherLamCount_le_zeroCountSumNP hq2 χ₁ Λ H
  -- the exponent never exceeds `2 K (c+1)`
  have hE : 0 ≤ (c + 1) * (1 - σ) := by
    rw [h1σ]
    exact mul_nonneg (by linarith) (div_nonneg (le_max_right _ _) hLpos.le)
  have hbase : (q : ℝ) * T ≤ (q : ℝ) * (10 * Real.log (q : ℝ)) :=
    mul_le_mul_of_nonneg_left hTq hqpos.le
  have hbasepos : 0 < (q : ℝ) * (10 * Real.log (q : ℝ)) :=
    mul_pos hqpos (by linarith)
  have hkey : ((q : ℝ) * T) ^ ((c + 1) * (1 - σ)) ≤ Real.exp (2 * K * (c + 1)) := by
    have hbase0 : 0 ≤ (q : ℝ) * T := by
      have : 0 < T := by rw [hTdef]; linarith
      exact mul_nonneg hqpos.le this.le
    have hlogb : Real.log ((q : ℝ) * (10 * Real.log (q : ℝ))) ≤ 2 * Real.log (q : ℝ) :=
      log_mul_ten_log_le hqpos (by linarith)
    have hlogbnn : 0 ≤ 2 * Real.log (q : ℝ) := by linarith
    have hlognn : 0 ≤ Real.log ((q : ℝ) * (10 * Real.log (q : ℝ))) := by
      apply Real.log_nonneg
      calc (1 : ℝ) ≤ 10 * Real.log (q : ℝ) := by linarith
        _ ≤ (q : ℝ) * (10 * Real.log (q : ℝ)) :=
            le_mul_of_one_le_left (by linarith) hq1
    have hE' : (c + 1) * (1 - σ) ≤ K * (c + 1) / Real.log (q : ℝ) := by
      rw [h1σ]
      have h1 : max Λ 0 / Real.log (q : ℝ) ≤ K / Real.log (q : ℝ) :=
        div_le_div_of_nonneg_right hmaxΛ hLpos.le
      have h2 : (c + 1) * (max Λ 0 / Real.log (q : ℝ))
          ≤ (c + 1) * (K / Real.log (q : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      have h3 : (c + 1) * (K / Real.log (q : ℝ)) = K * (c + 1) / Real.log (q : ℝ) := by ring
      linarith [h2, h3]
    have hprod : Real.log ((q : ℝ) * (10 * Real.log (q : ℝ))) * ((c + 1) * (1 - σ))
        ≤ 2 * K * (c + 1) := by
      have h4 := mul_le_mul hlogb hE' hE hlogbnn
      have h5 : 2 * Real.log (q : ℝ) * (K * (c + 1) / Real.log (q : ℝ)) = 2 * K * (c + 1) := by
        field_simp
      linarith [h4, h5]
    calc ((q : ℝ) * T) ^ ((c + 1) * (1 - σ))
        ≤ ((q : ℝ) * (10 * Real.log (q : ℝ))) ^ ((c + 1) * (1 - σ)) :=
          Real.rpow_le_rpow hbase0 hbase hE
      _ = Real.exp (Real.log ((q : ℝ) * (10 * Real.log (q : ℝ))) * ((c + 1) * (1 - σ))) :=
          Real.rpow_def_of_pos hbasepos _
      _ ≤ Real.exp (2 * K * (c + 1)) := Real.exp_le_exp.mpr hprod
  rw [hσdef, hTdef] at hbound hkey
  calc Work.ZeroFreeTables.otherLamCount χ₁ Λ H
      ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          Work.LinnikAreas.zeroCountIn χ (1 - max Λ 0 / Real.log (q : ℝ)) (max H 1) := hcount
    _ ≤ C₁ * ((q : ℝ) * max H 1)
          ^ ((c + 1) * (1 - (1 - max Λ 0 / Real.log (q : ℝ)))) := hbound
    _ ≤ C₁ * Real.exp (2 * K * (c + 1)) := mul_le_mul_of_nonneg_left hkey hC₁pos.le

/-! ## 3. The target: every `K > 0` -/

/-- **The parametric family zero count for every level `K > 0`.**

`OtherLamCountLeK_of_logFreeNP` applied to the workspace's unconditional instance
`Work.ZeroDensity.LogFree.logFreeNP_3979_5000_four` of the log-free non-principal estimate
(exponent coefficient `4` on the range `σ ≥ 3979/5000`), in its `(4+ε)`-form
`Work.ZeroFreeTables.logFreeNP4_countHyp`. -/
theorem OtherLamCountLeK_all : ∀ K : ℝ, 0 < K → Work.ZeroFreeTables.OtherLamCountLeK K :=
  fun K hK => OtherLamCountLeK_of_logFreeNP (3979 / 5000) 4 (by norm_num) (by norm_num)
    logFreeNP4_countHyp K hK

end Work.ZeroFreeTables
