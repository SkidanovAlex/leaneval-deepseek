import Mathlib
import Submission.Work.LinnikAreas.RepulsionCapDefs
import Submission.Work.LinnikAreas.lamOfEps200
import Submission.Work.LinnikAreas.BGTZ.ZFRInput_exists

/-!
# The capped Deuring--Heilbronn repulsion, without AREA 3

`Work.LinnikAreas.RepulsionWithCap ε₀ (7/16)` (see `LinnikAreas/RepulsionCapDefs.lean`) is the
Deuring--Heilbronn repulsion in the working region with the exceptional pair restricted to
`λ(β₁) ≤ ε₀`.  This file proves it for an explicit (tiny) `ε₀`, from *proved* ingredients only:

* **the BGTZ repulsion at all heights**, `BGTZ.RepulsionGenC (11/5) (11/10) C₀`
  (`Work.LinnikAreas.BGTZRepulsionGen`), whose only hypothesis beyond the Siegel datum is the
  *minimality* `λ(β₁) ≤ λ(ρ)` of the exceptional pair;
* **the unconditional uniform zero-free region** `BGTZ.ZFRInput` (proved in
  `BGTZ/ZFRInput_exists.lean` from Landau's repulsion of two real characters, the classical
  zero-free regions and the zero-free region of `ζ`), which gives a *constant* lower bound for
  every zero `ρ ≠ β₁` of every character with `Re ρ > 1/2`, and the elementary bound
  `λ(ρ) ≥ (1/2)·log q` for `Re ρ ≤ 1/2`; together these give the minimality of the exceptional
  pair, which is the only place where `Work.LinnikAreas.RepulsionWith_of_ZeroFreeCert` uses the
  frozen AREA 3 certificate `ZeroFreeCert` (its clauses (Z1)--(Z5));
* the uniform Siegel lower bound `Work.LinnikAreas.lamOfEps200` (`λ₁ ≫ log q/q^{1/200}`).

The cap `ε₀` is chosen below the constants of the zero-free region and small enough for the
two-exponential matching (`hbgUpgrade`, copied from `RepulsionWith_of_ZeroFreeCert`) that turns
the BGTZ bound into the explicit constant `7/16 < 11/25`.

Consumers: `LinnikAreas/siegelRestLowCap.lean`, `LinnikAreas/boxSumBoundCap.lean` and
`LinnikAreas/area6CapChain.lean`.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

open Work.LinnikContract

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **The arithmetic upgrade of the BGTZ repulsion** (copied from
`Work.LinnikAreas.RepulsionWith_of_ZeroFreeCert`): if `lam ≤ lamS` is small and `sig ≤ 2.22`, then
`(log(1/lam) - log(C₀·sig))/sig ≤ lamρ` implies `cr·log(1/lam) ≤ lamρ` for every `cr < 11/25`. -/
private lemma hbgUpgrade {cr C₀ sig lam lamS lamρ : ℝ} (hC₀ : 0 < C₀) (hcr : cr < 11 / 25)
    (hlam : 0 < lam) (hlamS : 0 < lamS) (hsmall : lam ≤ lamS)
    (hlogS : 50 * Real.log (2.22 * C₀ + 10) ≤ Real.log (1 / lamS))
    (hsig1 : 11 / 5 ≤ sig) (hsig2 : sig ≤ 2.22)
    (hbd : (Real.log (1 / lam) - Real.log (C₀ * sig)) / sig ≤ lamρ) :
    cr * Real.log (1 / lam) ≤ lamρ := by
  have hsigpos : 0 < sig := by linarith
  have hC0sig : 0 < C₀ * sig := mul_pos hC₀ hsigpos
  have hlogS' : Real.log (1 / lamS) ≤ Real.log (1 / lam) := by
    rw [one_div, one_div]
    exact Real.log_le_log (inv_pos.mpr hlamS) ((inv_le_inv₀ hlamS hlam).2 hsmall)
  have hlogpos : 0 < Real.log (1 / lam) := by
    have h1 : 0 < Real.log (1 / lamS) := by
      have h2 : 1 < 2.22 * C₀ + 10 := by linarith
      have h3 := Real.log_pos h2
      linarith
    linarith
  have hprod : cr * sig < 49 / 50 := by
    have h1 : cr * sig ≤ (11 / 25) * sig := mul_le_mul_of_nonneg_right (le_of_lt hcr) hsigpos.le
    have h2 : (11 / 25) * sig ≤ (11 / 25) * 2.22 := mul_le_mul_of_nonneg_left hsig2 (by norm_num)
    nlinarith
  have hkey : Real.log (C₀ * sig) ≤ Real.log (1 / lam) * (1 - cr * sig) := by
    have h1 : Real.log (C₀ * sig) ≤ Real.log (2.22 * C₀ + 10) := by
      apply Real.log_le_log hC0sig
      nlinarith [hsig2, hC₀]
    have h2 : Real.log (2.22 * C₀ + 10) ≤ Real.log (1 / lam) / 50 := by linarith
    have h3 : Real.log (1 / lam) / 50 ≤ Real.log (1 / lam) * (1 - cr * sig) := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 50)]
      nlinarith [hlogpos, hprod]
    linarith
  have hmain : cr * Real.log (1 / lam) ≤ (Real.log (1 / lam) - Real.log (C₀ * sig)) / sig := by
    rw [le_div_iff₀ hsigpos]
    nlinarith [hkey]
  linarith

/-- Siegel's lower bound dominates the BGTZ threshold (copied from
`Work.LinnikAreas.RepulsionWith_of_ZeroFreeCert`). -/
private lemma siegelGtBGTZ {q : ℕ} {Cs : ℝ} (hCs : 0 < Cs) (hq : 1 < q)
    (hlogq1 : 1 ≤ Real.log q) (hlogsq : 1 < Cs * (Real.log q) ^ 2) :
    1 / ((q:ℝ) ^ (1 / 100 : ℝ) * Real.log q) < Cs * Real.log q / (q:ℝ) ^ (1 / 200 : ℝ) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by positivity
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq.le
  have hq1' : (1:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hlogpos : 0 < Real.log q := lt_of_lt_of_le one_pos hlogq1
  have hDpos : (0:ℝ) < (q:ℝ) ^ (1 / 200 : ℝ) := Real.rpow_pos_of_pos hq0 _
  have hstep : (q:ℝ) ^ (1 / 200 : ℝ) < (q:ℝ) ^ (1 / 100 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hq1' (by norm_num)
  have h1 : 1 / ((q:ℝ) ^ (1 / 100 : ℝ) * Real.log q)
      < 1 / ((q:ℝ) ^ (1 / 200 : ℝ) * Real.log q) :=
    one_div_lt_one_div_of_lt (by positivity) (mul_lt_mul_of_pos_right hstep hlogpos)
  have h2 : 1 / ((q:ℝ) ^ (1 / 200 : ℝ) * Real.log q)
      ≤ Cs * Real.log q / (q:ℝ) ^ (1 / 200 : ℝ) := by
    have hDne : (q:ℝ) ^ (1 / 200 : ℝ) ≠ 0 := ne_of_gt hDpos
    have hLne : Real.log q ≠ 0 := ne_of_gt hlogpos
    rw [le_div_iff₀ hDpos]
    have heq : 1 / ((q:ℝ) ^ (1 / 200 : ℝ) * Real.log q) * (q:ℝ) ^ (1 / 200 : ℝ)
        = 1 / Real.log q := by field_simp
    rw [heq, div_le_iff₀ hlogpos]
    nlinarith [hlogsq]
  linarith

/-- `sig := 11/5 + (11/10)·log(5+|Im ρ|)/log q` lies in `[11/5, 2.22]` in the working region
(copied from `Work.LinnikAreas.RepulsionWith_of_ZeroFreeCert`). -/
private lemma sigLe {q : ℕ} (hlogq : 1000 ≤ Real.log q) {ρ : ℂ} (him : |ρ.im| ≤ 1) :
    11 / 5 ≤ 11 / 5 + (11 / 10) * (Real.log (5 + |ρ.im|) / Real.log q) ∧
    11 / 5 + (11 / 10) * (Real.log (5 + |ρ.im|) / Real.log q) ≤ 2.22 := by
  have hlogqpos : 0 < Real.log q := by linarith
  have h5 : 0 < 5 + |ρ.im| := by positivity
  have h5gt1 : 1 < 5 + |ρ.im| := by
    have := abs_nonneg ρ.im
    linarith
  have hlog6 : Real.log (5 + |ρ.im|) ≤ 5 := by
    refine le_trans (Real.log_le_sub_one_of_pos h5) ?_
    have := abs_nonneg ρ.im
    linarith
  have hdiv : Real.log (5 + |ρ.im|) / Real.log q ≤ 5 / 1000 := by
    rw [div_le_iff₀ hlogqpos]
    linarith
  constructor
  · have h1 : 0 ≤ (11 / 10 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q) := by
      apply mul_nonneg (by norm_num)
      exact div_nonneg (Real.log_nonneg (le_of_lt h5gt1)) hlogqpos.le
    linarith
  · have h1 : (11 / 10 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q) ≤ (11 / 10) * (5 / 1000) :=
      mul_le_mul_of_nonneg_left hdiv (by norm_num)
    linarith

/-- **The capped Deuring--Heilbronn repulsion with the explicit constant `7/16`.** -/
theorem repulsionWithCap_7_16 (hRepGen : BGTZRepulsionGenE) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ RepulsionWithCap ε₀ (7 / 16) := by
  obtain ⟨Cs, hCspos, hSiegel⟩ := lamOfEps200
  have hsp : 0 < Real.sqrt Cs := Real.sqrt_pos.mpr hCspos
  obtain ⟨cZ, hcZpos, hZFR⟩ := Work.LinnikAreas.BGTZ.ZFRInput_exists
  obtain ⟨qZ, hZFR⟩ := hZFR
  obtain ⟨cZb, hcZbpos, _hzfrLb, hgen⟩ := hRepGen
  set C₀ : ℝ := max (1000 / cZb) 1000 with hC₀def
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨qbg, hbg⟩ := hgen
  -- the cap
  set E : ℝ := Real.exp (-(60 * Real.log (2.22 * C₀ + 10))) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  set ε₀ : ℝ := min (cZ / 2) (min (1 / 100) E) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact lt_min (by positivity) (lt_min (by norm_num) hEpos)
  have hεZ : ε₀ ≤ cZ / 2 := by rw [hε₀def]; exact min_le_left _ _
  have hε1 : ε₀ ≤ 1 / 100 := by
    rw [hε₀def]
    calc min (cZ / 2) (min (1 / 100 : ℝ) E) ≤ min (1 / 100 : ℝ) E := min_le_right _ _
      _ ≤ 1 / 100 := min_le_left _ _
  have hεE : ε₀ ≤ E := by
    rw [hε₀def]
    calc min (cZ / 2) (min (1 / 100 : ℝ) E) ≤ min (1 / 100 : ℝ) E := min_le_right _ _
      _ ≤ E := min_le_right _ _
  refine ⟨ε₀, hε₀pos, by linarith [hε1], ?_⟩
  refine ⟨max (max qZ (max qbg (⌈Real.exp (1000 + 1 / Real.sqrt Cs)⌉₊ + 1))) 4, ?_⟩
  intro q hq hqne χ₁ β₁ hχ₁ hsq hβ₁ hz hle χ ρ hzρ him hne
  haveI : NeZero q := hqne
  have hqZ : qZ ≤ q := by omega
  have hqbg : qbg ≤ q := by omega
  have hqexp : ⌈Real.exp (1000 + 1 / Real.sqrt Cs)⌉₊ + 1 ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  have hq1 : 1 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hq4 : 4 ≤ q := by omega
  have hlogpos : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq1)
  have hexp_le : Real.exp (1000 + 1 / Real.sqrt Cs) ≤ (q : ℝ) := by
    have h2 : Real.exp (1000 + 1 / Real.sqrt Cs)
        ≤ ((⌈Real.exp (1000 + 1 / Real.sqrt Cs)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : ((⌈Real.exp (1000 + 1 / Real.sqrt Cs)⌉₊ + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hqexp
    push_cast at h3
    linarith
  have hlogge : 1000 + 1 / Real.sqrt Cs ≤ Real.log q := by
    calc 1000 + 1 / Real.sqrt Cs = Real.log (Real.exp (1000 + 1 / Real.sqrt Cs)) :=
          (Real.log_exp _).symm
      _ ≤ Real.log q := Real.log_le_log (Real.exp_pos _) hexp_le
  have hlog1000 : 1000 ≤ Real.log q := by
    have h1 : 0 < 1 / Real.sqrt Cs := one_div_pos.mpr hsp
    linarith
  have hkeylog : 1 / Real.sqrt Cs < Real.log q := by linarith
  have hlog1 : 1 ≤ Real.log q := by linarith
  set lam : ℝ := lamOf q (β₁ : ℂ) with hlamdef
  have hle' : lam ≤ ε₀ := by rw [hlamdef]; exact hle
  have hlampos : 0 < lam := Siegel.lamOf_pos hχ₁ hβ₁ hz
  have hlam10 : lam ≤ 1 / 10 := le_trans hle' (by linarith [hε1])
  have hlam100 : lam ≤ 1 / 100 := le_trans hle' hε1
  have hlamZ : lam ≤ cZ / 2 := le_trans hle' hεZ
  have hElam : lam ≤ E := le_trans hle' hεE
  -- the BGTZ hypotheses
  have hsieglow : Cs * Real.log q / (q : ℝ) ^ (1 / 200 : ℝ) ≤ lam := by
    rw [hlamdef]
    exact hSiegel q hq2 χ₁ β₁ hχ₁ hsq hβ₁ hz
  have hlogsq : 1 < Cs * (Real.log q) ^ 2 := by
    have h1 : 1 < Real.sqrt Cs * Real.log q := by
      have h := mul_lt_mul_of_pos_left hkeylog hsp
      have h' : Real.sqrt Cs * (1 / Real.sqrt Cs) = 1 := by field_simp
      rwa [h'] at h
    have h2 : 1 < (Real.sqrt Cs * Real.log q) ^ 2 := by nlinarith
    have h3 : (Real.sqrt Cs * Real.log q) ^ 2 = Cs * (Real.log q) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hCspos.le]
    linarith
  have hbig : 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log q) < lam :=
    lt_of_lt_of_le (siegelGtBGTZ hCspos hq1 hlog1 hlogsq) hsieglow
  have hβ₁hi : 1 - 1 / (10 * Real.log q) < β₁ := by
    have hpos : (0 : ℝ) < 10 * Real.log q := by positivity
    have h2 : (1 - β₁) * Real.log q ≤ 1 / 100 := by
      have h3 := hlam100
      rw [hlamdef, Work.LinnikContract.lamOf] at h3
      exact h3
    have h3 : 1 - β₁ ≤ 1 / (100 * Real.log q) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 100 * Real.log q)]
      have h4 : (1 - β₁) * (100 * Real.log q) = 100 * ((1 - β₁) * Real.log q) := by ring
      rw [h4]
      linarith
    have h4 : 1 / (100 * Real.log q) < 1 / (10 * Real.log q) := by
      apply one_div_lt_one_div_of_lt hpos
      linarith
    linarith
  -- ## the minimality of the exceptional pair
  have hmin : lam ≤ lamOf q ρ := by
    by_cases hρβ : ρ = (β₁ : ℂ)
    · rw [hρβ, ← hlamdef]
    · by_cases hre : ρ.re ≤ 1 / 2
      · -- ## `Re ρ ≤ 1/2`
        have h1 : (1 / 2 : ℝ) * Real.log q ≤ lamOf q ρ := by
          rw [Work.LinnikContract.lamOf]
          exact mul_le_mul_of_nonneg_right (by linarith) hlogpos.le
        have h2 : lam ≤ (1 / 2 : ℝ) * Real.log q := by
          have h500 : (500 : ℝ) ≤ (1 / 2) * Real.log q := by linarith [hlog1000]
          have hε500 : ε₀ ≤ 500 := by linarith [hε1]
          linarith [hle']
        linarith
      · -- ## `Re ρ > 1/2`: the unconditional zero-free region
        push_neg at hre
        have h := hZFR q hqZ χ₁ β₁ hχ₁ hsq hβ₁ hz hβ₁hi χ ρ hzρ hre hρβ
        have hmaxle : max 4 |ρ.im| ≤ 4 := by
          have h1 : |ρ.im| ≤ 4 := by linarith [abs_nonneg ρ.im]
          exact max_le (by norm_num) h1
        have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
        have hbase1 : (1 : ℝ) < (q : ℝ) * max 4 |ρ.im| := by
          have h3 : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq4
          have h4 : (4 : ℝ) ≤ max 4 |ρ.im| := le_max_left _ _
          nlinarith
        have hbase2 : (q : ℝ) * max 4 |ρ.im| ≤ 4 * (q : ℝ) := by nlinarith [hmaxle, hqpos]
        have hlogle : Real.log ((q : ℝ) * max 4 |ρ.im|) ≤ 2 * Real.log q := by
          have h1 := Real.log_le_log (by positivity) hbase2
          have h2 : Real.log (4 * (q : ℝ)) ≤ 2 * Real.log q := by
            rw [Real.log_mul (by norm_num) (by positivity)]
            have h3 : Real.log 4 ≤ Real.log q := by
              have h5 : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq4
              exact Real.log_le_log (by norm_num) h5
            linarith
          linarith
        have hlogpos' : 0 < Real.log ((q : ℝ) * max 4 |ρ.im|) := Real.log_pos hbase1
        have h2 : cZ / 2 ≤ lamOf q ρ := by
          rw [Work.LinnikContract.lamOf]
          have hA : cZ / (2 * Real.log q) ≤ (1 - ρ.re) := by
            have hB : cZ / (2 * Real.log q) ≤ cZ / Real.log ((q : ℝ) * max 4 |ρ.im|) := by
              exact div_le_div_of_nonneg_left (le_of_lt hcZpos) hlogpos' hlogle
            linarith [hB, h]
          have hC : cZ / (2 * Real.log q) * Real.log q = cZ / 2 := by field_simp
          nlinarith [hA, hC, hlogpos]
        linarith [h2, hlamZ]
  -- ## the BGTZ repulsion, upgraded to the constant `7/16`
  have hW := sigLe hlog1000 him
  have hkey := hbg q hqbg χ₁ β₁ hχ₁ hsq hβ₁ hz hbig hlam10 χ ρ hzρ hne hmin
  have hlogS : 50 * Real.log (2.22 * C₀ + 10) ≤ Real.log (1 / lam) := by
    have hL0pos : 0 < Real.log (2.22 * C₀ + 10) := Real.log_pos (by linarith)
    have h1 : Real.exp (60 * Real.log (2.22 * C₀ + 10)) ≤ 1 / lam := by
      rw [le_div_iff₀ hlampos]
      have h2 : Real.exp (60 * Real.log (2.22 * C₀ + 10)) * lam ≤ 1 := by
        have h3 : Real.exp (60 * Real.log (2.22 * C₀ + 10)) * lam
            ≤ Real.exp (60 * Real.log (2.22 * C₀ + 10)) * E :=
          mul_le_mul_of_nonneg_left hElam (Real.exp_pos _).le
        have h4 : Real.exp (60 * Real.log (2.22 * C₀ + 10)) * E = 1 := by
          rw [hEdef, ← Real.exp_add,
            show 60 * Real.log (2.22 * C₀ + 10) + -(60 * Real.log (2.22 * C₀ + 10))
              = 0 by ring, Real.exp_zero]
        linarith
      linarith
    have h5 : Real.log (Real.exp (60 * Real.log (2.22 * C₀ + 10))) ≤ Real.log (1 / lam) :=
      Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h5
    linarith
  exact hbgUpgrade (lamS := lam) hC₀pos (by norm_num) hlampos hlampos le_rfl hlogS hW.1 hW.2 hkey

end

end Work.LinnikAreas
