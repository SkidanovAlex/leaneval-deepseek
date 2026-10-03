/-
# `Work.FIChain.AcountAtil_log_bound`

The scaling estimate

  `log Z · Ã(Z) ≤ C · Ã(N) · (log log N / log N)`   for all `1 ≤ Z ≤ √N`, eventually in `N`,

where `Ã(x) = Σ_{n ≤ x} μ(n)² a_n`, `a_n = #{(a,c) ∈ ℤ² : a² + c⁴ = n}`
(`Work.FIChain.AcountAtilC`).

**Where it comes from.**  The two trivial counting estimates
`Ã(x) ≤ A(x) = #{(a,c) : a² + c⁴ ≤ x} ≪ x^{3/4}` and `Ã(x) ≫ A(x) ≫ x^{3/4}`
(the second is (9.12) of the companion paper, `Submission.ASP.FI_912`, in the form
`Submission.ASP.FI_Aseq_le_const_mul_Atil`) give `Ã(x) ≍ x^{3/4}`.  Hence for `Z ≤ √N`

  `log Z · Ã(Z) ≪ log N · Z^{3/4} ≤ log N · N^{3/8}`,

while `Ã(N) ≫ N^{3/4}`, so it suffices that

  `log N · N^{3/8} ≤ N^{3/4} · log log N / log N`,
  i.e.  `(log N)² ≤ N^{3/8} · log log N`,

which holds for all large `N` (this is `logSq_le_rpow_mul_loglog`, proved below as `aux_logSq`).
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.ASP.S30

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIChain

open Finset Filter

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. `(log N)² ≤ N^{3/8} · log log N` eventually -/

private lemma aux_logSq : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (Real.log (N : ℝ)) ^ 2 ≤ (N : ℝ) ^ ((3 : ℝ) / 8) * Real.log (Real.log (N : ℝ)) := by
  -- the threshold `exp(exp(256/9))` makes `log log N ≥ 256/9 = (16/3)²`
  refine ⟨max 3 (⌈Real.exp (Real.exp (256 / 9))⌉₊ + 1), fun N hN => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hNexp : ⌈Real.exp (Real.exp (256 / 9))⌉₊ + 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNR3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hexp_le : Real.exp (Real.exp (256 / 9)) ≤ (N : ℝ) := by
    have h1 : ((⌈Real.exp (Real.exp (256 / 9))⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (by omega : ⌈Real.exp (Real.exp (256 / 9))⌉₊ ≤ N)
    have h2 : Real.exp (Real.exp (256 / 9)) ≤ ((⌈Real.exp (Real.exp (256 / 9))⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    linarith
  have hlog_exp : Real.exp (256 / 9) ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hexp_le
    rwa [Real.log_exp] at h
  have hll : 256 / 9 ≤ Real.log (Real.log (N : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos (256 / 9)) hlog_exp
    rwa [Real.log_exp] at h
  -- `log N ≤ (16/3)·N^{3/16}`
  have hlogbound : Real.log (N : ℝ) ≤ (16 / 3) * (N : ℝ) ^ ((3 : ℝ) / 16) := by
    have h := Real.log_le_rpow_div hN0 (show (0 : ℝ) < 3 / 16 by norm_num)
    have h2 : (N : ℝ) ^ ((3 : ℝ) / 16) / (3 / 16) = (16 / 3) * (N : ℝ) ^ ((3 : ℝ) / 16) := by
      field_simp
    rw [h2] at h
    exact h
  have hlog2 : (Real.log (N : ℝ)) ^ 2 ≤ (16 / 3) ^ 2 * (N : ℝ) ^ ((3 : ℝ) / 8) := by
    have h1 : 0 ≤ Real.log (N : ℝ) := le_of_lt hlogpos
    have h3 := pow_le_pow_left₀ h1 hlogbound 2
    have h4 : ((16 / 3) * (N : ℝ) ^ ((3 : ℝ) / 16)) ^ 2
        = (16 / 3) ^ 2 * (N : ℝ) ^ ((3 : ℝ) / 8) := by
      rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ ((3 : ℝ) / 16)) 2,
        ← Real.rpow_mul hN0]
      norm_num
    linarith [h3, h4]
  have hmain : (16 / 3) ^ 2 * (N : ℝ) ^ ((3 : ℝ) / 8)
      ≤ (N : ℝ) ^ ((3 : ℝ) / 8) * Real.log (Real.log (N : ℝ)) := by
    have hNp : 0 ≤ (N : ℝ) ^ ((3 : ℝ) / 8) := Real.rpow_nonneg hN0 _
    have h : (16 / 3) ^ 2 ≤ Real.log (Real.log (N : ℝ)) := by
      have h' : ((16 : ℝ) / 3) ^ 2 = 256 / 9 := by norm_num
      rw [h'] at *
      exact hll
    calc (16 / 3) ^ 2 * (N : ℝ) ^ ((3 : ℝ) / 8)
        ≤ Real.log (Real.log (N : ℝ)) * (N : ℝ) ^ ((3 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_right h hNp
      _ = (N : ℝ) ^ ((3 : ℝ) / 8) * Real.log (Real.log (N : ℝ)) := by ring
  linarith [hlog2, hmain]

/-! ## 2. `Ã(x) ≪ x^{3/4}` -/

private lemma aux_C : ∃ C : ℝ, 0 < C ∧ ∀ Z : ℕ, 1 ≤ Z →
    AcountAtilC Z ≤ C * (Z : ℝ) ^ ((3 : ℝ) / 4) := by
  obtain ⟨Cup, hCup_pos, hCup⟩ := Submission.Aseq_le_const_mul_rpow
  refine ⟨Cup, hCup_pos, fun Z hZ => ?_⟩
  have h1 : AcountAtilC Z ≤ Submission.ASP.Acount Submission.ASP.FIa (Z : ℝ) :=
    Submission.ASP.Acount_atil_le Submission.ASP.FIa Submission.ASP.FIa_nonneg (Z : ℝ)
  have h2 : Submission.ASP.Acount Submission.ASP.FIa (Z : ℝ) = (Submission.Aseq Z : ℝ) - 1 :=
    Submission.ASP.FI_Acount_eq Z
  have h3 : (Submission.Aseq Z : ℝ) ≤ Cup * (Z : ℝ) ^ ((3 : ℝ) / 4) := hCup Z hZ
  have h4 : (0 : ℝ) ≤ (Submission.Aseq Z : ℝ) := Nat.cast_nonneg _
  linarith

/-! ## 3. `Ã(x) ≫ x^{3/4}` -/

/-- `Ã(x) ≥ 1` for `x ≥ 1`: the term `n = 1` is `ã_1 = a_1 = #{(1,0),(-1,0)} ≥ 1`. -/
private lemma one_le_AcountAtilC' {x : ℕ} (hx : 1 ≤ x) : 1 ≤ AcountAtilC x := by
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨le_rfl, hx⟩
  have hnn : ∀ i ∈ Finset.Icc 1 x, (0 : ℝ) ≤ Work.FITop.atilFIa i := by
    intro i _
    rw [Work.FITop.atilFIa, Submission.ASP.atil]
    exact Submission.ASP.atil_nonneg Submission.ASP.FIa_nonneg i
  have h1 : Work.FITop.atilFIa 1 ≤ ∑ n ∈ Finset.Icc 1 x, Work.FITop.atilFIa n :=
    Finset.single_le_sum hnn hmem
  have h2 : (1 : ℝ) ≤ Work.FITop.atilFIa 1 := by
    rw [Work.FITop.atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
    have h3 : ((ArithmeticFunction.moebius 1 : ℝ)) ^ 2 = 1 := by
      rw [Submission.ASP.moebius_sq_cast 1, if_pos squarefree_one]
    have h4 : (1 : ℝ) ≤ (Submission.an 1 : ℝ) := by
      exact_mod_cast Submission.ASP.an_one_pos'
    rw [h3, one_mul]
    exact h4
  have h5 : AcountAtilC x = ∑ n ∈ Finset.Icc 1 x, Work.FITop.atilFIa n := by
    rw [Work.FIChain.AcountAtilC, Work.FITop.AcountAtil, Submission.ASP.Acount, Nat.floor_natCast]
  linarith [h1, h2, h5.symm.le]

private lemma aux_D : ∃ c : ℝ, 0 < c ∧ ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
    c * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ AcountAtilC x := by
  obtain ⟨cA, hcA_pos, XA, hcA⟩ := Submission.exists_const_mul_rpow_le_Aseq
  obtain ⟨XG, hG⟩ := Submission.ASP.FI_Aseq_le_const_mul_Atil
  have hGpos : 0 < Submission.ASP.Gprod Submission.ASP.FIg := Submission.ASP.Gprod_FIg_pos
  -- `K = 2/G + 1`: `A(x) ≤ K·Ã(x)` for large `x`, since `A(x) = A_1(x) + 1`, `A_1(x) ≤ (2/G)Ã(x)`
  -- and `Ã(x) ≥ 1`.
  set K : ℝ := 2 / Submission.ASP.Gprod Submission.ASP.FIg + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  refine ⟨cA / K, by positivity, max XA (max XG 1), fun x hx => ?_⟩
  have hxXA : XA ≤ x := le_trans (le_max_left _ _) hx
  have hxXG : XG ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hAseq : cA * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Submission.Aseq x : ℝ) := hcA x hxXA
  have hGx : Submission.ASP.Acount Submission.ASP.FIa (x : ℝ)
      ≤ (2 / Submission.ASP.Gprod Submission.ASP.FIg) * AcountAtilC x := hG x hxXG
  have hone : 1 ≤ AcountAtilC x := one_le_AcountAtilC' hx1
  have hAseq_le : (Submission.Aseq x : ℝ) ≤ K * AcountAtilC x := by
    have h2 := Submission.ASP.FI_Acount_eq x
    rw [h2] at hGx
    have : (2 / Submission.ASP.Gprod Submission.ASP.FIg) * AcountAtilC x + 1
        ≤ K * AcountAtilC x := by
      rw [hKdef]; nlinarith [hone]
    linarith
  have hchain : cA * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ K * AcountAtilC x := le_trans hAseq hAseq_le
  rw [div_mul_eq_mul_div, div_le_iff₀ hKpos]
  linarith [hchain]

/-! ## 4. The scalar step `log Z · Z^{3/4} ≤ N^{3/4} · (log log N / log N)` for `Z ≤ √N` -/

private lemma key_arith {N Z : ℕ} (hN3 : 3 ≤ N)
    (hlog : (Real.log (N : ℝ)) ^ 2
      ≤ (N : ℝ) ^ ((3 : ℝ) / 8) * Real.log (Real.log (N : ℝ)))
    (hZ1 : 1 ≤ Z) (hZs : (Z : ℝ) ≤ Real.sqrt (N : ℝ)) :
    Real.log (Z : ℝ) * (Z : ℝ) ^ ((3 : ℝ) / 4)
      ≤ (N : ℝ) ^ ((3 : ℝ) / 4) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) := by
  have hNR3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hNpos : 0 < (N : ℝ) := by linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hZ1R : (1 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ1
  have hZpos : 0 < (Z : ℝ) := by linarith
  have hZleN : (Z : ℝ) ≤ (N : ℝ) := by
    have h1 : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
      nlinarith [Real.sq_sqrt hN0, Real.sqrt_nonneg (N : ℝ), hN1]
    linarith
  have hlogZnn : 0 ≤ Real.log (Z : ℝ) := Real.log_nonneg hZ1R
  have hlogZle : Real.log (Z : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hZpos hZleN
  have hZpow : (Z : ℝ) ^ ((3 : ℝ) / 4) ≤ (N : ℝ) ^ ((3 : ℝ) / 8) := by
    have h1 : (Z : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
      simpa [Real.sqrt_eq_rpow] using hZs
    have h2 : (Z : ℝ) ^ ((3 : ℝ) / 4) ≤ ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (le_of_lt hZpos) h1 (by norm_num)
    have h3 : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ ((3 : ℝ) / 4) = (N : ℝ) ^ ((3 : ℝ) / 8) := by
      rw [← Real.rpow_mul hN0]
      norm_num
    linarith [h2, h3]
  -- `log Z · Z^{3/4} ≤ log N · N^{3/8}`
  have hstep : Real.log (Z : ℝ) * (Z : ℝ) ^ ((3 : ℝ) / 4)
      ≤ Real.log (N : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 8) :=
    mul_le_mul hlogZle hZpow (Real.rpow_nonneg (le_of_lt hZpos) _) (le_of_lt hlogNpos)
  refine le_trans hstep ?_
  have hNpow_nn : 0 ≤ (N : ℝ) ^ ((3 : ℝ) / 8) := Real.rpow_nonneg hN0 _
  rw [show (N : ℝ) ^ ((3 : ℝ) / 4) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      = ((N : ℝ) ^ ((3 : ℝ) / 4) * Real.log (Real.log (N : ℝ))) / Real.log (N : ℝ) by ring]
  rw [le_div_iff₀ hlogNpos]
  -- `log N · N^{3/8} · log N ≤ N^{3/4} · log log N`
  have hkey : (Real.log (N : ℝ)) ^ 2 * (N : ℝ) ^ ((3 : ℝ) / 8)
      ≤ (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log (Real.log (N : ℝ)) := by
    have h1 : (Real.log (N : ℝ)) ^ 2 * (N : ℝ) ^ ((3 : ℝ) / 8)
        ≤ ((N : ℝ) ^ ((3 : ℝ) / 8) * Real.log (Real.log (N : ℝ)))
          * (N : ℝ) ^ ((3 : ℝ) / 8) :=
      mul_le_mul_of_nonneg_right hlog hNpow_nn
    have h2 : ((N : ℝ) ^ ((3 : ℝ) / 8) * Real.log (Real.log (N : ℝ)))
          * (N : ℝ) ^ ((3 : ℝ) / 8)
        = (N : ℝ) ^ ((3 : ℝ) / 4) * Real.log (Real.log (N : ℝ)) := by
      have h3 : (N : ℝ) ^ ((3 : ℝ) / 8) * (N : ℝ) ^ ((3 : ℝ) / 8)
          = (N : ℝ) ^ ((3 : ℝ) / 4) := by
        rw [← Real.rpow_add hNpos]
        norm_num
      rw [mul_comm ((N : ℝ) ^ ((3 : ℝ) / 8)) (Real.log (Real.log (N : ℝ))), mul_assoc, h3,
        mul_comm]
    linarith [h1, h2]
  have hcomm : Real.log (N : ℝ) * (N : ℝ) ^ ((3 : ℝ) / 8) * Real.log (N : ℝ)
      = (Real.log (N : ℝ)) ^ 2 * (N : ℝ) ^ ((3 : ℝ) / 8) := by ring
  rw [hcomm]
  exact hkey

/-! ## 5. The estimate -/

theorem AcountAtil_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ Z : ℕ,
      1 ≤ Z → (Z : ℝ) ≤ Real.sqrt (N : ℝ) →
      Real.log (Z : ℝ) * Work.FIChain.AcountAtilC Z
        ≤ C * (Work.FIChain.AcountAtilC N
            * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) := by
  obtain ⟨Cup, hCup_pos, hCup⟩ := aux_C
  obtain ⟨c, hc_pos, Xc, hc⟩ := aux_D
  obtain ⟨N₀, hN₀⟩ := aux_logSq
  refine ⟨Cup / c, by positivity, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨max N₀ (max Xc 3), fun N hN => ?_⟩
  intro Z hZ1 hZs
  have hN₀le : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hXc : Xc ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3 : 3 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNR3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hNpos : 0 < (N : ℝ) := by linarith
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hΞ := hN₀ N hN₀le
  have hllpos : 0 < Real.log (Real.log (N : ℝ)) := by
    have h1 : 0 < (Real.log (N : ℝ)) ^ 2 := pow_pos hlogNpos 2
    have h2 : 0 < (N : ℝ) ^ ((3 : ℝ) / 8) := Real.rpow_pos_of_pos hNpos _
    have h3 : 0 < (N : ℝ) ^ ((3 : ℝ) / 8) * Real.log (Real.log (N : ℝ)) :=
      lt_of_lt_of_le h1 hΞ
    exact pos_of_mul_pos_right h3 (le_of_lt h2)
  have hr_nn : 0 ≤ Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) :=
    div_nonneg (le_of_lt hllpos) (le_of_lt hlogNpos)
  have hZ1R : (1 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ1
  have hlogZnn : 0 ≤ Real.log (Z : ℝ) := Real.log_nonneg hZ1R
  have hÃZ : AcountAtilC Z ≤ Cup * (Z : ℝ) ^ ((3 : ℝ) / 4) := hCup Z hZ1
  have h1 : Real.log (Z : ℝ) * AcountAtilC Z
      ≤ Cup * (Real.log (Z : ℝ) * (Z : ℝ) ^ ((3 : ℝ) / 4)) := by
    have h := mul_le_mul_of_nonneg_left hÃZ hlogZnn
    linarith [h]
  have h2 := key_arith hN3 hΞ hZ1 hZs
  have h3 : Cup * (Real.log (Z : ℝ) * (Z : ℝ) ^ ((3 : ℝ) / 4))
      ≤ Cup * ((N : ℝ) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) :=
    mul_le_mul_of_nonneg_left h2 (le_of_lt hCup_pos)
  have hcN : c * (N : ℝ) ^ ((3 : ℝ) / 4) ≤ AcountAtilC N := hc N hXc
  have h5 : Cup * (N : ℝ) ^ ((3 : ℝ) / 4) ≤ (Cup / c) * AcountAtilC N := by
    have h6 := mul_le_mul_of_nonneg_left hcN (by positivity : (0 : ℝ) ≤ Cup / c)
    have h7 : (Cup / c) * (c * (N : ℝ) ^ ((3 : ℝ) / 4)) = Cup * (N : ℝ) ^ ((3 : ℝ) / 4) := by
      field_simp
    rwa [h7] at h6
  have h4 : Cup * ((N : ℝ) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)))
      ≤ (Cup / c) * (AcountAtilC N * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) := by
    calc Cup * ((N : ℝ) ^ ((3 : ℝ) / 4) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)))
        = (Cup * (N : ℝ) ^ ((3 : ℝ) / 4))
            * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) := by ring
      _ ≤ ((Cup / c) * AcountAtilC N)
            * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_right h5 hr_nn
      _ = (Cup / c) * (AcountAtilC N
            * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))) := by ring
  linarith [h1, h3, h4]

end

end Work.FIChain
