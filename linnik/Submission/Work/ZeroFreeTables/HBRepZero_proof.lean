/-
# ZeroFreeTables — HBRepZero_proof

**`Work.ZeroFreeTables.HBRepZero`**: in the *real–real* case of Heath-Brown's §6/§8
repeated-zero analysis — `χ₁` real (`χ₁² = 1`), the exceptional zero `ρ₁` real and
*multiple* (`2 ≤ zeroMult χ₁ ρ₁`) — one has `λ₁ ≥ 1.724` as soon as `λ₁ ≤ 0.7`.

The claim is the multiple-zero conjunct of HB's Table 4 entry `(0.7, 1.724)`
(`HBRepZero_red.hbRepZero_of_table4` derives it from `HBTable4`), but it is proved
here *directly* from the §6 engine the workspace already has, so that no input `Prop`
is needed:

* **`hb6Repeated`** — HB §6/§8 with the *repeated* zero: for a test function `f` of
  HB's Conditions 1–2, a real character `χ` and a real `β₁` in the §6 region whose
  window carries a zero of multiplicity `≥ 2`,
  `2F(−λ₁) − 4F(0) + f(0)(2c + 3ε) ≥ 0`, `λ₁ = (1−β₁) log q`.
  (HB's Lemma 6.4 at `ρ⁰ = ρ₁`, `µ⁰ = 0`: the two points `β⁰` and `β⁰+iγ⁰` coincide,
  so the zero `ρ₁` contributes twice to each of the two window sums of §6 — that is
  HB's *"or a repeated zero `ρ₀ = ρ₁`"* — giving the factor `4F(0)` that the
  distinct-zero Lemma 6.3 does not have.)
* **`winSum_two_mul`** — the window sum at `β₁` dominates twice the multiplicity-one
  contribution `F(0)`.
* **HB Lemma 7.2's test function** (`testFn7_2`) at the fixed scale `λ = 7/10`
  (`F(0) = 8/9`, `F(−7/10) = 8/5`, `f(0) = 56/75`) and the Burgess input `L52Hyp`
  with the real-character constant `1/6` turn the inequality into `λ₁ ≥ 4/3 − O(ε)`,
  contradicting `λ₁ ≤ 0.7`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.EngineRoadmap
import Submission.Work.ZeroFreeTables.HBRepZero_red
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.LinnikAreas.lemma6_3_wide
import Submission.Work.LinnikAreas.principalKsumWide
import Submission.Work.LinnikAreas.l52HypReal
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroFreeTables.winSum_two_mul
import Submission.Work.ZeroFreeTables.hb6Repeated
import Submission.Work.ZeroFreeTables.l52Hyp_real_fixedC
import Submission.Work.ZeroFreeTables.tf72_arith_false
import Submission.Work.NumberTheory.Linnik.scratch_kpos_real
import Submission.Work.NumberTheory.Linnik.scratch_l63
import Submission.Commons.NumberTheory.Linnik.le_windowSum_of_mem

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## Point conditions at the exceptional zero -/

/-- **Point conditions at the exceptional zero, for large `q`.**  If `ρ` is a
`zeroMult`-zero of `χ` (hence `0 < Re ρ < 1`) with `λ(ρ) ≤ 7/10`, then for
`q ≥ q₀(δ)` its real part `β = Re ρ` satisfies `|1 - β| ≤ δ`, HB's §6 point range
`|1 - β| ≤ √(log log q)/log q`, and `λ(ρ) > 0`. -/
private lemma rep_guard (δ : ℝ) (hδ0 : 0 < δ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
      zeroMult χ ρ ≠ 0 → lamOf q ρ ≤ 7/10 →
      |1 - ρ.re| ≤ δ ∧
        |1 - ρ.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ∧
        ρ.re < 1 ∧ 0 < lamOf q ρ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (max (7/10 / δ) 2))
  refine ⟨max N 3, ?_⟩
  intro q hq hqne χ ρ hzm h710
  have hqN : (N : ℝ) ≤ (q : ℝ) := by exact_mod_cast (le_trans (le_max_left N 3) hq)
  have hexp_lt : Real.exp (max (7/10 / δ) 2) < (q : ℝ) := lt_of_lt_of_le hN hqN
  have hC : max (7/10 / δ) 2 < Real.log (q : ℝ) := by
    have := Real.log_lt_log (Real.exp_pos _) hexp_lt
    rwa [Real.log_exp] at this
  have hlogC1 : 7/10 / δ < Real.log (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hC
  have hlogC2 : (2 : ℝ) < Real.log (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hC
  have hlogq_pos : 0 < Real.log (q : ℝ) := by linarith
  have hre : ρ.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hzm
  have hone : 0 < 1 - ρ.re := by linarith
  have hlam0pos : 0 < lamOf q ρ := by rw [lamOf]; exact mul_pos hone hlogq_pos
  have hle : 1 - ρ.re ≤ (7/10) / Real.log (q : ℝ) := by
    rw [lamOf] at h710
    rw [le_div_iff₀ hlogq_pos]
    linarith
  have habs : |1 - ρ.re| = 1 - ρ.re := abs_of_pos hone
  refine ⟨?_, ?_, hre, hlam0pos⟩
  · rw [habs]
    have h2 : (7/10) / Real.log (q : ℝ) ≤ δ := by
      rw [div_le_iff₀ hlogq_pos]
      rw [div_lt_iff₀ hδ0] at hlogC1
      nlinarith
    linarith
  · rw [habs]
    have h2 : (7/10) / Real.log (q : ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
      rw [div_le_div_iff_of_pos_right hlogq_pos]
      have h3 : (7/10 : ℝ) ≤ Real.sqrt (Real.log 2) := by
        rw [Real.le_sqrt (by norm_num : (0:ℝ) ≤ 7/10) (Real.log_nonneg (by norm_num))]
        nlinarith [Real.log_two_gt_d9]
      have h4 : Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) :=
        Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) hlogC2.le)
      linarith
    linarith

/-! ## The assembly -/

theorem HBRepZero_proof : Work.ZeroFreeTables.HBRepZero := by
  obtain ⟨δ, hδ0, hδ1, q₀L, hL52⟩ := l52Hyp_real_fixedC
  obtain ⟨q₀g, hg⟩ := rep_guard δ hδ0
  obtain ⟨T, hTx₀, hTf₀, hTF₀, hTFneg⟩ := testFn7_2 (7/10) (by norm_num)
  obtain ⟨B, hBnn, hBnd⟩ := T.f_bound
  obtain ⟨q₀R, hR⟩ := hb6Repeated (x₀ := T.x₀) (B := B) (c := 1/6 + 1/1000000)
    (ε := 1/100) (δ := δ) T.x₀_pos hBnn (by norm_num) hδ0 hδ1 T.f_cont T.f_supp T.f_diff
    hBnd T.f0_pos T.f_nonneg
    (fun z hz => by rw [← T.Fc_spec z]; exact T.Fc_re_nonneg z hz)
  refine ⟨max (max (max q₀R q₀L) q₀g) 3, ?_⟩
  intro q hq hqne χ₁ ρ₁ hm hsq him hmult hlam
  have hqR : q₀R ≤ q := by omega
  have hqL : q₀L ≤ q := by omega
  have hqg : q₀g ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  have hχ1 : χ₁ ≠ 1 := hm.1.1.1
  have hzm : zeroMult χ₁ ρ₁ ≠ 0 := hm.1.1.2.1
  obtain ⟨hβ₁δ, hpt, hre1, hlampos⟩ := hg q hqg χ₁ ρ₁ hzm hlam
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hcast : ((ρ₁.re : ℝ) : ℂ) = ρ₁ := Complex.ext (by simp) (by simp [him])
  letI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  -- Heath-Brown's minimality, in the `re` form used by the window bound
  have hminre : ∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ 1 → u.re ≤ ρ₁.re := by
    intro u hu himu
    have hle : lamOf q ρ₁ ≤ lamOf q u := hm.1.2 χ₁ u ⟨hχ1, hu, himu⟩
    rw [lamOf, lamOf] at hle
    have h2 := (mul_le_mul_iff_of_pos_right hlogq).mp hle
    linarith
  -- the window sum carries the doubled zero
  have hwin := winSum_two_mul (q := q) χ₁ hχ1 (f := T.f) (x₀ := T.x₀) (L := Real.log q)
    (δ := δ) (β₁ := ρ₁.re) (le_of_lt hlogq) hδ1
    (fun z hz => by rw [← T.Fc_spec z]; exact T.Fc_re_nonneg z hz)
    hβ₁δ (by rw [hcast]; exact hmult) hminre
  -- the Burgess input at this modulus
  have H : Commons.NumberTheory.Linnik.L52Hyp χ₁ (1/6 + 1/1000000) (1/100) δ :=
    hL52 q hqL χ₁ hχ1 hsq (1/100) (by norm_num) (by norm_num)
  -- HB §6, repeated-zero case
  have hreal : χ₁ * χ₁ = 1 := by simpa [pow_two] using hsq
  have hcore := hR (q := q) hqR χ₁ hχ1 hreal (β₁ := ρ₁.re) hβ₁δ hpt H hwin
  -- rewrite the two Laplace values in `F`-form
  have hA : T.F (-(lamOf q ρ₁))
      = ∫ t in (0:ℝ)..T.x₀, Real.exp ((Real.log (q : ℝ) * (1 - ρ₁.re)) * t) * T.f t := by
    rw [TestFn_F_eq_integral, lamOf]
    apply intervalIntegral.integral_congr
    intro t _
    show Real.exp (-(-((1 - ρ₁.re) * Real.log (q : ℝ)) * t)) * T.f t
        = Real.exp ((Real.log (q : ℝ) * (1 - ρ₁.re)) * t) * T.f t
    have harg : -(-((1 - ρ₁.re) * Real.log (q : ℝ)) * t)
        = (Real.log (q : ℝ) * (1 - ρ₁.re)) * t := by ring
    rw [harg]
  have hB : T.F 0 = ∫ t in (0:ℝ)..T.x₀, T.f t := by
    rw [TestFn_F_eq_integral]
    apply intervalIntegral.integral_congr
    intro t _
    show Real.exp (-(0 * t)) * T.f t = T.f t
    simp
  have hineq : 0 ≤ 2 * T.F (-(lamOf q ρ₁)) - 4 * T.F 0
      + T.f 0 * (2 * (1/6 + 1/1000000) + 3 * (1/100)) := by
    rw [hA, hB]
    linarith only [hcore]
  have hf0 : T.f 0 = 56/75 := by rw [hTf₀]; norm_num
  exact (tf72_arith_false hf0 hTF₀ hTFneg hlam hineq).elim

end Work.ZeroFreeTables
