/-
# `ApSumTenth.integral_riPhi_Ici_one` — the total mass of the Rosser–Iwaniec upper profile

The Rosser–Iwaniec upper profile `riPhi = F − 1` (with `F` the upper function of the linear
sieve) has total mass `2` on the half line:

  `∫_{Ici 1} riPhi = 2`.

The proof does **not** evaluate any integral: it combines

* the summed delay recursion `s · riPsi s = ∫_{Ici (s−1)} riPhi` (`riSys_mul_riPsi_eq_integral`,
  `ApSumTenth.riPhi_delay_system`) at `s = 2`, which reads `2 · riPsi 2 = ∫_{Ici 1} riPhi`,
* the limiting value `riPsi 2 = 1`.

The latter is the classical normalization `1 − f(2) = 1` of the Rosser–Iwaniec lower function.
It is obtained from the closed form

  `u · oddSum (n+1) u = (3 + Cv n) log (3/(u−1)) − 4 + u + Tv (n+1)`  (`oddSum_formula`)

at `u = 2`, letting `n → ∞`:

  `2 · riPsi 2 = (3 + Ctot) log 3 − 2 + Ttot`,

together with the *exact* limit form of the first-moment identity

  `Ctot · log 3 + Ttot = 4 − 3 log 3`,

which is the limit of the exact level identity
`Dv (k+1) − Dv k = 4 − 3 log 3 − Cv k log 3 − Tv (k+1)` (`Dv_diff`).  The only analytic input
for that limit is that `Dv` is nondecreasing (from the monotonicity `Gv_mono` of the centred
first moment) and bounded above by `18` (from the crude majorant `crudeV = 6 exp (2 − s)` of
`riPsi`, whose first moment converges).
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiDelay
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiLevelCore
import Submission.Work.NumberTheory.Chen.APSwitchUpper.oddSum_formula
import Submission.Work.NumberTheory.Chen.APSwitchUpper.moment_ineq
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhi_le_env
import Submission.Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_system

namespace Work.NumberTheory.Chen.ApSumTenth

open MeasureTheory Filter
open scoped BigOperators Topology
open Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

/-! ## §1  The level constants `Cv`, `Tv` and the centred first moment `Gv` -/

/-- `Cv (n+1) − Cv n = P (n+1)`: the level `Cv` increments by the mass `P` of the last odd
delay profile. -/
lemma Cv_diff (n : ℕ) : Cv (n + 1) - Cv n = P (n + 1) := by
  rw [Cv_eq_sum_P (n + 1), Cv_eq_sum_P n, Finset.sum_range_succ]
  ring

/-- `Dv` is nondecreasing: `Dv (n+1) − Dv n` splits into the (nonnegative) increment of the
centred first moment `Gv` and twice the (nonnegative) increment of `Cv`. -/
lemma Dv_mono : Monotone Dv := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hcvd : 0 ≤ Cv (n + 1) - Cv n := by
    rw [Cv_diff n]; exact P_nonneg (n + 1)
  have hrel : Dv (n + 1) - Dv n = (Gv (n + 1) - Gv n) + 2 * (Cv (n + 1) - Cv n) := by
    simp only [Gv]; ring
  linarith [hrel, Gv_mono n, hcvd]

/-! ## §2  The bound `Dv n ≤ 18` from the crude majorant `crudeV` -/

/-- The first moment of the crude majorant `6 x exp (2 − x)` of `riPsi`:
its antiderivative is `−6 (x+1) exp (2 − x)`. -/
lemma hasDerivAt_crudeV_moment :
    ∀ s : ℝ, HasDerivAt (fun t : ℝ => -(6 * ((t + 1) * Real.exp (2 - t))))
      (6 * (s * Real.exp (2 - s))) s := by
  intro s
  have h1 : HasDerivAt (fun t : ℝ => t + 1) 1 s := (hasDerivAt_id s).add_const 1
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (2 - t)) (Real.exp (2 - s) * (-1)) s := by
    have h := (hasDerivAt_const s (2 : ℝ)).sub (hasDerivAt_id s)
    simpa using h.exp
  have h3 : HasDerivAt (fun t : ℝ => (t + 1) * Real.exp (2 - t))
      (1 * Real.exp (2 - s) + (s + 1) * (Real.exp (2 - s) * (-1))) s := h1.mul h2
  have h4 : HasDerivAt (fun t : ℝ => -(6 * ((t + 1) * Real.exp (2 - t))))
      (-(6 * (1 * Real.exp (2 - s) + (s + 1) * (Real.exp (2 - s) * (-1))))) s :=
    (h3.const_mul 6).neg
  convert h4 using 1
  ring

/-- `Dv n ≤ 18`: the level-`n` first moment is dominated by the first moment of `crudeV`. -/
lemma Dv_le_eighteen (n : ℕ) : Dv n ≤ 18 := by
  have hM2 : (2 : ℝ) ≤ ((2 * n + 4 : ℕ) : ℝ) := by
    push_cast; exact_mod_cast (by omega : 2 ≤ 2 * n + 4)
  have hbound : ∀ x ∈ Set.Icc (2 : ℝ) (((2 * n + 4 : ℕ) : ℝ)),
      x * oddSum n x ≤ 6 * (x * Real.exp (2 - x)) := by
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := hx.1
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have h1 : oddSum n x ≤ crudeV x := riSys_oddSum_le_crudeV n x hx2
    calc x * oddSum n x ≤ x * crudeV x := mul_le_mul_of_nonneg_left h1 hx0
      _ = 6 * (x * Real.exp (2 - x)) := by rw [crudeV]; ring
  have hInt1 : IntervalIntegrable (fun x : ℝ => x * oddSum n x) volume (2 : ℝ)
      (((2 * n + 4 : ℕ) : ℝ)) := oddSum_mul_id_int n 2 _
  have hInt2 : IntervalIntegrable (fun x : ℝ => 6 * (x * Real.exp (2 - x))) volume (2 : ℝ)
      (((2 * n + 4 : ℕ) : ℝ)) :=
    (by fun_prop : Continuous (fun x : ℝ => 6 * (x * Real.exp (2 - x)))).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on hM2 hInt1 hInt2 hbound
  have hcalc : (∫ x in (2 : ℝ)..(((2 * n + 4 : ℕ) : ℝ)), 6 * (x * Real.exp (2 - x))) ≤ 18 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_crudeV_moment x) hInt2
    rw [h]
    have hF2 : -(6 * ((2 + 1) * Real.exp (2 - 2))) = -18 := by
      norm_num [Real.exp_zero]
    rw [hF2]
    have hnn : 0 ≤ 6 * ((((2 * n + 4 : ℕ) : ℝ) + 1) * Real.exp (2 - ((2 * n + 4 : ℕ) : ℝ))) :=
      mul_nonneg (by norm_num) (mul_nonneg (by linarith [hM2]) (le_of_lt (Real.exp_pos _)))
    linarith
  show Dv n ≤ 18
  rw [Dv]
  linarith [hmono, hcalc]

/-! ## §3  The exact limit of the first-moment identity: `Ctot log 3 + Ttot = 4 − 3 log 3` -/

/-- **The moment identity of the Rosser–Iwaniec profiles.**  The level identity `Dv_diff`,
together with the monotone convergence of the bounded sequence `Dv`, gives the exact relation
`Ctot · log 3 + Ttot = 4 − 3 log 3` between the totals `Ctot = ∫_2^∞ riPsi` and
`Ttot = ∫_3^∞ riPhi`. -/
theorem mass_moment_eq : Ctot * Real.log 3 + Ttot = 4 - 3 * Real.log 3 := by
  have hbdd : BddAbove (Set.range Dv) :=
    ⟨18, by rintro x ⟨n, rfl⟩; exact Dv_le_eighteen n⟩
  obtain ⟨L, hL⟩ : ∃ L, Tendsto Dv atTop (𝓝 L) :=
    ⟨_, tendsto_atTop_ciSup Dv_mono hbdd⟩
  have hL1 : Tendsto (fun n : ℕ => Dv (n + 1)) atTop (𝓝 L) :=
    hL.comp (tendsto_add_atTop_nat 1)
  have hzero : Tendsto (fun n : ℕ => Dv (n + 1) - Dv n) atTop (𝓝 0) := by
    have h := hL1.sub hL
    simpa using h
  have hlim : Tendsto (fun n : ℕ => 4 - 3 * Real.log 3 - Cv n * Real.log 3 - Tv (n + 1))
      atTop (𝓝 (4 - 3 * Real.log 3 - Ctot * Real.log 3 - Ttot)) := by
    have hA : Tendsto (fun n : ℕ => Cv n * Real.log 3) atTop (𝓝 (Ctot * Real.log 3)) :=
      tendsto_Cv.mul tendsto_const_nhds
    exact (tendsto_const_nhds.sub hA).sub (tendsto_Tv_add 1)
  have hlim' : Tendsto (fun n : ℕ => Dv (n + 1) - Dv n) atTop
      (𝓝 (4 - 3 * Real.log 3 - Ctot * Real.log 3 - Ttot)) :=
    hlim.congr' (Eventually.of_forall (fun n => (Dv_diff n).symm))
  have h0 : 4 - 3 * Real.log 3 - Ctot * Real.log 3 - Ttot = 0 := tendsto_nhds_unique hlim' hzero
  linarith [h0]

/-! ## §4  The normalization `riPsi 2 = 1` -/

/-- The partial odd sums tend to `riPsi` at `s = 2`. -/
lemma tendsto_oddSum_two : Tendsto (fun n : ℕ => oddSum (n + 1) 2) atTop (𝓝 (riPsi 2)) := by
  have hsum : HasSum (fun i : ℕ => profC (2 * i + 1) 2) (riPsi 2) :=
    (riSys_summable_odd 2 (by norm_num)).hasSum
  have h1 : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, profC (2 * i + 1) 2) atTop
      (𝓝 (riPsi 2)) := hsum.tendsto_sum_nat
  have h2 : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 2), profC (2 * i + 1) 2) atTop
      (𝓝 (riPsi 2)) := h1.comp (tendsto_add_atTop_nat 2)
  refine h2.congr' (Eventually.of_forall (fun n => ?_))
  show (∑ i ∈ Finset.range (n + 2), profC (2 * i + 1) 2) = oddSum (n + 1) 2
  rfl

/-- **The normalization `riPsi 2 = 1`** (the value `1 − f(2)` of the Rosser–Iwaniec lower
function at `2`). -/
theorem riPsi_two : riPsi 2 = 1 := by
  have hodd := tendsto_oddSum_two
  have hmain1 : Tendsto (fun n : ℕ => 2 * oddSum (n + 1) 2) atTop (𝓝 (2 * riPsi 2)) :=
    hodd.const_mul 2
  have hformula : ∀ n : ℕ, 2 * oddSum (n + 1) 2 = (3 + Cv n) * Real.log 3 - 2 + Tv (n + 1) := by
    intro n
    have h := oddSum_formula n (u := 2) (by norm_num) (by norm_num)
    have h' : (3 : ℝ) / (2 - 1) = 3 := by norm_num
    rw [h'] at h
    linarith [h]
  have hmain2 : Tendsto (fun n : ℕ => (3 + Cv n) * Real.log 3 - 2 + Tv (n + 1)) atTop
      (𝓝 ((3 + Ctot) * Real.log 3 - 2 + Ttot)) := by
    have hA : Tendsto (fun n : ℕ => (3 + Cv n) * Real.log 3) atTop
        (𝓝 ((3 + Ctot) * Real.log 3)) :=
      (tendsto_const_nhds.add tendsto_Cv).mul tendsto_const_nhds
    exact (hA.sub tendsto_const_nhds).add (tendsto_Tv_add 1)
  have hmain2' : Tendsto (fun n : ℕ => 2 * oddSum (n + 1) 2) atTop
      (𝓝 ((3 + Ctot) * Real.log 3 - 2 + Ttot)) :=
    hmain2.congr' (Eventually.of_forall (fun n => (hformula n).symm))
  have heq : 2 * riPsi 2 = (3 + Ctot) * Real.log 3 - 2 + Ttot :=
    tendsto_nhds_unique hmain1 hmain2'
  have hexp : (3 + Ctot) * Real.log 3 - 2 + Ttot
      = 3 * Real.log 3 + (Ctot * Real.log 3 + Ttot) - 2 := by ring
  have h2 : 2 * riPsi 2 = 2 := by
    rw [heq, hexp, mass_moment_eq]
    ring
  linarith [h2]

/-! ## §5  The target -/

theorem integral_riPhi_Ici_one :
    (∫ u in Set.Ici (1 : ℝ), Work.NumberTheory.Chen.APSwitchUpper.riPhi u) = 2 := by
  have h := riSys_mul_riPsi_eq_integral 2 (by norm_num)
  rw [show (2 : ℝ) - 1 = 1 from by norm_num] at h
  rw [← h, riPsi_two]
  ring

end

end Work.NumberTheory.Chen.ApSumTenth
