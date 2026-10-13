import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.NonlinRows.NRow19T2Parts.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-- The (`z`-only) Leibniz bound for `K₁₉ = A·H₂`: the `D_θ^b`-derivative always lands on `A`,
and the `∂_z^k`-derivative splits by the binomial rule against `H₂`. -/
theorem K19_pz_Dth_le {α : ℝ} {Φs : Fn}
    (hAsm : Work.FTS.EllipticEst.SmoothOpen (A19 α Φs))
    {k b : ℕ} (hk : k ≤ 4) (hb : b ≤ 4) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.pzIter k (Work.Spaces.DthIter b (K19 α Φs)) z θ|
        ≤ 257 * ∑ c ∈ Finset.range (k + 1),
            |Work.Spaces.pzIter c (Work.Spaces.DthIter b (A19 α Φs)) z θ|
              * |deriv^[k - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| := by
  intro z hz θ hθ
  have h := Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open k b hk hb
    (A19 α Φs) H2f hAsm smoothOpen_H2f z hz θ hθ
  have h' : |Work.Spaces.pzIter k (Work.Spaces.DthIter b (K19 α Φs)) z θ|
      ≤ 257 * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (b + 1),
          |Work.Spaces.pzIter c (Work.Spaces.DthIter a (A19 α Φs)) z θ|
            * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (b - a) H2f) z θ| := by
    rw [show K19 α Φs = (fun z θ => A19 α Φs z θ * H2f z θ) from rfl]
    exact h
  refine h'.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Finset.sum_le_sum fun c _ => ?_
  have hH2 : H2f = (fun z θ => Work.FTS.Nonlinear.Open.Row19Prep.H2b z) := rfl
  have hsingle : (∑ a ∈ Finset.range (b + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (A19 α Φs)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (b - a) H2f) z θ|)
      = |Work.Spaces.pzIter c (Work.Spaces.DthIter b (A19 α Φs)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (b - b) H2f) z θ| :=
    Finset.sum_eq_single b (fun a ha hne => by
      obtain ⟨n, hn⟩ : ∃ n, b - a = n + 1 := by
        rw [Finset.mem_range] at ha
        exact ⟨b - a - 1, by omega⟩
      have hz0 : Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (b - a) H2f) z θ = 0 := by
        rw [hH2, hn, Work.FTS.Nonlinear.Open.Row19Prep.DthIter_succ_z_only
          Work.FTS.Nonlinear.Open.Row19Prep.H2b n]
        exact congrFun (congrFun (pzIter_zero_fun (k - c)) z) θ
      rw [hz0, abs_zero, mul_zero]) (fun hmem => by
        rw [Finset.mem_range] at hmem
        omega)
  rw [hsingle]
  have hb0 : b - b = 0 := by omega
  rw [hb0, Work.Spaces.DthIter_zero, hH2, pzIter_zOnly]

/-- **The (η)-family**: the weighted `∂_z^m`-bound for `Z₁₉`. -/
theorem Z19_eta_bound {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hAsm : Work.FTS.EllipticEst.SmoothOpen (A19 α Φs))
    (hAmem : Work.Spaces.WlInfMem α 4 (A19 α Φs)) {C2 : ℝ}
    (hC2 : ∀ m j : ℕ, m ≤ 4 → j ≤ m → ∀ z : ℝ, 0 < z →
      (1 + z) * Work.Spaces.w z * z ^ m / (1 + z) ^ (m - j)
        * |deriv^[j] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| ≤ C2)
    (hC2nn : 0 ≤ C2) :
    ∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m (Z19 α Φs) z θ|
        ≤ 200000 * (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs)) := by
  intro m hm z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hL0 : 0 ≤ Work.Spaces.WlInf α 4 (A19 α Φs) := WlInf_nonneg' α 4 _ hAmem
  -- `pzIter m Z19 = c19 θ · pzIter m K19`
  have hZeq : Work.Spaces.pzIter m (Z19 α Φs) z θ
      = c19 α θ * Work.Spaces.pzIter m (K19 α Φs) z θ := by
    rw [show Z19 α Φs = (fun z θ => c19 α θ * K19 α Φs z θ) from rfl,
      Work.FTS.H2.pzIter_const_mul]
  have hKleib := K19_pz_Dth_le hAsm hm (by norm_num : (0:ℕ) ≤ 4) z hz θ hθ
  rw [Work.Spaces.DthIter_zero] at hKleib
  -- `|c19 θ| ≤ 10α`
  have hc19 : |c19 α θ| ≤ 10 * α := by
    have hc : (0 : ℝ) < Work.Spaces.c α := by
      have := (Work.Spaces.c_bounds α hα hα1).1
      linarith
    have hcf : c19 α θ = (α / Work.Spaces.c α) * Work.Spaces.Gam α θ := rfl
    rw [hcf, abs_mul]
    have hk : |α / Work.Spaces.c α| ≤ 10 * α := by
      rw [abs_of_nonneg (div_nonneg hα.le hc.le), div_le_iff₀ hc]
      nlinarith [(Work.Spaces.c_bounds α hα hα1).1]
    have hG1 : |Work.Spaces.Gam α θ| ≤ 1 := by
      rw [abs_of_nonneg (Gam_nonneg' hα hθI)]
      exact Gam_le_one' hα hθI
    calc |α / Work.Spaces.c α| * |Work.Spaces.Gam α θ|
        ≤ (10 * α) * 1 := mul_le_mul hk hG1 (abs_nonneg _) (by positivity)
      _ = 10 * α := by ring
  -- the weight
  have hAw : (1 + z) * Work.Spaces.w z * z ^ m = (1 + z) ^ 3 * z ^ m / z ^ 2 := by
    rw [Work.Spaces.w]
    field_simp
  have hAraw0 : 0 ≤ (1 + z) ^ 3 * z ^ m / z ^ 2 := by positivity
  have h257 : (0 : ℝ) ≤ 257 := by norm_num
  have h5nn : (0 : ℝ) ≤ 5 := by norm_num
  have h10a : (0 : ℝ) ≤ 10 * α := by linarith
  -- termwise bound
  have hterm : ∀ c ∈ Finset.range (m + 1),
      (1 + z) ^ 3 * z ^ m / z ^ 2
          * (|Work.Spaces.pzIter c (A19 α Φs) z θ|
              * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)
        ≤ Work.Spaces.WlInf α 4 (A19 α Φs) * C2 := by
    intro c hc
    have hc_le : c ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
    have hc4 : c ≤ 4 := by omega
    have hzc : (0 : ℝ) ≤ (1 + z) ^ c := by positivity
    have hsplit : (1 + z) ^ 3 * z ^ m / z ^ 2
        = (1 + z) ^ c * ((1 + z) ^ 3 * z ^ m / z ^ 2 / (1 + z) ^ c) := by
      have h1 : (0 : ℝ) < 1 + z := by linarith
      have h2 : (0 : ℝ) < (1 + z) ^ c := pow_pos h1 c
      field_simp
    rw [hsplit]
    have h1 : (1 + z) ^ c * ((1 + z) ^ 3 * z ^ m / z ^ 2 / (1 + z) ^ c)
          * (|Work.Spaces.pzIter c (A19 α Φs) z θ|
              * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)
        = ((1 + z) ^ c * |Work.Spaces.pzIter c (A19 α Φs) z θ|)
          * ((1 + z) ^ 3 * z ^ m / z ^ 2 / (1 + z) ^ c
              * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|) := by ring
    rw [h1]
    have hA := Work.Spaces.WlInf_z_bound α 4 (A19 α Φs) hAmem c hc4 z θ hzI hθI
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (z + 1) ^ c by positivity)] at hA
    have hA' : (1 + z) ^ c * |Work.Spaces.pzIter c (A19 α Φs) z θ|
        ≤ Work.Spaces.WlInf α 4 (A19 α Φs) := by
      rw [show (1 : ℝ) + z = z + 1 by ring]
      exact hA
    have hB := hC2 m (m - c) hm (by omega) z hz
    have hmc : m - (m - c) = c := by omega
    rw [hmc] at hB
    have hB' : (1 + z) ^ 3 * z ^ m / z ^ 2 / (1 + z) ^ c
        * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| ≤ C2 := by
      rwa [← hAw]
    have hden0 : 0 ≤ (1 + z) ^ 3 * z ^ m / z ^ 2 / (1 + z) ^ c := by positivity
    have hB0 : 0 ≤ (1 + z) ^ 3 * z ^ m / z ^ 2 / (1 + z) ^ c
        * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| :=
      mul_nonneg hden0 (abs_nonneg _)
    exact mul_le_mul hA' hB' hB0 hL0
  have hsum : (∑ c ∈ Finset.range (m + 1),
        (1 + z) ^ 3 * z ^ m / z ^ 2
          * (|Work.Spaces.pzIter c (A19 α Φs) z θ|
              * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))
      ≤ 5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2) := by
    have hs : (∑ c ∈ Finset.range (m + 1),
          (1 + z) ^ 3 * z ^ m / z ^ 2
            * (|Work.Spaces.pzIter c (A19 α Φs) z θ|
                * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))
        ≤ ∑ _c ∈ Finset.range (m + 1),
            Work.Spaces.WlInf α 4 (A19 α Φs) * C2 := Finset.sum_le_sum hterm
    refine hs.trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hL0 hC2nn)
    exact_mod_cast (show m + 1 ≤ 5 by omega)
  have hS0 : 0 ≤ ∑ c ∈ Finset.range (m + 1),
      |Work.Spaces.pzIter c (A19 α Φs) z θ|
        * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| :=
    Finset.sum_nonneg fun c _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hKleib' : |Work.Spaces.pzIter m (K19 α Φs) z θ|
      ≤ 257 * ∑ c ∈ Finset.range (m + 1),
          |Work.Spaces.pzIter c (A19 α Φs) z θ|
            * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z| := hKleib
  have hstep1 : |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m (Z19 α Φs) z θ|
      = ((1 + z) ^ 3 * z ^ m / z ^ 2)
          * (|c19 α θ| * |Work.Spaces.pzIter m (K19 α Φs) z θ|) := by
    rw [hZeq, hAw, abs_mul, abs_of_nonneg hAraw0, abs_mul]
  have hstep2 : ((1 + z) ^ 3 * z ^ m / z ^ 2)
          * (|c19 α θ| * |Work.Spaces.pzIter m (K19 α Φs) z θ|)
      ≤ ((1 + z) ^ 3 * z ^ m / z ^ 2)
          * ((10 * α) * (257 * (∑ c ∈ Finset.range (m + 1),
              |Work.Spaces.pzIter c (A19 α Φs) z θ|
                * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))) := by
    refine mul_le_mul_of_nonneg_left ?_ hAraw0
    refine mul_le_mul hc19 ?_ (abs_nonneg _) h10a
    exact hKleib'
  have hstep3 : ((1 + z) ^ 3 * z ^ m / z ^ 2)
          * ((10 * α) * (257 * (∑ c ∈ Finset.range (m + 1),
              |Work.Spaces.pzIter c (A19 α Φs) z θ|
                * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)))
      = 10 * α * 257 * (∑ c ∈ Finset.range (m + 1),
          (1 + z) ^ 3 * z ^ m / z ^ 2
            * (|Work.Spaces.pzIter c (A19 α Φs) z θ|
                * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)) := by
    rw [show ((1 + z) ^ 3 * z ^ m / z ^ 2)
          * ((10 * α) * (257 * (∑ c ∈ Finset.range (m + 1),
              |Work.Spaces.pzIter c (A19 α Φs) z θ|
                * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)))
        = 10 * α * 257 * (((1 + z) ^ 3 * z ^ m / z ^ 2)
            * (∑ c ∈ Finset.range (m + 1),
              |Work.Spaces.pzIter c (A19 α Φs) z θ|
                * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|)) from by ring,
      Finset.mul_sum]
  have hstep4 : 10 * α * 257 * (∑ c ∈ Finset.range (m + 1),
        (1 + z) ^ 3 * z ^ m / z ^ 2
          * (|Work.Spaces.pzIter c (A19 α Φs) z θ|
              * |deriv^[m - c] Work.FTS.Nonlinear.Open.Row19Prep.H2b z|))
      ≤ 200000 * (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs)) := by
    refine (mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 10 * α * 257)).trans ?_
    have hαΛ : 0 ≤ α * Work.Spaces.WlInf α 4 (A19 α Φs) := mul_nonneg hα.le hL0
    have hcoef : 10 * α * 257 * (5 * (Work.Spaces.WlInf α 4 (A19 α Φs) * C2))
        = 12850 * C2 * (α * Work.Spaces.WlInf α 4 (A19 α Φs)) := by ring
    have hcoef2 : 200000 * (CZ19 C2 * α * Work.Spaces.WlInf α 4 (A19 α Φs))
        = (200000 * (10 ^ 20 * (1 + C2) * (1 + TB19)))
            * (α * Work.Spaces.WlInf α 4 (A19 α Φs)) := by
      rw [CZ19]; ring
    rw [hcoef, hcoef2]
    have hle : 12850 * C2 ≤ 200000 * (10 ^ 20 * (1 + C2) * (1 + TB19)) := by
      nlinarith [hC2nn, TB19_nonneg]
    exact mul_le_mul_of_nonneg_right hle hαΛ
  exact hstep1.le.trans (hstep2.trans (hstep3.le.trans hstep4))


end Work.FTS.NonlinRows
