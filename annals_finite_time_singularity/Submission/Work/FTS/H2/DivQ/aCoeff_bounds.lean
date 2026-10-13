import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.FTS.H2.DivQ.JetDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ### Elementary facts about `κ` on `[0, xNear]` -/

lemma kappa_zero : kappa 0 = 1 := by
  rw [kappa_eq_cos_arcsin, Real.arcsin_zero, Real.cos_zero]

lemma kappa_abs_le_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xNear) : |kappa x| ≤ 1 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2, xNear_lt]
  rw [kappa_eq_sqrt, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg x])

lemma kappa_pos_of_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) xNear) : 0 < kappa x := by
  have hx2 : x ^ 2 < 1 := by nlinarith [hx.1, hx.2, xNear_lt]
  rw [kappa_eq_sqrt]
  exact Real.sqrt_pos.mpr (by linarith)

/-- `1/κ` is bounded on `[0,xNear]`. -/
lemma exists_inv_kappa_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (0 : ℝ) xNear, 1 / kappa x ≤ C := by
  have hpos : ∀ x ∈ Set.Icc (0 : ℝ) xNear, kappa x ≠ 0 :=
    fun x hx => ne_of_gt (kappa_pos_of_mem hx)
  have hcont : ContinuousOn (fun x => 1 / kappa x) (Set.Icc (0 : ℝ) xNear) :=
    continuousOn_const.div (contDiffOn_kappa.continuousOn.mono Icc_subset_U) hpos
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have hk : 0 < kappa x := kappa_pos_of_mem hx
  have h1 : 1 / kappa x = ‖1 / kappa x‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [h1]
  exact le_trans (hC x hx) (le_max_left _ _)

lemma hasDerivAt_kappa {x : ℝ} (hx : x ∈ U) : HasDerivAt kappa (-(x / kappa x)) x := by
  have hx2 : x ^ 2 < 1 := by
    have h1 : |x| < 3 / 4 := abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    nlinarith [abs_nonneg x, sq_abs x]
  have hne : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith
  have h1 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
    have h := (hasDerivAt_const (x := x) (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
    have hf : ((fun _ : ℝ => (1 : ℝ)) - (id : ℝ → ℝ) ^ 2) = fun y : ℝ => 1 - y ^ 2 := by
      funext y; simp
    rw [hf] at h
    convert h using 1
    simp
  have h2 : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-(2 * x) / (2 * Real.sqrt (1 - x ^ 2))) x := h1.sqrt hne
  rw [show kappa = fun y : ℝ => Real.sqrt (1 - y ^ 2) from funext fun y => kappa_eq_sqrt y]
  have hval : -(2 * x) / (2 * Real.sqrt (1 - x ^ 2))
      = -(x / (fun y : ℝ => Real.sqrt (1 - y ^ 2)) x) := by
    change -(2 * x) / (2 * Real.sqrt (1 - x ^ 2)) = -(x / Real.sqrt (1 - x ^ 2))
    ring
  rw [hval] at h2
  exact h2

lemma deriv_two_kappa_eq {x : ℝ} (hx : x ∈ U) :
    deriv (fun y : ℝ => 2 * kappa y) x = -(2 * x / kappa x) := by
  have h : deriv (fun y : ℝ => (2 : ℝ) * kappa y) x = 2 * deriv kappa x :=
    deriv_const_mul 2 (hasDerivAt_kappa hx).differentiableAt
  rw [show (fun y : ℝ => 2 * kappa y) = (fun y : ℝ => (2 : ℝ) * kappa y) from rfl, h,
    (hasDerivAt_kappa hx).deriv]
  ring

lemma contDiffOn_two_kappa : ContDiffOn ℝ ⊤ (fun x : ℝ => 2 * kappa x) U :=
  contDiffOn_const.mul contDiffOn_kappa

lemma exists_jetBdd_two_kappa (K : ℕ) :
    ∃ M : ℝ, JetBdd K (fun x : ℝ => 2 * kappa x) M :=
  exists_jetBdd_of_contDiffOn K contDiffOn_two_kappa

/-! ### The recursion `genCoeff`: equation lemmas and truncation -/

lemma genCoeff_zero_eq (init : ℝ → ℝ) (j : ℕ) :
    genCoeff init 0 j = fun x => if j = 0 then init x else 0 := rfl

lemma genCoeff_succ_eq (init : ℝ → ℝ) (i j : ℕ) :
    genCoeff init i.succ j = fun x =>
      2 * kappa x * (x * deriv (genCoeff init i j) x + (j : ℝ) * genCoeff init i j x)
        + (if j = 0 then 0 else 2 * kappa x * genCoeff init i (j - 1) x) := rfl

lemma genCoeff_init_zero (init : ℝ → ℝ) : genCoeff init 0 0 = init := by
  rw [genCoeff_zero_eq]
  funext x
  simp

lemma genCoeff_succ_zero (init : ℝ → ℝ) (i : ℕ) :
    genCoeff init i.succ 0 = fun x => 2 * kappa x * (x * deriv (genCoeff init i 0) x) := by
  rw [genCoeff_succ_eq]
  funext x
  simp

lemma genCoeff_succ_succ (init : ℝ → ℝ) (i j : ℕ) :
    genCoeff init i.succ j.succ = fun x =>
      2 * kappa x * (x * deriv (genCoeff init i j.succ) x
        + ((j.succ : ℕ) : ℝ) * genCoeff init i j.succ x)
        + 2 * kappa x * genCoeff init i j x := by
  rw [genCoeff_succ_eq]
  funext x
  simp

/-- For `j > i` the coefficient `genCoeff init i j` vanishes identically. -/
lemma genCoeff_zero (init : ℝ → ℝ) : ∀ i j : ℕ, i < j → genCoeff init i j = 0 := by
  intro i
  induction i with
  | zero =>
      intro j hj
      rw [genCoeff_zero_eq]
      funext x
      simp [Nat.pos_iff_ne_zero.mp hj]
  | succ i ih =>
      intro j hj
      rw [genCoeff_succ_eq, ih j (by omega), ih (j - 1) (by omega)]
      funext x
      have hj0 : j ≠ 0 := by omega
      simp [hj0]

lemma bCoeff_eq_genCoeff : ∀ i j : ℕ, bCoeff i j = genCoeff (fun _ : ℝ => 1) i j := by
  intro i
  induction i with
  | zero =>
      intro j
      rw [show bCoeff 0 j = fun _ => (if j = 0 then (1 : ℝ) else 0) from rfl, genCoeff_zero_eq]
  | succ i ih =>
      intro j
      rw [show bCoeff i.succ j = fun x =>
          2 * kappa x * (x * deriv (bCoeff i j) x + (j : ℝ) * bCoeff i j x)
            + (if j = 0 then 0 else 2 * kappa x * bCoeff i (j - 1) x) from rfl,
        genCoeff_succ_eq, ih j, ih (j - 1)]

lemma aCoeff_eq_genCoeff : ∀ i j : ℕ, aCoeff i j = genCoeff (fun x : ℝ => 2 * kappa x) i j := by
  intro i
  induction i with
  | zero =>
      intro j
      rw [show aCoeff 0 j = fun x => (if j = 0 then 2 * kappa x else 0) from rfl, genCoeff_zero_eq]
  | succ i ih =>
      intro j
      rw [show aCoeff i.succ j = fun x =>
          2 * kappa x * (x * deriv (aCoeff i j) x + (j : ℝ) * aCoeff i j x)
            + (if j = 0 then 0 else 2 * kappa x * aCoeff i (j - 1) x) from rfl,
        genCoeff_succ_eq, ih j, ih (j - 1)]

/-! ### The constant recursion and the main `JetBdd` induction -/

/-- One step of the constant recursion of the `JetBdd` induction. -/
noncomputable def levStep (M : ℝ) (n : ℕ) (C : ℝ) : ℝ :=
  (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2) + (2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1)
    + 2 * C + 1

/-- The constant of the `JetBdd` induction at level `i`: `levBound M0 M n i` bounds the first
`n - i` derivatives of the level-`i` coefficients. -/
noncomputable def levBound (M0 M : ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => M0 + 1
  | (i + 1) => levStep M n (levBound M0 M n i)

lemma levBound_succ (M0 M : ℝ) (n i : ℕ) :
    levBound M0 M n i.succ = levStep M n (levBound M0 M n i) := rfl

lemma levBound_nonneg {M0 M : ℝ} (h0 : 0 ≤ M0) (hM : 0 ≤ M) (n : ℕ) :
    ∀ i, 0 ≤ levBound M0 M n i := by
  intro i
  induction i with
  | zero => rw [levBound]; linarith
  | succ i ih =>
      rw [levBound_succ]
      simp only [levStep]
      positivity

private lemma lev_zero_case {M C : ℝ} {K n : ℕ} (hKn : K ≤ n) (hM : 0 ≤ M) (hC : 0 ≤ C) :
    (2 : ℝ) ^ K * M * ((2 : ℝ) ^ K * 1 * C) ≤ levStep M n C := by
  have hA : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hKn
  have hA0 : (0 : ℝ) ≤ (2 : ℝ) ^ K := by positivity
  have hAn : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have hMC : (0 : ℝ) ≤ M * C := mul_nonneg hM hC
  have hAA : (2 : ℝ) ^ K * (2 : ℝ) ^ K ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n := mul_le_mul hA hA hA0 hAn
  have key : (2 : ℝ) ^ K * M * ((2 : ℝ) ^ K * 1 * C) ≤ (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2)) := by
    have h1 : (2 : ℝ) ^ K * (2 : ℝ) ^ K * (M * C) ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) :=
      mul_le_mul_of_nonneg_right hAA hMC
    have h2 : (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 2) := by
      have := mul_le_mul_of_nonneg_left hn2 (mul_nonneg (mul_nonneg hAn hAn) hMC)
      simpa using this
    calc (2 : ℝ) ^ K * M * ((2 : ℝ) ^ K * 1 * C) = (2 : ℝ) ^ K * (2 : ℝ) ^ K * (M * C) := by ring
      _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) := h1
      _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 2) := h2
      _ = (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2)) := by ring
  have hfin : (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2)) ≤ levStep M n C := by
    simp only [levStep]
    have hX : (0 : ℝ) ≤ (2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1 := by positivity
    have hle : (2 : ℝ) ^ n * C * ((n : ℝ) + 2)
        ≤ (2 : ℝ) ^ n * C * ((n : ℝ) + 2) + (2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1 := by linarith
    have := mul_le_mul_of_nonneg_left hle (mul_nonneg hAn hM)
    linarith [this, hC]
  exact key.trans hfin

private lemma lev_succ_case {M C : ℝ} {K n : ℕ} (hKn : K ≤ n) (hM : 0 ≤ M) (hC : 0 ≤ C) :
    (2 : ℝ) ^ K * M * ((2 : ℝ) ^ K * 1 * C + (2 : ℝ) ^ K * (n : ℝ) * C)
      + (2 : ℝ) ^ K * M * C ≤ levStep M n C := by
  have hA : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hKn
  have hA0 : (0 : ℝ) ≤ (2 : ℝ) ^ K := by positivity
  have hAn : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn2 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hAn1 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hMC : (0 : ℝ) ≤ M * C := mul_nonneg hM hC
  have hAA : (2 : ℝ) ^ K * (2 : ℝ) ^ K ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n := mul_le_mul hA hA hA0 hAn
  have hpart1 : (2 : ℝ) ^ K * M * ((2 : ℝ) ^ K * 1 * C + (2 : ℝ) ^ K * (n : ℝ) * C)
      ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 2) := by
    have heq : (2 : ℝ) ^ K * M * ((2 : ℝ) ^ K * 1 * C + (2 : ℝ) ^ K * (n : ℝ) * C)
        = (2 : ℝ) ^ K * (2 : ℝ) ^ K * (M * C) * ((n : ℝ) + 1) := by ring
    rw [heq]
    have h1 : (2 : ℝ) ^ K * (2 : ℝ) ^ K * (M * C) ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) :=
      mul_le_mul_of_nonneg_right hAA hMC
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    have h3 : (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 1)
        ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 2) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact h2.trans h3
  have hpart2 : (2 : ℝ) ^ K * M * C
      ≤ (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1) := by
    have h1 : (2 : ℝ) ^ K * M * C ≤ (2 : ℝ) ^ n * M * C :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hM) hC
    have h2 : (2 : ℝ) ^ n * M * C ≤ (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hAn hM)
      have hX : (0 : ℝ) ≤ (2 : ℝ) ^ n + (n : ℝ) * C + 1 := by positivity
      linarith
    exact h1.trans h2
  have hsum : (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 2)
      + (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1) ≤ levStep M n C := by
    simp only [levStep]
    have hAM : (0 : ℝ) ≤ (2 : ℝ) ^ n * M := by positivity
    have e1 : (2 : ℝ) ^ n * (2 : ℝ) ^ n * (M * C) * ((n : ℝ) + 2)
        = (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2)) := by ring
    have e2 : (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2))
        + (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1)
        = (2 : ℝ) ^ n * M * ((2 : ℝ) ^ n * C * ((n : ℝ) + 2)
            + ((2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1)) := by ring
    rw [e1, e2]
    have hY : (0 : ℝ) ≤ (2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1 := by positivity
    have hle : (2 : ℝ) ^ n * C * ((n : ℝ) + 2)
        ≤ (2 : ℝ) ^ n * C * ((n : ℝ) + 2) + (2 : ℝ) ^ n + ((n : ℝ) + 2) * C + 1 := by linarith
    have := mul_le_mul_of_nonneg_left hle hAM
    linarith [this, hC]
  linarith [hpart1, hpart2, hsum]

/-- **The main induction.**  For `i + K ≤ n`, the first `K + 1` derivatives of every level-`i`
coefficient `genCoeff init i j` with `j ≤ i` are bounded by `levBound Minit Mκ n i` on
`[0, xNear]`; `Minit` bounds the jets of the initial datum, `Mκ` those of `2κ`. -/
theorem genCoeff_jetBdd (n : ℕ) {init : ℝ → ℝ} {Minit Mκ : ℝ}
    (hinit : JetBdd n init Minit) (hκ : JetBdd n (fun x : ℝ => 2 * kappa x) Mκ) :
    ∀ i K : ℕ, i + K ≤ n → ∀ j ≤ i, JetBdd K (genCoeff init i j) (levBound Minit Mκ n i) := by
  intro i
  induction i with
  | zero =>
      intro K hK j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst hj0
      rw [genCoeff_init_zero]
      have hle : JetBdd K init Minit := hinit.jet_mono (by omega)
      refine hle.jet_le ?_
      rw [levBound]
      linarith [hinit.jet_nonneg]
  | succ i ih =>
      intro K hK j hj
      have hM0 : 0 ≤ Minit := hinit.jet_nonneg
      have hMκ0 : 0 ≤ Mκ := hκ.jet_nonneg
      have hC : 0 ≤ levBound Minit Mκ n i := levBound_nonneg hM0 hMκ0 n i
      have ihK : ∀ j ≤ i, JetBdd (K + 1) (genCoeff init i j) (levBound Minit Mκ n i) :=
        ih (K + 1) (by omega)
      have hk : JetBdd K (fun x : ℝ => 2 * kappa x) Mκ := hκ.jet_mono (by omega)
      have hKn : K ≤ n := by omega
      rw [levBound_succ]
      rcases j with _ | j
      · rw [genCoeff_succ_zero]
        have hd : JetBdd K (deriv (genCoeff init i 0)) (levBound Minit Mκ n i) :=
          (ihK 0 (by omega)).jet_deriv
        have h1 : JetBdd K ((fun x : ℝ => x) * deriv (genCoeff init i 0))
            ((2 : ℝ) ^ K * 1 * levBound Minit Mκ n i) := JetBdd.jet_mul (JetBdd.jet_id K) hd
        have h2 : JetBdd K ((fun x : ℝ => 2 * kappa x) * ((fun x : ℝ => x) * deriv (genCoeff init i 0)))
            ((2 : ℝ) ^ K * Mκ * ((2 : ℝ) ^ K * 1 * levBound Minit Mκ n i)) :=
          JetBdd.jet_mul hk h1
        exact h2.jet_le (lev_zero_case hKn hMκ0 hC)
      · rw [genCoeff_succ_succ]
        have hb1 : JetBdd (K + 1) (genCoeff init i j.succ) (levBound Minit Mκ n i) := by
          by_cases hji : j.succ ≤ i
          · exact ihK j.succ hji
          · have heq : j.succ = i.succ := by omega
            rw [heq, genCoeff_zero init i i.succ (by omega)]
            exact (JetBdd.jet_zero (K + 1)).jet_le hC
        have hd1 : JetBdd K (deriv (genCoeff init i j.succ)) (levBound Minit Mκ n i) := hb1.jet_deriv
        have hx1 : JetBdd K ((fun x : ℝ => x) * deriv (genCoeff init i j.succ))
            ((2 : ℝ) ^ K * 1 * levBound Minit Mκ n i) :=
          JetBdd.jet_mul (JetBdd.jet_id K) hd1
        have hjc : JetBdd K ((fun _ : ℝ => ((j.succ : ℕ) : ℝ)) * genCoeff init i j.succ)
            ((2 : ℝ) ^ K * |((j.succ : ℕ) : ℝ)| * levBound Minit Mκ n i) :=
          JetBdd.jet_mul (JetBdd.jet_const K ((j.succ : ℕ) : ℝ)) (hb1.jet_mono (Nat.le_succ K))
        have hjcn : JetBdd K ((fun _ : ℝ => ((j.succ : ℕ) : ℝ)) * genCoeff init i j.succ)
            ((2 : ℝ) ^ K * (n : ℝ) * levBound Minit Mκ n i) := by
          refine hjc.jet_le ?_
          have hle : |((j.succ : ℕ) : ℝ)| ≤ (n : ℝ) := by
            rw [abs_of_nonneg (by positivity)]
            exact_mod_cast (by omega : j.succ ≤ n)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) hC
        have hs : JetBdd K ((fun x : ℝ => x) * deriv (genCoeff init i j.succ)
              + (fun _ : ℝ => ((j.succ : ℕ) : ℝ)) * genCoeff init i j.succ)
            ((2 : ℝ) ^ K * 1 * levBound Minit Mκ n i
              + (2 : ℝ) ^ K * (n : ℝ) * levBound Minit Mκ n i) := hx1.jet_add hjcn
        have hm1 : JetBdd K ((fun x : ℝ => 2 * kappa x)
              * ((fun x : ℝ => x) * deriv (genCoeff init i j.succ)
                + (fun _ : ℝ => ((j.succ : ℕ) : ℝ)) * genCoeff init i j.succ))
            ((2 : ℝ) ^ K * Mκ * ((2 : ℝ) ^ K * 1 * levBound Minit Mκ n i
              + (2 : ℝ) ^ K * (n : ℝ) * levBound Minit Mκ n i)) := JetBdd.jet_mul hk hs
        have hm2 : JetBdd K ((fun x : ℝ => 2 * kappa x) * genCoeff init i j)
            ((2 : ℝ) ^ K * Mκ * levBound Minit Mκ n i) :=
          JetBdd.jet_mul hk ((ihK j (by omega)).jet_mono (Nat.le_succ K))
        exact (hm1.jet_add hm2).jet_le (lev_succ_case hKn hMκ0 hC)

/-! ### The vanishing of the first derivative of the `j = 0` coefficients -/

/-- For the `a`-family (`init = 2κ`) the derivative of the `j = 0` coefficient vanishes at `0`
like `x`: `|(genCoeff (2κ) i 0)'| ≤ C x` on `[0,xNear]`. -/
lemma genCoeff_a0_deriv_le : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ x ∈ Set.Icc (0 : ℝ) xNear,
      |deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x| ≤ C * x := by
  intro i
  induction i with
  | zero =>
      obtain ⟨C0, hC0nn, hC0bd⟩ := exists_inv_kappa_bound
      refine ⟨2 * C0 + 1, by linarith, ?_⟩
      intro x hx
      have hxU : x ∈ U := Icc_subset_U hx
      have hxnn : 0 ≤ x := hx.1
      have hkpos : 0 < kappa x := kappa_pos_of_mem hx
      have hκnn : 0 ≤ kappa x := le_of_lt hkpos
      rw [genCoeff_init_zero, deriv_two_kappa_eq hxU, abs_neg, abs_div,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * x), abs_of_pos hkpos]
      have h2 : 1 ≤ C0 * kappa x := by
        have h1 : 1 / kappa x ≤ C0 := hC0bd x hx
        rwa [div_le_iff₀ hkpos] at h1
      rw [div_le_iff₀ hkpos]
      nlinarith [h2, hxnn, hκnn]
  | succ i ih =>
      obtain ⟨C, hCnn, hCbd⟩ := ih
      obtain ⟨C0, hC0nn, hC0bd⟩ := exists_inv_kappa_bound
      obtain ⟨E, hE⟩ := exists_jetBdd_two_kappa (i + 2)
      have hb : JetBdd 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) (levBound E E (i + 2) i) :=
        genCoeff_jetBdd (n := i + 2) (init := fun y : ℝ => 2 * kappa y) (Minit := E) (Mκ := E)
          hE hE i 2 (by omega) 0 (by omega)
      have hEnn : 0 ≤ levBound E E (i + 2) i :=
        levBound_nonneg hE.jet_nonneg hE.jet_nonneg (i + 2) i
      refine ⟨2 * C0 * C + 2 * C + 2 * levBound E E (i + 2) i + 1,
        by nlinarith [hCnn, hC0nn, hEnn, mul_nonneg hC0nn hCnn], ?_⟩
      intro x hx
      have hxU : x ∈ U := Icc_subset_U hx
      have hxnn : 0 ≤ x := hx.1
      have hx1 : x ≤ 1 := le_trans hx.2 xNear_le_one
      have hkpos : 0 < kappa x := kappa_pos_of_mem hx
      have hκnn : 0 ≤ kappa x := le_of_lt hkpos
      have hsm : ContDiffOn ℝ ⊤ (genCoeff (fun y : ℝ => 2 * kappa y) i 0) U := hb.jet_smooth
      have hdd_smooth : ContDiffOn ℝ ⊤ (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0)) U := by
        simpa [Function.iterate_one] using contDiffOn_iterate_deriv hsm 1
      have hDdiff : DifferentiableAt ℝ (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0)) x :=
        (hdd_smooth.contDiffAt (U_isOpen.mem_nhds hxU)).differentiableAt (by norm_num)
      have hdd : deriv (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0)) x
          = iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x := by
        rw [show deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0)
            = iteratedDeriv 1 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) from
              (iteratedDeriv_one).symm,
          ← iteratedDeriv_succ (n := 1) (f := genCoeff (fun y : ℝ => 2 * kappa y) i 0)]
      have hval : deriv (fun y : ℝ => 2 * kappa y * (y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) y)) x
          = (-(2 * x / kappa x)) * (x * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x)
            + (2 * kappa x) * (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
              + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x) := by
        have hf : HasDerivAt (fun y : ℝ => 2 * kappa y) (-(2 * x / kappa x)) x := by
          have h := (hasDerivAt_kappa hxU).const_mul (2 : ℝ)
          have hv : (2 : ℝ) * (-(x / kappa x)) = -(2 * x / kappa x) := by ring
          rwa [hv] at h
        have hD : HasDerivAt (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0))
            (iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x) x := by
          have h := hDdiff.hasDerivAt
          rwa [hdd] at h
        have hg : HasDerivAt (fun y : ℝ => y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) y)
            (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
              + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x) x := by
          have h := (hasDerivAt_id x).mul hD
          have hfun : (fun y : ℝ => y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) y)
              = (id : ℝ → ℝ) * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) := rfl
          rw [← hfun] at h
          simpa using h
        have hfin : HasDerivAt (fun y : ℝ => 2 * kappa y * (y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) y))
            ((-(2 * x / kappa x)) * (x * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x)
              + (2 * kappa x) * (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
                + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x)) x := by
          have h := hf.mul hg
          have hfun : (fun y : ℝ => 2 * kappa y * (y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) y))
              = (fun y : ℝ => 2 * kappa y)
                * (fun y : ℝ => y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) y) := rfl
          rw [← hfun] at h
          simpa using h
        exact hfin.deriv
      rw [genCoeff_succ_zero, hval]
      have hE2 : |iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x|
          ≤ levBound E E (i + 2) i := hb.jet_bound 2 (by omega) x hx
      have hDx : |deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x| ≤ C * x := hCbd x hx
      have hk1 : |kappa x| ≤ 1 := kappa_abs_le_one hx
      have hA : |-(2 * x / kappa x)| ≤ 2 * C0 * x := by
        rw [abs_neg, abs_of_nonneg (div_nonneg (by positivity) hκnn)]
        have h2 : x / kappa x ≤ C0 * x := by
          have h1 : 1 / kappa x ≤ C0 := hC0bd x hx
          rw [div_le_iff₀ hkpos] at h1 ⊢
          nlinarith [h1, hC0nn, hxnn, hκnn]
        have h3 : 2 * x / kappa x = 2 * (x / kappa x) := by ring
        rw [h3]
        linarith
      have hDxn : |x * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x| ≤ C * x ^ 2 := by
        rw [abs_mul, abs_of_nonneg hxnn]
        nlinarith [hDx, hCnn, hxnn]
      have hinside : |deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
          + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x|
          ≤ (C + levBound E E (i + 2) i) * x := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hxnn]
        have h3 : x * |iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x|
            ≤ x * levBound E E (i + 2) i := mul_le_mul_of_nonneg_left hE2 hxnn
        nlinarith [hDx, h3, hxnn, hEnn, hCnn]
      have hkk : |2 * kappa x| ≤ 2 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith [hk1]
      have t1 : |(-(2 * x / kappa x)) * (x * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x)|
          ≤ 2 * C0 * C * x := by
        rw [abs_mul]
        calc |-(2 * x / kappa x)| * |x * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x|
            ≤ (2 * C0 * x) * (C * x ^ 2) := mul_le_mul hA hDxn (abs_nonneg _) (by positivity)
          _ ≤ 2 * C0 * C * x := by
            have hxx : x ^ 3 ≤ x := by nlinarith [hx1, hxnn]
            nlinarith [hxx, hC0nn, hCnn, hxnn, mul_nonneg hC0nn hCnn]
      have t2 : |2 * kappa x * (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
            + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x)|
          ≤ 2 * (C + levBound E E (i + 2) i) * x := by
        rw [abs_mul]
        calc |2 * kappa x| * |deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
              + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x|
            ≤ 2 * ((C + levBound E E (i + 2) i) * x) :=
              mul_le_mul hkk hinside (abs_nonneg _) (by norm_num)
          _ = 2 * (C + levBound E E (i + 2) i) * x := by ring
      have hsum := (abs_add_le
        ((-(2 * x / kappa x)) * (x * deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x))
        (2 * kappa x * (deriv (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x
          + x * iteratedDeriv 2 (genCoeff (fun y : ℝ => 2 * kappa y) i 0) x)))
      nlinarith [hsum, t1, t2, hxnn]

/-- **Size and vanishing order of the expansion coefficients.**  On `[0, x₁]` (`x₁ = xNear = sin(π/4)`):

* each `b i j` with `j ≤ i` is bounded;
* each `a i l` with `l ≤ i` is bounded;
* for `i ≥ 1` the `l = 0` coefficient vanishes like `x²`: `∃ C ≥ 0, ∀ x ∈ [0,x₁], |a i 0 x| ≤ C x²`.

ROUTE.  Inductions on `i`, using that `κ x = √(1-x²)` is smooth on `[0,x₁]` with `κ ≥ 1/√2` there,
so `κ` and `κ' = -x/κ` are bounded; the finite set of sup norms is handled with the induction
hypotheses (the induction must be strengthened to also bound the first derivatives of the
coefficients, since the recursion differentiates them).  The `x²`-vanishing uses
`a (i+1) 0 = 2κ · x · (a i 0)'` (the `j = 0` branch of the recursion has no second term): if
`a i 0 = x² w i` with `w i` bounded then `2κx(x² w)' = 2κx²(2 w + x w')` is `x²` times the bounded
function `2κ(2w + xw')`.  The base case is `a 1 0 = 2κ·x·(2κ)' = 2κx(-2x/κ) = -4x²` using
`(√(1-x²))' = -x/√(1-x²)` on `(-1,1)`.  (Note the statement excludes `i = 0`, where `a 0 0 = 2κ`
is not `O(x²)`.) -/
theorem aCoeff_bounds (i : ℕ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ i, ∀ x ∈ Set.Icc 0 xNear, |bCoeff i j x| ≤ C) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ i, ∀ x ∈ Set.Icc 0 xNear, |aCoeff i j x| ≤ C) ∧
        (1 ≤ i → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc 0 xNear, |aCoeff i 0 x| ≤ C * x ^ 2) := by
  obtain ⟨Mκ, hMκ⟩ := exists_jetBdd_two_kappa i
  have hM0 : 0 ≤ Mκ := hMκ.jet_nonneg
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨levBound 1 Mκ i i, levBound_nonneg (by norm_num) hM0 i i, ?_⟩
    intro j hj x hx
    have hinit : JetBdd i (fun _ : ℝ => 1) 1 := by
      simpa using (JetBdd.jet_const i (1 : ℝ))
    have h := genCoeff_jetBdd (n := i) (init := fun _ : ℝ => 1) (Minit := 1) (Mκ := Mκ)
      hinit hMκ i 0 (by omega) j hj
    rw [bCoeff_eq_genCoeff]
    simpa using h.jet_bound 0 (Nat.zero_le 0) x hx
  · refine ⟨levBound Mκ Mκ i i, levBound_nonneg hM0 hM0 i i, ?_⟩
    intro j hj x hx
    have h := genCoeff_jetBdd (n := i) (init := fun y : ℝ => 2 * kappa y) (Minit := Mκ)
      (Mκ := Mκ) hMκ hMκ i 0 (by omega) j hj
    rw [aCoeff_eq_genCoeff]
    simpa using h.jet_bound 0 (Nat.zero_le 0) x hx
  · intro hi
    have hpred : (i - 1).succ = i := Nat.succ_pred_eq_of_pos hi
    obtain ⟨C₁, hC₁0, hC₁⟩ := genCoeff_a0_deriv_le (i - 1)
    have hgen : genCoeff (fun y : ℝ => 2 * kappa y) i 0
        = fun y => 2 * kappa y * (y * deriv (genCoeff (fun y : ℝ => 2 * kappa y) (i - 1) 0) y) := by
      conv_lhs => rw [← hpred]
      exact genCoeff_succ_zero (fun y : ℝ => 2 * kappa y) (i - 1)
    refine ⟨2 * C₁, by linarith, ?_⟩
    intro x hx
    have hxnn : 0 ≤ x := hx.1
    have hk1 : |kappa x| ≤ 1 := kappa_abs_le_one hx
    have hD : |deriv (genCoeff (fun y : ℝ => 2 * kappa y) (i - 1) 0) x| ≤ C₁ * x := hC₁ x hx
    rw [aCoeff_eq_genCoeff, hgen, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hxnn]
    have h1 : x * |deriv (genCoeff (fun y : ℝ => 2 * kappa y) (i - 1) 0) x| ≤ C₁ * x ^ 2 := by
      nlinarith [hD, hC₁0, hxnn]
    have h2 : (2 : ℝ) * |kappa x| ≤ 2 * 1 := by linarith [hk1]
    calc (2 : ℝ) * |kappa x| * (x * |deriv (genCoeff (fun y : ℝ => 2 * kappa y) (i - 1) 0) x|)
        ≤ 2 * 1 * (C₁ * x ^ 2) :=
          mul_le_mul h2 h1 (by positivity) (by norm_num)
      _ = (2 * C₁) * x ^ 2 := by ring

end Work.FTS.H2.DivQ
