
import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas.Density4.zeroDetAux
import Submission.Work.LinnikAreas.Density4.psiM_divisor_sum_zero
import Submission.Work.LinnikAreas.Density4.pow_sub_pow_mul_le
import Submission.Work.LinnikAreas.Density4.abel_sum_Icc
import Submission.Work.LinnikAreas.Density4.sum_exp_div_le
import Submission.Work.LinnikAreas.Density4.sum_one_div_succ_le_log
import Submission.Work.LinnikAreas.Density4.cube_mul_exp_neg_le
import Submission.Work.LinnikAreas.Density4.sum_mul_diff_le

namespace Work.LinnikAreas2

open Work.LinnikAreas.Density4

/-!
# `LinnikAreas2.PsiDefs2` — the `ψ`-mollifier vocabulary, in the `LinnikAreas2` namespace

A copy of `Submission/Work/LinnikAreas/Density4/psi_defs.lean` with the declarations moved into
the `Work.LinnikAreas2` namespace and the (unused) import of the module
`Work.LinnikAreas.Density4.sum_log_div_le` dropped.

Why the copy: the module `Work.LinnikAreas.Density4.sum_log_div_le` and the *lemma*
`Work.LinnikAreas.Density4.sum_log_div_le` (declared in
`Submission/Work/LinnikAreas/Density4/sum_abs_selLam_le.lean`, used by the `ZeroDensity/Jutila`
branch) have the same name, so no module whose import cone contains both can be elaborated.  The
`(D1)` assembly needs `psi_defs` while the `θ`-sieve (`graham_theta_sieve`) needs the Jutila
branch.  Keeping the `ψ`-vocabulary in this namespace removes `psi_defs` from the cone of the
assembly and dissolves the clash without touching any other area's files.

The model definitions `psiM`, `psiS` stay in `Work.LinnikAreas.Density4` (their defining modules
`Defs`/`zeroDetAux` are unrelated to the clash).
-/

open scoped BigOperators

noncomputable section

/-- `Ψ(n)²` where `Ψ(n) = ∑_{d | n} ψ_d` is the `ψ`-mollifier divisor sum of HB (11.6). -/
def psiSq (U V : ℝ) (n : ℕ) : ℝ := (∑ d ∈ n.divisors, psiM U V d)^2

/-- The partial sums `A(N) = Σ_{n ≤ N} Ψ(n)²` whose sharp bounds are HB (11.13). -/
def psSum (U V : ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, psiSq U V n

/-- The Heath-Brown weight `e^{-n/X} - e^{-nL²/U}`. -/
def wt (L U X : ℝ) (n : ℕ) : ℝ := Real.exp (-(n:ℝ)/X) - Real.exp (-(n:ℝ)*L^2/U)

/-- `φ(n) = (e^{-n/X} - e^{-nL²/U})/n`, the weight divided by `n`. -/
def phiW (L U X : ℝ) (n : ℕ) : ℝ := wt L U X n / n

/-- The lower bound `min 1 e^{-(x-u)/2}` for `L` in the case `U ≤ L² X`. -/
def Lmin (u x : ℝ) : ℝ := min 1 (Real.exp (-(x-u)/2))

lemma psiSq_nonneg (U V : ℝ) (n : ℕ) : 0 ≤ psiSq U V n := sq_nonneg _

lemma psiSq_one {U V : ℝ} (hU : 1 ≤ U) : psiSq U V 1 = 1 := by
  rw [psiSq, Nat.divisors_one, Finset.sum_singleton, psiM]
  rw [if_pos (by simpa using hU)]
  norm_num

lemma psiSq_eq_zero {U V : ℝ} (hU : 1 ≤ U) (hUV : U ≤ V) {n : ℕ} (hn : 2 ≤ n)
    (hnU : (n : ℝ) ≤ U) : psiSq U V n = 0 := by
  rw [psiSq, psiM_divisor_sum_zero hU hUV hn hnU]
  ring

lemma psSum_eq_one {U V : ℝ} (hU : 1 ≤ U) (hUV : U ≤ V) {N : ℕ} (hN : 1 ≤ N)
    (hNU : (N : ℝ) ≤ U) : psSum U V N = 1 := by
  have key : (∑ n ∈ Finset.Icc 1 N, psiSq U V n) = psiSq U V 1 :=
    Finset.sum_eq_single_of_mem (s := Finset.Icc 1 N) (f := fun n => psiSq U V n) (1 : ℕ)
      (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)
      (fun b hb hb1 => by
        have hb1' : 1 ≤ b := (Finset.mem_Icc.mp hb).1
        have hb2 : 2 ≤ b := by omega
        have hbU : (b : ℝ) ≤ U := by
          have : (b : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hb).2
          linarith
        exact psiSq_eq_zero hU hUV hb2 hbU)
  rw [psSum, key, psiSq_one hU]

lemma psSum_nonneg (U V : ℝ) (N : ℕ) : 0 ≤ psSum U V N :=
  Finset.sum_nonneg (fun n _ => psiSq_nonneg U V n)

lemma psiSq_le_psSum {U V : ℝ} {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    psiSq U V n ≤ psSum U V N := by
  rw [psSum]
  exact Finset.single_le_sum (fun b _ => psiSq_nonneg U V b)
    (Finset.mem_Icc.mpr ⟨hn, hnN⟩)

lemma wt_le_one {L U X : ℝ} (_hU : 0 < U) (hX : 0 < X) (n : ℕ) : wt L U X n ≤ 1 := by
  have h1 : Real.exp (-(n:ℝ)/X) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    have h2 : 0 ≤ (n:ℝ)/X := div_nonneg (by positivity) hX.le
    linarith
  have h2 : 0 ≤ Real.exp (-(n:ℝ)*L^2/U) := (Real.exp_pos _).le
  rw [wt]; linarith

lemma wt_le_exp {L U X : ℝ} (n : ℕ) : wt L U X n ≤ Real.exp (-(n:ℝ)/X) := by
  have h2 : 0 ≤ Real.exp (-(n:ℝ)*L^2/U) := (Real.exp_pos _).le
  rw [wt]; linarith

lemma wt_le_mul {L U X : ℝ} (hU : 0 < U) (hX : 0 < X) (n : ℕ) :
    wt L U X n ≤ (n:ℝ) * (L^2/U) := by
  have h1 : Real.exp (-(n:ℝ)/X) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    have h2 : 0 ≤ (n:ℝ)/X := div_nonneg (by positivity) hX.le
    linarith
  have h2 : 1 - (n:ℝ) * L^2 / U ≤ Real.exp (-((n:ℝ) * L^2 / U)) := Real.one_sub_le_exp_neg _
  have h3 : Real.exp (-(n:ℝ)*L^2/U) = Real.exp (-((n:ℝ) * L^2 / U)) := by ring_nf
  have h4 : (n:ℝ) * (L^2/U) = (n:ℝ) * L^2 / U := by ring
  rw [wt, h3, h4]
  linarith

lemma wt_nonneg {L U X : ℝ} (hU : 0 < U) (hX : 0 < X) (hcase : U ≤ L^2 * X) (n : ℕ) :
    0 ≤ wt L U X n := by
  have hn : (0:ℝ) ≤ (n:ℝ) := by positivity
  have hle : (n:ℝ) / X ≤ (n:ℝ) * L^2 / U := by
    rw [div_le_div_iff₀ hX hU]
    have h2 : U * (n:ℝ) ≤ (L^2*X) * (n:ℝ) := by nlinarith [hcase, hn]
    nlinarith [h2]
  have e1 : Real.exp (-(n:ℝ)*L^2/U) = Real.exp (-((n:ℝ)*L^2/U)) := by ring_nf
  have e2 : Real.exp (-(n:ℝ)/X) = Real.exp (-((n:ℝ)/X)) := by ring_nf
  rw [wt, e1, e2]
  have : Real.exp (-((n:ℝ)*L^2/U)) ≤ Real.exp (-((n:ℝ)/X)) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

lemma phiW_nonneg {L U X : ℝ} (hU : 0 < U) (hX : 0 < X) (hcase : U ≤ L^2 * X) (n : ℕ) :
    0 ≤ phiW L U X n := by
  rw [phiW]
  exact div_nonneg (wt_nonneg hU hX hcase n) (by positivity)

/-- The key algebraic identity relating the first difference of `φ` to that of `wt`. -/
lemma phiW_sub_ident {L U X : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    (n:ℝ) * (phiW L U X n - phiW L U X (n+1))
      = (wt L U X n - wt L U X (n+1)) + wt L U X (n+1) / ((n:ℝ) + 1) := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hn1 : ((n:ℝ) + 1) ≠ 0 := by positivity
  rw [phiW, phiW]
  field_simp
  push_cast
  ring

/-- In the case `U ≤ L² X` the weight `φ(n) = (e^{-n/X}-e^{-nL²/U})/n` is nonincreasing in `n ≥ 1`. -/
lemma phiW_sub_nonneg {L U X : ℝ} (hU : 0 < U) (hX : 0 < X) (hcase : U ≤ L^2 * X) {n : ℕ}
    (hn : 1 ≤ n) : 0 ≤ phiW L U X n - phiW L U X (n+1) := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1R : (0:ℝ) < (n:ℝ) + 1 := by linarith
  set p : ℝ := Real.exp (-(1/X)) with hp
  set q : ℝ := Real.exp (-(L^2/U)) with hq
  have hqpos : 0 < q := by rw [hq]; exact Real.exp_pos _
  have hp_le_one : p ≤ 1 := by
    rw [hp, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have h2 : 0 ≤ Real.exp 0 / X := div_nonneg (Real.exp_pos 0).le hX.le
    linarith
  have hqp : q ≤ p := by
    rw [hq, hp]
    apply Real.exp_le_exp.mpr
    have h : (1:ℝ)/X ≤ L^2/U := by
      rw [div_le_div_iff₀ hX hU]
      nlinarith [hcase]
    linarith
  have e1 : Real.exp (-(n:ℝ)/X) = p^n := by
    rw [hp, ← Real.exp_nat_mul]; congr 1; ring
  have e2 : Real.exp (-(n:ℝ)*L^2/U) = q^n := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; ring
  have e3 : Real.exp (-(((n+1 : ℕ)):ℝ)/X) = p^(n+1) := by
    rw [hp, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e4 : Real.exp (-(((n+1 : ℕ)):ℝ)*L^2/U) = q^(n+1) := by
    rw [hq, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hWn : wt L U X n = p^n - q^n := by rw [wt, e1, e2]
  have hWn1 : wt L U X (n+1) = p^(n+1) - q^(n+1) := by rw [wt, e3, e4]
  have hkey := pow_sub_pow_mul_le hqpos hqp hp_le_one hn
  rw [phiW, phiW, hWn, hWn1]
  have hcast : (((n+1 : ℕ)):ℝ) = (n:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hmain : (p^(n+1) - q^(n+1))/((n:ℝ)+1) ≤ (p^n - q^n)/(n:ℝ) := by
    rw [div_le_div_iff₀ hn1R hnR]
    linarith [hkey]
  linarith

/-- Telescoping of the `φ`-differences over a range. -/
lemma phiW_telescope {L U X : ℝ} {M : ℕ} (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Ico 1 M, (phiW L U X n - phiW L U X (n+1)) = phiW L U X 1 - phiW L U X M := by
  have h : ∑ i ∈ Finset.Ico 1 M, (phiW L U X (i+1) - phiW L U X i)
      = phiW L U X M - phiW L U X 1 := Finset.sum_Ico_sub (f := phiW L U X) hM
  have h2 : ∑ i ∈ Finset.Ico 1 M, (phiW L U X (i+1) - phiW L U X i)
      = -∑ i ∈ Finset.Ico 1 M, (phiW L U X i - phiW L U X (i+1)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h2] at h
  linarith

/-- Telescoping bound for the differences of a nonnegative sequence. -/
lemma sum_Ico_diff_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (A M : ℕ) :
    ∑ n ∈ Finset.Ico A M, (w n - w (n+1)) ≤ w A := by
  by_cases h : M ≤ A
  · rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty]
    exact hw A
  · have h1 : ∑ i ∈ Finset.Ico A M, (w (i+1) - w i) = w M - w A :=
      Finset.sum_Ico_sub (f := w) (not_le.mp h).le
    have h2 : ∑ i ∈ Finset.Ico A M, (w i - w (i+1))
        = -∑ i ∈ Finset.Ico A M, (w (i+1) - w i) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [h2, h1]
    linarith [hw A, hw M]

/-- `Finset.Icc A B` sums are `Finset.Ico A (B+1)` sums. -/
lemma sum_Icc_eq_sum_Ico_succ {f : ℕ → ℝ} (A B : ℕ) :
    ∑ n ∈ Finset.Icc A B, f n = ∑ n ∈ Finset.Ico A (B+1), f n := by
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega

/-- `Finset.Icc 1 (N-1)` sums are `Finset.Ico 1 N` sums. -/
lemma sum_Icc_one_eq_sum_Ico {f : ℕ → ℝ} (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 (N-1), f n = ∑ n ∈ Finset.Ico 1 N, f n := by
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega

end

end Work.LinnikAreas2
