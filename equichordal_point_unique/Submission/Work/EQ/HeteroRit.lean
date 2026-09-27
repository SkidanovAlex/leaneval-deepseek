import Mathlib
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.HeteroGerm
import Submission.Work.EQ.HeteroChain
import Submission.Work.EQ.HeteroR
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.germC_y_inverse

/-! ## The iterated backward branch map and its analyticity -/

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-- The `k`-fold backward branch map applied to a germ point. -/
def Rk (a : ℝ) (h : ℂ → ℂ) : ℕ → ℂ → ℂ × ℂ
  | 0, u => germC a h u
  | (k + 1), u => invBranch a true (Rk a h k u)

@[simp] theorem Rk_zero (a : ℝ) (h : ℂ → ℂ) (u : ℂ) : Rk a h 0 u = germC a h u := rfl

@[simp] theorem Rk_succ (a : ℝ) (h : ℂ → ℂ) (k : ℕ) (u : ℂ) :
    Rk a h (k + 1) u = invBranch a true (Rk a h k u) := rfl

/-- **Analyticity of the iterated branch map.**  If the points `Rk a h k u` avoid the singular
locus near `u₀`, then `u ↦ Rk a h k u` is analytic near `u₀`. -/
theorem analyticAt_Rk {a : ℝ} {h : ℂ → ℂ} {r : ℝ} (hh : IsStableGerm a h r)
    {k : ℕ} {u₀ : ℂ} (han : AnalyticAt ℂ (germC a h) u₀)
    (hslit : ∀ j : ℕ, j < k → bsq (subO1 a (Rk a h j u₀)) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun u => Rk a h k u) u₀ := by
  induction k with
  | zero => simpa using han
  | succ k ih =>
      have h1 : AnalyticAt ℂ (fun u => Rk a h k u) u₀ :=
        ih (fun j hj => hslit j (Nat.lt_trans hj (Nat.lt_succ_self k)))
      have hslit' : bsq (subO1 a (Rk a h k u₀)) ∈ Complex.slitPlane := hslit k (Nat.lt_succ_self k)
      have hne0 : bsq (subO1 a (Rk a h k u₀)) ≠ 0 :=
        fun h0 => Complex.zero_notMem_slitPlane (h0 ▸ hslit')
      have hg1 : AnalyticAt ℂ (fun u => (Rk a h k u).1) u₀ :=
        ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (Rk a h k u₀)).comp h1
      have hg2 : AnalyticAt ℂ (fun u => (Rk a h k u).2) u₀ :=
        ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (Rk a h k u₀)).comp h1
      have hbsq : AnalyticAt ℂ (fun u => bsq (subO1 a (Rk a h k u))) u₀ := by
        have hh' : (fun u => bsq (subO1 a (Rk a h k u)))
            = fun u => ((Rk a h k u).1 + (((a / 2 : ℝ)) : ℂ)) ^ 2 + (Rk a h k u).2 ^ 2 := by
          funext u; simp [bsq, subO1]
        rw [hh']
        exact ((hg1.add analyticAt_const).pow 2).add (hg2.pow 2)
      have hρ : AnalyticAt ℂ (fun u => (bsq (subO1 a (Rk a h k u))) ^ (1 / 2 : ℂ)) u₀ :=
        hbsq.cpow analyticAt_const hslit'
      have hρ0 : (bsq (subO1 a (Rk a h k u₀))) ^ (1 / 2 : ℂ) ≠ 0 := by
        intro hc
        refine hne0 ?_
        have h := Complex.cpow_nat_inv_pow (bsq (subO1 a (Rk a h k u₀))) (n := 2) (by norm_num)
        rw [show (1 / 2 : ℂ) = (((2 : ℕ)) : ℂ)⁻¹ by norm_num] at hc
        rw [hc, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h
        exact h.symm
      have hA : AnalyticAt ℂ (fun u => -((Rk a h k u).1)
          + ((Rk a h k u).1 + (((a / 2 : ℝ)) : ℂ))
            / ((bsq (subO1 a (Rk a h k u))) ^ (1 / 2 : ℂ))) u₀ :=
        (hg1.neg).add ((hg1.add analyticAt_const).div hρ hρ0)
      have hB : AnalyticAt ℂ (fun u => -((Rk a h k u).2) + (Rk a h k u).2
            / ((bsq (subO1 a (Rk a h k u))) ^ (1 / 2 : ℂ))) u₀ :=
        (hg2.neg).add (hg2.div hρ hρ0)
      have hgoal : (fun u => Rk a h (k + 1) u) = fun u =>
          (-((Rk a h k u).1) + ((Rk a h k u).1 + (((a / 2 : ℝ)) : ℂ))
              / ((bsq (subO1 a (Rk a h k u))) ^ (1 / 2 : ℂ)),
           -((Rk a h k u).2) + (Rk a h k u).2
              / ((bsq (subO1 a (Rk a h k u))) ^ (1 / 2 : ℂ))) := by
        funext u
        rw [Rk_succ, invBranch]
        simp only [subO1, bsq, if_true, bsq, one_mul]
      rw [hgoal]
      exact hA.prod hB

end

end Work.EQ
