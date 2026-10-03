import Mathlib
import Submission.Work.BourgainPlan.Maximal.kmsz_major_defs

namespace Work.BourgainPlan.IonescuWainger

open Filter

/-- **Lower semicontinuity of the `ρ`-variation** along pointwise convergence of sequences: for
`ρ > 0`, if `A j → B` pointwise then `V^ρ_{n ≥ κ}(B) ≤ liminf_j V^ρ_{n ≥ κ}(A j)`.

This is the `ρ`-general version of `Work.BourgainPlan.IonescuWainger.varRhoFrom_two_le_liminf`
(the case `ρ = 2`), obtained by the same argument: a fixed admissible chain contributes the
continuous function `a ↦ ofReal (chainLp ρ J a t)` of the (finitely many relevant) coordinates, and
the `ρ`-variation is the supremum over all chains. -/
theorem varRhoFrom_r_le_liminf {ρ : ℝ} (hρ : 0 < ρ) (κ : ℕ) (B : ℕ → ℂ) (A : ℕ → ℕ → ℂ)
    (hconv : ∀ n : ℕ, Filter.Tendsto (fun j : ℕ => A j n) Filter.atTop (nhds (B n))) :
    Work.BourgainPlan.Maximal.varRhoFrom ρ κ B
      ≤ Filter.liminf (fun j : ℕ => Work.BourgainPlan.Maximal.varRhoFrom ρ κ (A j)) Filter.atTop := by
  -- Write the left-hand side as a supremum over admissible chains.
  refine iSup_le fun hi => iSup_le fun J => iSup_le fun t => iSup_le fun ht
    => iSup_le fun hb => ?_
  -- For a fixed chain, the `ℓ^ρ`-length is a continuous function of the sequence.
  have hsum : Filter.Tendsto (fun j : ℕ => ∑ i ∈ Finset.range J,
      ‖A j (t (i + 1)) - A j (t i)‖ ^ ρ) Filter.atTop
      (nhds (∑ i ∈ Finset.range J, ‖B (t (i + 1)) - B (t i)‖ ^ ρ)) := by
    refine tendsto_finsetSum _ (fun i _ => ?_)
    have h1 : Filter.Tendsto (fun j : ℕ => ‖A j (t (i + 1)) - A j (t i)‖) Filter.atTop
        (nhds (‖B (t (i + 1)) - B (t i)‖)) :=
      ((hconv (t (i + 1))).sub (hconv (t i))).norm
    exact h1.rpow_const (Or.inr hρ.le)
  have hchain : Filter.Tendsto
      (fun j : ℕ => ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp ρ J (A j) t)) Filter.atTop
      (nhds (ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp ρ J B t))) := by
    simpa only [Work.BourgainPlan.Maximal.chainLp, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (hsum.rpow_const (Or.inr (by positivity : (0 : ℝ) ≤ 1 / ρ)))
  -- Hence the fixed chain is bounded by the `liminf` of the variations.
  rw [← hchain.liminf_eq]
  refine (Filter.le_liminf_iff).mpr (fun y hy => ?_)
  rw [hchain.liminf_eq] at hy
  filter_upwards [(tendsto_order.1 hchain).1 _ hy] with n hn
  exact hn.trans_le (le_iSup_of_le hi (le_iSup_of_le J (le_iSup_of_le t
    (le_iSup_of_le ht (le_iSup_of_le hb le_rfl)))))

end Work.BourgainPlan.IonescuWainger
