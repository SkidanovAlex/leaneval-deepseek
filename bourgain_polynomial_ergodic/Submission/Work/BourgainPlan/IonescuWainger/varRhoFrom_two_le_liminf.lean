import Mathlib
import Submission.Work.BourgainPlan.Maximal.kmsz_major_defs

namespace Work.BourgainPlan.IonescuWainger

open Filter

-- Route: `varRhoFrom 2 κ B = ⨆ hi, varRho 2 κ hi B = ⨆ (J) (t) (ht) (hb), ofReal (chainLp 2 J B t)`,
-- and for a fixed admissible chain the map `a ↦ ENNReal.ofReal (chainLp 2 J a t)` is continuous
-- (a finite sum of `‖a (t (j+1)) - a (t j)‖ ^ 2`, then `^ (1/2)`), hence
-- `ofReal (chainLp 2 J B t) = lim_j ofReal (chainLp 2 J (A j) t) ≤ liminf_j varRhoFrom 2 κ (A j)`.
-- Supremum over the chains.  The same argument is carried out for a continuous index in
-- `Commons.Analysis.Fourier.variation_liminf_le` (`Submission/Work/Analysis/Fourier/variation_liminf_le.lean`).
theorem varRhoFrom_two_le_liminf (κ : ℕ) (B : ℕ → ℂ) (A : ℕ → ℕ → ℂ)
    (hconv : ∀ n : ℕ, Filter.Tendsto (fun j : ℕ => A j n) Filter.atTop (nhds (B n))) :
    Work.BourgainPlan.Maximal.varRhoFrom 2 κ B
      ≤ Filter.liminf (fun j : ℕ => Work.BourgainPlan.Maximal.varRhoFrom 2 κ (A j)) Filter.atTop := by
  -- Write the left-hand side as a supremum over admissible chains.
  refine iSup_le fun hi => iSup_le fun J => iSup_le fun t => iSup_le fun ht
    => iSup_le fun hb => ?_
  -- For a fixed chain, the `ℓ²`-length is a continuous function of the sequence.
  have hsum : Filter.Tendsto (fun j : ℕ => ∑ i ∈ Finset.range J,
      ‖A j (t (i + 1)) - A j (t i)‖ ^ (2 : ℝ)) Filter.atTop
      (nhds (∑ i ∈ Finset.range J, ‖B (t (i + 1)) - B (t i)‖ ^ (2 : ℝ))) := by
    refine tendsto_finsetSum _ (fun i _ => ?_)
    have h1 : Filter.Tendsto (fun j : ℕ => ‖A j (t (i + 1)) - A j (t i)‖) Filter.atTop
        (nhds (‖B (t (i + 1)) - B (t i)‖)) :=
      ((hconv (t (i + 1))).sub (hconv (t i))).norm
    exact h1.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 2))
  have hchain : Filter.Tendsto
      (fun j : ℕ => ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp 2 J (A j) t)) Filter.atTop
      (nhds (ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp 2 J B t))) := by
    simpa only [Work.BourgainPlan.Maximal.chainLp, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (hsum.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2)))
  -- Hence the fixed chain is bounded by the `liminf` of the variations.
  rw [← hchain.liminf_eq]
  refine (Filter.le_liminf_iff).mpr (fun y hy => ?_)
  rw [hchain.liminf_eq] at hy
  filter_upwards [(tendsto_order.1 hchain).1 _ hy] with n hn
  exact hn.trans_le (le_iSup_of_le hi (le_iSup_of_le J (le_iSup_of_le t
    (le_iSup_of_le ht (le_iSup_of_le hb le_rfl)))))

end Work.BourgainPlan.IonescuWainger
