import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs

namespace Work.KMTAreas.A7HiRep

open scoped ENNReal NNReal BigOperators

/-- **Subadditivity of the chain part** in the walk: for `1 ≤ r` and walks `a b : ℕ → ℂ`,

  `chainPart r (a + b) ≤ chainPart r a + chainPart r b`.

(For a fixed chain the jumps of `a + b` are the sums of the jumps of `a` and of `b`; the `ℓ^r`
triangle inequality and `iSup` bookkeeping finish.) -/
theorem chainPartSubAdd (r : NNReal) (hr : 1 ≤ r) (a b : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.chainPart r (a + b)
      ≤ Work.KMTAreas.A7Hi.chainPart r a + Work.KMTAreas.A7Hi.chainPart r b := by
  -- `1 ≤ r` makes `WithLp r` a normed group, so the `ℓ^r`-norm is subadditive.
  haveI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  rw [Work.KMTAreas.A7Hi.chainPart]
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  -- The jump vector of `a + b` along the chain `N` is the sum of the jump vectors of `a` and `b`.
  have hvec : (fun i : Fin J => (a + b) (N ((i : ℕ) + 1)) - (a + b) (N (i : ℕ)))
      = (fun i : Fin J => a (N ((i : ℕ) + 1)) - a (N (i : ℕ)))
        + (fun i : Fin J => b (N ((i : ℕ) + 1)) - b (N (i : ℕ))) := by
    funext i
    simp only [Pi.add_apply]
    ring
  rw [hvec, WithLp.toLp_add]
  set u : WithLp (r : ℝ≥0∞) (Fin J → ℂ) :=
    WithLp.toLp r (fun i : Fin J => a (N ((i : ℕ) + 1)) - a (N (i : ℕ))) with hu
  set v : WithLp (r : ℝ≥0∞) (Fin J → ℂ) :=
    WithLp.toLp r (fun i : Fin J => b (N ((i : ℕ) + 1)) - b (N (i : ℕ))) with hv
  have hu_le : ENNReal.ofReal ‖u‖ ≤ Work.KMTAreas.A7Hi.chainPart r a := by
    rw [hu]
    exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))
  have hv_le : ENNReal.ofReal ‖v‖ ≤ Work.KMTAreas.A7Hi.chainPart r b := by
    rw [hv]
    exact le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl))
  have h1 : ENNReal.ofReal ‖u + v‖ ≤ ENNReal.ofReal ‖u‖ + ENNReal.ofReal ‖v‖ := by
    refine (ENNReal.ofReal_le_ofReal (norm_add_le u v)).trans (le_of_eq ?_)
    exact ENNReal.ofReal_add (norm_nonneg u) (norm_nonneg v)
  exact h1.trans (add_le_add hu_le hv_le)

end Work.KMTAreas.A7HiRep
