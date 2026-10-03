import ChallengeDeps
import Mathlib.Tactic
import Submission.Basic

/-!
# Elementary properties of the variational norm

We record the basic algebraic properties of the variational norm
`variationalNorm r a = sup_n ‖a n‖ₑ + V^r(a)` of a sequence `a : ℕ → ℂ`:

* subadditivity `‖a + b‖_{V^r} ≤ ‖a‖_{V^r} + ‖b‖_{V^r}`;
* homogeneity `‖c • a‖_{V^r} = ‖c‖ₑ * ‖a‖_{V^r}`.

These are the standard tools for manipulating variational estimates: splitting an average into
finitely many pieces and rescaling.
-/

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

/-- The "second term" of the variational norm: the supremum over monotone subsequences of the
`ℓ^r` norm of the successive differences. -/
noncomputable def varPart (r : ℝ≥0) (a : ℕ → ℂ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
    ENNReal.ofReal ‖(WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i)))‖

/-- The variational norm is the sum of its two defining suprema. -/
lemma variationalNorm_eq_add (r : ℝ≥0) (a : ℕ → ℂ) :
    variationalNorm r a = (⨆ n, ‖a n‖ₑ) + varPart r a := rfl

lemma varPart_nonneg (r : ℝ≥0) (a : ℕ → ℂ) : 0 ≤ varPart r a := bot_le

/-- The second term of the variational norm is subadditive (for `r ≥ 1`). -/
lemma varPart_add_le {r : ℝ≥0} (hr : 1 ≤ r) (a b : ℕ → ℂ) :
    varPart r (a + b) ≤ varPart r a + varPart r b := by
  haveI : Fact (1 ≤ (↑r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  refine iSup_le (fun J => iSup_le (fun N => iSup_le (fun hN => ?_)))
  have hsplit : WithLp.toLp r (fun (i : Fin J) ↦ (a + b) (N (i + 1)) - (a + b) (N i))
      = WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i))
        + WithLp.toLp r (fun (i : Fin J) ↦ b (N (i + 1)) - b (N i)) := by
    rw [← WithLp.toLp_add]
    congr 1
    funext i
    simp only [Pi.add_apply]
    abel
  rw [hsplit]
  calc ENNReal.ofReal ‖WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i))
          + WithLp.toLp r (fun (i : Fin J) ↦ b (N (i + 1)) - b (N i))‖
      ≤ ENNReal.ofReal (‖WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i))‖
          + ‖WithLp.toLp r (fun (i : Fin J) ↦ b (N (i + 1)) - b (N i))‖) :=
        ENNReal.ofReal_le_ofReal (norm_add_le
          (WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i)))
          (WithLp.toLp r (fun (i : Fin J) ↦ b (N (i + 1)) - b (N i))))
    _ = ENNReal.ofReal ‖WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i))‖
          + ENNReal.ofReal ‖WithLp.toLp r (fun (i : Fin J) ↦ b (N (i + 1)) - b (N i))‖ :=
        ENNReal.ofReal_add
          (norm_nonneg (WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i))))
          (norm_nonneg (WithLp.toLp r (fun (i : Fin J) ↦ b (N (i + 1)) - b (N i))))
    _ ≤ varPart r a + varPart r b := add_le_add
        (le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl)))
        (le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl)))

/-- The second term of the variational norm is homogeneous. -/
lemma varPart_smul {r : ℝ≥0} (hr : 1 ≤ r) (c : ℂ) (a : ℕ → ℂ) :
    varPart r (c • a) = ‖c‖ₑ * varPart r a := by
  haveI : Fact (1 ≤ (↑r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  have hpt : ∀ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
      ENNReal.ofReal ‖WithLp.toLp r (fun (i : Fin J) ↦ (c • a) (N (i + 1)) - (c • a) (N i))‖
        = ‖c‖ₑ * ENNReal.ofReal
            ‖WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i))‖ := by
    intro J N _
    have hv : (fun (i : Fin J) ↦ (c • a) (N (i + 1)) - (c • a) (N i))
        = c • (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i)) := by
      funext i
      simp only [Pi.smul_apply]
      rw [smul_sub]
    rw [hv, WithLp.toLp_smul, norm_smul, ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm]
  have key : (⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
        ENNReal.ofReal ‖WithLp.toLp r (fun (i : Fin J) ↦ (c • a) (N (i + 1)) - (c • a) (N i))‖)
      = (⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
        ‖c‖ₑ * ENNReal.ofReal ‖WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i))‖) :=
    iSup_congr (fun J => iSup_congr (fun N => iSup_congr (fun hN => hpt J N hN)))
  rw [varPart, key, varPart]
  simp_rw [ENNReal.mul_iSup]

/-- The supremum of the norms of a rescaled sequence is rescaled. -/
lemma iSup_enorm_smul (c : ℂ) (a : ℕ → ℂ) :
    (⨆ n, ‖(c • a) n‖ₑ) = ‖c‖ₑ * ⨆ n, ‖a n‖ₑ := by
  have hpt : ∀ n : ℕ, ‖(c • a) n‖ₑ = ‖c‖ₑ * ‖a n‖ₑ := by
    intro n
    rw [Pi.smul_apply, smul_eq_mul, enorm_mul]
  rw [show (⨆ n, ‖(c • a) n‖ₑ) = ⨆ n, ‖c‖ₑ * ‖a n‖ₑ from iSup_congr hpt]
  rw [ENNReal.mul_iSup]

/-- The variational norm is homogeneous (for `r ≥ 1`). -/
lemma variationalNorm_smul {r : ℝ≥0} (hr : 1 ≤ r) (c : ℂ) (a : ℕ → ℂ) :
    variationalNorm r (c • a) = ‖c‖ₑ * variationalNorm r a := by
  rw [variationalNorm_eq_add, variationalNorm_eq_add, varPart_smul hr, iSup_enorm_smul, mul_add]

/-- The supremum part of the variational norm is subadditive. -/
lemma iSup_enorm_add_le (a b : ℕ → ℂ) :
    (⨆ n, ‖(a + b) n‖ₑ) ≤ (⨆ n, ‖a n‖ₑ) + (⨆ n, ‖b n‖ₑ) := by
  refine iSup_le (fun n => ?_)
  calc ‖(a + b) n‖ₑ = ‖a n + b n‖ₑ := by rw [Pi.add_apply]
    _ ≤ ‖a n‖ₑ + ‖b n‖ₑ := enorm_add_le _ _
    _ ≤ (⨆ n, ‖a n‖ₑ) + (⨆ n, ‖b n‖ₑ) := add_le_add (le_iSup (fun n => ‖a n‖ₑ) n) (le_iSup (fun n => ‖b n‖ₑ) n)

/-- The variational norm is subadditive (for `r ≥ 1`). -/
lemma variationalNorm_add_le {r : ℝ≥0} (hr : 1 ≤ r) (a b : ℕ → ℂ) :
    variationalNorm r (a + b) ≤ variationalNorm r a + variationalNorm r b := by
  rw [variationalNorm_eq_add, variationalNorm_eq_add, variationalNorm_eq_add]
  calc (⨆ n, ‖(a + b) n‖ₑ) + varPart r (a + b)
      ≤ ((⨆ n, ‖a n‖ₑ) + (⨆ n, ‖b n‖ₑ)) + (varPart r a + varPart r b) :=
        add_le_add (iSup_enorm_add_le a b) (varPart_add_le hr a b)
    _ = ((⨆ n, ‖a n‖ₑ) + varPart r a) + ((⨆ n, ‖b n‖ₑ) + varPart r b) := by ring

end PointwiseErgodicTheorems
end Submission
