/-
# The clamped variation is dominated by the variation part (area A8)

`Work.KMTAreas.varK r K a` is the *clamped* `r`-variation of `a : ℕ → ℂ`: the maximum, over all
monotone chains `w : Fin (J+1) → Fin (K+1)` (`J ≤ K`), of
`(∑_{i<J} ‖a (w (i+1)) - a (w i)‖^r)^{1/r}`;
`Work.KMTAreas.A8.varPart r a` is the variation part of the challenge's variational norm,
`⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N), ofReal ‖WithLp.toLp r (fun i : Fin J ↦ a (N (i+1)) - a (N i))‖`
(its second summand, `Work.KMTAreas.A8.variationalNorm_eq_add`).

The content of this file is that the clamped quantity is dominated by the unclamped one:
`ENNReal.ofReal (varK r K a) ≤ varPart r a` for `1 ≤ r`.

Two ingredients:
* `exists_monotone_extend`: a monotone chain `w : Fin (J+1) → ℕ` extends to a monotone
  `N : ℕ → ℕ` agreeing with it on `Fin (J+1)`; so every clamped chain occurs in the supremum
  defining `varPart`;
* `ofReal_sum_rpow_eq_ofReal_norm_toLp`: the `rpow`-sum form of the clamped value is the
  `ℓ^r`-norm form used in `varPart` (combining `Work.KMTAreas.A8.ofReal_norm_toLp_eq_sum` with
  the `ENNReal.ofReal` arithmetic for sums and `rpow`s).
-/
import Mathlib
import Submission.Work.KMTAreas.A8.vNormK_defs

set_option autoImplicit false

namespace Work.KMTAreas.A8

open scoped BigOperators ENNReal NNReal

/-- The `rpow`-sum form of the clamped variation is the `WithLp` norm form appearing in the
challenge's variational norm: for `1 ≤ r` and `x : Fin J → ℂ`,
`ofReal ((∑ i, ‖x i‖^r)^{1/r}) = ofReal ‖WithLp.toLp r x‖`. -/
theorem ofReal_sum_rpow_eq_ofReal_norm_toLp {J : ℕ} {r : ℝ≥0} (hr : 1 ≤ r) (x : Fin J → ℂ) :
    ENNReal.ofReal ((∑ i : Fin J, ‖x i‖ ^ (r : ℝ)) ^ (1 / (r : ℝ)))
      = ENNReal.ofReal ‖WithLp.toLp r x‖ := by
  rw [ofReal_norm_toLp_eq_sum hr x]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)
  have hsum : 0 ≤ ∑ i : Fin J, ‖x i‖ ^ (r : ℝ) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  rw [← ENNReal.ofReal_rpow_of_nonneg hsum (by positivity : (0:ℝ) ≤ 1/(r:ℝ))]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (le_of_lt hr0), ofReal_norm]

/-- A monotone chain `w : Fin (J+1) → ℕ` extends to a monotone `N : ℕ → ℕ` with the same values:
`N k = w (min k J)`.  In particular the increments along `w` occur among the increments along
`N`, so `w` is admissible in the supremum defining `varPart`. -/
theorem exists_monotone_extend {J : ℕ} (w : Fin (J+1) → ℕ) (hw : Monotone w) :
    ∃ N : ℕ → ℕ, Monotone N ∧ ∀ i : Fin J, N i = w i.castSucc ∧ N (i+1) = w i.succ := by
  let N : ℕ → ℕ := fun k => w ⟨min k J, Nat.lt_succ_of_le (min_le_right k J)⟩
  have hN1 : ∀ i : Fin J, N i = w i.castSucc := by
    intro i
    dsimp only [N]
    congr 1
    exact Fin.ext (by simp)
  have hN2 : ∀ i : Fin J, N (i+1) = w i.succ := by
    intro i
    dsimp only [N]
    congr 1
    exact Fin.ext (by simp)
  exact ⟨N, fun k k' hkk => hw (min_le_min hkk le_rfl), fun i => ⟨hN1 i, hN2 i⟩⟩

theorem varK_le_varPart (r : NNReal) (hr : 1 ≤ r) (a : ℕ → ℂ) (K : ℕ) :
    ENNReal.ofReal (Work.KMTAreas.varK r K a) ≤ Work.KMTAreas.A8.varPart r a := by
  classical
  -- the clamped variation is a maximum over chains, so it is attained at some chain `p`
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Work.KMTAreas.Chain K)))
    Finset.univ_nonempty (fun p : Work.KMTAreas.Chain K =>
      (∑ i : Fin p.1.1, ‖a (p.2.1 i.succ) - a (p.2.1 i.castSucc)‖ ^ (r : ℝ)) ^ (1 / (r : ℝ)))
  set J : ℕ := p.1.1 with hJ
  set w : Fin (J+1) → ℕ := fun t => (p.2.1 t : ℕ) with hw
  have hwmono : Monotone w := fun t t' h => p.2.2 h
  -- every chain is a restriction of a monotone `N : ℕ → ℕ`
  obtain ⟨N, hNmono, hN⟩ := exists_monotone_extend w hwmono
  have hvec : (fun i : Fin J => a (N (i+1)) - a (N i))
      = fun i : Fin J => a (p.2.1 i.succ) - a (p.2.1 i.castSucc) := by
    funext i
    rw [(hN i).2, (hN i).1]
  rw [Work.KMTAreas.varK, hp]
  calc ENNReal.ofReal ((∑ i : Fin J, ‖a (p.2.1 i.succ) - a (p.2.1 i.castSucc)‖ ^ (r : ℝ)) ^ (1/(r:ℝ)))
      = ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => a (N (i+1)) - a (N i))‖ := by
        rw [hvec, ofReal_sum_rpow_eq_ofReal_norm_toLp hr]
    _ ≤ varPart r a := by
        rw [Work.KMTAreas.A8.varPart]
        refine le_iSup_of_le J ?_
        refine le_iSup_of_le N ?_
        exact le_iSup (fun _ : Monotone N => ENNReal.ofReal ‖WithLp.toLp r
          (fun i : Fin J => a (N (i+1)) - a (N i))‖) hNmono

end Work.KMTAreas.A8
