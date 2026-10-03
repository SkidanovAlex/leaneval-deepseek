import Mathlib
import Submission.Work.Analysis.Variation.Defs
import ChallengeDeps

namespace Work.Analysis.Variation

open scoped BigOperators ENNReal NNReal

/-- The variation part of the challenge's variational norm, isolated: the supremum over the
number of jumps `J` and the monotone index map `N` of the `ℓ^r` norm of the successive
differences of `a` along `N`. -/
private noncomputable def varPartK (r : NNReal) (a : ℕ → ℂ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
    ENNReal.ofReal ‖(WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i)))‖

/-- `variationalNorm` is the sum of the supremum norm and its variation part. -/
private theorem variationalNorm_eq_add' (r : NNReal) (a : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r a = (⨆ n, ‖a n‖ₑ) + varPartK r a := rfl

/-- **The `ℓ^r` norm of `WithLp.toLp` in terms of extended norms.**  For `1 ≤ r`, the norm of the
element of `ℓ^r` attached to `F : Fin J → ℂ` is `(∑ i, ‖F i‖ ^ r) ^ (1/r)`, and rewriting the real
norm inside `ENNReal.ofReal` as an extended norm gives exactly the sum appearing in `Vr`. -/
private theorem ofReal_norm_toLp_eq_sum (r : NNReal) (hr : 1 ≤ r) {J : ℕ} (F : Fin J → ℂ) :
    ENNReal.ofReal ‖WithLp.toLp r F‖ = (∑ i : Fin J, ‖F i‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)
  have hrt : ((r : ℝ≥0∞)).toReal = (r : ℝ) := ENNReal.coe_toReal r
  have hp : 0 < ((r : ℝ≥0∞)).toReal := by rw [hrt]; linarith
  rw [PiLp.norm_eq_sum (p := (r : ℝ≥0∞)) hp]
  rw [hrt]
  rw [← ENNReal.ofReal_rpow_of_nonneg
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (by positivity)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (le_of_lt hr0), ofReal_norm])

/-- The truncated `r`-variation is monotone in the truncation parameter. -/
private theorem Vr_mono {r : ℝ} {K K' : ℕ} (h : K ≤ K') (a : ℕ → ℂ) :
    Vr r K a ≤ Vr r K' a := by
  refine iSup_le fun J => iSup_le fun u => iSup_le fun hu => iSup_le fun h0 => iSup_le fun hK => ?_
  exact le_iSup_of_le J (le_iSup_of_le u (le_iSup_of_le hu (le_iSup_of_le h0
    (le_iSup_of_le (fun i => le_trans (hK i) h) le_rfl))))

/-- Prepend `0` to a sequence: `prependZero N 0 = 0` and `prependZero N (j + 1) = N j`. -/
private noncomputable def prependZero (N : ℕ → ℕ) : ℕ → ℕ := fun j => if j = 0 then 0 else N (j - 1)

private lemma prependZero_zero (N : ℕ → ℕ) : prependZero N 0 = 0 := by simp [prependZero]

private lemma prependZero_succ (N : ℕ → ℕ) (j : ℕ) : prependZero N (j + 1) = N j := by
  simp [prependZero]

private lemma monotone_prependZero {N : ℕ → ℕ} (hN : Monotone N) : Monotone (prependZero N) := by
  intro i j hij
  rcases j with _ | j
  · have : i = 0 := Nat.eq_zero_of_le_zero hij
    subst this; simp [prependZero_zero]
  · rcases i with _ | i
    · exact zero_le
    · rw [prependZero_succ, prependZero_succ]
      exact hN (Nat.succ_le_succ_iff.mp hij)

/-- Prepending `0` to the chain `N 0 ≤ ⋯ ≤ N J` adds one nonnegative jump, so the `ℓ^r` sum of
the jumps of `N` is dominated by that of `0, N 0, …, N J`. -/
private theorem sum_fin_le_sum_fin_prependZero (r : ℝ) {J : ℕ} (N : ℕ → ℕ) (a : ℕ → ℂ) :
    (∑ i : Fin J, ‖a (N (↑i + 1)) - a (N ↑i)‖ₑ ^ r)
      ≤ ∑ j : Fin (J + 1), ‖a (prependZero N (↑j + 1)) - a (prependZero N ↑j)‖ₑ ^ r := by
  rw [Fin.sum_univ_eq_sum_range (f := fun i => ‖a (N (i + 1)) - a (N i)‖ₑ ^ r) (n := J)]
  rw [Fin.sum_univ_eq_sum_range
    (f := fun j => ‖a (prependZero N (j + 1)) - a (prependZero N j)‖ₑ ^ r) (n := J + 1)]
  rw [Finset.sum_range_succ']
  refine le_trans (le_of_eq ?_) (le_add_of_nonneg_right (zero_le))
  exact Finset.sum_congr rfl fun j _ => by
    rw [prependZero_succ N (j + 1), prependZero_succ N j]

/-- Each term of `Vr r K a` (a chain anchored at `0` and bounded by `K`) is a term of the free
variation `varPartK r a`, by extending the chain `u` to a map `ℕ → ℕ`. -/
private theorem Vr_le_varPartK (r : NNReal) (hr : 1 ≤ r) (a : ℕ → ℂ) (K : ℕ) :
    Vr (r : ℝ) K a ≤ varPartK r a := by
  refine iSup_le fun J => iSup_le fun u => iSup_le fun hu => iSup_le fun h0 => iSup_le fun hK => ?_
  set N : ℕ → ℕ := fun n => u ⟨min n J, Nat.lt_succ_of_le (min_le_right n J)⟩ with hN
  have hmonoN : Monotone N := by
    intro n m hnm
    rw [hN]
    exact hu (by rw [Fin.le_def]; exact min_le_min hnm le_rfl)
  have hsum : (∑ j : Fin J, ‖a (u j.succ) - a (u j.castSucc)‖ₑ ^ (r : ℝ))
      = ∑ j : Fin J, ‖a (N (↑j + 1)) - a (N ↑j)‖ₑ ^ (r : ℝ) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : N (↑j + 1) = u j.succ := by
      rw [hN]
      refine congrArg u (Fin.ext ?_)
      simp only [Fin.val_succ]
      exact min_eq_left (Nat.succ_le_of_lt j.2)
    have h2 : N ↑j = u j.castSucc := by
      rw [hN]
      refine congrArg u (Fin.ext ?_)
      simp only [Fin.val_castSucc]
      exact min_eq_left (le_of_lt j.2)
    rw [h1, h2]
  calc (∑ j : Fin J, ‖a (u j.succ) - a (u j.castSucc)‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ))
      = (∑ j : Fin J, ‖a (N (↑j + 1)) - a (N ↑j)‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) := by rw [hsum]
    _ = ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J ↦ a (N (i + 1)) - a (N i))‖ :=
        (ofReal_norm_toLp_eq_sum r hr (fun i : Fin J ↦ a (N (i + 1)) - a (N i))).symm
    _ ≤ varPartK r a := le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hmonoN le_rfl))

/-- Conversely, each term of the free variation `varPartK r a` is dominated by a term of
`Vr r (N J) a`, by prepending `0` to the chain `N 0 ≤ ⋯ ≤ N J`. -/
private theorem varPartK_le_iSup_Vr (r : NNReal) (hr : 1 ≤ r) (a : ℕ → ℂ) :
    varPartK r a ≤ ⨆ K : ℕ, Vr (r : ℝ) K a := by
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  set u : Fin (J + 2) → ℕ := fun i => prependZero N ↑i with hu
  have hmono : Monotone u := by
    intro i j hij
    rw [hu]
    exact monotone_prependZero hN (by simpa only [Fin.le_def] using hij)
  have hu0 : u 0 = 0 := by simp [hu, prependZero]
  have huK : ∀ i : Fin (J + 2), u i ≤ N J := by
    intro i
    change prependZero N ↑i ≤ N J
    rcases Nat.eq_zero_or_pos (↑i) with hi | hi
    · rw [hi]; simp [prependZero]
    · obtain ⟨i', hi'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi)
      have hi'' : i' ≤ J := by
        have : ↑i ≤ J + 1 := Nat.lt_succ_iff.mp i.2
        omega
      rw [hi', prependZero_succ]
      exact hN hi''
  have hterm : (∑ i : Fin J, ‖a (N (↑i + 1)) - a (N ↑i)‖ₑ ^ (r : ℝ))
      ≤ ∑ j : Fin (J + 1), ‖a (u j.succ) - a (u j.castSucc)‖ₑ ^ (r : ℝ) := by
    rw [show (∑ j : Fin (J + 1), ‖a (u j.succ) - a (u j.castSucc)‖ₑ ^ (r : ℝ))
        = ∑ j : Fin (J + 1),
            ‖a (prependZero N (↑j + 1)) - a (prependZero N ↑j)‖ₑ ^ (r : ℝ) from
      Finset.sum_congr rfl (fun j _ => by
        simp only [hu, Fin.val_succ, Fin.val_castSucc])]
    exact sum_fin_le_sum_fin_prependZero (r : ℝ) N a
  calc ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J ↦ a (N (i + 1)) - a (N i))‖
      = (∑ i : Fin J, ‖a (N (↑i + 1)) - a (N ↑i)‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) :=
        ofReal_norm_toLp_eq_sum r hr _
    _ ≤ (∑ j : Fin (J + 1), ‖a (u j.succ) - a (u j.castSucc)‖ₑ ^ (r : ℝ)) ^ (1 / (r : ℝ)) :=
        ENNReal.rpow_le_rpow hterm (by positivity)
    _ ≤ Vr (r : ℝ) (N J) a :=
        le_iSup_of_le (J + 1) (le_iSup_of_le u (le_iSup_of_le hmono
          (le_iSup_of_le hu0 (le_iSup_of_le huK le_rfl))))
    _ ≤ ⨆ K : ℕ, Vr (r : ℝ) K a := le_iSup (fun K : ℕ => Vr (r : ℝ) K a) (N J)

/-- For monotone sequences in `ℝ≥0∞`, the supremum of the sums is the sum of the suprema. -/
private theorem iSup_add_monotone {a b : ℕ → ℝ≥0∞} (ha : Monotone a) (hb : Monotone b) :
    (⨆ n, a n + b n) = (⨆ n, a n) + (⨆ n, b n) := by
  have h2 : (⨆ n, a n) + (⨆ m, b m) = ⨆ n, ⨆ m, (a n + b m) := by
    rw [ENNReal.iSup_add]
    refine iSup_congr fun n => ?_
    rw [add_comm (a n), ENNReal.iSup_add]
    exact iSup_congr fun m => add_comm _ _
  refine le_antisymm (iSup_le fun n => add_le_add (le_iSup a n) (le_iSup b n)) ?_
  calc (⨆ n, a n) + (⨆ m, b m) = ⨆ n, ⨆ m, (a n + b m) := h2
    _ ≤ ⨆ n, (a n + b n) := iSup_le fun n => iSup_le fun m => by
        rcases le_total n m with h | h
        · exact le_trans (add_le_add_left (ha h) _) (le_iSup (fun k => a k + b k) m)
        · exact le_trans (add_le_add_right (hb h) _) (le_iSup (fun k => a k + b k) n)

/-- **Bridge to the challenge's `variationalNorm`.**  The variational norm of the challenge
(`PointwiseErgodicTheorems.variationalNorm`, `ChallengeDeps.lean`), the sum of the supremum norm
and the `r`-variation of the whole sequence, is the supremum over `K` of the *truncated* full
variation `VrFull r K a = (⨆_{k ≤ K} ‖a k‖) + Vr r K a`:
`PointwiseErgodicTheorems.variationalNorm r a = ⨆ K, VrFull (r : ℝ) K a` for `r ≥ 1`.
Proof: `variationalNorm` is the sum of two suprema.
* The supremum part `⨆ n ‖a n‖ₑ` is `⨆ K ⨆_{k < K+1} ‖a k‖ₑ` (an `iSup` over `ℕ` written as an
  increasing `iSup` over `Fin (K+1)`).
* The variation part is a supremum over `(J : ℕ)` and monotone `N : ℕ → ℕ` of
  `ENNReal.ofReal ‖WithLp.toLp r (fun i : Fin J => a (N (i+1)) - a (N i))‖`; the `ℓ^r` norm of
  `WithLp.toLp` is `(∑ i, ‖·‖ ^ r) ^ (1/r)` (`PiLp.norm_eq_sum`, `PiLp` being an abbreviation of
  `WithLp`), giving the same form as the terms of `Vr`.  For the two inequalities: (≤) given a
  monotone `N`, prepend `0` to the chain `N 0 ≤ … ≤ N J`: the chain `0, N 0, …, N J` is a
  `Fin (J+2)`-chain of `Vr` with `K := N J`, and the extra jump `a (N 0) - a 0` only adds a
  nonnegative term; (≥) given a monotone `u : Fin (J+1) → ℕ` with `u i ≤ K`, use the monotone
  extension `N i := u (min i J)`, which reproduces all `J` jumps exactly.  Finally
  `⨆ K (S_K + V_K) = (⨆ K S_K) + (⨆ K V_K)` because both `K ↦ S_K` and `K ↦ V_K` are monotone
  (`iSup_add_monotone` in `Submission/VarClamp.lean`, or by hand). -/
theorem variationalNorm_eq_iSup_VrFull (r : NNReal) (hr : 1 ≤ r) (a : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r a = ⨆ K : ℕ, VrFull (r : ℝ) K a := by
  have hmain : PointwiseErgodicTheorems.variationalNorm r a = (⨆ n, ‖a n‖ₑ) + varPartK r a :=
    variationalNorm_eq_add' r a
  have hS : (⨆ K : ℕ, ⨆ k : Fin (K + 1), ‖a k‖ₑ) = ⨆ n, ‖a n‖ₑ := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun K => iSup_le fun k => le_iSup (fun n => ‖a n‖ₑ) (↑k)
    · refine iSup_le fun n => ?_
      exact le_trans (le_iSup (fun k : Fin (n + 1) => ‖a k‖ₑ) ⟨n, Nat.lt_succ_self n⟩)
        (le_iSup (fun K => ⨆ k : Fin (K + 1), ‖a k‖ₑ) n)
  have hmonoS : Monotone fun K : ℕ => (⨆ k : Fin (K + 1), ‖a k‖ₑ) := by
    intro K K' h
    refine iSup_le fun k => le_iSup (fun k' : Fin (K' + 1) => ‖a k'‖ₑ) ⟨↑k, by omega⟩
  have hV : (⨆ K : ℕ, Vr (r : ℝ) K a) = varPartK r a :=
    le_antisymm (iSup_le (Vr_le_varPartK r hr a)) (varPartK_le_iSup_Vr r hr a)
  have hmonoV : Monotone fun K : ℕ => Vr (r : ℝ) K a := fun K K' h => Vr_mono h a
  rw [hmain, ← hS, ← hV, ← iSup_add_monotone hmonoS hmonoV]
  rfl

end Work.Analysis.Variation
