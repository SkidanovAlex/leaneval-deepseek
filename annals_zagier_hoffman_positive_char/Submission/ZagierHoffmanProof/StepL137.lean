import Submission.ZagierHoffmanProof.StepL136
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L137: the G5 u-values TAIL branch (SESSION 259g)

The `k−1 ≤ m` half of the count-(k−1) analogue of `g5c1_u_cA_values`: the
iterated leading member's tail entries equal s's.  All intermediates are stated
over `R0.cA u` with `hdepu`-typed indices (the elaboration trap of SESSION 259f:
`(toData F R0).cA u` rejects `u : R0.ιA`, since the ιA equality is only
definitional); `hstep`'s RHS is the `hc0`-LHS form, so `rw [hstep, hb]` needs no
`congr` block (the Fin indices are defeq by proof irrelevance + val reduction).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The tail branch of the G5 u-values: for `k−1 ≤ m < r` the iterated leading
member's entry is `s⟨m⟩`. -/
lemma maink_g5_u_cA_values_tail (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hdepu : R0.depA u = (r - k) + 1)
    (hc0 : ∀ hd : R0.depA u = (r - k) + 1,
      (fun x : Fin ((r - k) + 1) => R0.cA u (Fin.cast hd.symm x)) =
        bstarBase F r s k hk1 hkr hbig) :
    ∀ (m : ℕ) (hmQ : m < (RelData.BCqIter F (k - 1) (toData F R0)).depA
        (RelData.iterIdx F (k - 1) (toData F R0) u)) (hmr : m < r),
      k - 1 ≤ m →
      (RelData.BCqIter F (k - 1) (toData F R0)).cA
        (RelData.iterIdx F (k - 1) (toData F R0) u) ⟨m, hmQ⟩ = s ⟨m, hmr⟩ := by
  intro m hmQ hmr hm
  have hdep_eq : (RelData.BCqIter F (k - 1) (toData F R0)).depA
      (RelData.iterIdx F (k - 1) (toData F R0) u) = (toData F R0).depA u + (k - 1) :=
    RelData.BCqIter_depA_at F (k - 1) (toData F R0) u
  have hbase : m < (toData F R0).depA u + (k - 1) := by rw [← hdep_eq]; exact hmQ
  have hcv := RelData.BCqIter_cA_value F (k - 1) (toData F R0) u ⟨m, hbase⟩
  have hcast : (Fin.cast (RelData.BCqIter_depA_at F (k - 1) (toData F R0) u).symm
        ⟨m, hbase⟩) = (⟨m, hmQ⟩ : Fin ((RelData.BCqIter F (k - 1) (toData F R0)).depA
          (RelData.iterIdx F (k - 1) (toData F R0) u))) := by
    apply Fin.ext
    simp
  have hjlt : m - (k - 1) < (r - k) + 1 := by omega
  have hstep : (RelData.BCqIter F (k - 1) (toData F R0)).cA
      (RelData.iterIdx F (k - 1) (toData F R0) u) ⟨m, hmQ⟩
      = R0.cA u (Fin.cast hdepu.symm (⟨m - (k - 1), hjlt⟩ : Fin ((r - k) + 1))) := by
    rw [← hcast, hcv]
    rw [dif_neg (by simp only [Fin.val_mk]; omega)]
    rfl
  have hb := congrFun (hc0 hdepu) (⟨m - (k - 1), hjlt⟩ : Fin ((r - k) + 1))
  rw [hstep, hb]
  by_cases hj : m - (k - 1) = 0
  · have hmk : m = k - 1 := by omega
    have hidx : (⟨m - (k - 1), hjlt⟩ : Fin ((r - k) + 1)) = ⟨0, by omega⟩ :=
      Fin.ext (by simp [hj])
    rw [hidx]
    have hbh := bstarBase_head F r s k hk1 hkr hbig
    exact Eq.trans (show (bstarBase F r s k hk1 hkr hbig) ⟨0, by omega⟩
        = s ⟨k - 1, by omega⟩ from hbh)
      (congrArg s (Fin.ext (by simp only [Fin.val_mk]; omega)))
  · obtain ⟨t, ht⟩ : ∃ t, m - (k - 1) = t + 1 := ⟨m - (k - 1) - 1, by omega⟩
    have htlt : t < r - k := by omega
    have hidx : (⟨m - (k - 1), hjlt⟩ : Fin ((r - k) + 1)) = ⟨t + 1, by omega⟩ :=
      Fin.ext (by simp [ht])
    rw [hidx]
    have hbt := bstarBase_tail F r s k hk1 hkr hbig ⟨t, htlt⟩
    refine Eq.trans (show (bstarBase F r s k hk1 hkr hbig) ⟨t + 1, by omega⟩
        = sTail r s k hkr ⟨t, htlt⟩ from hbt) ?_
    refine Eq.trans (show sTail r s k hkr ⟨t, htlt⟩ = s ⟨k + t, by omega⟩ from rfl) ?_
    exact congrArg s (Fin.ext (by simp only [Fin.val_mk]; omega))

/-- ★★ The FULL G5 u-values lemma: the iterated leading member of the G5 chain
equals s entry-for-entry (front branch from StepL136, tail branch above).  This
completes step 2 of the `maink_g5_zeta_core` recipe (PLAN SESSION 259d). -/
lemma maink_g5_u_cA_values (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hdepu : R0.depA u = (r - k) + 1)
    (hc0 : ∀ hd : R0.depA u = (r - k) + 1,
      (fun x : Fin ((r - k) + 1) => R0.cA u (Fin.cast hd.symm x)) =
        bstarBase F r s k hk1 hkr hbig) :
    ∀ (m : ℕ) (hmQ : m < (RelData.BCqIter F (k - 1) (toData F R0)).depA
        (RelData.iterIdx F (k - 1) (toData F R0) u)) (hmr : m < r),
      (RelData.BCqIter F (k - 1) (toData F R0)).cA
        (RelData.iterIdx F (k - 1) (toData F R0) u) ⟨m, hmQ⟩ = s ⟨m, hmr⟩ := by
  intro m hmQ hmr
  by_cases hm : m < k - 1
  · exact maink_g5_u_cA_values_front F r s k hkr hallq R0 u m hmQ hmr hm
  · exact maink_g5_u_cA_values_tail F r s k hk1 hkr hbig R0 u hdepu hc0 m hmQ hmr (by omega)


end ZagierHoffmanPositiveChar
