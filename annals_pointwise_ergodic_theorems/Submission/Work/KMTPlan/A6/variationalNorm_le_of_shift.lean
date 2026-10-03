import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallDefs

/-!
# The variational norm of a sequence differing from another at the first term

If `u'` vanishes at `0` and `u` agrees with `u'` at every index `≥ 1`, then `u` is obtained from
`u'` by adding the "spike" `w = Pi.single 0 (u 0)`.  Since the `r`-variational norm (`r ≥ 1`) is
subadditive (`Submission.PointwiseErgodicTheorems.variationalNorm_add_le`), it suffices to bound
the variational norm of that spike.

Writing `w = Pi.single 0 (u 0)`:
* the sup term `⨆ n ‖w n‖ₑ` is `‖u 0‖ₑ`;
* for a chain `N` the jump vector `i ↦ w (N (i+1)) - w (N i)` has *at most one* nonzero entry
  (a nonzero jump forces `N i = 0 < N (i+1)`, and by monotonicity of `N` there is at most one such
  index), and every entry is `0` or `-(u 0)`; hence its `ℓ^r` norm is at most `‖u 0‖`
  (`ofReal_norm_toLp_le_of_spike`).

So `‖w‖_{V^r} ≤ 2‖u 0‖`, and the claim follows.
-/

namespace Work.KMTPlan.A6

open scoped ENNReal NNReal

set_option linter.style.haveILetI false

/-- A vector `F : Fin J → ℂ` all of whose entries are `0` or `c`, and with at most one nonzero
entry, has `ℓ^r`-norm (for `1 ≤ r`) at most `‖c‖`. -/
lemma ofReal_norm_toLp_le_of_spike {r : NNReal} (hr : 1 ≤ r) {J : ℕ} (F : Fin J → ℂ) (c : ℂ)
    (hval : ∀ i, F i = 0 ∨ F i = c) (huniq : ∀ i j, F i ≠ 0 → F j ≠ 0 → i = j) :
    ENNReal.ofReal ‖WithLp.toLp r F‖ ≤ ENNReal.ofReal ‖c‖ := by
  classical
  haveI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  by_cases hex : ∃ i, F i ≠ 0
  · obtain ⟨i₀, hi₀⟩ := hex
    have hF : F = Pi.single i₀ (F i₀) := by
      funext j
      rcases eq_or_ne j i₀ with hj | hj
      · rw [hj, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hj]
        by_contra hne
        exact hj (huniq j i₀ hne hi₀)
    have hF' : WithLp.toLp r F = PiLp.single (r : ℝ≥0∞) i₀ (F i₀) :=
      (congrArg (WithLp.toLp r) hF).trans rfl
    rw [hF', PiLp.norm_single]
    rcases hval i₀ with h | h
    · rw [h]; simp
    · rw [h]
  · have hF : F = 0 := funext fun i => by_contra fun hne => hex ⟨i, hne⟩
    rw [congrArg (WithLp.toLp r) hF, WithLp.toLp_zero]
    simp

theorem variationalNorm_le_of_shift (r : NNReal) (hr : 1 ≤ r) (u u' : ℕ → ℂ)
    (h0 : u' 0 = 0) (h : ∀ n : ℕ, 1 ≤ n → u n = u' n) :
    PointwiseErgodicTheorems.variationalNorm r u
      ≤ PointwiseErgodicTheorems.variationalNorm r u' + 2 * ENNReal.ofReal ‖u 0‖ := by
  set w : ℕ → ℂ := Pi.single 0 (u 0) with hw
  have hw0 : w 0 = u 0 := by rw [hw, Pi.single_eq_same]
  have hwn : ∀ n : ℕ, 1 ≤ n → w n = 0 := by
    intro n hn
    rw [hw, Pi.single_eq_of_ne (Nat.one_le_iff_ne_zero.mp hn)]
  have huw : u = u' + w := by
    funext n
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      rw [Pi.add_apply, hw0, h0, zero_add]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      rw [Pi.add_apply, hwn n hn1, h n hn1, add_zero]
  have hwbound : PointwiseErgodicTheorems.variationalNorm r w ≤ 2 * ENNReal.ofReal ‖u 0‖ := by
    rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
    have hsup : (⨆ n, ‖w n‖ₑ) ≤ ENNReal.ofReal ‖u 0‖ := by
      refine iSup_le fun n => ?_
      rcases eq_or_ne n 0 with hn | hn
      · subst hn
        rw [hw0]
        exact le_of_eq (ofReal_norm (u 0)).symm
      · rw [hwn n (Nat.one_le_iff_ne_zero.mpr hn), enorm_zero]
        simp
    have hvar : Submission.PointwiseErgodicTheorems.varPart r w ≤ ENNReal.ofReal ‖u 0‖ := by
      refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
      have hval : ∀ i : Fin J,
          (w (N (i + 1)) - w (N i)) = 0 ∨ (w (N (i + 1)) - w (N i)) = -(u 0) := by
        intro i
        rcases eq_or_ne (N i) 0 with hni | hni
        · rcases eq_or_ne (N (i + 1)) 0 with hni1 | hni1
          · left; rw [hni1, hni, hw0]; ring
          · right; rw [hni, hw0, hwn (N (i + 1)) (Nat.one_le_iff_ne_zero.mpr hni1)]; ring
        · left
          have h1 : 1 ≤ N i := Nat.one_le_iff_ne_zero.mpr hni
          have h2 : 1 ≤ N (i + 1) := le_trans h1 (hN (Nat.le_succ (i : ℕ)))
          rw [hwn (N i) h1, hwn (N (i + 1)) h2]; ring
      have huniq : ∀ i j : Fin J,
          (w (N (i + 1)) - w (N i)) ≠ 0 → (w (N (j + 1)) - w (N j)) ≠ 0 → i = j := by
        intro i j hi hj
        have key : ∀ k : Fin J, (w (N (k + 1)) - w (N k)) ≠ 0 → N k = 0 ∧ 1 ≤ N (k + 1) := by
          intro k hk
          rcases eq_or_ne (N k) 0 with hnk | hnk
          · refine ⟨hnk, ?_⟩
            rcases eq_or_ne (N (k + 1)) 0 with hnk1 | hnk1
            · exact absurd (by rw [hnk1, hnk, hw0]; ring) hk
            · exact Nat.one_le_iff_ne_zero.mpr hnk1
          · have h1 : 1 ≤ N k := Nat.one_le_iff_ne_zero.mpr hnk
            have h2 : 1 ≤ N (k + 1) := le_trans h1 (hN (Nat.le_succ (k : ℕ)))
            exact absurd (by rw [hwn (N k) h1, hwn (N (k + 1)) h2]; ring) hk
        obtain ⟨hi0, hi1⟩ := key i hi
        obtain ⟨hj0, hj1⟩ := key j hj
        by_contra hij
        have hne : (i : ℕ) ≠ (j : ℕ) := fun hh => hij (Fin.ext hh)
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have hle : (i : ℕ) + 1 ≤ (j : ℕ) := by omega
          have hmono := hN hle
          omega
        · have hle : (j : ℕ) + 1 ≤ (i : ℕ) := by omega
          have hmono := hN hle
          omega
      have hspike := ofReal_norm_toLp_le_of_spike hr (fun i : Fin J => w (N (i + 1)) - w (N i))
        (-(u 0)) hval huniq
      simpa using hspike
    calc (⨆ n, ‖w n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r w
        ≤ ENNReal.ofReal ‖u 0‖ + ENNReal.ofReal ‖u 0‖ := add_le_add hsup hvar
      _ = 2 * ENNReal.ofReal ‖u 0‖ := by rw [two_mul]
  calc PointwiseErgodicTheorems.variationalNorm r u
      = PointwiseErgodicTheorems.variationalNorm r (u' + w) := by rw [huw]
    _ ≤ PointwiseErgodicTheorems.variationalNorm r u' + PointwiseErgodicTheorems.variationalNorm r w :=
        Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr u' w
    _ ≤ PointwiseErgodicTheorems.variationalNorm r u' + 2 * ENNReal.ofReal ‖u 0‖ :=
        add_le_add_right hwbound _

end Work.KMTPlan.A6
