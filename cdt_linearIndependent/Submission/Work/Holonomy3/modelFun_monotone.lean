import Mathlib
import Submission.Work.Holonomy3.model_deps

namespace Work.Holonomy3

open Set

/-- **Monotonicity from a covering sequence of pieces.**  If `b : ℕ → ℝ` is nondecreasing, its
consecutive pieces `[b n, b (n+1)]` cover the nonnegative half-line, and `f` is nondecreasing on
each piece `[b n, b (n+1)]`, then `f` is nondecreasing on `[0, ∞)`.  (This is the tool used to
assemble the pieces of the model function `modelFun w`.) -/
lemma monotoneOn_Ici_of_cover {f : ℝ → ℝ} {b : ℕ → ℝ}
    (hb_mono : ∀ n, b n ≤ b (n+1))
    (hb_cover : ∀ t : ℝ, 0 ≤ t → ∃ n, b n ≤ t ∧ t ≤ b (n+1))
    (hmono : ∀ n, MonotoneOn f (Set.Icc (b n) (b (n+1)))) :
    MonotoneOn f (Set.Ici 0) := by
  have hbG : Monotone b := monotone_nat_of_le_succ hb_mono
  have hstep : ∀ n, f (b n) ≤ f (b (n+1)) := fun n =>
    hmono n (Set.left_mem_Icc.mpr (hb_mono n)) (Set.right_mem_Icc.mpr (hb_mono n)) (hb_mono n)
  have hG : Monotone (fun k => f (b k)) := monotone_nat_of_le_succ hstep
  intro x hx y hy hxy
  obtain ⟨n, hn1, hn2⟩ := hb_cover x hx
  obtain ⟨m, hm1, hm2⟩ := hb_cover y hy
  rcases lt_trichotomy n m with h | h | h
  · have h1 : f x ≤ f (b (n+1)) := hmono n ⟨hn1, hn2⟩ ⟨hb_mono n, le_rfl⟩ hn2
    have h2 : f (b (n+1)) ≤ f (b m) := hG (Nat.succ_le_of_lt h)
    have h3 : f (b m) ≤ f y := hmono m ⟨le_rfl, hb_mono m⟩ ⟨hm1, hm2⟩ hm1
    exact le_trans h1 (le_trans h2 h3)
  · subst h; exact hmono n ⟨hn1, hn2⟩ ⟨hm1, hm2⟩ hxy
  · have : y = x := le_antisymm (le_trans hm2 (le_trans (hbG (Nat.succ_le_of_lt h)) hn1)) hxy
    rw [this]

/-- The model function of Lemma `lcm-2` (the integrand of the paper's `I_ξ^m(ξ)`), i.e.
`modelFun w t = max (t - w) 0` for `t ≤ 1` and `harmonicFun w t + correctionFun w t` for `t > 1`,
is nondecreasing on `ℝ` when `0 ≤ w`.  (It is in fact continuous: the harmonic step function's
upward jumps at the grid points `1 + kB` are exactly cancelled by the downward jumps of the
correction function, and on each piece `[1+kB, 1+(k+1)B]` it equals
`Σ_{h ≤ k} 1/h + max (t/(k+1) - w) 0`, which is nondecreasing in `t`.) -/
theorem modelFun_monotone {w : ℝ} (hw : 0 ≤ w) :
    Monotone (Submission.CDT.IntegratedLcm.modelFun w) := by
  -- On the first piece `[0, 1]` the model function is `max (t - w) 0`, hence nondecreasing.
  have hpiece0 :
      MonotoneOn (Submission.CDT.IntegratedLcm.modelFun w)
        (Set.Icc (Submission.CDT.IntegratedLcm.modelGrid w 0)
          (Submission.CDT.IntegratedLcm.modelGrid w 1)) := by
    intro t ht u hu htu
    simp only [Submission.CDT.IntegratedLcm.modelGrid_zero,
      Submission.CDT.IntegratedLcm.modelGrid_succ, Nat.cast_zero, zero_mul, add_zero] at ht hu
    rw [Submission.CDT.IntegratedLcm.modelFun_of_le_one w t ht.2,
      Submission.CDT.IntegratedLcm.modelFun_of_le_one w u hu.2]
    exact max_le_max (sub_le_sub_right htu w) le_rfl
  -- On each later piece `[1 + kB, 1 + (k+1)B]` the model function is the nondecreasing
  -- function `Σ_{h ≤ k} 1/h + max (t/(k+1) - w) 0`.
  have hpiece : ∀ n,
      MonotoneOn (Submission.CDT.IntegratedLcm.modelFun w)
        (Set.Icc (Submission.CDT.IntegratedLcm.modelGrid w n)
          (Submission.CDT.IntegratedLcm.modelGrid w (n+1))) := by
    intro n
    match n with
    | 0 => exact hpiece0
    | (k+1) =>
      intro t ht u hu htu
      simp only [Submission.CDT.IntegratedLcm.modelGrid_succ] at ht hu
      push_cast at ht hu
      rw [Submission.CDT.IntegratedLcm.modelFun_eq_piece_closed w k t ht.1 ht.2,
        Submission.CDT.IntegratedLcm.modelFun_eq_piece_closed w k u hu.1 hu.2]
      have hle : t / ((k:ℝ)+1) - w ≤ u / ((k:ℝ)+1) - w :=
        sub_le_sub_right (div_le_div_of_nonneg_right htu (by positivity)) w
      exact add_le_add_right (max_le_max hle (le_refl (0:ℝ)))
        (∑ h ∈ Finset.Icc 1 k, (1:ℝ)/h)
  -- The grid `modelGrid w` covers the nonnegative half-line.
  have hcover : ∀ t : ℝ, 0 ≤ t → ∃ n,
      Submission.CDT.IntegratedLcm.modelGrid w n ≤ t ∧
        t ≤ Submission.CDT.IntegratedLcm.modelGrid w (n+1) := by
    intro t ht
    by_cases h1 : t ≤ 1
    · refine ⟨0, ?_, ?_⟩
      · simpa using ht
      · simpa [Submission.CDT.IntegratedLcm.modelGrid_succ,
          Submission.CDT.IntegratedLcm.modelGrid_zero] using h1
    · have hB : 0 < Submission.CDT.IntegratedLcm.stepB w :=
        Submission.CDT.IntegratedLcm.stepB_pos w
      have hnn : 0 ≤ (t - 1) / Submission.CDT.IntegratedLcm.stepB w :=
        div_nonneg (by linarith) (le_of_lt hB)
      refine ⟨⌊(t - 1) / Submission.CDT.IntegratedLcm.stepB w⌋₊ + 1, ?_, ?_⟩
      · rw [Submission.CDT.IntegratedLcm.modelGrid_succ]
        have h : (⌊(t-1)/Submission.CDT.IntegratedLcm.stepB w⌋₊ : ℝ)
            ≤ (t-1)/Submission.CDT.IntegratedLcm.stepB w := Nat.floor_le hnn
        rw [le_div_iff₀ hB] at h
        linarith
      · rw [Submission.CDT.IntegratedLcm.modelGrid_succ]
        have h : (t-1)/Submission.CDT.IntegratedLcm.stepB w
            < (⌊(t-1)/Submission.CDT.IntegratedLcm.stepB w⌋₊ : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        rw [div_lt_iff₀ hB] at h
        push_cast
        linarith
  have hbmono : ∀ n, Submission.CDT.IntegratedLcm.modelGrid w n ≤
      Submission.CDT.IntegratedLcm.modelGrid w (n+1) :=
    fun n => le_of_lt (Submission.CDT.IntegratedLcm.modelGrid_lt_succ w n)
  have hmonoOn : MonotoneOn (Submission.CDT.IntegratedLcm.modelFun w) (Set.Ici 0) :=
    monotoneOn_Ici_of_cover hbmono hcover hpiece
  intro x y hxy
  rcases le_total y 0 with hy | hy
  · -- both `≤ 1`
    rw [Submission.CDT.IntegratedLcm.modelFun_of_le_one w x (le_trans hxy (le_trans hy (by norm_num))),
      Submission.CDT.IntegratedLcm.modelFun_of_le_one w y (le_trans hy (by norm_num))]
    exact max_le_max (sub_le_sub_right hxy w) le_rfl
  · rcases le_total x 0 with hx | hx
    · -- `x ≤ 0 < y`: the left value vanishes
      rw [Submission.CDT.IntegratedLcm.modelFun_of_le_one w x (le_trans hx (by norm_num))]
      rw [max_eq_right (show x - w ≤ 0 by linarith)]
      exact Submission.CDT.IntegratedLcm.modelFun_nonneg w y
    · -- `0 ≤ x ≤ y`
      exact hmonoOn hx hy hxy

end Work.Holonomy3
