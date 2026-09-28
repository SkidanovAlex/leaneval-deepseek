import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Sig2.ellXY_le_sum
import Submission.Work.HP.Sig2.ellXY_pair_le

/-!
# `Work.HP.MDEstimates.pair_counts_clean`

The pair counts `ℓ_{r,n}(X,Y;Δ) ≪ X^r Y^r Δ^{n-1} (log Δ)^{2 min(r-2,1)}` for all `2 ≤ r`,
proved on top of the `sorry`-free `Work.HP.Sig2` development (which does not depend on the
fragile `Work.HP.window_sum_r2` module).

This mirrors `Work.HP.pair_counts`, but obtains the rank-`2` case from `Sig2.ellXY_pair_le_two`
and the rank-`≥ 3` case by assembling `Sig2.ellXY_le_sum` with the window-sum bound
`Sig2.hws_ge3_of`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.HP.MDEstimates

open Work.HP

/-- Pair counts `ℓ_{r,n}(X,Y;Δ) ≪ X^r Y^r Δ^{n-1} (log Δ)^{2 min(r-2,1)}` for `2 ≤ r`.
Same statement as `Work.HP.pair_counts`, but resting only on the `Sig2` development. -/
theorem pair_counts_clean (n r : ℕ) (hn : 2 ≤ n) (hr : 2 ≤ r) (hrn : r ≤ n + 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ X Y Δ : ℝ, 1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (ellXY n r X Y Δ : ℝ)
        ≤ K * X ^ r * Y ^ r * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1) := by
  rcases eq_or_lt_of_le hr with h2 | h3
  · subst h2
    obtain ⟨K, hK, hK'⟩ := Work.HP.Sig2.ellXY_pair_le_two n hn
    refine ⟨K, hK, ?_⟩
    intro X Y Δ hX hY hΔ
    have h := hK' X Y Δ hX hY hΔ
    have hmin : 2 * min (2 - 2) 1 = 0 := by norm_num
    rw [hmin, pow_zero, mul_one]
    exact h
  · obtain ⟨Kc, hKc, hKc'⟩ := Work.HP.Sig2.schmidt_bound (ι := Fin (n + 1))
    obtain ⟨Kmk0, hKmk0, hmink0⟩ := Work.HP.Sig2.minkowski_prod (ι := Fin (n + 1))
    have hKmink : 1 ≤ max Kmk0 1 := le_max_right _ _
    have hmink : ∀ L : Submodule ℤ (Fin (n + 1) → ℤ),
        (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ max Kmk0 1 * detL L := fun L =>
      le_trans (hmink0 L)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (detL_nonneg L))
    obtain ⟨Knum, hKnum, hnum'⟩ :=
      Work.HP.Sig2.num_lattices_of (ι := Fin (n + 1)) (max Kmk0 1) (by linarith) hmink
    have hnum : ∃ (Knum : ℝ), 0 < Knum ∧ ∀ (s : Fin r → ℝ)
        (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))), (∀ j, 1 ≤ s j) →
        (∀ L ∈ F, IsPrimLat L ∧ rk L = r ∧ ∀ j : Fin r, lam L (j.1 + 1) ≤ s j) →
        (F.card : ℝ) ≤ Knum * ∏ j : Fin r, s j ^ (n + 1 + r + 1 - 2 * (j.1 + 1)) := by
      refine ⟨Knum, hKnum, ?_⟩
      intro s F hs hF
      have hkey := hnum' r s hs
      simp only [Fintype.card_fin] at hkey
      exact le_trans (Work.HP.Sig2.card_le_ncard_Tset (ι := Fin (n + 1)) r s F hF
        (Work.HP.Sig2.Tset_finite (ι := Fin (n + 1)) r s)) hkey
    obtain ⟨Cdya, hCdya, hdya'⟩ := Work.HP.Sig2.dyadic_sum_ge3 (n + 1) r h3 (by omega)
    obtain ⟨Karith, hKarith, harith'⟩ :=
      Work.HP.Sig2.window_sum_arith n r hn h3 hrn (max Kmk0 1) hKmink Cdya hCdya
        (fun L' hL => by
          have h := hdya' L' hL
          have he : ((n + 1 : ℕ) : ℝ) - 2 = (↑n : ℝ) + 1 - 2 := by push_cast; ring
          rw [he] at h
          exact h)
    obtain ⟨Kws, hKws, hws⟩ := Work.HP.Sig2.hws_ge3_of n r hn h3 hrn hnum (max Kmk0 1)
      hKmink hmink ⟨Kc, hKc, hKc'⟩ ⟨Karith, hKarith, harith'⟩
    refine ⟨Kws, hKws, ?_⟩
    intro X Y Δ hX hY hΔ
    rcases le_total X Y with hXY | hYX
    · obtain ⟨T, hT, hle⟩ := Work.HP.Sig2.ellXY_le_sum n r (by omega) hrn
        (Work.HP.Sig2.hred' n r (by omega) hrn) X Y Δ hX hY hΔ hXY
      exact le_trans hle (hws X Y Δ hX hY hΔ hXY T hT)
    · rw [Work.HP.Sig2.ellXY_comm n r X Y Δ]
      obtain ⟨T, hT, hle⟩ := Work.HP.Sig2.ellXY_le_sum n r (by omega) hrn
        (Work.HP.Sig2.hred' n r (by omega) hrn) Y X Δ hY hX hΔ hYX
      refine le_trans hle (le_trans (hws Y X Δ hY hX hΔ hYX T hT) ?_)
      exact le_of_eq (by ring)

end Work.HP.MDEstimates
