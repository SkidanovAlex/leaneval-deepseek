import Mathlib
import Submission.Work.BourgainPlan.Maximal.rhoVariationDefs

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators ENNReal

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **The oscillation is dominated by the variation** (the pointwise half of KMSZ
arXiv:2606.12663, Proposition 5.10; the case `ρ = 2` is the remark after their (6.7)).

`varOscSel ρ lo hi a` is the selection form of the `ρ`-oscillation over the window `[lo, hi]`: the
supremum, over increasing block boundaries `o 0 = lo < … < o J = hi` and selected indices
`n j ∈ [o j, o (j+1)]`, of `(Σ_{j<J} ‖a (n j) − a (o j)‖^ρ)^{1/ρ}`.  (This is the same object
as the block-sup form `varOsc`, since in `ℝ≥0∞` a finite sum of suprema is the supremum of the
sums over independent selections.)

The proof is a gluing of chains: the "alternating" chain
`o 0, n 0, o 1, n 1, …, o J` is monotone with values in `[lo, hi]`, and
`(chainLp ρ (2*J) a t)^ρ = Σ_{j<J} (‖a (n j) − a (o j)‖^ρ + ‖a (o (j+1)) − a (n j)‖^ρ)
≥ Σ_{j<J} ‖a (n j) − a (o j)‖^ρ`.
Watch out: `Monotone` is a *global* condition on `ℕ → ℕ`, so the alternating chain must be
clamped (e.g. constantly `o J = hi`) for indices `> 2*J`. -/
theorem varOscSel_le_varRho {E : Type*} [SeminormedAddCommGroup E] {ρ : ℝ} (hρ : 1 ≤ ρ)
    (lo hi : ℕ) (a : ℕ → E) :
    varOscSel ρ lo hi a ≤ varRho ρ lo hi a := by
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hinv : 0 ≤ (1 : ℝ) / ρ := by positivity
  rw [varOscSel]
  refine iSup_le fun J => iSup_le fun o => iSup_le fun n => iSup_le fun ho0 =>
    iSup_le fun hoJ => iSup_le fun homo => iSup_le fun hsel => ?_
  -- the selection condition, in the form of a pair of inequalities (the definition
  -- states it as membership in `Finset.Ico`)
  have hsel' : ∀ j < J, o j ≤ n j ∧ n j ≤ o (j + 1) := fun j hj => by
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp (hsel j hj)
    exact ⟨h1, le_of_lt h2⟩
  -- the alternating chain `o 0, n 0, o 1, n 1, …, o J`, clamped to `o J` past `2*J`
  let u : ℕ → ℕ := fun k =>
    if 2 * J ≤ k then o J else if k % 2 = 0 then o (k / 2) else n (k / 2)
  have hu_even : ∀ j < J, u (2 * j) = o j := by
    intro j hj
    simp only [u, if_neg (by omega : ¬ 2 * J ≤ 2 * j),
      if_pos (by omega : (2 * j) % 2 = 0)]
    congr 1
    omega
  have hu_odd : ∀ j < J, u (2 * j + 1) = n j := by
    intro j hj
    simp only [u, if_neg (by omega : ¬ 2 * J ≤ 2 * j + 1),
      if_neg (by omega : ¬ (2 * j + 1) % 2 = 0)]
    congr 1
    omega
  have hu_mono : Monotone u := by
    refine monotone_nat_of_le_succ fun k => ?_
    by_cases hk : 2 * J ≤ k
    · have h1 : u k = o J := by simp only [u, if_pos hk]
      have h2 : u (k + 1) = o J := by simp only [u, if_pos (le_trans hk (Nat.le_succ k))]
      rw [h1, h2]
    · by_cases hk1 : 2 * J ≤ k + 1
      · have hodd : ¬ k % 2 = 0 := by omega
        have hlt : k / 2 < J := by omega
        have hle : k / 2 + 1 ≤ J := by omega
        simp only [u, if_neg hk, if_pos hk1, if_neg hodd]
        exact le_trans (hsel' (k / 2) hlt).2 (homo hle)
      · have hlt : k / 2 < J := by omega
        simp only [u, if_neg hk, if_neg hk1]
        rcases Nat.mod_two_eq_zero_or_one k with hev | hodd
        · have hdiv : (k + 1) / 2 = k / 2 := by omega
          simp only [if_pos hev, if_neg (by omega : ¬ (k + 1) % 2 = 0), hdiv]
          exact (hsel' (k / 2) hlt).1
        · have hdiv : (k + 1) / 2 = k / 2 + 1 := by omega
          simp only [if_neg (by omega : ¬ k % 2 = 0),
            if_pos (by omega : (k + 1) % 2 = 0), hdiv]
          exact (hsel' (k / 2) hlt).2
  have hu_hi : ∀ k ≤ 2 * J, u k ≤ hi := by
    intro k hk
    by_cases h : 2 * J ≤ k
    · simp only [u, if_pos h]
      exact le_of_eq hoJ
    · have hlt : k / 2 < J := by omega
      have hle : k / 2 + 1 ≤ J := by omega
      rcases Nat.mod_two_eq_zero_or_one k with hev | hodd
      · simp only [u, if_neg h, if_pos hev]
        exact le_trans (homo (by omega : k / 2 ≤ J)) (le_of_eq hoJ)
      · simp only [u, if_neg h, if_neg (by omega : ¬ k % 2 = 0)]
        exact le_trans (hsel' (k / 2) hlt).2 (le_trans (homo hle) (le_of_eq hoJ))
  have hu_lo : ∀ k ≤ 2 * J, lo ≤ u k := by
    intro k hk
    by_cases h : 2 * J ≤ k
    · simp only [u, if_pos h]
      rw [← ho0]
      exact homo (Nat.zero_le J)
    · rcases Nat.mod_two_eq_zero_or_one k with hev | hodd
      · simp only [u, if_neg h, if_pos hev]
        rw [← ho0]
        exact homo (Nat.zero_le _)
      · have hlt : k / 2 < J := by omega
        simp only [u, if_neg h, if_neg (by omega : ¬ k % 2 = 0)]
        rw [← ho0]
        exact le_trans (homo (Nat.zero_le _)) (hsel' (k / 2) hlt).1
  have hterms : ∀ j ∈ Finset.range J,
      ‖a (n j) - a (o j)‖ ^ ρ = ‖a (u (2 * j + 1)) - a (u (2 * j))‖ ^ ρ := by
    intro j hj
    rw [hu_odd j (Finset.mem_range.mp hj), hu_even j (Finset.mem_range.mp hj)]
  have hsum : ∑ j ∈ Finset.range J, ‖a (n j) - a (o j)‖ ^ ρ
      ≤ ∑ l ∈ Finset.range (2 * J), ‖a (u (l + 1)) - a (u l)‖ ^ ρ := by
    have hsub : (Finset.range J).image (fun j => 2 * j) ⊆ Finset.range (2 * J) := by
      intro l hl
      rw [Finset.mem_image] at hl
      obtain ⟨j, hj, rfl⟩ := hl
      rw [Finset.mem_range] at hj ⊢
      omega
    calc ∑ j ∈ Finset.range J, ‖a (n j) - a (o j)‖ ^ ρ
        = ∑ j ∈ Finset.range J, ‖a (u (2 * j + 1)) - a (u (2 * j))‖ ^ ρ :=
          Finset.sum_congr rfl hterms
      _ = ∑ l ∈ (Finset.range J).image (fun j => 2 * j),
            ‖a (u (l + 1)) - a (u l)‖ ^ ρ :=
          (Finset.sum_image (s := Finset.range J) (g := fun j => 2 * j)
            (f := fun l => ‖a (u (l + 1)) - a (u l)‖ ^ ρ)
            (fun x _ y _ hxy => by
              have h : 2 * x = 2 * y := by simpa using hxy
              omega)).symm
      _ ≤ ∑ l ∈ Finset.range (2 * J), ‖a (u (l + 1)) - a (u l)‖ ^ ρ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun l _ _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hmain : (∑ j ∈ Finset.range J, ‖a (n j) - a (o j)‖ ^ ρ) ^ (1 / ρ)
      ≤ chainLp ρ (2 * J) a u := by
    rw [chainLp]
    exact Real.rpow_le_rpow
      (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _) hsum hinv
  refine le_trans (ENNReal.ofReal_le_ofReal hmain) ?_
  rw [varRho]
  refine le_iSup_of_le (2 * J) (le_iSup_of_le u (le_iSup_of_le hu_mono ?_))
  exact le_iSup_of_le (fun j hj => ⟨hu_lo j hj, hu_hi j hj⟩) le_rfl

end

end Work.BourgainPlan.Maximal
