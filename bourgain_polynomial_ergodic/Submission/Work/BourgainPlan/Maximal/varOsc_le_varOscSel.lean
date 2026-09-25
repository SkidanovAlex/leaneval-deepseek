import Mathlib
import Submission.Work.BourgainPlan.Maximal.rhoVariationDefs

namespace Work.BourgainPlan.Maximal

open scoped BigOperators ENNReal

/-- **The block form of the `ρ`-oscillation is dominated by its selection form** (for `ρ > 0`).

`varOsc ρ lo hi a` is KMSZ's (5.6) with the `sup` *inside* each block,
`(Σ_{j<J} (⨆_{n ∈ [o_j, o_{j+1})} ‖a n − a (o_j)‖ₑ)^ρ)^{1/ρ}`, while `varOscSel ρ lo hi a` chooses
one index `n j ∈ [o_j, o_{j+1})` per block and takes the supremum over all selections.  For a
boundary sequence all of whose blocks are nonempty the two agree: in `ℝ≥0∞` a finite sum of suprema
is the supremum of the sums over independent selections (the ingredients are
`(⨆_n x_n)^ρ = ⨆_n x_n^ρ` for `ρ > 0`, by continuity of `ENNReal.rpow` in its exponent, and
`(⨆_i x_i) + (⨆_j y_j) = ⨆_{(i,j)} (x_i + y_j)`, which holds because `ENNReal` addition preserves
suprema; induct on `Finset.range J`).  A block with `o j = o (j+1)` is empty: it contributes
`(⊥)^ρ = 0` to the block form, whereas the same boundaries admit *no* selection — the reduction is
to delete the repeated values of `o` (this does not change the block value, since the deleted
blocks contribute `0`), which restores admissibility. -/
theorem varOsc_le_varOscSel {E : Type*} [SeminormedAddCommGroup E] {ρ : ℝ} (hρ : 0 < ρ)
    (lo hi : ℕ) (a : ℕ → E) :
    varOsc ρ lo hi a ≤ varOscSel ρ lo hi a := by
  -- In the strictly increasing case every block is nonempty, so one can choose (via the fact that
  -- a finite nonempty supremum in `ℝ≥0∞` is attained) an index in each block realising its `sup`;
  -- the block value then *equals* the corresponding selection value.
  have strictCase : ∀ (J : ℕ) (o : ℕ → ℕ), o 0 = lo → o J = hi → Monotone o →
      (∀ j < J, o j < o (j + 1)) →
      (∑ j ∈ Finset.range J, (⨆ n ∈ Finset.Ico (o j) (o (j + 1)), ‖a n - a (o j)‖ₑ) ^ ρ) ^ (1 / ρ)
        ≤ varOscSel ρ lo hi a := by
    intro J o ho0 hoJ hmono hstrict
    have hex : ∀ j, j < J → ∃ n ∈ Finset.Ico (o j) (o (j + 1)),
        (⨆ m ∈ Finset.Ico (o j) (o (j + 1)), ‖a m - a (o j)‖ₑ) = ‖a n - a (o j)‖ₑ := by
      intro j hj
      have hne : (Finset.Ico (o j) (o (j + 1))).Nonempty :=
        ⟨o j, Finset.mem_Ico.mpr ⟨le_rfl, hstrict j hj⟩⟩
      obtain ⟨n, hn, hsup⟩ := Finset.exists_mem_eq_sup _ hne (fun m => ‖a m - a (o j)‖ₑ)
      exact ⟨n, hn, by rwa [Finset.sup_eq_iSup] at hsup⟩
    let nsel : ℕ → ℕ := fun j => if hj : j < J then Classical.choose (hex j hj) else 0
    have hnsel_mem : ∀ j < J, nsel j ∈ Finset.Ico (o j) (o (j + 1)) := by
      intro j hj
      simp only [nsel, dif_pos hj]
      exact (Classical.choose_spec (hex j hj)).1
    have hnsel_eq : ∀ j < J,
        (⨆ m ∈ Finset.Ico (o j) (o (j + 1)), ‖a m - a (o j)‖ₑ) = ‖a (nsel j) - a (o j)‖ₑ := by
      intro j hj
      simp only [nsel, dif_pos hj]
      exact (Classical.choose_spec (hex j hj)).2
    have hsum1 : (∑ j ∈ Finset.range J,
          (⨆ m ∈ Finset.Ico (o j) (o (j + 1)), ‖a m - a (o j)‖ₑ) ^ ρ)
        = ∑ j ∈ Finset.range J, (‖a (nsel j) - a (o j)‖ₑ) ^ ρ := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hnsel_eq j (Finset.mem_range.mp hj)]
    have hsum2 : (∑ j ∈ Finset.range J, (‖a (nsel j) - a (o j)‖ₑ) ^ ρ)
        = ENNReal.ofReal (∑ j ∈ Finset.range J, ‖a (nsel j) - a (o j)‖ ^ ρ) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [show ‖a (nsel j) - a (o j)‖ₑ = ENNReal.ofReal ‖a (nsel j) - a (o j)‖ from by simp,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (le_of_lt hρ)]
      · intro j hj
        exact Real.rpow_nonneg (norm_nonneg _) _
    have hSnonneg : 0 ≤ ∑ j ∈ Finset.range J, ‖a (nsel j) - a (o j)‖ ^ ρ :=
      Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) _
    have hfin : (∑ j ∈ Finset.range J,
          (⨆ m ∈ Finset.Ico (o j) (o (j + 1)), ‖a m - a (o j)‖ₑ) ^ ρ) ^ (1 / ρ)
        = ENNReal.ofReal ((∑ j ∈ Finset.range J, ‖a (nsel j) - a (o j)‖ ^ ρ) ^ (1 / ρ)) := by
      rw [hsum1, hsum2, ENNReal.ofReal_rpow_of_nonneg hSnonneg (by positivity)]
    rw [hfin]
    exact le_iSup_of_le J (le_iSup_of_le o (le_iSup_of_le nsel
      (le_iSup_of_le ho0 (le_iSup_of_le hoJ
        (le_iSup_of_le hmono (le_iSup_of_le hnsel_mem le_rfl))))))
  -- In the general case, delete a repeated boundary value: the merge does not change the block
  -- sum (the deleted block is empty and contributes `0`), and strictly decreases `J`, so that a
  -- strong induction on `J` reaches the strictly increasing case.
  have main : ∀ n : ℕ, ∀ o : ℕ → ℕ, o 0 = lo → o n = hi → Monotone o →
      (∑ j ∈ Finset.range n, (⨆ m ∈ Finset.Ico (o j) (o (j + 1)), ‖a m - a (o j)‖ₑ) ^ ρ)
        ^ (1 / ρ) ≤ varOscSel ρ lo hi a := by
    intro n
    refine Nat.strong_induction_on n (fun n ih => ?_)
    intro o ho0 hoJ hmono
    by_cases hstrict : ∀ j < n, o j < o (j + 1)
    · exact strictCase n o ho0 hoJ hmono hstrict
    · have hexA : ∃ A, A < n ∧ o (A + 1) ≤ o A := by
        by_contra hcon
        exact hstrict fun j hj => lt_of_not_ge fun hge => hcon ⟨j, hj, hge⟩
      obtain ⟨A, hAn, hAle⟩ := hexA
      have hAeq : o A = o (A + 1) := le_antisymm (hmono (Nat.le_succ A)) hAle
      -- the compression `ψ` (delete the repeated value), and the reduced boundary sequence `o'`
      let ψ : ℕ → ℕ := fun j => if j < A then j else j + 1
      let o' : ℕ → ℕ := fun j => o (ψ j)
      have hψstrict : StrictMono ψ := by
        intro i j hij
        simp only [ψ]
        by_cases hi : i < A
        · rw [if_pos hi]
          by_cases hj : j < A
          · rw [if_pos hj]; exact hij
          · rw [if_neg hj]; omega
        · rw [if_neg hi]
          have hj : ¬ j < A := by omega
          rw [if_neg hj]; omega
      have hmono' : Monotone o' := hmono.comp hψstrict.monotone
      have hstep : ∀ j, o (ψ j + 1) = o (ψ (j + 1)) := by
        intro j
        rcases lt_trichotomy (j + 1) A with h | h | h
        · have h1 : ψ j = j := by simp only [ψ, if_pos (by omega : j < A)]
          have h2 : ψ (j + 1) = j + 1 := by simp only [ψ, if_pos h]
          rw [h1, h2]
        · have h1 : ψ j = j := by simp only [ψ, if_pos (by omega : j < A)]
          have h2 : ψ (j + 1) = j + 1 + 1 := by
            simp only [ψ, if_neg (by omega : ¬ j + 1 < A)]
          rw [h1, h2, h, hAeq]
        · have h1 : ψ j = j + 1 := by simp only [ψ, if_neg (by omega : ¬ j < A)]
          have h2 : ψ (j + 1) = j + 1 + 1 := by
            simp only [ψ, if_neg (by omega : ¬ j + 1 < A)]
          rw [h1, h2]
      have ho'0 : o' 0 = lo := by
        change o (ψ 0) = lo
        rcases Nat.eq_zero_or_pos A with hA0 | hApos
        · subst hA0
          have h1 : ψ 0 = 1 := by simp [ψ]
          rw [h1, ← hAeq, ho0]
        · have h1 : ψ 0 = 0 := by simp only [ψ, if_pos hApos]
          rw [h1, ho0]
      have ho'n : o' (n - 1) = hi := by
        change o (ψ (n - 1)) = hi
        rw [show ψ (n - 1) = n from by
          simp only [ψ, if_neg (by omega : ¬ n - 1 < A)]; omega, hoJ]
      let F : ℕ → ℝ≥0∞ := fun k => (⨆ m ∈ Finset.Ico (o k) (o (k + 1)), ‖a m - a (o k)‖ₑ) ^ ρ
      let F' : ℕ → ℝ≥0∞ := fun k => (⨆ m ∈ Finset.Ico (o' k) (o' (k + 1)), ‖a m - a (o' k)‖ₑ) ^ ρ
      have hFA : F A = 0 := by
        change (⨆ m ∈ Finset.Ico (o A) (o (A + 1)), ‖a m - a (o A)‖ₑ) ^ ρ = 0
        rw [hAeq, Finset.Ico_self]
        simp [ENNReal.zero_rpow_of_pos hρ]
      have hFeq : ∀ j, F' j = F (ψ j) := by
        intro j
        change (⨆ m ∈ Finset.Ico (o (ψ j)) (o (ψ (j + 1))), ‖a m - a (o (ψ j))‖ₑ) ^ ρ
          = (⨆ m ∈ Finset.Ico (o (ψ j)) (o (ψ j + 1)), ‖a m - a (o (ψ j))‖ₑ) ^ ρ
        rw [hstep j]
      have himage : (Finset.range (n - 1)).image ψ = (Finset.range n).erase A := by
        ext k
        simp only [Finset.mem_image, Finset.mem_range, Finset.mem_erase]
        constructor
        · rintro ⟨j, hj, rfl⟩
          refine ⟨?_, ?_⟩
          · simp only [ψ]; split_ifs <;> omega
          · simp only [ψ]; split_ifs <;> omega
        · rintro ⟨hkA, hkn⟩
          rcases lt_or_gt_of_ne hkA with hklt | hkgt
          · exact ⟨k, by omega, by simp only [ψ, if_pos hklt]⟩
          · exact ⟨k - 1, by omega, by simp only [ψ, if_neg (by omega : ¬ k - 1 < A)]; omega⟩
      have hinj : Set.InjOn ψ ↑(Finset.range (n - 1)) :=
        fun x _ y _ hxy => hψstrict.injective hxy
      have hsum : ∑ k ∈ Finset.range n, F k = ∑ k ∈ Finset.range (n - 1), F' k := by
        rw [← Finset.sum_erase (s := Finset.range n) (a := A) (f := F) hFA, ← himage,
            Finset.sum_image (f := F) (g := ψ) hinj]
        exact Finset.sum_congr rfl fun j _ => (hFeq j).symm
      have hIH := ih (n - 1) (by omega) o' ho'0 ho'n hmono'
      calc (∑ j ∈ Finset.range n,
            (⨆ m ∈ Finset.Ico (o j) (o (j + 1)), ‖a m - a (o j)‖ₑ) ^ ρ) ^ (1 / ρ)
          = (∑ k ∈ Finset.range n, F k) ^ (1 / ρ) := rfl
        _ = (∑ k ∈ Finset.range (n - 1), F' k) ^ (1 / ρ) := by rw [hsum]
        _ ≤ varOscSel ρ lo hi a := hIH
  rw [varOsc]
  refine iSup_le fun J => iSup_le fun o => iSup_le fun ho0 => iSup_le fun hoJ =>
    iSup_le fun hmono => ?_
  exact main J o ho0 hoJ hmono

end Work.BourgainPlan.Maximal
