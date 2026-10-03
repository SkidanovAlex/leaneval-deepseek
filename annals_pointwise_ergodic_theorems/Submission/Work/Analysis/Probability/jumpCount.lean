import Mathlib

/-!
# The `λ`-jump counting functional of a path, and its elementary properties

For a path `x : ℕ → ℝ` and a level `λ`, let
`Kpath x λ := sup over increasing `u : ℕ → ℕ` and `J` of `#{ j < J : |x (u (j+1)) - x (u j)| > λ }`.

This is the *counting* version of the `λ`-jump function (the supremum over all subsequences of the
number of gaps exceeding `λ`).  Its elementary features, used in the proof of the weak `(1,1)` bound
for the martingale variation, are

* `one_le_Kpath_iff` : `Kpath x λ ≥ 1` iff the path has two values differing by more than `λ`;
  combined with Doob's maximal inequality this gives the level-`1` bound
  `μ {ω | Kpath x λ ≥ 1} ≤ 2‖f‖₁/λ`;
* the dyadic layer-cake inequality expressing the path `r`-variation as a weighted sum of the
  jump counts `Kpath x (t 2^{-k-1})` (see `weak_type_one_Vsup`).
-/

open scoped ENNReal BigOperators

namespace Work.Analysis.Probability

/-- The `λ`-jump counting functional of a path: the maximal number of gaps exceeding `lam`
over all subsequences. -/
noncomputable def Kpath (x : ℕ → ℝ) (lam : ℝ) : ℝ≥0∞ :=
  ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
    ((Finset.filter (fun j => lam < |x (u.1 (j+1)) - x (u.1 j)|) (Finset.range J)).card : ℝ≥0∞)

/-- The `r`-variation of a path, `ℝ≥0∞`-valued. -/
noncomputable def VpathR (x : ℕ → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
    ENNReal.ofReal ((∑ j ∈ Finset.range J, |x (u.1 (j+1)) - x (u.1 j)| ^ r) ^ (1/r))

/-- The `λ`-jump counting functional applied to a path family. -/
noncomputable def Jcount {Ω : Type*} (g : ℕ → Ω → ℝ) (lam : ℝ) (ω : Ω) : ℝ≥0∞ :=
  Kpath (fun n => g n ω) lam

lemma Kpath_anti (x : ℕ → ℝ) {lam lam' : ℝ} (h : lam ≤ lam') : Kpath x lam' ≤ Kpath x lam := by
  refine iSup_le (fun u => iSup_le (fun J => ?_))
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_))
    (le_iSup_of_le u (le_iSup_of_le J le_rfl))
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨hj.1, lt_of_le_of_lt h hj.2⟩

/-- `Kpath x λ ≥ 1` exactly when two points of the path differ by more than `λ`. -/
lemma one_le_Kpath_iff {x : ℕ → ℝ} {lam : ℝ} :
    1 ≤ Kpath x lam ↔ ∃ s s' : ℕ, s < s' ∧ lam < |x s' - x s| := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hzero : Kpath x lam = 0 := by
      refine le_antisymm ?_ bot_le
      refine iSup_le (fun u => iSup_le (fun J => ?_))
      have hempty : (Finset.filter (fun j => lam < |x (u.1 (j+1)) - x (u.1 j)|)
          (Finset.range J)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro j hj
        rw [Finset.mem_filter] at hj
        exact not_lt.mpr (hc (u.1 j) (u.1 (j+1)) (u.2 (Nat.lt_succ_self j))) hj.2
      rw [hempty]
      simp
    rw [hzero] at h
    exact absurd h (by simp)
  · rintro ⟨s, s', hss, hlt⟩
    have hpos : 0 < s' - s := by omega
    refine le_iSup_of_le ⟨fun j => s + j * (s' - s), ?_⟩ (le_iSup_of_le 1 ?_)
    · intro a b hab
      simp only
      exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hab hpos) s
    · have hmem : 0 ∈ Finset.filter (fun j => lam < |x ((fun j => s + j * (s' - s)) (j+1)) - x ((fun j => s + j * (s' - s)) j)|)
          (Finset.range 1) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by norm_num, ?_⟩
        have h1 : s + 1 * (s' - s) = s' := by omega
        have h0 : s + 0 * (s' - s) = s := by omega
        rw [h1, h0]
        exact hlt
      exact_mod_cast Finset.card_pos.mpr ⟨0, hmem⟩

end Work.Analysis.Probability
