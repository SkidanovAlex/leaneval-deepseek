import Mathlib
import Submission.Work.Analysis.Probability.greedyDefs

/-!
# `Kpath` is dominated by the greedy `δ`-jump count

For a path `x : ℕ → ℝ` and levels `δ, λ` with `0 < δ` and `2 * δ ≤ λ`, the maximal number
`Kpath x λ` of gaps exceeding `λ` along an arbitrary subsequence is at most the number
`greedyJumps x δ` of greedy `δ`-jumps of the path.

The proof is the classical block argument.  The greedy times `t k = greedyTime x δ k` cut `ℕ`
into blocks `[t k, t (k+1))`; on a block the path stays within `δ` of its initial value
`x (t k)`, so two points of one block are at distance at most `2 * δ ≤ λ` and hence a `λ`-jump
can never start inside a block, and two `λ`-jumps cannot start in the same block.  Since the
chain can only stop in the final (infinite) block, which contains no jump either, distinct
`λ`-jumps are charged to distinct *finite* blocks, of which there are exactly `greedyJumps x δ`.
-/

open scoped ENNReal BigOperators

namespace Work.Analysis.Probability

/-! ## Elementary properties of `nextJump` -/

private lemma nextJump_eq_find {x : ℕ → ℝ} {δ : ℝ} {a : ℕ}
    (h : ∃ n : ℕ, a < n ∧ δ < |x n - x a|) :
    nextJump x δ a = ((Nat.find h : ℕ) : ℕ∞) := by
  classical
  show dite (∃ n : ℕ, a < n ∧ δ < |x n - x a|)
    (fun h => ((Nat.find h : ℕ) : ℕ∞)) (fun _ => ⊤) = _
  rw [dif_pos h]

private lemma nextJump_eq_top {x : ℕ → ℝ} {δ : ℝ} {a : ℕ}
    (h : ¬ ∃ n : ℕ, a < n ∧ δ < |x n - x a|) : nextJump x δ a = ⊤ := by
  classical
  show dite (∃ n : ℕ, a < n ∧ δ < |x n - x a|)
    (fun h => ((Nat.find h : ℕ) : ℕ∞)) (fun _ => ⊤) = _
  rw [dif_neg h]

private lemma coe_lt_nextJump (x : ℕ → ℝ) (δ : ℝ) (a : ℕ) :
    ((a : ℕ) : ℕ∞) < nextJump x δ a := by
  classical
  by_cases h : ∃ n : ℕ, a < n ∧ δ < |x n - x a|
  · rw [nextJump_eq_find h, ENat.natCast_lt_natCast]
    exact (Nat.find_spec h).1
  · rw [nextJump_eq_top h]
    exact ENat.natCast_lt_top a

/-- Any `m` lying strictly between `a` and `nextJump x δ a` is within `δ` of `x a`:
`nextJump x δ a` is the *first* time at which the path leaves the `δ`-neighbourhood of `x a`. -/
private lemma abs_le_of_lt_nextJump {x : ℕ → ℝ} {δ : ℝ} {a m : ℕ} (ham : a < m)
    (hm : ((m : ℕ) : ℕ∞) < nextJump x δ a) : |x m - x a| ≤ δ := by
  classical
  by_cases h : ∃ n : ℕ, a < n ∧ δ < |x n - x a|
  · rw [nextJump_eq_find h, ENat.natCast_lt_natCast] at hm
    exact le_of_not_gt (fun hg => Nat.find_min h hm ⟨ham, hg⟩)
  · exact le_of_not_gt (fun hg => h ⟨m, ham, hg⟩)

/-! ## Elementary properties of the greedy chain -/

private lemma greedyTime_zero (x : ℕ → ℝ) (δ : ℝ) : greedyTime x δ 0 = 0 := rfl

private lemma greedyTime_succ_eq (x : ℕ → ℝ) (δ : ℝ) (k : ℕ) :
    greedyTime x δ (k + 1) =
      (if greedyTime x δ k < ⊤ then nextJump x δ ((greedyTime x δ k).toNat) else ⊤) := rfl

private lemma greedyTime_lt_succ_of_lt_top (x : ℕ → ℝ) (δ : ℝ) {k : ℕ}
    (h : greedyTime x δ k < ⊤) : greedyTime x δ k < greedyTime x δ (k + 1) := by
  rw [greedyTime_succ_eq, if_pos h]
  have hcoe : (((greedyTime x δ k).toNat : ℕ) : ℕ∞) = greedyTime x δ k :=
    ENat.natCast_toNat (ne_of_lt h)
  rw [← hcoe]
  exact coe_lt_nextJump x δ _

/-- The greedy chain grows at least linearly: `k ≤ t k`. -/
private lemma coe_le_greedyTime (x : ℕ → ℝ) (δ : ℝ) (k : ℕ) :
    ((k : ℕ) : ℕ∞) ≤ greedyTime x δ k := by
  induction k with
  | zero => simp [greedyTime]
  | succ k ih =>
      by_cases h : greedyTime x δ k < ⊤
      · have hlt : greedyTime x δ k < greedyTime x δ (k + 1) :=
          greedyTime_lt_succ_of_lt_top x δ h
        have key : ((k : ℕ) : ℕ∞) + 1 ≤ greedyTime x δ (k + 1) :=
          (ENat.add_one_le_iff (ENat.natCast_ne_top k)).mpr (lt_of_le_of_lt ih hlt)
        rw [Nat.cast_succ]
        exact key
      · have htop : greedyTime x δ (k + 1) = ⊤ := by
          rw [greedyTime_succ_eq, if_neg h]
        rw [htop]
        exact le_top

/-- For every `n` some greedy time eventually passes `n`. -/
private lemma exists_lt_greedyTime (x : ℕ → ℝ) (δ : ℝ) (n : ℕ) :
    ∃ k : ℕ, ((n : ℕ) : ℕ∞) < greedyTime x δ (k + 1) :=
  ⟨n, lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self n))
    (coe_le_greedyTime x δ (n + 1))⟩

/-- Every `n` lies in a block `[t k, t (k+1))` of the greedy chain. -/
private lemma exists_block (x : ℕ → ℝ) (δ : ℝ) (n : ℕ) :
    ∃ k : ℕ, greedyTime x δ k ≤ ((n : ℕ) : ℕ∞) ∧
      ((n : ℕ) : ℕ∞) < greedyTime x δ (k + 1) := by
  classical
  have hex : ∃ k : ℕ, ((n : ℕ) : ℕ∞) < greedyTime x δ (k + 1) := exists_lt_greedyTime x δ n
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  by_contra hcon
  rw [not_le] at hcon
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, greedyTime_zero] at hcon
      exact absurd hcon (not_lt.mpr zero_le)
    · exact hpos
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hQm : ((n : ℕ) : ℕ∞) < greedyTime x δ (m + 1) := by rw [← hm]; exact hcon
  have := Nat.find_min' hex hQm
  omega

/-- On a greedy block `[t k, t (k+1))` the path stays within `δ` of `x (t k)`. -/
private lemma abs_le_of_mem_block (x : ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (k n : ℕ)
    (h1 : greedyTime x δ k ≤ ((n : ℕ) : ℕ∞))
    (h2 : ((n : ℕ) : ℕ∞) < greedyTime x δ (k + 1)) :
    |x n - x ((greedyTime x δ k).toNat)| ≤ δ := by
  have htop : greedyTime x δ k < ⊤ := lt_of_le_of_lt h1 (ENat.natCast_lt_top n)
  have hsucc : greedyTime x δ (k + 1) = nextJump x δ ((greedyTime x δ k).toNat) := by
    rw [greedyTime_succ_eq, if_pos htop]
  have hle : (greedyTime x δ k).toNat ≤ n := by
    have h := h1
    rw [← ENat.natCast_toNat (ne_of_lt htop)] at h
    exact ENat.natCast_le_natCast.mp h
  rcases lt_or_eq_of_le hle with hlt | heq
  · have h2' : ((n : ℕ) : ℕ∞) < nextJump x δ ((greedyTime x δ k).toNat) := by
      rw [← hsucc]; exact h2
    exact abs_le_of_lt_nextJump hlt h2'
  · rw [heq, sub_self, abs_zero]
    exact hδ

/-! ## The counting argument -/

theorem kpath_le_greedy_jumps (x : ℕ → ℝ) {δ lam : ℝ} (hδ : 0 < δ) (h : 2 * δ ≤ lam) :
    Work.Analysis.Probability.Kpath x lam ≤ Work.Analysis.Probability.greedyJumps x δ := by
  refine iSup_le (fun u => iSup_le (fun J => ?_))
  classical
  -- a block index for every point of the path
  have hex : ∀ j : ℕ, ∃ k : ℕ, greedyTime x δ k ≤ ((u.1 j : ℕ) : ℕ∞) ∧
      ((u.1 j : ℕ) : ℕ∞) < greedyTime x δ (k + 1) := fun j => exists_block x δ (u.1 j)
  choose F hF1 hF2 using hex
  set S : Finset ℕ :=
    Finset.filter (fun j => lam < |x (u.1 (j + 1)) - x (u.1 j)|) (Finset.range J) with hSdef
  have hmem : ∀ j : ℕ, j ∈ S ↔ j ∈ Finset.range J ∧ lam < |x (u.1 (j + 1)) - x (u.1 j)| := by
    intro j
    rw [hSdef, Finset.mem_filter]
  -- `u` is monotone
  have hule : ∀ j : ℕ, ((u.1 j : ℕ) : ℕ∞) ≤ ((u.1 (j + 1) : ℕ) : ℕ∞) := fun j =>
    ENat.natCast_le_natCast.mpr (le_of_lt (u.2 (Nat.lt_succ_self j)))
  -- two points of one block are at distance at most `2 * δ`
  have hclose : ∀ k n n' : ℕ,
      greedyTime x δ k ≤ ((n : ℕ) : ℕ∞) → ((n : ℕ) : ℕ∞) < greedyTime x δ (k + 1) →
      greedyTime x δ k ≤ ((n' : ℕ) : ℕ∞) → ((n' : ℕ) : ℕ∞) < greedyTime x δ (k + 1) →
      |x n - x n'| ≤ 2 * δ := by
    intro k n n' h1 h2 h3 h4
    have b1 := abs_le_of_mem_block x δ (le_of_lt hδ) k n h1 h2
    have b2 := abs_le_of_mem_block x δ (le_of_lt hδ) k n' h3 h4
    have htri : |x n - x n'| ≤
        |x n - x ((greedyTime x δ k).toNat)| + |x ((greedyTime x δ k).toNat) - x n'| := by
      have key := abs_add_le (x n - x ((greedyTime x δ k).toNat))
        (x ((greedyTime x δ k).toNat) - x n')
      rwa [sub_add_sub_cancel] at key
    calc |x n - x n'| ≤
          |x n - x ((greedyTime x δ k).toNat)| + |x ((greedyTime x δ k).toNat) - x n'| := htri
      _ ≤ δ + δ := add_le_add b1 (by simpa [abs_sub_comm] using b2)
      _ = 2 * δ := by ring
  -- a `λ`-jump never starts in the final (infinite) block: its block is finite
  have hFin : ∀ j ∈ S, greedyTime x δ (F j + 1) < ⊤ := by
    intro j hj
    obtain ⟨-, hjump⟩ := (hmem j).mp hj
    by_contra hcon
    have htop : greedyTime x δ (F j + 1) = ⊤ := le_antisymm le_top (not_lt.mp hcon)
    have hlift : ((u.1 (j + 1) : ℕ) : ℕ∞) < greedyTime x δ (F j + 1) := by
      rw [htop]
      exact ENat.natCast_lt_top _
    have hcl := hclose (F j) (u.1 j) (u.1 (j + 1)) (hF1 j) (hF2 j)
      (le_trans (hF1 j) (hule j)) hlift
    have hkey : |x (u.1 (j + 1)) - x (u.1 j)| ≤ lam :=
      by simpa [abs_sub_comm] using le_trans hcl h
    exact absurd hjump (not_lt.mpr hkey)
  -- two `λ`-jumps never start in the same block
  have hinj : ∀ j ∈ S, ∀ j' ∈ S, F j = F j' → j = j' := by
    intro j hj j' hj' hFF
    obtain ⟨-, hjump⟩ := (hmem j).mp hj
    obtain ⟨-, hjump'⟩ := (hmem j').mp hj'
    by_contra hne
    have hkey : ∀ a b : ℕ, a < b → lam < |x (u.1 (a + 1)) - x (u.1 a)| →
        F a = F b → False := by
      intro a b hab hjab hFab
      have huab : u.1 (a + 1) ≤ u.1 b := by
        rcases Nat.lt_or_ge (a + 1) b with hc | hc
        · exact le_of_lt (u.2 hc)
        · have h1 : a + 1 = b := Nat.le_antisymm (Nat.succ_le_of_lt hab) hc
          rw [h1]
      have h2b : ((u.1 b : ℕ) : ℕ∞) < greedyTime x δ (F a + 1) := by
        rw [hFab]
        exact hF2 b
      have hcl := hclose (F a) (u.1 (a + 1)) (u.1 a) (le_trans (hF1 a) (hule a))
        (lt_of_le_of_lt (ENat.natCast_le_natCast.mpr huab) h2b) (hF1 a) (hF2 a)
      have : |x (u.1 (a + 1)) - x (u.1 a)| ≤ lam := le_trans hcl h
      exact absurd hjab (not_lt.mpr this)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hkey j j' hlt hjump hFF
    · exact hkey j' j hlt hjump' hFF.symm
  -- counting: `S` injects into the set of finite blocks
  have hcard : ((S.card : ℕ) : ℝ≥0∞) ≤ greedyJumps x δ := by
    rcases Finset.eq_empty_or_nonempty S with hE | hNE
    · simp [hE]
    · obtain ⟨j₀, hj₀⟩ := hNE
      have hTne : (S.image F).Nonempty :=
        ⟨F j₀, Finset.mem_image.mpr ⟨j₀, hj₀, rfl⟩⟩
      have hcardT : (S.image F).card = S.card :=
        Finset.card_image_of_injOn
          (fun a ha b hb hab => hinj a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab)
      have hsub : S.image F ⊆ Finset.range ((S.image F).max' hTne + 1) := by
        intro b hb
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Finset.le_max' (S.image F) b hb)
      have hmTop : greedyTime x δ ((S.image F).max' hTne + 1) < ⊤ := by
        obtain ⟨j, hj, hjF⟩ := Finset.mem_image.mp (Finset.max'_mem (S.image F) hTne)
        rw [← hjF]
        exact hFin j hj
      have hle : S.card ≤ (S.image F).max' hTne + 1 := by
        calc S.card = (S.image F).card := hcardT.symm
          _ ≤ (Finset.range ((S.image F).max' hTne + 1)).card := Finset.card_le_card hsub
          _ = (S.image F).max' hTne + 1 := Finset.card_range _
      refine le_trans (Nat.cast_le.mpr hle) ?_
      refine le_iSup_of_le ((S.image F).max' hTne) ?_
      exact le_iSup_of_le hmTop le_rfl
  exact hcard

end Work.Analysis.Probability
