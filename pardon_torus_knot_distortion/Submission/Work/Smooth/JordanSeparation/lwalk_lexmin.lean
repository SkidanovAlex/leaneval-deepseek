import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_lex

/-!
# `vmin W ≤ vmax W - (1,1)` for a simple closed lattice walk
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-! ### A one-dimensional closed `±1` walk repeats a value -/

/-- A closed `±1` walk of length `n ≥ 3` that starts by going up repeats a value at two indices
other than the trivial pair `(0,n)`. -/
theorem oneD_repeat_of_up {y : ℕ → ℤ} {n : ℕ} (hn : 3 ≤ n) (h1 : y 0 < y 1)
    (hstep : ∀ k < n, y (k + 1) = y k + 1 ∨ y (k + 1) = y k - 1) (hcl : y n = y 0) :
    ∃ i j, i < j ∧ j ≤ n ∧ (i, j) ≠ (0, n) ∧ y i = y j := by
  classical
  by_contra hcon
  have hpair : ∀ i j, i < j → j ≤ n → (i, j) ≠ (0, n) → y i ≠ y j := by
    intro i j hij hjn hne heq
    exact hcon ⟨i, j, hij, hjn, hne, heq⟩
  have hne0 : ∀ k, 1 ≤ k → k ≤ n - 1 → y k ≠ y 0 := by
    intro k hk1 hk2 h
    exact hpair 0 k (by omega) (by omega)
      (by intro h; have h' := Prod.ext_iff.mp h; omega) h.symm
  obtain ⟨u, hu, hu'⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.Icc 1 (n - 1)) ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩ (f := y)
  have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
  have hu2 : u ≤ n - 1 := (Finset.mem_Icc.mp hu).2
  set M : ℤ := y u with hM
  have hyu : y u = M := hM.symm
  have hM1 : y 1 ≤ M := by
    rw [← hyu]
    calc y 1 ≤ (Finset.Icc 1 (n - 1)).sup'
          ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩ y :=
        Finset.le_sup' y (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
      _ = y u := hu'
  have hMgt : y 0 < y u := lt_of_lt_of_le h1 hM1
  have hstepu : y u = y (u - 1) + 1 ∨ y u = y (u - 1) - 1 := by
    have h := hstep (u - 1) (by omega)
    rwa [show u - 1 + 1 = u from by omega] at h
  have hstepu2 : y (u + 1) = y u + 1 ∨ y (u + 1) = y u - 1 := hstep u (by omega)
  have hprev_le : y (u - 1) ≤ y u := by
    rcases Nat.eq_zero_or_pos (u - 1) with h | h
    · rw [h]; exact le_of_lt hMgt
    · calc y (u - 1) ≤ (Finset.Icc 1 (n - 1)).sup'
            ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩ y :=
          Finset.le_sup' y (Finset.mem_Icc.mpr ⟨h, by omega⟩)
        _ = y u := hu'
  have hnext_le : y (u + 1) ≤ y u := by
    rcases eq_or_lt_of_le (show u + 1 ≤ n from by omega) with h | h
    · rw [h, hcl]; exact le_of_lt hMgt
    · calc y (u + 1) ≤ (Finset.Icc 1 (n - 1)).sup'
            ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩ y :=
          Finset.le_sup' y (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        _ = y u := hu'
  rcases eq_or_ne (y (u - 1)) (y u) with hp | hp
  · exact absurd hp (hpair (u - 1) u (by omega) (by omega)
      (by intro h; have h' := Prod.ext_iff.mp h; omega))
  rcases eq_or_ne (y (u + 1)) (y u) with hn' | hn'
  · exact absurd hn'.symm (hpair u (u + 1) (by omega) (by omega)
      (by intro h; have h' := Prod.ext_iff.mp h; omega))
  · have hp1 : y (u - 1) = y u - 1 := by
      rcases hstepu with h | h
      · omega
      · exfalso; omega
    have hn1 : y (u + 1) = y u - 1 := by
      rcases hstepu2 with h | h
      · exfalso; omega
      · omega
    exact absurd (hp1.trans hn1.symm) (hpair (u - 1) (u + 1) (by omega) (by omega)
      (by intro h; have h' := Prod.ext_iff.mp h; omega))

/-- A closed `±1` walk of length `n ≥ 3` starting by going down repeats a value. -/
theorem oneD_repeat_of_down {y : ℕ → ℤ} {n : ℕ} (hn : 3 ≤ n) (h1 : y 1 < y 0)
    (hstep : ∀ k < n, y (k + 1) = y k + 1 ∨ y (k + 1) = y k - 1) (hcl : y n = y 0) :
    ∃ i j, i < j ∧ j ≤ n ∧ (i, j) ≠ (0, n) ∧ y i = y j := by
  let z : ℕ → ℤ := fun k => -y k
  have hz1 : z 0 < z 1 := by dsimp [z]; simpa using h1
  have hzstep : ∀ k < n, z (k + 1) = z k + 1 ∨ z (k + 1) = z k - 1 := by
    intro k hk
    rcases hstep k hk with h | h
    · right; dsimp [z]; omega
    · left; dsimp [z]; omega
  have hzcl : z n = z 0 := by dsimp [z]; simpa using hcl
  obtain ⟨i, j, hij, hjn, hne, he⟩ := oneD_repeat_of_up (y := z) hn hz1 hzstep hzcl
  exact ⟨i, j, hij, hjn, hne, by simpa [z] using he⟩

/-- A closed `±1` walk of length `n ≥ 3` repeats a value. -/
theorem oneD_repeat {y : ℕ → ℤ} {n : ℕ} (hn : 3 ≤ n) (hne1 : y 1 ≠ y 0)
    (hstep : ∀ k < n, y (k + 1) = y k + 1 ∨ y (k + 1) = y k - 1) (hcl : y n = y 0) :
    ∃ i j, i < j ∧ j ≤ n ∧ (i, j) ≠ (0, n) ∧ y i = y j := by
  rcases lt_or_gt_of_ne hne1 with h | h
  · exact oneD_repeat_of_down hn h hstep hcl
  · exact oneD_repeat_of_up hn h hstep hcl

/-! ### The walk-level ingredients -/

/-- If no step of the segment `[a,b)` changes the first coordinate, then the first coordinates of
the endpoints agree. -/
theorem fst_eq_of_no_change {W : LWalk} {a b : ℕ} (hab : a ≤ b) (hb : b ≤ W.n)
    (hno : ∀ k, a ≤ k → k < b → (W.v k).1 = (W.v (k + 1)).1) :
    (W.v a).1 = (W.v b).1 := by
  have key : ∀ c, a ≤ c → c ≤ b → (W.v a).1 = (W.v c).1 := by
    intro c
    induction c with
    | zero => intro hac _; rw [Nat.le_zero.mp hac]
    | succ c ih =>
      intro hac hcb
      rcases Nat.eq_or_lt_of_le hac with h | h
      · rw [h]
      · rw [← hno c (by omega) (by omega)]
        exact ih (by omega) (by omega)
  exact key b hab le_rfl

/-- No lattice point is a unit step from itself. -/
theorem not_gridStep_self (p : ℤ × ℤ) : ¬ GridStep p p := by
  rintro (⟨-, h | h⟩ | ⟨-, h | h⟩) <;> omega

/-- If all vertices have the same first coordinate and `n ≥ 3`, the walk has a non-trivial double
point. -/
theorem exists_double_of_all_fst_eq {W : LWalk} (hn : 3 ≤ W.n)
    (heq : ∀ k ≤ W.n, (W.v k).1 = (W.v 0).1) :
    ∃ i j, i < j ∧ j ≤ W.n ∧ (i, j) ≠ (0, W.n) ∧ W.v i = W.v j := by
  have hstep : ∀ k < W.n, (W.v (k + 1)).2 = (W.v k).2 + 1 ∨ (W.v (k + 1)).2 = (W.v k).2 - 1 := by
    intro k hk
    have h1 : (W.v k).1 = (W.v (k + 1)).1 := by rw [heq k (by omega), heq (k + 1) (by omega)]
    rcases W.step k hk with ⟨ha, hb | hb⟩ | ⟨ha, hb | hb⟩
    · left; omega
    · right; omega
    · exfalso; omega
    · exfalso; omega
  have hne1 : (W.v 1).2 ≠ (W.v 0).2 := by
    intro h
    have h0 : W.v 0 = W.v 1 := Prod.ext (by rw [heq 0 (Nat.zero_le _), heq 1 (by omega)]) h.symm
    exact not_gridStep_self (W.v 0) (h0 ▸ W.step 0 (by omega))
  obtain ⟨i, j, hij, hjn, hne, he⟩ :=
    oneD_repeat (y := fun k => (W.v k).2) hn hne1 hstep (by rw [W.closed])
  refine ⟨i, j, hij, hjn, hne, Prod.ext ?_ he⟩
  rw [heq i (le_trans (le_of_lt hij) hjn), heq j hjn]

/-- A horizontal step keeps the second coordinate. -/
theorem snd_eq_of_step_fst_ne {W : LWalk} {k : ℕ} (hk : k < W.n)
    (h : (W.v k).1 ≠ (W.v (k + 1)).1) : (W.v k).2 = (W.v (k + 1)).2 := by
  rcases W.step k hk with ⟨ha, -⟩ | ⟨ha, hb | hb⟩
  · exact absurd ha h
  · exact ha
  · exact ha

/-- **The two-column case.**  If a simple closed lattice walk has vertices in exactly the two
columns `vmin1 W` and `vmin1 W + 1`, then its lexicographically minimal vertex is strictly below
the lexicographically maximal one. -/
theorem vmin2_lt_vmax2_of_gap_one {W : LWalk} (hW : W.IsSimple) (hn : 3 ≤ W.n)
    (hgap : vmin1 W + 1 = vmax1 W) : vmin2 W < vmax2 W := by
  classical
  have hcol : ∀ k ≤ W.n, (W.v k).1 = vmin1 W ∨ (W.v k).1 = vmax1 W := by
    intro k hk
    have h1 := vmin1_le W hk
    have h2 := le_vmax1 W hk
    omega
  -- a crossing exists
  have hex : ∃ k < W.n, (W.v k).1 ≠ (W.v (k + 1)).1 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨κ, hκ, hκv⟩ := exists_vmin W
    obtain ⟨κ', hκ', hκ'v⟩ := exists_vmax W
    have he : (W.v κ).1 = (W.v κ').1 := by
      rcases le_total κ κ' with h | h
      · exact fst_eq_of_no_change h hκ' (fun k _ hkb => hcon k (by omega))
      · exact (fst_eq_of_no_change h hκ (fun k _ hkb => hcon k (by omega))).symm
    rw [hκv, hκ'v] at he
    have he' : vmin1 W = vmax1 W := he
    omega
  obtain ⟨k0, hk0n, hk0ne⟩ := hex
  have hk0h : (W.v k0).2 = (W.v (k0 + 1)).2 := snd_eq_of_step_fst_ne hk0n hk0ne
  have hm2M2 : vmin2 W ≤ vmax2 W := by
    rcases hcol k0 (le_of_lt hk0n) with hL | hR <;>
      rcases hcol (k0 + 1) (by omega) with hL' | hR'
    · exact absurd (hL.trans hL'.symm) hk0ne
    · have h1 : vmin2 W ≤ (W.v k0).2 := vmin2_le W (le_of_lt hk0n) hL
      have h2 : (W.v (k0 + 1)).2 ≤ vmax2 W := le_vmax2 W (by omega) hR'
      omega
    · have h1 : vmin2 W ≤ (W.v (k0 + 1)).2 := vmin2_le W (by omega) hL'
      have h2 : (W.v k0).2 ≤ vmax2 W := le_vmax2 W (le_of_lt hk0n) hR
      omega
    · exact absurd (hR.trans hR'.symm) hk0ne
  by_contra hlt
  have hEq : vmax2 W = vmin2 W := le_antisymm (not_lt.mp hlt) hm2M2
  -- every crossing is a traversal of the edge `[vmin W, vmax W]`
  have hcv : ∀ k < W.n, (W.v k).1 ≠ (W.v (k + 1)).1 →
      ((W.v k = vmin W ∧ W.v (k + 1) = vmax W) ∨
        (W.v k = vmax W ∧ W.v (k + 1) = vmin W)) := by
    intro k hk hne
    have hA := hcol k (le_of_lt hk)
    have hB := hcol (k + 1) (by omega)
    have hh : (W.v k).2 = (W.v (k + 1)).2 := snd_eq_of_step_fst_ne hk hne
    have hleft : ∀ {m m' : ℕ}, m ≤ W.n → (W.v m).1 = vmin1 W → m' ≤ W.n →
        (W.v m').1 = vmax1 W → (W.v m).2 = (W.v m').2 → (W.v m).2 = vmin2 W := by
      intro m m' hm h1 hm' h2 heq
      have h1' : vmin2 W ≤ (W.v m).2 := vmin2_le W hm h1
      have h2' : (W.v m').2 ≤ vmax2 W := le_vmax2 W hm' h2
      omega
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact absurd (hA.trans hB.symm) hne
    · left
      have hk2 : (W.v k).2 = vmin2 W := hleft (le_of_lt hk) hA (by omega) hB hh
      refine ⟨Prod.ext hA hk2, ?_⟩
      change W.v (k + 1) = vmax W
      refine Prod.ext hB ?_
      change (W.v (k + 1)).2 = vmax2 W
      omega
    · right
      have hk2 : (W.v (k + 1)).2 = vmin2 W := hleft (by omega) hB (le_of_lt hk) hA hh.symm
      refine ⟨?_, Prod.ext hB hk2⟩
      change W.v k = vmax W
      refine Prod.ext hA ?_
      change (W.v k).2 = vmax2 W
      omega
    · exact absurd (hA.trans hB.symm) hne
  -- there are at least two crossings
  set S : Finset ℕ := (Finset.range W.n).filter (fun k => (W.v k).1 ≠ (W.v (k + 1)).1) with hSdef
  have hSne : S.Nonempty := ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk0n, hk0ne⟩⟩
  have hcard_ne : S.card ≠ 1 := by
    intro hcard
    obtain ⟨k1, hk1⟩ := Finset.card_eq_one.mp hcard
    have hk1S : k1 ∈ S := by rw [hk1]; exact Finset.mem_singleton_self k1
    have hk1n : k1 < W.n := Finset.mem_range.mp (Finset.mem_filter.mp hk1S).1
    have hk1ne : (W.v k1).1 ≠ (W.v (k1 + 1)).1 := (Finset.mem_filter.mp hk1S).2
    have hno1 : ∀ k, 0 ≤ k → k < k1 → (W.v k).1 = (W.v (k + 1)).1 := by
      intro k _ hk
      by_contra h
      have hmem : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩
      rw [hk1, Finset.mem_singleton] at hmem
      omega
    have hno2 : ∀ k, k1 + 1 ≤ k → k < W.n → (W.v k).1 = (W.v (k + 1)).1 := by
      intro k hk1k hk
      by_contra h
      have hmem : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, h⟩
      rw [hk1, Finset.mem_singleton] at hmem
      omega
    have e1 : (W.v 0).1 = (W.v k1).1 :=
      fst_eq_of_no_change (a := 0) (b := k1) (Nat.zero_le _) (le_of_lt hk1n) hno1
    have e2 : (W.v (k1 + 1)).1 = (W.v W.n).1 :=
      fst_eq_of_no_change (a := k1 + 1) (b := W.n) (by omega) le_rfl hno2
    rw [W.closed] at e2
    exact hk1ne (e1.symm.trans e2.symm)
  have htwo : ∃ k1 ∈ S, ∃ k2 ∈ S, k1 < k2 := by
    have hpos : 0 < S.card := Finset.card_pos.mpr hSne
    obtain ⟨k1, hk1, k2, hk2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨k1, hk1, k2, hk2, h⟩
    · exact ⟨k2, hk2, k1, hk1, h⟩
  obtain ⟨k1, hk1S, k2, hk2S, hk12⟩ := htwo
  have hk1n : k1 < W.n := Finset.mem_range.mp (Finset.mem_filter.mp hk1S).1
  have hk2n : k2 < W.n := Finset.mem_range.mp (Finset.mem_filter.mp hk2S).1
  have hk1ne : (W.v k1).1 ≠ (W.v (k1 + 1)).1 := (Finset.mem_filter.mp hk1S).2
  have hk2ne : (W.v k2).1 ≠ (W.v (k2 + 1)).1 := (Finset.mem_filter.mp hk2S).2
  -- the four cases all give a non-trivial double point; we exhibit it for each
  have hne01 : (k1, k2) ≠ (0, W.n) := by
    intro h
    exact (by omega : k2 ≠ W.n) (Prod.ext_iff.mp h).2
  have hne02 : (k1 + 1, k2) ≠ (0, W.n) := by
    intro h
    exact (by omega : k1 + 1 ≠ 0) (Prod.ext_iff.mp h).1
  rcases hcv k1 hk1n hk1ne with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
    rcases hcv k2 hk2n hk2ne with ⟨a2, b2⟩ | ⟨a2, b2⟩
  · exact absurd (hW k1 k2 hk12 (le_of_lt hk2n) hne01 (a1.trans a2.symm)) (fun h => h)
  · by_cases hcase : (k1, k2 + 1) = (0, W.n)
    · have hk1' : k1 = 0 := (Prod.ext_iff.mp hcase).1
      have hk2' : k2 + 1 = W.n := (Prod.ext_iff.mp hcase).2
      exact (hW (k1 + 1) k2 (by omega) (le_of_lt hk2n) hne02 (b1.trans a2.symm))
    · exact absurd (hW k1 (k2 + 1) (by omega) (by omega) hcase (a1.trans b2.symm)) (fun h => h)
  · by_cases hcase : (k1, k2 + 1) = (0, W.n)
    · have hk1' : k1 = 0 := (Prod.ext_iff.mp hcase).1
      have hk2' : k2 + 1 = W.n := (Prod.ext_iff.mp hcase).2
      exact (hW (k1 + 1) k2 (by omega) (le_of_lt hk2n) hne02 (b1.trans a2.symm))
    · exact absurd (hW k1 (k2 + 1) (by omega) (by omega) hcase (a1.trans b2.symm)) (fun h => h)
  · exact absurd (hW k1 k2 hk12 (le_of_lt hk2n) hne01 (a1.trans a2.symm)) (fun h => h)

/-- **The lex-min vertex is below the opposite corner of the cell at the lex-max vertex.** -/
theorem lexmin_le_vmax_sub_one {W : LWalk} (hW : W.IsSimple) (hn : 4 ≤ W.n) :
    LexLe (vmin W) (vmax W - (1, 1)) := by
  rw [lexLe_iff]
  have hle : vmin1 W ≤ vmax1 W := by
    have h1 := vmin1_le W (Nat.zero_le W.n)
    have h2 := le_vmax1 W (Nat.zero_le W.n)
    omega
  have hne : vmin1 W ≠ vmax1 W := by
    intro h
    have hall : ∀ k ≤ W.n, (W.v k).1 = (W.v 0).1 := by
      intro k hk
      have h1 := vmin1_le W hk
      have h2 := le_vmax1 W hk
      have h0 : (W.v 0).1 = vmin1 W := by
        have h1' := vmin1_le W (Nat.zero_le W.n)
        have h2' := le_vmax1 W (Nat.zero_le W.n)
        omega
      omega
    obtain ⟨i, j, hij, hjn, hne, heq⟩ := exists_double_of_all_fst_eq (W := W) (by omega) hall
    exact (hW i j hij hjn hne) heq
  rcases lt_or_eq_of_le hle with hlt | heq
  · rcases eq_or_lt_of_le (show vmin1 W + 1 ≤ vmax1 W from hlt) with h2 | h2
    · right
      constructor
      · show vmin1 W = vmax1 W - 1
        omega
      · show vmin2 W ≤ vmax2 W - 1
        have h3 := vmin2_lt_vmax2_of_gap_one hW (by omega) h2
        omega
    · left
      show vmin1 W < vmax1 W - 1
      omega
  · exact absurd heq hne

end

end Work.Smooth.JordanSeparation
