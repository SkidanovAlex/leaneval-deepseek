import Mathlib.Data.Real.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Topology.Order

theorem exists_partition_refine_of_mem {a b : ℝ} {N : ℕ} {c : ℕ → ℝ}
    (hc0 : c 0 = a) (hcN : c N = b) (hmono : ∀ k < N, c k < c (k + 1)) {s : ℝ}
    (hs : s ∈ Set.Ioo a b) :
    ∃ (N' : ℕ) (c' : ℕ → ℝ), c' 0 = a ∧ c' N' = b ∧ (∀ k < N', c' k < c' (k + 1)) ∧
      (∃ m < N', c' m = s) ∧
      (∀ k < N', ∃ j < N, Set.Icc (c' k) (c' (k + 1)) ⊆ Set.Icc (c j) (c (j + 1))) := by
  obtain ⟨ha, hb⟩ := hs
  have hex : ∃ k, s < c k := ⟨N, by rw [hcN]; exact hb⟩
  set k0 := Nat.find hex with hk0def
  have hk0spec : s < c k0 := by rw [hk0def]; exact Nat.find_spec hex
  have hk0le : k0 ≤ N := by
    rw [hk0def]
    exact Nat.find_le (h := hex) (by rw [hcN]; exact hb)
  have hk0pos : 1 ≤ k0 := by
    rcases Nat.eq_zero_or_pos k0 with h | h
    · exfalso
      rw [h, hc0] at hk0spec
      exact (not_lt.mpr (le_of_lt ha)) hk0spec
    · exact h
  set j := k0 - 1 with hjdef
  have hjsucc : j + 1 = k0 := Nat.succ_pred_eq_of_pos (lt_of_lt_of_le Nat.zero_lt_one hk0pos)
  have hjltN : j < N := by
    have h : j + 1 ≤ N := by rw [hjsucc]; exact hk0le
    omega
  have hjk0 : j < k0 := by rw [← hjsucc]; exact Nat.lt_succ_self j
  have hcj_le : c j ≤ s := by
    have h : ¬ (s < c j) := Nat.find_min hex (by rwa [hk0def] at hjk0)
    exact not_lt.mp h
  have hcj1_gt : s < c (j + 1) := by rw [hjsucc]; exact hk0spec
  rcases lt_or_eq_of_le hcj_le with hlt | heq
  · -- c j < s : insert s
    let c' : ℕ → ℝ := fun k => if k ≤ j then c k else if k = j + 1 then s else c (k - 1)
    have hc'_le : ∀ k, k ≤ j → c' k = c k := by
      intro k hk
      show (if k ≤ j then c k else if k = j + 1 then s else c (k - 1)) = c k
      rw [if_pos hk]
    have hc'_eq : c' (j + 1) = s := by
      have h1 : ¬ ((j + 1 : ℕ) ≤ j) := by omega
      show (if (j + 1) ≤ j then c (j + 1) else if (j + 1) = j + 1 then s else c (j + 1 - 1)) = s
      rw [if_neg h1, if_pos rfl]
    have hc'_gt : ∀ k, j < k → k ≠ j + 1 → c' k = c (k - 1) := by
      intro k hk hkne
      have h1 : ¬ (k ≤ j) := not_le.mpr hk
      show (if k ≤ j then c k else if k = j + 1 then s else c (k - 1)) = c (k - 1)
      rw [if_neg h1, if_neg hkne]
    have hc'0 : c' 0 = a := by rw [hc'_le 0 (Nat.zero_le j), hc0]
    have hc'N : c' (N + 1) = b := by
      have hgt : j < N + 1 := by omega
      have hne : N + 1 ≠ j + 1 := by omega
      rw [hc'_gt (N + 1) hgt hne, Nat.add_sub_cancel, hcN]
    have hmono' : ∀ k < N + 1, c' k < c' (k + 1) := by
      intro k hkN
      rcases le_or_gt k j with hkj | hkj
      · rcases lt_or_eq_of_le hkj with hklt | hkeq
        · have h1 : k + 1 ≤ j := by omega
          rw [hc'_le k (le_of_lt hklt), hc'_le (k + 1) h1]
          exact hmono k (by omega)
        · rw [hkeq, hc'_le j (le_refl j), hc'_eq]
          exact hlt
      · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hkj) with hkeq | hklt
        · rw [← hkeq, hc'_eq, hc'_gt (j + 1 + 1) (by omega) (by omega), Nat.add_sub_cancel]
          exact hcj1_gt
        · have hkm : k ≠ j + 1 := by omega
          have h1 : k + 1 ≠ j + 1 := by omega
          rw [hc'_gt k hkj hkm, hc'_gt (k + 1) (by omega) h1, Nat.add_sub_cancel]
          have hm := hmono (k - 1) (by omega)
          rwa [Nat.sub_add_cancel (show 1 ≤ k by omega)] at hm
    have hcont : ∀ k < N + 1, ∃ j' < N,
        Set.Icc (c' k) (c' (k + 1)) ⊆ Set.Icc (c j') (c (j' + 1)) := by
      intro k hkN
      rcases le_or_gt k j with hkj | hkj
      · rcases lt_or_eq_of_le hkj with hklt | hkeq
        · have h1 : k + 1 ≤ j := by omega
          exact ⟨k, by omega, Set.Icc_subset_Icc (le_of_eq (hc'_le k (le_of_lt hklt)).symm)
            (le_of_eq (hc'_le (k + 1) h1))⟩
        · refine ⟨j, hjltN, ?_⟩
          rw [hkeq, hc'_le j (le_refl j), hc'_eq]
          exact Set.Icc_subset_Icc (le_refl _) (le_of_lt hcj1_gt)
      · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hkj) with hkeq | hklt
        · refine ⟨j, hjltN, ?_⟩
          rw [← hkeq, hc'_eq, hc'_gt (j + 1 + 1) (by omega) (by omega), Nat.add_sub_cancel]
          exact Set.Icc_subset_Icc (le_of_lt hlt) (le_refl _)
        · have hkm : k ≠ j + 1 := by omega
          have h1 : k + 1 ≠ j + 1 := by omega
          have e1 : c' k = c (k - 1) := hc'_gt k hkj hkm
          have e2 : c' (k + 1) = c k := by
            rw [hc'_gt (k + 1) (by omega) h1, Nat.add_sub_cancel]
          exact ⟨k - 1, by omega, Set.Icc_subset_Icc (le_of_eq e1.symm)
            (le_of_eq (e2.trans (congrArg c (Nat.sub_add_cancel (show 1 ≤ k by omega)).symm)))⟩
    exact ⟨N + 1, c', hc'0, hc'N, hmono', ⟨j + 1, by omega, hc'_eq⟩, hcont⟩
  · exact ⟨N, c, hc0, hcN, hmono, ⟨j, hjltN, heq⟩, fun k hk => ⟨k, hk, Set.Subset.refl _⟩⟩

end Commons.Topology.Order