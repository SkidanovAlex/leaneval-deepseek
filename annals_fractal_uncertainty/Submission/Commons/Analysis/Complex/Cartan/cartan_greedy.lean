import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.Analysis.Complex.Cartan

open scoped BigOperators

/-- The greedy-decomposition predicate for a subset `S` of the indices: a partition of `S` into
clusters with levels and centres as in `cartan_greedy`. -/
def CartanGreedyProp (n : ℕ) (a : Fin n → ℂ) (ρ : ℝ) (S : Finset (Fin n)) : Prop :=
  ∃ (J : Finset ℕ) (c : ℕ → ℂ) (lam : ℕ → ℕ) (cl : Fin n → ℕ),
    (∀ j ∈ J, 1 ≤ lam j) ∧
    (∀ i ∈ S, cl i ∈ J) ∧
    (∀ i ∈ S, ‖c (cl i) - a i‖ < (lam (cl i) : ℝ) * ρ) ∧
    (∀ j ∈ J, lam j ≤ (S.filter (fun i => cl i = j)).card) ∧
    (∑ j ∈ J, lam j ≤ S.card) ∧
    (∀ (k : ℕ) (z : ℂ), 1 ≤ k →
      k ≤ (S.filter (fun i => ‖z - a i‖ < (k : ℝ) * ρ)).card →
      ∃ i ∈ S, ‖z - a i‖ < (k : ℝ) * ρ ∧ k ≤ lam (cl i))

/-- **Greedy cluster decomposition underlying Cartan's lemma.**

Given `n ≥ 0` points `a : Fin n → ℂ` (possibly repeated) and a scale `ρ > 0`, one can partition
the index set into clusters. Each cluster `j` has a centre `c j` and an integer "level" `lam j ≥ 1`,
every index `i` of the cluster lies strictly inside the ball `B(c j, lam j · ρ)`, each cluster has at
least `lam j` members, the total of the levels is at most `n`, and the following *key counting
property* holds: whenever a ball of radius `k·ρ` contains at least `k` of the points, one of those
points lies in a cluster of level at least `k`. -/
theorem cartan_greedy (n : ℕ) (a : Fin n → ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (J : Finset ℕ) (c : ℕ → ℂ) (lam : ℕ → ℕ) (cl : Fin n → ℕ),
      (∀ j ∈ J, 1 ≤ lam j) ∧
      (∀ i, cl i ∈ J) ∧
      (∀ i, ‖c (cl i) - a i‖ < (lam (cl i) : ℝ) * ρ) ∧
      (∀ j ∈ J, lam j ≤ (Finset.univ.filter (fun i => cl i = j)).card) ∧
      (∑ j ∈ J, lam j ≤ n) ∧
      (∀ (k : ℕ) (z : ℂ), 1 ≤ k → k ≤ n →
        k ≤ (Finset.univ.filter (fun i => ‖z - a i‖ < (k : ℝ) * ρ)).card →
        ∃ i, ‖z - a i‖ < (k : ℝ) * ρ ∧ k ≤ lam (cl i)) := by
  classical
  have main : ∀ S : Finset (Fin n), CartanGreedyProp n a ρ S := by
    intro S
    suffices h : ∀ m, ∀ S : Finset (Fin n), S.card = m → CartanGreedyProp n a ρ S by
      exact h S.card S rfl
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro S hS
      by_cases hSempty : S = ∅
      · rw [hSempty]
        unfold CartanGreedyProp
        refine ⟨∅, fun _ => 0, fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro j hj; exact absurd hj (Finset.notMem_empty j)
        · intro i hi; exact absurd hi (Finset.notMem_empty i)
        · intro i hi; exact absurd hi (Finset.notMem_empty i)
        · intro j hj; exact absurd hj (Finset.notMem_empty j)
        · simp
        · intro k z hk hcard
          simp only [Finset.filter_empty, Finset.card_empty] at hcard
          omega
      · have hSnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSempty
        have hScardpos : 0 < S.card := Finset.card_pos.mpr hSnonempty
        let Good : ℕ → Prop := fun k => ∃ z : ℂ,
          k ≤ (S.filter (fun i => ‖z - a i‖ < (k : ℝ) * ρ)).card
        have hGood1 : Good 1 := by
          obtain ⟨i0, hi0⟩ := hSnonempty
          refine ⟨a i0, ?_⟩
          have hmem : i0 ∈ S.filter (fun i => ‖a i0 - a i‖ < ((1:ℕ):ℝ) * ρ) := by
            rw [Finset.mem_filter]
            refine ⟨hi0, ?_⟩
            have h0 : ‖a i0 - a i0‖ = (0:ℝ) := by simp
            rw [h0]
            have h1ρ : (0:ℝ) < ((1:ℕ):ℝ) * ρ := by rw [Nat.cast_one, one_mul]; exact hρ
            exact h1ρ
          exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨i0, hmem⟩)
        let K := Nat.findGreatest Good S.card
        have hKgood : Good K :=
          Nat.findGreatest_spec (P := Good) (n := S.card) (m := 1) (by omega) hGood1
        have hKmax : ∀ k, Good k → k ≤ K := by
          intro k hk
          have hkle : k ≤ S.card := by
            obtain ⟨z, hz⟩ := hk
            exact le_trans hz (Finset.card_le_card (Finset.filter_subset _ _))
          exact Nat.le_findGreatest (P := Good) hkle hk
        have hK1 : 1 ≤ K := hKmax 1 hGood1
        obtain ⟨z0, hz0⟩ := hKgood
        let C : Finset (Fin n) := S.filter (fun i => ‖z0 - a i‖ < (K:ℝ) * ρ)
        have hCsubl : C ⊆ S := Finset.filter_subset _ _
        have hCcard : K ≤ C.card := hz0
        have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
        have hClt : (S \ C).card < m := by
          have hsub : S \ C ⊂ S := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨Finset.sdiff_subset, ?_⟩
            intro hEq
            obtain ⟨i, hiC⟩ := hCne
            have hiS : i ∈ S := hCsubl hiC
            have h2 : i ∈ S \ C := by rw [hEq]; exact hiS
            exact (Finset.mem_sdiff.mp h2).2 hiC
          have := Finset.card_lt_card hsub
          omega
        obtain ⟨J₁, c₁, lam₁, cl₁, h1₁, h2₁, h3₁, h4₁, h5₁, h6₁⟩ :=
          ih (S \ C).card hClt (S \ C) rfl
        let j0 : ℕ := J₁.sup id + 1
        have hj0 : j0 ∉ J₁ := by
          intro hj
          have hle2 : j0 ≤ J₁.sup id := Finset.le_sup (f := id) hj
          simp only [j0] at hle2
          omega
        let J₂ : Finset ℕ := insert j0 J₁
        let c₂ : ℕ → ℂ := fun j => if j = j0 then z0 else c₁ j
        let lam₂ : ℕ → ℕ := fun j => if j = j0 then K else lam₁ j
        let cl₂ : Fin n → ℕ := fun i => if i ∈ C then j0 else cl₁ i
        have hlam2_j0 : lam₂ j0 = K := by simp [lam₂]
        have hlam2_ne : ∀ j, j ≠ j0 → lam₂ j = lam₁ j := by
          intro j hj; simp [lam₂, hj]
        have hc2_j0 : c₂ j0 = z0 := by simp [c₂]
        have hc2_ne : ∀ j, j ≠ j0 → c₂ j = c₁ j := by
          intro j hj; simp [c₂, hj]
        have hcl2_C : ∀ i, i ∈ C → cl₂ i = j0 := by
          intro i hi; simp [cl₂, hi]
        have hcl2_notC : ∀ i, i ∉ C → cl₂ i = cl₁ i := by
          intro i hi; simp [cl₂, hi]
        have hcl2_iff : ∀ i ∈ S, (cl₂ i = j0 ↔ i ∈ C) := by
          intro i hiS
          by_cases hiC : i ∈ C
          · rw [hcl2_C i hiC]; exact ⟨fun _ => hiC, fun _ => rfl⟩
          · rw [hcl2_notC i hiC]
            constructor
            · intro h
              exact absurd (h ▸ h2₁ i (Finset.mem_sdiff.mpr ⟨hiS, hiC⟩)) hj0
            · intro h; exact absurd h hiC
        refine ⟨J₂, c₂, lam₂, cl₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro j hj
          change j ∈ insert j0 J₁ at hj
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · rw [hlam2_j0]; exact hK1
          · rw [hlam2_ne j (fun h => hj0 (h ▸ hj))]; exact h1₁ j hj
        · intro i hiS
          by_cases hiC : i ∈ C
          · rw [hcl2_C i hiC]; exact Finset.mem_insert_self j0 J₁
          · rw [hcl2_notC i hiC]
            exact Finset.mem_insert_of_mem (h2₁ i (Finset.mem_sdiff.mpr ⟨hiS, hiC⟩))
        · intro i hiS
          by_cases hiC : i ∈ C
          · rw [hcl2_C i hiC, hc2_j0, hlam2_j0]
            exact (Finset.mem_filter.mp hiC).2
          · have hiSC : i ∈ S \ C := Finset.mem_sdiff.mpr ⟨hiS, hiC⟩
            have hmem : cl₁ i ∈ J₁ := h2₁ i hiSC
            have hne : cl₁ i ≠ j0 := fun h => hj0 (h ▸ hmem)
            rw [hcl2_notC i hiC, hc2_ne (cl₁ i) hne, hlam2_ne (cl₁ i) hne]
            exact h3₁ i hiSC
        · intro j hj
          change j ∈ insert j0 J₁ at hj
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · rw [hlam2_j0]
            have hset : S.filter (fun i => cl₂ i = j0) = C := by
              ext i
              rw [Finset.mem_filter]
              constructor
              · rintro ⟨hiS, hci⟩; exact (hcl2_iff i hiS).mp hci
              · intro hiC; exact ⟨hCsubl hiC, (hcl2_iff i (hCsubl hiC)).mpr hiC⟩
            rw [hset]; exact hCcard
          · have hne : j ≠ j0 := fun h => hj0 (h ▸ hj)
            rw [hlam2_ne j hne]
            refine le_trans (h4₁ j hj) (Finset.card_le_card ?_)
            intro i hi
            rw [Finset.mem_filter] at hi ⊢
            obtain ⟨hiSC, hci⟩ := hi
            exact ⟨(Finset.mem_sdiff.mp hiSC).1,
              by rw [hcl2_notC i (Finset.mem_sdiff.mp hiSC).2]; exact hci⟩
        · change (∑ j ∈ insert j0 J₁, lam₂ j) ≤ S.card
          rw [Finset.sum_insert hj0]
          rw [hlam2_j0]
          have hsum : (∑ j ∈ J₁, lam₂ j) = (∑ j ∈ J₁, lam₁ j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hlam2_ne j (fun h => hj0 (h ▸ hj))]
          rw [hsum]
          have hcard : (S \ C).card + C.card = S.card := Finset.card_sdiff_add_card_eq_card hCsubl
          omega
        · intro k z hk hcard
          have hGoodk : Good k := ⟨z, hcard⟩
          have hkK : k ≤ K := hKmax k hGoodk
          by_cases hInt : ∃ i ∈ S, ‖z - a i‖ < (k:ℝ) * ρ ∧ i ∈ C
          · obtain ⟨i, hiS, hik, hiC⟩ := hInt
            exact ⟨i, hiS, hik, by rw [hcl2_C i hiC, hlam2_j0]; exact hkK⟩
          · have hcard' : k ≤ ((S \ C).filter (fun i => ‖z - a i‖ < (k:ℝ) * ρ)).card := by
              refine le_trans hcard (Finset.card_le_card ?_)
              intro i hi
              rw [Finset.mem_filter] at hi ⊢
              obtain ⟨hiS, hik⟩ := hi
              exact ⟨Finset.mem_sdiff.mpr ⟨hiS, fun hiC => hInt ⟨i, hiS, hik, hiC⟩⟩, hik⟩
            obtain ⟨i, hiSC, hik, hlev⟩ := h6₁ k z hk hcard'
            refine ⟨i, (Finset.mem_sdiff.mp hiSC).1, hik, ?_⟩
            have hne : cl₁ i ≠ j0 := fun h => hj0 (h ▸ h2₁ i hiSC)
            rw [hcl2_notC i (Finset.mem_sdiff.mp hiSC).2, hlam2_ne (cl₁ i) hne]
            exact hlev
  have huniv := main Finset.univ
  simp only [CartanGreedyProp] at huniv
  obtain ⟨J, c, lam, cl, h1, h2, h3, h4, h5, h6⟩ := huniv
  refine ⟨J, c, lam, cl, h1, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact h2 i (Finset.mem_univ i)
  · intro i; exact h3 i (Finset.mem_univ i)
  · intro j hj; simpa using h4 j hj
  · simpa using h5
  · intro k z hk hkn hkcard
    obtain ⟨i, -, hi1, hi2⟩ := h6 k z hk (by simpa using hkcard)
    exact ⟨i, hi1, hi2⟩

end Commons.Analysis.Complex.Cartan