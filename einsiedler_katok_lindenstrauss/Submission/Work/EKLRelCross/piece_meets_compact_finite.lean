import Mathlib
import Submission.Work.EKLRelCross.LeafCtor

namespace Work.EKLRelCross

open Work.EKLContract

/-! ## Elementary facts about the annuli `piece U k` -/

/-- The `k`-th annulus is contained in the subgroup `U`. -/
theorem piece_subset_U (U : Subgroup SL3) (k : ℕ) : piece U k ⊆ (U : Set SL3) := by
  cases k with
  | zero => intro g hg; exact hg.1
  | succ j =>
    intro g hg
    have hg' : g ∈ Ucl U ((j : ℝ) + 2) \ Ucl U ((j : ℝ) + 1) := by
      simpa only [piece] using hg
    exact hg'.1.1

/-- For `k ≥ 1` the annulus `piece U k` lies in the complement of the closed ball `Ucl U k`. -/
theorem piece_subset_compl_Ucl {U : Subgroup SL3} {k : ℕ} (hk : 1 ≤ k) :
    piece U k ⊆ (Ucl U (k : ℝ))ᶜ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
  intro g hg
  have hg' : g ∈ Ucl U ((j : ℝ) + 2) \ Ucl U ((j : ℝ) + 1) := by
    simpa only [piece] using hg
  rw [Set.mem_compl_iff, hcast]
  exact hg'.2

/-- A compact subset of `SL₃(ℝ)` has bounded matrix entries. -/
theorem exists_entry_bound {K : Set SL3} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ g ∈ K, ∀ i j : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ B := by
  classical
  by_cases hne : K.Nonempty
  · have hper : ∀ p : Fin 3 × Fin 3, ∃ B : ℝ,
        ∀ g ∈ K, |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| ≤ B := by
      intro p
      have hc : IsCompact ((fun g : SL3 => |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) '' K) :=
        hK.image (by fun_prop)
      obtain ⟨B, hB⟩ := hc.bddAbove
      exact ⟨B, fun g hg => hB ⟨g, hg, rfl⟩⟩
    choose Bf hBf using hper
    refine ⟨(Finset.univ : Finset (Fin 3 × Fin 3)).sup' Finset.univ_nonempty (fun p => Bf p),
      fun g hg i j => ?_⟩
    exact le_trans (hBf (i, j) g hg)
      (Finset.le_sup' (fun p : Fin 3 × Fin 3 => Bf p) (Finset.mem_univ (i, j)))
  · exact ⟨0, fun g hg => absurd ⟨g, hg⟩ hne⟩

/-- **The target lemma.**  A compact subset of `SL₃(ℝ)` meets only finitely many of the annuli
`piece U k`: `K ∩ piece U k = ∅` for all sufficiently large `k`. -/
theorem piece_meets_compact_finite {U : Subgroup Work.EKLContract.SL3} {K : Set Work.EKLContract.SL3}
    (hK : IsCompact K) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → K ∩ Work.EKLRelCross.piece U k = ∅ := by
  obtain ⟨B, hB⟩ := exists_entry_bound hK
  refine ⟨Nat.ceil B + 1, fun k hk => ?_⟩
  have hkB : B + 1 ≤ (k : ℝ) := by
    have h1 : B + 1 ≤ ((Nat.ceil B : ℕ) : ℝ) + 1 := add_le_add (Nat.le_ceil B) le_rfl
    have h2 : ((Nat.ceil B + 1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    rw [Nat.cast_add, Nat.cast_one] at h2
    exact le_trans h1 h2
  have hk1 : 1 ≤ k :=
    le_trans (by rw [Nat.add_comm]; exact Nat.le_add_right _ _) hk
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro g ⟨hgK, hgp⟩
  exact piece_subset_compl_Ucl hk1 hgp
    ⟨piece_subset_U U k hgp, fun i j => by
      have hb : |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ B := hB g hgK i j
      have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ (1 : ℝ) := by
        rw [Matrix.one_apply]; split <;> simp
      calc |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          ≤ |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
            simpa using abs_sub_le ((g : Matrix (Fin 3) (Fin 3) ℝ) i j) 0
              ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
        _ ≤ B + 1 := add_le_add hb hone
        _ ≤ (k : ℝ) := hkB⟩

end Work.EKLRelCross
