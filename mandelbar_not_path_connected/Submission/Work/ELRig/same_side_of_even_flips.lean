import Mathlib
import Submission.Work.ELRig.side_of_odd_crossings

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 2000000

noncomputable section

open Set

namespace Work.ELRig

/-- **Same side for an even number of flips.**  A continuous path `σ : ℝ → ℂ` which off a finite
set `T ⊂ (0, b)` runs inside `A ∪ B` (`A`, `B` open and disjoint), which swaps sides exactly at the
points of a subset `F ⊆ T` of *even* cardinality, and which preserves sides at the remaining points
of `T`, has `σ 0` and `σ b` on the same side; in particular `σ b ∈ A` forces `σ 0 ∈ A`. -/
theorem same_side_of_even_flips {A B : Set ℂ} {σ : ℝ → ℂ} {b : ℝ} {T F : Finset ℝ}
    (hA : IsOpen A) (hB : IsOpen B) (hdisj : Disjoint A B) (hσ : Continuous σ) (hb : 0 < b)
    (hT0 : ∀ t ∈ T, 0 < t) (hTb : ∀ t ∈ T, t < b) (hFT : ∀ t ∈ F, t ∈ T)
    (hFflip : ∀ t ∈ F, ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε → t + δ ∈ Set.Icc (0 : ℝ) b →
      t - δ ∈ Set.Icc (0 : ℝ) b → t + δ ∉ T → t - δ ∉ T →
      (σ (t + δ) ∈ A ∧ σ (t - δ) ∈ B) ∨ (σ (t + δ) ∈ B ∧ σ (t - δ) ∈ A))
    (hTnotF : ∀ t ∈ T, t ∉ F → ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε → t + δ ∈ Set.Icc (0 : ℝ) b →
      t - δ ∈ Set.Icc (0 : ℝ) b → t + δ ∉ T → t - δ ∉ T →
      (σ (t + δ) ∈ A ∧ σ (t - δ) ∈ A) ∨ (σ (t + δ) ∈ B ∧ σ (t - δ) ∈ B))
    (hoff : ∀ t ∈ Set.Icc (0 : ℝ) b, t ∉ T → σ t ∈ A ∪ B)
    (heven : Even F.card) (htop : σ b ∈ A) : σ 0 ∈ A := by
  classical
  by_cases hne : T.card = 0
  · -- `T` is empty: `[0, b]` is crossing free and connected
    have hTempty : T = ∅ := Finset.card_eq_zero.mp hne
    have h0I : (0:ℝ) ∈ Set.Icc (0:ℝ) b := ⟨le_rfl, le_of_lt hb⟩
    have hbI : b ∈ Set.Icc (0:ℝ) b := ⟨le_of_lt hb, le_rfl⟩
    have hnoT : ∀ u ∈ Set.Icc (0:ℝ) b, u ∉ T := by
      intro u hu; rw [hTempty]; simp
    exact (side_iff_of_Icc hA hB hdisj hσ hoff h0I hbI (le_of_lt hb) hnoT).mpr htop
  · set n := T.card with hn
    have hnpos : 0 < n := by rw [hn]; exact Nat.pos_of_ne_zero hne
    let a : Fin n ↪o ℝ := T.orderEmbOfFin hn.symm
    have ha_mono : StrictMono (a : Fin n → ℝ) := a.strictMono
    have ha_mem : ∀ i : Fin n, a i ∈ T := fun i => Finset.orderEmbOfFin_mem T hn.symm i
    have ha_range : Set.range (a : Fin n → ℝ) = (T : Set ℝ) := Finset.range_orderEmbOfFin T hn.symm
    have ha0 : ∀ i : Fin n, 0 < a i := fun i => hT0 _ (ha_mem i)
    have hab : ∀ i : Fin n, a i < b := fun i => hTb _ (ha_mem i)
    have hbpos : 0 < b := lt_trans (ha0 ⟨0, hnpos⟩) (hab ⟨0, hnpos⟩)
    -- every element of `T` is some `a i`
    have ht_range : ∀ t ∈ T, ∃ i : Fin n, a i = t := by
      intro t ht
      have hmem : t ∈ Set.range (a : Fin n → ℝ) := by rw [ha_range]; exact ht
      exact hmem
    -- basic size facts about the sample points
    have hp_ge0 : ∀ j, j ≤ n → 0 ≤ p n a b j := by
      intro j hj
      have h1 := (p_mem ha_mono ha0 hab hnpos hj).1
      have h2 := q_ge_zero ha0 hbpos j
      linarith
    have hp_le_b : ∀ j, j ≤ n → p n a b j ≤ b := by
      intro j hj
      have h1 := (p_mem ha_mono ha0 hab hnpos hj).2
      have h2 := q_le_b hab hbpos (j+1)
      linarith
    have hpI : ∀ j, j ≤ n → p n a b j ∈ Set.Icc (0:ℝ) b :=
      fun j hj => ⟨hp_ge0 j hj, hp_le_b j hj⟩
    -- the unique crossing in the `j`-th gap
    have hTmid : ∀ {j : ℕ} (hj : j < n) {u : ℝ},
        u ∈ Set.Icc (p n a b j) (p n a b (j+1)) → u ∈ T → u = a ⟨j, hj⟩ := by
      intro j hj u hu huT
      obtain ⟨i, hi⟩ := ht_range u huT
      have hqi : q n a b (i.val + 1) = u := (q_succ_of_lt i.isLt).trans hi
      have hpj : q n a b j < p n a b j := (p_mem ha_mono ha0 hab hnpos (le_of_lt hj)).1
      have hpj1 : p n a b (j+1) < q n a b (j+2) :=
        (p_mem ha_mono ha0 hab hnpos (by omega : j+1 ≤ n)).2
      have hlt1 : q n a b j < q n a b (i.val+1) := by rw [hqi]; exact lt_of_lt_of_le hpj hu.1
      have hlt2 : q n a b (i.val+1) < q n a b (j+2) := by rw [hqi]; exact lt_of_le_of_lt hu.2 hpj1
      have hji : j < i.val + 1 := by
        by_contra h
        push_neg at h
        exact absurd (q_mono_le ha_mono ha0 hab hnpos (i.val+1) j h (by omega)) (not_le.mpr hlt1)
      have hi2 : i.val + 1 < j + 2 := by
        by_contra h
        push_neg at h
        exact absurd (q_mono_le ha_mono ha0 hab hnpos (j+2) (i.val+1) h (by omega)) (not_le.mpr hlt2)
      have hiv : i.val = j := by omega
      have hfin : i = ⟨j, hj⟩ := Fin.ext hiv
      rw [hfin] at hi
      exact hi.symm
    -- everything in `T` is `> p 0`
    have hTle0 : ∀ t ∈ T, p n a b 0 < t := by
      intro t ht
      obtain ⟨i, hi⟩ := ht_range t ht
      have hqi : q n a b (i.val + 1) = t := (q_succ_of_lt i.isLt).trans hi
      have hle : q n a b 1 ≤ q n a b (i.val + 1) :=
        q_mono_le ha_mono ha0 hab hnpos 1 (i.val+1) (by omega) (by omega)
      have hpq : p n a b 0 < q n a b 1 := (p_mem ha_mono ha0 hab hnpos (by omega : 0 ≤ n)).2
      rw [hqi] at hle
      linarith
    -- everything in `T` is `< p n`
    have hTltn : ∀ t ∈ T, t < p n a b n := by
      intro t ht
      obtain ⟨i, hi⟩ := ht_range t ht
      have hqi : q n a b (i.val + 1) = t := (q_succ_of_lt i.isLt).trans hi
      have hle : q n a b (i.val + 1) ≤ q n a b n :=
        q_mono_le ha_mono ha0 hab hnpos (i.val+1) n (by omega) (by omega)
      have hqn : q n a b n < p n a b n := (p_mem ha_mono ha0 hab hnpos le_rfl).1
      rw [hqi] at hle
      linarith
    -- `P j` : the side of `σ` at the `j`-th sample point
    let P : ℕ → Prop := fun j => σ (p n a b j) ∈ A
    -- `σ b` is on the `A`-side, hence so is `p n`
    have hPn : P n := by
      have hbI : b ∈ Set.Icc (0:ℝ) b := ⟨le_of_lt hbpos, le_rfl⟩
      have hnoT : ∀ u ∈ Set.Icc (p n a b n) b, u ∉ T := by
        intro u hu huT
        exact absurd hu.1 (not_le.mpr (hTltn u huT))
      have := side_iff_of_Icc hA hB hdisj hσ hoff (hpI n le_rfl) hbI (hp_le_b n le_rfl) hnoT
      exact this.mpr htop
    -- `σ 0` is on the side of `p 0`
    have hP0 : (σ 0 ∈ A) ↔ P 0 := by
      have h0I : (0:ℝ) ∈ Set.Icc (0:ℝ) b := ⟨le_rfl, le_of_lt hbpos⟩
      have hnoT : ∀ u ∈ Set.Icc (0:ℝ) (p n a b 0), u ∉ T := by
        intro u hu huT
        exact absurd hu.2 (not_le.mpr (hTle0 u huT))
      exact side_iff_of_Icc hA hB hdisj hσ hoff h0I (hpI 0 (by omega)) (hp_ge0 0 (by omega)) hnoT
    -- the index set of flipping crossing times
    let K : Finset (Fin n) := Finset.univ.filter (fun i => a i ∈ F)
    have hKcard : K.card = F.card := by
      have himg : K.image (fun i => (a i : ℝ)) = F := by
        ext y
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, K]
        constructor
        · rintro ⟨i, hiF, rfl⟩; exact hiF
        · intro hyF
          have hyT : y ∈ T := hFT y hyF
          have hymem : y ∈ Set.range (a : Fin n → ℝ) := by rw [ha_range]; exact hyT
          obtain ⟨i, hi⟩ := hymem
          exact ⟨i, by rwa [← hi] at hyF, hi⟩
      have hc : (K.image (fun i => (a i : ℝ))).card = K.card :=
        Finset.card_image_of_injective (f := fun i => (a i : ℝ)) K
          (fun i j hij => a.injective hij)
      rw [himg] at hc
      exact hc.symm
    -- Conditional step relation: `P (j+1) ↔ (P j ↔ ¬ (j ∈ K))`
    have hstep : ∀ j (hj : j < n),
        (P (j+1) ↔ (P j ↔ ¬ ((⟨j, hj⟩ : Fin n) ∈ K))) := by
      intro j hj
      have hmemK : ((⟨j, hj⟩ : Fin n) ∈ K) ↔ (a ⟨j, hj⟩ ∈ F) := by
        simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      -- the geometric step common to both cases
      have common : ∀ (ε : ℝ), 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
            (a ⟨j, hj⟩ + δ ∈ Set.Icc (0:ℝ) b) ∧ (a ⟨j, hj⟩ - δ ∈ Set.Icc (0:ℝ) b) ∧
            (a ⟨j, hj⟩ + δ ∉ T) ∧ (a ⟨j, hj⟩ - δ ∉ T) ∧
            ((σ (a ⟨j, hj⟩ - δ) ∈ A) ↔ P j) ∧
            ((σ (a ⟨j, hj⟩ + δ) ∈ A) ↔ P (j+1)) := by
        intro ε hεpos
        set δ : ℝ := min (ε/2) (min ((q n a b (j+1) - p n a b j)/2)
                                       ((p n a b (j+1) - q n a b (j+1))/2)) with hδdef
        have hajq : a ⟨j, hj⟩ = q n a b (j+1) := (q_succ_of_lt hj).symm
        have hpj_qj : q n a b j < p n a b j := (p_mem ha_mono ha0 hab hnpos (le_of_lt hj)).1
        have hpj_qj1 : p n a b j < q n a b (j+1) := (p_mem ha_mono ha0 hab hnpos (le_of_lt hj)).2
        have hqj1_pj1 : q n a b (j+1) < p n a b (j+1) :=
          (p_mem ha_mono ha0 hab hnpos (by omega : j+1 ≤ n)).1
        have hδpos : 0 < δ := by
          rw [hδdef]; exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
        have hδε : δ < ε := by
          rw [hδdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hδA : δ < q n a b (j+1) - p n a b j := by
          rw [hδdef]
          exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
        have hδB : δ < p n a b (j+1) - q n a b (j+1) := by
          rw [hδdef]
          exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
        have hleft : p n a b j < a ⟨j, hj⟩ - δ := by rw [hajq]; linarith
        have hright : a ⟨j, hj⟩ + δ < p n a b (j+1) := by rw [hajq]; linarith
        have hIJ1 : a ⟨j, hj⟩ + δ ∈ Set.Icc (0:ℝ) b :=
          ⟨le_of_lt (by linarith [ha0 ⟨j, hj⟩, hδpos]),
           le_of_lt (lt_of_lt_of_le hright (hp_le_b (j+1) (by omega)))⟩
        have hIJ2 : a ⟨j, hj⟩ - δ ∈ Set.Icc (0:ℝ) b :=
          ⟨le_of_lt (lt_of_le_of_lt (hp_ge0 j (le_of_lt hj)) hleft),
           le_of_lt (lt_trans (by linarith [hδpos]) (hab ⟨j, hj⟩))⟩
        have hnotT1 : a ⟨j, hj⟩ + δ ∉ T := by
          intro hT
          have hmem : a ⟨j, hj⟩ + δ ∈ Set.Icc (p n a b j) (p n a b (j+1)) :=
            ⟨le_of_lt (by rw [hajq]; linarith), le_of_lt hright⟩
          have hthis := hTmid hj hmem hT
          linarith [hδpos]
        have hnotT2 : a ⟨j, hj⟩ - δ ∉ T := by
          intro hT
          have hmem : a ⟨j, hj⟩ - δ ∈ Set.Icc (p n a b j) (p n a b (j+1)) :=
            ⟨le_of_lt hleft, le_of_lt (by rw [hajq]; linarith)⟩
          have hthis := hTmid hj hmem hT
          linarith [hδpos]
        have hsideL : (σ (a ⟨j, hj⟩ - δ) ∈ A) ↔ P j := by
          have hnoT : ∀ u ∈ Set.Icc (p n a b j) (a ⟨j, hj⟩ - δ), u ∉ T := by
            intro u hu huT
            have hmem : u ∈ Set.Icc (p n a b j) (p n a b (j+1)) :=
              ⟨hu.1, le_of_lt (lt_of_le_of_lt hu.2 (by linarith [hright, hδpos]))⟩
            have hthis := hTmid hj hmem huT
            rw [hthis] at hu
            linarith [hu.2, hδpos]
          exact (side_iff_of_Icc hA hB hdisj hσ hoff (hpI j (le_of_lt hj)) hIJ2
            (le_of_lt hleft) hnoT).symm
        have hsideR : (σ (a ⟨j, hj⟩ + δ) ∈ A) ↔ P (j+1) := by
          have hnoT : ∀ u ∈ Set.Icc (a ⟨j, hj⟩ + δ) (p n a b (j+1)), u ∉ T := by
            intro u hu huT
            have hmem : u ∈ Set.Icc (p n a b j) (p n a b (j+1)) :=
              ⟨le_of_lt (lt_of_lt_of_le hleft (le_trans (by linarith [hδpos]) hu.1)), hu.2⟩
            have hthis := hTmid hj hmem huT
            rw [hthis] at hu
            linarith [hu.1, hδpos]
          exact side_iff_of_Icc hA hB hdisj hσ hoff hIJ1 (hpI (j+1) (by omega))
            (le_of_lt hright) hnoT
        exact ⟨δ, hδpos, hδε, hIJ1, hIJ2, hnotT1, hnotT2, hsideL, hsideR⟩
      by_cases hafF : a ⟨j, hj⟩ ∈ F
      · -- flipping crossing
        obtain ⟨ε, hεpos, hεflip⟩ := hFflip (a ⟨j, hj⟩) hafF
        obtain ⟨δ, hδpos, hδε, hIJ1, hIJ2, hnotT1, hnotT2, hsideL, hsideR⟩ := common ε hεpos
        have hfl := hεflip δ hδpos hδε hIJ1 hIJ2 hnotT1 hnotT2
        have hrel : P j ↔ ¬ P (j+1) := by
          rcases hfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · constructor
            · intro hpj
              exact absurd (hsideL.mpr hpj) (Set.disjoint_right.mp hdisj h2)
            · intro hpj1
              exact absurd (hsideR.mp h1) hpj1
          · constructor
            · intro _ hpj1
              exact absurd (hsideR.mpr hpj1) (Set.disjoint_right.mp hdisj h1)
            · intro _
              exact hsideL.mp h2
        have hK : (⟨j, hj⟩ : Fin n) ∈ K := hmemK.mpr hafF
        have hgoal : P (j+1) ↔ ¬ P j :=
          ⟨fun h1 hpj => hrel.mp hpj h1, fun hnpj => by by_contra h; exact hnpj (hrel.mpr h)⟩
        simpa [hK] using hgoal
      · -- non-flipping crossing
        obtain ⟨ε, hεpos, hεflip⟩ := hTnotF (a ⟨j, hj⟩) (ha_mem ⟨j, hj⟩) hafF
        obtain ⟨δ, hδpos, hδε, hIJ1, hIJ2, hnotT1, hnotT2, hsideL, hsideR⟩ := common ε hεpos
        have hfl := hεflip δ hδpos hδε hIJ1 hIJ2 hnotT1 hnotT2
        have hrel : P j ↔ P (j+1) := by
          rcases hfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨fun _ => hsideR.mp h1, fun _ => hsideL.mp h2⟩
          · exact ⟨fun hpj => absurd (hsideL.mpr hpj) (Set.disjoint_right.mp hdisj h2),
                   fun hpj1 => absurd (hsideR.mpr hpj1) (Set.disjoint_right.mp hdisj h1)⟩
        have hnotK : (⟨j, hj⟩ : Fin n) ∉ K := fun h => hafF (hmemK.mp h)
        simpa [hnotK] using hrel.symm
    -- the number of flips among the first `j` crossing times, as a cardinality over `Fin n`
    set G : ℕ → ℕ := (fun j => (K.filter (fun i : Fin n => i.val < j)).card) with hGdef
    have hG0 : G 0 = 0 := by simp [hGdef]
    have hGn : G n = F.card := by
      have hfull : K.filter (fun i : Fin n => i.val < n) = K := by
        ext i
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.1, fun h => ⟨h, i.isLt⟩⟩
      simp only [hGdef, hfull, hKcard]
    have hGstep : ∀ j (hj : j < n),
        G (j+1) = G j + (if (⟨j, hj⟩ : Fin n) ∈ K then 1 else 0) := by
      intro j hj
      simp only [hGdef]
      have hsplit : K.filter (fun i : Fin n => i.val < j+1) =
          K.filter (fun i : Fin n => i.val < j) ∪
            K.filter (fun i : Fin n => i = ⟨j, hj⟩) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hiK, hi⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact Or.inl ⟨hiK, h⟩
          · exact Or.inr ⟨hiK, Fin.ext h⟩
        · rintro (⟨hiK, h⟩ | ⟨hiK, h⟩)
          · exact ⟨hiK, Nat.lt_succ_of_lt h⟩
          · exact ⟨hiK, by rw [h]; exact Nat.lt_succ_self j⟩
      have hdisjK : Disjoint (K.filter (fun i : Fin n => i.val < j))
          (K.filter (fun i : Fin n => i = ⟨j, hj⟩)) := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        rw [Finset.mem_filter] at hi1 hi2
        have h2 : i.val = j := by rw [hi2.2]
        omega
      have hcard_last : (K.filter (fun i : Fin n => i = ⟨j, hj⟩)).card =
          if (⟨j, hj⟩ : Fin n) ∈ K then 1 else 0 := by
        rw [Finset.filter_eq' K ⟨j, hj⟩]
        by_cases hc : (⟨j, hj⟩ : Fin n) ∈ K
        · rw [if_pos hc, if_pos hc, Finset.card_singleton]
        · rw [if_neg hc, if_neg hc, Finset.card_empty]
      rw [hsplit, Finset.card_union_of_disjoint hdisjK, hcard_last]
    have hEven_step : ∀ j (hj : j < n),
        Even (G (j+1)) ↔ (Even (G j) ↔ ¬ ((⟨j, hj⟩ : Fin n) ∈ K)) := by
      intro j hj
      have h := hGstep j hj
      by_cases hc : (⟨j, hj⟩ : Fin n) ∈ K
      · rw [h, if_pos hc]
        simp only [hc, not_true, iff_false, Nat.even_add_one]
      · rw [h, if_neg hc]
        simp only [hc, not_false_eq_true, iff_true, Nat.add_zero]
    -- parity propagation from step 0
    have hpar : ∀ j, j ≤ n → (P j ↔ (P 0 ↔ Even (G j))) := by
      intro j
      induction j with
      | zero => intro _; rw [hG0]; simp
      | succ j ih =>
          intro hj
          have hj' : j < n := by omega
          have hih : P j ↔ (P 0 ↔ Even (G j)) := ih (by omega)
          rw [hstep j hj', hih, hEven_step j hj']
          tauto
    have hPn_true : P 0 ↔ Even (G n) := (hpar n le_rfl).mp hPn
    have hEn : Even (G n) := by rw [hGn]; exact heven
    exact hP0.mpr (hPn_true.mpr hEn)

end Work.ELRig
