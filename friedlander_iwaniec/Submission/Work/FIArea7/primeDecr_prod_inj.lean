import Mathlib

namespace Work.FIArea7

/-- If `f` and `g` are both strictly decreasing (in the index order) families of primes
indexed by the elements of a finset `S`, and the products over `S` agree, then `f` and `g`
agree on `S`. -/
theorem primeDecr_prod_inj {k : ℕ} (S : Finset (Fin k)) {f g : Fin k → ℕ}
    (hf : ∀ i ∈ S, (f i).Prime) (hfd : ∀ i j, i ∈ S → j ∈ S → i < j → f j < f i)
    (hg : ∀ i ∈ S, (g i).Prime) (hgd : ∀ i j, i ∈ S → j ∈ S → i < j → g j < g i)
    (hprod : ∏ i ∈ S, f i = ∏ i ∈ S, g i) : ∀ i ∈ S, f i = g i := by
  classical
  suffices H : ∀ n (T : Finset (Fin k)), T.card = n →
      (∀ i ∈ T, (f i).Prime) → (∀ i j, i ∈ T → j ∈ T → i < j → f j < f i) →
      (∀ i ∈ T, (g i).Prime) → (∀ i j, i ∈ T → j ∈ T → i < j → g j < g i) →
      (∏ i ∈ T, f i = ∏ i ∈ T, g i) → ∀ i ∈ T, f i = g i by
    exact H S.card S rfl hf hfd hg hgd hprod
  intro n
  induction n with
  | zero =>
    intro T hcard _ _ _ _ _ i hi
    rw [Finset.card_eq_zero.mp hcard] at hi
    exact (Finset.notMem_empty i hi).elim
  | succ n ih =>
    intro T hcard hfT hfdT hgT hgdT hprodT
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨m, hmem, hmin⟩ : ∃ m ∈ T, ∀ j ∈ T, m ≤ j :=
      ⟨T.min' hne, T.min'_mem hne, fun j hj => T.min'_le j hj⟩
    -- `m` is the strict maximum of `f` and of `g` on `T`
    have hf_lt : ∀ j ∈ T, j ≠ m → f j < f m := by
      intro j hj hjne
      exact hfdT m j hmem hj (lt_of_le_of_ne (hmin j hj) (Ne.symm hjne))
    have hg_lt : ∀ j ∈ T, j ≠ m → g j < g m := by
      intro j hj hjne
      exact hgdT m j hmem hj (lt_of_le_of_ne (hmin j hj) (Ne.symm hjne))
    have hf_le : ∀ j ∈ T, f j ≤ f m := by
      intro j hj
      by_cases h : j = m
      · exact le_of_eq (by rw [h])
      · exact le_of_lt (hf_lt j hj h)
    have hg_le : ∀ j ∈ T, g j ≤ g m := by
      intro j hj
      by_cases h : j = m
      · exact le_of_eq (by rw [h])
      · exact le_of_lt (hg_lt j hj h)
    have hfmp : (f m).Prime := hfT m hmem
    have hgmp : (g m).Prime := hgT m hmem
    have hfm_dvd : f m ∣ ∏ i ∈ T, g i := by
      rw [← hprodT]; exact Finset.dvd_prod_of_mem f hmem
    obtain ⟨j, hj, hdj⟩ := (Nat.prime_iff.mp hfmp).dvd_finsetProd_iff g |>.mp hfm_dvd
    have hgj_eq : g j = f m := (hgT j hj).dvd_iff_eq hfmp.ne_one |>.mp hdj
    have hgm_dvd : g m ∣ ∏ i ∈ T, f i := by
      rw [hprodT]; exact Finset.dvd_prod_of_mem g hmem
    obtain ⟨j', hj', hdj'⟩ := (Nat.prime_iff.mp hgmp).dvd_finsetProd_iff f |>.mp hgm_dvd
    have hfj'_eq : f j' = g m := (hfT j' hj').dvd_iff_eq hgmp.ne_one |>.mp hdj'
    have hm_eq : f m = g m := by
      apply le_antisymm
      · calc f m = g j := hgj_eq.symm
          _ ≤ g m := hg_le j hj
      · calc g m = f j' := hfj'_eq.symm
          _ ≤ f m := hf_le j' hj'
    -- strip off `m` and apply the induction hypothesis
    have hcard' : (T.erase m).card = n := by
      rw [Finset.card_erase_of_mem hmem, hcard]; omega
    have hprod' : ∏ i ∈ T.erase m, f i = ∏ i ∈ T.erase m, g i := by
      have hfmul := Finset.mul_prod_erase T f hmem
      have hgmul := Finset.mul_prod_erase T g hmem
      have hkey : f m * (∏ i ∈ T.erase m, f i) = f m * (∏ i ∈ T.erase m, g i) := by
        calc f m * (∏ i ∈ T.erase m, f i)
            = ∏ i ∈ T, f i := hfmul
          _ = ∏ i ∈ T, g i := hprodT
          _ = g m * (∏ i ∈ T.erase m, g i) := hgmul.symm
          _ = f m * (∏ i ∈ T.erase m, g i) := by rw [← hm_eq]
      exact Nat.mul_left_cancel hfmp.pos hkey
    have hIH := ih (T.erase m) hcard'
      (fun i hi => hfT i (Finset.mem_of_mem_erase hi))
      (fun i j hi hj hij => hfdT i j (Finset.mem_of_mem_erase hi) (Finset.mem_of_mem_erase hj) hij)
      (fun i hi => hgT i (Finset.mem_of_mem_erase hi))
      (fun i j hi hj hij => hgdT i j (Finset.mem_of_mem_erase hi) (Finset.mem_of_mem_erase hj) hij)
      hprod'
    intro i hi
    by_cases h : i = m
    · rw [h]; exact hm_eq
    · exact hIH i (Finset.mem_erase.mpr ⟨h, hi⟩)

end Work.FIArea7
