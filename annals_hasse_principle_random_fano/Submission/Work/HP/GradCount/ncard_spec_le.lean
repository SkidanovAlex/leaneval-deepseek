import Mathlib

namespace Work.HP.GradCount

lemma int_card_Icc_cast (a b : ℤ) (hab : a ≤ b + 1) :
    ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
  have h := Int.card_Icc_of_le a b hab
  exact_mod_cast h

lemma ceil_le_floor_add_one (α β : ℝ) (h : α ≤ β) : ⌈α⌉ ≤ ⌊β⌋ + 1 := by
  have h1 : ((⌈α⌉ - 1 : ℤ) : ℝ) ≤ β := by
    have := Int.ceil_lt_add_one α
    push_cast
    linarith
  have h2 : (⌈α⌉ : ℤ) - 1 ≤ ⌊β⌋ := Int.le_floor.mpr h1
  omega

/-- A box of integer points cut out by one "special" coordinate `j` (with the `n` other coordinates
each confined to an affine interval of length `2C/u`, and coordinate `j` then confined to an affine
interval of length `2C/v`) has at most `(2C/u+2)^n * (2C/v+2)` elements. -/
theorem ncard_spec_le (n : ℕ) (j : Fin (n + 1)) (u v C : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hC : 0 ≤ C) (w A : Fin (n + 1) → ℝ) :
    (({c : Fin (n + 1) → ℤ |
        (∀ k : Fin (n + 1), k ≠ j → |(c k : ℝ) * u + A k| ≤ C) ∧
        |(c j : ℝ) * v + ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ) + A j| ≤ C} : Set _).ncard : ℝ)
      ≤ (2 * C / u + 2) ^ n * (2 * C / v + 2) := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Set (Fin (n + 1) → ℤ), S = {c : Fin (n + 1) → ℤ |
        (∀ k : Fin (n + 1), k ≠ j → |(c k : ℝ) * u + A k| ≤ C) ∧
        |(c j : ℝ) * v + ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ) + A j| ≤ C} := ⟨_, rfl⟩
  rw [← hS]
  have hSmem : ∀ c : Fin (n + 1) → ℤ, c ∈ S ↔
      ((∀ k : Fin (n + 1), k ≠ j → |(c k : ℝ) * u + A k| ≤ C) ∧
        |(c j : ℝ) * v + ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ) + A j| ≤ C) := by
    intro c; simp only [hS, Set.mem_ofPred_eq]
  let Wc : (Fin (n + 1) → ℤ) → ℝ := fun c => ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ)
  let lo : (Fin (n + 1) → ℤ) → ℤ := fun c => ⌈(-C - Wc c - A j) / v⌉
  let ρ : (Fin (n + 1) → ℤ) → ({k : Fin (n + 1) // k ≠ j} → ℤ) := fun c k => c k.1
  let φ : (Fin (n + 1) → ℤ) → ({k : Fin (n + 1) // k ≠ j} → ℤ) × ℤ := fun c => (ρ c, c j - lo c)
  have hWceq : ∀ c, Wc c = ∑ i ∈ Finset.univ.erase j, w i * (c i : ℝ) := fun c => rfl
  have hloeq : ∀ c, lo c = ⌈(-C - Wc c - A j) / v⌉ := fun c => rfl
  have hρapply : ∀ (c : Fin (n + 1) → ℤ) (k : {k : Fin (n + 1) // k ≠ j}), ρ c k = c k.1 :=
    fun c k => rfl
  have hρW : ∀ c c', ρ c = ρ c' → Wc c = Wc c' := by
    intro c c' h
    rw [hWceq c, hWceq c']
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have hci : c i = c' i := by
      have hh := congrFun h ⟨i, hij⟩
      simp only [hρapply] at hh
      simpa using hh
    rw [hci]
  have hφinj : Function.Injective φ := by
    intro c c' h
    have h1 : ρ c = ρ c' := by
      have := congrArg Prod.fst h
      simpa [φ] using this
    have h2 : c j - lo c = c' j - lo c' := by
      have := congrArg Prod.snd h
      simpa [φ] using this
    have hlo : lo c = lo c' := by rw [hloeq c, hloeq c', hρW c c' h1]
    have hcj : c j = c' j := by
      have hh := h2; rw [hlo] at hh; omega
    funext k
    by_cases hk : k = j
    · rw [hk]; exact hcj
    · have hh := congrFun h1 ⟨k, hk⟩
      simp only [hρapply] at hh
      simpa using hh
  have himg : φ '' S ⊆ (ρ '' S) ×ˢ (Set.Icc (0 : ℤ) ⌊2 * C / v⌋) := by
    rintro p ⟨c, hc, rfl⟩
    rw [Set.mem_prod]
    refine ⟨⟨c, hc, by simp [φ]⟩, ?_⟩
    change c j - lo c ∈ Set.Icc (0 : ℤ) ⌊2 * C / v⌋
    have hcond := (hSmem c).mp hc
    have hjc : |(c j : ℝ) * v + Wc c + A j| ≤ C := by
      rw [hWceq c]; exact hcond.2
    obtain ⟨hle, hge⟩ := abs_le.mp hjc
    rw [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · have hlo_le : lo c ≤ c j := by
        rw [hloeq c]
        apply Int.ceil_le.mpr
        rw [div_le_iff₀ hv]
        linarith
      omega
    · have hup : ((c j - lo c : ℤ) : ℝ) ≤ 2 * C / v := by
        have hcj_le : (c j : ℝ) ≤ (C - Wc c - A j) / v := by
          rw [le_div_iff₀ hv]; linarith
        have hlo_ge : ((-C - Wc c - A j) / v) ≤ (lo c : ℝ) := by
          rw [hloeq c]; exact Int.le_ceil _
        have hdiff : (C - Wc c - A j) / v - (-C - Wc c - A j) / v = 2 * C / v := by
          rw [sub_div]; ring
        push_cast
        linarith
      rw [Int.le_floor]
      exact hup
  let loI : ({k : Fin (n + 1) // k ≠ j} → ℤ) := fun k => ⌈(-C - A k.1) / u⌉
  let hiI : ({k : Fin (n + 1) // k ≠ j} → ℤ) := fun k => ⌊(C - A k.1) / u⌋
  have hloI : ∀ k, loI k = ⌈(-C - A k.1) / u⌉ := fun k => rfl
  have hhiI : ∀ k, hiI k = ⌊(C - A k.1) / u⌋ := fun k => rfl
  have hBsub : ρ '' S ⊆ Set.Icc loI hiI := by
    rintro t ⟨c, hc, rfl⟩
    rw [Set.mem_Icc]
    constructor
    · intro k
      have hcond := (hSmem c).mp hc
      have hle := (abs_le.mp (hcond.1 k.1 k.2)).1
      rw [hloI k]
      apply Int.ceil_le.mpr
      change (-C - A k.1) / u ≤ (c k.1 : ℝ)
      rw [div_le_iff₀ hu]
      linarith
    · intro k
      have hcond := (hSmem c).mp hc
      have hge := (abs_le.mp (hcond.1 k.1 k.2)).2
      rw [hhiI k]
      apply Int.le_floor.mpr
      change (c k.1 : ℝ) ≤ (C - A k.1) / u
      rw [le_div_iff₀ hu]
      linarith
  have hcardι : Fintype.card {k : Fin (n + 1) // k ≠ j} = n := by
    rw [Fintype.card_subtype_compl (p := fun k : Fin (n + 1) => k = j),
      Fintype.card_subtype_eq, Fintype.card_fin]
    omega
  have hBcard : ((ρ '' S).ncard : ℝ) ≤ (2 * C / u + 2) ^ n := by
    have h1 : (ρ '' S).ncard ≤ (Set.Icc loI hiI).ncard :=
      Set.ncard_le_ncard hBsub (Set.finite_Icc loI hiI)
    have h2 : (Set.Icc loI hiI).ncard = ∏ k, (Finset.Icc (loI k) (hiI k)).card := by
      rw [Set.ncard_Icc, Pi.card_Icc]
    have hfactor : ∀ k : {k : Fin (n + 1) // k ≠ j},
        ((Finset.Icc (loI k) (hiI k)).card : ℝ) ≤ 2 * C / u + 2 := by
      intro k
      have hαβ : (-C - A k.1) / u ≤ (C - A k.1) / u := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hu)
        linarith
      have hab : loI k ≤ hiI k + 1 := by
        rw [hloI k, hhiI k]
        exact ceil_le_floor_add_one _ _ hαβ
      rw [int_card_Icc_cast _ _ hab]
      have hi_le : ((hiI k : ℤ) : ℝ) ≤ (C - A k.1) / u := by
        rw [hhiI k]; exact Int.floor_le _
      have lo_ge : ((-C - A k.1) / u) ≤ ((loI k : ℤ) : ℝ) := by
        rw [hloI k]; exact Int.le_ceil _
      have hdiff : (C - A k.1) / u - (-C - A k.1) / u = 2 * C / u := by
        rw [sub_div]; ring
      linarith
    have h3 : (∏ k : {k : Fin (n + 1) // k ≠ j},
          ((Finset.Icc (loI k) (hiI k)).card : ℝ)) ≤
        ∏ k : {k : Fin (n + 1) // k ≠ j}, (2 * C / u + 2) := by
      apply Finset.prod_le_prod₀
      · intro k _; exact Nat.cast_nonneg _
      · intro k _; exact hfactor k
    have h4 : (∏ k : {k : Fin (n + 1) // k ≠ j}, (2 * C / u + 2)) = (2 * C / u + 2) ^ n := by
      rw [Finset.prod_const, Finset.card_univ, hcardι]
    calc ((ρ '' S).ncard : ℝ)
        ≤ ((Set.Icc loI hiI).ncard : ℝ) := by exact_mod_cast h1
      _ = ((∏ k, (Finset.Icc (loI k) (hiI k)).card : ℕ) : ℝ) := by rw [h2]
      _ = ∏ k, ((Finset.Icc (loI k) (hiI k)).card : ℝ) := by rw [Nat.cast_prod]
      _ ≤ ∏ k : {k : Fin (n + 1) // k ≠ j}, (2 * C / u + 2) := h3
      _ = (2 * C / u + 2) ^ n := h4
  have hIcc_card : ((Set.Icc (0 : ℤ) ⌊2 * C / v⌋).ncard : ℝ) ≤ 2 * C / v + 1 := by
    rw [Set.ncard_Icc]
    have h2Cv : (0 : ℝ) ≤ 2 * C / v := div_nonneg (by linarith) (le_of_lt hv)
    have hfn : (0 : ℤ) ≤ ⌊2 * C / v⌋ := by
      rw [Int.le_floor]; push_cast; linarith
    have hab : (0 : ℤ) ≤ ⌊2 * C / v⌋ + 1 := by omega
    rw [int_card_Icc_cast (0 : ℤ) ⌊2 * C / v⌋ hab]
    have := Int.floor_le (2 * C / v)
    push_cast
    linarith
  have hBfin : (ρ '' S).Finite := (Set.finite_Icc loI hiI).subset hBsub
  have himg_le : ((φ '' S).ncard : ℝ) ≤
      (((ρ '' S) ×ˢ Set.Icc (0 : ℤ) ⌊2 * C / v⌋).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard himg (hBfin.prod (Set.finite_Icc _ _))
  have h2Cu : (0 : ℝ) ≤ 2 * C / u + 2 := by
    have hh : (0 : ℝ) ≤ 2 * C / u := div_nonneg (by linarith) (le_of_lt hu)
    linarith
  have hmain : ((φ '' S).ncard : ℝ) ≤ (2 * C / u + 2) ^ n * (2 * C / v + 2) := by
    calc ((φ '' S).ncard : ℝ)
        ≤ (((ρ '' S) ×ˢ Set.Icc (0 : ℤ) ⌊2 * C / v⌋).ncard : ℝ) := himg_le
      _ = ((ρ '' S).ncard : ℝ) * ((Set.Icc (0 : ℤ) ⌊2 * C / v⌋).ncard : ℝ) := by
            rw [Set.ncard_prod]; push_cast; ring
      _ ≤ (2 * C / u + 2) ^ n * (2 * C / v + 1) := by
            exact mul_le_mul hBcard hIcc_card (Nat.cast_nonneg _) (pow_nonneg h2Cu n)
      _ ≤ (2 * C / u + 2) ^ n * (2 * C / v + 2) := by
            exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg h2Cu n)
  have hφcard : (S.ncard : ℝ) = ((φ '' S).ncard : ℝ) := by
    rw [← Set.ncard_image_of_injective S hφinj]
  rw [hφcard]
  exact hmain

end Work.HP.GradCount
