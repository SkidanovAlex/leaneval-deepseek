import Mathlib

namespace Work.WilG4c

/-- Mean value inequality on an open interval, for a function with values in a normed space.

If `f` is continuous on the closed interval `[x, y]`, differentiable on the open interval
`(x, y)` with derivative `f'`, and `‖f' t‖ ≤ C` there, then `‖f y - f x‖ ≤ C * (y - x)`.

The differentiability assumption is only made on the *open* interval, so the standard
`norm_image_sub_le_of_norm_deriv_right_le_segment` (which requires a right derivative at the left
endpoint) cannot be applied directly.  Instead we apply it on `[a, y]` for `a ∈ (x, y)`, which
gives `‖f y - f a‖ ≤ C * (y - a) ≤ C * (y - x)` whenever `C ≥ 0`, and then let `a → x⁺` using the
continuity of `f` on `[x, y]` (via an `ε`-argument). -/
lemma mvt_open {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {C x y : ℝ} (hxy : x ≤ y)
    (hcont : ContinuousOn f (Set.Icc x y))
    (hdiff : ∀ t ∈ Set.Ioo x y, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Set.Ioo x y, ‖f' t‖ ≤ C) :
    ‖f y - f x‖ ≤ C * (y - x) := by
  rcases lt_or_eq_of_le hxy with hlt | heq
  · -- `C ≥ 0` because `(x, y)` is nonempty.
    have hC : 0 ≤ C := le_trans (norm_nonneg _) (hbound ((x+y)/2) ⟨by linarith, by linarith⟩)
    -- The mean value inequality on `[a, y]` for every `a ∈ (x, y)`.
    have hseg : ∀ a ∈ Set.Ioo x y, ‖f y - f a‖ ≤ C * (y - x) := by
      intro a ha
      have hcont' : ContinuousOn f (Set.Icc a y) :=
        hcont.mono (Set.Icc_subset_Icc ha.1.le le_rfl)
      have hder'' : ∀ t ∈ Set.Ico a y, HasDerivWithinAt f (f' t) (Set.Ici t) t := fun t ht =>
        (hdiff t ⟨lt_of_lt_of_le ha.1 ht.1, ht.2⟩).hasDerivWithinAt
      have hbnd' : ∀ t ∈ Set.Ico a y, ‖f' t‖ ≤ C := fun t ht =>
        hbound t ⟨lt_of_lt_of_le ha.1 ht.1, ht.2⟩
      have h1 := norm_image_sub_le_of_norm_deriv_right_le_segment (a := a) (b := y)
        hcont' hder'' hbnd' y ⟨ha.2.le, le_rfl⟩
      calc ‖f y - f a‖ ≤ C * (y - a) := h1
        _ ≤ C * (y - x) := mul_le_mul_of_nonneg_left (by linarith [ha.1]) hC
    -- Pass to the limit `a → x⁺`.
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hcw : ContinuousWithinAt f (Set.Icc x y) x := hcont x ⟨le_rfl, hxy⟩
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousWithinAt_iff.mp hcw) ε hε
    set ρ : ℝ := min δ (y - x) / 2 with hρdef
    have hminpos : 0 < min δ (y - x) := lt_min hδpos (by linarith)
    have hρpos : 0 < ρ := by rw [hρdef]; positivity
    have hρlt : ρ < δ := by
      rw [hρdef]
      have : min δ (y - x) ≤ δ := min_le_left _ _
      linarith
    have hρy : x + ρ < y := by
      rw [hρdef]
      have : min δ (y - x) ≤ y - x := min_le_right _ _
      linarith
    have hρmem : x + ρ ∈ Set.Ioo x y := ⟨by linarith, hρy⟩
    have hdist : ‖f (x + ρ) - f x‖ < ε := by
      have hd := hδ (show x + ρ ∈ Set.Icc x y from ⟨by linarith, hρy.le⟩) (by
        have : dist (x + ρ) x = ρ := by
          rw [Real.dist_eq, show x + ρ - x = ρ by ring, abs_of_pos hρpos]
        rw [this]; exact hρlt)
      simpa only [dist_eq_norm] using hd
    have h1 : ‖f y - f (x + ρ)‖ ≤ C * (y - x) := hseg (x + ρ) hρmem
    calc ‖f y - f x‖
        = ‖(f y - f (x + ρ)) + (f (x + ρ) - f x)‖ := by
            rw [show f y - f x = (f y - f (x + ρ)) + (f (x + ρ) - f x) by abel]
      _ ≤ ‖f y - f (x + ρ)‖ + ‖f (x + ρ) - f x‖ := norm_add_le _ _
      _ ≤ C * (y - x) + ε := add_le_add h1 hdist.le
  · subst heq; simp

/-- **Mean value inequality with finitely many exceptional points.**

Let `f : ℝ → E` be continuous on `[a, b]` and differentiable with derivative `f'` at every
`t ∈ (a, b)` outside a finite set `T`, with `‖f' t‖ ≤ C` there.  Then
`‖f b - f a‖ ≤ C * (b - a)`.

The proof is by induction on the number of points of `T` strictly inside `(x, y)`: if there are
none, `mvt_open` applies directly; otherwise one splits `[x, y]` at an exceptional point `z` and
applies the induction hypothesis to `[x, z]` and `[z, y]`. -/
theorem norm_sub_le_of_hasDerivAt_off_finset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] :
    ∀ (T : Finset ℝ) (f f' : ℝ → E) (C a b : ℝ), a ≤ b →
    ContinuousOn f (Set.Icc a b) →
    (∀ t ∈ Set.Ioo a b, t ∉ (T : Set ℝ) → HasDerivAt f (f' t) t) →
    (∀ t ∈ Set.Ioo a b, t ∉ (T : Set ℝ) → ‖f' t‖ ≤ C) →
    ‖f b - f a‖ ≤ C * (b - a) := by
  intro T f f' C a b hab hcont hdiff hbound
  -- `key n` : the statement for pairs `x ≤ y` in `[a,b]` such that `(x,y)` contains at most `n`
  -- points of `T`.
  have key : ∀ n : ℕ, ∀ x y : ℝ, x ≤ y → x ∈ Set.Icc a b → y ∈ Set.Icc a b →
      (T.filter (fun p => x < p ∧ p < y)).card ≤ n → ‖f y - f x‖ ≤ C * (y - x) := by
    intro n
    induction n with
    | zero =>
      intro x y hxy hx hy hcard
      have hempty : T.filter (fun p => x < p ∧ p < y) = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      have hcont' : ContinuousOn f (Set.Icc x y) := hcont.mono (Set.Icc_subset_Icc hx.1 hy.2)
      refine mvt_open (f' := f') (C := C) (x := x) (y := y) hxy hcont' ?_ ?_
      · intro t ht
        exact hdiff t ⟨lt_of_le_of_lt hx.1 ht.1, lt_of_lt_of_le ht.2 hy.2⟩ (by
          intro htT
          have hmem : t ∈ T.filter (fun p => x < p ∧ p < y) :=
            Finset.mem_filter.mpr ⟨htT, ht.1, ht.2⟩
          rw [hempty] at hmem
          exact absurd hmem (by simp))
      · intro t ht
        exact hbound t ⟨lt_of_le_of_lt hx.1 ht.1, lt_of_lt_of_le ht.2 hy.2⟩ (by
          intro htT
          have hmem : t ∈ T.filter (fun p => x < p ∧ p < y) :=
            Finset.mem_filter.mpr ⟨htT, ht.1, ht.2⟩
          rw [hempty] at hmem
          exact absurd hmem (by simp))
    | succ n ih =>
      intro x y hxy hx hy hcard
      by_cases hle : (T.filter (fun p => x < p ∧ p < y)).card ≤ n
      · exact ih x y hxy hx hy hle
      · have hlt0 : n < (T.filter (fun p => x < p ∧ p < y)).card := not_le.mp hle
        have hcard' : (T.filter (fun p => x < p ∧ p < y)).card = n + 1 := by omega
        have hne : (T.filter (fun p => x < p ∧ p < y)).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hemp
          rw [hemp] at hcard'
          simp only [Finset.card_empty] at hcard'
          omega
        -- An exceptional point `z` strictly inside `(x, y)`.
        obtain ⟨z, hz⟩ := hne
        rw [Finset.mem_filter] at hz
        obtain ⟨hzs, hzx, hzy⟩ := hz
        have hzI : z ∈ Set.Icc a b := ⟨le_trans hx.1 hzx.le, le_trans hzy.le hy.2⟩
        -- The two halves have strictly fewer exceptional points.
        have hc1 : (T.filter (fun p => x < p ∧ p < z)).card ≤ n := by
          have hsub : T.filter (fun p => x < p ∧ p < z) ⊆ T.filter (fun p => x < p ∧ p < y) := by
            intro p hp
            rw [Finset.mem_filter] at hp ⊢
            exact ⟨hp.1, hp.2.1, lt_trans hp.2.2 hzy⟩
          have hne1 : T.filter (fun p => x < p ∧ p < z) ≠ T.filter (fun p => x < p ∧ p < y) := by
            intro h
            have hmem : z ∈ T.filter (fun p => x < p ∧ p < z) := by
              rw [h]; exact Finset.mem_filter.mpr ⟨hzs, hzx, hzy⟩
            rw [Finset.mem_filter] at hmem
            exact absurd hmem.2.2 (lt_irrefl z)
          have hlt' := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne1⟩)
          omega
        have hc2 : (T.filter (fun p => z < p ∧ p < y)).card ≤ n := by
          have hsub : T.filter (fun p => z < p ∧ p < y) ⊆ T.filter (fun p => x < p ∧ p < y) := by
            intro p hp
            rw [Finset.mem_filter] at hp ⊢
            exact ⟨hp.1, lt_trans hzx hp.2.1, hp.2.2⟩
          have hne2 : T.filter (fun p => z < p ∧ p < y) ≠ T.filter (fun p => x < p ∧ p < y) := by
            intro h
            have hmem : z ∈ T.filter (fun p => z < p ∧ p < y) := by
              rw [h]; exact Finset.mem_filter.mpr ⟨hzs, hzx, hzy⟩
            rw [Finset.mem_filter] at hmem
            exact absurd hmem.2.1 (lt_irrefl z)
          have hlt' := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne2⟩)
          omega
        have h1 := ih x z hzx.le hx hzI hc1
        have h2 := ih z y hzy.le hzI hy hc2
        calc ‖f y - f x‖ = ‖(f y - f z) + (f z - f x)‖ := by
              rw [show f y - f x = (f y - f z) + (f z - f x) by abel]
          _ ≤ ‖f y - f z‖ + ‖f z - f x‖ := norm_add_le _ _
          _ ≤ C * (y - z) + C * (z - x) := add_le_add h2 h1
          _ = C * (y - x) := by ring
  exact key T.card a b hab ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ (Finset.card_filter_le T (fun p => a < p ∧ p < b))

end Work.WilG4c
