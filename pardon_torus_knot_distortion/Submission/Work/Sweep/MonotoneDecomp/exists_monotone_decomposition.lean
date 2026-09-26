import Mathlib

/-!
# A monotone decomposition of a `C¹` function on an interval

Given `f f' : ℝ → ℝ`, a pointwise within-derivative hypothesis
`HasDerivWithinAt f (f' t) (Icc a b) t` on `[a, b]`, and continuity of `f'` on `[a, b]`,
we produce

* a compact set `C ⊆ [a, b]` containing the zero set of `f'` on `[a, b]` and contained in
  `{f' = 0} ∪ {a, b}`, and
* a countable, pairwise disjoint, measurable family `D : ℕ → Set ℝ` covering `[a, b] \ C`
  on every member of which `f'` is nonzero and `f` is strictly monotone (increasing or
  decreasing).

The construction is the natural one.  `C` is the (compact) zero set of `f'` together with
the two endpoints.  The complement `A = [a, b] \ C` is open in `ℝ`, and on every connected
piece of `A` the continuous function `f'` has constant sign, so `f` is strictly monotone
there.  To index the pieces we use the countable family of closed intervals `[r, s]` with
`r, s ∈ ℚ` that are contained in `A`: each point of `A` lies in such an interval, and such
an interval lies inside a single connected piece of `A`.  A greedy `disjointed` enumeration
turns that cover into a pairwise disjoint one.
-/

open Set MeasureTheory

noncomputable section

namespace Work.Sweep.MonotoneDecomp

/-- The closed interval with rational endpoints `p.1`, `p.2`, when it is contained in `A`,
and the empty set otherwise.  These are the blocks out of which the monotone decomposition
is built. -/
noncomputable def blockOf (A : Set ℝ) (p : ℚ × ℚ) : Set ℝ := by
  classical
  exact if (Set.Icc (p.1 : ℝ) (p.2 : ℝ)) ⊆ A then Set.Icc (p.1 : ℝ) (p.2 : ℝ) else ∅

/-- On an interval `[x, y]` on which a continuous real function never vanishes, the function
has constant sign. -/
lemma sign_const_on_Icc {g : ℝ → ℝ} {x y : ℝ}
    (hcont : ContinuousOn g (Set.Icc x y)) (hne : ∀ z ∈ Set.Icc x y, g z ≠ 0) :
    (∀ z ∈ Set.Icc x y, 0 < g z) ∨ (∀ z ∈ Set.Icc x y, g z < 0) := by
  by_cases hxy : x ≤ y
  · have hxmem : x ∈ Set.Icc x y := ⟨le_rfl, hxy⟩
    rcases lt_or_gt_of_ne (hne x hxmem) with hxneg | hxpos
    · right
      intro z hz
      by_contra h
      have hz' : 0 < g z := by
        rcases lt_trichotomy (g z) 0 with h' | h' | h'
        · exact absurd h' h
        · exact absurd h' (hne z hz)
        · exact h'
      obtain ⟨c, hc, hc0⟩ := (isPreconnected_Icc (a := x) (b := y)).intermediate_value₂ hxmem hz
        hcont continuousOn_const (le_of_lt hxneg) (le_of_lt hz')
      exact hne c hc hc0
    · left
      intro z hz
      by_contra h
      have hz' : g z < 0 := by
        rcases lt_trichotomy (g z) 0 with h' | h' | h'
        · exact h'
        · exact absurd h' (hne z hz)
        · exact absurd h' h
      obtain ⟨c, hc, hc0⟩ := (isPreconnected_Icc (a := x) (b := y)).intermediate_value₂ hz hxmem
        hcont continuousOn_const (le_of_lt hz') (le_of_lt hxpos)
      exact hne c hc hc0
  · left
    intro z hz
    exact absurd (le_trans hz.1 hz.2) hxy

/-- Mean value theorem corollary: if `f` has positive within-derivative `f'` on `Ioo a b`
and `[x, y] ⊆ Ioo a b`, then `f` is strictly increasing on `[x, y]`. -/
lemma strictMonoOn_Icc_of_hasDerivAt_pos {f f' : ℝ → ℝ} {a b x y : ℝ}
    (hsub : Set.Icc x y ⊆ Set.Ioo a b)
    (hder : ∀ t ∈ Set.Ioo a b, HasDerivAt f (f' t) t)
    (hpos : ∀ t ∈ Set.Icc x y, 0 < f' t) : StrictMonoOn f (Set.Icc x y) := by
  intro u hu v hv huv
  have hIccuv : Set.Icc u v ⊆ Set.Ioo a b := (Set.Icc_subset_Icc hu.1 hv.2).trans hsub
  have hcontIoo : ContinuousOn f (Set.Ioo a b) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hcont : ContinuousOn f (Set.Icc u v) := hcontIoo.mono hIccuv
  have hderat : ∀ t ∈ Set.Ioo u v, HasDerivAt f (f' t) t :=
    fun t ht => hder t (hIccuv ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope f f' huv hcont hderat
  have hcpos : 0 < f' c := hpos c ⟨hu.1.trans (le_of_lt hc.1), (le_of_lt hc.2).trans hv.2⟩
  rw [hsl] at hcpos
  have hden : 0 < v - u := sub_pos.mpr huv
  have : 0 < f v - f u := (div_pos_iff_of_pos_right hden).mp hcpos
  linarith

/-- Mean value theorem corollary: if `f` has negative within-derivative `f'` on `Ioo a b`
and `[x, y] ⊆ Ioo a b`, then `f` is strictly decreasing on `[x, y]`. -/
lemma strictAntiOn_Icc_of_hasDerivAt_neg {f f' : ℝ → ℝ} {a b x y : ℝ}
    (hsub : Set.Icc x y ⊆ Set.Ioo a b)
    (hder : ∀ t ∈ Set.Ioo a b, HasDerivAt f (f' t) t)
    (hneg : ∀ t ∈ Set.Icc x y, f' t < 0) : StrictAntiOn f (Set.Icc x y) := by
  intro u hu v hv huv
  have hIccuv : Set.Icc u v ⊆ Set.Ioo a b := (Set.Icc_subset_Icc hu.1 hv.2).trans hsub
  have hcontIoo : ContinuousOn f (Set.Ioo a b) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hcont : ContinuousOn f (Set.Icc u v) := hcontIoo.mono hIccuv
  have hderat : ∀ t ∈ Set.Ioo u v, HasDerivAt f (f' t) t :=
    fun t ht => hder t (hIccuv ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope f f' huv hcont hderat
  have hcneg : f' c < 0 := hneg c ⟨hu.1.trans (le_of_lt hc.1), (le_of_lt hc.2).trans hv.2⟩
  rw [hsl] at hcneg
  have hden : 0 < v - u := sub_pos.mpr huv
  have : f v - f u < 0 := by
    rcases div_neg_iff.mp hcneg with ⟨-, h⟩ | ⟨h, -⟩
    · linarith
    · exact h
  linarith

/-- The complement of the zero set of `f'` (and of the endpoints) inside `[a, b]` can be
covered by a countable pairwise disjoint family of measurable sets, on each of which `f'`
does not vanish and `f` is strictly monotone. -/
lemma decomp_aux (f f' : ℝ → ℝ) (a b : ℝ) (_hab : a ≤ b)
    (hf' : ∀ t ∈ Set.Icc a b, HasDerivWithinAt f (f' t) (Set.Icc a b) t)
    (hcont : ContinuousOn f' (Set.Icc a b)) :
    ∃ D : ℕ → Set ℝ,
      (∀ n, MeasurableSet (D n)) ∧
      Pairwise (Function.onFun Disjoint D) ∧
      (∀ n, D n ⊆ Set.Icc a b) ∧
      (∀ n, ∀ t ∈ D n, f' t ≠ 0) ∧
      (⋃ n, D n) = Set.Icc a b \ ({t ∈ Set.Icc a b | f' t = 0} ∪ {a, b}) ∧
      (∀ n, StrictMonoOn f (D n) ∨ StrictAntiOn f (D n)) := by
  classical
  set Z : Set ℝ := {t ∈ Set.Icc a b | f' t = 0} with hZ
  set C : Set ℝ := Z ∪ {a, b} with hC
  set A : Set ℝ := Set.Icc a b \ C with hA
  have hZclosed : IsClosed Z := by
    rw [hZ]
    have h := hcont.preimage_isClosed_of_isClosed isClosed_Icc
      (show IsClosed ({0} : Set ℝ) from isClosed_singleton)
    rw [show Set.Icc a b ∩ f' ⁻¹' {0} = {t : ℝ | t ∈ Set.Icc a b ∧ f' t = 0} from by
      ext t; simp [Set.mem_singleton_iff]] at h
    exact h
  have hCclosed : IsClosed C := by
    rw [hC]
    exact hZclosed.union (((Set.finite_singleton b).insert a).isClosed)
  have hac : a ∈ C := by rw [hC]; exact Or.inr (Or.inl rfl)
  have hbc : b ∈ C := by rw [hC]; exact Or.inr (Or.inr rfl)
  have hA_sub : A ⊆ Set.Icc a b := by
    intro t ht
    rw [hA] at ht
    exact ht.1
  have hA_Ioo : A ⊆ Set.Ioo a b := by
    intro t ht
    have htI : t ∈ Set.Icc a b := hA_sub ht
    have htC : t ∉ C := by rw [hA] at ht; exact ht.2
    refine ⟨?_, ?_⟩
    · rcases lt_or_eq_of_le htI.1 with h | h
      · exact h
      · exact absurd (h ▸ hac) htC
    · rcases lt_or_eq_of_le htI.2 with h | h
      · exact h
      · exact absurd (h ▸ hbc) htC
  have hAnz : ∀ t ∈ A, f' t ≠ 0 := by
    intro t ht hzero
    have htI : t ∈ Set.Icc a b := hA_sub ht
    have htC : t ∉ C := by rw [hA] at ht; exact ht.2
    exact htC (by rw [hC]; exact Or.inl (by rw [hZ]; exact ⟨htI, hzero⟩))
  have hAeq : A = Set.Ioo a b ∩ Cᶜ := by
    ext t; constructor
    · intro ht
      exact ⟨hA_Ioo ht, by rw [hA] at ht; exact ht.2⟩
    · rintro ⟨htIoo, htC⟩
      rw [hA]
      exact ⟨Set.Ioo_subset_Icc_self htIoo, htC⟩
  have hAopen : IsOpen A := by
    rw [hAeq]
    exact isOpen_Ioo.inter hCclosed.isOpen_compl
  have hderAt : ∀ t ∈ Set.Ioo a b, HasDerivAt f (f' t) t :=
    fun t ht => (hf' t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℚ × ℚ, Function.Surjective e := exists_surjective_nat (ℚ × ℚ)
  have hblocks_sub : ∀ n, blockOf A (e n) ⊆ A := by
    intro n
    by_cases h : Set.Icc ((e n).1 : ℝ) ((e n).2 : ℝ) ⊆ A
    · rw [blockOf, if_pos h]; exact h
    · rw [blockOf, if_neg h]; exact empty_subset _
  have hblocks_meas : ∀ n, MeasurableSet (blockOf A (e n)) := by
    intro n
    by_cases h : Set.Icc ((e n).1 : ℝ) ((e n).2 : ℝ) ⊆ A
    · rw [blockOf, if_pos h]; exact measurableSet_Icc
    · rw [blockOf, if_neg h]; exact MeasurableSet.empty
  have hcover : ∀ t ∈ A, ∃ n, t ∈ blockOf A (e n) := by
    intro t ht
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hAopen t ht
    rw [Real.ball_eq_Ioo] at hεsub
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show t - ε < t by linarith)
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show t < t + ε by linarith)
    obtain ⟨n, hn⟩ := he (r, s)
    refine ⟨n, ?_⟩
    rw [hn, blockOf, if_pos ?_]
    · exact ⟨le_of_lt hr2, le_of_lt hs1⟩
    · intro z hz
      exact hεsub ⟨by linarith [hz.1, hr1], by linarith [hz.2, hs2]⟩
  have hEmono : ∀ n, StrictMonoOn f (blockOf A (e n)) ∨ StrictAntiOn f (blockOf A (e n)) := by
    intro n
    by_cases h : Set.Icc ((e n).1 : ℝ) ((e n).2 : ℝ) ⊆ A
    · rw [blockOf, if_pos h]
      have hsub : Set.Icc ((e n).1 : ℝ) ((e n).2 : ℝ) ⊆ Set.Ioo a b := h.trans hA_Ioo
      have hcont' : ContinuousOn f' (Set.Icc ((e n).1 : ℝ) ((e n).2 : ℝ)) :=
        hcont.mono (h.trans hA_sub)
      have hne' : ∀ z ∈ Set.Icc ((e n).1 : ℝ) ((e n).2 : ℝ), f' z ≠ 0 :=
        fun z hz => hAnz z (h hz)
      rcases sign_const_on_Icc hcont' hne' with hpos | hneg
      · exact Or.inl (strictMonoOn_Icc_of_hasDerivAt_pos hsub hderAt hpos)
      · exact Or.inr (strictAntiOn_Icc_of_hasDerivAt_neg hsub hderAt hneg)
    · rw [blockOf, if_neg h]
      exact Or.inl (by intro x hx; exact absurd hx (Set.notMem_empty x))
  have hUnion : (⋃ n, blockOf A (e n)) = A := by
    refine le_antisymm (Set.iUnion_subset hblocks_sub) ?_
    intro t ht
    obtain ⟨n, hn⟩ := hcover t ht
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  refine ⟨disjointed (fun n => blockOf A (e n)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n => MeasurableSet.disjointed hblocks_meas n
  · exact disjoint_disjointed _
  · intro n
    exact (disjointed_subset _ n).trans ((hblocks_sub n).trans hA_sub)
  · intro n t ht
    exact hAnz t (hblocks_sub n ((disjointed_subset _ n) ht))
  · rw [iUnion_disjointed, hUnion, hA, hC]
  · intro n
    exact (hEmono n).imp (fun hh => hh.mono (disjointed_subset _ n))
      (fun hh => hh.mono (disjointed_subset _ n))

theorem exists_monotone_decomposition (f f' : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf' : ∀ t ∈ Set.Icc a b, HasDerivWithinAt f (f' t) (Set.Icc a b) t)
    (hcont : ContinuousOn f' (Set.Icc a b)) :
    ∃ (C : Set ℝ) (D : ℕ → Set ℝ),
      IsCompact C ∧
      C ⊆ Set.Icc a b ∧
      {t ∈ Set.Icc a b | f' t = 0} ⊆ C ∧
      C ⊆ {t : ℝ | f' t = 0} ∪ {a, b} ∧
      (∀ n, MeasurableSet (D n)) ∧
      Pairwise (Function.onFun Disjoint D) ∧
      (∀ n, D n ⊆ Set.Icc a b) ∧
      Disjoint C (⋃ n, D n) ∧
      C ∪ (⋃ n, D n) = Set.Icc a b ∧
      (∀ n, ∀ t ∈ D n, f' t ≠ 0) ∧
      (∀ n, StrictMonoOn f (D n) ∨ StrictAntiOn f (D n)) := by
  obtain ⟨D, hDmeas, hDdisj, hDsub, hDne, hDunion, hDmono⟩ :=
    decomp_aux f f' a b hab hf' hcont
  have hZclosed : IsClosed {t ∈ Set.Icc a b | f' t = 0} := by
    have h := hcont.preimage_isClosed_of_isClosed isClosed_Icc
      (show IsClosed ({0} : Set ℝ) from isClosed_singleton)
    rw [show Set.Icc a b ∩ f' ⁻¹' {0} = {t : ℝ | t ∈ Set.Icc a b ∧ f' t = 0} from by
      ext t; simp [Set.mem_singleton_iff]] at h
    exact h
  have hZcomp : IsCompact {t ∈ Set.Icc a b | f' t = 0} :=
    IsCompact.of_isClosed_subset isCompact_Icc hZclosed (fun _ ht => ht.1)
  have hCcomp : IsCompact ({t ∈ Set.Icc a b | f' t = 0} ∪ {a, b}) :=
    hZcomp.union (((Set.finite_singleton b).insert a).isCompact)
  have hCsub : ({t ∈ Set.Icc a b | f' t = 0} ∪ {a, b}) ⊆ Set.Icc a b := by
    refine Set.union_subset (fun _ ht => ht.1) ?_
    rintro t (rfl | rfl)
    · exact ⟨le_rfl, hab⟩
    · exact ⟨hab, le_rfl⟩
  refine ⟨{t ∈ Set.Icc a b | f' t = 0} ∪ {a, b}, D, hCcomp, hCsub, ?_, ?_, hDmeas, hDdisj,
    hDsub, ?_, ?_, hDne, hDmono⟩
  · exact Set.subset_union_left
  · exact Set.union_subset (fun _ ht => Or.inl ht.2) Set.subset_union_right
  · rw [hDunion]
    exact disjoint_sdiff_right
  · rw [hDunion]
    exact Set.union_sdiff_cancel hCsub

end Work.Sweep.MonotoneDecomp
