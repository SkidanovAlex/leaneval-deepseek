import Mathlib
import Submission.Work.ELRig.countable_zeros_of_analyticOn
import Submission.Work.ELRig.odd_ncard_zeros_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set Function Filter

theorem countable_deriv_zero_of_analyticOn {f : ℝ → ℝ} {a b : ℝ}
    (hf : AnalyticOn ℝ f (Set.Ioo a b)) (hne : ¬ ∀ x ∈ Set.Ioo a b, deriv f x = 0) :
    ({x : ℝ | x ∈ Set.Ioo a b ∧ deriv f x = 0}).Countable := by
  have h1 : AnalyticOn ℝ (deriv f) (Set.Ioo a b) := fun x hx =>
    ((hf.analyticAt (Ioo_mem_nhds hx.1 hx.2)).deriv).analyticWithinAt
  exact countable_zeros_of_analyticOn h1 hne

theorem exists_lt_notMem_of_countable {S : Set ℝ} {R : ℝ} (hS : S.Countable) :
    ∃ x₀ : ℝ, x₀ < -R ∧ x₀ ∉ S := by
  by_contra h
  push Not at h
  have hsub : Set.Iio (-R) ⊆ S := fun x hx => h x hx
  have hcount : (Set.Iio (-R)).Countable := hS.mono hsub
  have hc : Cardinal.mk (Set.Iio (-R)) ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0_iff.mpr hcount
  rw [Cardinal.mk_Iio_real] at hc
  exact absurd hc (not_le.mpr Cardinal.aleph0_lt_continuum)

theorem false_of_eqOn_const_Ioo {u : ℝ → ℝ} (hcont : Continuous u)
    (hper : ∀ s : ℝ, u (s + 1) = u s + 1) (n : ℤ) {c : ℝ}
    (h : ∀ s ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1), u s = c) : False := by
  have hab : (n : ℝ) ≠ (n : ℝ) + 1 := by norm_num
  have hcl := Set.EqOn.closure (f := u) (g := fun _ => c) (fun s hs => h s hs) hcont
      continuous_const
  rw [closure_Ioo hab] at hcl
  have h1 : u (n : ℝ) = c := hcl (left_mem_Icc.mpr (by norm_num))
  have h2 : u ((n : ℝ) + 1) = c := hcl (right_mem_Icc.mpr (by norm_num))
  have hp := hper (n : ℝ)
  linarith

theorem odd_transversal_level {γ : ℝ → ℂ} {R : ℝ}
    (hcont : Continuous γ) (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1)
    (han : ∀ n : ℤ, AnalyticOn ℝ (fun s : ℝ => γ s) (Set.Ioo (n : ℝ) ((n : ℝ) + 1))) :
    ∃ x₀ : ℝ, x₀ < -R ∧ Odd (Set.ncard {s : ℝ | (γ s).re = x₀}) ∧
      ∀ s : ℝ, (γ s).re = x₀ → deriv (fun t : ℝ => (γ t).re) s ≠ 0 := by
  set u : ℝ → ℝ := fun s => (γ s).re with hu
  have hu_cont : Continuous u := by
    rw [hu]; simpa [Function.comp_def] using Complex.continuous_re.comp hcont
  have hu_per : ∀ s : ℝ, u (s + 1) = u s + 1 := by
    intro s
    simp only [hu]
    rw [hper s]
    simp
  have hu_an : ∀ n : ℤ, AnalyticOn ℝ u (Set.Ioo (n : ℝ) ((n : ℝ) + 1)) := by
    intro n
    rw [hu]
    simpa [Function.comp_def] using Complex.reCLM.comp_analyticOn (han n)
  have hnotconst : ∀ (n : ℤ) (c : ℝ), ¬ (∀ s ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1), u s = c) :=
    fun n c h => false_of_eqOn_const_Ioo hu_cont hu_per n h
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ s : ℝ, |u s - s| ≤ M := by
    have hpv : Function.Periodic (fun s : ℝ => u s - s) 1 := by
      intro s
      show u (s + 1) - (s + 1) = u s - s
      rw [hu_per s]; ring
    have hbc : Continuous (fun s : ℝ => u s - s) := hu_cont.sub continuous_id
    have hb := hpv.isBounded_of_continuous (by norm_num) hbc
    obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp hb
    refine ⟨C + |u 0|, fun s => ?_⟩
    have h0 : dist (u s - s) (u 0 - 0) ≤ C := hC s 0
    rw [Real.dist_eq] at h0
    calc |u s - s| = |((u s - s) - (u 0 - 0)) + (u 0 - 0)| := by ring_nf
      _ ≤ |(u s - s) - (u 0 - 0)| + |u 0 - 0| := abs_add_le _ _
      _ = |(u s - s) - (u 0 - 0)| + |u 0| := by rw [sub_zero]
      _ ≤ C + |u 0| := add_le_add h0 le_rfl
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (u 0 - 0)) (hM 0)
  -- the derivative of `u` is not identically zero on any unit interval
  have hne_deriv : ∀ k : ℤ, ¬ ∀ x ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1), deriv u x = 0 := by
    intro k hcon
    have hmem : (k : ℝ) + 1/3 ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1) := by
      constructor <;> norm_num
    exact hnotconst k (u ((k : ℝ) + 1/3)) (fun x hx =>
      IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
        (hu_an k).differentiableOn (fun y hy => hcon y hy) hx hmem)
  -- the set of critical points is countable
  have hCPcount : ({s : ℝ | deriv u s = 0} : Set ℝ).Countable := by
    have hcover : {s : ℝ | deriv u s = 0}
        = ⋃ k : ℤ, {s : ℝ | (k : ℝ) ≤ s ∧ s < (k : ℝ) + 1 ∧ deriv u s = 0} := by
      ext s
      simp only [mem_iUnion]
      constructor
      · intro hs
        exact ⟨Int.floor s, Int.floor_le s, Int.lt_floor_add_one s, hs⟩
      · rintro ⟨_, _, _, h3⟩; exact h3
    rw [hcover]
    apply Set.countable_iUnion
    intro k
    have hsub2 : ({s : ℝ | (k : ℝ) ≤ s ∧ s < (k : ℝ) + 1 ∧ deriv u s = 0} : Set ℝ)
        ⊆ ({(k : ℝ)} : Set ℝ)
          ∪ {s : ℝ | s ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1) ∧ deriv u s = 0} := by
      intro s hs
      rcases hs with ⟨h1, h2, h3⟩
      rcases eq_or_lt_of_le h1 with hh | hh
      · exact Or.inl hh.symm
      · exact Or.inr ⟨⟨hh, h2⟩, h3⟩
    exact Set.Countable.mono hsub2 (Set.Countable.union (Set.finite_singleton _).countable
      (countable_deriv_zero_of_analyticOn (hu_an k) (hne_deriv k)))
  -- levels to avoid
  have hCV : (u '' {s : ℝ | deriv u s = 0}).Countable := hCPcount.image u
  have hIV : (u '' (Set.range (fun k : ℤ => (k : ℝ)))).Countable :=
    (Set.countable_range (fun k : ℤ => (k : ℝ))).image u
  obtain ⟨x₀, hx₀lt, hx₀B⟩ := exists_lt_notMem_of_countable (R := R) (hCV.union hIV)
  have hx₀CV : x₀ ∉ u '' {s : ℝ | deriv u s = 0} := fun h => hx₀B (Or.inl h)
  have hx₀IV : x₀ ∉ u '' (Set.range (fun k : ℤ => (k : ℝ))) := fun h => hx₀B (Or.inr h)
  -- any level point is not an integer
  have not_int_of : ∀ {x : ℝ}, u x = x₀ → ∀ k : ℤ, x ≠ (k : ℝ) := by
    intro x hx k hk
    exact hx₀IV ⟨(k : ℝ), ⟨k, rfl⟩, by rw [← hk]; exact hx⟩
  have exists_Ioo_of : ∀ {x : ℝ}, (∀ k : ℤ, x ≠ (k : ℝ)) →
      ∃ k : ℤ, x ∈ Set.Ioo (k : ℝ) ((k : ℝ) + 1) := by
    intro x hx
    exact ⟨Int.floor x, lt_of_le_of_ne (Int.floor_le x) (fun h => hx (Int.floor x) h.symm),
      Int.lt_floor_add_one x⟩
  have haz_of : ∀ x : ℝ, u x = x₀ → AnalyticAt ℝ u x := by
    intro x hx
    obtain ⟨k, hk⟩ := exists_Ioo_of (not_int_of hx)
    exact (hu_an k).analyticAt (Ioo_mem_nhds hk.1 hk.2)
  have hderiv_ne_of : ∀ x : ℝ, u x = x₀ → deriv u x ≠ 0 := by
    intro x hx h0
    exact hx₀CV ⟨x, h0, hx⟩
  -- the level set is finite
  have hLclosed : IsClosed {s : ℝ | u s = x₀} := isClosed_eq hu_cont continuous_const
  have hLsub : {s : ℝ | u s = x₀} ⊆ Set.Icc (x₀ - M) (x₀ + M) := by
    intro s hs
    have hs' : u s = x₀ := hs
    have h := hM s
    rw [hs'] at h
    rw [abs_le] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hLcompact : IsCompact {s : ℝ | u s = x₀} :=
    isCompact_Icc.of_isClosed_subset hLclosed hLsub
  have hcod : {s : ℝ | u s ≠ x₀} ∈ Filter.codiscreteWithin {s : ℝ | u s = x₀} := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro z hz
    obtain ⟨k, hk⟩ := exists_Ioo_of (not_int_of hz)
    have haz : AnalyticAt ℝ u z := (hu_an k).analyticAt (Ioo_mem_nhds hk.1 hk.2)
    rcases haz.eventually_eq_or_eventually_ne (analyticAt_const (v := x₀)) with h1 | h2
    · exfalso
      refine hnotconst k x₀ (fun x hx => ?_)
      have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
        (fun y hy => (hu_an k).analyticAt (Ioo_mem_nhds hy.1 hy.2))
        (fun y hy => analyticAt_const (v := x₀)) isPreconnected_Ioo hk h1
      exact hEqOn hx
    · exact mem_of_superset h2 Set.subset_union_left
  have hLfin : ({s : ℝ | u s = x₀} : Set ℝ).Finite := by
    have h := hLcompact.finite_sdiff_of_mem_codiscreteWithin hcod
    convert h using 1
    ext s
    simp
  refine ⟨x₀, hx₀lt, ?_, ?_⟩
  · have heq : {s : ℝ | (γ s).re = x₀} = {s : ℝ | u s = x₀} := by
      ext s; simp [hu]
    rw [heq]
    have hab : x₀ - M - 1 < x₀ + M + 1 := by linarith [hM0]
    have hcont' : ContinuousOn (fun t : ℝ => u t - x₀)
        (Set.Icc (x₀ - M - 1) (x₀ + M + 1)) :=
      (hu_cont.sub continuous_const).continuousOn
    have hfin' : ({s : ℝ | u s - x₀ = 0} : Set ℝ).Finite := by
      simpa only [sub_eq_zero] using hLfin
    have hsub' : ({s : ℝ | u s - x₀ = 0} : Set ℝ)
        ⊆ Set.Ioo (x₀ - M - 1) (x₀ + M + 1) := by
      intro s hs
      have hs' : u s = x₀ := sub_eq_zero.mp hs
      have h := hM s
      rw [hs'] at h
      rw [abs_le] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have hsimple' : ∀ s : ℝ, u s - x₀ = 0 →
        ∃ d : ℝ, d ≠ 0 ∧ HasDerivAt (fun t : ℝ => u t - x₀) d s := by
      intro s hs
      have hs' : u s = x₀ := sub_eq_zero.mp hs
      exact ⟨deriv u s, hderiv_ne_of s hs',
        (haz_of s hs').hasStrictDerivAt.hasDerivAt.sub_const x₀⟩
    have hiff := odd_ncard_zeros_iff (g := fun t : ℝ => u t - x₀) hab hcont' hfin' hsub' hsimple'
    have hga : u (x₀ - M - 1) - x₀ < 0 := by
      have h := (abs_le.mp (hM (x₀ - M - 1))).2
      linarith
    have hgb : 0 < u (x₀ + M + 1) - x₀ := by
      have h := (abs_le.mp (hM (x₀ + M + 1))).1
      linarith
    have hprod : (u (x₀ - M - 1) - x₀) * (u (x₀ + M + 1) - x₀) < 0 :=
      mul_neg_of_neg_of_pos hga hgb
    have hodd := hiff.mpr hprod
    simpa only [sub_eq_zero] using hodd
  · intro s hs
    have : deriv u s ≠ 0 := hderiv_ne_of s (by rw [hu]; exact hs)
    simpa only [hu] using this

end Work.ELRig
