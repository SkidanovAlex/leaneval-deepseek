import Mathlib

namespace Work.CountedPinch

/-- **The endpoint of an embedded arc that already fills an open neighbourhood of itself has a
one-sided open neighbourhood whose punctured version is preconnected.**  If `f : [0,1] → Y` is
continuous and injective, `V` is open in `Y`, `f 0 ∈ V` and `V ⊆ range f`, then there is an open
`U ∋ f 0` with `U ⊆ V` and `U \ {f 0}` preconnected.

The witness is the germ of the arc: the image of the initial piece `{t < ε}` of the interval that
still lies in `V`; its openness in `Y` comes from the fact that `f` is a homeomorphism onto its
range (compact domain, Hausdorff codomain) together with `V ⊆ range f`, and its puncture is the
image of the preconnected set `(0,ε)`. -/
theorem oneSided_of_arcEndpoint {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : C(Set.Icc (0 : ℝ) 1, Y)) (hinj : Function.Injective f)
    {V : Set Y} (hV : IsOpen V) (hxV : f ⟨0, by norm_num⟩ ∈ V) (hVsub : V ⊆ Set.range f) :
    ∃ U : Set Y, IsOpen U ∧ f ⟨0, by norm_num⟩ ∈ U ∧ U ⊆ V ∧
      IsPreconnected (U \ {f ⟨0, by norm_num⟩}) := by
  -- The arc is a closed embedding: continuous, injective, compact domain, Hausdorff codomain.
  have hemb : Topology.IsClosedEmbedding (f : Set.Icc (0 : ℝ) 1 → Y) :=
    f.continuous.isClosedEmbedding hinj
  have hind : Topology.IsInducing (f : Set.Icc (0 : ℝ) 1 → Y) := hemb.isInducing
  -- `f ⁻¹' V` is an open neighbourhood of the left endpoint in `[0,1]`.
  have hWopen : IsOpen (f ⁻¹' V : Set (Set.Icc (0 : ℝ) 1)) := hV.preimage f.continuous
  have hx0W : (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈ f ⁻¹' V := hxV
  -- Its trace in `ℝ` supplies an ambient open `O`, hence a one-sided interval `[0,ε)` inside it.
  obtain ⟨O, hOopen, hOeq⟩ :=
    (Topology.IsInducing.subtypeVal (t := Set.Icc (0 : ℝ) 1)).isOpen_iff.mp hWopen
  have h0O : (0 : ℝ) ∈ O := by
    have h : (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈
        (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) ⁻¹' O := by
      rw [hOeq]; exact hx0W
    simpa using h
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (hOopen.mem_nhds h0O)
  set ε : ℝ := min δ 1 with hεdef
  have hεpos : 0 < ε := lt_min hδpos one_pos
  have hεle1 : ε ≤ 1 := min_le_right _ _
  have hεleδ : ε ≤ δ := min_le_left _ _
  have hmemV : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1), t < ε → f ⟨t, ht⟩ ∈ V := by
    intro t ht hlt
    have htball : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact lt_of_lt_of_le hlt hεleδ
    have htO : t ∈ O := hδsub htball
    have : (⟨t, ht⟩ : Set.Icc (0 : ℝ) 1) ∈
        (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) ⁻¹' O := htO
    rw [hOeq] at this
    exact this
  -- The initial piece of the interval that still lies in `V`, and its punctured version.
  set S : Set (Set.Icc (0 : ℝ) 1) := {t | (t : ℝ) < ε} with hSdef
  set T : Set (Set.Icc (0 : ℝ) 1) := {t | (t : ℝ) ∈ Set.Ioo (0 : ℝ) ε} with hTdef
  have hSopen : IsOpen S := by
    have hSe : S = (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) ⁻¹' Set.Iio ε := by
      ext t; rfl
    rw [hSe]
    exact isOpen_Iio.preimage continuous_subtype_val
  obtain ⟨O', hO'open, hO'eq⟩ := hind.isOpen_iff.mp hSopen
  refine ⟨O' ∩ V, hO'open.inter hV, ?_, Set.inter_subset_right, ?_⟩
  · -- `f 0` lies in the witness.
    refine ⟨?_, hxV⟩
    have : (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈ f ⁻¹' O' := by
      rw [hO'eq]
      show (0 : ℝ) < ε
      exact hεpos
    exact this
  · -- The witness is `f '' S`, and its puncture is `f '' T`.
    have hfS : f '' S = O' ∩ Set.range f := by
      rw [← hO'eq, Set.image_preimage_eq_inter_range]
    have hSsub : S ⊆ f ⁻¹' V := fun t ht => hmemV (t : ℝ) t.2 ht
    have hfSsubV : f '' S ⊆ V := by
      rintro y ⟨t, htS, rfl⟩
      exact hmemV (t : ℝ) t.2 htS
    have hOVEq : O' ∩ V = f '' S := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro y ⟨hyO', hyV⟩
        rw [hfS]
        exact ⟨hyO', hVsub hyV⟩
      · intro y hy
        have hy' : y ∈ O' ∩ Set.range f := hfS ▸ hy
        exact ⟨hy'.1, hfSsubV hy⟩
    have hdiff : f '' (S \ {⟨0, by norm_num⟩}) = (O' ∩ V) \ {f ⟨0, by norm_num⟩} := by
      rw [Set.image_sdiff hinj, Set.image_singleton, ← hOVEq]
    have hSdiff : S \ {⟨0, by norm_num⟩} = T := by
      ext t
      rw [Set.mem_sdiff, hSdef, hTdef]
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_Ioo]
      constructor
      · rintro ⟨htS, hne⟩
        have hne0 : (t : ℝ) ≠ 0 := fun h => hne (Subtype.ext (by rw [h]))
        exact ⟨lt_of_le_of_ne t.2.1 (Ne.symm hne0), htS⟩
      · rintro ⟨hpos, hlt⟩
        exact ⟨hlt, fun h => absurd (show (t : ℝ) = 0 by rw [h]) (ne_of_gt hpos)⟩
    have hTpc : IsPreconnected T := by
      have himg : (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) '' T = Set.Ioo (0 : ℝ) ε := by
        ext x
        constructor
        · rintro ⟨t, ht, rfl⟩; exact ht
        · intro hx
          exact ⟨⟨x, ⟨le_of_lt hx.1, le_trans (le_of_lt hx.2) hεle1⟩⟩, hx, rfl⟩
      exact ((Topology.IsInducing.subtypeVal (t := Set.Icc (0 : ℝ) 1)).isPreconnected_image
        (s := T)).mp (himg ▸ isPreconnected_Ioo)
    have hgoal : IsPreconnected (f '' T) :=
      hTpc.image (f : Set.Icc (0 : ℝ) 1 → Y) f.continuous.continuousOn
    rw [← hSdiff, hdiff] at hgoal
    exact hgoal

end Work.CountedPinch
