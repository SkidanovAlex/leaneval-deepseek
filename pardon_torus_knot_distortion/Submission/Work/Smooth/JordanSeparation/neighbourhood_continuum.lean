import Mathlib

namespace Work.Smooth.JordanSeparation

open Set Metric
open scoped Topology

/-- **Limits of connected compact sets are connected.**

If `γ n` are preconnected subsets of a metric space `X` and `γ n` converges to the compact set `L`
in the Hausdorff (e)metric, then `L` is preconnected.  This is the Hausdorff-metric form of the
classical fact that the Hausdorff limit of connected sets is connected: if `L = A ⊔ B` were a
separation into closed nonempty pieces, the two pieces would be at positive distance `δ`, so for
large `n` the set `γ n` would be covered by the two disjoint open sets `thickening δ A` and
`thickening δ B` while meeting both, contradicting its preconnectedness. -/
theorem isPreconnected_of_tendsto_hausdorffEDist {X : Type*} [PseudoMetricSpace X] [T2Space X]
    {γ : ℕ → Set X} {L : Set X} (hL : IsCompact L) (hγ : ∀ n, IsPreconnected (γ n))
    (hconv : Filter.Tendsto (fun n => Metric.hausdorffEDist (γ n) L) Filter.atTop (𝓝 0)) :
    IsPreconnected L := by
  rcases L.eq_empty_or_nonempty with rfl | hLne
  · exact isPreconnected_empty
  intro u v hu hv huv hLu hLv
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hnem : ∀ x, x ∈ L → x ∈ u → x ∈ v → False := by
    intro x hxL hxu hxv
    have : x ∈ L ∩ (u ∩ v) := ⟨hxL, hxu, hxv⟩
    rw [hne] at this; exact this
  have hAc : IsClosed (L \ v) := hL.isClosed.sdiff hv
  have hBc : IsClosed (L \ u) := hL.isClosed.sdiff hu
  have hAk : IsCompact (L \ v) := hL.of_isClosed_subset hAc Set.sdiff_subset
  have hUnion : (L \ v) ∪ (L \ u) = L := by
    ext x; constructor
    · rintro (⟨hxL, -⟩ | ⟨hxL, -⟩) <;> exact hxL
    · intro hxL
      rcases huv hxL with hxu | hxv
      · left; exact ⟨hxL, fun hxv => hnem x hxL hxu hxv⟩
      · right; exact ⟨hxL, fun hxu => hnem x hxL hxu hxv⟩
  have hdisj : Disjoint (L \ v) (L \ u) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rcases huv hx1.1 with hxu | hxv
    · exact hx2.2 hxu
    · exact hx1.2 hxv
  have hAne : (L \ v).Nonempty := by
    obtain ⟨x, hxL, hxu⟩ := hLu
    exact ⟨x, hxL, fun hxv => hnem x hxL hxu hxv⟩
  have hBne : (L \ u).Nonempty := by
    obtain ⟨x, hxL, hxv⟩ := hLv
    exact ⟨x, hxL, fun hxu => hnem x hxL hxu hxv⟩
  obtain ⟨δ, hδpos, hδdisj⟩ := hdisj.exists_thickenings hAk hBc
  have hLunion : thickening δ (L \ v) ∪ thickening δ (L \ u) = thickening δ L := by
    rw [← Metric.thickening_union, hUnion]
  have hev : ∀ᶠ n in Filter.atTop, Metric.hausdorffEDist (γ n) L < ENNReal.ofReal δ :=
    (tendsto_order.1 hconv).2 (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδpos)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  have hsub : γ N ⊆ thickening δ (L \ v) ∪ thickening δ (L \ u) := by
    rw [hLunion]
    intro x hx
    exact (Metric.mem_thickening_iff_exists_edist_lt L x).mpr
      (Metric.exists_edist_lt_of_hausdorffEDist_lt hx (hN N le_rfl))
  have hneA : (γ N ∩ thickening δ (L \ v)).Nonempty := by
    obtain ⟨a, haL, hav⟩ := hAne
    have h1 : Metric.infEDist a (γ N) ≤ Metric.hausdorffEDist L (γ N) :=
      Metric.infEDist_le_hausdorffEDist_of_mem haL
    rw [Metric.hausdorffEDist_comm] at h1
    obtain ⟨x, hxγ, hxa⟩ := Metric.infEDist_lt_iff.mp (lt_of_le_of_lt h1 (hN N le_rfl))
    exact ⟨x, hxγ, (Metric.mem_thickening_iff_exists_edist_lt (L \ v) x).mpr
      ⟨a, ⟨haL, hav⟩, by rw [edist_comm]; exact hxa⟩⟩
  have hneB : (γ N ∩ thickening δ (L \ u)).Nonempty := by
    obtain ⟨a, haL, hau⟩ := hBne
    have h1 : Metric.infEDist a (γ N) ≤ Metric.hausdorffEDist L (γ N) :=
      Metric.infEDist_le_hausdorffEDist_of_mem haL
    rw [Metric.hausdorffEDist_comm] at h1
    obtain ⟨x, hxγ, hxa⟩ := Metric.infEDist_lt_iff.mp (lt_of_le_of_lt h1 (hN N le_rfl))
    exact ⟨x, hxγ, (Metric.mem_thickening_iff_exists_edist_lt (L \ u) x).mpr
      ⟨a, ⟨haL, hau⟩, by rw [edist_comm]; exact hxa⟩⟩
  have hcontra := hγ N (thickening δ (L \ v)) (thickening δ (L \ u)) isOpen_thickening
    isOpen_thickening hsub hneA hneB
  obtain ⟨z, hzγ, hzA, hzB⟩ := hcontra
  exact Set.disjoint_left.mp hδdisj hzA hzB

/-- **Continuum limit.**  Let `F` be a nonempty closed subset of the unit square.  If for every
`ε > 0` there is a compact connected set `U` lying in the `ε`-neighbourhood of `F` (i.e. every
point of `U` is at distance `< ε` from `F`) that meets both the left edge `{0} × [0,1]` and the
right edge `{1} × [0,1]` of the square, then `F` itself contains a compact connected set meeting
both edges. -/
theorem neighbourhood_continuum {F : Set (ℝ × ℝ)} (hFc : IsClosed F) (hFne : F.Nonempty)
    (hFQ : F ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)
    (h : ∀ ε > 0, ∃ U : Set (ℝ × ℝ), U ⊆ {p : ℝ × ℝ | Metric.infDist p F < ε} ∧ IsCompact U ∧
        IsConnected U ∧ (U ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty ∧
        (U ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty) :
    ∃ K : Set (ℝ × ℝ), K ⊆ F ∧ IsCompact K ∧ IsConnected K ∧
      (K ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty ∧
      (K ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty := by
  -- The closed square is compact, so `F` is compact; a slightly larger closed square `T` will
  -- contain every one of the approximating continua.
  have hT2c : IsCompact (Set.Icc (-1:ℝ) 2 ×ˢ Set.Icc (-1:ℝ) 2) := isCompact_Icc.prod isCompact_Icc
  have hLedgec : IsCompact (({0}:Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) := isCompact_singleton.prod isCompact_Icc
  have hRedgec : IsCompact (({1}:Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) := isCompact_singleton.prod isCompact_Icc
  -- A sequence of compact connected sets approximating `F` and running from the left edge to the
  -- right edge.
  choose U hUsub hUcomp hUconn hUL hUR using fun n : ℕ => h (1/((n:ℝ)+1)) (by positivity)
  have hUsub' : ∀ n, U n ⊆ Metric.thickening (1/((n:ℝ)+1)) F :=
    fun n p hp => (Metric.mem_thickening_iff_infDist_lt hFne).mpr (hUsub n hp)
  have hU_T2 : ∀ n, U n ⊆ Set.Icc (-1:ℝ) 2 ×ˢ Set.Icc (-1:ℝ) 2 := by
    intro n p hp
    have hε_le : (1:ℝ)/((n:ℝ)+1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hin : Metric.infDist p F < 1 := lt_of_lt_of_le (hUsub n hp) hε_le
    have hpth : p ∈ Metric.thickening 1 F := (Metric.mem_thickening_iff_infDist_lt hFne).mpr hin
    obtain ⟨z2, hzF2, hdist2⟩ := (Metric.mem_thickening_iff.mp hpth)
    have hzQ := hFQ hzF2
    rw [Prod.dist_eq] at hdist2
    have h1 : dist p.1 z2.1 < 1 := lt_of_le_of_lt (le_max_left _ _) hdist2
    have h2 : dist p.2 z2.2 < 1 := lt_of_le_of_lt (le_max_right _ _) hdist2
    rw [Real.dist_eq] at h1 h2
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
    obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
    exact ⟨⟨by linarith [hzQ.1.1], by linarith [hzQ.1.2]⟩, ⟨by linarith [hzQ.2.1], by linarith [hzQ.2.2]⟩⟩
  let u : ℕ → TopologicalSpace.NonemptyCompacts (ℝ × ℝ) :=
    fun n => ⟨⟨U n, hUcomp n⟩, (hUconn n).1⟩
  have huT2 : ∀ n, (u n : Set (ℝ × ℝ)) ⊆ Set.Icc (-1:ℝ) 2 ×ˢ Set.Icc (-1:ℝ) 2 := fun n => hU_T2 n
  -- Blaschke selection: the hyperspace of nonempty compact subsets of `T` is compact, so the
  -- sequence has a Hausdorff-convergent subsequence.
  have hS : IsCompact {K : TopologicalSpace.NonemptyCompacts (ℝ × ℝ) |
      (K : Set (ℝ × ℝ)) ⊆ Set.Icc (-1:ℝ) 2 ×ˢ Set.Icc (-1:ℝ) 2} :=
    TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact hT2c
  obtain ⟨A, hA, φ, hφ, htend⟩ := hS.tendsto_subseq (fun n => huT2 n)
  have hconv : Filter.Tendsto (fun n => Metric.hausdorffEDist ((u (φ n)) : Set (ℝ × ℝ))
      (A : Set (ℝ × ℝ))) Filter.atTop (𝓝 0) := by
    have h2 : Filter.Tendsto (fun n => edist (u (φ n)) A) Filter.atTop (𝓝 (edist A A)) :=
      htend.edist tendsto_const_nhds
    rw [edist_self] at h2
    exact h2
  -- The limit is preconnected, being a Hausdorff limit of preconnected sets.
  have hApre : IsPreconnected (A : Set (ℝ × ℝ)) :=
    isPreconnected_of_tendsto_hausdorffEDist A.isCompact' (fun n => (hUconn (φ n)).2) hconv
  -- The limit lies in `F`: it is contained in every `cthickening (1/(k+1)) F`, and the
  -- intersection of these is `F` because `F` is closed.
  have hAF : (A : Set (ℝ × ℝ)) ⊆ F := by
    intro x hx
    rw [Metric.mem_iff_infEDist_zero_of_closed hFc]
    have hle : ∀ k : ℕ, Metric.infEDist x F ≤ ENNReal.ofReal (1/((k:ℝ)+1)) := by
      intro k
      have hcl : IsClosed {K : TopologicalSpace.NonemptyCompacts (ℝ × ℝ) |
          (K : Set (ℝ × ℝ)) ⊆ Metric.cthickening (1/((k:ℝ)+1)) F} :=
        TopologicalSpace.NonemptyCompacts.isClosed_subsets_of_isClosed Metric.isClosed_cthickening
      have hev : ∀ᶠ n in Filter.atTop, (u (φ n)) ∈ {K : TopologicalSpace.NonemptyCompacts (ℝ × ℝ) |
          (K : Set (ℝ × ℝ)) ⊆ Metric.cthickening (1/((k:ℝ)+1)) F} := by
        have hevn : ∀ᶠ n in Filter.atTop, (1:ℝ)/((φ n : ℝ)+1) ≤ (1:ℝ)/((k:ℝ)+1) := by
          filter_upwards [Filter.eventually_ge_atTop k] with n hn
          have hkn : (k:ℝ) + 1 ≤ (φ n : ℝ) + 1 := by
            have hkφ : (k:ℝ) ≤ (φ n : ℝ) := by
              exact_mod_cast (le_trans hn (hφ.le_apply (x := n)))
            linarith
          exact one_div_le_one_div_of_le (by positivity) hkn
        filter_upwards [hevn] with n hn
        intro p hp
        exact Metric.cthickening_mono hn F (Metric.thickening_subset_cthickening _ F (hUsub' (φ n) hp))
      exact Metric.mem_cthickening_iff.mp ((hcl.mem_of_tendsto htend hev) hx)
    have hg : Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (1/((k:ℝ)+1))) Filter.atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using
        (ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    have hevle : ∀ᶠ k : ℕ in Filter.atTop, Metric.infEDist x F ≤ ENNReal.ofReal (1/((k:ℝ)+1)) :=
      Filter.Eventually.of_forall hle
    exact le_antisymm (le_of_tendsto_of_tendsto (f := fun _ : ℕ => Metric.infEDist x F)
      (g := fun k : ℕ => ENNReal.ofReal (1/((k:ℝ)+1))) tendsto_const_nhds hg hevle) zero_le
  -- The limit meets both edges, since the property of meeting a fixed closed set is closed in the
  -- hyperspace.
  have hAL : (((A:Set (ℝ×ℝ)) ∩ (({0}:Set ℝ) ×ˢ Set.Icc (0:ℝ) 1))).Nonempty := by
    have hcl : IsClosed {K : TopologicalSpace.NonemptyCompacts (ℝ × ℝ) |
        ((K : Set (ℝ × ℝ)) ∩ (({0}:Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty} :=
      TopologicalSpace.NonemptyCompacts.isClosed_inter_nonempty_of_isClosed hLedgec.isClosed
    exact hcl.mem_of_tendsto htend (Filter.Eventually.of_forall (fun n => hUL (φ n)))
  have hAR : (((A:Set (ℝ×ℝ)) ∩ (({1}:Set ℝ) ×ˢ Set.Icc (0:ℝ) 1))).Nonempty := by
    have hcl : IsClosed {K : TopologicalSpace.NonemptyCompacts (ℝ × ℝ) |
        ((K : Set (ℝ × ℝ)) ∩ (({1}:Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty} :=
      TopologicalSpace.NonemptyCompacts.isClosed_inter_nonempty_of_isClosed hRedgec.isClosed
    exact hcl.mem_of_tendsto htend (Filter.Eventually.of_forall (fun n => hUR (φ n)))
  exact ⟨(A : Set (ℝ × ℝ)), hAF, A.isCompact', ⟨A.nonempty', hApre⟩, hAL, hAR⟩

end Work.Smooth.JordanSeparation
