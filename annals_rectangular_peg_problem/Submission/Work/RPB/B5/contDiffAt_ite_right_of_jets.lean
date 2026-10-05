import Mathlib

/-!
# Gluing a `C^k` function across a one-sided seam (rectangular peg problem, B5)

We prove `contDiffAt_ite_right_of_jets`: if `f` is `C^k` at `x₀`, if `g` is `C^k` at `x₀` from the
right (that is, within `Set.Ioi x₀`), and if the one-sided jets of `g` at `x₀` agree with the jets
of `f` at `x₀`, then the function

`x ↦ if x₀ < x then g x else f x`

is `C^k` at `x₀`.

The proof is in three steps.

* `iteratedFDerivWithin_jets`: the hypothesised matching of the *iterated derivatives*
  (`iteratedDerivWithin j g (Ioi x₀) x₀ = iteratedDeriv j f x₀`) upgrades to a matching of the
  full *iterated Fréchet derivatives* of the two half-restrictions,
  `iteratedFDerivWithin ℝ m f (s ∩ Iic x₀) x₀ = iteratedFDerivWithin ℝ m g (s ∩ Ici x₀) x₀`.
  Indeed a multilinear map `ℝ^m → E` is determined by its value on the all-ones vector (that is
  exactly `ContinuousMultilinearMap.piFieldEquiv`).

* `hasFTaylorSeriesUpToOn_of_halfspaces_1d`: a formal Taylor series which works on both closed
  halves `s ∩ Iic a` and `s ∩ Ici a` of an open set `s` works on all of `s`. This is the
  one-dimensional analogue of the half-space gluing lemma used elsewhere in the project.

* The main theorem obtains a `C^k` Taylor series of `f` on an open neighbourhood, a `C^k` Taylor
  series of `g` on the right half, glues them into a single series `p` on an open interval, and
  concludes with `HasFTaylorSeriesUpToOn.contDiffOn`.
-/

open Filter Set
open scoped Topology

namespace Work.RPB.B5

/-- The hypothesised equality of one-sided jets of `g` with the jets of `f` upgrades to an
equality of the iterated Fréchet derivatives of the two half-restrictions. -/
theorem iteratedFDerivWithin_jets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (f g : ℝ → E) (x₀ : ℝ) (s : Set ℝ) (hs : s ∈ 𝓝 x₀)
    (hf : ContDiffAt ℝ k f x₀)
    (hjet : ∀ j ≤ k, iteratedDerivWithin j g (Set.Ioi x₀) x₀ = iteratedDeriv j f x₀) :
    ∀ m ≤ k, iteratedFDerivWithin ℝ m f (s ∩ Set.Iic x₀) x₀
           = iteratedFDerivWithin ℝ m g (s ∩ Set.Ici x₀) x₀ := by
  intro m hm
  -- `s ∩ Iic x₀` and `s ∩ Ici x₀` agree with `Iic x₀` and `Ici x₀` near `x₀`
  have hL : (s ∩ Set.Iic x₀) =ᶠ[𝓝 x₀] (Set.Iic x₀) :=
    Filter.eventually_of_mem hs (fun y hy => by simp [Set.mem_inter_iff, hy])
  have hR : (s ∩ Set.Ici x₀) =ᶠ[𝓝 x₀] (Set.Ici x₀) :=
    Filter.eventually_of_mem hs (fun y hy => by simp [Set.mem_inter_iff, hy])
  -- it suffices to match the two multilinear maps on the all-ones vector
  have hdiag : (iteratedFDerivWithin ℝ m f (s ∩ Set.Iic x₀) x₀) (fun _ => 1)
             = (iteratedFDerivWithin ℝ m g (s ∩ Set.Ici x₀) x₀) (fun _ => 1) := by
    rw [iteratedFDerivWithin_congr_set hL m, iteratedFDerivWithin_congr_set hR m]
    rw [show Set.Ici x₀ = insert x₀ (Set.Ioi x₀) from by simp only [Set.Ioi_insert]]
    rw [iteratedFDerivWithin_insert]
    rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Iic x₀)
          (hf.of_le (by exact_mod_cast hm)) (by simp)]
    change iteratedDeriv m f x₀ = iteratedDerivWithin m g (Set.Ioi x₀) x₀
    rw [hjet m hm]
  rw [← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self
        (iteratedFDerivWithin ℝ m f (s ∩ Set.Iic x₀) x₀),
      ← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self
        (iteratedFDerivWithin ℝ m g (s ∩ Set.Ici x₀) x₀),
      hdiag]

/-- **Half-space gluing, one-dimensional case.**  If a function admits the same formal Taylor
series `p` on the two closed halves `s ∩ Iic a` and `s ∩ Ici a` of an open set `s`, then it admits
`p` as Taylor series on all of `s`. -/
theorem hasFTaylorSeriesUpToOn_of_halfspaces_1d {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ → E) (N : ℕ) {s : Set ℝ} (hs : IsOpen s) {a : ℝ}
    {p : ℝ → FormalMultilinearSeries ℝ ℝ E}
    (hL : HasFTaylorSeriesUpToOn N F p (s ∩ Set.Iic a))
    (hR : HasFTaylorSeriesUpToOn N F p (s ∩ Set.Ici a)) :
    HasFTaylorSeriesUpToOn N F p s := by
  have halfL : ∀ {z : ℝ}, z ∈ s → z < a → s ∩ Set.Iic a ∈ 𝓝 z := by
    intro z hz hzlt
    exact Filter.inter_mem (hs.mem_nhds hz)
      (mem_of_superset ((isOpen_lt continuous_id continuous_const).mem_nhds hzlt)
        (fun w hw => show w ≤ a from le_of_lt hw))
  have halfR : ∀ {z : ℝ}, z ∈ s → a < z → s ∩ Set.Ici a ∈ 𝓝 z := by
    intro z hz hzlt
    exact Filter.inter_mem (hs.mem_nhds hz)
      (mem_of_superset ((isOpen_lt continuous_const continuous_id).mem_nhds hzlt)
        (fun w hw => show a ≤ w from le_of_lt hw))
  have hunion : (s ∩ Set.Iic a) ∪ (s ∩ Set.Ici a) = s := by
    rw [← Set.inter_union_distrib_left, Set.Iic_union_Ici, Set.inter_univ]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    by_cases h : z ≤ a
    · exact hL.zero_eq z ⟨hz, h⟩
    · exact hR.zero_eq z ⟨hz, le_of_lt (not_le.mp h)⟩
  · intro m hm z hz
    rcases lt_trichotomy z a with h | h | h
    · exact ((hL.fderivWithin m hm z ⟨hz, le_of_lt h⟩).hasFDerivAt
        (halfL hz h)).hasFDerivWithinAt
    · rw [← hunion]
      exact (hL.fderivWithin m hm z ⟨hz, le_of_eq h⟩).union
        (hR.fderivWithin m hm z ⟨hz, le_of_eq h.symm⟩)
    · exact ((hR.fderivWithin m hm z ⟨hz, le_of_lt h⟩).hasFDerivAt
        (halfR hz h)).hasFDerivWithinAt
  · intro m hm z hz
    rcases lt_trichotomy z a with h | h | h
    · exact (((hL.cont m hm).continuousWithinAt ⟨hz, le_of_lt h⟩).continuousAt
        (halfL hz h)).continuousWithinAt
    · rw [← hunion]
      exact ((hL.cont m hm).continuousWithinAt ⟨hz, le_of_eq h⟩).union
        ((hR.cont m hm).continuousWithinAt ⟨hz, le_of_eq h.symm⟩)
    · exact (((hR.cont m hm).continuousWithinAt ⟨hz, le_of_lt h⟩).continuousAt
        (halfR hz h)).continuousWithinAt

theorem contDiffAt_ite_right_of_jets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (f g : ℝ → E) (x₀ : ℝ)
    (hf : ContDiffAt ℝ k f x₀)
    (hg : ContDiffWithinAt ℝ k g (Set.Ioi x₀) x₀)
    (hjet : ∀ j ≤ k, iteratedDerivWithin j g (Set.Ioi x₀) x₀ = iteratedDeriv j f x₀) :
    ContDiffAt ℝ k (fun x => if x₀ < x then g x else f x) x₀ := by
  -- an open neighbourhood on which `f` is `C^k`
  obtain ⟨uf, huf_open, hxuf, huf⟩ := hf.contDiffOn' (le_refl _) (by simp)
  -- an open neighbourhood `ug` such that `g` is `C^k` on `Ici x₀ ∩ ug`
  obtain ⟨ug, hug_open, hxug, hug⟩ := hg.contDiffOn' (le_refl _) (by simp)
  have hmem : uf ∩ ug ∈ 𝓝 x₀ :=
    Filter.inter_mem (huf_open.mem_nhds hxuf) (hug_open.mem_nhds hxug)
  obtain ⟨l, u, hxIoo, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hmem
  obtain ⟨hlx, hxu⟩ := Set.mem_Ioo.mp hxIoo
  have huf' : ContDiffOn ℝ k f uf := by simpa using huf
  -- name the glued function
  set h : ℝ → E := (fun x => if x₀ < x then g x else f x) with hh
  -- the two half-sets are half-open intervals
  have hLset : Set.Ioo l u ∩ Set.Iic x₀ = Set.Ioc l x₀ := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hlz, _⟩, hzx⟩; exact ⟨hlz, hzx⟩
    · rintro ⟨hlz, hzx⟩; exact ⟨⟨hlz, lt_of_le_of_lt hzx hxu⟩, hzx⟩
  have hRset : Set.Ioo l u ∩ Set.Ici x₀ = Set.Ico x₀ u := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ico]
    constructor
    · rintro ⟨⟨_, hzu⟩, hxz⟩; exact ⟨hxz, hzu⟩
    · rintro ⟨hxz, hzu⟩; exact ⟨⟨lt_of_lt_of_le hlx hxz, hzu⟩, hxz⟩
  have hLud : UniqueDiffOn ℝ (Set.Ioo l u ∩ Set.Iic x₀) := by
    rw [hLset]; exact uniqueDiffOn_Ioc l x₀
  have hRud : UniqueDiffOn ℝ (Set.Ioo l u ∩ Set.Ici x₀) := by
    rw [hRset]; exact uniqueDiffOn_Ico x₀ u
  -- smoothness of `f` on the interval and of `g` on its right half
  have hf_s : ContDiffOn ℝ k f (Set.Ioo l u) := huf'.mono (fun z hz => (hsub hz).1)
  have hg_s : ContDiffOn ℝ k g (Set.Ioo l u ∩ Set.Ici x₀) :=
    hug.mono (fun z hz => ⟨by rw [Set.Ioi_insert]; exact hz.2, (hsub hz.1).2⟩)
  -- Taylor series on the two halves
  have hfser : HasFTaylorSeriesUpToOn k f (ftaylorSeriesWithin ℝ f (Set.Ioo l u ∩ Set.Iic x₀))
      (Set.Ioo l u ∩ Set.Iic x₀) :=
    (hf_s.mono (fun z hz => hz.1)).ftaylorSeriesWithin hLud
  have hgser : HasFTaylorSeriesUpToOn k g (ftaylorSeriesWithin ℝ g (Set.Ioo l u ∩ Set.Ici x₀))
      (Set.Ioo l u ∩ Set.Ici x₀) :=
    hg_s.ftaylorSeriesWithin hRud
  -- the glued Taylor series
  let p : ℝ → FormalMultilinearSeries ℝ ℝ E :=
    fun z => if z ≤ x₀ then ftaylorSeriesWithin ℝ f (Set.Ioo l u ∩ Set.Iic x₀) z
             else ftaylorSeriesWithin ℝ g (Set.Ioo l u ∩ Set.Ici x₀) z
  have hg0 : g x₀ = f x₀ := by simpa using hjet 0 (Nat.zero_le k)
  -- the series works on the left half
  have hL : HasFTaylorSeriesUpToOn k h p (Set.Ioo l u ∩ Set.Iic x₀) := by
    refine (hfser.congr_series (fun m hm z hz => ?_)).congr (fun z hz => ?_)
    · show ftaylorSeriesWithin ℝ f (Set.Ioo l u ∩ Set.Iic x₀) z m = p z m
      rw [show p z = ftaylorSeriesWithin ℝ f (Set.Ioo l u ∩ Set.Iic x₀) z from
            ite_eq_left (show z ≤ x₀ from hz.2)]
    · show h z = f z
      rw [hh]; simp only [ite_eq_right (not_lt.mpr (show z ≤ x₀ from hz.2))]
  -- the series works on the right half
  have hR : HasFTaylorSeriesUpToOn k h p (Set.Ioo l u ∩ Set.Ici x₀) := by
    refine (hgser.congr_series (fun m hm z hz => ?_)).congr (fun z hz => ?_)
    · rcases lt_or_eq_of_le (show x₀ ≤ z from hz.2) with hlt | heq
      · show ftaylorSeriesWithin ℝ g (Set.Ioo l u ∩ Set.Ici x₀) z m = p z m
        rw [show p z = ftaylorSeriesWithin ℝ g (Set.Ioo l u ∩ Set.Ici x₀) z from
              ite_eq_right (not_le.mpr hlt)]
      · rw [← heq]
        show ftaylorSeriesWithin ℝ g (Set.Ioo l u ∩ Set.Ici x₀) x₀ m = p x₀ m
        rw [show p x₀ = ftaylorSeriesWithin ℝ f (Set.Ioo l u ∩ Set.Iic x₀) x₀ from
              ite_eq_left le_rfl]
        show iteratedFDerivWithin ℝ m g (Set.Ioo l u ∩ Set.Ici x₀) x₀
            = iteratedFDerivWithin ℝ m f (Set.Ioo l u ∩ Set.Iic x₀) x₀
        exact (iteratedFDerivWithin_jets k f g x₀ (Set.Ioo l u) (isOpen_Ioo.mem_nhds hxIoo) hf
                hjet m (by exact_mod_cast hm)).symm
    · show h z = g z
      rw [hh]
      rcases lt_or_eq_of_le (show x₀ ≤ z from hz.2) with hlt | heq
      · simp only [ite_eq_left hlt]
      · rw [← heq]
        simp only [ite_eq_right (not_lt.mpr le_rfl)]
        exact hg0.symm
  -- glue and conclude
  have hFT : HasFTaylorSeriesUpToOn k h p (Set.Ioo l u) :=
    hasFTaylorSeriesUpToOn_of_halfspaces_1d h k isOpen_Ioo hL hR
  exact (hFT.contDiffOn.contDiffWithinAt hxIoo).contDiffAt (isOpen_Ioo.mem_nhds hxIoo)

end Work.RPB.B5
