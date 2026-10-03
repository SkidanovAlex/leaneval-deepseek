import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basic
import Submission.Work.Horn.endSurj

/-!
# `Work.Horn.E_surjOn_ends` — surjectivity of the lifted horn map onto `ℂ ∖ (Φ c + ℤ)`

Shishikura, Prop. 5.3 (the `surj` half of the HORN assembly).  For `f₀ ∈ 𝓕₀` with immediate basin
`B`, unique critical point `c ∈ B` and §4.1 data `d : ParabData f₀ D₀`, the lifted horn map
`E = Φ ∘ φ₀` maps each of the two ends `BuOf d B`, `BlOf d B` onto the complement
`S = ℂ ∖ (Φ c + ℤ)` of the critical-value lattice, provided `E` is a covering over `S` on that end.

## Route

Write `S = {y : ℂ | ∀ k : ℤ, y ≠ Φ c + k}`, the complement of the lattice `Φ c + ℤ`.

1. **`S` is preconnected.**  The lattice `Φ c + ℤ` is countable and `ℂ` has real rank `2 > 1`, so
   its complement is even *path* connected (`Set.Countable.isPathConnected_compl_of_one_lt_rank`).
2. **A covering map onto `S` covers `S`.**  `subset_range_of_isCoveringMapOn`:  let `f : Q → ℂ` be a
   covering over a preconnected `S` whose image meets `S`.  For `y ∈ S ∩ range f` the map `f` is a
   local homeomorphism at the point over `y` (`IsCoveringMapOn.isLocalHomeomorphOn` and
   `IsLocalHomeomorphOn.map_nhds_eq`), so `range f ∈ 𝓝 y`; for `y ∈ S ∖ range f` the fibre is empty,
   so `IsEvenlyCovered` supplies an *open* neighbourhood of `y` disjoint from `range f`.  Hence
   `range f` is clopen in `S`, and `S` is preconnected, so `range f ⊇ S`.
3. **The image of each end meets `S`.**  At the upper end `E w - w → 0` and at the lower end
   `E w - w → cl` (`ParabData.E_upper_iff`, `E_lower_iff`); the Banach fixed point argument
   (`Work.Horn.exists_preimage_of_im_gt`, `exists_preimage_of_im_lt`) gives that a far upper
   (resp. lower) half plane is contained in the image of `E` on `{η₀ < Im}` (resp. `{Im < -η₀}`),
   which lies in the end under consideration.  The point `i·M` for a suitable `M` is in that half
   plane and off the lattice `Φ c + ℤ` (its imaginary part cannot differ from `Im (Φ c)` by an
   integer unless it *equals* `Im (Φ c)`, which we avoid).
-/

namespace Work.Horn

open Filter Topology Metric Set
open scoped Topology

noncomputable section

/-! ## Auxiliary analytic facts about `ParabData` -/

/-- The parabolic basin is a neighbourhood of each of its points (it is open). -/
theorem parabolicBasin_mem_nhds {f : ℂ → ℂ} {D : Set ℂ} {z : ℂ}
    (hz : z ∈ MandelDim.ParabolicBasin f D) : MandelDim.ParabolicBasin f D ∈ 𝓝 z := by
  obtain ⟨U, hU, hiter, hconv⟩ := hz
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  exact Filter.mem_of_superset (hVopen.mem_nhds hzV) fun w hw =>
    ⟨U, Filter.mem_of_superset (hVopen.mem_nhds hw) hVU, hiter, hconv⟩

/-- `E = Φ ∘ φ` is holomorphic at every point of its domain `DE = φ⁻¹(basin)`. -/
private theorem differentiableAt_E {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {w : ℂ} (hw : w ∈ d.DE) : DifferentiableAt ℂ d.E w := by
  rw [Work.Horn.MandelDim.ParabData.mem_DE] at hw
  exact (d.Φ_holo.differentiableAt (parabolicBasin_mem_nhds hw.2)).comp w
    (d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hw.1))

/-! ## The complement of the lattice `a + ℤ` is preconnected -/

/-- `ℂ ∖ (a + ℤ)` is preconnected: `a + ℤ` is countable and `ℂ` has real rank `2 > 1`, so the
complement of a countable set is path connected (`Set.Countable.isPathConnected_compl_of_one_lt_rank`);
this even gives that the complement is path connected. -/
theorem isPreconnected_compl_add_int (a : ℂ) :
    IsPreconnected ({y : ℂ | ∀ k : ℤ, y ≠ a + (k : ℂ)}) := by
  have hrange : {y : ℂ | ∀ k : ℤ, y ≠ a + (k : ℂ)}
      = (Set.range (fun k : ℤ => a + (k : ℂ)))ᶜ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists]
    exact forall_congr' fun k => by rw [eq_comm]
  rw [hrange]
  exact (Set.Countable.isPathConnected_compl_of_one_lt_rank (E := ℂ)
    (by rw [Complex.rank_real_complex]; norm_num) (Set.countable_range _)).isConnected.isPreconnected

/-! ## A covering map over a preconnected `S` that meets its image covers `S` -/

/-- If `y` is not in the range of `f`, an evenly covered neighbourhood of `y` is disjoint from the
range of `f`: the trivialization would otherwise produce a point of the empty fibre `f ⁻¹' {y}`. -/
theorem disjoint_nhds_of_notMem_range {Q : Set ℂ} {f : Q → ℂ} {y : ℂ}
    (h : IsEvenlyCovered f y (f ⁻¹' {y})) (hy : y ∉ Set.range f) :
    ∃ W : Set ℂ, IsOpen W ∧ y ∈ W ∧ Disjoint W (Set.range f) := by
  obtain ⟨-, W, hyW, hWopen, -, H, -⟩ := h
  refine ⟨W, hWopen, hyW, ?_⟩
  rw [Set.disjoint_left]
  rintro z hzW ⟨x, hx⟩
  have hxW : x ∈ f ⁻¹' W := by rw [Set.mem_preimage, hx]; exact hzW
  have hp : f ⁻¹' {y} := (H ⟨x, hxW⟩).2
  exact hy ⟨(hp : Q), hp.2⟩

/-- **A covering map over a preconnected `S` whose image meets `S` maps onto `S`.** -/
theorem subset_range_of_isCoveringMapOn {Q S : Set ℂ} {f : Q → ℂ}
    (hS : IsPreconnected S) (hcov : IsCoveringMapOn f S) (hne : (S ∩ Set.range f).Nonempty) :
    S ⊆ Set.range f := by
  have hmem_nhds : ∀ y ∈ S, y ∈ Set.range f → Set.range f ∈ 𝓝 y := by
    rintro y hyS ⟨x, rfl⟩
    have hmap := hcov.isLocalHomeomorphOn.map_nhds_eq (x := x) hyS
    rw [← hmap, Filter.mem_map]
    exact Filter.mem_of_superset Filter.univ_mem (fun z _ => Set.mem_range_self z)
  set V : Set ℂ := ⋃₀ {W : Set ℂ | IsOpen W ∧ Disjoint W (Set.range f)} with hV
  have hVopen : IsOpen V := isOpen_sUnion (fun W hW => hW.1)
  have hVdisj : Disjoint V (Set.range f) := by
    rw [Set.disjoint_left]
    intro z hzV hzr
    obtain ⟨W, hW, hzW⟩ := hzV
    exact (Set.disjoint_left.mp hW.2 hzW) hzr
  set u : Set ℂ := ⋃₀ {W : Set ℂ | IsOpen W ∧ Disjoint W V ∧ W ⊆ Set.range f} with hu
  have huopen : IsOpen u := isOpen_sUnion (fun W hW => hW.1)
  have hudisj : Disjoint u V := by
    rw [Set.disjoint_left]
    intro z hzu hzV
    obtain ⟨W, hW, hzW⟩ := hzu
    exact (Set.disjoint_left.mp hW.2.1 hzW) hzV
  have husub : u ⊆ Set.range f := sUnion_subset_iff.mpr (fun W hW => hW.2.2)
  have hSu : S ∩ Set.range f ⊆ u := by
    rintro y ⟨hyS, hyr⟩
    obtain ⟨W, hWsub, hWopen, hyW⟩ := _root_.mem_nhds_iff.mp (hmem_nhds y hyS hyr)
    exact ⟨W, ⟨hWopen,
      Set.disjoint_left.mpr (fun z hzW hzV => (Set.disjoint_left.mp hVdisj hzV) (hWsub hzW)),
      hWsub⟩, hyW⟩
  have hsub : S ⊆ u ∪ V := by
    intro y hyS
    by_cases hyr : y ∈ Set.range f
    · exact Or.inl (hSu ⟨hyS, hyr⟩)
    · obtain ⟨W, hWopen, hyW, hWdisj⟩ := disjoint_nhds_of_notMem_range (hcov y hyS) hyr
      exact Or.inr ⟨W, ⟨hWopen, hWdisj⟩, hyW⟩
  have hne' : (S ∩ u).Nonempty := hne.mono (fun y hy => ⟨hy.1, hSu hy⟩)
  exact (hS.subset_left_of_subset_union huopen hVopen hudisj hsub hne').trans husub

/-! ## The target -/

/-- If the lifted horn map `E = Φ ∘ φ₀` is a covering over the complement of the critical-value
lattice on both ends `BuOf d B`, `BlOf d B`, then it is surjective onto that complement from each
end. -/
theorem E_surjOn_ends (hTopo : MandelDim.HornTopoStatement)
    {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    (hcov : IsCoveringMapOn (fun x : MandelDim.BuOf d B => d.E x)
              {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} ∧
            IsCoveringMapOn (fun x : MandelDim.BlOf d B => d.E x)
              {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k}) :
    (∀ y : ℂ, (∀ k : ℤ, y ≠ d.Φ c + k) → ∃ w ∈ MandelDim.BuOf d B, d.E w = y) ∧
    (∀ y : ℂ, (∀ k : ℤ, y ≠ d.Φ c + k) → ∃ w ∈ MandelDim.BlOf d B, d.E w = y) := by
  obtain ⟨-, -, -, -, hHalfU, hHalfL, hsub⟩ := hTopo f₀ D₀ B c d hsetup
  have hholU : DifferentiableOn ℂ d.E {w : ℂ | d.η₀ < w.im} := fun w hw =>
    (differentiableAt_E d (hsub (Or.inl (hHalfU hw)))).differentiableWithinAt
  have hholL : DifferentiableOn ℂ d.E {w : ℂ | w.im < -d.η₀} := fun w hw =>
    (differentiableAt_E d (hsub (Or.inr (hHalfL hw)))).differentiableWithinAt
  obtain ⟨R, hR⟩ := Work.Horn.exists_preimage_of_im_gt (E := d.E) (r := d.η₀) hholU
    (Work.Horn.MandelDim.ParabData.E_upper_iff d)
  obtain ⟨cl, hcl⟩ := Work.Horn.MandelDim.ParabData.E_lower_iff d
  obtain ⟨Rl, hRl⟩ := Work.Horn.exists_preimage_of_im_lt (E := d.E) (r := d.η₀) (cl := cl) hholL hcl
  have hneU : (({y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k}) ∩
      Set.range (fun x : MandelDim.BuOf d B => d.E x)).Nonempty := by
    set M : ℝ := max R (max (d.Φ c).im 0) + 1 with hM
    have hMR : R < M := by rw [hM]; linarith [le_max_left R (max (d.Φ c).im 0)]
    have hMim : (d.Φ c).im < M := by
      rw [hM]; linarith [le_max_right R (max (d.Φ c).im 0), le_max_left (d.Φ c).im 0]
    have him : (Complex.I * (M : ℂ)).im = M := by simp [Complex.mul_im]
    have hyS : (Complex.I * (M : ℂ)) ∈ {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} := by
      intro k hk
      have h1 : (Complex.I * (M : ℂ) - (d.Φ c + (k : ℂ))).im = M - (d.Φ c).im := by
        simp [Complex.mul_im]
      have h2 : (Complex.I * (M : ℂ) - (d.Φ c + (k : ℂ))).im = 0 := by rw [hk]; simp
      rw [h1] at h2; linarith
    obtain ⟨w, hw, hwE⟩ := hR (Complex.I * (M : ℂ)) (by rw [him]; exact hMR)
    exact ⟨Complex.I * (M : ℂ), hyS, ⟨⟨w, hHalfU hw⟩, by simpa using hwE⟩⟩
  have hneL : (({y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k}) ∩
      Set.range (fun x : MandelDim.BlOf d B => d.E x)).Nonempty := by
    set M : ℝ := min Rl (min (d.Φ c).im 0) - 1 with hM
    have hMR : M < Rl := by rw [hM]; linarith [min_le_left Rl (min (d.Φ c).im 0)]
    have hMim : M < (d.Φ c).im := by
      rw [hM]; linarith [min_le_right Rl (min (d.Φ c).im 0), min_le_left (d.Φ c).im 0]
    have him : (Complex.I * (M : ℂ)).im = M := by simp [Complex.mul_im]
    have hyS : (Complex.I * (M : ℂ)) ∈ {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} := by
      intro k hk
      have h1 : (Complex.I * (M : ℂ) - (d.Φ c + (k : ℂ))).im = M - (d.Φ c).im := by
        simp [Complex.mul_im]
      have h2 : (Complex.I * (M : ℂ) - (d.Φ c + (k : ℂ))).im = 0 := by rw [hk]; simp
      rw [h1] at h2; linarith
    obtain ⟨w, hw, hwE⟩ := hRl (Complex.I * (M : ℂ)) (by rw [him]; exact hMR)
    exact ⟨Complex.I * (M : ℂ), hyS, ⟨⟨w, hHalfL hw⟩, by simpa using hwE⟩⟩
  have hsurjU := subset_range_of_isCoveringMapOn (isPreconnected_compl_add_int (d.Φ c)) hcov.1 hneU
  have hsurjL := subset_range_of_isCoveringMapOn (isPreconnected_compl_add_int (d.Φ c)) hcov.2 hneL
  constructor
  · intro y hy
    obtain ⟨x, hx⟩ := hsurjU hy
    exact ⟨x.1, x.2, hx⟩
  · intro y hy
    obtain ⟨x, hx⟩ := hsurjL hy
    exact ⟨x.1, x.2, hx⟩

end

end Work.Horn
