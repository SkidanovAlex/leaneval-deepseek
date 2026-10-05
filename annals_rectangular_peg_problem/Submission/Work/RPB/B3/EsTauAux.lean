import Mathlib

/-!
# Auxiliaries for the `τ`-extension `Work.RPB.B3.es_tau_extend`

We work on `M = ℝ × (ℝ × ℝ)` with coordinates `(τ, t, r)`.

* `reflLin c` is the linear map `(τ,t,r) ↦ (c*τ, t, r)`, used to extend a function defined on
  the closed strip `τ ∈ [0,1]` across the boundary points (`τ = 0`, `τ = 1`).
* `hasFTaylorSeriesUpToOn_of_halfspaces` glues a Taylor series from the two closed halves
  `{τ ≤ a}` and `{a ≤ τ}` of an open set to the whole open set.
-/

open scoped ContDiff Topology
open Filter

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B3

/-- The linear map `(τ,t,r) ↦ (c*τ, t, r)` of `M = ℝ × (ℝ × ℝ)`. -/
def reflLin (c : ℝ) : (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × (ℝ × ℝ)) :=
  (c • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

@[simp] theorem reflLin_apply (c τ : ℝ) (t r : ℝ) :
    reflLin c (τ, t, r) = (c * τ, t, r) := by
  simp [reflLin]

@[simp] theorem reflLin_apply' (c : ℝ) (z : ℝ × (ℝ × ℝ)) :
    reflLin c z = (c * z.1, z.2.1, z.2.2) := by
  obtain ⟨τ, t, r⟩ := z; rfl

theorem reflLin_zero (t r : ℝ) : reflLin 0 (0, t, r) = (0, t, r) := by simp

/-- The open box `(-1,1) × ℝ × (-δ,δ)`. -/
def esBox (δ : ℝ) : Set (ℝ × (ℝ × ℝ)) := Set.Ioo (-1) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ

/-- The left half `{τ ≤ 0}` of `esBox δ`. -/
def esHalfL (δ : ℝ) : Set (ℝ × (ℝ × ℝ)) := esBox δ ∩ {z | z.1 ≤ 0}

/-- The right half `{0 ≤ τ}` of `esBox δ`. -/
def esHalfR (δ : ℝ) : Set (ℝ × (ℝ × ℝ)) := esBox δ ∩ {z | 0 ≤ z.1}

/-- The middle band `(-1,0) × ℝ × (-δ,δ)`. -/
def esBandL (δ : ℝ) : Set (ℝ × (ℝ × ℝ)) := Set.Ioo (-1) 0 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ

/-- The middle band `(0,1) × ℝ × (-δ,δ)`. -/
def esBandR (δ : ℝ) : Set (ℝ × (ℝ × ℝ)) := Set.Ioo 0 1 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ

theorem mem_esBox {δ : ℝ} {z : ℝ × (ℝ × ℝ)} :
    z ∈ esBox δ ↔ z.1 ∈ Set.Ioo (-1) 1 ∧ z.2.2 ∈ Set.Ioo (-δ) δ := by
  simp [esBox, and_assoc]

theorem isOpen_esBox (δ : ℝ) : IsOpen (esBox δ) :=
  isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo)

theorem isOpen_esBandL (δ : ℝ) : IsOpen (esBandL δ) :=
  isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo)

theorem isOpen_esBandR (δ : ℝ) : IsOpen (esBandR δ) :=
  isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo)

theorem bandL_subset (δ : ℝ) : esBandL δ ⊆ esHalfL δ := by
  intro z hz
  rw [esHalfL, Set.mem_inter_iff, mem_esBox]
  exact ⟨⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2.2⟩, le_of_lt hz.1.2⟩

theorem bandR_subset (δ : ℝ) : esBandR δ ⊆ esHalfR δ := by
  intro z hz
  rw [esHalfR, Set.mem_inter_iff, mem_esBox]
  exact ⟨⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2.2⟩, le_of_lt hz.1.1⟩

theorem convex_esBox (δ : ℝ) : Convex ℝ (esBox δ) :=
  (convex_Ioo (-1) 1).prod (convex_univ.prod (convex_Ioo (-δ) δ))

theorem convex_esHalfL (δ : ℝ) : Convex ℝ (esHalfL δ) := by
  rw [show esHalfL δ = esBox δ ∩ (Set.Iic (0:ℝ) ×ˢ Set.univ) by ext z; simp [esHalfL]]
  exact (convex_esBox δ).inter ((convex_Iic (0:ℝ)).prod convex_univ)

theorem convex_esHalfR (δ : ℝ) : Convex ℝ (esHalfR δ) := by
  rw [show esHalfR δ = esBox δ ∩ (Set.Ici (0:ℝ) ×ˢ Set.univ) by ext z; simp [esHalfR]]
  exact (convex_esBox δ).inter ((convex_Ici (0:ℝ)).prod convex_univ)

theorem uniqueDiffOn_esBox (δ : ℝ) : UniqueDiffOn ℝ (esBox δ) :=
  (isOpen_esBox δ).uniqueDiffOn

theorem uniqueDiffOn_esHalfL {δ : ℝ} (hδ : 0 < δ) : UniqueDiffOn ℝ (esHalfL δ) := by
  refine uniqueDiffOn_convex (convex_esHalfL δ) ⟨(-1/2, 0, 0), ?_⟩
  rw [mem_interior_iff_mem_nhds]
  exact mem_of_superset ((isOpen_esBandL δ).mem_nhds (by
    simp only [esBandL, Set.mem_prod, Set.mem_Ioo, Set.mem_univ, true_and]
    exact ⟨⟨by norm_num, by norm_num⟩, by linarith, by linarith⟩)) (bandL_subset δ)

theorem uniqueDiffOn_esHalfR {δ : ℝ} (hδ : 0 < δ) : UniqueDiffOn ℝ (esHalfR δ) := by
  refine uniqueDiffOn_convex (convex_esHalfR δ) ⟨(1/2, 0, 0), ?_⟩
  rw [mem_interior_iff_mem_nhds]
  exact mem_of_superset ((isOpen_esBandR δ).mem_nhds (by
    simp only [esBandR, Set.mem_prod, Set.mem_Ioo, Set.mem_univ, true_and]
    exact ⟨⟨by norm_num, by norm_num⟩, by linarith, by linarith⟩)) (bandR_subset δ)

/-- A point of the right half of a neighbourhood of `τ = a`, with `τ > a`, is an interior
point of that half. -/
theorem half_left_mem_nhds {s : Set (ℝ × (ℝ × ℝ))} (hs : IsOpen s) {z : ℝ × (ℝ × ℝ)}
    {a : ℝ} (hz : z ∈ s) (hzlt : z.1 < a) : s ∩ {w | w.1 ≤ a} ∈ 𝓝 z := by
  have h1 : ({w : ℝ × (ℝ × ℝ) | w.1 < a}) ∈ 𝓝 z :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds hzlt
  exact Filter.inter_mem (hs.mem_nhds hz) (mem_of_superset h1 fun w hw => le_of_lt (show w.1 < a from hw))

theorem half_right_mem_nhds {s : Set (ℝ × (ℝ × ℝ))} (hs : IsOpen s) {z : ℝ × (ℝ × ℝ)}
    {a : ℝ} (hz : z ∈ s) (hzlt : a < z.1) : s ∩ {w | a ≤ w.1} ∈ 𝓝 z := by
  have h1 : ({w : ℝ × (ℝ × ℝ) | a < w.1}) ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hzlt
  exact Filter.inter_mem (hs.mem_nhds hz) (mem_of_superset h1 fun w hw => le_of_lt (show a < w.1 from hw))

/-- **Gluing lemma.**  If `F` admits the same Taylor series `p` on the two closed halves
`{τ ≤ a}` and `{a ≤ τ}` of an open set `s`, then it admits `p` as Taylor series on `s`. -/
theorem hasFTaylorSeriesUpToOn_of_halfspaces {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ × (ℝ × ℝ) → E) (N : ℕ)
    {s : Set (ℝ × (ℝ × ℝ))} (hs : IsOpen s) {a : ℝ}
    {p : (ℝ × (ℝ × ℝ)) → FormalMultilinearSeries ℝ (ℝ × (ℝ × ℝ)) E}
    (hL : HasFTaylorSeriesUpToOn N F p (s ∩ {z | z.1 ≤ a}))
    (hR : HasFTaylorSeriesUpToOn N F p (s ∩ {z | a ≤ z.1})) :
    HasFTaylorSeriesUpToOn N F p s := by
  have hunion : (s ∩ {z : ℝ × (ℝ × ℝ) | z.1 ≤ a}) ∪ (s ∩ {z | a ≤ z.1}) = s := by
    have hAB : ({z : ℝ × (ℝ × ℝ) | z.1 ≤ a} ∪ {z | a ≤ z.1}) = Set.univ := by
      ext z; simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact le_total z.1 a
    rw [← Set.inter_union_distrib_left, hAB, Set.inter_univ]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    by_cases h : z.1 ≤ a
    · exact hL.zero_eq z ⟨hz, h⟩
    · exact hR.zero_eq z ⟨hz, le_of_lt (not_le.mp h)⟩
  · intro m hm z hz
    rcases lt_trichotomy z.1 a with h | h | h
    · exact ((hL.fderivWithin m hm z ⟨hz, le_of_lt h⟩).hasFDerivAt
        (half_left_mem_nhds hs hz h)).hasFDerivWithinAt
    · rw [← hunion]
      exact (hL.fderivWithin m hm z ⟨hz, show z.1 ≤ a from le_of_eq h⟩).union
        (hR.fderivWithin m hm z ⟨hz, show a ≤ z.1 from le_of_eq h.symm⟩)
    · exact ((hR.fderivWithin m hm z ⟨hz, le_of_lt h⟩).hasFDerivAt
        (half_right_mem_nhds hs hz h)).hasFDerivWithinAt
  · intro m hm z hz
    rcases lt_trichotomy z.1 a with h | h | h
    · exact (((hL.cont m hm).continuousWithinAt ⟨hz, le_of_lt h⟩).continuousAt
        (half_left_mem_nhds hs hz h)).continuousWithinAt
    · rw [← hunion]
      exact ((hL.cont m hm).continuousWithinAt ⟨hz, show z.1 ≤ a from le_of_eq h⟩).union
        ((hR.cont m hm).continuousWithinAt ⟨hz, show a ≤ z.1 from le_of_eq h.symm⟩)
    · exact (((hR.cont m hm).continuousWithinAt ⟨hz, le_of_lt h⟩).continuousAt
        (half_right_mem_nhds hs hz h)).continuousWithinAt

/-- Version of the gluing lemma yielding `ContDiffOn`. -/
theorem contDiffOn_of_halfspaces {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ × (ℝ × ℝ) → E) (N : ℕ)
    {s : Set (ℝ × (ℝ × ℝ))} (hs : IsOpen s) {a : ℝ}
    {p : (ℝ × (ℝ × ℝ)) → FormalMultilinearSeries ℝ (ℝ × (ℝ × ℝ)) E}
    (hL : HasFTaylorSeriesUpToOn N F p (s ∩ {z | z.1 ≤ a}))
    (hR : HasFTaylorSeriesUpToOn N F p (s ∩ {z | a ≤ z.1})) :
    ContDiffOn ℝ N F s :=
  (hasFTaylorSeriesUpToOn_of_halfspaces F N hs hL hR).contDiffOn

/-! ### Half-bands and the reflection preimage -/

/-- The half-band `(p, 0] × ℝ × (-δ,δ)`. -/
def halfBand (p δ : ℝ) : Set (ℝ × (ℝ × ℝ)) := Set.Ioc p 0 ×ˢ Set.univ ×ˢ Set.Ioo (-δ) δ

theorem mem_halfBand {p δ : ℝ} {z : ℝ × (ℝ × ℝ)} :
    z ∈ halfBand p δ ↔ z.1 ∈ Set.Ioc p 0 ∧ z.2.2 ∈ Set.Ioo (-δ) δ := by
  simp [halfBand, and_assoc]

theorem convex_halfBand (p δ : ℝ) : Convex ℝ (halfBand p δ) :=
  (convex_Ioc p 0).prod (convex_univ.prod (convex_Ioo (-δ) δ))

theorem uniqueDiffOn_halfBand {p δ : ℝ} (hp : p < 0) (hδ : 0 < δ) :
    UniqueDiffOn ℝ (halfBand p δ) := by
  refine uniqueDiffOn_convex (convex_halfBand p δ) ⟨(p/2, 0, 0), ?_⟩
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset (((isOpen_Ioo (a := p) (b := 0)).prod
    (isOpen_univ.prod (isOpen_Ioo (a := -δ) (b := δ)))).mem_nhds ?_) ?_
  · exact ⟨⟨by linarith, by linarith⟩, trivial, ⟨by linarith, by linarith⟩⟩
  · intro z hz
    rw [mem_halfBand]
    exact ⟨⟨hz.1.1, hz.1.2.le⟩, hz.2.2⟩

theorem esHalfL_eq_halfBand (δ : ℝ) : esHalfL δ = halfBand (-1) δ := by
  ext z
  simp only [esHalfL, esBox, halfBand, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo,
    Set.mem_univ, Set.mem_Ioc, Set.mem_setOf_eq, true_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1.1, h3⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨h1, by linarith [h2]⟩, h3⟩, h2⟩

/-- The reflection preimage of the right half is a half-band. -/
theorem preimage_halfR_eq {δ c : ℝ} (hc : c < 0) :
    (reflLin c) ⁻¹' esHalfR δ = halfBand (1/c) δ := by
  ext z
  rw [Set.mem_preimage, esHalfR, Set.mem_inter_iff, mem_esBox, mem_halfBand, Set.mem_setOf_eq]
  have hz : reflLin c z = (c * z.1, z.2.1, z.2.2) := by obtain ⟨a, b, d⟩ := z; rfl
  rw [hz]
  simp only []
  constructor
  · rintro ⟨⟨h1, h2⟩, h4⟩
    refine ⟨⟨?_, ?_⟩, h2⟩
    · rw [div_lt_iff_of_neg hc]; nlinarith [h1.2]
    · nlinarith [h4, hc]
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨⟨?_, ?_⟩, h3⟩, ?_⟩
    · nlinarith [h2, hc]
    · have := (div_lt_iff_of_neg hc).mp h1; nlinarith [this]
    · nlinarith [h2, hc]

theorem esHalfL_subset_preimage_halfR {δ c : ℝ} (hc : c ∈ Set.Ioo (-1) 0) :
    esHalfL δ ⊆ (reflLin c) ⁻¹' esHalfR δ := by
  rw [esHalfL_eq_halfBand, preimage_halfR_eq hc.2]
  intro z hz
  rw [mem_halfBand] at hz ⊢
  have hone : (1:ℝ)/c < -1 := by rw [div_lt_iff_of_neg hc.2]; linarith [hc.1]
  exact ⟨⟨lt_trans hone hz.1.1, hz.1.2⟩, hz.2⟩

/-- The two half-bands coincide eventually at a point with `τ = 0`. -/
theorem halfBand_eventuallyEq {δ c : ℝ} (hc : c ∈ Set.Ioo (-1) 0)
    {z : ℝ × (ℝ × ℝ)} (hz : z.1 = 0) :
    halfBand (-1) δ =ᶠ[𝓝 z] halfBand (1/c) δ := by
  have hone : (1:ℝ)/c < -1 := by rw [div_lt_iff_of_neg hc.2]; linarith [hc.1]
  have hU : ({w : ℝ × (ℝ × ℝ) | -1 < w.1}) ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds (by show -1 < z.1; rw [hz]; norm_num)
  refine Filter.eventually_of_mem hU ?_
  intro w hw
  apply propext
  simp only [mem_halfBand]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨hone.trans h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨show -1 < w.1 from hw, h2⟩, h3⟩

end Work.RPB.B3
