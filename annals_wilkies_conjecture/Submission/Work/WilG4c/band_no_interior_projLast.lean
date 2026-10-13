import Mathlib
import Submission.Work.WilG1.Cell.thin_union
import Submission.Work.Wilkies.Defs

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilG4c

/-!
# Bands with empty interior project to sets with empty interior

Let `C ⊆ ℝ^m` and let `Z ⊆ ℝ^{m+1}` be the band over `C` cut out by two `EReal`-valued
boundary functions `a < b` that are continuous on `C`:

  `z ∈ Z ↔ Fin.init z ∈ C ∧ a (Fin.init z) < z (last) < b (Fin.init z)`.

Then the projection `WilkiesDesign.projLast Z` is exactly `C` (every point of `C` admits a
real strictly between `a` and `b`), and `interior Z = ∅` forces `interior C = ∅`: over an
*interior* point of `C` the band is open, since `a`, `b` are continuous there and the
strict inequality `a < b` leaves room for a small vertical window.
-/

/-- A real number strictly between two extended reals. -/
theorem exists_real_btwn_EReal {a b : EReal} (h : a < b) :
    ∃ t : ℝ, a < (t : EReal) ∧ (t : EReal) < b :=
  EReal.lt_iff_exists_real_btwn.mp h

/-- If `x` is an interior point of `C`, then any band over `C` with continuous
`EReal`-valued bounds `a < b` has nonempty interior. -/
theorem interior_band_nonempty {m : ℕ} {Z : Set (Fin (m + 1) → ℝ)} {C : Set (Fin m → ℝ)}
    {a b : (Fin m → ℝ) → EReal}
    (ha : ContinuousOn a C) (hb : ContinuousOn b C) (hab : ∀ x ∈ C, a x < b x)
    (hmem : ∀ z : Fin (m + 1) → ℝ, z ∈ Z ↔ Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧
      ((z (Fin.last m) : ℝ) : EReal) < b (Fin.init z))
    {x : Fin m → ℝ} (hx : x ∈ interior C) : (interior Z).Nonempty := by
  have hxC : x ∈ C := interior_subset hx
  have habx : a x < b x := hab x hxC
  -- a point `t` of the band and a strictly smaller / larger pair of reals
  obtain ⟨t, ht1, ht2⟩ := exists_real_btwn_EReal habx
  obtain ⟨t1, ht1a, ht1t⟩ := exists_real_btwn_EReal ht1
  obtain ⟨t2, htt2, ht2b⟩ := exists_real_btwn_EReal ht2
  -- `t1 < t < t2`
  have ht1t' : t1 < t := EReal.coe_lt_coe_iff.mp ht1t
  have htt2' : t < t2 := EReal.coe_lt_coe_iff.mp htt2
  have hx_nhds : C ∈ 𝓝 x :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset
  have ha_cont : ContinuousAt a x := ha.continuousAt hx_nhds
  have hb_cont : ContinuousAt b x := hb.continuousAt hx_nhds
  -- the piece of the base on which `a < t1` and `t2 < b`
  set V : Set (Fin m → ℝ) :=
    {y | a y < (t1 : EReal)} ∩ {y | (t2 : EReal) < b y} ∩ C with hV
  have hVnhds : V ∈ 𝓝 x := by
    rw [hV]
    exact Filter.inter_mem (Filter.inter_mem
      (ha_cont.preimage_mem_nhds ((isOpen_Iio' (t1 : EReal)).mem_nhds ht1a))
      (hb_cont.preimage_mem_nhds ((isOpen_Ioi' (t2 : EReal)).mem_nhds ht2b))) hx_nhds
  -- the distinguished point of the band
  set z : Fin (m + 1) → ℝ := Fin.snoc x t with hz
  have hzi : Fin.init z = x := by rw [hz, Fin.init_snoc]
  have hzl : z (Fin.last m) = t := by rw [hz, Fin.snoc_last]
  refine ⟨z, ?_⟩
  rw [mem_interior_iff_mem_nhds]
  -- a neighbourhood of `z` consisting of points whose base is in `V` and whose last
  -- coordinate stays in the window `(t1, t2)`
  have hW1 : Fin.init ⁻¹' V ∈ 𝓝 z := by
    have hπ : ContinuousAt (fun w : Fin (m + 1) → ℝ => Fin.init w) z :=
      continuousAt_id.finInit
    exact hπ.preimage_mem_nhds (show V ∈ 𝓝 (Fin.init z) from by rw [hzi]; exact hVnhds)
  have hW2 : {z' : Fin (m + 1) → ℝ | z' (Fin.last m) ∈ Set.Ioo t1 t2} ∈ 𝓝 z := by
    have hc : ContinuousAt (fun z' : Fin (m + 1) → ℝ => z' (Fin.last m)) z :=
      (continuous_apply (Fin.last m)).continuousAt
    exact hc.preimage_mem_nhds
      (show Set.Ioo t1 t2 ∈ 𝓝 (z (Fin.last m)) from by
        rw [hzl]; exact isOpen_Ioo.mem_nhds ⟨ht1t', htt2'⟩)
  refine Filter.mem_of_superset (Filter.inter_mem hW1 hW2) (fun z' hz' => ?_)
  obtain ⟨hz'V, hz'I⟩ := hz'
  rw [hV] at hz'V
  obtain ⟨⟨hz'a, hz'b⟩, hz'C⟩ := hz'V
  exact (hmem z').mpr ⟨hz'C,
    lt_trans hz'a (EReal.coe_lt_coe_iff.mpr hz'I.1),
    lt_trans (EReal.coe_lt_coe_iff.mpr hz'I.2) hz'b⟩

theorem band_no_interior_projLast {m : ℕ} {Z : Set (Fin (m + 1) → ℝ)}
    {C : Set (Fin m → ℝ)} {a b : (Fin m → ℝ) → EReal}
    (ha : ContinuousOn a C) (hb : ContinuousOn b C) (hab : ∀ x ∈ C, a x < b x)
    (hmem : ∀ z : Fin (m + 1) → ℝ, z ∈ Z ↔ Fin.init z ∈ C ∧
      a (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧
      ((z (Fin.last m) : ℝ) : EReal) < b (Fin.init z))
    (hInt : interior Z = ∅) : ¬ (interior (WilkiesDesign.projLast Z)).Nonempty := by
  -- the projection of a band over `C` is exactly `C`
  have hproj : WilkiesDesign.projLast Z = C := by
    ext x
    constructor
    · rintro ⟨t, ht⟩
      simpa using ((hmem (Fin.snoc x t)).mp ht).1
    · intro hx
      obtain ⟨t, ht1, ht2⟩ := exists_real_btwn_EReal (hab x hx)
      exact ⟨t, (hmem (Fin.snoc x t)).mpr ⟨by simpa using hx, by simpa using ht1,
        by simpa using ht2⟩⟩
  rw [hproj]
  rintro ⟨x, hx⟩
  obtain ⟨z, hz⟩ := interior_band_nonempty ha hb hab hmem hx
  rw [hInt] at hz
  exact hz

end Work.WilG4c
