/-
  `Work.WilCrux.level_separation` — the one-level separation statement underlying the isolation
  step (N1, `WilCrux/DESIGN.md`) of the flat-sheet normal form.

  Two cells `A`, `A'` of `ℝ^{p+1}` over the *same* base `D ⊆ ℝ^p` — each a graph cell or a band
  cell over `D` — that are disjoint, cannot have a point of `A` in the closure of `A'`: **unless**
  `A` is a graph and `A'` a band, which is exactly the excluded case `hnot`.  (That case really
  does occur: over `D = {0}` the point `0` is a graph cell and `(0,1)` is a band cell whose
  closure contains `0`.)

  The mathematics is level-by-level.  Write `z ∈ ℝ^{p+1}` with base `x = Fin.init z ∈ D`.  If
  `z ∈ closure A'` then the vertical coordinate of `z` is squeezed by the level functions of `A'`
  (`graph_closure_mem`, `band_closure_bounds`), and the final contradiction comes from the
  disjointness of `A` and `A'` evaluated at the base point `x`.
-/
import Mathlib
import Submission.Work.WilCrux.SheetDefs

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology

namespace Work.WilCrux

/-! ### Two closure lemmas for the level cells -/

/-- Extraction of an open neighbourhood from membership in `𝓝[s] x`: a set which is a
`s`-neighbourhood of `x` contains `V ∩ s` for an open neighbourhood `V` of `x`. -/
private theorem exists_isOpen_nhds_of_mem_nhdsWithin {α : Type*} [TopologicalSpace α]
    {s S : Set α} {x : α} (h : S ∈ 𝓝[s] x) :
    ∃ V : Set α, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, y ∈ s → y ∈ S := by
  rw [nhdsWithin] at h
  obtain ⟨S₁, hS₁, S₂, hS₂, hEq⟩ := Filter.mem_inf_iff.mp h
  have h₂ : s ⊆ S₂ := Filter.mem_principal.mp hS₂
  obtain ⟨W, hWS₁, hWopen, hxW⟩ := mem_nhds_iff.mp hS₁
  exact ⟨W, hWopen, hxW, fun y hyW hys => hEq.symm ▸ ⟨hWS₁ hyW, h₂ hys⟩⟩

/-- If `z` lies in the closure of the graph of a function `g` continuous on `D`, and the base
point of `z` lies in `D`, then `z` sits on that graph: the closure of the graph can only leave the
graph in directions whose base point has left `D`. -/
private theorem graph_closure_mem {p : ℕ} {D : Set (Fin p → ℝ)} {g : (Fin p → ℝ) → ℝ}
    (hg : ContinuousOn g D) {z : Fin (p + 1) → ℝ}
    (hz : z ∈ closure {w : Fin (p + 1) → ℝ |
      Fin.init w ∈ D ∧ w (Fin.last p) = g (Fin.init w)})
    (hxD : Fin.init z ∈ D) :
    z (Fin.last p) = g (Fin.init z) := by
  have hinitc : Continuous (fun w : Fin (p + 1) → ℝ => Fin.init w) :=
    continuous_pi fun i => by
      simpa only [Fin.init] using (continuous_apply (Fin.castSucc i) :
        Continuous (fun w : Fin (p + 1) → ℝ => w (Fin.castSucc i)))
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · set m : ℝ := (z (Fin.last p) + g (Fin.init z)) / 2 with hm
    have h1 : z (Fin.last p) < m := by rw [hm]; linarith
    have h2 : m < g (Fin.init z) := by rw [hm]; linarith
    obtain ⟨V, hVopen, hxV, hVm⟩ := exists_isOpen_nhds_of_mem_nhdsWithin
      ((hg.continuousWithinAt hxD).preimage_mem_nhdsWithin (isOpen_Ioi.mem_nhds h2))
    set W : Set (Fin (p + 1) → ℝ) := (Fin.init ⁻¹' V) ∩ {w | w (Fin.last p) < m} with hWdef
    have hWopen : IsOpen W := by
      rw [hWdef]
      exact (hVopen.preimage hinitc).inter (isOpen_Iio.preimage (continuous_apply (Fin.last p)))
    have hzW : z ∈ W := by rw [hWdef]; exact ⟨hxV, h1⟩
    have hsub : {w : Fin (p + 1) → ℝ |
        Fin.init w ∈ D ∧ w (Fin.last p) = g (Fin.init w)} ⊆ Wᶜ := by
      intro w hw
      rw [hWdef]
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      rintro ⟨hwV, hwl⟩
      have hVw : m < g (Fin.init w) := hVm (Fin.init w) hwV hw.1
      rw [← hw.2] at hVw
      exact absurd hVw (not_lt.mpr (le_of_lt hwl))
    exact (closure_minimal hsub hWopen.isClosed_compl hz) hzW
  · set m : ℝ := (z (Fin.last p) + g (Fin.init z)) / 2 with hm
    have h1 : g (Fin.init z) < m := by rw [hm]; linarith
    have h2 : m < z (Fin.last p) := by rw [hm]; linarith
    obtain ⟨V, hVopen, hxV, hVm⟩ := exists_isOpen_nhds_of_mem_nhdsWithin
      ((hg.continuousWithinAt hxD).preimage_mem_nhdsWithin (isOpen_Iio.mem_nhds h1))
    set W : Set (Fin (p + 1) → ℝ) := (Fin.init ⁻¹' V) ∩ {w | m < w (Fin.last p)} with hWdef
    have hWopen : IsOpen W := by
      rw [hWdef]
      exact (hVopen.preimage hinitc).inter (isOpen_Ioi.preimage (continuous_apply (Fin.last p)))
    have hzW : z ∈ W := by rw [hWdef]; exact ⟨hxV, h2⟩
    have hsub : {w : Fin (p + 1) → ℝ |
        Fin.init w ∈ D ∧ w (Fin.last p) = g (Fin.init w)} ⊆ Wᶜ := by
      intro w hw
      rw [hWdef]
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      rintro ⟨hwV, hwl⟩
      have hVw : g (Fin.init w) < m := hVm (Fin.init w) hwV hw.1
      rw [← hw.2] at hVw
      exact absurd hVw (not_lt.mpr (le_of_lt hwl))
    exact (closure_minimal hsub hWopen.isClosed_compl hz) hzW

/-- If `z` lies in the closure of the band cell with level functions `a, b` continuous on `D`, and
the base point of `z` lies in `D`, then the vertical coordinate of `z` is squeezed between `a` and
`b` at that base point (the strict inequalities survive the closure as non-strict ones). -/
private theorem band_closure_bounds {p : ℕ} {D : Set (Fin p → ℝ)} {a b : (Fin p → ℝ) → EReal}
    (ha : ContinuousOn a D) (hb : ContinuousOn b D) {z : Fin (p + 1) → ℝ}
    (hz : z ∈ closure {w : Fin (p + 1) → ℝ | Fin.init w ∈ D ∧
      a (Fin.init w) < ((w (Fin.last p) : ℝ) : EReal) ∧
      ((w (Fin.last p) : ℝ) : EReal) < b (Fin.init w)})
    (hxD : Fin.init z ∈ D) :
    a (Fin.init z) ≤ ((z (Fin.last p) : ℝ) : EReal) ∧
      ((z (Fin.last p) : ℝ) : EReal) ≤ b (Fin.init z) := by
  have hinitc : Continuous (fun w : Fin (p + 1) → ℝ => Fin.init w) :=
    continuous_pi fun i => by
      simpa only [Fin.init] using (continuous_apply (Fin.castSucc i) :
        Continuous (fun w : Fin (p + 1) → ℝ => w (Fin.castSucc i)))
  constructor
  · by_contra h
    rw [not_le] at h
    obtain ⟨s, hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.mp h
    have hzs : z (Fin.last p) < s := EReal.coe_lt_coe_iff.mp hs1
    obtain ⟨V, hVopen, hxV, hVm⟩ := exists_isOpen_nhds_of_mem_nhdsWithin
      ((ha.continuousWithinAt hxD).preimage_mem_nhdsWithin (isOpen_Ioi.mem_nhds hs2))
    set W : Set (Fin (p + 1) → ℝ) := (Fin.init ⁻¹' V) ∩ {w | w (Fin.last p) < s} with hWdef
    have hWopen : IsOpen W := by
      rw [hWdef]
      exact (hVopen.preimage hinitc).inter (isOpen_Iio.preimage (continuous_apply (Fin.last p)))
    have hzW : z ∈ W := by rw [hWdef]; exact ⟨hxV, hzs⟩
    have hsub : {w : Fin (p + 1) → ℝ | Fin.init w ∈ D ∧
        a (Fin.init w) < ((w (Fin.last p) : ℝ) : EReal) ∧
        ((w (Fin.last p) : ℝ) : EReal) < b (Fin.init w)} ⊆ Wᶜ := by
      intro w hw
      rw [hWdef]
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      rintro ⟨hwV, hwl⟩
      have hVw : (s : EReal) < a (Fin.init w) := hVm (Fin.init w) hwV hw.1
      have hlt : (s : EReal) < ((w (Fin.last p) : ℝ) : EReal) := lt_trans hVw hw.2.1
      exact absurd (EReal.coe_lt_coe_iff.mp hlt) (not_lt.mpr (le_of_lt hwl))
    exact (closure_minimal hsub hWopen.isClosed_compl hz) hzW
  · by_contra h
    rw [not_le] at h
    obtain ⟨s, hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.mp h
    have hzs : s < z (Fin.last p) := EReal.coe_lt_coe_iff.mp hs2
    obtain ⟨V, hVopen, hxV, hVm⟩ := exists_isOpen_nhds_of_mem_nhdsWithin
      ((hb.continuousWithinAt hxD).preimage_mem_nhdsWithin (isOpen_Iio.mem_nhds hs1))
    set W : Set (Fin (p + 1) → ℝ) := (Fin.init ⁻¹' V) ∩ {w | s < w (Fin.last p)} with hWdef
    have hWopen : IsOpen W := by
      rw [hWdef]
      exact (hVopen.preimage hinitc).inter (isOpen_Ioi.preimage (continuous_apply (Fin.last p)))
    have hzW : z ∈ W := by rw [hWdef]; exact ⟨hxV, hzs⟩
    have hsub : {w : Fin (p + 1) → ℝ | Fin.init w ∈ D ∧
        a (Fin.init w) < ((w (Fin.last p) : ℝ) : EReal) ∧
        ((w (Fin.last p) : ℝ) : EReal) < b (Fin.init w)} ⊆ Wᶜ := by
      intro w hw
      rw [hWdef]
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      rintro ⟨hwV, hwl⟩
      have hVw : b (Fin.init w) < (s : EReal) := hVm (Fin.init w) hwV hw.1
      have hlt : ((w (Fin.last p) : ℝ) : EReal) < (s : EReal) := lt_trans hw.2.2 hVw
      exact absurd (EReal.coe_lt_coe_iff.mp hlt) (not_lt.mpr (le_of_lt hwl))
    exact (closure_minimal hsub hWopen.isClosed_compl hz) hzW

/-! ### The disjoint-interval step -/

/-- Two nonempty open intervals of `EReal` cut out by real parameters cannot both contain a common
real point; stated contrapositively: if `(a,b)` and `(a',b')` have empty intersection at the level
of real points, then a real `y` which lies in `(a,b)` and in the closed interval `[a',b']` is
impossible. -/
theorem ereal_band_disjoint {a b a' b' : EReal} (hab' : a' < b')
    (hdisj : ∀ t : ℝ, ¬ (a < (t : EReal) ∧ (t : EReal) < b ∧
      a' < (t : EReal) ∧ (t : EReal) < b'))
    {y : ℝ} (ha : a < (y : EReal)) (hb : (y : EReal) < b)
    (ha' : a' ≤ (y : EReal)) (hb' : (y : EReal) ≤ b') : False := by
  rcases lt_or_eq_of_le ha' with h1 | h1
  · rcases lt_or_eq_of_le hb' with h2 | h2
    · exact hdisj y ⟨ha, hb, h1, h2⟩
    · obtain ⟨t, ht1, ht2⟩ :=
        EReal.lt_iff_exists_real_btwn.mp (max_lt_iff.mpr ⟨ha, h1⟩)
      exact hdisj t ⟨lt_of_le_of_lt (le_max_left a a') ht1, lt_trans ht2 hb,
        lt_of_le_of_lt (le_max_right a a') ht1, h2 ▸ ht2⟩
  · rcases lt_or_eq_of_le hb' with h2 | h2
    · obtain ⟨t, ht1, ht2⟩ :=
        EReal.lt_iff_exists_real_btwn.mp (lt_min_iff.mpr ⟨hb, h2⟩)
      exact hdisj t ⟨lt_trans ha ht1, lt_of_lt_of_le ht2 (min_le_left b b'),
        h1.symm ▸ ht1, lt_of_lt_of_le ht2 (min_le_right b b')⟩
    · exact absurd (h1.trans h2) (ne_of_lt hab')

/-! ### The target -/

theorem level_separation {p : ℕ} {D : Set (Fin p → ℝ)} {A A' : Set (Fin (p + 1) → ℝ)}
    (hA : Work.WilCrux.IsGraphCellAt A D ∨ Work.WilCrux.IsBandCellAt A D)
    (hA' : Work.WilCrux.IsGraphCellAt A' D ∨ Work.WilCrux.IsBandCellAt A' D)
    (hdisj : Disjoint A A')
    (hnot : ¬ (Work.WilCrux.IsGraphCellAt A D ∧ Work.WilCrux.IsBandCellAt A' D)) :
    A ∩ closure A' = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  rw [Set.mem_inter_iff] at hz
  obtain ⟨hzA, hzcl⟩ := hz
  rcases hA with hAg | hAb
  · rcases hA' with hA'g | hA'b
    · obtain ⟨f, hf, hAeq⟩ := hAg
      obtain ⟨g, hg, hA'eq⟩ := hA'g
      have hzAlit := hAeq ▸ hzA
      have hzcllit := hA'eq ▸ hzcl
      have hxD : Fin.init z ∈ D := hzAlit.1
      have hlast : z (Fin.last p) = g (Fin.init z) := graph_closure_mem hg hzcllit hxD
      have hzA' : z ∈ A' := by rw [hA'eq]; exact ⟨hxD, hlast⟩
      exact Set.disjoint_left.mp hdisj hzA hzA'
    · exact absurd ⟨hAg, hA'b⟩ hnot
  · rcases hA' with hA'g | hA'b
    · obtain ⟨a, b, ha, hb, hab, hAeq⟩ := hAb
      obtain ⟨g, hg, hA'eq⟩ := hA'g
      have hzAlit := hAeq ▸ hzA
      have hzcllit := hA'eq ▸ hzcl
      have hxD : Fin.init z ∈ D := hzAlit.1
      have hlast : z (Fin.last p) = g (Fin.init z) := graph_closure_mem hg hzcllit hxD
      have hzA' : z ∈ A' := by rw [hA'eq]; exact ⟨hxD, hlast⟩
      exact Set.disjoint_left.mp hdisj hzA hzA'
    · obtain ⟨a, b, ha, hb, hab, hAeq⟩ := hAb
      obtain ⟨a', b', ha', hb', hab', hA'eq⟩ := hA'b
      have hzAlit := hAeq ▸ hzA
      have hzcllit := hA'eq ▸ hzcl
      have hxD : Fin.init z ∈ D := hzAlit.1
      obtain ⟨hle, hge⟩ := band_closure_bounds ha' hb' hzcllit hxD
      refine ereal_band_disjoint (hab' (Fin.init z) hxD) ?_ hzAlit.2.1 hzAlit.2.2 hle hge
      intro t ht
      obtain ⟨h1, h2, h3, h4⟩ := ht
      have hmemA : (Fin.snoc (Fin.init z) t) ∈ A := by
        rw [hAeq]
        exact ⟨by rw [Fin.init_snoc]; exact hxD,
          by rw [Fin.init_snoc, Fin.snoc_last]; exact h1,
          by rw [Fin.init_snoc, Fin.snoc_last]; exact h2⟩
      have hmemA' : (Fin.snoc (Fin.init z) t) ∈ A' := by
        rw [hA'eq]
        exact ⟨by rw [Fin.init_snoc]; exact hxD,
          by rw [Fin.init_snoc, Fin.snoc_last]; exact h3,
          by rw [Fin.init_snoc, Fin.snoc_last]; exact h4⟩
      exact Set.disjoint_left.mp hdisj hmemA hmemA'

end Work.WilCrux
