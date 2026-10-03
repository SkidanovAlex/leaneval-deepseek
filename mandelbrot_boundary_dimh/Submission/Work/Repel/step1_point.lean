import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.basinEnters.zero_not_mem_basin
import Submission.Work.L62.basin_iface
import Submission.Work.Horn.basic

/-!
# REPEL, Step 1: the initial point of the lifted inverse orbit

(Shishikura, §6, Step 1.)  Let `f₀` be a parabolic germ with §4.1 data `d : ParabData f₀ D₀` and
horn data `hd : HornData d`, and let `z` be an inverse orbit of `f₀` with `z 0 = 0`, `z j ∈ D₀`
for `j ≥ 1`, `z → 0` and `z` not identically `0`.  Then there is a lift `w ∈ d.Dφ` with
`d.φ (w - j) = z j` for all `j` (this is Lemma 5.1 = the field `ParabData.invOrbit`) and, in
addition, `π w ∉ {0} ∪ π(Bu ∪ Bl)`; the latter is exactly the paper's remark that
`π(w̃₀) ∉ Dom(g₀)`, because `z 0 = 0` is *not* in the parabolic basin (`φ w = z 0 = 0`), while
`π(Bu ∪ Bl)` is the `π`-image of a `ℤ`-invariant subset of `d.DE = d.φ ⁻¹' (basin)` — so a
`π`-preimage of a point of `π(Bu ∪ Bl)` in `d.DE` (up to an integer shift) would itself lie in
`d.DE`.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

/-- **REPEL Step 1.**  The lifted inverse orbit `{w - j}` of the inverse orbit `{z j}` of `0`
avoiding the parabolic basin. -/
theorem step1_point {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (hd : HornData d)
    (hinf : IsParabolicGerm f₀ D₀)
    (z : ℕ → ℂ) (hz0 : z 0 = 0) (hzrec : ∀ j : ℕ, f₀ (z (j + 1)) = z j)
    (hztend : Tendsto z atTop (𝓝 0)) (hzD : ∀ j : ℕ, 1 ≤ j → z j ∈ D₀)
    (hzne : ∃ j : ℕ, z j ≠ 0) :
    ∃ w : ℂ, w ∈ d.Dφ ∧ (∀ j : ℕ, w - j ∈ d.Dφ ∧ d.φ (w - j) = z j) ∧
      piExp w ∉ insert 0 (piExp '' (hd.Bu ∪ hd.Bl)) := by
  -- Lemma 5.1: the lifted inverse orbit
  obtain ⟨w, hwDφ, hw, -⟩ := d.invOrbit z hzD hzrec hztend hzne
  -- `φ w = z 0 = 0`, and `0` is not in the parabolic basin
  have hφw : d.φ w = 0 := by
    have h := (hw 0).2
    rw [hz0] at h
    simpa using h
  have hwDE : w ∉ d.DE := by
    intro hmem
    rw [Work.Horn.MandelDim.ParabData.mem_DE] at hmem
    have hb : d.φ w ∈ ParabolicBasin f₀ D₀ := hmem.2
    rw [hφw] at hb
    exact Work.Parab.basinEnters.zero_not_mem_parabolicBasin hinf hb
  refine ⟨w, hwDφ, hw, ?_⟩
  rw [Set.mem_insert_iff, not_or]
  refine ⟨Work.Horn.MandelDim.piExp_ne_zero w, ?_⟩
  -- a `π`-preimage in `Bu ∪ Bl` would put `w` itself in `Bu ∪ Bl ⊆ d.DE`
  rintro ⟨w', hw', hπ⟩
  obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp hπ
  have hT : MandelDim.IsTInvariant (hd.Bu ∪ hd.Bl) := fun v => by
    simp only [Set.mem_union, hd.Bu_T v, hd.Bl_T v]
  have hmem' : w' + ((-k : ℤ) : ℂ) ∈ hd.Bu ∪ hd.Bl :=
    Work.Horn.MandelDim.IsTInvariant.add_int hT hw' (-k)
  have heq : w' + ((-k : ℤ) : ℂ) = w := by
    rw [hk]; push_cast; ring
  exact hwDE (hd.sub (heq ▸ hmem'))

end Work.Repel
