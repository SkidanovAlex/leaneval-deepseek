import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.TailBand
import Submission.Work.ELRig.range_lift_closed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set

/-- **The horizontal window at a given level is finite.**

Let `f : ℝ → ℂ` be `1`-periodic up to the translation `w ↦ w + 1`
(`f (s + 1) = f s + 1`), and suppose that its `Im`-level set at height `c` over one
period is finite.  Then only finitely many *real parts* of points of `range f` lying on the
horizontal line `Im = c` fall into a bounded window `[A, B]`.

Indeed, `f s = f (Int.fract s) + ⌊s⌋` (`Work.ELRig.periodicShift_translate`), so every such real
part is of the form `(f r).re + n` with `r = Int.fract s ∈ [0,1)` in the (finite) level set and
`n = ⌊s⌋ : ℤ`; the constraint `A ≤ (f r).re + n ≤ B` leaves only finitely many `n` for each of
the finitely many `r`. -/
theorem finite_re_level_window {f : ℝ → ℂ} (hper : ∀ s : ℝ, f (s + 1) = f s + 1) (c A B : ℝ)
    (hT : ({s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (f s).im = c}).Finite) :
    Set.Finite {y : ℝ | ∃ s : ℝ, (f s).im = c ∧ y = (f s).re ∧ A ≤ y ∧ y ≤ B} := by
  set T : Set ℝ := {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (f s).im = c} with hTdef
  have hinner : ∀ r : ℝ,
      Set.Finite {y : ℝ | ∃ n : ℤ, y = (f r).re + (n : ℝ) ∧ A ≤ y ∧ y ≤ B} := by
    intro r
    have hN : Set.Finite {n : ℤ | A ≤ (f r).re + (n : ℝ) ∧ (f r).re + (n : ℝ) ≤ B} := by
      refine Set.Finite.subset (Set.finite_Icc ⌈A - (f r).re⌉ ⌊B - (f r).re⌋) ?_
      intro n hn
      rw [Set.mem_setOf_eq] at hn
      rw [Set.mem_Icc]
      exact ⟨(Int.ceil_le).mpr (by linarith [hn.1]), (Int.le_floor).mpr (by linarith [hn.2])⟩
    refine (hN.image (fun n : ℤ => (f r).re + (n : ℝ))).subset ?_
    rintro y ⟨n, rfl, hA', hB'⟩
    exact ⟨n, ⟨hA', hB'⟩, rfl⟩
  refine (hT.biUnion (fun r _ => hinner r)).subset ?_
  rintro y ⟨s, hsim, rfl, hA, hB⟩
  have hshift := periodicShift_translate f hper ⌊s⌋ (Int.fract s)
  rw [Int.fract_add_floor] at hshift
  have him2 : (f (Int.fract s)).im = (f s).im := by
    rw [hshift, Complex.add_im, Complex.intCast_im, add_zero]
  have hre2 : (f s).re = (f (Int.fract s)).re + (⌊s⌋ : ℝ) := by
    rw [hshift, Complex.add_re, Complex.intCast_re]
  refine Set.mem_biUnion (x := Int.fract s) (y := (f s).re) ?_ ?_
  · rw [hTdef]
    exact ⟨⟨Int.fract_nonneg s, Int.fract_lt_one s⟩, by rw [him2, hsim]⟩
  · exact ⟨⌊s⌋, by rw [hre2], hA, hB⟩

theorem cyl_horizontal_isolated {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) {u w : ℂ}
    (hfin₁ : ({s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im}).Finite)
    (hfin₂ : ({s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}).Finite)
    (hwΛ : w ∈ Set.range L.γ₁ ∪ Set.range L.γ₂)
    (hwim : w.im = u.im) (hwre₀ : u.re ≤ w.re) (hwre₁ : w.re ≤ u.re + 1) :
    ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      w + t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
      w - t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
  -- the window of real parts of the two lifts on the horizontal line `Im = u.im`
  set Y₁ : Set ℝ := {y : ℝ | ∃ s : ℝ, (L.γ₁ s).im = u.im ∧ y = (L.γ₁ s).re ∧
    u.re - 1 ≤ y ∧ y ≤ u.re + 2} with hY₁def
  set Y₂ : Set ℝ := {y : ℝ | ∃ s : ℝ, (L.γ₂ s).im = u.im ∧ y = (L.γ₂ s).re ∧
    u.re - 1 ≤ y ∧ y ≤ u.re + 2} with hY₂def
  have hYfin : (Y₁ ∪ Y₂).Finite :=
    (finite_re_level_window L.per₁ u.im (u.re - 1) (u.re + 2) hfin₁).union
      (finite_re_level_window L.per₂ u.im (u.re - 1) (u.re + 2) hfin₂)
  have hmemY : ∀ z : ℂ, z.im = u.im → u.re - 1 ≤ z.re → z.re ≤ u.re + 2 →
      z ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ → z.re ∈ Y₁ ∪ Y₂ := by
    intro z hzim hz0 hz1 hzr
    rcases hzr with h | h
    · left
      obtain ⟨s, hs⟩ := h
      exact ⟨s, by rw [hs]; exact hzim, by rw [hs], hz0, hz1⟩
    · right
      obtain ⟨s, hs⟩ := h
      exact ⟨s, by rw [hs]; exact hzim, by rw [hs], hz0, hz1⟩
  -- the least positive distance from `w.re` to the other real parts
  set S : Finset ℝ :=
    ((hYfin.toFinset.filter (fun y => y ≠ w.re)).image (fun y => |y - w.re|)) ∪ {1} with hSdef
  have hSne : S.Nonempty := by
    rw [hSdef]
    exact ⟨1, Finset.mem_union_right _ (Finset.mem_singleton_self 1)⟩
  set δ : ℝ := S.min' hSne with hδdef
  have hδmem : δ ∈ S := by rw [hδdef]; exact Finset.min'_mem S hSne
  have hδle : ∀ y ∈ S, δ ≤ y := by
    intro y hy
    rw [hδdef]
    exact Finset.min'_le S y hy
  have hδpos : 0 < δ := by
    rw [hSdef] at hδmem
    rcases Finset.mem_union.mp hδmem with h | h
    · rcases Finset.mem_image.mp h with ⟨y, hy, hyeq⟩
      rw [← hyeq]
      exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hy).2)
    · rw [Finset.mem_singleton.mp h]
      norm_num
  have hδ1 : δ ≤ 1 :=
    hδle 1 (by rw [hSdef]; exact Finset.mem_union_right _ (Finset.mem_singleton_self 1))
  refine ⟨δ, hδpos, ?_⟩
  intro t ht
  rw [Set.mem_Ioo] at ht
  obtain ⟨ht0, htδ⟩ := ht
  have ht1 : t < 1 := lt_of_lt_of_le htδ hδ1
  have hstep : ∀ v : ℂ, v.im = u.im → u.re - 1 ≤ v.re → v.re ≤ u.re + 2 →
      v.re ≠ w.re → |v.re - w.re| = t → v ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ → False := by
    intro v hvim hv0 hv1 hvne hvt hvmem
    have hmemS : |v.re - w.re| ∈ S := by
      rw [hSdef]
      refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v.re, ?_, rfl⟩)
      exact Finset.mem_filter.mpr
        ⟨(hYfin.mem_toFinset).mpr (hmemY v hvim hv0 hv1 hvmem), hvne⟩
    have := hδle _ hmemS
    rw [hvt] at this
    linarith
  constructor
  · intro hmem
    refine hstep (w + (t : ℂ)) ?_ ?_ ?_ ?_ ?_ hmem
    · simp only [Complex.add_im, Complex.ofReal_im, add_zero]
      exact hwim
    · simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    · simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    · intro hcontr
      have hre : (w + (t : ℂ)).re = w.re + t := by
        simp only [Complex.add_re, Complex.ofReal_re]
      rw [hre] at hcontr
      linarith
    · have hre : (w + (t : ℂ)).re - w.re = t := by
        simp only [Complex.add_re, Complex.ofReal_re]
        ring
      rw [hre, abs_of_pos ht0]
  · intro hmem
    refine hstep (w - (t : ℂ)) ?_ ?_ ?_ ?_ ?_ hmem
    · simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact hwim
    · simp only [Complex.sub_re, Complex.ofReal_re]
      linarith
    · simp only [Complex.sub_re, Complex.ofReal_re]
      linarith
    · intro hcontr
      have hre : (w - (t : ℂ)).re = w.re - t := by
        simp only [Complex.sub_re, Complex.ofReal_re]
      rw [hre] at hcontr
      linarith
    · have hre : (w - (t : ℂ)).re - w.re = -t := by
        simp only [Complex.sub_re, Complex.ofReal_re]
        ring
      rw [hre, abs_neg, abs_of_pos ht0]

end Work.ELRig
