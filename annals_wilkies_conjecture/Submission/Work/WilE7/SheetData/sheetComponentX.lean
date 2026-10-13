import Mathlib
import Submission.Work.WilE7.SheetData.DefsX

namespace Work.WilE7.SheetData

open Classical
open WilkiesDesign WilkiesDesign.E

/-- The sheet-component lemma with the stratum `S` replaced by a bare semi-Pfaffian set `X`.

This is `Work.WilE7.sheetComponentGen` with `S.X.set` everywhere replaced by `X.set`; the
`Good` hypothesis and the value of `S.j` of that lemma are never used, so the same proof applies
to an arbitrary semi-Pfaffian `X`. -/
theorem sheetComponentX {p q : ℕ} (X Z : WilkiesDesign.E.SemiPf (p + q))
    (u₀ : Fin (p + q) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p q) (connectedComponentIn Z.set u₀))
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (hcov : ∀ z ∈ X.set, WilkiesDesign.E.projFirst p q z ∈ C →
      ∃ j, s j (WilkiesDesign.E.projFirst p q z) = WilkiesDesign.E.projSnd p q z)
    (j : Fin k) :
    (∀ z ∈ connectedComponentIn (Work.WilE7.SheetData.sheetProductX p q Z X)
        (Work.WilE7.sheetProductPt u₀ s j),
      WilkiesDesign.E.projSnd p q
        (WilkiesDesign.E.projSnd (p + q) (p + q) z) =
        s j (WilkiesDesign.E.projFirst p q
          (WilkiesDesign.E.projSnd (p + q) (p + q) z))) ∧
    (∀ x ∈ C, ∃ z ∈ connectedComponentIn (Work.WilE7.SheetData.sheetProductX p q Z X)
        (Work.WilE7.sheetProductPt u₀ s j),
      WilkiesDesign.E.projFirst p q
        (WilkiesDesign.E.projSnd (p + q) (p + q) z) = x) := by
  -- the base of `u₀` lies in `C`, because `u₀` is in its own component
  have hu₀C : WilkiesDesign.E.projFirst p q u₀ ∈ C := by
    rw [hC]
    exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
  have hs₀ : Fin.append (WilkiesDesign.E.projFirst p q u₀)
      (s j (WilkiesDesign.E.projFirst p q u₀)) ∈ X.set := hsub j _ hu₀C
  set W : Set (Fin ((p + q) + (p + q)) → ℝ) := sheetProductX p q Z X with hW
  set w₀ : Fin ((p + q) + (p + q)) → ℝ := Work.WilE7.sheetProductPt u₀ s j with hw₀
  have hw₀fst : WilkiesDesign.E.projFirst (p + q) (p + q) w₀ = u₀ := by
    rw [hw₀]; exact Work.WilE7.projFirst_sheetProductPt u₀ s j
  -- `w₀` lies in the fibre product, over the base point `projFirst p q u₀ ∈ C`
  have hw₀W : w₀ ∈ W := by
    rw [hW, mem_sheetProductX]
    exact ⟨by rw [hw₀, Work.WilE7.projFirst_sheetProductPt]; exact hu₀,
      by rw [hw₀, Work.WilE7.projSnd_sheetProductPt]; exact hs₀,
      by rw [hw₀, Work.WilE7.projFirst_sheetProductPt, Work.WilE7.projSnd_sheetProductPt,
        Work.WilE7.projFirst_append]⟩
  have hw₀G : w₀ ∈ sheetBaseX p q Z X C := by
    refine ⟨hw₀W, ?_⟩
    rw [hw₀, Work.WilE7.projSnd_sheetProductPt, Work.WilE7.projFirst_append]
    exact hu₀C
  -- ## every point of the component bases over `C`
  have hbase : ∀ z ∈ connectedComponentIn W w₀,
      WilkiesDesign.E.projFirst p q (WilkiesDesign.E.projSnd (p + q) (p + q) z) ∈ C := by
    intro z hz
    have hzW : z ∈ W := connectedComponentIn_subset W w₀ hz
    have hzZ : WilkiesDesign.E.projFirst (p + q) (p + q) z ∈ connectedComponentIn Z.set u₀ := by
      have h := Work.WilE7.imageSubsetConnectedComponentIn (hs := isPreconnected_connectedComponentIn)
        (f := WilkiesDesign.E.projFirst (p + q) (p + q))
        (hf := (continuous_projFirst (p + q) (p + q)).continuousOn)
        (x := w₀) (hx := mem_connectedComponentIn hw₀W) (F := Z.set)
        (hF := fun y hy => (connectedComponentIn_subset W w₀ hy).1) z hz
      simpa [hw₀fst] using h
    have h1 : WilkiesDesign.E.projFirst p q
        (WilkiesDesign.E.projFirst (p + q) (p + q) z) ∈ C := by
      rw [hC]; exact ⟨_, hzZ, rfl⟩
    rw [← hzW.2.2]
    exact h1
  -- ## the component of `w₀` in `W` is its component in `G = sheetBaseX p q Z X C`
  have hOG : connectedComponentIn W w₀ ⊆ sheetBaseX p q Z X C :=
    fun z hz => ⟨connectedComponentIn_subset W w₀ hz, hbase z hz⟩
  have hcomp : connectedComponentIn W w₀ = connectedComponentIn (sheetBaseX p q Z X C) w₀ := by
    refine subset_antisymm ?_ ?_
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hw₀W) hOG
    · exact connectedComponentIn_mono w₀ (fun z hz => hz.1)
  -- ## `G` is partitioned into the sheet pieces `sheetPart s G i`
  have hcover : ∀ x : sheetBaseX p q Z X C, ∃ i : Fin k, x ∈ sheetPart s (sheetBaseX p q Z X C) i := by
    intro x
    have hxW : x.1 ∈ W := x.2.1
    obtain ⟨i, hi⟩ := hcov (WilkiesDesign.E.projSnd (p + q) (p + q) x.1) hxW.2.1 x.2.2
    exact ⟨i, by rw [Work.WilE7.mem_sheetPart]; exact hi.symm⟩
  have hdisj : ∀ i i' : Fin k, i ≠ i' →
      Disjoint (sheetPart s (sheetBaseX p q Z X C) i) (sheetPart s (sheetBaseX p q Z X C) i') := by
    intro i i' hii'
    rw [Set.disjoint_left]
    intro x hxi hxi'
    rw [Work.WilE7.mem_sheetPart] at hxi hxi'
    exact hii' (hinj _ x.2.2 (hxi.symm.trans hxi'))
  have hcl : ∀ i : Fin k, IsClosed (sheetPart s (sheetBaseX p q Z X C) i) :=
    fun i => Work.WilE7.isClosed_sheetPart s hcont (fun z hz => hz.2) i
  have hclopen : IsClopen (sheetPart s (sheetBaseX p q Z X C) j) :=
    Work.WilE7.clopenPartition (sheetPart s (sheetBaseX p q Z X C)) hcover hdisj hcl j
  have hw₀part : (⟨w₀, hw₀G⟩ : sheetBaseX p q Z X C) ∈ sheetPart s (sheetBaseX p q Z X C) j := by
    rw [Work.WilE7.mem_sheetPart]
    show WilkiesDesign.E.projSnd p q (WilkiesDesign.E.projSnd (p + q) (p + q) w₀) =
      s j (WilkiesDesign.E.projFirst p q (WilkiesDesign.E.projSnd (p + q) (p + q) w₀))
    simp only [hw₀, Work.WilE7.projSnd_sheetProductPt, Work.WilE7.projFirst_append,
      Work.WilE7.projSnd_append]
  have hcc : connectedComponent (⟨w₀, hw₀G⟩ : sheetBaseX p q Z X C) ⊆
      sheetPart s (sheetBaseX p q Z X C) j :=
    hclopen.connectedComponent_subset hw₀part
  refine ⟨?_, ?_⟩
  · -- ## first half: the component lies on the graph of `s j`
    intro z hz
    have hzG : z ∈ connectedComponentIn (sheetBaseX p q Z X C) w₀ := hcomp ▸ hz
    rw [Work.WilE7.mem_connectedComponentIn_subtype hw₀G] at hzG
    obtain ⟨y, hy, hyz⟩ := hzG
    have hy' : y ∈ sheetPart s (sheetBaseX p q Z X C) j := hcc hy
    rw [Work.WilE7.mem_sheetPart] at hy'
    rw [← hyz]
    exact hy'
  · -- ## second half: the component projects onto `C`
    intro x hx
    rw [hC] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨Work.WilE7.sheetProductPt u s j, ?_, ?_⟩
    · have hζcont : ContinuousOn (fun u' : Fin (p + q) → ℝ => Work.WilE7.sheetProductPt u' s j)
          (connectedComponentIn Z.set u₀) :=
        Work.WilE7.continuousOn_sheetProductPt s j (hcont j) (fun u' hu' => by
          rw [hC]; exact ⟨u', hu', rfl⟩)
      have himg : ∀ y ∈ connectedComponentIn Z.set u₀, Work.WilE7.sheetProductPt y s j ∈ W := by
        intro y hy
        rw [hW, mem_sheetProductX]
        exact ⟨by rw [Work.WilE7.projFirst_sheetProductPt]; exact connectedComponentIn_subset Z.set u₀ hy,
          by rw [Work.WilE7.projSnd_sheetProductPt]; exact hsub j _ (by rw [hC]; exact ⟨y, hy, rfl⟩),
          by rw [Work.WilE7.projFirst_sheetProductPt, Work.WilE7.projSnd_sheetProductPt,
            Work.WilE7.projFirst_append]⟩
      have h := Work.WilE7.imageSubsetConnectedComponentIn (hs := isPreconnected_connectedComponentIn)
        (f := fun u' : Fin (p + q) → ℝ => Work.WilE7.sheetProductPt u' s j) (hf := hζcont)
        (x := u₀) (hx := mem_connectedComponentIn hu₀) (F := W) (hF := himg) u hu
      simpa [hw₀] using h
    · rw [Work.WilE7.projSnd_sheetProductPt, Work.WilE7.projFirst_append]

end Work.WilE7.SheetData
