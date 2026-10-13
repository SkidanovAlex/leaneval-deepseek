/-
  WilE7 (`Work.WilE7.sheetComponent`): the sheet-component lemma of the `W_j` `Star`/`SubPf`
  presentation of the graph and band cells.

  Given a `Good` stratum `S : Stratum p (m+1)` whose part over a base set `C ⊆ ℝ^p` is covered by
  the graphs of `k` continuous, pointwise distinct maps `s j : ℝ^p → ℝ^{m+1}` (`sheetAssembly`),
  and a semi-Pfaffian set `Z ⊆ ℝ^{p+(m+1)}` together with `u₀ ∈ Z.set` defining the base set
  `C = π (connectedComponentIn Z.set u₀)`, the connected component `W_j°` of the fibre product

  `W = {(z₁, z₂) : z₁ ∈ Z.set, z₂ ∈ S.X.set, π z₁ = π z₂}`

  through the point `w₀ = (u₀, (π u₀, s j (π u₀)))` is exactly the part of `W` lying on the graph
  of `s j` over `C`:

  * every `z ∈ W_j°` has `projSnd z₂ = s j (projFirst z₂)`, and
  * for every `x ∈ C` there is `z ∈ W_j°` with `projFirst z₂ = x`.

  Proof.  Let `G = {z ∈ W : π z₂ ∈ C}` and let `O` be the component of `w₀` in `W`.

  * (base projection) `projFirst (p+q) (p+q) '' O` is preconnected (continuous image of `O`),
    contains `u₀ = projFirst (p+q) (p+q) w₀` and lies in `Z.set`; hence it lies in the component
    `connectedComponentIn Z.set u₀`.  So `π z₁ ∈ C` for `z ∈ O` and `O ⊆ G`.
  * (clopen partition) `hcov` and the pointwise injectivity of the sheets split `G` into the
    pairwise disjoint sets `A_i = {z ∈ G : projSnd z₂ = s i (projFirst z₂)}`.  Each `A_i` is closed
    in `G` by continuity of `s i` on `C`; since there are finitely many and they cover `G`, each is
    also open.  The component `O` is connected and meets `A_j` at `w₀`, so `O ⊆ A_j`: first half.
  * (cover) for `x ∈ C` choose `u ∈ connectedComponentIn Z.set u₀` with `π u = x` and put
    `z = (u, (x, s j x))`: `u ↦ z` is continuous on the component, `z` lies in `W`, and its image
    is a preconnected subset of `W` containing `w₀`, hence `z` lies in the component of `w₀`.  Its
    second factor has base `x`: second half.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.stratGraph
import Submission.Work.WilE7.sheetAssembly
import Submission.Work.WilE7.cells
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.SheetComponentDefs
import Submission.Work.WilE7.clopenPartition
import Submission.Work.WilE7.imageSubsetConnectedComponentIn
import Submission.Work.WilE7.isClosed_sheetPart

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-! ## Coordinates of the fibre-product point `sheetProductPt u₀ s j` -/

theorem projFirst_sheetProductPt {p q : ℕ} (u₀ : Fin (p + q) → ℝ) {k : ℕ}
    (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ)) (j : Fin k) :
    projFirst (p + q) (p + q) (sheetProductPt u₀ s j) = u₀ := by
  simp only [sheetProductPt, projFirst_append]

theorem projSnd_sheetProductPt {p q : ℕ} (u₀ : Fin (p + q) → ℝ) {k : ℕ}
    (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ)) (j : Fin k) :
    projSnd (p + q) (p + q) (sheetProductPt u₀ s j) =
      Fin.append (projFirst p q u₀) (s j (projFirst p q u₀)) := by
  simp only [sheetProductPt, projSnd_append]

theorem projFirst_projSnd_sheetProductPt {p q : ℕ} (u₀ : Fin (p + q) → ℝ) {k : ℕ}
    (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ)) (j : Fin k) :
    projFirst p q (projSnd (p + q) (p + q) (sheetProductPt u₀ s j)) = projFirst p q u₀ := by
  simp only [sheetProductPt, projSnd_append, projFirst_append]

/-- Membership in the connected component, unwound through the subtype. -/
theorem mem_connectedComponentIn_subtype {α : Type*} [TopologicalSpace α] {F : Set α} {x y : α}
    (hx : x ∈ F) :
    y ∈ connectedComponentIn F x ↔
      ∃ z : F, z ∈ connectedComponent ⟨x, hx⟩ ∧ (z : α) = y := by
  rw [connectedComponentIn_eq_image hx, Set.mem_image]

/-- `u ↦ sheetProductPt u s j` is continuous as soon as the sheet `s j` is continuous on a set
containing all the base projections. -/
theorem continuousOn_sheetProductPt {p q : ℕ} {C : Set (Fin p → ℝ)}
    {A : Set (Fin (p + q) → ℝ)} {k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ)) (j : Fin k)
    (hcont : ContinuousOn (s j) C) (hA : ∀ u ∈ A, projFirst p q u ∈ C) :
    ContinuousOn (fun u => sheetProductPt u s j) A := by
  have hΨ : ContinuousOn (fun x : Fin p → ℝ => Fin.append x (s j x)) C :=
    continuousOn_append hcont
  have hinner : ContinuousOn (fun u : Fin (p + q) → ℝ =>
      Fin.append (projFirst p q u) (s j (projFirst p q u))) A :=
    hΨ.comp' (continuous_projFirst p q).continuousOn (fun u hu => hA u hu)
  have hfinal : ContinuousOn (fun u : Fin (p + q) → ℝ =>
      Fin.append u (Fin.append (projFirst p q u) (s j (projFirst p q u)))) A :=
    continuousOn_append hinner
  exact hfinal

/-! ## The sheet-component lemma, with the fibre dimension `q` a variable -/

theorem sheetComponentGen {p q : ℕ} (S : Stratum p q) (hGood : S.Good) (hj : S.j = q)
    (Z : SemiPf (p + q)) (u₀ : Fin (p + q) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ)) (hC : C = Set.image (projFirst p q) (connectedComponentIn Z.set u₀))
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, projFirst p q z ∈ C → ∃ j, s j (projFirst p q z) = projSnd p q z)
    (j : Fin k) :
    (∀ z ∈ connectedComponentIn (sheetProduct p q Z S) (sheetProductPt u₀ s j),
      projSnd p q (projSnd (p + q) (p + q) z) =
        s j (projFirst p q (projSnd (p + q) (p + q) z))) ∧
    (∀ x ∈ C, ∃ z ∈ connectedComponentIn (sheetProduct p q Z S) (sheetProductPt u₀ s j),
      projFirst p q (projSnd (p + q) (p + q) z) = x) := by
  classical
  have _ := hGood
  have _ := hj
  -- the base of `u₀` lies in `C`, because `u₀` is in its own component
  have hu₀C : projFirst p q u₀ ∈ C := by
    rw [hC]
    exact ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
  have hs₀ : Fin.append (projFirst p q u₀) (s j (projFirst p q u₀)) ∈ S.X.set := hsub j _ hu₀C
  set W : Set (Fin ((p + q) + (p + q)) → ℝ) := sheetProduct p q Z S with hW
  set w₀ : Fin ((p + q) + (p + q)) → ℝ := sheetProductPt u₀ s j with hw₀
  have hw₀fst : projFirst (p + q) (p + q) w₀ = u₀ := by
    rw [hw₀]; exact projFirst_sheetProductPt u₀ s j
  -- `w₀` lies in the fibre product, over the base point `projFirst p q u₀ ∈ C`
  have hw₀W : w₀ ∈ W := by
    rw [hW, mem_sheetProduct]
    exact ⟨by rw [hw₀, projFirst_sheetProductPt]; exact hu₀,
      by rw [hw₀, projSnd_sheetProductPt]; exact hs₀,
      by rw [hw₀, projFirst_sheetProductPt, projSnd_sheetProductPt, projFirst_append]⟩
  have hw₀G : w₀ ∈ sheetBase Z S C := by
    refine ⟨hw₀W, ?_⟩
    rw [hw₀, projSnd_sheetProductPt, projFirst_append]
    exact hu₀C
  -- ## every point of the component bases over `C`
  have hbase : ∀ z ∈ connectedComponentIn W w₀,
      projFirst p q (projSnd (p + q) (p + q) z) ∈ C := by
    intro z hz
    have hzW : z ∈ W := connectedComponentIn_subset W w₀ hz
    have hzZ : projFirst (p + q) (p + q) z ∈ connectedComponentIn Z.set u₀ := by
      have h := imageSubsetConnectedComponentIn (hs := isPreconnected_connectedComponentIn)
        (f := projFirst (p + q) (p + q)) (hf := (continuous_projFirst (p + q) (p + q)).continuousOn)
        (x := w₀) (hx := mem_connectedComponentIn hw₀W) (F := Z.set)
        (hF := fun y hy => (connectedComponentIn_subset W w₀ hy).1) z hz
      simpa [hw₀fst] using h
    have h1 : projFirst p q (projFirst (p + q) (p + q) z) ∈ C := by
      rw [hC]; exact ⟨_, hzZ, rfl⟩
    rw [← hzW.2.2]
    exact h1
  -- ## the component of `w₀` in `W` is its component in `G = sheetBase Z S C`
  have hOG : connectedComponentIn W w₀ ⊆ sheetBase Z S C :=
    fun z hz => ⟨connectedComponentIn_subset W w₀ hz, hbase z hz⟩
  have hcomp : connectedComponentIn W w₀ = connectedComponentIn (sheetBase Z S C) w₀ := by
    refine subset_antisymm ?_ ?_
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hw₀W) hOG
    · exact connectedComponentIn_mono w₀ (fun z hz => hz.1)
  -- ## `G` is partitioned into the sheet pieces `sheetPart s G i`
  have hcover : ∀ x : sheetBase Z S C, ∃ i : Fin k, x ∈ sheetPart s (sheetBase Z S C) i := by
    intro x
    have hxW : x.1 ∈ W := x.2.1
    obtain ⟨i, hi⟩ := hcov (projSnd (p + q) (p + q) x.1) hxW.2.1 x.2.2
    exact ⟨i, by rw [mem_sheetPart]; exact hi.symm⟩
  have hdisj : ∀ i i' : Fin k, i ≠ i' →
      Disjoint (sheetPart s (sheetBase Z S C) i) (sheetPart s (sheetBase Z S C) i') := by
    intro i i' hii'
    rw [Set.disjoint_left]
    intro x hxi hxi'
    rw [mem_sheetPart] at hxi hxi'
    exact hii' (hinj _ x.2.2 (hxi.symm.trans hxi'))
  have hcl : ∀ i : Fin k, IsClosed (sheetPart s (sheetBase Z S C) i) :=
    fun i => isClosed_sheetPart s hcont (fun z hz => hz.2) i
  have hclopen : IsClopen (sheetPart s (sheetBase Z S C) j) :=
    clopenPartition (sheetPart s (sheetBase Z S C)) hcover hdisj hcl j
  have hw₀part : (⟨w₀, hw₀G⟩ : sheetBase Z S C) ∈ sheetPart s (sheetBase Z S C) j := by
    rw [mem_sheetPart]
    show projSnd p q (projSnd (p + q) (p + q) w₀) =
      s j (projFirst p q (projSnd (p + q) (p + q) w₀))
    simp only [hw₀, projSnd_sheetProductPt, projFirst_append, projSnd_append]
  have hcc : connectedComponent (⟨w₀, hw₀G⟩ : sheetBase Z S C) ⊆
      sheetPart s (sheetBase Z S C) j :=
    hclopen.connectedComponent_subset hw₀part
  refine ⟨?_, ?_⟩
  · -- ## first half: the component lies on the graph of `s j`
    intro z hz
    have hzG : z ∈ connectedComponentIn (sheetBase Z S C) w₀ := hcomp ▸ hz
    rw [mem_connectedComponentIn_subtype hw₀G] at hzG
    obtain ⟨y, hy, hyz⟩ := hzG
    have hy' : y ∈ sheetPart s (sheetBase Z S C) j := hcc hy
    rw [mem_sheetPart] at hy'
    rw [← hyz]
    exact hy'
  · -- ## second half: the component projects onto `C`
    intro x hx
    rw [hC] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨sheetProductPt u s j, ?_, ?_⟩
    · have hζcont : ContinuousOn (fun u' : Fin (p + q) → ℝ => sheetProductPt u' s j)
          (connectedComponentIn Z.set u₀) :=
        continuousOn_sheetProductPt s j (hcont j) (fun u' hu' => by
          rw [hC]; exact ⟨u', hu', rfl⟩)
      have himg : ∀ y ∈ connectedComponentIn Z.set u₀, sheetProductPt y s j ∈ W := by
        intro y hy
        rw [hW, mem_sheetProduct]
        exact ⟨by rw [projFirst_sheetProductPt]; exact connectedComponentIn_subset Z.set u₀ hy,
          by rw [projSnd_sheetProductPt]; exact hsub j _ (by rw [hC]; exact ⟨y, hy, rfl⟩),
          by rw [projFirst_sheetProductPt, projSnd_sheetProductPt, projFirst_append]⟩
      have h := imageSubsetConnectedComponentIn (hs := isPreconnected_connectedComponentIn)
        (f := fun u' : Fin (p + q) → ℝ => sheetProductPt u' s j) (hf := hζcont)
        (x := u₀) (hx := mem_connectedComponentIn hu₀) (F := W) (hF := himg) u hu
      simpa [hw₀] using h
    · rw [projSnd_sheetProductPt, projFirst_append]

/-! ## The requested lemma -/

theorem sheetComponent
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1)) (hGood : S.Good) (hj : S.j = m + 1)
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j, s j (WilkiesDesign.E.projFirst p (m + 1) z) = WilkiesDesign.E.projSnd p (m + 1) z)
    (j : Fin k) :
    (∀ z ∈ connectedComponentIn {z : Fin ((p + (m + 1)) + (p + (m + 1))) → ℝ |
        WilkiesDesign.E.projFirst (p + (m + 1)) (p + (m + 1)) z ∈ Z.set ∧
        WilkiesDesign.E.projSnd (p + (m + 1)) (p + (m + 1)) z ∈ S.X.set ∧
        WilkiesDesign.E.projFirst p (m + 1) (WilkiesDesign.E.projFirst (p + (m + 1)) (p + (m + 1)) z) =
          WilkiesDesign.E.projFirst p (m + 1) (WilkiesDesign.E.projSnd (p + (m + 1)) (p + (m + 1)) z)}
      (Fin.append u₀ (Fin.append (WilkiesDesign.E.projFirst p (m + 1) u₀) (s j (WilkiesDesign.E.projFirst p (m + 1) u₀)))),
      WilkiesDesign.E.projSnd p (m + 1) (WilkiesDesign.E.projSnd (p + (m + 1)) (p + (m + 1)) z) =
        s j (WilkiesDesign.E.projFirst p (m + 1) (WilkiesDesign.E.projSnd (p + (m + 1)) (p + (m + 1)) z))) ∧
    (∀ x ∈ C, ∃ z ∈ connectedComponentIn {z : Fin ((p + (m + 1)) + (p + (m + 1))) → ℝ |
        WilkiesDesign.E.projFirst (p + (m + 1)) (p + (m + 1)) z ∈ Z.set ∧
        WilkiesDesign.E.projSnd (p + (m + 1)) (p + (m + 1)) z ∈ S.X.set ∧
        WilkiesDesign.E.projFirst p (m + 1) (WilkiesDesign.E.projFirst (p + (m + 1)) (p + (m + 1)) z) =
          WilkiesDesign.E.projFirst p (m + 1) (WilkiesDesign.E.projSnd (p + (m + 1)) (p + (m + 1)) z)}
      (Fin.append u₀ (Fin.append (WilkiesDesign.E.projFirst p (m + 1) u₀) (s j (WilkiesDesign.E.projFirst p (m + 1) u₀)))),
      WilkiesDesign.E.projFirst p (m + 1) (WilkiesDesign.E.projSnd (p + (m + 1)) (p + (m + 1)) z) = x) :=
  sheetComponentGen (p := p) (q := m + 1) S hGood hj Z u₀ hu₀ C hC k s hcont hinj hsub hcov j

end Work.WilE7
