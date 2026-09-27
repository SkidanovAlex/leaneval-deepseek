import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Api
import Submission.Work.Engulf.E4alt.ShellPrep

open Set Metric PL

namespace Work.Engulf.E4alt

/-- **`E4b`'s collision analysis, pointwise form.**

Let `x` lie in the `i`-th shelled simplex `ord[i]` (a core face, `f '' simp (ord i)` in the
`5/8`-cube), let `lam` be another core face whose simplex is already engulfed
(`simp lam ⊆ K ∪ ⋃_{j<i} ∂ ord[j]`), and let `A_τ`, `A_lam` be the affine witnesses of `ND.g₁` on
them.  If `A_τ x = A_lam y` for some `y ∈ simp lam`, then either `x` already lies on the floor
`floorOf τ₀ τ₁` of the joining simplex or in the previously attached part `⋃_{j<i} ∂ ord[j]`, or
the collision point `A_τ x` lies in the exceptional set `D` of the pair bound.

This is the point-set content of `E4b`: the two non-`D` alternatives of the pair bound land on the
attached part.  In the first alternative (`A_τ x ∈ A_τ '' simp (ord i ∩ lam)`) the injectivity of
`A_τ` on `simp (ord i)` puts `x` itself in `simp lam`, and `hlam_eng` + `H7.meetK` finish.  In the
second (`A_τ x ∈ A_τ '' simp (ord i ∩ Fzv) ∩ A_lam '' simp (lam ∩ Fzv)`) injectivity puts `x` in
the frozen hull `simp (ord i ∩ Fzv) ⊆ L` (`NormData.Fzv_hull`), the corresponding point `w` of the
frozen hull of `lam` also lies in `L` (`Fzv_hull` for `lam`), and `g₁` agrees with `f` on `L`
(`NormData.g₁frz`), so `H7.clean` forces `x = w`; again `x ∈ simp lam` and `hlam_eng` finish. -/
theorem collisionOfPair {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M}
    {ε : ℝ} (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    {i : ℕ} (hi : i < ND.ord.length)
    (hτcore : f '' PL.simp (ND.ord[i]) ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ))
    {lam : Finset (PL.E N)} (hlam : lam ∈ ND.Γ₁.faces)
    (hlam_core : f '' PL.simp lam ⊆ ψ.toFun '' PL.closedCube (5 / 8 : ℝ))
    (hlam_eng : PL.simp lam ⊆ K ∪ ⋃ j ∈ Finset.range i, ⋃ (hj : j < ND.ord.length),
        ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w))
    (A_τ A_lam : PL.E N →ᵃ[ℝ] PL.E n)
    (hτwit : ∀ x ∈ PL.simp (ND.ord[i]), ND.g₁ x = ψ.toFun (A_τ x))
    (hlam_wit : ∀ x ∈ PL.simp lam, ND.g₁ x = ψ.toFun (A_lam x))
    (hτinj : Set.InjOn A_τ (PL.simp (ND.ord[i])))
    (D : Set (PL.E n))
    (hDmem : A_τ '' PL.simp (ND.ord[i]) ∩ A_lam '' PL.simp lam ⊆
      A_τ '' PL.simp (ND.ord[i] ∩ lam) ∪
        (A_τ '' PL.simp (ND.ord[i] ∩ ND.Fzv) ∩ A_lam '' PL.simp (lam ∩ ND.Fzv)) ∪ D)
    {x : PL.E N} (hx : x ∈ PL.simp (ND.ord[i])) {y : PL.E N} (hy : y ∈ PL.simp lam)
    (heq : A_τ x = A_lam y) :
    x ∈ PL.simp (ND.ord[i]) ∩ (Work.Engulf.floorOf τ₀ τ₁ ∪
        ⋃ j ∈ Finset.range i, ⋃ (hj : j < ND.ord.length),
          ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w)) ∨ A_τ x ∈ D := by
  have hτmem : ND.ord[i] ∈ ND.Γ₁.faces := ND.ord_mem _ (List.getElem_mem hi)
  have hsubΔ : PL.simp (ND.ord[i]) ⊆ PL.simp (τ₀ ∪ τ₁) := ND.ord_sub _ (List.getElem_mem hi)
  have hxΔ : x ∈ PL.simp (τ₀ ∪ τ₁) := hsubΔ hx
  -- once `x ∈ simp lam` the conclusion follows from `hlam_eng` and `H7.meetK`
  have hconcl : x ∈ PL.simp lam → x ∈ PL.simp (ND.ord[i]) ∩
      (Work.Engulf.floorOf τ₀ τ₁ ∪ ⋃ j ∈ Finset.range i, ⋃ (hj : j < ND.ord.length),
        ⋃ w ∈ ND.ord[j], PL.simp (ND.ord[j].erase w)) := by
    intro hxslam
    rcases hlam_eng hxslam with hK | hunion
    · exact ⟨hx, Or.inl (by
        have hKm : x ∈ K ∩ PL.simp (τ₀ ∪ τ₁) := ⟨hK, hxΔ⟩
        rwa [H7.meetK] at hKm)⟩
    · exact ⟨hx, Or.inr hunion⟩
  -- `A_τ x` lies in the intersection of the two images
  have hmem : A_τ x ∈ A_τ '' PL.simp (ND.ord[i]) ∩ A_lam '' PL.simp lam :=
    ⟨⟨x, hx, rfl⟩, ⟨y, hy, heq.symm⟩⟩
  rcases hDmem hmem with (hA | hB) | hD
  · -- the collision already happens inside `simp (ord[i] ∩ lam)`
    obtain ⟨z, hz, hzx⟩ := hA
    have hzs : z ∈ PL.simp (ND.ord[i]) :=
      Work.Engulf.simp_mono Finset.inter_subset_left hz
    have hzeq : z = x := hτinj hzs hx hzx
    have hzslam : z ∈ PL.simp lam :=
      Work.Engulf.simp_mono Finset.inter_subset_right hz
    have hxslam : x ∈ PL.simp lam := by rw [← hzeq]; exact hzslam
    exact Or.inl (hconcl hxslam)
  · -- the collision happens inside the frozen hulls
    obtain ⟨hzB, hwB⟩ := hB
    obtain ⟨z, hz, hzx⟩ := hzB
    obtain ⟨w, hw, hwx⟩ := hwB
    have hzs : z ∈ PL.simp (ND.ord[i]) :=
      Work.Engulf.simp_mono Finset.inter_subset_left hz
    have hzeq : z = x := hτinj hzs hx hzx
    -- `x` is a frozen point of the core face, hence lies in `L`
    have hxFzv : x ∈ PL.simp (ND.ord[i] ∩ ND.Fzv) := by rw [← hzeq]; exact hz
    have hxL : x ∈ L := ND.Fzv_hull _ hτmem hτcore hxFzv
    have hwlam : w ∈ PL.simp lam :=
      Work.Engulf.simp_mono Finset.inter_subset_left hw
    have hwL : w ∈ L := ND.Fzv_hull lam hlam hlam_core hw
    -- `g₁` agrees with `f` on `L`, so the two points have the same `f`-image
    have hfx : f x = ψ.toFun (A_τ x) := by rw [← ND.g₁frz hxL, hτwit x hx]
    have hfw : f w = ψ.toFun (A_lam w) := by rw [← ND.g₁frz hwL, hlam_wit w hwlam]
    have hfeq : f x = f w := by rw [hfx, hfw, hwx]
    -- `w` lies in `K ∪ simp (τ₀ ∪ τ₁)`, so `H7.clean` applies
    have hwKΔ : w ∈ K ∪ PL.simp (τ₀ ∪ τ₁) := by
      rcases hlam_eng hwlam with hK | hU
      · exact Or.inl hK
      · refine Or.inr ?_
        obtain ⟨j, hjmem, h1⟩ := Set.mem_iUnion₂.mp hU
        obtain ⟨hjlen, h2⟩ := Set.mem_iUnion.mp h1
        obtain ⟨w', hw', hxw'⟩ := Set.mem_iUnion₂.mp h2
        exact ND.ord_sub _ (List.getElem_mem hjlen)
          (Work.Engulf.simp_mono (Finset.erase_subset w' _) hxw')
    have hxw : x = w := H7.clean x ⟨hxΔ, hxL⟩ w ⟨hwKΔ, hwL⟩ hfeq
    have hxslam : x ∈ PL.simp lam := by rw [hxw]; exact hwlam
    exact Or.inl (hconcl hxslam)
  · exact Or.inr hD

end Work.Engulf.E4alt
