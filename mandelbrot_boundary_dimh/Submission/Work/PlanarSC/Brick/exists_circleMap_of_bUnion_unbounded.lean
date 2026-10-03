import Mathlib
import Submission.Work.PlanarSC.Brick
import Submission.Work.HornSC.Cells
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.HornSC.ScaleComponent.isBounded_connectedComponentIn_mul
import Submission.Work.PlanarSC.Brick.exists_enclosing_wall_circle
import Submission.Work.PlanarSC.Brick.noPinch_brickCells
import Submission.Lib.Unif2.Commons.Topology.Jordan.plane_separation
import Submission.Lib.Unif2.Commons.Topology.Connected.frontier_component_compl_range

/-!
# The frontier of the unbounded component of the complement of a union of bricks

The bricks `bcell h p` of the brick-wall tiling are unions of *two* unit cells of the lattice
`h·ℤ²`; a brick-cell set is therefore a finite union of unit cells with the extra property that
the two cells of each brick occur together (`NoPinch`).  For such a cell set the frontier of the
unbounded complementary component is a single simple closed polygonal curve, which is the
HornSC `wallSet` cycle decomposition result applied to the cell model.

The main theorem is `exists_circleMap_of_bUnion_unbounded`.
-/

namespace Work.PlanarSC.Brick

open Set

noncomputable section

/-! ## The scaled lattice and the cell model of a brick union -/

/-- The point `h * (m + j I)` of the lattice `h ℤ²`. -/
def latPt (h : ℝ) (p : ℤ × ℤ) : ℂ := (h : ℂ) * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)

@[simp] theorem latPt_re (h : ℝ) (p : ℤ × ℤ) : (latPt h p).re = h * (p.1 : ℝ) := by
  simp [latPt, Complex.mul_re]

@[simp] theorem latPt_im (h : ℝ) (p : ℤ × ℤ) : (latPt h p).im = h * (p.2 : ℝ) := by
  simp [latPt, Complex.mul_re]

/-- The image of a subset of `ℂ` under the similarity `z ↦ c * z`. -/
def simScale (c : ℂ) (S : Set ℂ) : Set ℂ := (fun z => c * z) '' S

theorem mem_simScale {c : ℂ} {S : Set ℂ} {z : ℂ} : z ∈ simScale c S ↔ ∃ w ∈ S, c * w = z := Iff.rfl

/-- The two unit cells of the brick `p = (i,j)`, namely `(2i + j % 2, j)` and `(2i + j % 2 + 1, j)`. -/
def brickCellsOf (p : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {(2 * p.1 + p.2 % 2, p.2), (2 * p.1 + p.2 % 2 + 1, p.2)}

/-- The set of unit cells covered by the bricks indexed by `A`. -/
def brickCellSet (A : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) := A.biUnion brickCellsOf

theorem mem_brickCellsOf {p c : ℤ × ℤ} :
    c ∈ brickCellsOf p ↔ c = (2 * p.1 + p.2 % 2, p.2) ∨ c = (2 * p.1 + p.2 % 2 + 1, p.2) := by
  simp [brickCellsOf]

theorem mem_brickCellSet {A : Finset (ℤ × ℤ)} {c : ℤ × ℤ} :
    c ∈ brickCellSet A ↔ ∃ p ∈ A, c ∈ brickCellsOf p := by
  simp [brickCellSet, Finset.mem_biUnion]

/-! ## Scaled cells -/

/-- `z` lies in the scaled cell `h · cell (a,b)` iff its coordinates lie between the scaled
bounds. -/
theorem mem_simScale_cell {h : ℝ} (hh : 0 < h) {a b : ℤ} {z : ℂ} :
    z ∈ simScale (h : ℂ) (Work.HornSC.cell (a, b)) ↔
      (a : ℝ) * h ≤ z.re ∧ z.re ≤ ((a : ℝ) + 1) * h ∧
        (b : ℝ) * h ≤ z.im ∧ z.im ≤ ((b : ℝ) + 1) * h := by
  have hne : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hi : 0 < h⁻¹ := inv_pos.mpr hh
  have hmul : ∀ w : ℂ, (h : ℂ) * (↑(h⁻¹ : ℝ) * w) = w := by
    intro w
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hh.ne', Complex.ofReal_one, one_mul]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Work.HornSC.mem_cell] at hw
    obtain ⟨h1, h2, h3, h4⟩ := hw
    have e1 : ((h : ℂ) * w).re = h * w.re := by simp [Complex.mul_re]
    have e2 : ((h : ℂ) * w).im = h * w.im := by simp [Complex.mul_im]
    rw [e1, e2]
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    refine ⟨↑(h⁻¹ : ℝ) * z, ?_, hmul z⟩
    rw [Work.HornSC.mem_cell]
    have e1 : (↑(h⁻¹ : ℝ) * z : ℂ).re = h⁻¹ * z.re := by simp [Complex.mul_re]
    have e2 : (↑(h⁻¹ : ℝ) * z : ℂ).im = h⁻¹ * z.im := by simp [Complex.mul_im]
    rw [e1, e2]
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc (a : ℝ) = h⁻¹ * ((a : ℝ) * h) := by
            rw [mul_comm ((a : ℝ)) h, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
        _ ≤ h⁻¹ * z.re := mul_le_mul_of_nonneg_left h1 hi.le
    · calc h⁻¹ * z.re ≤ h⁻¹ * (((a : ℝ) + 1) * h) := mul_le_mul_of_nonneg_left h2 hi.le
        _ = (a : ℝ) + 1 := by
            rw [mul_comm (((a : ℝ) + 1)) h, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
    · calc (b : ℝ) = h⁻¹ * ((b : ℝ) * h) := by
            rw [mul_comm ((b : ℝ)) h, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
        _ ≤ h⁻¹ * z.im := mul_le_mul_of_nonneg_left h3 hi.le
    · calc h⁻¹ * z.im ≤ h⁻¹ * (((b : ℝ) + 1) * h) := mul_le_mul_of_nonneg_left h4 hi.le
        _ = (b : ℝ) + 1 := by
            rw [mul_comm (((b : ℝ) + 1)) h, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]

/-- A brick is the scaled union of its two unit cells. -/
theorem bcell_eq_simScale {h : ℝ} (hh : 0 < h) (p : ℤ × ℤ) :
    bcell h p = simScale (h : ℂ)
      (Work.HornSC.cell (2 * p.1 + p.2 % 2, p.2) ∪
        Work.HornSC.cell (2 * p.1 + p.2 % 2 + 1, p.2)) := by
  have hun : simScale (h : ℂ)
      (Work.HornSC.cell (2 * p.1 + p.2 % 2, p.2) ∪
        Work.HornSC.cell (2 * p.1 + p.2 % 2 + 1, p.2)) =
      simScale (h : ℂ) (Work.HornSC.cell (2 * p.1 + p.2 % 2, p.2)) ∪
        simScale (h : ℂ) (Work.HornSC.cell (2 * p.1 + p.2 % 2 + 1, p.2)) := by
    simp only [simScale]
    exact Set.image_union (fun z : ℂ => (h : ℂ) * z) _ _
  rw [hun]
  have hA : ((↑(2 * p.1 + p.2 % 2) : ℝ) + 1) * h = (↑(2 * p.1 + p.2 % 2) : ℝ) * h + h := by ring
  have hB : (↑(2 * p.1 + p.2 % 2 + 1) : ℝ) * h = (↑(2 * p.1 + p.2 % 2) : ℝ) * h + h := by
    push_cast; ring
  have hC : (↑(2 * p.1 + p.2 % 2 + 2) : ℝ) * h = (↑(2 * p.1 + p.2 % 2) : ℝ) * h + 2 * h := by
    push_cast; ring
  have hD : ((↑(2 * p.1 + p.2 % 2 + 1) : ℝ) + 1) * h =
      (↑(2 * p.1 + p.2 % 2) : ℝ) * h + 2 * h := by push_cast; ring
  ext z
  rw [mem_bcell, Set.mem_union, mem_simScale_cell hh, mem_simScale_cell hh]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rcases le_total z.re ((↑(2 * p.1 + p.2 % 2) : ℝ) * h + h) with hle | hle
    · exact Or.inl ⟨h1, by rw [hA]; exact hle, h3, h4⟩
    · exact Or.inr ⟨by rw [hB]; exact hle, by rw [hD]; rw [hC] at h2; exact h2, h3, h4⟩
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨h1, by rw [hA] at h2; rw [hC]; linarith, h3, h4⟩
    · exact ⟨by rw [hB] at h1; linarith, by rw [hD] at h2; rw [hC]; linarith, h3, h4⟩

theorem bcell_subset_simScale_brickCellSet {h : ℝ} (hh : 0 < h) {A : Finset (ℤ × ℤ)} {p : ℤ × ℤ}
    (hp : p ∈ A) : bcell h p ⊆ simScale (h : ℂ) (Work.HornSC.cellUnion (brickCellSet A)) := by
  intro z hz
  rw [bcell_eq_simScale hh] at hz
  rw [mem_simScale] at hz ⊢
  obtain ⟨w, hw, hzw⟩ := hz
  refine ⟨w, ?_, hzw⟩
  rw [Work.HornSC.cellUnion, Set.mem_iUnion₂]
  rcases hw with hw | hw
  · exact ⟨(2 * p.1 + p.2 % 2, p.2),
      mem_brickCellSet.mpr ⟨p, hp, mem_brickCellsOf.mpr (Or.inl rfl)⟩, hw⟩
  · exact ⟨(2 * p.1 + p.2 % 2 + 1, p.2),
      mem_brickCellSet.mpr ⟨p, hp, mem_brickCellsOf.mpr (Or.inr rfl)⟩, hw⟩

theorem bUnion_eq_simScale {h : ℝ} (hh : 0 < h) (A : Finset (ℤ × ℤ)) :
    bUnion h A = simScale (h : ℂ) (Work.HornSC.cellUnion (brickCellSet A)) := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rw [mem_bUnion] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    exact bcell_subset_simScale_brickCellSet hh hp hzp
  · intro z hz
    rw [mem_simScale] at hz
    obtain ⟨w, hw, hzw⟩ := hz
    rw [Work.HornSC.cellUnion, Set.mem_iUnion₂] at hw
    obtain ⟨c, hc, hwc⟩ := hw
    rw [mem_brickCellSet] at hc
    obtain ⟨p, hp, hpc⟩ := hc
    rw [mem_bUnion]
    refine ⟨p, hp, ?_⟩
    rw [bcell_eq_simScale hh, mem_simScale]
    refine ⟨w, ?_, hzw⟩
    rcases mem_brickCellsOf.mp hpc with rfl | rfl
    · exact Or.inl hwc
    · exact Or.inr hwc


/-! ## The frontier of the unbounded component of a no-pinch cell union -/

set_option maxHeartbeats 1600000 in
theorem exists_circleMap_of_cellUnion_of_noPinch {B : Finset (ℤ × ℤ)}
    (hne : B.Nonempty) (hnp : Work.HornSC.NoPinch B)
    (hconn : IsConnected (Work.HornSC.cellUnion B)) {x₀ : ℂ}
    (hx₀ : x₀ ∉ Work.HornSC.cellUnion B)
    (hxu : ¬ Bornology.IsBounded (connectedComponentIn ((Work.HornSC.cellUnion B)ᶜ) x₀)) :
    ∃ γ : C(Circle, ℂ), Function.Injective γ ∧
      Set.range γ = frontier (connectedComponentIn ((Work.HornSC.cellUnion B)ᶜ) x₀) := by
  classical
  obtain ⟨γ, hγinj, hγsub, hγenc⟩ := exists_enclosing_wall_circle hne hnp hconn
  have hγK : Set.range γ ⊆ Work.HornSC.cellUnion B :=
    hγsub.trans (wallSet_subset_cellUnion B)
  obtain ⟨A, B', hAo, hBo, hAc, hBc, hAB, hAbdd, hBunbdd, hABun⟩ :=
    Commons.Topology.Jordan.plane_separation γ hγinj
  have hABun' : (Set.range γ)ᶜ ⊆ A ∪ B' := le_of_eq hABun.symm
  have hABun'' : B' ⊆ (Set.range γ)ᶜ := fun z hz => hABun ▸ Or.inr hz
  have hAun : A ⊆ (Set.range γ)ᶜ := fun z hz => hABun ▸ Or.inl hz
  -- the complement of the curve is not preconnected
  have hnp' : ¬ IsPreconnected (Set.range γ)ᶜ := by
    intro hp
    obtain ⟨a, ha⟩ := hAc.nonempty
    obtain ⟨b, hb⟩ := hBc.nonempty
    rcases hp.subset_or_subset hAo hBo hAB hABun' with h | h
    · exact Set.disjoint_left.mp hAB (h (hABun'' hb)) hb
    · exact Set.disjoint_left.mp hAB ha (h (hAun ha))
  -- the two complementary components are the connected components of the complement
  have hcompA : ∀ a ∈ A, connectedComponentIn ((Set.range γ)ᶜ) a = A := by
    intro a ha
    have hamem : a ∈ (Set.range γ)ᶜ := hAun ha
    refine Set.Subset.antisymm ?_ ?_
    · have hsub : connectedComponentIn ((Set.range γ)ᶜ) a ⊆ (Set.range γ)ᶜ :=
        connectedComponentIn_subset _ _
      rcases IsPreconnected.subset_or_subset (s := connectedComponentIn ((Set.range γ)ᶜ) a)
        hAo hBo hAB (fun z hz => hABun' (hsub hz)) (isPreconnected_connectedComponentIn) with h | h
      · exact h
      · exact absurd (Set.disjoint_left.mp hAB ha (h (mem_connectedComponentIn hamem))) (by simp)
    · exact hAc.isPreconnected.subset_connectedComponentIn ha hAun
  have hcompB : ∀ b ∈ B', connectedComponentIn ((Set.range γ)ᶜ) b = B' := by
    intro b hb
    have hbmem : b ∈ (Set.range γ)ᶜ := hABun'' hb
    refine Set.Subset.antisymm ?_ ?_
    · have hsub : connectedComponentIn ((Set.range γ)ᶜ) b ⊆ (Set.range γ)ᶜ :=
        connectedComponentIn_subset _ _
      rcases IsPreconnected.subset_or_subset (s := connectedComponentIn ((Set.range γ)ᶜ) b)
        hAo hBo hAB (fun z hz => hABun' (hsub hz)) (isPreconnected_connectedComponentIn) with h | h
      · exact absurd (Set.disjoint_left.mp hAB (h (mem_connectedComponentIn hbmem)) hb) (by simp)
      · exact h
    · exact hBc.isPreconnected.subset_connectedComponentIn hb hABun''
  have hfrontA : frontier A = Set.range γ := by
    obtain ⟨a, ha⟩ := hAc.nonempty
    have := Commons.Topology.Connected.frontier_component_compl_range γ hγinj hnp' a (hAun ha)
    rwa [hcompA a ha] at this
  have hfrontB : frontier B' = Set.range γ := by
    obtain ⟨b, hb⟩ := hBc.nonempty
    have := Commons.Topology.Connected.frontier_component_compl_range γ hγinj hnp' b (hABun'' hb)
    rwa [hcompB b hb] at this
  -- the unbounded component of the complement of the cell union
  have hUK : connectedComponentIn ((Work.HornSC.cellUnion B)ᶜ) x₀ ⊆ (Set.range γ)ᶜ := by
    intro z hz
    simp only [Set.mem_compl_iff]
    intro hzγ
    exact (connectedComponentIn_subset _ _ hz) (hγK hzγ)
  have hUB' : connectedComponentIn ((Work.HornSC.cellUnion B)ᶜ) x₀ ⊆ B' := by
    rcases IsPreconnected.subset_or_subset (s := connectedComponentIn ((Work.HornSC.cellUnion B)ᶜ) x₀)
      hAo hBo hAB (fun z hz => hABun' (hUK hz)) (isPreconnected_connectedComponentIn) with h | h
    · exact absurd (hAbdd.subset h) hxu
    · exact h
  have hB'sub : B' ⊆ (Work.HornSC.cellUnion B)ᶜ := by
    intro z hzB
    by_contra hzK
    have hzK' : z ∈ Work.HornSC.cellUnion B := by simpa only [Set.mem_compl_iff, not_not] using hzK
    have hbdd := hγenc z hzK'
    rw [hcompB z hzB] at hbdd
    exact hBunbdd hbdd
  have hB'U : B' ⊆ connectedComponentIn ((Work.HornSC.cellUnion B)ᶜ) x₀ := by
    intro z hzB
    have hzK' : z ∈ (Work.HornSC.cellUnion B)ᶜ := hB'sub hzB
    have hcont : B' ⊆ connectedComponentIn ((Work.HornSC.cellUnion B)ᶜ) z :=
      hBc.isPreconnected.subset_connectedComponentIn hzB hB'sub
    have hbdd : ¬ Bornology.IsBounded (connectedComponentIn ((Work.HornSC.cellUnion B)ᶜ) z) :=
      fun h => hBunbdd (h.subset hcont)
    have hxK' : x₀ ∈ (Work.HornSC.cellUnion B)ᶜ := by simpa only [Set.mem_compl_iff] using hx₀
    have huniq := Commons.Topology.Jordan.compl_compact_unique_unbounded
      (Work.HornSC.isCompact_cellUnion B) hzK' hxK' hbdd hxu
    rw [← huniq]
    exact mem_connectedComponentIn hzK'
  have hUeq : connectedComponentIn ((Work.HornSC.cellUnion B)ᶜ) x₀ = B' :=
    Set.Subset.antisymm hUB' hB'U
  exact ⟨γ, hγinj, by rw [hUeq, hfrontB]⟩

/-! ## The similarity `z ↦ h z` and the final assembly -/

theorem simScale_frontier_component {h : ℝ} (hh : 0 < h) {S : Set ℂ} {x : ℂ} (hx : x ∈ Sᶜ) :
    simScale (h : ℂ) (frontier (connectedComponentIn Sᶜ x)) =
      frontier (connectedComponentIn ((simScale (h : ℂ) S)ᶜ) ((h : ℂ) * x)) := by
  have hne : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set Φ : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero (h : ℂ) hne with hΦdef
  have hΦcoe : ⇑Φ = fun z : ℂ => (h : ℂ) * z := by
    funext z; simp [hΦdef, Homeomorph.smulOfNeZero, Homeomorph.smul, smul_eq_mul]
  have himg : ∀ T : Set ℂ, simScale (h : ℂ) T = Φ '' T := by
    intro T; rw [simScale, hΦcoe]
  have hbij : Function.Bijective (fun z : ℂ => (h : ℂ) * z) :=
    ⟨fun a b hab => mul_left_cancel₀ hne hab,
     fun w => ⟨(h : ℂ)⁻¹ * w, by
       change (h : ℂ) * ((h : ℂ)⁻¹ * w) = w
       rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]⟩⟩
  have hcompl : simScale (h : ℂ) Sᶜ = (simScale (h : ℂ) S)ᶜ := by
    simp only [simScale]; exact Set.image_compl_eq hbij
  have hcomp : connectedComponentIn ((simScale (h : ℂ) S)ᶜ) ((h : ℂ) * x) =
      Φ '' connectedComponentIn Sᶜ x := by
    rw [Homeomorph.image_connectedComponentIn Φ hx, ← himg (Sᶜ), hcompl, hΦcoe]
  rw [hcomp, ← Homeomorph.image_frontier Φ, ← himg]

theorem exists_circleMap_of_bUnion_unbounded {h : ℝ} (hh : 0 < h) {A : Finset (ℤ × ℤ)}
    (hA : IsConnected (Work.PlanarSC.Brick.bUnion h A)) {z₀ : ℂ}
    (hz₀ : z₀ ∉ Work.PlanarSC.Brick.bUnion h A)
    (hz₀u : ¬ Bornology.IsBounded (connectedComponentIn ((Work.PlanarSC.Brick.bUnion h A)ᶜ) z₀)) :
    ∃ γ : C(Circle, ℂ), Function.Injective γ ∧
      Set.range γ = frontier (connectedComponentIn ((Work.PlanarSC.Brick.bUnion h A)ᶜ) z₀) := by
  classical
  have hne0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set B : Finset (ℤ × ℤ) := brickCellSet A with hBdef
  have hsc : Work.PlanarSC.Brick.bUnion h A = simScale (h : ℂ) (Work.HornSC.cellUnion B) :=
    bUnion_eq_simScale hh A
  set x₀ : ℂ := (h : ℂ)⁻¹ * z₀ with hx₀def
  have hmul : (h : ℂ) * x₀ = z₀ := by
    rw [hx₀def]
    change (h : ℂ) * ((h : ℂ)⁻¹ * z₀) = z₀
    rw [← mul_assoc, mul_inv_cancel₀ hne0, one_mul]
  have hconn : IsConnected (Work.HornSC.cellUnion B) := by
    have hA' : IsConnected (simScale (h : ℂ) (Work.HornSC.cellUnion B)) := hsc ▸ hA
    set Φ : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero (h : ℂ) hne0 with hΦdef
    have hΦcoe : ⇑Φ = fun z : ℂ => (h : ℂ) * z := by
      funext z; simp [hΦdef, Homeomorph.smulOfNeZero, Homeomorph.smul, smul_eq_mul]
    have hscΦ : simScale (h : ℂ) (Work.HornSC.cellUnion B) = Φ '' Work.HornSC.cellUnion B := by
      rw [simScale, hΦcoe]
    have hcancel : Φ.symm '' (Φ '' Work.HornSC.cellUnion B) = Work.HornSC.cellUnion B := by
      ext z; constructor
      · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩; simpa using hv
      · intro hz; exact ⟨Φ z, ⟨z, hz, rfl⟩, Φ.symm_apply_apply z⟩
    have := hA'.image Φ.symm Φ.symm.continuous.continuousOn
    rw [hscΦ, hcancel] at this
    exact this
  have hne : B.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon] at hconn
    exact hconn.nonempty.ne_empty (by simp [Work.HornSC.cellUnion])
  have hnp : Work.HornSC.NoPinch B := by
    rw [hBdef]
    show Work.HornSC.NoPinch (A.biUnion fun p : ℤ × ℤ =>
      ({(2 * p.1 + p.2 % 2, p.2), (2 * p.1 + p.2 % 2 + 1, p.2)} : Finset (ℤ × ℤ)))
    exact noPinch_brickCells A
  have hx₀ : x₀ ∉ Work.HornSC.cellUnion B := by
    intro hxin
    refine hz₀ ?_
    rw [hsc]
    exact ⟨x₀, hxin, hmul⟩
  have hxu : ¬ Bornology.IsBounded (connectedComponentIn ((Work.HornSC.cellUnion B)ᶜ) x₀) := by
    intro hb
    refine hz₀u ?_
    have hK : Bornology.IsBounded
        (connectedComponentIn ((simScale (h : ℂ) (Work.HornSC.cellUnion B))ᶜ) ((h : ℂ) * x₀)) := by
      simpa only [simScale] using Work.HornSC.ScaleComponent.isBounded_connectedComponentIn_mul hh
        (K := Work.HornSC.cellUnion B) (a := x₀) hb
    rw [hmul, ← hsc] at hK
    exact hK
  obtain ⟨γ, hγinj, hγrng⟩ :=
    exists_circleMap_of_cellUnion_of_noPinch hne hnp hconn hx₀ hxu
  refine ⟨⟨fun t => (h : ℂ) * γ t, by fun_prop⟩, ?_, ?_⟩
  · rintro s t hst
    exact hγinj (mul_left_cancel₀ hne0 hst)
  · have hrange : Set.range (fun t : Circle => (h : ℂ) * γ t) = simScale (h : ℂ) (Set.range γ) := by
      ext z; constructor
      · rintro ⟨t, rfl⟩; exact ⟨γ t, ⟨t, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨t, rfl⟩, rfl⟩; exact ⟨t, rfl⟩
    change Set.range (fun t : Circle => (h : ℂ) * γ t) =
      frontier (connectedComponentIn ((Work.PlanarSC.Brick.bUnion h A)ᶜ) z₀)
    rw [hrange, hγrng, simScale_frontier_component hh hx₀, ← hsc, hmul]

end

end Work.PlanarSC.Brick
