import Submission.Work.Drive.ManifoldParity.InterSetDefs

/-!
# The product picture and the `ℝ⁵` picture

The target `Work.Drive.transverse_inter_boundary_parity` counts pairs `(s,t) ∈ ℝ² × ℝ³`; the mod-2
chapter works in `ℝ⁵` via the block identification `mkPart : ℝ² × ℝ³ → ℝ⁵`.  This file records the
translation of the boundary intersection set and of its cardinality.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

theorem sqPart_mkPart (s : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 3)) :
    sqPart (mkPart s t) = s := by
  have h : sqPart (mkPart s t) = sqPartCLM (mkPart s t) := (sqPartCLM_eq_sqPart _).symm
  rw [h, sqPartCLM_mkPart]

theorem cbPart_mkPart (s : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 3)) :
    cbPart (mkPart s t) = t := by
  have h : cbPart (mkPart s t) = cbPartCLM (mkPart s t) := (cbPartCLM_eq_cbPart _).symm
  rw [h, cbPartCLM_mkPart]

/-- The two block projections jointly invert `mkPart`. -/
theorem mkPart_sqPart_cbPart (x : Amb 4) : mkPart (sqPart x) (cbPart x) = x := by
  ext i
  revert i
  refine Fin.addCases (m := 2) (n := 3)
    (motive := fun i => mkPart (sqPart x) (cbPart x) i = x i) ?_ ?_
  · intro i
    show mkPart (sqPart x) (cbPart x) (sqIdx i) = x (sqIdx i)
    rw [mkPart_sqIdx, sqPart_apply]
  · intro j
    show mkPart (sqPart x) (cbPart x) (cbIdx j) = x (cbIdx j)
    rw [mkPart_cbIdx, cbPart_apply]

theorem mkPart_injective₂ : Function.Injective2 mkPart := by
  intro s t s' t' h
  constructor
  · have := congrArg sqPart h
    rwa [sqPart_mkPart, sqPart_mkPart] at this
  · have := congrArg cbPart h
    rwa [cbPart_mkPart, cbPart_mkPart] at this

/-- The boundary intersection set in the product picture. -/
def prodBInterSet (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M) :
    Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 3)) :=
  {p | D p.1 = N p.2 ∧ p.1 ∈ Submission.Drive.unitBox 1 ∧ p.2 ∈ Submission.Drive.unitBox 2 ∧
    (p.1 ∈ Submission.Drive.unitBoxBdry 1 ∨ p.2 ∈ Submission.Drive.unitBoxBdry 2)}

theorem exists_coord_mkPart_sq (s : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 3)) :
    (∃ i : Fin 2, mkPart s t (sqIdx i) = 0 ∨ mkPart s t (sqIdx i) = 1) ↔
      ∃ i : Fin 2, s i = 0 ∨ s i = 1 := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by simpa [mkPart_sqIdx] using hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by simpa [mkPart_sqIdx] using hi⟩

theorem exists_coord_mkPart_cb (s : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 3)) :
    (∃ j : Fin 3, mkPart s t (cbIdx j) = 0 ∨ mkPart s t (cbIdx j) = 1) ↔
      ∃ j : Fin 3, t j = 0 ∨ t j = 1 := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, by simpa [mkPart_cbIdx] using hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, by simpa [mkPart_cbIdx] using hj⟩

theorem unitBoxBdry_iff (m : ℕ) (x : Amb m) :
    x ∈ Submission.Drive.unitBoxBdry m ↔
      x ∈ Submission.Drive.unitBox m ∧ ∃ i : Fin (m + 1), x i = 0 ∨ x i = 1 := Iff.rfl

/-- **The boundary intersection set, elementwise.** -/
theorem mem_bInterSet_iff (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M) (x : Amb 4) :
    x ∈ bInterSet D N ↔
      (D (sqPart x) = N (cbPart x) ∧ sqPart x ∈ Submission.Drive.unitBox 1 ∧
        cbPart x ∈ Submission.Drive.unitBox 2 ∧
        (sqPart x ∈ Submission.Drive.unitBoxBdry 1 ∨
          cbPart x ∈ Submission.Drive.unitBoxBdry 2)) := by
  rw [mem_bInterSet, mem_unitBoxBdry_five_iff x, unitBoxBdry_iff, unitBoxBdry_iff, onSqFace,
    onCubeFace, mem_unitBox_five_iff x]
  simp only [sqPart_apply, cbPart_apply]
  constructor
  · rintro ⟨⟨h1, h2⟩, hD, -, hbd⟩
    refine ⟨hD, h1, h2, ?_⟩
    rcases hbd with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h2, h⟩
  · rintro ⟨hD, h1, h2, hbd⟩
    refine ⟨⟨h1, h2⟩, hD, ⟨h1, h2⟩, ?_⟩
    rcases hbd with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2

theorem prod_mkPart_mem_bInterSet_iff (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M)
    (s : EuclideanSpace ℝ (Fin 2)) (t : EuclideanSpace ℝ (Fin 3)) :
    mkPart s t ∈ bInterSet D N ↔
      (D s = N t ∧ s ∈ Submission.Drive.unitBox 1 ∧ t ∈ Submission.Drive.unitBox 2 ∧
        (s ∈ Submission.Drive.unitBoxBdry 1 ∨ t ∈ Submission.Drive.unitBoxBdry 2)) := by
  rw [mem_bInterSet_iff, sqPart_mkPart, cbPart_mkPart]

theorem prodBInterSet_image (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M) :
    prodBInterSet D N =
      (fun x : Amb 4 => (sqPart x, cbPart x)) '' bInterSet D N := by
  ext p
  obtain ⟨s, t⟩ := p
  rw [Set.mem_image]
  constructor
  · intro hp
    exact ⟨mkPart s t, (prod_mkPart_mem_bInterSet_iff D N s t).mpr hp,
      Prod.ext (sqPart_mkPart s t) (cbPart_mkPart s t)⟩
  · rintro ⟨x, hx, hxt⟩
    rw [← hxt]
    exact (mem_bInterSet_iff D N x).mp hx

theorem inj_prodOf (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M) :
    Function.Injective (fun x : Amb 4 => (sqPart x, cbPart x)) := by
  intro x y hxy
  have h1 : sqPart x = sqPart y := congrArg Prod.fst hxy
  have h2 : cbPart x = cbPart y := congrArg Prod.snd hxy
  rw [← mkPart_sqPart_cbPart x, ← mkPart_sqPart_cbPart y, h1, h2]

theorem prodBInterSet_finite_iff (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M) :
    (prodBInterSet D N).Finite ↔ (bInterSet D N).Finite := by
  rw [prodBInterSet_image]
  exact Set.finite_image_iff (inj_prodOf D N).injOn

theorem prodBInterSet_ncard (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M) :
    (prodBInterSet D N).ncard = (bInterSet D N).ncard := by
  rw [prodBInterSet_image]
  exact Set.ncard_image_of_injective _ (inj_prodOf D N)

end

end Work.Drive

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- The box membership in the two pictures. -/
theorem mem_unitBox_iff_prod (x : Amb 4) :
    x ∈ Submission.Drive.unitBox 4 ↔
      sqPart x ∈ Submission.Drive.unitBox 1 ∧ cbPart x ∈ Submission.Drive.unitBox 2 :=
  mem_unitBox_five_iff x

/-- The boundary membership in the two pictures (given the box membership). -/
theorem mem_unitBoxBdry_iff_prod (x : Amb 4) (hbox : x ∈ Submission.Drive.unitBox 4) :
    x ∈ Submission.Drive.unitBoxBdry 4 ↔
      sqPart x ∈ Submission.Drive.unitBoxBdry 1 ∨
        cbPart x ∈ Submission.Drive.unitBoxBdry 2 := by
  have hb1 : sqPart x ∈ Submission.Drive.unitBox 1 := ((mem_unitBox_five_iff x).mp hbox).1
  have hb2 : cbPart x ∈ Submission.Drive.unitBox 2 := ((mem_unitBox_five_iff x).mp hbox).2
  rw [unitBoxBdry_iff, unitBoxBdry_iff, unitBoxBdry_iff, exists_fin_five_iff]
  simp only [← sqPart_apply, ← cbPart_apply]
  constructor
  · rintro ⟨-, h | h⟩
    · exact Or.inl ⟨hb1, h⟩
    · exact Or.inr ⟨hb2, h⟩
  · rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact ⟨hbox, Or.inl h⟩
    · exact ⟨hbox, Or.inr h⟩

end

end Work.Drive
