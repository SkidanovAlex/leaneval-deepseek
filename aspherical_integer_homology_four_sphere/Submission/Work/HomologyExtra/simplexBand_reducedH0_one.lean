import Mathlib
import Submission.Work.HomologyExtra.Basic
import Submission.Work.Cohomology.reducedH0OfTwoPoints

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The reduced zeroth homology of the band of `∂Δ²`

The band of `∂Δ² ⊆ ℝ³` is the set of points of the boundary of the `2`-simplex whose last
barycentric coordinate lies strictly between `0` and `1`.  It is the union of the two open edges
`[v₀,v₂]` and `[v₁,v₂]` with the vertices removed, hence a disjoint union of two open arcs: it is
homotopy equivalent to the two-point space `S⁰`, and its reduced zeroth singular homology is `ℤ`.

This file proves that `ZerothHomotopy` of the band is `Bool` (by exhibiting the two midpoints of
the two open arcs and checking that every point of the band is joined to exactly one of them), and
deduces the statement from Mathlib's identification of `H₀` with the free module on
`ZerothHomotopy` (`Work.Cohomology.redH0_zerothEquivBool`).
-/

open CategoryTheory AlgebraicTopology Topology
open scoped Topology unitInterval

namespace Work.HomologyExtra

noncomputable section

/-! ## The band of `∂Δ²` in barycentric coordinates -/

/-- The barycentric coordinates of a point of `∂Δ²`, as a vector in `ℝ³`. -/
abbrev bandWeights : ↥(simplexBoundary 2) → (Fin 3 → ℝ) :=
  fun x i => (x : simplex 2).weights i

/-- The band of `∂Δ²`, described by its barycentric coordinate vectors: non-negative coordinates
summing to `1`, the last one strictly between `0` and `1`, and (because the point lies on the
boundary) some coordinate equal to `0`. -/
def bandWeightSet : Set (Fin 3 → ℝ) :=
  {f | (∀ i, 0 ≤ f i) ∧ (∑ i, f i = 1) ∧ 0 < f 2 ∧ f 2 < 1 ∧ ∃ i, f i = 0}

theorem mem_bandWeightSet_iff (f : Fin 3 → ℝ) : f ∈ bandWeightSet ↔
    (∀ i, 0 ≤ f i) ∧ (∑ i, f i = 1) ∧ 0 < f 2 ∧ f 2 < 1 ∧ ∃ i, f i = 0 := Iff.rfl

theorem isEmbedding_bandWeights : IsEmbedding bandWeights :=
  (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).comp IsEmbedding.subtypeVal

theorem bandWeights_preimage : bandWeights ⁻¹' bandWeightSet = simplexBand 1 := by
  ext x
  rw [Set.mem_preimage, mem_bandWeightSet_iff]
  simp only [simplexBand]
  constructor
  · rintro ⟨-, -, h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => Convexity.StdSimplex.weights_nonneg (w := (x : simplex 2)) i,
      Convexity.StdSimplex.total_of_fintype (x : simplex 2), h1, h2, ?_⟩
    exact x.2

theorem bandWeightSet_subset_range : bandWeightSet ⊆ Set.range bandWeights := by
  rintro f ⟨hfnn, hfsum, hfpos, hflt, i, hi⟩
  have hmem : f ∈ Set.range
      (fun t : Convexity.StdSimplex ℝ (Fin 3) => fun i => t.weights i) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨hfnn, hfsum⟩
  obtain ⟨w, hw⟩ := hmem
  refine ⟨⟨w, ?_⟩, hw⟩
  exact ⟨i, by rw [show w.weights i = f i from congrFun hw i, hi]⟩

/-- The band of `∂Δ²`, as a subspace of `∂Δ²`, is homeomorphic to its barycentric coordinate
model. -/
noncomputable def bandHomeo : ↥(simplexBand 1) ≃ₜ ↥(bandWeightSet) :=
  (Homeomorph.setCongr bandWeights_preimage).symm.trans
    (isEmbedding_bandWeights.homeomorphOfSubsetRange bandWeightSet_subset_range)

/-! ## The two open arcs of the band -/

/-- The open arc `[v₁,v₂]` of the band, parametrised by the last barycentric coordinate. -/
def halfMapA (t : ℝ) : Fin 3 → ℝ := ![0, 1 - t, t]

/-- The open arc `[v₀,v₂]` of the band, parametrised by the last barycentric coordinate. -/
def halfMapB (t : ℝ) : Fin 3 → ℝ := ![1 - t, 0, t]

/-- The "left" arc `{f 0 = 0}` of the band. -/
def halfA : Set (Fin 3 → ℝ) := halfMapA '' Set.Ioo (0 : ℝ) 1

/-- The "right" arc `{f 1 = 0}` of the band. -/
def halfB : Set (Fin 3 → ℝ) := halfMapB '' Set.Ioo (0 : ℝ) 1

/-- The midpoint of the arc `{f 0 = 0}`, i.e. `(0, 1/2, 1/2)`. -/
def zA : Fin 3 → ℝ := halfMapA (1/2)

/-- The midpoint of the arc `{f 1 = 0}`, i.e. `(1/2, 0, 1/2)`. -/
def zB : Fin 3 → ℝ := halfMapB (1/2)

theorem zA_apply_zero : zA 0 = 0 := by simp [zA, halfMapA]

theorem zA_apply_one : zA 1 = 1/2 := by simp [zA, halfMapA]; norm_num

theorem zB_apply_zero : zB 0 = 1/2 := by simp [zB, halfMapB]; norm_num

theorem zB_apply_one : zB 1 = 0 := by simp [zB, halfMapB]

theorem zA_ne_zB : zA ≠ zB := by
  intro h
  have h0 := congrFun h 0
  rw [zA_apply_zero, zB_apply_zero] at h0
  norm_num at h0

theorem continuous_halfMapA : Continuous halfMapA := by
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;> simp [halfMapA] <;> fun_prop

theorem continuous_halfMapB : Continuous halfMapB := by
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;> simp [halfMapB] <;> fun_prop

theorem zA_mem_halfA : zA ∈ halfA := ⟨1/2, by norm_num, rfl⟩

theorem zB_mem_halfB : zB ∈ halfB := ⟨1/2, by norm_num, rfl⟩

theorem halfA_subset_bandWeightSet : halfA ⊆ bandWeightSet := by
  rintro f ⟨t, ht, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [halfMapA] <;> linarith [ht.1, ht.2]
  · rw [Fin.sum_univ_three]
    simp [halfMapA]
  · simpa [halfMapA] using ht.1
  · simpa [halfMapA] using ht.2
  · exact ⟨0, by simp [halfMapA]⟩

theorem halfB_subset_bandWeightSet : halfB ⊆ bandWeightSet := by
  rintro f ⟨t, ht, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [halfMapB] <;> linarith [ht.1, ht.2]
  · rw [Fin.sum_univ_three]
    simp [halfMapB]
  · simpa [halfMapB] using ht.1
  · simpa [halfMapB] using ht.2
  · exact ⟨1, by simp [halfMapB]⟩

theorem isPathConnected_halfA : IsPathConnected halfA :=
  (convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1/2, by norm_num⟩ |>.image continuous_halfMapA

theorem isPathConnected_halfB : IsPathConnected halfB :=
  (convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1/2, by norm_num⟩ |>.image continuous_halfMapB

/-! ## Which arc a point of the band belongs to -/

theorem bandWeightSet_eq_zero_or {f : Fin 3 → ℝ} (hf : f ∈ bandWeightSet) :
    f 0 = 0 ∨ f 1 = 0 := by
  obtain ⟨-, -, hfpos, -, i, hi⟩ := hf
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi
  · exfalso
    have h2 : f 2 = 0 := by simpa using hi
    rw [h2] at hfpos
    exact lt_irrefl 0 hfpos

theorem bandWeightSet_apply_zero_ne_apply_one {f : Fin 3 → ℝ} (hf : f ∈ bandWeightSet) :
    f 0 ≠ f 1 := by
  intro h
  have hcase := bandWeightSet_eq_zero_or hf
  obtain ⟨-, hfsum, hfpos, hflt, -⟩ := hf
  have hsum : f 0 + f 1 + f 2 = 1 := by simpa [Fin.sum_univ_three] using hfsum
  rcases hcase with h0 | h1
  · linarith
  · linarith

theorem mem_halfA_of_mem {f : Fin 3 → ℝ} (hf : f ∈ bandWeightSet) (h0 : f 0 = 0) :
    f ∈ halfA := by
  obtain ⟨-, hfsum, hfpos, hflt, -⟩ := hf
  have hsum : f 0 + f 1 + f 2 = 1 := by simpa [Fin.sum_univ_three] using hfsum
  refine ⟨f 2, ⟨hfpos, hflt⟩, ?_⟩
  ext i
  fin_cases i
  · simp [halfMapA, h0]
  · have hf1 : f 1 = 1 - f 2 := by linarith
    simp [halfMapA, hf1]
  · simp [halfMapA]

theorem mem_halfB_of_mem {f : Fin 3 → ℝ} (hf : f ∈ bandWeightSet) (h1 : f 1 = 0) :
    f ∈ halfB := by
  obtain ⟨-, hfsum, hfpos, hflt, -⟩ := hf
  have hsum : f 0 + f 1 + f 2 = 1 := by simpa [Fin.sum_univ_three] using hfsum
  refine ⟨f 2, ⟨hfpos, hflt⟩, ?_⟩
  ext i
  fin_cases i
  · have hf0 : f 0 = 1 - f 2 := by linarith
    simp [halfMapB, hf0]
  · simp [halfMapB, h1]
  · simp [halfMapB]

/-! ## The path components of the band -/

theorem joined_zA_of_mem {f : Fin 3 → ℝ} (hf : f ∈ bandWeightSet) (h0 : f 0 = 0) :
    Joined (⟨f, hf⟩ : ↥bandWeightSet) ⟨zA, halfA_subset_bandWeightSet zA_mem_halfA⟩ :=
  ((isPathConnected_halfA.joinedIn f (mem_halfA_of_mem hf h0) zA zA_mem_halfA).mono
    halfA_subset_bandWeightSet).joined_subtype

theorem joined_zB_of_mem {f : Fin 3 → ℝ} (hf : f ∈ bandWeightSet) (h1 : f 1 = 0) :
    Joined (⟨f, hf⟩ : ↥bandWeightSet) ⟨zB, halfB_subset_bandWeightSet zB_mem_halfB⟩ :=
  ((isPathConnected_halfB.joinedIn f (mem_halfB_of_mem hf h1) zB zB_mem_halfB).mono
    halfB_subset_bandWeightSet).joined_subtype

theorem not_joined_zA_zB :
    ¬ Joined (⟨zA, halfA_subset_bandWeightSet zA_mem_halfA⟩ : ↥bandWeightSet)
      ⟨zB, halfB_subset_bandWeightSet zB_mem_halfB⟩ := by
  rintro ⟨γ⟩
  set g : unitInterval → ℝ := fun t => (γ t).1 1 - (γ t).1 0 with hg
  have hcont : Continuous g := by
    rw [hg]
    exact ((continuous_apply 1).comp (continuous_subtype_val.comp γ.continuous)).sub
      ((continuous_apply 0).comp (continuous_subtype_val.comp γ.continuous))
  have h0 : g 0 = 1/2 := by
    rw [hg]
    change (γ 0).1 1 - (γ 0).1 0 = 1/2
    rw [Path.source γ]
    simp only [Subtype.coe_mk]
    rw [zA_apply_one, zA_apply_zero]
    norm_num
  have h1 : g 1 = -1/2 := by
    rw [hg]
    change (γ 1).1 1 - (γ 1).1 0 = -1/2
    rw [Path.target γ]
    simp only [Subtype.coe_mk]
    rw [zB_apply_one, zB_apply_zero]
    norm_num
  have hmem : (0 : ℝ) ∈ Set.range g := by
    apply intermediate_value_univ (1 : unitInterval) (0 : unitInterval) hcont
    rw [h1, h0]
    norm_num
  obtain ⟨t, ht⟩ := hmem
  have ht' : (γ t).1 1 - (γ t).1 0 = 0 := by
    rw [hg] at ht
    exact ht
  exact bandWeightSet_apply_zero_ne_apply_one (γ t).2 (by linarith)

/-- The path component of the midpoint of the arc `{f 0 = 0}` of the band. -/
def clA : ZerothHomotopy ↥bandWeightSet :=
  ZerothHomotopy.mk ⟨zA, halfA_subset_bandWeightSet zA_mem_halfA⟩

/-- The path component of the midpoint of the arc `{f 1 = 0}` of the band. -/
def clB : ZerothHomotopy ↥bandWeightSet :=
  ZerothHomotopy.mk ⟨zB, halfB_subset_bandWeightSet zB_mem_halfB⟩

theorem clA_ne_clB : clA ≠ clB := by
  intro h
  exact not_joined_zA_zB (Quotient.exact h)

theorem zerothHomotopy_mk_eq_or (z : ZerothHomotopy ↥bandWeightSet) : z = clA ∨ z = clB := by
  obtain ⟨f, rfl⟩ := ZerothHomotopy.mk_surjective z
  by_cases h0 : f.1 0 = 0
  · exact Or.inl (ZerothHomotopy.sound (joined_zA_of_mem f.2 h0).somePath)
  · refine Or.inr (ZerothHomotopy.sound (joined_zB_of_mem f.2 ?_).somePath)
    rcases bandWeightSet_eq_zero_or f.2 with h | h
    · exact absurd h h0
    · exact h

/-- The band `{0 < w₂ < 1} ⊆ ∂Δ²` has exactly two path components. -/
noncomputable def bandWeightZerothEquivBool : ZerothHomotopy ↥bandWeightSet ≃ Bool := by
  classical
  refine ⟨fun z => if z = clA then true else false,
    fun b => if b then clA else clB, ?_, ?_⟩
  · intro z
    show (if (if z = clA then true else false) = true then clA else clB) = z
    by_cases h : z = clA
    · rw [if_pos h, if_pos rfl, h]
    · have h2 : z = clB := by
        rcases zerothHomotopy_mk_eq_or z with h' | h'
        · exact absurd h' h
        · exact h'
      rw [if_neg h, if_neg Bool.false_ne_true, h2]
  · intro b
    cases b
    · show (if (if (false : Bool) = true then clA else clB) = clA then true else false) = false
      rw [if_neg Bool.false_ne_true, if_neg (Ne.symm clA_ne_clB)]
    · show (if (if (true : Bool) = true then clA else clB) = clA then true else false) = true
      rw [if_pos rfl, if_pos rfl]

/-! ## Transporting `ZerothHomotopy` along a homeomorphism -/

theorem zerothHomotopyEquivOfHomeomorph_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    (ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (e x))
        (fun _ _ p => ZerothHomotopy.sound (p.map e.continuous))
      : ZerothHomotopy X → ZerothHomotopy Y) (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (e x) := rfl

/-- A homeomorphism induces a bijection on path components. -/
noncomputable def zerothHomotopyEquivOfHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : ZerothHomotopy X ≃ ZerothHomotopy Y where
  toFun := ZerothHomotopy.lift (fun x => ZerothHomotopy.mk (e x))
    (fun _ _ p => ZerothHomotopy.sound (p.map e.continuous))
  invFun := ZerothHomotopy.lift (fun y => ZerothHomotopy.mk (e.symm y))
    (fun _ _ p => ZerothHomotopy.sound (p.map e.symm.continuous))
  left_inv := by
    intro z
    induction z using ZerothHomotopy.rec with
    | mk x => simp [ZerothHomotopy.lift_mk]
  right_inv := by
    intro z
    induction z using ZerothHomotopy.rec with
    | mk y => simp [ZerothHomotopy.lift_mk]

/-- The band of `∂Δ²` has exactly two path components. -/
noncomputable def bandZerothEquivBool :
    ZerothHomotopy (TopCat.of (simplexBand 1)) ≃ Bool :=
  (zerothHomotopyEquivOfHomeomorph bandHomeo).trans bandWeightZerothEquivBool

/-! ## The main statement -/

theorem simplexBand_reducedH0_one :
    Nonempty (Work.Cohomology.kerMod (ModuleCat.Hom.hom
      (TopCat.singularHomology₀ε (TopCat.of (Work.HomologyExtra.simplexBand 1))
        (ModuleCat.of ℤ ℤ))) ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨h⟩ := Work.Cohomology.redH0_zerothEquivBool (TopCat.of (simplexBand 1))
    bandZerothEquivBool
  exact ⟨(Work.Cohomology.ofKerIsoKerMod (ModuleCat.Hom.hom
    (TopCat.singularHomology₀ε (TopCat.of (Work.HomologyExtra.simplexBand 1))
      (ModuleCat.of ℤ ℤ)))).symm ≪≫ h⟩

end

end Work.HomologyExtra
