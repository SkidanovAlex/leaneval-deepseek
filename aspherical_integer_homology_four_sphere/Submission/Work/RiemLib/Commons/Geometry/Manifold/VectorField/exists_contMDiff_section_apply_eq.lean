import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Manifold.VectorField

open scoped _root_.Manifold _root_.ContDiff
open _root_.VectorField Bundle
open Filter

/-- **Every element of a fibre of a `C^∞` vector bundle extends to a global `C^∞` section.**

Let `V` be a `C^∞` vector bundle with model fibre `F` over a `C^∞` manifold `M` modelled on
`(E, H)`.  Given `x : M` and `v : V x`, there is a globally `C^∞` section `s` of `V` with
`s x = v`.  The section is constructed by trivializing `V` near `x` and multiplying the constant
coordinate vector by a smooth bump function supported in the base set of the trivialization; outside
that base set the section is set to `0`. -/
theorem exists_contMDiff_section_apply_eq_of_vectorBundle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ y, TopologicalSpace (V y)]
    [∀ y, AddCommMonoid (V y)] [∀ y, Module ℝ (V y)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    (x : M) (v : V x) :
    ∃ s : Π y : M, V y, CMDiff ∞ (T% s) ∧ s x = v := by
  classical
  -- the bundle trivialization at `x`
  set e := trivializationAt F V x with he
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  -- a smooth bump function centred at `x` whose closed support lies in `e.baseSet`
  obtain ⟨f, -, hf⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.1
      (e.open_baseSet.mem_nhds hx)
  -- the coordinate of `v` in the trivialization `e` at `x`
  set w : F := (e ⟨x, v⟩).2 with hw
  refine ⟨fun y => if y ∈ e.baseSet then e.symm y (f y • w) else 0, ?_, ?_⟩
  · -- smoothness
    intro y
    by_cases hy : y ∈ e.baseSet
    · -- inside the base set use the trivialization `e`
      rw [Bundle.Trivialization.contMDiffAt_section_iff e hy]
      refine (f.contMDiffAt.smul (contMDiffAt_const (c := w))).congr_of_eventuallyEq ?_
      filter_upwards [e.open_baseSet.mem_nhds hy] with z hz
      simp only [if_pos hz, e.apply_mk_symm hz]
      rfl
    · -- outside the base set the section vanishes near `y`
      have hyt : y ∉ tsupport (f : M → ℝ) := fun h => hy (hf h)
      refine (contMDiff_zeroSection ℝ V y).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport (f : M → ℝ)).isOpen_compl.mem_nhds hyt] with z hz
      have hz0 : (f : M → ℝ) z = 0 := image_eq_zero_of_notMem_tsupport hz
      have hσz : (if z ∈ e.baseSet then e.symm z (f z • w) else 0) = 0 := by
        rw [hz0, zero_smul]
        by_cases hz' : z ∈ e.baseSet
        · rw [if_pos hz', ← Trivialization.symmₗ_apply (R := ℝ) e hz' (0 : F)]
          exact map_zero _
        · rw [if_neg hz']
      show (⟨z, (if z ∈ e.baseSet then e.symm z (f z • w) else 0)⟩ :
        TotalSpace F V) = zeroSection F V z
      rw [hσz]
      rfl
  · -- the prescribed value at `x`
    show (if x ∈ e.baseSet then e.symm x (f x • w) else 0) = v
    rw [if_pos hx, f.eq_one, one_smul]
    exact e.symm_apply_apply_mk hx v

/-- Every tangent vector extends to a globally `C^∞` vector field with the prescribed value. -/
theorem exists_contMDiff_section_apply_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {x : M} (v : TangentSpace I x) :
    ∃ X : Π y : M, TangentSpace I y, CMDiff ∞ (T% X) ∧ X x = v :=
  exists_contMDiff_section_apply_eq_of_vectorBundle (V := TangentSpace I) x v

end Commons.Geometry.Manifold.VectorField
