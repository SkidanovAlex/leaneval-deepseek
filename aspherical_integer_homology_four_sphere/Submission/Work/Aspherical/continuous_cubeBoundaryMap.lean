import Mathlib
import Submission.Work.Aspherical.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Aspherical

/-- The map `I^k → Y` obtained by looking at the first `k` coordinates of a point of `I^{k+1}`. -/
private def cubeBoundaryFirstC (k : ℕ) :
    ↥(Cube.boundary (Fin (k+1))) → (Fin k → ↥(Set.Icc (0:ℝ) 1)) :=
  fun u i => (u : Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) (Fin.castSucc i)

private lemma continuous_cubeBoundaryFirstC (k : ℕ) :
    Continuous (cubeBoundaryFirstC k) := by
  apply continuous_pi; intro i
  exact (continuous_apply (Fin.castSucc i)).comp continuous_subtype_val

/-- The boundary map of the cylinder `I^k × I`, viewed as a map on `∂I^{k+1}`: it equals `F` on
the bottom face `{last coordinate = 0}` and the constant `e` on the rest. It is continuous
whenever `F` is constant `e` on `∂I^k`. -/
theorem continuous_cubeBoundaryMap {k : ℕ} {Y : Type*} [TopologicalSpace Y] {e : Y}
    {F : C(Fin k → ↥(Set.Icc (0:ℝ) 1), Y)}
    (hF : ∀ y ∈ Cube.boundary (Fin k), F y = e) :
    Continuous (fun u : ↥(Cube.boundary (Fin (k+1))) =>
      if (u : Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) (Fin.last k) = 0
        then F (fun i => (u : Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) (Fin.castSucc i))
        else e) := by
  classical
  -- Abbreviations for the first-`k`-coordinates map and the target function.
  let g : ↥(Cube.boundary (Fin (k+1))) → Y :=
    fun u => if (u : Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) (Fin.last k) = 0
      then F (cubeBoundaryFirstC k u) else e
  change Continuous g
  -- The "bottom face" `A` and the complementary closed piece `B`.  Both are closed in `∂I^{k+1}`
  -- and together they cover it; we glue the two restrictions.
  let A : Set ↥(Cube.boundary (Fin (k+1))) :=
    {u | (u : Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) (Fin.last k) = 0}
  let B : Set ↥(Cube.boundary (Fin (k+1))) :=
    {u | (u : Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) (Fin.last k) = 1} ∪
    {u | cubeBoundaryFirstC k u ∈ Cube.boundary (Fin k)}
  have hAc : IsClosed A := by
    simp only [A]
    exact isClosed_eq
      ((continuous_apply (Fin.last k)).comp continuous_subtype_val) continuous_const
  have hBc : IsClosed B := by
    simp only [B]
    apply IsClosed.union
    · exact isClosed_eq
        ((continuous_apply (Fin.last k)).comp continuous_subtype_val) continuous_const
    · exact (isClosed_boundary k).preimage (continuous_cubeBoundaryFirstC k)
  have hcover : A ∪ B = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr; intro u
    rcases u.property with ⟨j, hj⟩
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · by_cases h0 : (u : Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) (Fin.last k) = 0
      · exact Or.inl h0
      · exact Or.inr (Or.inr ⟨i, hj⟩)
    · by_cases h0 : (u : Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) (Fin.last k) = 0
      · exact Or.inl h0
      · exact Or.inr (Or.inl (hj.resolve_left h0))
  -- On the bottom face `g` is the continuous composite `F ∘ (first k coordinates)`.
  have hAcont : ContinuousOn g A := by
    refine ContinuousOn.congr
      ((F.continuous.comp (continuous_cubeBoundaryFirstC k)).continuousOn) ?_
    intro u hu
    simp only [g]
    exact ite_eq_left hu
  -- On the complementary piece `g` is the constant `e`: on the top face this is the `else`
  -- branch, and on the side faces `F` is evaluated at a point of `∂I^k`, hence is `e`.
  have hBcont : ContinuousOn g B := by
    refine ContinuousOn.congr
      ((continuous_const : Continuous (fun _ : ↥(Cube.boundary (Fin (k+1))) => e)).continuousOn) ?_
    intro u hu
    simp only [B, Set.mem_union, Set.mem_ofPred_eq] at hu
    simp only [g]
    rcases hu with h1 | h2
    · rw [ite_eq_right]; intro h0; exact zero_ne_one (h0 ▸ h1)
    · by_cases h0 : (u : Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) (Fin.last k) = 0
      · rw [ite_eq_left h0]; exact hF (cubeBoundaryFirstC k u) h2
      · rw [ite_eq_right h0]
  rw [← continuousOn_univ, ← hcover]
  exact hAcont.union_of_isClosed hBcont hAc hBc

end Work.Aspherical
