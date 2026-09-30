import Mathlib
import Submission.Work.Aspherical.Basic
import Submission.Work.Aspherical.continuous_cubeBoundaryMap
import Submission.Work.Aspherical.cube_exists_extension_of_nullhomotopic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped unitInterval Topology

namespace Work.Aspherical

noncomputable section

/-- The map `I × I^k → I^{k+1}` sending `(t, x)` to the point with last coordinate `t` and
`i`-th coordinate `x i`. -/
def cylToCube (k : ℕ) : C(↥(Set.Icc (0:ℝ) 1) × (Fin k → ↥(Set.Icc (0:ℝ) 1)),
    Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) where
  toFun p := Fin.lastCases (motive := fun _ => ↥(Set.Icc (0:ℝ) 1)) p.1 p.2
  continuous_toFun := by
    apply continuous_pi
    intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · simp only [Fin.lastCases_castSucc]
      exact (continuous_apply i).comp continuous_snd
    · simp only [Fin.lastCases_last]
      exact continuous_fst

@[simp] lemma cylToCube_apply_last (k : ℕ) (t : ↥(Set.Icc (0:ℝ) 1))
    (x : Fin k → ↥(Set.Icc (0:ℝ) 1)) :
    cylToCube k (t, x) (Fin.last k) = t := by simp [cylToCube]

@[simp] lemma cylToCube_apply_castSucc (k : ℕ) (t : ↥(Set.Icc (0:ℝ) 1))
    (x : Fin k → ↥(Set.Icc (0:ℝ) 1)) (i : Fin k) :
    cylToCube k (t, x) (Fin.castSucc i) = x i := by simp [cylToCube]

/-- The boundary map of the cylinder `I^k × I`, viewed as a map on `∂I^{k+1}`: it equals `F` on
the bottom face `{last coordinate = 0}` and the constant `e` on the rest. -/
def cubeBoundaryMap {k : ℕ} {Y : Type*} [TopologicalSpace Y]
    (F : C(Fin k → ↥(Set.Icc (0:ℝ) 1), Y)) (e : Y)
    (hF : ∀ y ∈ Cube.boundary (Fin k), F y = e) :
    C(↥(Cube.boundary (Fin (k+1))), Y) where
  toFun u := if (u : Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) (Fin.last k) = 0
    then F (fun i => (u : Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) (Fin.castSucc i)) else e
  continuous_toFun := continuous_cubeBoundaryMap hF

@[simp] lemma cubeBoundaryMap_apply {k : ℕ} {Y : Type*} [TopologicalSpace Y]
    (F : C(Fin k → ↥(Set.Icc (0:ℝ) 1), Y)) (e : Y)
    (hF : ∀ y ∈ Cube.boundary (Fin k), F y = e)
    (u : ↥(Cube.boundary (Fin (k+1)))) :
    cubeBoundaryMap F e hF u =
      if (u : Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) (Fin.last k) = 0
        then F (fun i => (u : Fin (k+1) → ↥(Set.Icc (0:ℝ) 1)) (Fin.castSucc i)) else e := rfl

/-- A map from the cube `I^k` (`k ≥ 1`) into a contractible space that is constant on the
boundary is homotopic to the corresponding constant map, relative to the boundary. -/
theorem cube_homotopicRel_const_of_contractible {k : ℕ} [NeZero k] {Y : Type*}
    [TopologicalSpace Y] [ContractibleSpace Y] {e : Y} {F : C(Fin k → ↥(Set.Icc (0:ℝ) 1), Y)}
    (hF : ∀ y ∈ Cube.boundary (Fin k), F y = e) :
    F.HomotopicRel (ContinuousMap.const (Fin k → ↥(Set.Icc (0:ℝ) 1)) e) (Cube.boundary (Fin k)) := by
  let b : C(↥(Cube.boundary (Fin (k+1))), Y) := cubeBoundaryMap F e hF
  have hb : ContinuousMap.Nullhomotopic b := by
    have h := (id_nullhomotopic Y).comp_left b
    simpa [ContinuousMap.id_comp] using h
  obtain ⟨G, hG⟩ := cube_exists_extension_of_nullhomotopic (n := k+1) b hb
  refine ⟨{ toContinuousMap := G.comp (cylToCube k),
            map_zero_left := ?_,
            map_one_left := ?_,
            prop' := ?_ }⟩
  · intro x
    have hmem : cylToCube k (0, x) ∈ Cube.boundary (Fin (k+1)) :=
      ⟨Fin.last k, Or.inl (by simp)⟩
    show G (cylToCube k (0, x)) = F x
    rw [hG ⟨cylToCube k (0, x), hmem⟩, cubeBoundaryMap_apply]
    rw [ite_eq_left (by simp)]
    congr 1
    funext i
    simp
  · intro x
    have hmem : cylToCube k (1, x) ∈ Cube.boundary (Fin (k+1)) :=
      ⟨Fin.last k, Or.inr (by simp)⟩
    show G (cylToCube k (1, x)) = e
    rw [hG ⟨cylToCube k (1, x), hmem⟩, cubeBoundaryMap_apply]
    rw [ite_eq_right (by simp)]
  · intro t x hx
    obtain ⟨i, hi⟩ := hx
    have hmem : cylToCube k (t, x) ∈ Cube.boundary (Fin (k+1)) := by
      refine ⟨Fin.castSucc i, ?_⟩
      rcases hi with h | h
      · left; rw [cylToCube_apply_castSucc, h]
      · right; rw [cylToCube_apply_castSucc, h]
    show G (cylToCube k (t, x)) = F x
    rw [hG ⟨cylToCube k (t, x), hmem⟩, cubeBoundaryMap_apply]
    have hx' : (fun i => cylToCube k (t, x) (Fin.castSucc i)) = x := by
      funext i; rw [cylToCube_apply_castSucc]
    rw [hx']
    by_cases hlast : cylToCube k (t, x) (Fin.last k) = 0
    · rw [ite_eq_left hlast]
    · rw [ite_eq_right hlast]; exact (hF x ⟨i, hi⟩).symm

end

end Work.Aspherical
