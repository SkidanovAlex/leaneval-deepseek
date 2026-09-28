import Mathlib
import Submission.Work.Serre.E0SimplexDefs

/-!
# SUBPROJECT SERRE — E0 in range form: gluing a matching family of faces

`Work.Serre.e0SimplexBdryOfMatching`: a family `x i : Δ^{k+1} → X` of maps on the faces of
`Δ^{k+2}` which agree on the overlaps glues into a continuous map on the simplicial boundary
`∂Δ^{k+2} = Work.Serre.simplexBdry (k+2)`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial
open scoped Simplicial Topology

namespace Work.Serre

noncomputable section

open Work.RatHurewicz.Bridge

/-! ## Deleting a coordinate of a point of the boundary -/

/-- The point of `Δ^{m+1}` obtained from `z : Δ^{m+2}` by deleting the `i`-th coordinate.  It is a
point of the simplex when `z i = 0`. -/
def uncoface (m : ℕ) (i : Fin (m+2)) (z : ↥(stdSimplex ℝ (Fin (m+2)))) : Fin (m+1) → ℝ :=
  fun j => z.1 (Fin.succAbove i j)

@[simp]
theorem uncoface_apply (m : ℕ) (i : Fin (m+2)) (z : ↥(stdSimplex ℝ (Fin (m+2))))
    (j : Fin (m+1)) : uncoface m i z j = z.1 (Fin.succAbove i j) := rfl

/-- Deleting a vanishing coordinate gives a point of the standard simplex. -/
theorem uncoface_mem (m : ℕ) (i : Fin (m+2)) (z : ↥(stdSimplex ℝ (Fin (m+2))))
    (hz : z.1 i = 0) : uncoface m i z ∈ stdSimplex ℝ (Fin (m+1)) := by
  refine ⟨fun j => z.2.1 _, ?_⟩
  have h := Fin.sum_univ_succAbove (f := fun l : Fin (m+2) => z.1 l) i
  have h2 : ∑ j : Fin (m+1), uncoface m i z j = ∑ l : Fin (m+2), z.1 l - z.1 i := by
    simp only [uncoface_apply]
    linarith
  rw [h2, z.2.2, hz, sub_zero]

/-- **Re-inserting the deleted coordinate recovers the point.** -/
theorem coface_uncoface (m : ℕ) (i : Fin (m+2)) (z : ↥(stdSimplex ℝ (Fin (m+2))))
    (hz : z.1 i = 0) :
    coface m i ⟨uncoface m i z, uncoface_mem m i z hz⟩ = z := by
  ext p
  simp only [coface_apply, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [Finset.sum_filter]
  by_cases hp : p = i
  · rw [hp, Finset.sum_eq_zero (fun j _ => by rw [if_neg (Fin.succAbove_ne i j)])]
    exact hz.symm
  · obtain ⟨j, hj⟩ : ∃ j : Fin (m+1), Fin.succAbove i j = p := by
      rcases lt_or_gt_of_ne hp with h | h
      · refine ⟨⟨p.val, by omega⟩, ?_⟩
        rw [Fin.succAbove_of_castSucc_lt]
        · rfl
        · simp only [Fin.lt_def, Fin.val_castSucc]; exact h
      · refine ⟨⟨p.val - 1, by omega⟩, ?_⟩
        rw [Fin.succAbove_of_le_castSucc]
        · exact Fin.ext (by simp only [Fin.val_succ]; omega)
        · simp only [Fin.le_def, Fin.val_castSucc]; omega
    rw [Finset.sum_eq_single j]
    · rw [if_pos hj]
      show z.1 (Fin.succAbove i j) = z.1 p
      rw [hj]
    · intro b _ hbj
      rw [if_neg]
      exact fun h => hbj (Fin.succAbove_right_injective (p := i) (by rw [h, ← hj]))
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- **Deleting the coordinate inserted by a coface recovers the point.** -/
theorem uncoface_coface (m : ℕ) (i : Fin (m+2)) (z : ↥(stdSimplex ℝ (Fin (m+1)))) :
    uncoface m i (coface m i z) = z.1 := by
  funext j
  show ((stdSimplex.map (Fin.succAbove i) z : ↥(stdSimplex ℝ (Fin (m+2)))) : Fin (m+2) → ℝ)
      (Fin.succAbove i j) = z.1 j
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]
    rfl
  · intro b _ hbj
    rw [if_neg]
    exact fun hh => hbj (Fin.succAbove_right_injective (p := i) hh)
  · intro hh
    exact absurd (Finset.mem_univ _) hh

/-! ## The `succAbove` identity behind the overlap of two faces -/

/-- The value formula for `Fin.succAbove`. -/
theorem val_succAbove {n : ℕ} (p : Fin (n+1)) (i : Fin n) :
    (p.succAbove i).val = if i.val < p.val then i.val else i.val + 1 := by
  by_cases h : i.castSucc < p
  · rw [Fin.succAbove_of_castSucc_lt p i h, Fin.val_castSucc,
      if_pos (by simpa [Fin.lt_def, Fin.val_castSucc] using h)]
  · rw [Fin.succAbove_of_le_castSucc p i (le_of_not_gt h), Fin.val_succ,
      if_neg (by simpa [Fin.lt_def, Fin.val_castSucc] using h)]

/-- **The `succAbove`-composition identity**: `succAbove i ∘ succAbove (j-1) = succAbove j ∘
succAbove i` for `i < j`.  Both composites skip the two elements `i` and `j` of `Fin (m+3)`. -/
theorem succAbove_succAbove {m : ℕ} (i j : Fin (m+3)) (hij : i < j) (l : Fin (m+1)) :
    (Fin.succAbove i) (Fin.succAbove ⟨j.val - 1, by omega⟩ l) =
      (Fin.succAbove j) (Fin.succAbove ⟨i.val, by have h : i.val < j.val := hij; omega⟩ l) := by
  apply Fin.ext
  simp only [val_succAbove]
  split_ifs <;> omega

/-- The two ways of deleting two coordinates of a point of `Δ^{m+2}` give the same point of
`Δ^m`. -/
theorem uncoface_uncoface {m : ℕ} (i j : Fin (m+3)) (hij : i < j)
    (z : ↥(stdSimplex ℝ (Fin (m+3)))) (hi : z.1 i = 0) (hj : z.1 j = 0) :
    uncoface m ⟨j.val - 1, by omega⟩
        ⟨uncoface (m+1) i z, uncoface_mem (m+1) i z hi⟩ =
      uncoface m ⟨i.val, by have h : i.val < j.val := hij; omega⟩
        ⟨uncoface (m+1) j z, uncoface_mem (m+1) j z hj⟩ := by
  funext l
  simp only [uncoface_apply]
  exact congrArg z.1 (succAbove_succAbove i j hij l)

/-- **The two readings of the overlap of the `i`-th and `j`-th face agree** (`i < j`). -/
theorem uncoface_agree {X : Type} [TopologicalSpace X] {m : ℕ}
    (x : (i : Fin (m+3)) → C(↥(stdSimplex ℝ (Fin (m+2))), X))
    (hx : ∀ (i j : Fin (m+3)) (hij : i < j),
      (x j).comp (coface m ⟨i.val, by have h : i.val < j.val := hij; omega⟩) =
        (x i).comp (coface m ⟨j.val - 1, by omega⟩))
    (i j : Fin (m+3)) (hij : i < j) (z : ↥(stdSimplex ℝ (Fin (m+3))))
    (hi : z.1 i = 0) (hj : z.1 j = 0) :
    x i ⟨uncoface (m+1) i z, uncoface_mem (m+1) i z hi⟩ =
      x j ⟨uncoface (m+1) j z, uncoface_mem (m+1) j z hj⟩ := by
  have hjm : j.val - 1 < m + 2 := by omega
  have him : i.val < m + 2 := by omega
  -- the vanishing coordinates of the deleted points
  have hw0 : (uncoface (m+1) i z) ⟨j.val - 1, hjm⟩ = 0 := by
    simp only [uncoface_apply]
    rw [show (Fin.succAbove i) ⟨j.val - 1, hjm⟩ = j from by
      rw [Fin.succAbove_of_le_castSucc i ⟨j.val - 1, hjm⟩
        (by simp only [Fin.le_def, Fin.val_castSucc]; omega)]
      exact Fin.ext (by simp only [Fin.val_succ]; omega)]
    exact hj
  have hw0' : (uncoface (m+1) j z) ⟨i.val, him⟩ = 0 := by
    simp only [uncoface_apply]
    rw [show (Fin.succAbove j) ⟨i.val, him⟩ = i from by
      rw [Fin.succAbove_of_castSucc_lt j ⟨i.val, him⟩
        (by simp only [Fin.lt_def, Fin.val_castSucc]; exact hij)]
      exact Fin.ext (by simp only [Fin.val_castSucc])]
    exact hi
  -- coface of the deleted points recovers them
  have hco := coface_uncoface m ⟨j.val - 1, hjm⟩
    ⟨uncoface (m+1) i z, uncoface_mem (m+1) i z hi⟩ hw0
  have hco' := coface_uncoface m ⟨i.val, him⟩
    ⟨uncoface (m+1) j z, uncoface_mem (m+1) j z hj⟩ hw0'
  -- the matching hypothesis, evaluated at the common deleted point
  have h1 := congrArg
    (fun (g : C(↥(stdSimplex ℝ (Fin (m+1))), X)) =>
      g ⟨uncoface m ⟨j.val - 1, hjm⟩ ⟨uncoface (m+1) i z, uncoface_mem (m+1) i z hi⟩,
        uncoface_mem m ⟨j.val - 1, hjm⟩ _ hw0⟩) (hx i j hij)
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply] at h1
  have hkey := uncoface_uncoface i j hij z hi hj
  rw [← hco, ← hco']
  rw [← h1]
  exact congrArg (fun t : ↥(stdSimplex ℝ (Fin (m+1))) => x j (coface m ⟨i.val, him⟩ t))
    (Subtype.ext hkey)

end

end Work.Serre


namespace Work.Serre

noncomputable section

open Work.RatHurewicz.Bridge

/-- **Gluing a matching family of simplex faces into a map on the boundary `∂Δ^{k+2}`.** -/
theorem e0SimplexBdryOfMatching (k : ℕ) {X : Type} [TopologicalSpace X]
    (x : (i : Fin (k + 3)) → C(↥(stdSimplex ℝ (Fin (k + 2))), X))
    (hx : ∀ (i j : Fin (k + 3)) (hij : i < j),
      (x j).comp (coface k ⟨i.val, by have h : i.val < j.val := hij; omega⟩) =
        (x i).comp (coface k ⟨j.val - 1, by omega⟩)) :
    ∃ b : C(↥(simplexBdry (k+2)), X),
      ∀ i : Fin (k+3), b.comp (faceIncl (k+1) i) = x i := by
  classical
  -- a fixed vertex of `Δ^{k+1}`, used only in the junk branch of the piece maps
  let pt : ↥(stdSimplex ℝ (Fin (k+2))) :=
    ⟨fun j => if j = 0 then (1 : ℝ) else 0,
      ⟨fun j => by by_cases h : j = 0 <;> simp [h], by
        rw [Finset.sum_ite_eq']
        simp⟩⟩
  -- the `i`-th face of the boundary
  let E : Fin (k+3) → Set ↥(simplexBdry (k+2)) :=
    fun i => {z | (z : ↥(stdSimplex ℝ (Fin (k+3)))) i = 0}
  have hEclosed : ∀ i, IsClosed (E i) := by
    intro i
    refine isClosed_eq ?_ continuous_const
    have h1 : Continuous fun w : ↥(stdSimplex ℝ (Fin (k+3))) => (w : Fin (k+3) → ℝ) :=
      continuous_subtype_val
    exact (continuous_apply i).comp (h1.comp continuous_subtype_val)
  -- the piece maps
  let G : (i : Fin (k+3)) → (↥(simplexBdry (k+2)) → X) := fun i z =>
    x i (if h : (z : ↥(stdSimplex ℝ (Fin (k+3)))) i = 0
      then ⟨uncoface (k+1) i z.1, uncoface_mem (k+1) i z.1 h⟩
      else pt)
  -- on the `i`-th face the piece map is continuous
  have hGcont : ∀ i, ContinuousOn (G i) (E i) := by
    intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have hpiece : ∀ z : ↥(E i), G i z.1 =
        x i ⟨uncoface (k+1) i z.1.1, uncoface_mem (k+1) i z.1.1 z.2⟩ := by
      intro z
      have hz : ((z.1 : ↥(simplexBdry (k+2))) : ↥(stdSimplex ℝ (Fin (k+3)))) i = 0 := z.2
      simp only [G, dif_pos hz]
    refine Continuous.congr ?_ (fun z => (hpiece z).symm)
    refine (x i).continuous.comp (Continuous.subtype_mk ?_ _)
    refine continuous_pi fun j => ?_
    exact (continuous_apply (Fin.succAbove i j)).comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))
  -- the pieces agree on overlaps
  have hGagree : ∀ i j, ∀ z, z ∈ E i → z ∈ E j → G i z = G j z := by
    intro i j z hi hj
    by_cases hij : i = j
    · rw [hij]
    · have hzi : ((z : ↥(simplexBdry (k+2))) : ↥(stdSimplex ℝ (Fin (k+3)))) i = 0 := hi
      have hzj : ((z : ↥(simplexBdry (k+2))) : ↥(stdSimplex ℝ (Fin (k+3)))) j = 0 := hj
      have hGi : G i z = x i ⟨uncoface (k+1) i z.1, uncoface_mem (k+1) i z.1 hzi⟩ := by
        simp only [G, dif_pos hzi]
      have hGj : G j z = x j ⟨uncoface (k+1) j z.1, uncoface_mem (k+1) j z.1 hzj⟩ := by
        simp only [G, dif_pos hzj]
      rw [hGi, hGj]
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact uncoface_agree x hx i j hlt z.1 hzi hzj
      · exact (uncoface_agree x hx j i hlt z.1 hzj hzi).symm
  -- the faces cover the boundary
  have hwit : ∀ z : ↥(simplexBdry (k+2)), ∃ i : Fin (k+3),
      (z : ↥(stdSimplex ℝ (Fin (k+3)))) i = 0 := fun z => z.2
  let bfun : ↥(simplexBdry (k+2)) → X := fun z => G (Classical.choose (hwit z)) z
  have hbval : ∀ (z : ↥(simplexBdry (k+2))) (i : Fin (k+3)), z ∈ E i → bfun z = G i z := by
    intro z i hi
    exact hGagree _ i z (Classical.choose_spec (hwit z)) hi
  -- continuity of the glued map
  have hcont : Continuous bfun := by
    rw [continuous_iff_isClosed]
    intro T hT
    have hsub : bfun ⁻¹' T = ⋃ i, (E i ∩ G i ⁻¹' T) := by
      ext z
      constructor
      · intro hz
        refine Set.mem_iUnion.mpr ⟨Classical.choose (hwit z), Classical.choose_spec (hwit z), ?_⟩
        rw [Set.mem_preimage]
        exact hz
      · intro hz
        obtain ⟨i, hi, hzT⟩ := Set.mem_iUnion.mp hz
        rw [Set.mem_preimage] at hzT
        rw [Set.mem_preimage, hbval z i hi]
        exact hzT
    rw [hsub]
    refine isClosed_iUnion_of_finite fun i => ?_
    obtain ⟨U, hU, hUeq⟩ := (continuousOn_iff_isClosed.mp (hGcont i)) T hT
    have hset : E i ∩ G i ⁻¹' T = U ∩ E i := by
      ext z; constructor
      · rintro ⟨hzE, hzT⟩
        refine ⟨?_, hzE⟩
        have hmem : z ∈ (G i) ⁻¹' T ∩ E i := ⟨hzT, hzE⟩
        rw [hUeq] at hmem
        exact hmem.1
      · rintro ⟨hzU, hzE⟩
        refine ⟨hzE, ?_⟩
        have hmem : z ∈ U ∩ E i := ⟨hzU, hzE⟩
        rw [← hUeq] at hmem
        exact hmem.1
    rw [hset]
    exact hU.inter (hEclosed i)
  refine ⟨⟨bfun, hcont⟩, ?_⟩
  intro i
  ext z
  have hzE : faceIncl (k+1) i z ∈ E i := by
    show ((faceIncl (k+1) i z : ↥(simplexBdry (k+2))) : ↥(stdSimplex ℝ (Fin (k+3)))) i = 0
    rw [faceIncl_coe]
    exact coface_apply_self (k+1) i z
  have hzE' : (((faceIncl (k+1) i z : ↥(simplexBdry (k+2)))) : ↥(stdSimplex ℝ (Fin (k+3)))) i
      = 0 := hzE
  change bfun (faceIncl (k+1) i z) = x i z
  have h1 : bfun (faceIncl (k+1) i z) = G i (faceIncl (k+1) i z) := hbval _ i hzE
  have h2 : G i (faceIncl (k+1) i z) =
      x i ⟨uncoface (k+1) i (faceIncl (k+1) i z).1, uncoface_mem (k+1) i _ hzE'⟩ := by
    simp only [G, dif_pos hzE']
  rw [h1, h2]
  congr 1
  apply Subtype.ext
  change uncoface (k+1) i ((faceIncl (k+1) i z : ↥(simplexBdry (k+2))) :
    ↥(stdSimplex ℝ (Fin (k+3)))) = z.1
  rw [faceIncl_coe]
  exact uncoface_coface (k+1) i z

end

end Work.Serre
