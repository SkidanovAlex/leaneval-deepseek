import Mathlib
import Submission.Work.HomologyExtra.SimplexDisk

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HomologyExtra

noncomputable section

/-!
# Elementary properties of the corner model of the simplex

`Work.HomologyExtra.cornerSimplex n` is the compact convex body
`{y : ℝⁿ | y ≥ 0, ∑ᵢ yᵢ ≤ 1}` (the image of `Δⁿ` under forgetting the last barycentric
coordinate).  This file records the basic point-set facts about it that the reduction of the
simplex pair `(Δⁿ, ∂Δⁿ)` to the disc pair `(Dⁿ, Sⁿ⁻¹)` needs: convexity, closedness,
boundedness, and a description of its interior and its topological frontier.

The interior is the set of points with *strictly* positive coordinates and *strictly* smaller
than `1` coordinate sum, so a point of the corner lies on the frontier exactly when it is in the
corner and either its coordinate sum equals `1` or one of its coordinates vanishes; this is
precisely the image of `∂Δⁿ`.
-/

/-- The `i`-th standard basis vector of `EuclideanSpace ℝ (Fin n)`, scaled by `c`
(i.e. `c` in coordinate `i` and `0` elsewhere). -/
private def cornerUnitVec (n : ℕ) (i : Fin n) (c : ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (Pi.single i c)

private theorem cornerUnitVec_self (n : ℕ) (i : Fin n) (c : ℝ) :
    cornerUnitVec n i c i = c := by
  simp [cornerUnitVec]

private theorem cornerUnitVec_sum (n : ℕ) (i : Fin n) (c : ℝ) :
    ∑ j : Fin n, cornerUnitVec n i c j = c := by
  simp [cornerUnitVec]

/-- The coordinate sum of a small translation `y + t • d` is the translate of the coordinate
sum by `t` times the coordinate sum of `d`. -/
private theorem cornerSimplex_sum_add_smul (n : ℕ) (y d : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ∑ i, (y + t • d) i = (∑ i, y i) + t * ∑ i, d i := by
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
  rw [Finset.mul_sum]

/-- If `y` lies in the interior of `s`, then for every direction `d` some point of the ray
`y + t • d`, `t > 0`, still lies in `s`. -/
private theorem cornerSimplex_exists_pos_smul_mem_of_mem_interior {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {y d : E} (hy : y ∈ interior s) :
    ∃ t : ℝ, 0 < t ∧ y + t • d ∈ s := by
  have hcont : Continuous fun t : ℝ => y + t • d := by fun_prop
  have hy' : y + (0 : ℝ) • d ∈ interior s := by simpa using hy
  have hmem : (fun t : ℝ => y + t • d) ⁻¹' interior s ∈ nhds (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hy')
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨ε / 2, by linarith, interior_subset (hball ?_)⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
  linarith

/-- The interior of a coordinate half-space is the corresponding open half-space.  This is the
openness of a coordinate projection of `EuclideanSpace`. -/
private theorem cornerSimplex_coord_interior (n : ℕ) (i : Fin n) :
    interior {y : EuclideanSpace ℝ (Fin n) | 0 ≤ y i} = {y | 0 < y i} := by
  have h : {y : EuclideanSpace ℝ (Fin n) | 0 ≤ y i}
      = (fun f : PiLp 2 (fun _ : Fin n => ℝ) => f.ofLp i) ⁻¹' (Set.Ici (0 : ℝ)) := rfl
  rw [h, ← IsOpenMap.preimage_interior_eq_interior_preimage
        (PiLp.isOpenMap_apply 2 (fun _ : Fin n => ℝ) i)
        (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i) (Set.Ici (0 : ℝ)), interior_Ici]
  rfl

/-- The interior of the non-negative orthant. -/
private theorem cornerSimplex_orthant_interior (n : ℕ) :
    interior {y : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ y i} = {y | ∀ i, 0 < y i} := by
  have h : {y : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ y i} = ⋂ i : Fin n, {y | 0 ≤ y i} := by
    ext y; simp
  rw [h, interior_iInter_of_finite]
  ext y
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, cornerSimplex_coord_interior]

/-- The interior of the half-space `{y | ∑ᵢ yᵢ ≤ 1}` is the open half-space `{y | ∑ᵢ yᵢ < 1}`;
here `1 ≤ n` is needed to move in a direction increasing the coordinate sum. -/
private theorem cornerSimplex_sum_interior (n : ℕ) (hn : 1 ≤ n) :
    interior {y : EuclideanSpace ℝ (Fin n) | ∑ i, y i ≤ 1} = {y | ∑ i, y i < 1} := by
  apply Set.Subset.antisymm
  · intro y hy
    have hy2 := interior_subset hy
    have hyB : ∑ i, y i ≤ 1 := by simpa using hy2
    rcases lt_or_eq_of_le hyB with h | h
    · exact h
    · exfalso
      obtain ⟨t, ht, hyt⟩ :=
        cornerSimplex_exists_pos_smul_mem_of_mem_interior
          (s := {y : EuclideanSpace ℝ (Fin n) | ∑ i, y i ≤ 1}) hy
          (d := cornerUnitVec n ⟨0, by omega⟩ 1)
      have hsum : ∑ i, cornerUnitVec n ⟨0, by omega⟩ 1 i = 1 := cornerUnitVec_sum n _ 1
      have hle : ∑ i, (y + t • cornerUnitVec n ⟨0, by omega⟩ 1) i ≤ 1 := hyt
      rw [cornerSimplex_sum_add_smul, hsum] at hle
      linarith
  · intro y hy
    have hopen : IsOpen {z : EuclideanSpace ℝ (Fin n) | ∑ i, z i < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    have hy' : y ∈ interior {z : EuclideanSpace ℝ (Fin n) | ∑ i, z i < 1} := by
      rw [hopen.interior_eq]; exact hy
    have hsub : {z : EuclideanSpace ℝ (Fin n) | ∑ i, z i < 1} ⊆
        {z : EuclideanSpace ℝ (Fin n) | ∑ i, z i ≤ 1} :=
      fun z hz => by simpa using le_of_lt (show ∑ i, z i < 1 from hz)
    exact interior_mono hsub hy'

/-! ## The basic facts -/

private theorem convex_cornerSimplex (n : ℕ) : Convex ℝ (cornerSimplex n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    nlinarith [hx.1 i, hy.1 i]
  · have h1 : ∑ i, (a • x + b • y) i = a * (∑ i, x i) + b * (∑ i, y i) := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib]
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [h1]
    have h2 : a * (∑ i, x i) ≤ a * 1 := mul_le_mul_of_nonneg_left hx.2 ha
    have h3 : b * (∑ i, y i) ≤ b * 1 := mul_le_mul_of_nonneg_left hy.2 hb
    linarith

private theorem isClosed_cornerSimplex (n : ℕ) : IsClosed (cornerSimplex n) := by
  have h : cornerSimplex n =
      (⋂ i : Fin n, {y : EuclideanSpace ℝ (Fin n) | 0 ≤ y i}) ∩ {y | ∑ i, y i ≤ 1} := by
    ext y; simp [cornerSimplex]
  rw [h]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
  · exact isClosed_le (by fun_prop) continuous_const

private theorem isBounded_cornerSimplex (n : ℕ) : Bornology.IsBounded (cornerSimplex n) := by
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)).subset ?_
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_one.mpr
  calc ∑ i, ‖y i‖ ^ 2 = ∑ i, (y i) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.norm_of_nonneg (hy.1 i)]
    _ ≤ ∑ i, y i := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : y i ≤ 1 :=
          le_trans (Finset.single_le_sum (fun j _ => hy.1 j) (Finset.mem_univ i)) hy.2
        nlinarith [hy.1 i]
    _ ≤ 1 := hy.2

private theorem interior_cornerSimplex (n : ℕ) (hn : 1 ≤ n) :
    interior (cornerSimplex n) =
      {y : EuclideanSpace ℝ (Fin n) | (∀ i, 0 < y i) ∧ ∑ i, y i < 1} := by
  have h : cornerSimplex n =
      {y : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ y i} ∩ {y | ∑ i, y i ≤ 1} := by
    ext y; simp [cornerSimplex]
  rw [h, interior_inter, cornerSimplex_orthant_interior, cornerSimplex_sum_interior n hn]
  ext y; simp

/-- A point of the corner lies on its topological frontier exactly when it is in the corner and
either its coordinate sum is `1` (the "far facet" `Δⁿ⁻¹`) or one of its coordinates vanishes
(the coordinate hyperplane facets). -/
private theorem mem_frontier_cornerSimplex (n : ℕ) (hn : 1 ≤ n) (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ frontier (cornerSimplex n) ↔
      y ∈ cornerSimplex n ∧ (∑ i, y i = 1 ∨ ∃ i, y i = 0) := by
  have hclosed := isClosed_cornerSimplex n
  have hint := interior_cornerSimplex n hn
  rw [hclosed.frontier_eq, hint]
  constructor
  · rintro ⟨hyS, hyI⟩
    have hyS' : (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1 := hyS
    refine ⟨hyS, ?_⟩
    by_contra hcon
    obtain ⟨hne1, hne2⟩ := not_or.mp hcon
    have hall : ∀ i, y i ≠ 0 := fun i => not_exists.mp hne2 i
    apply hyI
    exact ⟨fun i => lt_of_le_of_ne (hyS'.1 i) (Ne.symm (hall i)),
      lt_of_le_of_ne hyS'.2 hne1⟩
  · rintro ⟨hyS, h⟩
    refine ⟨hyS, ?_⟩
    intro hmem
    have hmem' : (∀ i, 0 < y i) ∧ ∑ i, y i < 1 := hmem
    rcases h with h1 | h2
    · exact absurd h1 (ne_of_lt hmem'.2)
    · obtain ⟨i, hi⟩ := h2
      exact absurd hi (ne_of_gt (hmem'.1 i))

theorem cornerSimplex_facts (n : ℕ) (hn : 1 ≤ n) :
    Convex ℝ (Work.HomologyExtra.cornerSimplex n) ∧
      IsClosed (Work.HomologyExtra.cornerSimplex n) ∧
        Bornology.IsBounded (Work.HomologyExtra.cornerSimplex n) ∧
          interior (Work.HomologyExtra.cornerSimplex n) =
            {y : EuclideanSpace ℝ (Fin n) | (∀ i, 0 < y i) ∧ ∑ i, y i < 1} ∧
          (∀ y : EuclideanSpace ℝ (Fin n), y ∈ frontier (Work.HomologyExtra.cornerSimplex n) ↔
            y ∈ Work.HomologyExtra.cornerSimplex n ∧ (∑ i, y i = 1 ∨ ∃ i, y i = 0)) := by
  exact ⟨convex_cornerSimplex n, isClosed_cornerSimplex n, isBounded_cornerSimplex n,
    interior_cornerSimplex n hn, mem_frontier_cornerSimplex n hn⟩

end

end Work.HomologyExtra
