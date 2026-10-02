import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The standard simplex is a retract of the cube

`stdSimplex ℝ (Fin (n + 1))` is the set of nonnegative vectors of total mass `1` in
`Fin (n + 1) → ℝ`, and hence a subset of the unit cube `Fin (n + 1) → Set.Icc 0 1`.
We exhibit a continuous inclusion `i` of the simplex into the cube together with a
continuous retraction `r` of the cube onto the simplex (with `r ∘ i = id`), by pushing
every point of the cube along a straight line towards the uniform point
`(1/(n+1), …, 1/(n+1)) ∈ Δⁿ`, far enough to reach the hyperplane of total mass `1`:

`r y j = ((y j) + max (1 - ∑ y k) 0) / ((∑ y k) + (n + 1) * max (1 - ∑ y k) 0)`.

The numerator correction `a = max (1 - Σ) 0` is continuous, so is the denominator,
and the denominator is `≥ 1` (it equals the total mass when that is `≥ 1`, and
`(n+1) - n·Σ ≥ 1` otherwise).  On the simplex itself `Σ = 1`, `a = 0`, the denominator
is `1`, and `r` is the identity.
-/

namespace Work.RatHurewicz

open Set

/-- The unit cube `[0,1]^(n+1)`, as a type. -/
private abbrev Cube (n : ℕ) : Type := Fin (n + 1) → Set.Icc (0 : ℝ) 1

/-- Total mass `∑ j, y j` of a point of the cube. -/
private noncomputable def cubeSum {n : ℕ} (y : Cube n) : ℝ := ∑ j, (y j : ℝ)

/-- The shift `max (1 - Σ) 0` added to every coordinate. -/
private noncomputable def cubeShift {n : ℕ} (y : Cube n) : ℝ := max (1 - cubeSum y) 0

/-- The normalising denominator.  It is `≥ 1`, see `one_le_cubeNorm`. -/
private noncomputable def cubeNorm {n : ℕ} (y : Cube n) : ℝ :=
  cubeSum y + ((n + 1 : ℕ) : ℝ) * cubeShift y

/-- The retraction of the cube onto the simplex, as a bare function. -/
private noncomputable def cubeRetractFun {n : ℕ} (y : Cube n) : Fin (n + 1) → ℝ :=
  fun j => ((y j : ℝ) + cubeShift y) / cubeNorm y

private lemma cubeSum_nonneg {n : ℕ} (y : Cube n) : 0 ≤ cubeSum y :=
  Finset.sum_nonneg fun j _ => (y j).2.1

private lemma cubeShift_nonneg {n : ℕ} (y : Cube n) : 0 ≤ cubeShift y := le_max_right _ _

private lemma one_le_cubeNorm {n : ℕ} (y : Cube n) : 1 ≤ cubeNorm y := by
  have hs : 0 ≤ cubeSum y := cubeSum_nonneg y
  have hc : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n) : 1 ≤ n + 1)
  rcases le_total (cubeSum y) 1 with h | h
  · have hsh : cubeShift y = 1 - cubeSum y := by
      rw [cubeShift, max_eq_left]; linarith
    rw [cubeNorm, hsh]
    nlinarith [mul_le_mul_of_nonneg_left h (by linarith : (0:ℝ) ≤ ((n+1:ℕ):ℝ))]
  · have hsh : cubeShift y = 0 := by rw [cubeShift, max_eq_right]; linarith
    rw [cubeNorm, hsh, mul_zero, add_zero]
    linarith

private lemma cubeNorm_pos {n : ℕ} (y : Cube n) : 0 < cubeNorm y :=
  lt_of_lt_of_le one_pos (one_le_cubeNorm y)

private lemma cubeRetractFun_sum {n : ℕ} (y : Cube n) : ∑ j, cubeRetractFun y j = 1 := by
  show ∑ j, ((y j : ℝ) + cubeShift y) / cubeNorm y = 1
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have h1 : (∑ j : Fin (n+1), cubeShift y) = ((n + 1 : ℕ) : ℝ) * cubeShift y := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [h1]
  change cubeNorm y / cubeNorm y = 1
  exact div_self (ne_of_gt (cubeNorm_pos y))

private lemma cubeRetractFun_mem {n : ℕ} (y : Cube n) :
    cubeRetractFun y ∈ stdSimplex ℝ (Fin (n + 1)) :=
  ⟨fun j => div_nonneg (add_nonneg (y j).2.1 (cubeShift_nonneg y))
      (le_of_lt (cubeNorm_pos y)), cubeRetractFun_sum y⟩

private lemma continuous_cubeSum {n : ℕ} : Continuous (cubeSum (n := n)) := by
  unfold cubeSum
  exact continuous_finsetSum _ fun j _ => continuous_subtype_val.comp (continuous_apply j)

private lemma continuous_cubeShift {n : ℕ} : Continuous (cubeShift (n := n)) := by
  unfold cubeShift
  exact Continuous.max (continuous_const.sub continuous_cubeSum) continuous_const

private lemma continuous_cubeNorm {n : ℕ} : Continuous (cubeNorm (n := n)) := by
  unfold cubeNorm
  exact continuous_cubeSum.add (continuous_const.mul continuous_cubeShift)

private lemma continuous_cubeRetractFun {n : ℕ} : Continuous (cubeRetractFun (n := n)) := by
  unfold cubeRetractFun
  exact continuous_pi fun j =>
    (((continuous_subtype_val.comp (continuous_apply j)).add continuous_cubeShift).div
      continuous_cubeNorm fun y => ne_of_gt (cubeNorm_pos y))

/-- The inclusion of the standard simplex into the unit cube. -/
private noncomputable def simplexIncl (n : ℕ) : C(stdSimplex ℝ (Fin (n + 1)), Cube n) :=
  ⟨fun x j => ⟨x.1 j, mem_Icc_of_mem_stdSimplex x.2 j⟩, by
    apply continuous_pi
    intro j
    exact Continuous.subtype_mk ((continuous_apply j).comp continuous_subtype_val) _⟩

private lemma simplexIncl_apply (n : ℕ) (x : stdSimplex ℝ (Fin (n + 1))) (j : Fin (n + 1)) :
    ((simplexIncl n x) j : ℝ) = x.1 j := rfl

private lemma cubeSum_simplexIncl (n : ℕ) (x : stdSimplex ℝ (Fin (n + 1))) :
    cubeSum (simplexIncl n x) = ∑ j, x.1 j := by
  unfold cubeSum
  exact Finset.sum_congr rfl fun j _ => simplexIncl_apply n x j

/-- The retraction of the unit cube onto the standard simplex. -/
private noncomputable def cubeRetract (n : ℕ) : C(Cube n, stdSimplex ℝ (Fin (n + 1))) :=
  ⟨fun y => ⟨cubeRetractFun y, cubeRetractFun_mem y⟩,
    Continuous.subtype_mk continuous_cubeRetractFun fun y => cubeRetractFun_mem y⟩

theorem retract_stdSimplex_cube (n : ℕ) :
    ∃ (i : C(stdSimplex ℝ (Fin (n + 1)), Fin (n + 1) → Set.Icc (0:ℝ) 1))
      (r : C(Fin (n + 1) → Set.Icc (0:ℝ) 1, stdSimplex ℝ (Fin (n + 1)))),
      r.comp i = ContinuousMap.id _ := by
  refine ⟨simplexIncl n, cubeRetract n, ?_⟩
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  funext j
  show cubeRetractFun (simplexIncl n x) j = x.1 j
  have hsum : cubeSum (simplexIncl n x) = 1 := by
    rw [cubeSum_simplexIncl]; exact x.2.2
  have hshift : cubeShift (simplexIncl n x) = 0 := by
    rw [cubeShift, hsum]; norm_num
  have hnorm : cubeNorm (simplexIncl n x) = 1 := by
    rw [cubeNorm, hsum, hshift, mul_zero, add_zero]
  rw [cubeRetractFun, hshift, hnorm, simplexIncl_apply]
  norm_num

end Work.RatHurewicz
