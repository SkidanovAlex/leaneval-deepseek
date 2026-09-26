import Mathlib
import Submission.Work.Drive.Mono.Geom3Defs
import Submission.Work.Drive.Mono.BoxGen
import Submission.Work.Drive.Mono.NoGrazeDefs
import Submission.Work.Drive.Mono.Band.HeightGoodDefs
import Submission.Work.Drive.Mono.Band.heightGood_exists_in
import Submission.Work.Drive.Mono.exists_countable_heightGood_dense

/-!
# A countable dense set of good height directions that avoids the chords of the box sphere

The third data package of the monotone (`BoxGenE`) route chooses the height direction `n` of the
sweep, and the sweep direction is then `v = orthDir (shiftVσ σ 1) (unitDir n)`: the normalised
component of the `σ 2`-axis orthogonal to `n`.  This file proves that the choice of `n` can be made
in a countable dense set `Q'` of good height directions (`Work.Drive.Mono.Band.HeightGood`) which is
*non-degenerate for the chords of the box sphere*: no chord of the trace
`F ∩ {boxNorm c σ = s}` is parallel to `orthDir (shiftVσ σ 1) (unitDir ng)`.

The mathematics is one elementary observation about the box.  Along a segment on which the box norm
is constant, one coordinate is constant (`g3_coord_eq_of_boxNorm_segment`): since the box norm is the
maximum of the three coordinate terms, at the *midpoint* of the segment some coordinate term
attains the maximum `s`; the coordinate function is affine on the segment and its absolute value is
bounded by `s` on the whole segment (as the box norm is the maximum), so the equality case of the
triangle inequality at `0`, `1/2` and `1` forces that coordinate to be constant on the segment.  Hence every chord of the trace has a *vanishing* coordinate, whereas
`orthDir (shiftVσ σ 1) (unitDir n)` has *no* vanishing coordinate as soon as `n` has none
(`g3_orthDir_unitDir_coord_ne_zero`).  Directions with all coordinates non-zero form an open dense
set, so intersecting them with the countable dense set of good height directions
(`Work.Drive.Mono.exists_countable_heightGood_dense`) gives `Q'`.

(No regularity or countability of the set of chord directions is needed: the genericity used is only
that the chosen direction has no vanishing coordinate.)

## Remark (what the genericity really is, and what it is not)

`g3_coord_eq_of_boxNorm_segment` is *optimal* in the following sense: a straight segment of the trace
`F ∩ {boxNorm c σ = s}` has a **vanishing σ-coordinate of its direction**, and this cannot be
improved — the trace really can contain a straight segment in a coordinate direction (the standard
example is a tube about a plane curve containing a straight piece, whose trace on the box face
`x = const` contains the translate of that piece).  What is used above is only the other side: for a
direction `n` with no vanishing coordinate the direction `orthDir (shiftVσ σ 1) (unitDir n)` has no
vanishing coordinate either, so it is *never* parallel to a chord of the trace, whatever the geometry
of the latter.  The statement is therefore not vacuous: it is exactly the "no `v`-chord" clause
(`∃ λ, y - y' = λ • v → y = y'`) for `v = orthDir (shiftVσ σ 1) (unitDir ng)`, and `Q'` consists of
the good height directions with all three coordinates non-zero (`g3_noVanishingCoord`).
-/

set_option linter.unusedVariables false

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open scoped RealInnerProductSpace

noncomputable section

/-! ## 1. The box norm along a segment -/

/-- The coordinates of a convex combination in `R3`. -/
theorem g3_coord_convex (y y' : R3) (t : ℝ) (i : Fin 3) :
    ((1 - t) • y + t • y') i = (1 - t) * y i + t * y' i := by
  simp

/-- The `σ i`-coordinate of the point of the segment from `y` to `y'`, relative to the centre `c`. -/
def g3_segCoord (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y y' : R3) (t : ℝ) : ℝ :=
  ((1 - t) • y + t • y') (σ i) - c (σ i)

theorem g3_segCoord_affine (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y y' : R3) (t : ℝ) :
    g3_segCoord c σ i y y' t = (y (σ i) - c (σ i)) + t * (y' (σ i) - y (σ i)) := by
  rw [g3_segCoord, g3_coord_convex]
  ring

theorem g3_segCoord_half (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (y y' : R3) :
    g3_segCoord c σ i y y' (1 / 2)
      = (g3_segCoord c σ i y y' 0 + g3_segCoord c σ i y y' 1) / 2 := by
  rw [g3_segCoord_affine, g3_segCoord_affine, g3_segCoord_affine]
  ring

/-- The box norm bounds each coordinate of the box. -/
theorem g3_abs_coord_sub_le_boxNorm (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) {z : R3}
    (h : Submission.boxNorm c σ z = s) (i : Fin 3) :
    |z (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
  have h1 : |z (σ i) - c (σ i)| / Submission.boxSide i ≤ Submission.boxNorm c σ z := by
    rw [Submission.boxNorm]
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · exact le_trans (le_max_left _ _) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
    · exact le_max_right _ _
  rw [h, div_le_iff₀ (Submission.boxSide_pos i)] at h1
  simpa [mul_comm] using h1

/-- A coordinate attaining the maximum defining the box norm. -/
theorem g3_exists_abs_coord_eq_boxNorm (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (z : R3)
    (h : Submission.boxNorm c σ z = s) :
    ∃ i : Fin 3, |z (σ i) - c (σ i)| = Submission.boxSide i * s := by
  rw [Submission.boxNorm] at h
  rcases max_eq_iff.mp h with ⟨h', _⟩ | ⟨h2, _⟩
  · rcases max_eq_iff.mp h' with ⟨h0, _⟩ | ⟨h1, _⟩
    · exact ⟨0, by rw [div_eq_iff (Submission.boxSide_pos 0).ne'] at h0; rw [h0]; ring⟩
    · exact ⟨1, by rw [div_eq_iff (Submission.boxSide_pos 1).ne'] at h1; rw [h1]; ring⟩
  · exact ⟨2, by rw [div_eq_iff (Submission.boxSide_pos 2).ne'] at h2; rw [h2]; ring⟩

/-- **The box sphere has no diagonal chord.**  If the box norm is constant along a (non-degenerate)
segment, then one of the σ-coordinates is constant along it. -/
theorem g3_coord_eq_of_boxNorm_segment {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y y' : R3}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, Submission.boxNorm c σ ((1 - t) • y + t • y') = s) :
    ∃ i : Fin 3, y (σ i) = y' (σ i) := by
  have hhalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  obtain ⟨i, hi⟩ := g3_exists_abs_coord_eq_boxNorm c σ s ((1 - (1 / 2)) • y + (1 / 2) • y')
    (h (1 / 2) hhalf)
  refine ⟨i, ?_⟩
  have hmid : |g3_segCoord c σ i y y' (1 / 2)| = Submission.boxSide i * s := by
    rw [g3_segCoord]
    exact hi
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g3_segCoord c σ i y y' t| ≤ Submission.boxSide i * s := by
    intro t ht
    rw [g3_segCoord]
    exact g3_abs_coord_sub_le_boxNorm c σ s (h t ht) i
  have h0 : |g3_segCoord c σ i y y' 0| ≤ Submission.boxSide i * s := hb 0 (by norm_num)
  have h1 : |g3_segCoord c σ i y y' 1| ≤ Submission.boxSide i * s := hb 1 (by norm_num)
  have htri : |g3_segCoord c σ i y y' 0 + g3_segCoord c σ i y y' 1|
      ≤ |g3_segCoord c σ i y y' 0| + |g3_segCoord c σ i y y' 1| := abs_add_le _ _
  have habs : |g3_segCoord c σ i y y' 0 + g3_segCoord c σ i y y' 1|
      = 2 * (Submission.boxSide i * s) := by
    have h2 : |(g3_segCoord c σ i y y' 0 + g3_segCoord c σ i y y' 1) / 2|
        = Submission.boxSide i * s := by
      rw [← hmid, g3_segCoord_half]
    rw [abs_div, abs_two] at h2
    linarith
  have hK0 : |g3_segCoord c σ i y y' 0| = Submission.boxSide i * s := by linarith
  have hK1 : |g3_segCoord c σ i y y' 1| = Submission.boxSide i * s := by linarith
  have habsK : |g3_segCoord c σ i y y' 0 + g3_segCoord c σ i y y' 1|
      = |g3_segCoord c σ i y y' 0| + |g3_segCoord c σ i y y' 1| := by
    rw [habs, hK0, hK1]; ring
  have hprod : g3_segCoord c σ i y y' 0 * g3_segCoord c σ i y y' 1
      = (Submission.boxSide i * s) ^ 2 := by
    have hsq : (g3_segCoord c σ i y y' 0 + g3_segCoord c σ i y y' 1) ^ 2
        = (|g3_segCoord c σ i y y' 0| + |g3_segCoord c σ i y y' 1|) ^ 2 := by
      rw [← sq_abs (g3_segCoord c σ i y y' 0 + g3_segCoord c σ i y y' 1), habsK]
    have e2 : (|g3_segCoord c σ i y y' 0| + |g3_segCoord c σ i y y' 1|) ^ 2
        = |g3_segCoord c σ i y y' 0| ^ 2
          + 2 * (|g3_segCoord c σ i y y' 0| * |g3_segCoord c σ i y y' 1|)
          + |g3_segCoord c σ i y y' 1| ^ 2 := by ring
    have e0 : |g3_segCoord c σ i y y' 0| ^ 2 = (Submission.boxSide i * s) ^ 2 := by rw [hK0]
    have e1 : |g3_segCoord c σ i y y' 1| ^ 2 = (Submission.boxSide i * s) ^ 2 := by rw [hK1]
    have e3 : (g3_segCoord c σ i y y' 0) ^ 2 = (Submission.boxSide i * s) ^ 2 := by
      rw [← sq_abs (g3_segCoord c σ i y y' 0), hK0]
    have e4 : (g3_segCoord c σ i y y' 1) ^ 2 = (Submission.boxSide i * s) ^ 2 := by
      rw [← sq_abs (g3_segCoord c σ i y y' 1), hK1]
    have e5 : |g3_segCoord c σ i y y' 0| * |g3_segCoord c σ i y y' 1|
        = (Submission.boxSide i * s) ^ 2 := by rw [hK0, hK1]; ring
    nlinarith [hsq, e2, e0, e1, e3, e4, e5]
  have hK0sq : (g3_segCoord c σ i y y' 0) ^ 2 = (Submission.boxSide i * s) ^ 2 := by
    rw [← sq_abs (g3_segCoord c σ i y y' 0), hK0]
  have hK1sq : (g3_segCoord c σ i y y' 1) ^ 2 = (Submission.boxSide i * s) ^ 2 := by
    rw [← sq_abs (g3_segCoord c σ i y y' 1), hK1]
  have hsq0 : (g3_segCoord c σ i y y' 0 - g3_segCoord c σ i y y' 1) ^ 2 = 0 := by
    have e : (g3_segCoord c σ i y y' 0 - g3_segCoord c σ i y y' 1) ^ 2
        = (g3_segCoord c σ i y y' 0) ^ 2
          - 2 * (g3_segCoord c σ i y y' 0 * g3_segCoord c σ i y y' 1)
          + (g3_segCoord c σ i y y' 1) ^ 2 := by ring
    rw [e, hK0sq, hK1sq, hprod]
    ring
  have h01 : g3_segCoord c σ i y y' 0 = g3_segCoord c σ i y y' 1 := by
    have h2 : g3_segCoord c σ i y y' 0 - g3_segCoord c σ i y y' 1 = 0 := sq_eq_zero_iff.mp hsq0
    linarith
  have haff0 := g3_segCoord_affine c σ i y y' 0
  have haff1 := g3_segCoord_affine c σ i y y' 1
  simp only [mul_one] at haff0 haff1
  linarith

/-! ## 2. The direction `orthDir (shiftVσ σ 1) (unitDir n)` -/

/-- **A direction with no vanishing coordinate has a sweep direction with no vanishing
coordinate.**  Here `orthDir (shiftVσ σ 1) (unitDir n)` is the normalised component of the
`σ 2`-axis orthogonal to `unitDir n`. -/
theorem g3_orthDir_unitDir_coord_ne_zero {σ : Equiv.Perm (Fin 3)} {n : R3}
    (hn : ∀ j : Fin 3, n j ≠ 0) (j : Fin 3) :
    orthDir (Work.BoxShrink.shiftVσ σ 1) (unitDir n) j ≠ 0 := by
  have hn0 : n ≠ 0 := fun h => hn 0 (by rw [h]; rfl)
  have hnorm0 : ‖n‖ ≠ 0 := norm_ne_zero_iff.mpr hn0
  set m := unitDir n with hm
  have hmj : ∀ j : Fin 3, m j ≠ 0 := by
    intro j
    rw [hm, unitDir]
    simp only [PiLp.smul_apply, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero hnorm0) (hn j)
  have hmn : ‖m‖ = 1 := by rw [hm]; exact unitDir_norm n hn0
  have hm2 : m (σ 2) ^ 2 ≠ 1 := by
    intro h
    have hsum : (∑ i : Fin 3, m i ^ 2) = 1 := by
      have h3 : inner ℝ m m = 1 := by
        rw [real_inner_self_eq_norm_sq, hmn]
        norm_num
      rw [PiLp.inner_apply] at h3
      simpa using h3
    rw [← Equiv.sum_comp σ (fun i : Fin 3 => m i ^ 2), Fin.sum_univ_three] at hsum
    have hz : m (σ 0) ^ 2 = 0 := by
      nlinarith [sq_nonneg (m (σ 0)), sq_nonneg (m (σ 1))]
    exact hmj (σ 0) (sq_eq_zero_iff.mp hz)
  set e := Work.BoxShrink.shiftVσ σ 1 with he
  set cc := e - inner ℝ e m • m with hcc
  have hinner : inner ℝ e m = m (σ 2) := inner_shiftVσ_one σ m
  have hcc_apply : cc j = e j - (inner ℝ e m) * m j := by
    rw [hcc]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  have he_apply : e j = if j = σ 2 then 1 else 0 := by
    rw [he, Work.BoxShrink.shiftVσ_apply]
  have hcj : cc j ≠ 0 := by
    by_cases hj : j = σ 2
    · subst hj
      rw [hcc_apply, he_apply, if_pos rfl, hinner]
      intro hzero
      exact hm2 (by linarith [hzero])
    · rw [hcc_apply, he_apply, if_neg hj, hinner, zero_sub]
      exact neg_ne_zero.mpr (mul_ne_zero (hmj (σ 2)) (hmj j))
  have hccne : cc ≠ 0 := fun h => hcj (by rw [h]; rfl)
  have horth : orthDir e m = ‖cc‖⁻¹ • cc := by rw [orthDir, ← hcc]
  rw [horth]
  simp only [PiLp.smul_apply, smul_eq_mul]
  exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hccne)) hcj

/-! ## 3. The open dense set of directions with no vanishing coordinate -/

/-- The directions with no vanishing coordinate. -/
def g3_noVanishingCoord : Set R3 := {n : R3 | ∀ j : Fin 3, n j ≠ 0}

theorem g3_isOpen_noVanishingCoord : IsOpen g3_noVanishingCoord := by
  have hset : g3_noVanishingCoord = ⋂ j : Fin 3, {n : R3 | n j ≠ 0} := by
    ext n; simp [g3_noVanishingCoord]
  rw [hset]
  refine isOpen_iInter_of_finite fun j => ?_
  have h : {n : R3 | n j ≠ 0} = (EuclideanSpace.proj (𝕜 := ℝ) j) ⁻¹' ({0}ᶜ : Set ℝ) := by
    ext n
    simp [EuclideanSpace.coe_proj]
  rw [h]
  exact (isOpen_compl_singleton (x := (0 : ℝ))).preimage
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous

theorem g3_dense_noVanishingCoord : Dense g3_noVanishingCoord := by
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨x, hxU⟩ := hne
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU x hxU
  set w : R3 := WithLp.toLp 2 (fun _ : Fin 3 => (1 : ℝ)) with hw
  have hwapp : ∀ i : Fin 3, w i = 1 := fun i => by rw [hw]
  have hwne : w ≠ 0 := fun h => by
    have h1 : w 0 = 0 := by rw [h]; rfl
    rw [hwapp 0] at h1
    exact one_ne_zero h1
  have hwnormpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  obtain ⟨δ, hδ, hδρ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * ‖w‖ < ρ := by
    refine ⟨ρ / (2 * ‖w‖), by positivity, ?_⟩
    have h3 : ρ / (2 * ‖w‖) * ‖w‖ = ρ / 2 := by
      field_simp
    rw [h3]
    linarith
  set F : Finset ℝ := {-(x 0), -(x 1), -(x 2), 0} with hF
  have hInf : (Set.Ioo (0 : ℝ) δ).Infinite := Set.Ioo_infinite hδ
  obtain ⟨ε, hεI, hεF⟩ := hInf.exists_notMem_finset F
  refine ⟨x + ε • w, ?_, ?_⟩
  · apply hρU
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : x + ε • w - x = ε • w := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hεI.1]
    calc ε * ‖w‖ < δ * ‖w‖ := mul_lt_mul_of_pos_right hεI.2 hwnormpos
      _ < ρ := hδρ
  · intro j
    have hcoord : (x + ε • w) j = x j + ε := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hwapp, mul_one]
    rw [hcoord]
    intro hzero
    have heq : ε = -(x j) := by linarith
    apply hεF
    rw [heq, hF]
    fin_cases j <;> simp

/-! ## 4. The statement -/

theorem g3_exists_dense_heightGood_avoiding_chords (ψ : Submission.Diffeo) {s : ℝ}
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (hBG : Work.Drive.Mono.BoxGen ψ c σ s) :
    ∃ Q' : Set LeanEval.KnotTheory.PardonDistortion.R3, Q'.Countable ∧
      (∀ n ∈ Q', Work.Drive.Mono.Band.HeightGood ψ n) ∧
      (∀ U : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen U → U.Nonempty →
        (U ∩ Q').Nonempty) ∧
      (∀ ng ∈ Q', ∀ y y' : LeanEval.KnotTheory.PardonDistortion.R3,
        y ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        y' ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        Submission.boxNorm c σ y = s → Submission.boxNorm c σ y' = s →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          (1 - t) • y + t • y' ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
          Submission.boxNorm c σ ((1 - t) • y + t • y') = s) →
        (∃ kk : ℝ, y - y' = kk • Work.Drive.Mono.orthDir (Work.BoxShrink.shiftVσ σ 1)
          (Work.Drive.Mono.unitDir ng)) → y = y') := by
  classical
  obtain ⟨Q, hQc, hQH, hQd⟩ := exists_countable_heightGood_dense ψ
  refine ⟨Q ∩ g3_noVanishingCoord, hQc.mono Set.inter_subset_left, ?_, ?_, ?_⟩
  · intro n hn
    exact hQH n hn.1
  · intro U hU hne
    obtain ⟨n, hnU, hnZ⟩ := (dense_iff_inter_open.mp g3_dense_noVanishingCoord) U hU hne
    obtain ⟨n', ⟨hn'U, hn'Z⟩, hn'Q⟩ :=
      hQd (U ∩ g3_noVanishingCoord) (hU.inter g3_isOpen_noVanishingCoord) ⟨n, hnU, hnZ⟩
    exact ⟨n', hn'U, hn'Q, hn'Z⟩
  · intro ng hng y y' hy hy' hyb hyb' hseg hchord
    obtain ⟨hi, hcoord⟩ := g3_coord_eq_of_boxNorm_segment
      (s := s) (c := c) (σ := σ) (y := y) (y' := y') (fun t ht => (hseg t ht).2)
    have hngNZ : ∀ j : Fin 3, ng j ≠ 0 := hng.2
    have hdir : orthDir (Work.BoxShrink.shiftVσ σ 1) (unitDir ng) (σ hi) ≠ 0 :=
      g3_orthDir_unitDir_coord_ne_zero hngNZ (σ hi)
    obtain ⟨kk, hkk⟩ := hchord
    have hk0 : kk = 0 := by
      have h1 : (y - y') (σ hi) = 0 := by
        simp only [PiLp.sub_apply, hcoord, sub_self]
      rw [hkk, PiLp.smul_apply, smul_eq_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_right hdir
    rw [hk0, zero_smul] at hkk
    exact sub_eq_zero.mp hkk

end

end Work.Drive.Mono
