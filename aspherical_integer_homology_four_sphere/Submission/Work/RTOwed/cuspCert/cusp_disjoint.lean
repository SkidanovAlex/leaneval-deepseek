/-
# The five ceiling tori of `M̄` are pairwise disjoint

This file proves `Work.RTOwed.cuspCert.cusp_disjoint`, one of the certificates of the concrete cusp
development of `Work.FoldInst.Mbar` (definitions in `Submission/Work/RTOwed/cuspDev.lean`): the
ranges of the ceiling maps `mbarPt v : E3 → M̄` of two different cusps `v ≠ v'` are disjoint.

## The mathematics

`mbarPt v x = mk (cuspPtX v x)`, where `cuspPtX v x = (cubeBit a, kleinPt a (redV v x))` with
`a = cubeOf v x` is a cube of the cusp `v` (`Work.Cusp.cubeCusp a = v`).  So a point of
`range (mbarPt v)` is the class of a point of `Q̄` lying on the *truncation facet* of the ideal
vertex `w = cubeVert a`, and `v` is the *orbit* of `w` under the group `Gg` of sign changes (the
five cusps are the five orbits of `Gg` on the 24 ideal vertices: the four pairs `{±e_i}` of
coordinate vertices and the 16 diagonal vertices).

The two ingredients of the proof are then:

* **the orbit of a tight truncation vertex is well defined on `Q̄`** (`tight_cusp`): if a point
  `y ∈ Q̄` lies on the truncation facets of two vertices `w`, `w'`, then `w` and `w'` have the same
  cusp.  This is a small explicit convexity computation: the side constraints of `Q̄` give
  `|y_i| + |y_j| ≤ 1` for `i ≠ j`, the truncation constraints at `±e_i` give `|y_i| ≤ 4/5`, whence
  `|Σ_i ± y_i| ≤ 7/5 < 8/5`: two coordinate vertices of different axes, or a coordinate vertex and
  a diagonal vertex, cannot both be tight.
* **the cusp of a vertex is invariant under `Gg`** (`cuspOfVert_truncPerm`): `truncPerm g` is the
  sign change of the ideal vertices, and each of the five orbits is `Gg`-invariant.

The relation `~₁` of `M̄` identifies `x` with `γ · x` for a group element `γ`; since the action maps
the truncation facet of `w` to that of `truncPerm γ.1 w`, a common point of `range (mbarPt v)` and
`range (mbarPt v')` would force `cuspOfVert (cubeVert a) = cuspOfVert (cubeVert b)`, i.e. `v = v'`.

The finite certificates about the cubes (the image of a cube lies in `Q̄`, on the truncation facet of
its own vertex) are those of `Submission/Work/RTOwed/cuspCert/cube_quad.lean`.
-/
import Mathlib
import Submission.Work.RTOwed.cuspDev
import Submission.Work.RTOwed.cuspCertWalls
import Submission.Work.RTOwed.cuspCert.cube_quad
import Submission.Work.RTOwed.cuspCert.lattice_bridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set

namespace Work.RTOwed.cuspCert

open Work.RTOwed

/-! ## The cusp of a truncation vertex -/

/-- The cusp (`Fin 5`) of an ideal vertex of `Q̄` (index `0..23`, RT numbering minus one): the four
coordinate vertices `16..23` (`±e_0, ±e_1, ±e_2, ±e_3`) give the cusps `0..3`, and the 16 diagonal
vertices `0..15` give the cusp `4`. -/
def cuspOfVert (w : Fin 24) : Fin 5 :=
  if (w : ℕ) < 16 then 4 else ⟨((w : ℕ) - 16) / 2, by omega⟩

/-- The coordinate axis of a coordinate vertex. -/
def axisIdx (w : Fin 24) : Fin 4 := ⟨((w : ℕ) - 16) / 2, by omega⟩

/-- The sign of a coordinate vertex. -/
def axisSign (w : Fin 24) : ℤ := if (w : ℕ) % 2 = 0 then 1 else -1

lemma cuspOfVert_eq_four_iff (w : Fin 24) : cuspOfVert w = 4 ↔ (w : ℕ) < 16 := by
  fin_cases w <;> decide +kernel

lemma axisSign_pm (w : Fin 24) : axisSign w = 1 ∨ axisSign w = -1 := by
  unfold axisSign; split <;> simp

lemma axis_n2_form (w : Fin 24) (h : 16 ≤ (w : ℕ)) :
    Work.FoldInst.truncNormal2 w = fun r => if r = axisIdx w then 2 * axisSign w else 0 := by
  revert h; fin_cases w <;> decide +kernel

lemma cuspOfVert_axis (w : Fin 24) (h : 16 ≤ (w : ℕ)) : cuspOfVert w = (axisIdx w).castSucc := by
  revert h; fin_cases w <;> decide +kernel

lemma half_entry_z (w : Fin 24) (h : (w : ℕ) < 16) : ∀ r : Fin 4,
    Work.FoldInst.truncNormal2 w r = 1 ∨ Work.FoldInst.truncNormal2 w r = -1 := by
  revert h; fin_cases w <;> decide +kernel

/-- The cusp of a cube is the cusp of its ideal vertex. -/
theorem cubeCusp_cuspOfVert (a : Fin 48) :
    Work.Cusp.cubeCusp a = cuspOfVert (cubeVert a) := by
  revert a; decide +kernel

/-- **The cusp of an ideal vertex is invariant under the sign-change group.** -/
theorem cuspOfVert_truncPerm (g : Fin 4 → ZMod 2) (w : Fin 24) :
    cuspOfVert (Work.FoldInst.truncPerm g w) = cuspOfVert w := by
  revert g w; decide +kernel

set_option maxHeartbeats 4000000 in
/-- The cube of a residue class, with the residues given as `Fin 4` values. -/
theorem cubeCusp_cubeOfMod_aux (v : Fin 5) (p : Fin 3 → Fin 4) :
    Work.Cusp.cubeCusp (Work.Cusp.cubeOfMod v (fun i => (p i : ℤ))) = v := by
  revert p
  fin_cases v <;> decide +kernel

/-- **The cube of a residue class is a cube of that cusp.** -/
theorem cubeCusp_cubeOfMod (v : Fin 5) (p : Fin 3 → ℤ) :
    Work.Cusp.cubeCusp (Work.Cusp.cubeOfMod v p) = v := by
  have hb : ∀ i : Fin 3, 0 < (Work.Cusp.latMod v i : ℤ) := by
    intro i; fin_cases v <;> fin_cases i <;> decide +kernel
  have hm : ∀ i : Fin 3, (Work.Cusp.latMod v i : ℤ) ≤ 4 := by
    intro i; fin_cases v <;> fin_cases i <;> decide +kernel
  have hp : Work.Cusp.cubeOfMod v p
      = Work.Cusp.cubeOfMod v (fun i => p i % (Work.Cusp.latMod v i : ℤ)) := by
    have h : p = (fun i => p i % (Work.Cusp.latMod v i : ℤ)) +
        (fun i => (Work.Cusp.latMod v i : ℤ) * (p i / (Work.Cusp.latMod v i : ℤ))) := by
      funext i
      simp only [Pi.add_apply]
      have h' := Int.mul_ediv_add_emod (p i) (Work.Cusp.latMod v i : ℤ)
      linarith
    conv_lhs => rw [h]
    exact cubeOfMod_add_latMod v _ _
  rw [hp]
  obtain ⟨q, hq⟩ : ∃ q : Fin 3 → Fin 4,
      ∀ i : Fin 3, (q i : ℤ) = p i % (Work.Cusp.latMod v i : ℤ) := by
    refine ⟨fun i => ⟨(p i % (Work.Cusp.latMod v i : ℤ)).toNat, ?_⟩, fun i => ?_⟩
    · have h1 : 0 ≤ p i % (Work.Cusp.latMod v i : ℤ) := Int.emod_nonneg _ (ne_of_gt (hb i))
      have h2 : p i % (Work.Cusp.latMod v i : ℤ) < 4 :=
        lt_of_lt_of_le (Int.emod_lt_of_pos _ (hb i)) (hm i)
      have h3 := Int.toNat_of_nonneg h1
      omega
    · exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt (hb i)))
  rw [show (fun i => p i % (Work.Cusp.latMod v i : ℤ)) = fun i => (q i : ℤ) from
    funext fun i => (hq i).symm]
  exact cubeCusp_cubeOfMod_aux v q

/-! ## The explicit convexity computation on `Q̄` -/

lemma sum_ite_pair (i k : Fin 4) (s t : ℝ) (y : Fin 4 → ℝ) :
    ∑ j : Fin 4, ((if j = i then s else 0) + (if j = k then t else 0)) * y j
      = s * y i + t * y k := by
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

lemma sum_pair_cast (i k : Fin 4) (s t : ℤ) (y : Fin 4 → ℝ) :
    ∑ j : Fin 4, (((if j = i then s else 0) + (if j = k then t else 0) : ℤ) : ℝ) * y j
      = (s:ℝ) * y i + (t:ℝ) * y k := by
  simp only [Int.cast_add, Int.cast_ite, Int.cast_zero]
  exact sum_ite_pair i k (s:ℝ) (t:ℝ) y

lemma sum_single_cast (i : Fin 4) (a : ℤ) (y : Fin 4 → ℝ) :
    ∑ r : Fin 4, (((if r = i then a else 0) : ℤ) : ℝ) * y r = (a:ℝ) * y i := by
  simp only [Int.cast_ite, Int.cast_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- The side of the 24-cell with normal `s·e_i + t·e_k` (`i ≠ k`, `s, t = ±1`). -/
lemma exists_side (i k : Fin 4) (h : i ≠ k) (s t : ℤ) (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) :
    ∃ S : Fin 24, ∀ j : Fin 4, Work.FoldInst.sideNormal S j
      = (if j = i then s else 0) + (if j = k then t else 0) := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    fin_cases i <;> fin_cases k <;> first | exact absurd rfl h | decide

/-- The coordinate vertex of `Q` with truncation normal `2 s e_i`. -/
lemma exists_axis (i : Fin 4) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    ∃ w : Fin 24, Work.FoldInst.truncNormal2 w = fun r => if r = i then 2 * s else 0 := by
  rcases hs with rfl | rfl <;> fin_cases i <;> decide +kernel

/-- **The side constraints of `Q̄`**: `s·y_i + t·y_k ≤ 1` for every choice of signs. -/
lemma pair_le (y : Work.FoldInst.E4) (hy : y ∈ Work.FoldInst.Qbar) (i k : Fin 4) (h : i ≠ k)
    (s t : ℤ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    (s:ℝ) * y i + (t:ℝ) * y k ≤ 1 := by
  obtain ⟨S, hS⟩ := exists_side i k h s t hs ht
  have hcon : (0:ℝ) ≤ Work.FoldInst.sideSlack S y := hy.1 S
  have hsum : ∑ j : Fin 4, (Work.FoldInst.sideNormal S j : ℝ) * y j
      = (s:ℝ) * y i + (t:ℝ) * y k := by
    have h1 : ∑ j : Fin 4, (Work.FoldInst.sideNormal S j : ℝ) * y j
        = ∑ j : Fin 4, (((if j = i then s else 0) + (if j = k then t else 0) : ℤ) : ℝ) * y j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hS j]
    rw [h1, sum_pair_cast]
  simp only [Work.FoldInst.sideSlack, hsum] at hcon
  linarith

/-- **Two distinct coordinates of a point of `Q̄`**: `|y_i| + |y_k| ≤ 1` for `i ≠ k`. -/
lemma abs_add_le_one (y : Work.FoldInst.E4) (hy : y ∈ Work.FoldInst.Qbar) {i k : Fin 4}
    (h : i ≠ k) : |y i| + |y k| ≤ 1 := by
  have h1 : y i + y k ≤ 1 := by
    have := pair_le y hy i k h 1 1 (Or.inl rfl) (Or.inl rfl)
    push_cast at this; linarith
  have h3 : y i - y k ≤ 1 := by
    have := pair_le y hy i k h 1 (-1) (Or.inl rfl) (Or.inr rfl)
    push_cast at this; linarith
  have h5 : |y i + y k| ≤ 1 := by
    rw [abs_le]
    constructor
    · have := pair_le y hy i k h (-1) (-1) (Or.inr rfl) (Or.inr rfl)
      push_cast at this; linarith
    · exact h1
  have h6 : |y i - y k| ≤ 1 := by
    rw [abs_le]
    constructor
    · have := pair_le y hy i k h (-1) 1 (Or.inr rfl) (Or.inl rfl)
      push_cast at this; linarith
    · exact h3
  rcases le_total 0 (y i) with hi | hi <;> rcases le_total 0 (y k) with hk | hk
  · rw [abs_of_nonneg hi, abs_of_nonneg hk]
    have := (abs_le.mp h5).2; linarith
  · rw [abs_of_nonneg hi, abs_of_nonpos hk]
    have := (abs_le.mp h6).2; linarith
  · rw [abs_of_nonpos hi, abs_of_nonneg hk]
    have := (abs_le.mp h6).1; linarith
  · rw [abs_of_nonpos hi, abs_of_nonpos hk]
    have := (abs_le.mp h5).1; linarith

/-- The slack at a coordinate vertex, in coordinates: `truncSlack w y = 4/5 - s·y_i`. -/
lemma axis_slack_eq (y : Work.FoldInst.E4) {i : Fin 4} {s : ℤ} (w : Fin 24)
    (hw : Work.FoldInst.truncNormal2 w = fun r => if r = i then 2 * s else 0) :
    Work.FoldInst.truncSlack w y = 4 / 5 - (s:ℝ) * y i := by
  have hsum : ∑ r : Fin 4, (Work.FoldInst.truncNormal2 w r : ℝ) * y r = 2 * ((s:ℝ) * y i) := by
    rw [hw, sum_single_cast i (2 * s) y]
    push_cast
    ring
  simp only [Work.FoldInst.truncSlack, hsum]
  ring

/-- **The truncation constraints at `±e_i`**: `|y_i| ≤ 4/5` on `Q̄`. -/
lemma abs_coord_le {y : Work.FoldInst.E4} (hy : y ∈ Work.FoldInst.Qbar) (i : Fin 4) :
    |y i| ≤ 4 / 5 := by
  have key : ∀ w : Fin 24, 0 ≤ Work.FoldInst.truncSlack w y := fun w => hy.2 w
  rw [abs_le]
  constructor
  · obtain ⟨w, hw⟩ := exists_axis i (-1) (Or.inr rfl)
    have h := axis_slack_eq y w hw
    have := key w
    linarith
  · obtain ⟨w, hw⟩ := exists_axis i 1 (Or.inl rfl)
    have h := axis_slack_eq y w hw
    have := key w
    linarith

/-- The tightness at a diagonal vertex, in coordinates: `Σ_r (2 p_w)_r y_r = 8/5`. -/
lemma half_sum_eq {y : Work.FoldInst.E4} {w : Fin 24}
    (hw : Work.FoldInst.truncSlack w y = 0) :
    ∑ r : Fin 4, (Work.FoldInst.truncNormal2 w r : ℝ) * y r = 8 / 5 := by
  simp only [Work.FoldInst.truncSlack] at hw
  linarith

/-- **The tight coordinate vertex of a point of `Q̄`**: if `w` is a coordinate vertex and `y ∈ Q̄`
is tight at `w`, the coordinate and the cusp of `w` are determined by `y`. -/
lemma axis_tight_coord {y : Work.FoldInst.E4} {w : Fin 24}
    (hw : Work.FoldInst.truncSlack w y = 0) (h : cuspOfVert w ≠ 4) :
    ∃ i : Fin 4, |y i| = 4 / 5 ∧ cuspOfVert w = i.castSucc := by
  have h16 : 16 ≤ (w : ℕ) := by
    by_contra hh
    exact h ((cuspOfVert_eq_four_iff w).mpr (by omega))
  have hform : Work.FoldInst.truncNormal2 w
      = fun r => if r = axisIdx w then 2 * axisSign w else 0 := axis_n2_form w h16
  refine ⟨axisIdx w, ?_, cuspOfVert_axis w h16⟩
  have hs := axisSign_pm w
  have hh := axis_slack_eq y w hform
  rw [hw] at hh
  rcases hs with hs | hs
  · rw [hs] at hh; push_cast at hh
    rw [abs_of_pos (by linarith : (0:ℝ) < y (axisIdx w))]
    linarith
  · rw [hs] at hh; push_cast at hh
    rw [abs_of_neg (by linarith : y (axisIdx w) < 0)]
    linarith

/-- **The cusp of a tight truncation vertex is well defined on `Q̄`.**  Two ideal vertices whose
truncation facets meet a common point of `Q̄` lie in the same orbit of the sign-change group, i.e.
have the same cusp. -/
lemma tight_cusp {y : Work.FoldInst.E4} (hy : y ∈ Work.FoldInst.Qbar) {w w' : Fin 24}
    (hw : Work.FoldInst.truncSlack w y = 0) (hw' : Work.FoldInst.truncSlack w' y = 0) :
    cuspOfVert w = cuspOfVert w' := by
  by_contra hne
  -- a diagonal vertex and a coordinate vertex cannot both be tight
  have hcontr : ∀ {w : Fin 24}, Work.FoldInst.truncSlack w y = 0 → (w : ℕ) < 16 →
      ∀ i : Fin 4, |y i| = 4 / 5 → False := by
    intro w hwt hwlt i hi
    have hsum := half_sum_eq hwt
    have hentry : ∀ r : Fin 4, |(Work.FoldInst.truncNormal2 w r : ℝ)| = 1 := by
      intro r
      rcases half_entry_z w hwlt r with h1 | h1 <;> rw [h1] <;> norm_num
    have hb : |∑ r : Fin 4, (Work.FoldInst.truncNormal2 w r : ℝ) * y r| ≤ 7 / 5 := by
      calc |∑ r : Fin 4, (Work.FoldInst.truncNormal2 w r : ℝ) * y r|
          ≤ ∑ r : Fin 4, |(Work.FoldInst.truncNormal2 w r : ℝ) * y r| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ r : Fin 4, |y r| := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [abs_mul, hentry r, one_mul]
        _ ≤ 7 / 5 := by
            have hle : ∀ r : Fin 4, |y r| ≤ (if r = i then (4 / 5 : ℝ) else 1 / 5) := by
              intro r
              by_cases hr : r = i
              · rw [ite_eq_left hr, hr]; exact le_of_eq hi
              · rw [ite_eq_right hr]
                have hp := abs_add_le_one y hy (Ne.symm hr)
                linarith
            refine le_trans (Finset.sum_le_sum fun r _ => hle r) ?_
            fin_cases i <;> simp [Fin.sum_univ_four] <;> norm_num
    rw [hsum] at hb
    norm_num at hb
  rcases eq_or_ne (cuspOfVert w) 4 with h4 | h4
  · rcases eq_or_ne (cuspOfVert w') 4 with h4' | h4'
    · exact hne (by rw [h4, h4'])
    · obtain ⟨i, hi, -⟩ := axis_tight_coord hw' h4'
      exact hcontr hw ((cuspOfVert_eq_four_iff w).mp h4) i hi
  · rcases eq_or_ne (cuspOfVert w') 4 with h4' | h4'
    · obtain ⟨i, hi, -⟩ := axis_tight_coord hw h4
      exact hcontr hw' ((cuspOfVert_eq_four_iff w').mp h4') i hi
    · obtain ⟨i, hi, hci⟩ := axis_tight_coord hw h4
      obtain ⟨j, hj, hcj⟩ := axis_tight_coord hw' h4'
      by_cases hij : i = j
      · exact hne (by rw [hci, hcj, hij])
      · have hp := abs_add_le_one y hy hij
        rw [hi, hj] at hp
        norm_num at hp

/-! ## The disjointness of the ceiling tori -/

theorem cusp_disjoint : ∀ v v' : Fin 5, v ≠ v' →
    Disjoint (Set.range (Work.RTOwed.mbarPt v)) (Set.range (Work.RTOwed.mbarPt v')) := by
  intro v v' hne
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  rintro p ⟨h1, h2⟩
  obtain ⟨x, rfl⟩ := h1
  obtain ⟨x', hx'⟩ := h2
  -- the two ceiling points are classes of the good branch of `cuspPtX`, whose Klein points lie in
  -- `Q̄` on the truncation facets of the vertices `cubeVert (cubeOf v x)` and `cubeVert (cubeOf v' x')`
  have hq : kleinPt (cubeOf v x) (redV v x) ∈ Work.FoldInst.Qbar :=
    cube_quad.1 _ _ (redV_mem_cubeBox v x)
  have hq' : kleinPt (cubeOf v' x') (redV v' x') ∈ Work.FoldInst.Qbar :=
    cube_quad.1 _ _ (redV_mem_cubeBox v' x')
  have hcptx : cuspPtX v x = xbarOf (cubeOf v x) (kleinPt (cubeOf v x) (redV v x)) hq :=
    cuspPtX_of_mem v x hq
  have hcptx' : cuspPtX v' x' = xbarOf (cubeOf v' x') (kleinPt (cubeOf v' x') (redV v' x')) hq' :=
    cuspPtX_of_mem v' x' hq'
  have hmk : Work.FoldInst.mk (cuspPtX v' x') = Work.FoldInst.mk (cuspPtX v x) := hx'
  rw [hcptx, hcptx'] at hmk
  -- the identifying group element and the transport of the truncation facets
  obtain ⟨γ, -, hact⟩ := Quotient.exact hmk
  have hqq : Work.FoldInst.act γ.1 (kleinPt (cubeOf v' x') (redV v' x'))
      = kleinPt (cubeOf v x) (redV v x) := by
    have h1 := congrArg (fun z : CuspXbar => z.2.1) hact
    simpa [xbarOf] using h1
  have hfac : Work.FoldInst.truncSlack (cubeVert (cubeOf v x)) (kleinPt (cubeOf v x) (redV v x))
      = 0 := by
    have h := twenty_truncSlack_vert (cubeOf v x) (redV v x)
    linarith
  have hfac' : Work.FoldInst.truncSlack (Work.FoldInst.truncPerm γ.1 (cubeVert (cubeOf v' x')))
      (kleinPt (cubeOf v x) (redV v x)) = 0 := by
    have h := Work.FoldInst.truncSlack_act_aux γ.1 (cubeVert (cubeOf v' x'))
      (kleinPt (cubeOf v' x') (redV v' x'))
    rw [hqq] at h
    rw [h]
    have h2 := twenty_truncSlack_vert (cubeOf v' x') (redV v' x')
    linarith
  -- the two tight vertices have the same cusp, and the cusp label is invariant under the action
  have key := tight_cusp hq hfac' hfac
  rw [cuspOfVert_truncPerm] at key
  have hvv : v = v' := by
    have e1 : Work.Cusp.cubeCusp (cubeOf v x) = v := cubeCusp_cubeOfMod v (floorV x)
    have e2 : Work.Cusp.cubeCusp (cubeOf v' x') = v' := cubeCusp_cubeOfMod v' (floorV x')
    have e3 : Work.Cusp.cubeCusp (cubeOf v x) = cuspOfVert (cubeVert (cubeOf v x)) :=
      cubeCusp_cuspOfVert (cubeOf v x)
    have e4 : Work.Cusp.cubeCusp (cubeOf v' x') = cuspOfVert (cubeVert (cubeOf v' x')) :=
      cubeCusp_cuspOfVert (cubeOf v' x')
    rw [← e1, e3, ← key, ← e4, e2]
  exact hne hvv

end Work.RTOwed.cuspCert
