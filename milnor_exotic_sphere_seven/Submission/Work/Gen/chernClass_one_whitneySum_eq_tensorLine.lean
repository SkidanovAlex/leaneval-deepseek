import Mathlib
import Submission.Work.Gen.LineTensor
import Submission.Work.Whitney.Basic
import Submission.Work.Gen.tautQuotient_line_tensor
import Submission.Work.Thom.chernClass_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
# The determinant trick at rank `2`: `c₁(L ⊕ M) = c₁(L ⊗ M)`

For two complex line bundles `L`, `M` over a base `B`, the tautological quotient
`Q = π^*(L ⊕ M)/ℂ·s` over the punctured total space `X = (L ⊕ M)∖0` is canonically isomorphic to
the pullback `π^*(L ⊗ M)`, via the fibrewise *wedge* `v ↦ v ∧ s` with the tautological section `s`
(this is `Submission/Work/Gen/tautQuotient_line_tensor.lean`, whose scaffolding is imported here).

Combining that isomorphism with

* isomorphism-invariance of the Chern classes (`Work.Thom.chernClass_BundleIso`),
* naturality of the Chern classes under pullback (`Work.Thom.chernClass_comap`), and
* the descent equation `c_j(L ⊕ M) = (π^*)^{-1} c_j(Q)` (`Work.Thom.chernClass_succ_of_le`),

gives the **determinant trick at rank `2`**:

`c₁(L ⊕ M) = c₁(π^{*,-1}(Q)) = c₁(L ⊗ M)`.

The isomorphism is built here from scratch (`Work.Gen.tautQuotient_tensorLine_iso`) because the
scaffolded module states it but does not prove it; the fibrewise map is the wedge `wedgeCLM`, read
in the natural charts of `Q` and of the tensor pullback, and the content of the construction is

* `wedge_core_scalar`: the *chart-independence* of the wedge — the composite
  `Z.coordChange · i ∘ wedge ∘ Q.coordChange i ·` is the fixed-chart expression `chartWedge`,
  which is the statement that `v ↦ v ∧ s` is well defined on the quotient;
* `wedge_inv_scalar`: the same for the inverse `(wedgeScalar)⁻¹ • id`;
* continuity of both, through `Work.Thom.continuous_totalSpaceMap_clm`.
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

/-! ## The scalar of a scalar endomorphism of `ℂ¹`, and the two signs -/

/-- Two endomorphisms of `ℂ¹` with the same scalar are equal. -/
theorem eq_of_scl_eq {f g : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)}
    (h : scl f = scl g) : f = g := by
  rw [scl_smul_id f, scl_smul_id g, h]

/-- The scalar of `wedgeCLM` is `wedgeScalar`. -/
theorem scl_wedgeCLM (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) (y : lmPunct L M) :
    scl (wedgeCLM L M y) = wedgeScalar L M y :=
  scl_smul_id_eq _

/-- The scalar of `chartWedge` is `chartWedgeScalar`. -/
theorem scl_chartWedge (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) (i : ι₁ × ι₂) (k : Fin 2)
    (y : lmPunct L M) :
    scl (chartWedge L M i k y) = chartWedgeScalar L M i k y :=
  scl_smul_id_eq _

/-- The sign of the wedge in the `k`-th model chart of a rank-`2` fibre: `-1` for `k = 0`,
`+1` for `k = 1`. -/
def wsign (k : Fin 2) : ℂ := if k = 0 then -1 else 1

theorem wsign_ne_zero (k : Fin 2) : wsign k ≠ 0 := by
  rw [wsign]; split <;> norm_num

theorem wsign_zero : wsign (0 : Fin 2) = -1 := rfl

theorem wsign_one : wsign (1 : Fin 2) = 1 := by rw [wsign]; simp

/-! ## The bilinear form `wedge2` -/

theorem oneVec_ofLp_zero : (oneVec : EuclideanSpace ℂ (Fin 1)).ofLp 0 = 1 := rfl

theorem wedge2_add_left (u u' w : EuclideanSpace ℂ (Fin 2)) :
    wedge2 (u + u') w = wedge2 u w + wedge2 u' w := by
  rw [wedge2, wedge2, wedge2]
  simp only [WithLp.ofLp_add, Pi.add_apply]
  ring

theorem wedge2_smul_left (c : ℂ) (u w : EuclideanSpace ℂ (Fin 2)) :
    wedge2 (c • u) w = c * wedge2 u w := by
  rw [wedge2, wedge2]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem wedge2_self (w : EuclideanSpace ℂ (Fin 2)) : wedge2 w w = 0 := by
  rw [wedge2]; ring

/-- The wedge is unchanged by adding a multiple of its second argument to the first: this is the
algebraic content of "the map `v ↦ v ∧ w` kills the line `ℂ·w`". -/
theorem wedge2_eq_of_sub_smul (u v w : EuclideanSpace ℂ (Fin 2)) (c : ℂ)
    (h : u - v = c • w) : wedge2 u w = wedge2 v w := by
  have h' : u = v + c • w := sub_eq_iff_eq_add'.mp h
  rw [h', wedge2_add_left, wedge2_smul_left, wedge2_self, mul_zero, add_zero]

/-- **The wedge in the `k`-th model chart**: `fillFun k z ∧ w = ± z₀ w_k`. -/
theorem wedge2_fillFun (k : Fin 2) (z : EuclideanSpace ℂ (Fin 1))
    (w : EuclideanSpace ℂ (Fin 2)) :
    wedge2 (fillFun k z) w = wsign k * z.ofLp 0 * w.ofLp k := by
  have hsab : ∀ m : Fin 1, (0 : Fin 2).succAbove m = 1 := by intro m; fin_cases m; decide
  have hsab1 : ∀ m : Fin 1, (1 : Fin 2).succAbove m = 0 := by intro m; fin_cases m; decide
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    rw [wedge2, fillFun_apply_self, zero_mul, zero_sub, wsign_zero]
    have h1 : (fillFun (0 : Fin 2) z).ofLp 1 = z.ofLp 0 := by
      have h := fillFun_apply_succAbove (0 : Fin 2) z (0 : Fin 1)
      rwa [hsab 0] at h
    rw [h1]; ring
  · have hk1 : k = 1 := Fin.eq_one_of_ne_zero k hk
    subst hk1
    rw [wedge2, fillFun_apply_self, zero_mul, sub_zero, wsign_one]
    have h1 : (fillFun (1 : Fin 2) z).ofLp 0 = z.ofLp 0 := by
      have h := fillFun_apply_succAbove (1 : Fin 2) z (0 : Fin 1)
      rwa [hsab1 0] at h
    rw [h1]; ring

/-! ## The charts of `L ⊕ M` at a punctured point

Throughout, `L`, `M` are complex line bundles over `B` and `y` is a point of the punctured total
space `X = (L ⊕ M)∖0`; `W = L ⊕ M` is the rank-`2` bundle, `Q` its tautological quotient and
`Z = π^*(L ⊗ M)` the pullback of the tensor product to `X`. -/

section Data

variable (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
  (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂)

/-- The base point of a punctured point of `L ⊕ M`. -/
abbrev lmPt (y : lmPunct L M) : B := (y : (realification (lmSum L M)).TotalSpace).proj

/-- The `W`-chart coordinate of a punctured point, read in the chart of `W = L ⊕ M` with
index `i`.  This is `chartCoord` with the `localTriv` of the realification replaced by the
`localTriv` of `W` itself. -/
abbrev lwFix (i : ι₁ × ι₂) (y : lmPunct L M) : EuclideanSpace ℂ (Fin 2) :=
  (VectorBundleCore.localTriv (lmSum L M) i (y : (realification (lmSum L M)).TotalSpace)).2

theorem chartCoord_eq_lwFix (i : ι₁ × ι₂) (y : lmPunct L M) :
    chartCoord L M i y = lwFix L M i y := by
  rw [chartCoord]
  exact localTriv_snd_eq (lmSum L M) i _

/-- The second component of the natural index of the tautological quotient is the chosen
non-vanishing coordinate of the tautological section. -/
theorem qidx_snd (y : lmPunct L M) :
    ((lmQuot L M).indexAt y).2 = tqCoord (lmSum L M) y := by
  rw [show lmQuot L M = tautQuotientCore (lmSum L M) from rfl, tautQuotientCore_indexAt]

/-- The first component of the natural index of the tautological quotient is the natural index
of `W`. -/
theorem qidx_fst (y : lmPunct L M) :
    ((lmQuot L M).indexAt y).1 = (lmSum L M).indexAt (lmPt L M y) := by
  rw [show lmQuot L M = tautQuotientCore (lmSum L M) from rfl, tautQuotientCore_indexAt]

/-- The natural chart coordinate of the tautological section is non-vanishing at `tqCoord`. -/
theorem lwNat_ne_zero (y : lmPunct L M) :
    (lwFix L M ((lmSum L M).indexAt (lmPt L M y)) y).ofLp
      ((lmQuot L M).indexAt y).2 ≠ 0 := by
  rw [qidx_snd]
  exact tqCoord_spec (lmSum L M) y

/-- `wedgeSign` is the sign `wsign` at the natural index of the quotient. -/
theorem wedgeSign_eq (y : lmPunct L M) :
    wedgeSign L M y = wsign ((lmQuot L M).indexAt y).2 := by
  rw [qidx_snd, wedgeSign, wsign]
  rcases eq_or_ne (tqCoord (lmSum L M) y) 0 with h | h
  · rw [h]; norm_num
  · rw [Fin.eq_one_of_ne_zero _ h]; norm_num

/-- `wedgeCoeff` is the natural chart coordinate of the tautological section at `tqCoord`. -/
theorem wedgeCoeff_eq (y : lmPunct L M) :
    wedgeCoeff L M y
      = (chartCoord L M ((lmSum L M).indexAt (lmPt L M y)) y).ofLp
          ((lmQuot L M).indexAt y).2 := by
  rw [qidx_snd]
  rfl

/-- **The scalar of the wedge map, in terms of the natural chart**: `wedgeScalar` is the signed
`tqCoord`-th coordinate of the tautological section in the natural chart of `W`. -/
theorem wedgeScalar_eq_wnat (y : lmPunct L M) :
    scl (wedgeCLM L M y)
      = wsign ((lmQuot L M).indexAt y).2
        * (chartCoord L M ((lmSum L M).indexAt (lmPt L M y)) y).ofLp
            ((lmQuot L M).indexAt y).2 := by
  rw [scl_wedgeCLM, wedgeScalar, wedgeSign_eq L M y, wedgeCoeff_eq L M y]

/-- **The scalar of `chartWedge` in the fixed chart `i`**: it is the signed `k`-th coordinate of
the tautological section in that chart. -/
theorem chartWedgeScalar_eq (i : ι₁ × ι₂) (k : Fin 2) (y : lmPunct L M) :
    scl (chartWedge L M i k y)
      = wsign k * (lwFix L M i y).ofLp k := by
  rw [scl_chartWedge, chartWedgeScalar]
  simp only [chartCoord_eq_lwFix L M i y]
  have hsab : ∀ m : Fin 1, (0 : Fin 2).succAbove m = 1 := by intro m; fin_cases m; decide
  have hsab1 : ∀ m : Fin 1, (1 : Fin 2).succAbove m = 0 := by intro m; fin_cases m; decide
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    have h1 : (fillFun (0 : Fin 2) oneVec).ofLp 1 = 1 := by
      have h := fillFun_apply_succAbove (0 : Fin 2) oneVec (0 : Fin 1)
      rw [hsab 0] at h
      rw [h, oneVec_ofLp_zero]
    rw [wsign_zero, fillFun_apply_self, h1]
    ring
  · have hk1 : k = 1 := Fin.eq_one_of_ne_zero k hk
    subst hk1
    have h1 : (fillFun (1 : Fin 2) oneVec).ofLp 0 = 1 := by
      have h := fillFun_apply_succAbove (1 : Fin 2) oneVec (0 : Fin 1)
      rw [hsab1 0] at h
      rw [h, oneVec_ofLp_zero]
    rw [wsign_one, fillFun_apply_self, h1]
    ring

/-- **The natural coordinate of the tautological section is the image of the fixed one** under the
transition function of `W`. -/
theorem lwNat_eq_coordChange (i : ι₁ × ι₂) (y : lmPunct L M)
    (hy : lmPt L M y ∈ (lmSum L M).baseSet i) :
    (lmSum L M).coordChange i ((lmSum L M).indexAt (lmPt L M y)) (lmPt L M y) (lwFix L M i y)
      = lwFix L M ((lmSum L M).indexAt (lmPt L M y)) y :=
  coordChange_localTriv_snd (lmSum L M) i ((lmSum L M).indexAt (lmPt L M y)) _
    hy ((lmSum L M).mem_baseSet_at _)

/-- Membership in the base set of the tautological quotient, read on the first component. -/
theorem mem_baseSet_fst (i : ι₁ × ι₂) (k : Fin 2) (y : lmPunct L M)
    (hy : y ∈ (lmQuot L M).baseSet (i, k)) :
    lmPt L M y ∈ (lmSum L M).baseSet i := by
  have h := hy
  rw [show lmQuot L M = tautQuotient (m := 1) (lmSum L M) from rfl, tautQuotient_baseSet] at h
  exact h.1

/-- The scalar of the tautological quotient's transition, in the natural charts: this is the
`quoFun` of the fixed-chart lift, and it is definitional. -/
theorem scl_tautQuotient_coordChange (i : ι₁ × ι₂) (k : Fin 2) (y : lmPunct L M) :
    scl ((lmQuot L M).coordChange (i, k) ((lmQuot L M).indexAt y) y)
      = (quoFun (((lmQuot L M).indexAt y).2)
          (lwFix L M ((lmSum L M).indexAt (lmPt L M y)) y)
          (((lmSum L M).coordChange i ((lmSum L M).indexAt (lmPt L M y)) (lmPt L M y))
            (fillFun k oneVec))).ofLp 0 := by
  have hidx : (lmQuot L M).indexAt y
      = ((lmSum L M).indexAt (lmPt L M y), ((lmQuot L M).indexAt y).2) :=
    Prod.ext (qidx_fst L M y) rfl
  show (((lmQuot L M).coordChange (i, k) ((lmQuot L M).indexAt y) y) oneVec).ofLp 0 = _
  rw [hidx]
  rw [show lmQuot L M = Work.Thom.tautQuotient (m := 1) (lmSum L M) from rfl,
    tautQuotient_coordChange]

/-- **The key scalar identity of the determinant trick**: the natural-chart wedge scalar times the
coordinate of the tautological quotient's transition is the determinant `a b` of the transition of
`W = L ⊕ M` times the fixed-chart wedge scalar.

Equivalently: the wedge `v ↦ v ∧ s` is chart-independent. -/
theorem wedge_key_scalar (i : ι₁ × ι₂) (k : Fin 2) (y : lmPunct L M)
    (hy : y ∈ (lmQuot L M).baseSet (i, k)) :
    scl (wedgeCLM L M y) * scl ((lmQuot L M).coordChange (i, k) ((lmQuot L M).indexAt y) y)
      = scl (L.coordChange i.1 ((lmSum L M).indexAt (lmPt L M y)).1 (lmPt L M y))
        * scl (M.coordChange i.2 ((lmSum L M).indexAt (lmPt L M y)).2 (lmPt L M y))
        * scl (chartWedge L M i k y) := by
  have hxi := mem_baseSet_fst L M i k y hy
  have hwn := lwNat_eq_coordChange L M i y hxi
  have hc0 : (lwFix L M ((lmSum L M).indexAt (lmPt L M y)) y).ofLp 0
      = scl (L.coordChange i.1 ((lmSum L M).indexAt (lmPt L M y)).1 (lmPt L M y))
        * (lwFix L M i y).ofLp 0 := by
    rw [← hwn,
      whitneySum_coordChange_apply_zero L M i ((lmSum L M).indexAt (lmPt L M y)) (lmPt L M y)]
  have hc1 : (lwFix L M ((lmSum L M).indexAt (lmPt L M y)) y).ofLp 1
      = scl (M.coordChange i.2 ((lmSum L M).indexAt (lmPt L M y)).2 (lmPt L M y))
        * (lwFix L M i y).ofLp 1 := by
    rw [← hwn,
      whitneySum_coordChange_apply_one L M i ((lmSum L M).indexAt (lmPt L M y)) (lmPt L M y)]
  have hqc := scl_tautQuotient_coordChange L M i k y
  have hne := lwNat_ne_zero L M y
  have hA : wedge2 (((lmSum L M).coordChange i ((lmSum L M).indexAt (lmPt L M y))
        (lmPt L M y)) (fillFun k oneVec))
        (lwFix L M ((lmSum L M).indexAt (lmPt L M y)) y)
      = scl (wedgeCLM L M y) * scl ((lmQuot L M).coordChange (i, k) ((lmQuot L M).indexAt y) y) := by
    have hsub := sub_fillFun_quoFun (((lmQuot L M).indexAt y).2)
      (lwFix L M ((lmSum L M).indexAt (lmPt L M y)) y)
      (((lmSum L M).coordChange i ((lmSum L M).indexAt (lmPt L M y)) (lmPt L M y))
        (fillFun k oneVec)) hne
    rw [wedge2_eq_of_sub_smul _ _ _ _ hsub, wedge2_fillFun]
    rw [← hqc, wedgeScalar_eq_wnat L M y,
      chartCoord_eq_lwFix L M ((lmSum L M).indexAt (lmPt L M y)) y]
    ring
  have hB : wedge2 (((lmSum L M).coordChange i ((lmSum L M).indexAt (lmPt L M y))
        (lmPt L M y)) (fillFun k oneVec))
        (lwFix L M ((lmSum L M).indexAt (lmPt L M y)) y)
      = scl (L.coordChange i.1 ((lmSum L M).indexAt (lmPt L M y)).1 (lmPt L M y))
        * scl (M.coordChange i.2 ((lmSum L M).indexAt (lmPt L M y)).2 (lmPt L M y))
        * scl (chartWedge L M i k y) := by
    have hc0' : (((lmSum L M).coordChange i ((lmSum L M).indexAt (lmPt L M y))
        (lmPt L M y)) (lwFix L M i y)).ofLp 0
        = scl (L.coordChange i.1 ((lmSum L M).indexAt (lmPt L M y)).1 (lmPt L M y))
          * (lwFix L M i y).ofLp 0 := by
      rw [hwn, hc0]
    have hc1' : (((lmSum L M).coordChange i ((lmSum L M).indexAt (lmPt L M y))
        (lmPt L M y)) (lwFix L M i y)).ofLp 1
        = scl (M.coordChange i.2 ((lmSum L M).indexAt (lmPt L M y)).2 (lmPt L M y))
          * (lwFix L M i y).ofLp 1 := by
      rw [hwn, hc1]
    have hu0 := whitneySum_coordChange_apply_zero L M i ((lmSum L M).indexAt (lmPt L M y))
      (lmPt L M y) (fillFun k oneVec)
    have hu1 := whitneySum_coordChange_apply_one L M i ((lmSum L M).indexAt (lmPt L M y))
      (lmPt L M y) (fillFun k oneVec)
    rw [← hwn, wedge2_diag hu0 hu1 hc0' hc1', wedge2_fillFun, oneVec_ofLp_zero]
    rw [mul_one, ← chartWedgeScalar_eq L M i k y]
  exact hA.symm.trans hB

/-- The scalar cocycle for a complex line bundle: the two transition scalars of a pair of charts
are reciprocal on the overlap. -/
theorem scl_cc_mul_scl_cc {ι : Type} {B : Type} [TopologicalSpace B]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (i j : ι) (x : B)
    (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) :
    scl (Z.coordChange j i x) * scl (Z.coordChange i j x) = 1 := by
  have h := scl_coordChange_comp (Z := Z) i j i x ⟨⟨hi, hj⟩, hi⟩
  have hself : scl (Z.coordChange i i x) = 1 := by
    have hid : Z.coordChange i i x = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
      apply ContinuousLinearMap.ext
      intro v
      exact Z.coordChange_self i x hi v
    rw [hid, scl_id]
  rw [hself] at h
  rw [mul_comm (scl (Z.coordChange j i x)) (scl (Z.coordChange i j x)), ← h]

/-- The scalar of the transition of the pullback of the tensor product, in the natural charts. -/
theorem scl_tens_coordChange (i : ι₁ × ι₂) (y : lmPunct L M) :
    scl ((lmTens L M).coordChange ((lmTens L M).indexAt y) i y)
      = scl (L.coordChange ((lmSum L M).indexAt (lmPt L M y)).1 i.1 (lmPt L M y))
        * scl (M.coordChange ((lmSum L M).indexAt (lmPt L M y)).2 i.2 (lmPt L M y)) := by
  show scl ((tensorLine L M).coordChange ((tensorLine L M).indexAt ((lmProj L M) y)) i
    ((lmProj L M) y)) = _
  rw [tensorLine_coordChange, scl_smul_id_eq,
    show (tensorLine L M).indexAt ((lmProj L M) y) = (lmSum L M).indexAt (lmPt L M y) from
      (Work.Whitney.whitneySum_indexAt L M (lmPt L M y)).symm,
    show (lmProj L M) y = lmPt L M y from rfl]

/-- **Chart-independence of the wedge**: the natural-chart fibrewise wedge map, read in the fixed
chart `(i,k)` of the tautological quotient and the fixed chart `i` of `W = L ⊕ M`, is `chartWedge`.
This is the statement that `v ↦ v ∧ s` descends to the quotient `Q = π^*(L ⊕ M)/ℂ·s`. -/
theorem wedge_core (i : ι₁ × ι₂) (k : Fin 2) (y : lmPunct L M)
    (hy : y ∈ (lmQuot L M).baseSet (i, k)) :
    (lmTens L M).coordChange ((lmTens L M).indexAt y) i y ∘SL
      (wedgeCLM L M y ∘SL (lmQuot L M).coordChange (i, k) ((lmQuot L M).indexAt y) y)
      = chartWedge L M i k y := by
  have hxi := mem_baseSet_fst L M i k y hy
  have hxiL : lmPt L M y ∈ L.baseSet i.1 := by
    have h := hxi
    rw [show lmSum L M = Work.Whitney.whitneySum (m₁ := 1) (m₂ := 1) L M from rfl,
      Work.Whitney.whitneySum_baseSet] at h
    exact h.1
  have hxiM : lmPt L M y ∈ M.baseSet i.2 := by
    have h := hxi
    rw [show lmSum L M = Work.Whitney.whitneySum (m₁ := 1) (m₂ := 1) L M from rfl,
      Work.Whitney.whitneySum_baseSet] at h
    exact h.2
  have hzc : scl ((lmTens L M).coordChange ((lmTens L M).indexAt y) i y)
      * (scl (L.coordChange i.1 ((lmSum L M).indexAt (lmPt L M y)).1 (lmPt L M y))
        * scl (M.coordChange i.2 ((lmSum L M).indexAt (lmPt L M y)).2 (lmPt L M y))) = 1 := by
    rw [scl_tens_coordChange L M i y]
    have hL := scl_cc_mul_scl_cc L i.1 ((lmSum L M).indexAt (lmPt L M y)).1 (lmPt L M y) hxiL
      (L.mem_baseSet_at _)
    have hM := scl_cc_mul_scl_cc M i.2 ((lmSum L M).indexAt (lmPt L M y)).2 (lmPt L M y) hxiM
      (M.mem_baseSet_at _)
    calc scl (L.coordChange ((lmSum L M).indexAt (lmPt L M y)).1 i.1 (lmPt L M y))
            * scl (M.coordChange ((lmSum L M).indexAt (lmPt L M y)).2 i.2 (lmPt L M y))
            * (scl (L.coordChange i.1 ((lmSum L M).indexAt (lmPt L M y)).1 (lmPt L M y))
              * scl (M.coordChange i.2 ((lmSum L M).indexAt (lmPt L M y)).2 (lmPt L M y)))
        = (scl (L.coordChange ((lmSum L M).indexAt (lmPt L M y)).1 i.1 (lmPt L M y))
              * scl (L.coordChange i.1 ((lmSum L M).indexAt (lmPt L M y)).1 (lmPt L M y)))
            * (scl (M.coordChange ((lmSum L M).indexAt (lmPt L M y)).2 i.2 (lmPt L M y))
              * scl (M.coordChange i.2 ((lmSum L M).indexAt (lmPt L M y)).2 (lmPt L M y))) := by
          ring
      _ = 1 := by rw [hL, hM, mul_one]
  have hscalar : scl ((lmTens L M).coordChange ((lmTens L M).indexAt y) i y
        ∘SL (wedgeCLM L M y ∘SL (lmQuot L M).coordChange (i, k) ((lmQuot L M).indexAt y) y))
      = scl (chartWedge L M i k y) := by
    rw [scl_comp, scl_comp, wedge_key_scalar L M i k y hy, ← mul_assoc, hzc, one_mul]
  rw [scl_smul_id ((lmTens L M).coordChange ((lmTens L M).indexAt y) i y
      ∘SL (wedgeCLM L M y ∘SL (lmQuot L M).coordChange (i, k) ((lmQuot L M).indexAt y) y)),
    scl_smul_id (chartWedge L M i k y), hscalar]

/-- The wedge scalar of the natural chart is non-zero at a punctured point. -/
theorem wedgeScalar_ne_zero (y : lmPunct L M) : wedgeScalar L M y ≠ 0 := by
  rw [wedgeScalar]
  refine mul_ne_zero ?_ ?_
  · rw [wedgeSign_eq L M y]; exact wsign_ne_zero _
  · rw [wedgeCoeff_eq L M y,
      chartCoord_eq_lwFix L M ((lmSum L M).indexAt (lmPt L M y)) y]
    exact lwNat_ne_zero L M y

/-- The fixed-chart wedge scalar is non-zero on the base set of the tautological quotient. -/
theorem chartWedgeScalar_ne_zero (i : ι₁ × ι₂) (k : Fin 2) (y : lmPunct L M)
    (hy : y ∈ (lmQuot L M).baseSet (i, k)) : chartWedgeScalar L M i k y ≠ 0 := by
  have h := hy
  rw [show lmQuot L M = tautQuotient (m := 1) (lmSum L M) from rfl, tautQuotient_baseSet] at h
  rw [← scl_chartWedge L M i k y, chartWedgeScalar_eq L M i k y]
  exact mul_ne_zero (wsign_ne_zero k) h.2

/-- The determinant of the transition of `W = L ⊕ M` is the product of the two line bundles'
transition scalars, and it is the reciprocal of the scalar of the tensor line's transition. -/
theorem scl_tens_recip (i : ι₁ × ι₂) (y : lmPunct L M)
    (hy : lmPt L M y ∈ (lmSum L M).baseSet i) :
    scl ((lmTens L M).coordChange ((lmTens L M).indexAt y) i y)
      * (scl (L.coordChange i.1 ((lmSum L M).indexAt (lmPt L M y)).1 (lmPt L M y))
        * scl (M.coordChange i.2 ((lmSum L M).indexAt (lmPt L M y)).2 (lmPt L M y))) = 1 := by
  have hL : lmPt L M y ∈ L.baseSet i.1 := by
    have h := hy
    rw [show lmSum L M = Work.Whitney.whitneySum (m₁ := 1) (m₂ := 1) L M from rfl,
      Work.Whitney.whitneySum_baseSet] at h
    exact h.1
  have hM : lmPt L M y ∈ M.baseSet i.2 := by
    have h := hy
    rw [show lmSum L M = Work.Whitney.whitneySum (m₁ := 1) (m₂ := 1) L M from rfl,
      Work.Whitney.whitneySum_baseSet] at h
    exact h.2
  rw [scl_tens_coordChange L M i y]
  have h1 := scl_cc_mul_scl_cc L i.1 ((lmSum L M).indexAt (lmPt L M y)).1 (lmPt L M y) hL
    (L.mem_baseSet_at _)
  have h2 := scl_cc_mul_scl_cc M i.2 ((lmSum L M).indexAt (lmPt L M y)).2 (lmPt L M y) hM
    (M.mem_baseSet_at _)
  calc scl (L.coordChange ((lmSum L M).indexAt (lmPt L M y)).1 i.1 (lmPt L M y))
          * scl (M.coordChange ((lmSum L M).indexAt (lmPt L M y)).2 i.2 (lmPt L M y))
          * (scl (L.coordChange i.1 ((lmSum L M).indexAt (lmPt L M y)).1 (lmPt L M y))
            * scl (M.coordChange i.2 ((lmSum L M).indexAt (lmPt L M y)).2 (lmPt L M y)))
      = (scl (L.coordChange ((lmSum L M).indexAt (lmPt L M y)).1 i.1 (lmPt L M y))
            * scl (L.coordChange i.1 ((lmSum L M).indexAt (lmPt L M y)).1 (lmPt L M y)))
          * (scl (M.coordChange ((lmSum L M).indexAt (lmPt L M y)).2 i.2 (lmPt L M y))
            * scl (M.coordChange i.2 ((lmSum L M).indexAt (lmPt L M y)).2 (lmPt L M y))) := by
        ring
    _ = 1 := by rw [h1, h2, mul_one]

/-- **The abstract algebra of the inverse chart computation**: from the wedge relation
`w * qcN = ab * h`, the reciprocity `zcJ * ab = 1` and the quotient's cocycle `qcS * qcN = 1`, the
inverse wedge transforms by `h⁻¹ zcJ`. -/
theorem inv_scalar_algebra {w qcN qcS ab h zcI zcJ zcC : ℂ} (hqcN : qcN ≠ 0)
    (hkey : w * qcN = ab * h) (hz : zcJ * ab = 1) (hq : qcS * qcN = 1)
    (hc : zcC = zcJ * zcI) :
    h⁻¹ * zcC = qcS * (w⁻¹ * zcI) := by
  have hwinv : w⁻¹ = qcN * zcJ * h⁻¹ := by
    have hw' : w = ab * h * qcN⁻¹ := by
      rw [← hkey, mul_assoc, mul_inv_cancel₀ hqcN, mul_one]
    rw [hw', mul_inv_rev, mul_inv_rev, inv_inv, inv_eq_of_mul_eq_one_left hz]
    ring
  have hqinv : qcS = qcN⁻¹ := eq_inv_of_mul_eq_one_left hq
  rw [hwinv, hqinv, hc]
  field_simp

/-- **Chart-independence of the inverse wedge**: the inverse of the natural-chart wedge map, read
in the fixed charts, is the reciprocal of the fixed-chart wedge composed with a transition of
`Z = π^*(L ⊗ M)`. -/
theorem wedge_inv_core (i₁ : ι₁ × ι₂) (i₂ : (ι₁ × ι₂) × Fin 2) (y : lmPunct L M)
    (hy : y ∈ (lmTens L M).baseSet i₁ ∩ (lmQuot L M).baseSet i₂) :
    (lmQuot L M).coordChange ((lmQuot L M).indexAt y) i₂ y ∘SL
      ((wedgeScalar L M y)⁻¹ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) ∘SL
        (lmTens L M).coordChange i₁ ((lmTens L M).indexAt y) y)
      = ((chartWedgeScalar L M i₂.1 i₂.2 y)⁻¹
          * scl ((lmTens L M).coordChange i₁ i₂.1 y)) •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
  have hyZ : y ∈ (lmTens L M).baseSet i₂.1 := baseSet_subset_tensSet L M i₂ hy.2
  have hyW : lmPt L M y ∈ (lmSum L M).baseSet i₂.1 := by
    have h := hy.2
    rw [show lmQuot L M = tautQuotient (m := 1) (lmSum L M) from rfl,
      tautQuotient_baseSet] at h
    exact h.1
  have hq : scl ((lmQuot L M).coordChange ((lmQuot L M).indexAt y) i₂ y)
      * scl ((lmQuot L M).coordChange i₂ ((lmQuot L M).indexAt y) y) = 1 :=
    scl_cc_mul_scl_cc (lmQuot L M) i₂ ((lmQuot L M).indexAt y) y hy.2
      ((lmQuot L M).mem_baseSet_at y)
  have hc : scl ((lmTens L M).coordChange i₁ i₂.1 y)
      = scl ((lmTens L M).coordChange ((lmTens L M).indexAt y) i₂.1 y)
        * scl ((lmTens L M).coordChange i₁ ((lmTens L M).indexAt y) y) := by
    rw [scl_coordChange_comp (Z := lmTens L M) i₁ ((lmTens L M).indexAt y) i₂.1 y
      ⟨⟨hy.1, (lmTens L M).mem_baseSet_at y⟩, hyZ⟩]
    ring
  have hscalar : scl ((lmQuot L M).coordChange ((lmQuot L M).indexAt y) i₂ y
        ∘SL (((wedgeScalar L M y)⁻¹ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
          ∘SL (lmTens L M).coordChange i₁ ((lmTens L M).indexAt y) y))
      = scl (((chartWedgeScalar L M i₂.1 i₂.2 y)⁻¹
          * scl ((lmTens L M).coordChange i₁ i₂.1 y)) •
          ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) := by
    rw [scl_comp, scl_comp, scl_smul_id_eq, scl_smul_id_eq, ← scl_wedgeCLM L M y,
      ← scl_chartWedge L M i₂.1 i₂.2 y]
    exact (inv_scalar_algebra (w := scl (wedgeCLM L M y)) (hqcN := by
        have h0 : scl ((lmQuot L M).coordChange i₂ ((lmQuot L M).indexAt y) y)
            * scl ((lmQuot L M).coordChange ((lmQuot L M).indexAt y) i₂ y) = 1 :=
          scl_cc_mul_scl_cc (lmQuot L M) ((lmQuot L M).indexAt y) i₂ y
            ((lmQuot L M).mem_baseSet_at y) hy.2
        intro hcon
        rw [hcon, zero_mul] at h0
        exact one_ne_zero h0.symm)
      (wedge_key_scalar L M i₂.1 i₂.2 y hy.2)
      (scl_tens_recip L M i₂.1 y hyW) hq hc).symm
  exact eq_of_scl_eq hscalar

/-- **Continuity of the natural-chart wedge composite**: the content is that the natural-chart
formula agrees with the fixed-chart one (`wedge_core`), whose continuity is
`continuousOn_fixedChart`. -/
theorem continuousOn_wedge_nat (i₁ : (ι₁ × ι₂) × Fin 2) (i₂ : ι₁ × ι₂) :
    ContinuousOn (fun y : lmPunct L M =>
      (lmTens L M).coordChange ((lmTens L M).indexAt y) i₂ y ∘SL wedgeCLM L M y
        ∘SL (lmQuot L M).coordChange i₁ ((lmQuot L M).indexAt y) y)
      ((lmQuot L M).baseSet i₁ ∩ (lmTens L M).baseSet i₂) := by
  refine (continuousOn_fixedChart L M i₁ i₂).congr ?_
  intro y hy
  exact overlap_identity_of_core L M i₁ i₂ y hy
    (wedge_core L M i₁.1 i₁.2 y hy.1)

/-- Continuity of the fixed-chart expression for the **inverse** wedge: `h⁻¹` times a transition of
`Z = π^*(L ⊗ M)`. -/
theorem continuousOn_wedgeInv_fixed (i₁ : ι₁ × ι₂) (i₂ : (ι₁ × ι₂) × Fin 2) :
    ContinuousOn (fun y : lmPunct L M =>
      ((chartWedgeScalar L M i₂.1 i₂.2 y)⁻¹ * scl ((lmTens L M).coordChange i₁ i₂.1 y)) •
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
      ((lmTens L M).baseSet i₁ ∩ (lmQuot L M).baseSet i₂) := by
  have h1 : ContinuousOn (fun y : lmPunct L M => (chartWedgeScalar L M i₂.1 i₂.2 y)⁻¹)
      ((lmTens L M).baseSet i₁ ∩ (lmQuot L M).baseSet i₂) :=
    ((continuousOn_chartWedgeScalar L M i₂.1 i₂.2).mono
        (fun y hy => baseSet_subset_chartSet L M i₂ hy.2)).inv₀
      (fun y hy => chartWedgeScalar_ne_zero L M i₂.1 i₂.2 y hy.2)
  have h2 : ContinuousOn (fun y : lmPunct L M => scl ((lmTens L M).coordChange i₁ i₂.1 y))
      ((lmTens L M).baseSet i₁ ∩ (lmQuot L M).baseSet i₂) :=
    (continuous_scl.comp_continuousOn ((lmTens L M).continuousOn_coordChange i₁ i₂.1)).mono
      (fun y hy => ⟨hy.1, baseSet_subset_tensSet L M i₂ hy.2⟩)
  exact (h1.mul h2).smul continuousOn_const

/-- **Continuity of the natural-chart inverse wedge composite**. -/
theorem continuousOn_wedgeInv_nat (i₁ : ι₁ × ι₂) (i₂ : (ι₁ × ι₂) × Fin 2) :
    ContinuousOn (fun y : lmPunct L M =>
      (lmQuot L M).coordChange ((lmQuot L M).indexAt y) i₂ y ∘SL
        ((wedgeScalar L M y)⁻¹ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
          ∘SL (lmTens L M).coordChange i₁ ((lmTens L M).indexAt y) y)
      ((lmTens L M).baseSet i₁ ∩ (lmQuot L M).baseSet i₂) := by
  refine (continuousOn_wedgeInv_fixed L M i₁ i₂).congr ?_
  intro y hy
  exact wedge_inv_core L M i₁ i₂ y hy

/-- **The determinant trick (bundles)**: the tautological quotient of the rank-`2` bundle
`L ⊕ M` over its punctured total space is canonically isomorphic to the pullback of the tensor
product `L ⊗ M`, via the fibrewise wedge `v ↦ v ∧ s`. -/
theorem tautQuotient_tensorLine_iso :
    Nonempty (BundleIso (lmQuot L M) (lmTens L M)) := by
  refine ⟨{
    hom := fun y => (wedgeCLM L M y).toLinearMap
    inv := fun y =>
      (((wedgeScalar L M y)⁻¹ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))).toLinearMap
    left_inv := ?_
    right_inv := ?_
    continuous_hom := ?_
    continuous_inv := ?_ }⟩
  · intro y x
    show ((wedgeScalar L M y)⁻¹ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
        (wedgeCLM L M y x) = x
    rw [wedgeCLM]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul,
      inv_mul_cancel₀ (wedgeScalar_ne_zero L M y), one_smul]
  · intro y x
    show (wedgeCLM L M y)
        (((wedgeScalar L M y)⁻¹ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) x) = x
    rw [wedgeCLM]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul,
      mul_inv_cancel₀ (wedgeScalar_ne_zero L M y), one_smul]
  · exact continuous_totalSpaceMap_clm (lmQuot L M) (lmTens L M) (ContinuousMap.id _)
      (fun y => wedgeCLM L M y) (continuousOn_wedge_nat L M)
  · exact continuous_totalSpaceMap_clm (lmTens L M) (lmQuot L M) (ContinuousMap.id _)
      (fun y => (wedgeScalar L M y)⁻¹ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
      (continuousOn_wedgeInv_nat L M)

end Data

/-- **The determinant trick at rank `2`**: for complex line bundles `L`, `M` over a topological
base, `c₁(L ⊕ M) = c₁(L ⊗ M)`.

The tautological quotient of `L ⊕ M` over the punctured total space is `π^*(L ⊗ M)`
(`tautQuotient_tensorLine_iso`), so the descent equation of the Chern recursion
(`chernClass_succ_of_le`), isomorphism-invariance (`chernClass_BundleIso`) and naturality under
pullback (`chernClass_comap`) give the identity. -/
theorem chernClass_one_whitneySum_eq_tensorLine {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type}
    [Fintype ι₁] [Fintype ι₂]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) :
    Work.Thom.chernClass (1 + 1) 1 (Work.Whitney.whitneySum L M)
      = Work.Thom.chernClass 1 1 (Work.Gen.tensorLine L M) := by
  obtain ⟨e⟩ := tautQuotient_tensorLine_iso L M
  have hiso : Work.Thom.chernClass 1 1 (lmQuot L M) = Work.Thom.chernClass 1 1 (lmTens L M) :=
    Work.Thom.chernClass_BundleIso (lmQuot L M) (lmTens L M) e
  have hnat : Work.Thom.chernClass 1 1 (lmTens L M)
      = (Work.Thom.CohMap (lmProj L M) ℤ (2 * 1)).hom
          (Work.Thom.chernClass 1 1 (Work.Gen.tensorLine L M)) :=
    Work.Thom.chernClass_comap (m := 1) (j := 1) (Work.Gen.tensorLine L M) (lmProj L M)
  have key : Work.Thom.chernClass 1 1 (tautQuotient (m := 1) (lmSum L M))
      = (Work.Thom.CohMap (lmProj L M) ℤ (2 * 1)).hom
          (Work.Thom.chernClass 1 1 (Work.Gen.tensorLine L M)) :=
    hiso.trans hnat
  rw [Work.Thom.chernClass_succ_of_le (Work.Whitney.whitneySum (m₁ := 1) (m₂ := 1) L M)
    (j := 1) le_rfl]
  rw [key]
  exact LinearEquiv.symm_apply_apply _ _

end

end Work.Gen
