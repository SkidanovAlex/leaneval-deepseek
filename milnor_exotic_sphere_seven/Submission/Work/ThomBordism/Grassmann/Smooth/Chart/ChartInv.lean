import Submission.Work.ThomBordism.Grassmann.Smooth.Chart.Continuity

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The charts of the oriented Grassmannian

This file assembles the chart of the oriented Grassmannian `OG k m` attached to a chart index `S`
and an orientation sign `ε`:

* `chartSrc S ε` — the open set of points of `OG k m` whose plane is `S`-transverse and whose
  orientation sign is `ε`;
* `chartInv S ε d` — the point of `chartSrc S ε` whose graph data is `d` (namely `posPoint S d`
  for `ε = 1` and `negPoint S d` otherwise);
* `chartTgt S ε` — the open image of the chart;
* `chart S ε` — the chart itself, an `OpenPartialHomeomorph (OG k m) (Amb k →L[ℝ] Amb m)`.
-/

namespace Work.ThomBordism.Grassmann.Smooth

open scoped Topology
open Set

noncomputable section

variable {k m : ℕ}

/-! ## The two points over a graph lie in the chart -/

theorem posPoint_mem_baseSet (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    posPoint S d ∈ baseSet S :=
  (mem_baseSet_iff S _).mpr (posFrame_mem_chartSet S d)

theorem negPoint_mem_baseSet (S : ChartIdx k m) (d : Amb k →L[ℝ] Amb m) :
    negPoint S d ∈ baseSet S :=
  (mem_baseSet_iff S _).mpr (negFrame_mem_chartSet S d)

/-! ## Uniqueness of a point with given graph data and orientation -/

theorem projS_coordEval (S : ChartIdx k m) (f : Stiefel k m) (hf : f ∈ chartSet S) (v : Amb k) :
    projS S (coordEval S f v) = v := by
  rw [projS_eq_toLp_coordProj, coordProj_coordEval S f v hf, WithLp.toLp_ofLp]

/-- **A point of the chart is determined by its graph data and its orientation sign.** -/
theorem eq_of_chartData_eq_of_frameSign_eq {S : ChartIdx k m} {x y : OG k m}
    (hx : x ∈ baseSet S) (hy : y ∈ baseSet S)
    (hd : chartData S x = chartData S y) (hs : frameSign S x = frameSign S y) : x = y := by
  obtain ⟨f, rfl⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = x := Quotient.exists_rep x
  obtain ⟨g, rfl⟩ : ∃ g : Stiefel k m, Quotient.mk'' g = y := Quotient.exists_rep y
  have hfS : f ∈ chartSet S := (mem_baseSet_iff S f).mp hx
  have hgS : g ∈ chartSet S := (mem_baseSet_iff S g).mp hy
  have hfg : chartFun S f = chartFun S g := hd
  -- the two frames span the same plane
  have hspan : Submodule.span ℝ (Set.range f.1) = Submodule.span ℝ (Set.range g.1) := by
    refine le_antisymm ?_ ?_
    · intro w hw
      have hw1 : w = coordEval S f (projS S w) := (coordEval_coordProj S f hfS hw).symm
      have hw2 : coordEval S g (projS S w) = w := by
        have h1 : projS S (coordEval S g (projS S w)) = projS S w :=
          projS_coordEval S g hgS _
        have h2 : projC S (coordEval S g (projS S w)) = projC S w := by
          rw [← chartFun_apply, ← hfg, chartFun_apply,
            show coordEval S f (projS S w) = w from hw1.symm]
        calc coordEval S g (projS S w)
            = inclS S (projS S (coordEval S g (projS S w)))
              + inclC S (projC S (coordEval S g (projS S w))) :=
              (inclS_projS_add_inclC_projC S _).symm
          _ = inclS S (projS S w) + inclC S (projC S w) := by rw [h1, h2]
          _ = w := inclS_projS_add_inclC_projC S w
      rw [← hw2, coordEval]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (coordVec_mem_span S g i)
    · intro w hw
      have hw1 : w = coordEval S g (projS S w) := (coordEval_coordProj S g hgS hw).symm
      have hw2 : coordEval S f (projS S w) = w := by
        have h1 : projS S (coordEval S f (projS S w)) = projS S w :=
          projS_coordEval S f hfS _
        have h2 : projC S (coordEval S f (projS S w)) = projC S w := by
          rw [← chartFun_apply, hfg, chartFun_apply,
            show coordEval S g (projS S w) = w from hw1.symm]
        calc coordEval S f (projS S w)
            = inclS S (projS S (coordEval S f (projS S w)))
              + inclC S (projC S (coordEval S f (projS S w))) :=
              (inclS_projS_add_inclC_projC S _).symm
          _ = inclS S (projS S w) + inclC S (projC S w) := by rw [h1, h2]
          _ = w := inclS_projS_add_inclC_projC S w
      rw [← hw2, coordEval]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (coordVec_mem_span S f i)
  -- the signs agree, so the frames define the same oriented point
  have hdetf : (frameMatrix S f.1).det ≠ 0 := hfS
  have hdetg : (frameMatrix S g.1).det ≠ 0 := hgS
  have hsign : 0 < (frameMatrix S f.1).det * (frameMatrix S g.1).det := by
    have hss : frameSign S (Quotient.mk'' f) * frameSign S (Quotient.mk'' g) = 1 := by
      rw [hs]; exact frameSign_mul_self S (Quotient.mk'' g) hy
    have h1 : (frameMatrix S f.1).det * (frameMatrix S g.1).det
        = (frameSign S (Quotient.mk'' f) * frameSign S (Quotient.mk'' g))
          * (|(frameMatrix S f.1).det| * |(frameMatrix S g.1).det|) := by
      conv_lhs => rw [frameMatrix_det_eq_sign S f hfS, frameMatrix_det_eq_sign S g hgS]
      ring
    rw [h1, hss, one_mul]
    exact mul_pos (abs_pos.mpr hdetf) (abs_pos.mpr hdetg)
  exact (mkEqOfDetSign f.2 g.2 hspan hdetf hsign).symm

/-! ## The source of the chart -/

/-- The set of points of the Grassmannian whose plane is `S`-transverse and whose orientation sign
is `ε`. -/
def chartSrc (S : ChartIdx k m) (ε : ℝ) : Set (OG k m) := {x | x ∈ baseSet S ∧ frameSign S x = ε}

theorem mem_chartSrc {S : ChartIdx k m} {ε : ℝ} {x : OG k m} :
    x ∈ chartSrc S ε ↔ x ∈ baseSet S ∧ frameSign S x = ε := Iff.rfl

theorem isOpen_chartSrc (S : ChartIdx k m) (ε : ℝ) : IsOpen (chartSrc S ε) := by
  rcases eq_or_ne ε 1 with h1 | h1
  · subst h1
    have hset : chartSrc S 1 = baseSet S ∩ frameSign S ⁻¹' {t : ℝ | 0 < t} := by
      ext x; constructor
      · rintro ⟨hx, h⟩
        exact ⟨hx, by show 0 < frameSign S x; rw [h]; norm_num⟩
      · rintro ⟨hx, h⟩
        refine ⟨hx, ?_⟩
        have hpos : 0 < frameSign S x := h
        have hsq : frameSign S x ^ 2 = 1 := by
          rw [sq]; exact frameSign_mul_self S x hx
        rcases sq_eq_one_iff.mp hsq with h' | h'
        · exact h'
        · rw [h'] at hpos; norm_num at hpos
    rw [hset]
    exact (continuousOn_frameSign S).isOpen_inter_preimage (isOpen_baseSet S) isOpen_Ioi
  · rcases eq_or_ne ε (-1) with h2 | h2
    · subst h2
      have hset : chartSrc S (-1) = baseSet S ∩ frameSign S ⁻¹' {t : ℝ | t < 0} := by
        ext x; constructor
        · rintro ⟨hx, h⟩
          exact ⟨hx, by show frameSign S x < 0; rw [h]; norm_num⟩
        · rintro ⟨hx, h⟩
          refine ⟨hx, ?_⟩
          have hneg : frameSign S x < 0 := h
          have hsq : frameSign S x ^ 2 = 1 := by
            rw [sq]; exact frameSign_mul_self S x hx
          rcases sq_eq_one_iff.mp hsq with h' | h'
          · rw [h'] at hneg; norm_num at hneg
          · exact h'
      rw [hset]
      exact (continuousOn_frameSign S).isOpen_inter_preimage (isOpen_baseSet S) isOpen_Iio
    · have hset : chartSrc S ε = ∅ := by
        ext x; constructor
        · rintro ⟨hx, h⟩
          have hsq : frameSign S x ^ 2 = 1 := by
            rw [sq]; exact frameSign_mul_self S x hx
          rcases sq_eq_one_iff.mp hsq with h' | h'
          · exact absurd (h.symm.trans h') h1
          · exact absurd (h.symm.trans h') h2
        · intro hx; exact hx.elim
      rw [hset]; exact isOpen_empty

/-! ## The inverse chart -/

/-- The point of `chartSrc S ε` with graph data `d`. -/
def chartInv (S : ChartIdx k m) (ε : ℝ) (d : Amb k →L[ℝ] Amb m) : OG k m :=
  if ε = 1 then posPoint S d else negPoint S d

theorem chartInv_of_eq_one (S : ChartIdx k m) {d : Amb k →L[ℝ] Amb m} {ε : ℝ} (h : ε = 1) :
    chartInv S ε d = posPoint S d := if_pos h

theorem chartInv_of_ne_one (S : ChartIdx k m) {d : Amb k →L[ℝ] Amb m} {ε : ℝ} (h : ε ≠ 1) :
    chartInv S ε d = negPoint S d := if_neg h

/-- The image of the chart. -/
def chartTgt (S : ChartIdx k m) (ε : ℝ) : Set (Amb k →L[ℝ] Amb m) :=
  {d | chartInv S ε d ∈ chartSrc S ε}

theorem continuous_chartInv (S : ChartIdx k m) (ε : ℝ) : Continuous (chartInv S ε) := by
  rcases eq_or_ne ε 1 with h | h
  · rw [show chartInv S ε = posPoint S from funext fun d => chartInv_of_eq_one S h]
    exact continuous_posPoint S
  · rw [show chartInv S ε = negPoint S from funext fun d => chartInv_of_ne_one S h]
    exact continuous_negPoint S

theorem isOpen_chartTgt (S : ChartIdx k m) (ε : ℝ) : IsOpen (chartTgt S ε) :=
  (isOpen_chartSrc S ε).preimage (continuous_chartInv S ε)

theorem chartData_chartInv (S : ChartIdx k m) (ε : ℝ) {d : Amb k →L[ℝ] Amb m}
    (hd : d ∈ chartTgt S ε) : chartData S (chartInv S ε d) = d := by
  rcases eq_or_ne ε 1 with h | h
  · rw [chartInv_of_eq_one S h]; exact chartData_posPoint S d
  · rw [chartInv_of_ne_one S h]; exact chartData_negPoint S d

theorem chartInv_chartData (S : ChartIdx k m) (ε : ℝ) {x : OG k m} (hx : x ∈ chartSrc S ε) :
    chartInv S ε (chartData S x) = x := by
  obtain ⟨hxbase, hxsign⟩ := hx
  rcases eq_or_ne ε 1 with h | h
  · rw [chartInv_of_eq_one S h]
    refine eq_of_chartData_eq_of_frameSign_eq (posPoint_mem_baseSet S _) hxbase
      (chartData_posPoint S _) ?_
    rw [frameSign_posPoint, hxsign, ← h]
  · have hk : 0 < k := by
      by_contra hk
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
      exact h (hxsign.symm.trans (frameSign_eq_one_of_k_eq_zero hk0 x))
    have hε : ε = -1 := by
      have hsq : frameSign S x ^ 2 = 1 := by
        rw [sq]; exact frameSign_mul_self S x hxbase
      rcases sq_eq_one_iff.mp hsq with h' | h'
      · exact absurd (hxsign.symm.trans h') h
      · exact hxsign.symm.trans h'
    rw [chartInv_of_ne_one S h]
    refine eq_of_chartData_eq_of_frameSign_eq (negPoint_mem_baseSet S _) hxbase
      (chartData_negPoint S _) ?_
    rw [frameSign_negPoint hk, hxsign, hε]

/-! ## The chart -/

/-- **The chart of the oriented Grassmannian** attached to the chart index `S` and the orientation
sign `ε`. -/
noncomputable def chart (S : ChartIdx k m) (ε : ℝ) :
    OpenPartialHomeomorph (OG k m) (Amb k →L[ℝ] Amb m) where
  toFun := chartData S
  invFun := chartInv S ε
  source := chartSrc S ε
  target := chartTgt S ε
  map_source' := fun x hx => by
    show chartInv S ε (chartData S x) ∈ chartSrc S ε
    rw [chartInv_chartData S ε hx]; exact hx
  map_target' := fun d hd => hd
  left_inv' := fun x hx => chartInv_chartData S ε hx
  right_inv' := fun d hd => chartData_chartInv S ε hd
  continuousOn_toFun := (continuousOn_chartData S).mono fun x hx => hx.1
  continuousOn_invFun := (continuous_chartInv S ε).continuousOn
  open_source := isOpen_chartSrc S ε
  open_target := isOpen_chartTgt S ε

@[simp] theorem chart_source (S : ChartIdx k m) (ε : ℝ) : (chart S ε).source = chartSrc S ε := rfl
@[simp] theorem chart_target (S : ChartIdx k m) (ε : ℝ) : (chart S ε).target = chartTgt S ε := rfl
@[simp] theorem chart_toFun (S : ChartIdx k m) (ε : ℝ) : ⇑(chart S ε) = chartData S := rfl
@[simp] theorem chart_invFun (S : ChartIdx k m) (ε : ℝ) : (chart S ε).symm = chartInv S ε := rfl

end

end Work.ThomBordism.Grassmann.Smooth
