import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.H_le_Wt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false
private lemma DzIter_add_hkm (i b : ℕ) (f : ℝ → ℝ → ℝ) :
    DzIter (i + b) f = DzIter i (DzIter b f) := by
  induction i with
  | zero => simp
  | succ n ih => rw [Nat.succ_add, DzIter_succ, ih, DzIter_succ]

/-- `DzIter` passes through `mixed` on the left. -/
private lemma DzIter_mixed_hkm (i b a : ℕ) (f : ℝ → ℝ → ℝ) :
    DzIter i (mixed b a f) = mixed (i + b) a f := by
  simp only [mixed]; rw [DzIter_add_hkm]

/-- Pointwise domination of the `H²`-integrand of `mixed b a g` by the `H⁴`-integrand of `g`,
for `a + b ≤ 2`.  Each term of the former is (a square whose base is) a weighted mixed
derivative of `g` of total order `≤ 4`; the index sets match up and the weights are dominated. -/
private lemma HkIntegrand_mixed_le_aux (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ)
    (hsm : SmoothNbhd g) (b a : ℕ) (hab : a + b ≤ 2) (z θ : ℝ) (hz : z ∈ Iz)
    (hθ : θ ∈ Iθ) :
    HkIntegrand α 2 (mixed b a g) z θ ≤ HkIntegrand α 4 g z θ := by
  have hb2 : b ≤ 2 := by omega
  have ha2 : a ≤ 2 := by omega
  set H : ℝ := w z / (Real.sin (2 * θ)) ^ (eta / 2) with hH
  set W : ℝ := Wt α z θ with hW
  -- Index convention: a pair `x = (p, q)` records `p = D_θ`-order and `q = D_z`-order.
  set T : ℕ × ℕ → ℝ := fun x =>
    if x.1 = 0 then (DzIter x.2 g z θ * H) ^ 2 else (mixed x.2 x.1 g z θ * W) ^ 2 with hT
  set S1 : Finset (ℕ × ℕ) := (Finset.range 3).image (fun i => (a, i + b)) with hS1def
  set S2 : Finset (ℕ × ℕ) := ((Finset.range 3 ×ˢ Finset.range 3).filter
      (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2)).image (fun x => (x.1 + a, x.2 + b))
    with hS2def
  set R1 : Finset (ℕ × ℕ) := (Finset.range 5).image (fun q => ((0 : ℕ), q)) with hR1def
  set R2 : Finset (ℕ × ℕ) := (Finset.range 5 ×ˢ Finset.range 5).filter
      (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 4) with hR2def
  have hTnn : ∀ x, 0 ≤ T x := by
    rintro ⟨x1, x2⟩; simp only [hT]; split <;> exact sq_nonneg _
  -- The first sum of `HkIntegrand α 4 g` sits on the index set `R1`.
  have hR1 : (∑ x ∈ R1, T x) = ∑ i ∈ Finset.range 5, (DzIter i g z θ * H) ^ 2 := by
    rw [hR1def]
    have hinj : Set.InjOn (fun q : ℕ => ((0 : ℕ), q)) (↑(Finset.range 5) : Set ℕ) := by
      intro x _ y _ h; simpa using h
    rw [Finset.sum_image (f := T) hinj]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    simp only [hT]; simp
  -- The second sum of `HkIntegrand α 4 g` sits on the index set `R2`.
  have hR2 : (∑ x ∈ R2, T x)
      = ∑ p ∈ Finset.range 5, ∑ q ∈ Finset.range 5,
          (if 1 ≤ p ∧ p + q ≤ 4 then (mixed q p g z θ * W) ^ 2 else 0) := by
    rw [hR2def, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    simp only [hT]
    by_cases hc : 1 ≤ p ∧ p + q ≤ 4
    · rw [if_pos hc, if_pos hc, if_neg (by omega : ¬ p = 0)]
    · rw [if_neg hc, if_neg hc]
  -- The first sum of `HkIntegrand α 2 (mixed b a g)` is dominated on `S1`.
  have hS1 : (∑ i ∈ Finset.range 3, (DzIter i (mixed b a g) z θ * H) ^ 2) ≤ ∑ x ∈ S1, T x := by
    rw [hS1def]
    have hinj : Set.InjOn (fun i : ℕ => (a, i + b)) (↑(Finset.range 3) : Set ℕ) := by
      intro x _ y _ h; simpa using h
    rw [Finset.sum_image (f := T) hinj]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [DzIter_mixed_hkm i b a g]
    simp only [hT]
    by_cases ha : a = 0
    · subst ha; rw [if_pos rfl]; simp [mixed]
    · rw [if_neg ha]
      have hHW : H ^ 2 ≤ W ^ 2 := by rw [hH, hW]; exact H_le_Wt α hα z θ hz hθ
      nlinarith [hHW, sq_nonneg (mixed (i + b) a g z θ)]
  -- The second sum of `HkIntegrand α 2 (mixed b a g)` equals the sum on `S2`.
  have hS2a : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0))
      = ∑ x ∈ (Finset.range 3 ×ˢ Finset.range 3).filter
            (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2),
          T (x.1 + a, x.2 + b) := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp only
    by_cases hc : 1 ≤ i ∧ i + j ≤ 2
    · rw [if_pos hc, if_pos hc]
      simp only [hT]
      rw [if_neg (by omega : ¬ i + a = 0)]
      rw [mixed_comm g hsm j i b a z θ hz hθ]
    · rw [if_neg hc, if_neg hc]
  have hS2b : (∑ x ∈ (Finset.range 3 ×ˢ Finset.range 3).filter
          (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2), T (x.1 + a, x.2 + b))
      = ∑ x ∈ S2, T x := by
    rw [hS2def]
    have hinj : Set.InjOn (fun x : ℕ × ℕ => (x.1 + a, x.2 + b))
        (↑((Finset.range 3 ×ˢ Finset.range 3).filter
          (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2)) : Set (ℕ × ℕ)) := by
      intro x _ y _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Nat.add_right_cancel h.1) (Nat.add_right_cancel h.2)
    rw [Finset.sum_image (f := T) hinj]
  have hS2 : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0))
      = ∑ x ∈ S2, T x := hS2a.trans hS2b
  -- `S1` and `S2` are disjoint, and so are `R1` and `R2`.
  have hdisjS : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hS1def, Finset.mem_image] at hx1
    obtain ⟨i, _, rfl⟩ := hx1
    rw [hS2def, Finset.mem_image] at hx2
    obtain ⟨y, hy, hxy⟩ := hx2
    rw [Finset.mem_filter] at hy
    simp only [Prod.mk.injEq] at hxy
    have hy1 : 1 ≤ y.1 := hy.2.1
    omega
  have hdisjR : Disjoint R1 R2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hR1def, Finset.mem_image] at hx1
    obtain ⟨q, _, rfl⟩ := hx1
    rw [hR2def, Finset.mem_filter] at hx2
    have h := hx2.2.1
    simp only [] at h
    omega
  -- Every index of `S1 ∪ S2` is an index of `R1 ∪ R2`.
  have hsub : S1 ∪ S2 ⊆ R1 ∪ R2 := by
    intro x hx
    rw [Finset.mem_union] at hx ⊢
    rcases hx with hx | hx
    · rw [hS1def, Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [Finset.mem_range] at hi
      by_cases ha : a = 0
      · left
        rw [hR1def, Finset.mem_image]
        exact ⟨i + b, by rw [Finset.mem_range]; omega, by simp [ha]⟩
      · right
        rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
        dsimp only
        refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · rw [hS2def, Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hy
      right
      rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      dsimp only
      refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  have hLHSunfold : HkIntegrand α 2 (mixed b a g) z θ
      = (∑ i ∈ Finset.range 3, (DzIter i (mixed b a g) z θ * H) ^ 2)
        + ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
            (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0) := by
    simp [HkIntegrand, ← hH, ← hW]
  have hRHSunfold : HkIntegrand α 4 g z θ
      = (∑ i ∈ Finset.range 5, (DzIter i g z θ * H) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i g z θ * W) ^ 2 else 0) := by
    simp [HkIntegrand, ← hH, ← hW]
  have hstep1 : (∑ i ∈ Finset.range 3, (DzIter i (mixed b a g) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
            (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0))
      ≤ ∑ x ∈ S1 ∪ S2, T x := by
    rw [hS2, Finset.sum_union hdisjS]
    linarith [hS1]
  have hstep2 : (∑ x ∈ S1 ∪ S2, T x)
      ≤ (∑ i ∈ Finset.range 5, (DzIter i g z θ * H) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i g z θ * W) ^ 2 else 0) := by
    rw [← hR1, ← hR2, ← Finset.sum_union hdisjR]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hTnn x)
  rw [hLHSunfold, hRHSunfold]
  exact le_trans hstep1 hstep2


/-! ## The open set on which joint continuity holds -/

/-- The open set `(0,∞) × (0,π/2)` on which the integrand is jointly continuous. -/
private def U : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)

private lemma isOpen_U : IsOpen U := isOpen_Ioi.prod isOpen_Ioo

private lemma U_subset_nbhU : U ⊆ nbhU :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num))
    (Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos]))

/-- `sin (2θ)` is positive for `θ ∈ (0, π/2)`. -/
private lemma sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2)) : 0 < Real.sin (2 * θ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-! ## Continuity of the individual weight factors -/

private lemma contOn_slice_sinpow (p : ℝ) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (Set.Ioo 0 (π/2)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
    (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))

private lemma contOn_slice_H (z : ℝ) :
    ContinuousOn (fun θ : ℝ => w z / (Real.sin (2 * θ)) ^ (eta / 2)) (Set.Ioo 0 (π/2)) :=
  continuousOn_const.div (contOn_slice_sinpow (eta / 2))
    (fun θ hθ => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos hθ) _))

private lemma contOn_slice_Wt (α z : ℝ) :
    ContinuousOn (fun θ : ℝ => Wt α z θ) (Set.Ioo 0 (π/2)) := by
  simp only [Wt, wTheta]
  exact continuousOn_const.mul (contOn_slice_sinpow (-(gam α / 2)))

private lemma contOn_uncurry_sinpow (p : ℝ) :
    ContinuousOn (fun y : ℝ × ℝ => (Real.sin (2 * y.2)) ^ p) U :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun y hy => Or.inl (ne_of_gt (sin_two_pos hy.2)))

private lemma contOn_uncurry_w : ContinuousOn (fun y : ℝ × ℝ => w y.1) U := by
  simp only [w]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun y hy => ?_)
  exact pow_ne_zero 2 (ne_of_gt hy.1)

private lemma contOn_uncurry_H :
    ContinuousOn (fun y : ℝ × ℝ => w y.1 / (Real.sin (2 * y.2)) ^ (eta / 2)) U :=
  contOn_uncurry_w.div (contOn_uncurry_sinpow (eta / 2))
    (fun y hy => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos hy.2) _))

private lemma contOn_uncurry_Wt (α : ℝ) :
    ContinuousOn (fun y : ℝ × ℝ => Wt α y.1 y.2) U := by
  simp only [Wt, wTheta]
  exact contOn_uncurry_w.mul (contOn_uncurry_sinpow (-(gam α / 2)))

/-! ## Continuity of the slices of an iterated derivative, and of the integrand -/

private lemma contOn_slice {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) {z : ℝ} (hz : z ∈ Iz) :
    ContinuousOn (fun θ : ℝ => f z θ) (Set.Ioo 0 (π/2)) := by
  have hz' : (-1 : ℝ) < z := by rw [Iz, Set.mem_Ici] at hz; linarith
  have hpair : ContDiffOn ℝ ⊤ (fun θ : ℝ => (z, θ)) (Set.Ioo (-1) (π / 2 + 1)) := by
    fun_prop
  have hmaps : MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo (-1) (π / 2 + 1)) nbhU :=
    fun θ hθ => ⟨hz', hθ⟩
  exact (h.comp hpair hmaps).continuousOn.mono
    (Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos]))

private lemma contOn_uncurry {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ContinuousOn (fun y : ℝ × ℝ => f y.1 y.2) U := h.continuousOn.mono U_subset_nbhU

private lemma contOn_slice_HkIntegrand (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f)
    {z : ℝ} (hz : z ∈ Iz) :
    ContinuousOn (fun θ : ℝ => HkIntegrand α k f z θ) (Set.Ioo 0 (π/2)) := by
  simp only [HkIntegrand]
  refine ContinuousOn.add ?_ ?_
  · apply continuousOn_finsetSum
    intro i _
    exact ((contOn_slice (SmoothNbhd.DzIter h i) hz).mul (contOn_slice_H z)).pow 2
  · apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    split_ifs with hc
    · exact ((contOn_slice (SmoothNbhd.DzIter (SmoothNbhd.DthIter h i) j) hz).mul
        (contOn_slice_Wt α z)).pow 2
    · exact continuousOn_const

private lemma contOn_uncurry_HkIntegrand (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ContinuousOn (fun y : ℝ × ℝ => HkIntegrand α k f y.1 y.2) U := by
  simp only [HkIntegrand]
  refine ContinuousOn.add ?_ ?_
  · apply continuousOn_finsetSum
    intro i _
    exact ((contOn_uncurry (SmoothNbhd.DzIter h i)).mul contOn_uncurry_H).pow 2
  · apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    split_ifs with hc
    · exact ((contOn_uncurry (SmoothNbhd.DzIter (SmoothNbhd.DthIter h i) j)).mul
        (contOn_uncurry_Wt α)).pow 2
    · exact continuousOn_const

/-! ## The half-open intervals have the same measure as their interiors -/

private lemma measurableSet_Iz : MeasurableSet Iz := measurableSet_Ici
private lemma measurableSet_Iθ : MeasurableSet Iθ := measurableSet_Icc

private lemma restrict_Iz_eq : volume.restrict Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show (Iz : Set ℝ) = Set.Ici 0 from rfl, Set.Ici_sdiff_Ioi, Set.Icc_self]
    exact measure_singleton 0
  · rw [show (Iz : Set ℝ) = Set.Ici 0 from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioi_subset_Ici_self, measure_empty]

private lemma restrict_Iθ_eq : volume.restrict Iθ = volume.restrict (Set.Ioo 0 (π/2)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show (Iθ : Set ℝ) = Set.Icc 0 (π/2) from rfl,
      Set.Icc_sdiff_Ioo_same (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)]
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton 0) (measure_singleton _)
  · rw [show (Iθ : Set ℝ) = Set.Icc 0 (π/2) from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]

/-! ## Measurability of the integrand -/

private lemma aestronglyMeasurable_slice (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f)
    {z : ℝ} (hz : z ∈ Iz) :
    AEStronglyMeasurable (fun θ : ℝ => HkIntegrand α k f z θ) (volume.restrict Iθ) := by
  have hmeas : AEMeasurable (fun θ : ℝ => HkIntegrand α k f z θ)
      (volume.restrict (Set.Ioo 0 (π/2))) :=
    (contOn_slice_HkIntegrand α k h hz).aemeasurable isOpen_Ioo.measurableSet
  rw [restrict_Iθ_eq]
  exact hmeas.aestronglyMeasurable

private lemma aestronglyMeasurable_uncurry (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    AEStronglyMeasurable (fun y : ℝ × ℝ => HkIntegrand α k f y.1 y.2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) := by
  rw [restrict_Iz_eq, restrict_Iθ_eq]
  have hUc : ((volume.restrict (Set.Ioi (0 : ℝ))).prod
      (volume.restrict (Set.Ioo 0 (π/2)))) Uᶜ = 0 := by
    rw [Measure.prod_restrict, Measure.restrict_apply (isOpen_U.measurableSet.compl)]
    change (volume.prod volume) (Uᶜ ∩ U) = 0
    rw [Set.compl_inter_self, measure_empty]
  have hae : ∀ᵐ y ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod
      (volume.restrict (Set.Ioo 0 (π/2)))), y ∈ U := by
    rw [ae_iff]
    exact hUc
  rw [← Measure.restrict_eq_self_of_ae_mem hae]
  exact (contOn_uncurry_HkIntegrand α k h).aestronglyMeasurable isOpen_U.measurableSet

/-! ## Assembly: `HkMem` transfers from `g` to its mixed derivatives -/

theorem HkMem_mixed_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α 4 g)
    (b a : ℕ) (hab : a + b ≤ 2) :
    Work.Spaces.HkMem α 2 (Work.Spaces.mixed b a g) := by
  have hsm' : SmoothNbhd (mixed b a g) := SmoothNbhd.DzIter (SmoothNbhd.DthIter hsm a) b
  have hle : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      HkIntegrand α 2 (mixed b a g) z θ ≤ HkIntegrand α 4 g z θ :=
    fun z hz θ hθ => HkIntegrand_mixed_le_aux α hα g hsm b a hab z θ hz hθ
  have hslice : ∀ z ∈ Iz, AEStronglyMeasurable
      (fun θ : ℝ => HkIntegrand α 2 (mixed b a g) z θ) (volume.restrict Iθ) :=
    fun z hz => aestronglyMeasurable_slice α 2 hsm' hz
  constructor
  · intro z hz
    refine Integrable.mono' (hmem.1 z hz) (hslice z hz) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iθ] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (HkIntegrand_nonneg α 2 (mixed b a g) z θ)]
    exact hle z hz θ hθ
  · refine Integrable.mono' hmem.2
      (aestronglyMeasurable_uncurry α 2 hsm').integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Iz] with z hz
    have hnn : 0 ≤ ∫ θ in Iθ, HkIntegrand α 2 (mixed b a g) z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Iθ
        (fun θ _ => HkIntegrand_nonneg α 2 (mixed b a g) z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Iθ
        (fun θ _ => HkIntegrand_nonneg α 2 (mixed b a g) z θ))
      (hmem.1 z hz)
      (ae_restrict_of_forall_mem measurableSet_Iθ (fun θ hθ => hle z hz θ hθ))

end Work.Spaces
