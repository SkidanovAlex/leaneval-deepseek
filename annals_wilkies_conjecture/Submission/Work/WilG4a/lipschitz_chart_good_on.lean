/-
  WilG4a — the `Λ`-restricted Lipschitz chart statement for a good cell (BNZ §5.1).

  This is the `Λ`-parametrised form of `Work.WilG4a.lipschitz_chart_good`: the hypotheses
  `F i₁ l · : I → I` and `F j l · : I → I` are assumed only for the parameters `l ∈ Λ`, and
  the conclusions are drawn only for those `l`.  Everything is proved parameter-wise, so
  nothing changes mathematically: for a fixed `l ∈ Λ` the argument only uses the cell data
  at `l` and the two "maps `I` into `I`" hypotheses at that same `l`.

  For a fixed `l`, `GoodCell` gives one of two shapes for the fibre `fibre κ l`:

  * a subsingleton (empty or a point).  Then `chart1` is constant on it and every claim is
    immediate (`Submission.Work.WilG4a.lipschitz_chart_point`).
  * a nondegenerate open interval `(a,b)`.  Then the dominating member `F i₁ l` is strictly
    monotone on `(a,b)` with nonvanishing derivative, its image is the interval
    `(Aend, Bend)`, and `chart1 (F i₁) κ l` is the inverse branch of `F i₁ l` reparametrised
    by `t`: the chain rule gives
    `(F j l ∘ chart1)'(t) = (Bend - Aend) · ∂ₓF j / ∂ₓF i₁`,
    bounded by `1` because `|∂ₓF j| ≤ |∂ₓF i₁|` (domination) and `Bend - Aend ≤ 1`.

  The analytic pieces of the second case are provided by the sibling modules
  `cgo_fibre_mono_image` (monotonicity and shape of the image of the fibre),
  `cgo_chart1_char` (the chart is the unique point of the fibre above each `t`),
  `cgo_chart1_contDiffOn` (the chart is `C¹` on `I`, with the inverse-function derivative
  formula) and `cgo_chart1_comp_contDiff` (the chain rule and the bound `≤ 1`).  This file
  supplies the reduction from `GoodCell` to slice-level data, the two cases, and the
  assembly.
-/
import Mathlib
import Submission.Work.WilG4a.LipChartsDefs
import Submission.Work.WilG4a.lipschitz_chart_point
import Submission.Work.WilG4a.cgo_fibre_mono_image
import Submission.Work.WilG4a.cgo_chart1_char
import Submission.Work.WilG4a.cgo_chart1_contDiffOn
import Submission.Work.WilG4a.cgo_chart1_comp_contDiff

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilG4a

variable {p : ℕ}

/-! ## 1. Reading the slice data of a family member at a parameter `l` -/

/-- Every fibre of a set contained in the strip `{z | z (last) ∈ I}` is contained in `I`. -/
theorem cgoL_fibre_subset_I (κ : Set (Fin (p + 1) → ℝ)) (hκ : κ ⊆ strip p)
    (l : Fin p → ℝ) : fibre κ l ⊆ I := by
  intro y hy
  simpa [strip] using hκ hy

/-- The chart attached to a set inside the strip always takes its values in `I`. -/
theorem cgoL_chart1_mem_I (f : (Fin p → ℝ) → ℝ → ℝ) (κ : Set (Fin (p + 1) → ℝ))
    (l : Fin p → ℝ) (hκ : κ ⊆ strip p) {t : ℝ} (ht : t ∈ I) : chart1 f κ l t ∈ I := by
  rw [chart1]
  by_cases h : ∃ y : ℝ, Fin.snoc l y ∈ κ ∧ f l y = Aend κ f l + (Bend κ f l - Aend κ f l) * t
  · rw [dif_pos h]
    exact cgoL_fibre_subset_I κ hκ l (Classical.choose_spec h).1
  · rw [dif_neg h]
    exact ⟨by norm_num, by norm_num⟩

theorem cgoL_update_snoc_last (l : Fin p → ℝ) (x y : ℝ) :
    Function.update (Fin.snoc l x : Fin (p+1) → ℝ) (Fin.last p) y = Fin.snoc l y := by
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [Function.update_of_ne (by simp [Fin.castSucc_ne_last])]; simp
  · simp

theorem cgoL_sliceFun_snoc (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (x : ℝ) :
    sliceFun f (Fin.snoc l x) = fun y : ℝ => f l y := by
  funext y
  simp only [sliceFun, cgoL_update_snoc_last, famFun_apply]

theorem cgoL_isSliceDeriv_snoc (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ)
    (y s : ℝ) : IsSliceDeriv f (Fin.snoc l y) s ↔ HasDerivAt (f l) s y := by
  simp only [IsSliceDeriv, cgoL_sliceFun_snoc, Fin.snoc_last]

theorem cgoL_isSliceDeriv_snoc_update (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ)
    (y x s : ℝ) :
    IsSliceDeriv f (Function.update (Fin.snoc l y) (Fin.last p) x) s ↔ HasDerivAt (f l) s x := by
  rw [cgoL_update_snoc_last]
  exact cgoL_isSliceDeriv_snoc f l x s

theorem cgoL_xDeriv_snoc (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (y : ℝ) :
    xDeriv f (Fin.snoc l y) = deriv (f l) y := by
  simp only [xDeriv, cgoL_sliceFun_snoc, Fin.snoc_last]

theorem cgoL_sliceDiff_snoc (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ sliceDiff f ↔ DifferentiableAt ℝ (f l) y := by
  simp only [sliceDiff, Set.mem_ofPred_eq, cgoL_sliceFun_snoc, Fin.snoc_last]

theorem cgoL_posSet_snoc (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ posSet f ↔ ∃ s : ℝ, HasDerivAt (f l) s y ∧ 0 < s := by
  simp only [posSet, Set.mem_ofPred_eq, cgoL_isSliceDeriv_snoc]

theorem cgoL_negSet_snoc (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ negSet f ↔ ∃ s : ℝ, HasDerivAt (f l) s y ∧ s < 0 := by
  simp only [negSet, Set.mem_ofPred_eq, cgoL_isSliceDeriv_snoc]

theorem cgoL_domSet_snoc (f g : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ domSet f g ↔
      ∃ s t : ℝ, HasDerivAt (f l) s y ∧ HasDerivAt (g l) t y ∧ |s| ≤ |t| := by
  simp only [domSet, Set.mem_ofPred_eq, cgoL_isSliceDeriv_snoc]

theorem cgoL_sliceDerivCont_snoc (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (y : ℝ) :
    Fin.snoc l y ∈ sliceDerivCont f ↔
      ∃ s : ℝ, HasDerivAt (f l) s y ∧ ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - y| < δ →
        ∃ s' : ℝ, HasDerivAt (f l) s' x ∧ |s' - s| < ε := by
  simp only [sliceDerivCont, Set.mem_ofPred_eq, Fin.snoc_last, cgoL_isSliceDeriv_snoc,
    cgoL_isSliceDeriv_snoc_update]

/-- `sliceDerivCont` at a point of `κ` says exactly that the derivative of the slice is
continuous there. -/
theorem cgoL_continuousAt_deriv_of_sliceDerivCont (f : (Fin p → ℝ) → ℝ → ℝ)
    (l : Fin p → ℝ) {y : ℝ} (hy : Fin.snoc l y ∈ sliceDerivCont f) :
    ContinuousAt (fun x : ℝ => deriv (f l) x) y := by
  rw [cgoL_sliceDerivCont_snoc] at hy
  obtain ⟨s, hs, hcont⟩ := hy
  have hs' : deriv (f l) y = s := hs.deriv
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hcont ε hε
  refine ⟨δ, hδ, fun x hx => ?_⟩
  obtain ⟨s', hs'2, hlt⟩ := h x (by simpa [Real.dist_eq] using hx)
  rw [Real.dist_eq, hs'2.deriv, hs']
  exact hlt

/-! ## 2. The slice data supplied by `GoodCell` at a parameter `l` -/

/-- On the fibre of a good cell, every family member is differentiable with continuous
derivative, and the dominating member dominates the others. -/
theorem cgoL_slice_data {k : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ}
    {κ : Set (Fin (p+1) → ℝ)} {i₁ : Fin k} (hgood : GoodCell k F κ i₁) (l : Fin p → ℝ) :
    (∀ y ∈ fibre κ l, HasDerivAt (F i₁ l) (deriv (F i₁ l) y) y ∧
      ContinuousAt (fun y' : ℝ => deriv (F i₁ l) y') y) ∧
    (∀ y ∈ fibre κ l, ∀ j : Fin k, HasDerivAt (F j l) (deriv (F j l) y) y ∧
      ContinuousAt (fun y' : ℝ => deriv (F j l) y') y ∧
      |deriv (F j l) y| ≤ |deriv (F i₁ l) y|) := by
  constructor
  · intro y hy
    have hz : Fin.snoc l y ∈ κ := hy
    have hd : DifferentiableAt ℝ (F i₁ l) y := by
      rw [← cgoL_sliceDiff_snoc]; exact hgood.1 i₁ hz
    have hc : ContinuousAt (fun y' : ℝ => deriv (F i₁ l) y') y :=
      cgoL_continuousAt_deriv_of_sliceDerivCont (F i₁) l (hgood.2.1 i₁ hz)
    exact ⟨hd.hasDerivAt, hc⟩
  · intro y hy j
    have hz : Fin.snoc l y ∈ κ := hy
    have hd : DifferentiableAt ℝ (F j l) y := by
      rw [← cgoL_sliceDiff_snoc]; exact hgood.1 j hz
    have hc : ContinuousAt (fun y' : ℝ => deriv (F j l) y') y :=
      cgoL_continuousAt_deriv_of_sliceDerivCont (F j) l (hgood.2.1 j hz)
    have hdom := hgood.2.2.1 j hz
    rw [cgoL_domSet_snoc] at hdom
    obtain ⟨s, t, hs, ht, hle⟩ := hdom
    refine ⟨hd.hasDerivAt, hc, ?_⟩
    rw [hs.deriv, ht.deriv]
    exact hle

/-- The slice data of a good cell together with the sign of the derivative of the dominating
member. -/
theorem cgoL_slice_data_sign {k : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ}
    {κ : Set (Fin (p+1) → ℝ)} {i₁ : Fin k} (hgood : GoodCell k F κ i₁)
    (hsign : κ ⊆ posSet (F i₁) ∨ κ ⊆ negSet (F i₁)) (l : Fin p → ℝ) :
    (∀ y ∈ fibre κ l, HasDerivAt (F i₁ l) (deriv (F i₁ l) y) y ∧
      ContinuousAt (fun y' : ℝ => deriv (F i₁ l) y') y) ∧
    (∀ y ∈ fibre κ l, deriv (F i₁ l) y ≠ 0) ∧
    ((∀ y ∈ fibre κ l, 0 < deriv (F i₁ l) y) ∨ (∀ y ∈ fibre κ l, deriv (F i₁ l) y < 0)) ∧
    (∀ y ∈ fibre κ l, ∀ j : Fin k, HasDerivAt (F j l) (deriv (F j l) y) y ∧
      ContinuousAt (fun y' : ℝ => deriv (F j l) y') y ∧
      |deriv (F j l) y| ≤ |deriv (F i₁ l) y|) := by
  have hdata := cgoL_slice_data hgood l
  refine ⟨hdata.1, ?_, ?_, hdata.2⟩
  · intro y hy
    rcases hsign with hp | hn
    · obtain ⟨s, hs, hspos⟩ := (cgoL_posSet_snoc (F i₁) l y).mp (hp hy)
      rw [hs.deriv]; exact ne_of_gt hspos
    · obtain ⟨s, hs, hsneg⟩ := (cgoL_negSet_snoc (F i₁) l y).mp (hn hy)
      rw [hs.deriv]; exact ne_of_lt hsneg
  · rcases hsign with hp | hn
    · left; intro y hy
      obtain ⟨s, hs, hspos⟩ := (cgoL_posSet_snoc (F i₁) l y).mp (hp hy)
      rw [hs.deriv]; exact hspos
    · right; intro y hy
      obtain ⟨s, hs, hsneg⟩ := (cgoL_negSet_snoc (F i₁) l y).mp (hn hy)
      rw [hs.deriv]; exact hsneg

/-! ## 3. The two cases of the dichotomy, at a single parameter `l` -/

/-- The inverse-function formula for the chart, from its continuity on `I`: if the chart is a
left inverse of the reparametrisation `t ↦ Aend + (Bend - Aend) t` through `f l`, and `f l` has
nonvanishing derivative at the corresponding points of the fibre, then the chart has derivative
`(Bend - Aend) / (f l)'` there. -/
theorem cgoL_chart1_hasDerivAt (f : (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p+1) → ℝ)) (l : Fin p → ℝ)
    (hcts : ContinuousOn (chart1 f κ l) I)
    (hchar : ∀ t ∈ I, chart1 f κ l t ∈ fibre κ l ∧
      f l (chart1 f κ l t) = Aend κ f l + (Bend κ f l - Aend κ f l) * t)
    (hdiff : ∀ y ∈ fibre κ l, HasDerivAt (f l) (deriv (f l) y) y)
    (hne' : ∀ y ∈ fibre κ l, deriv (f l) y ≠ 0)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (chart1 f κ l)
      ((Bend κ f l - Aend κ f l) / deriv (f l) (chart1 f κ l t)) t := by
  have hmem : I ∈ nhds t := isOpen_Ioo.mem_nhds ht
  have hT : HasDerivAt (fun u : ℝ => Aend κ f l + (Bend κ f l - Aend κ f l) * u)
      (Bend κ f l - Aend κ f l) t := by
    have h := ((hasDerivAt_id t).const_mul (Bend κ f l - Aend κ f l)).const_add (Aend κ f l)
    have hv : (Bend κ f l - Aend κ f l) * 1 = Bend κ f l - Aend κ f l := by ring
    simpa [hv] using h
  refine HasDerivAt.of_comp_left (hcts.continuousAt hmem) (hdiff _ (hchar t ht).1) hT
    (hne' _ (hchar t ht).1) ?_
  filter_upwards [hmem] with u hu
  exact (hchar u hu).2

/-- The point (subsingleton fibre) case, at a single parameter `l`. -/
theorem cgoL_point_case {k : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ}
    {κ : Set (Fin (p+1) → ℝ)} {i₁ j : Fin k} (hκ : κ ⊆ strip p) (l : Fin p → ℝ)
    (hsub : (fibre κ l).Subsingleton) :
    (∀ t ∈ I, chart1 (F i₁) κ l t ∈ I) ∧
    (ContDiffOn ℝ 1 (fun t : ℝ => F j l (chart1 (F i₁) κ l t)) I ∧
      ∀ t ∈ I, |iteratedDeriv 1 (fun t : ℝ => F j l (chart1 (F i₁) κ l t)) t| ≤ 1) ∧
    (∀ x ∈ fibre κ l, ∃ t ∈ I, chart1 (F i₁) κ l t = x) :=
  ⟨fun t ht => cgoL_chart1_mem_I (F i₁) κ l hκ ht,
   ⟨contDiffOn_chart1_comp (F i₁) (F j) κ l hsub,
    fun t ht => by rw [iteratedDeriv_chart1_comp (F i₁) (F j) κ l hsub t]; norm_num⟩,
   chart1_surjOn_fibre (F i₁) κ l hsub⟩

/-- The interval case, at a single parameter `l`: the chart is the inverse branch of the
dominating member and every composite `F j l ∘ chart1` is `C¹` with derivative bounded by
`1`. -/
theorem cgoL_interval_case {k : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ}
    {κ : Set (Fin (p+1) → ℝ)} {i₁ j : Fin k}
    (hκ : κ ⊆ strip p) (hgood : GoodCell k F κ i₁)
    (l : Fin p → ℝ) (hi₁l : ∀ x ∈ I, F i₁ l x ∈ I) {a b : ℝ} (hfab : fibre κ l = Set.Ioo a b)
    (hne : (fibre κ l).Nonempty) :
    (∀ t ∈ I, chart1 (F i₁) κ l t ∈ I) ∧
    (ContDiffOn ℝ 1 (fun t : ℝ => F j l (chart1 (F i₁) κ l t)) I ∧
      ∀ t ∈ I, |iteratedDeriv 1 (fun t : ℝ => F j l (chart1 (F i₁) κ l t)) t| ≤ 1) ∧
    (∀ x ∈ fibre κ l, ∃ t ∈ I, chart1 (F i₁) κ l t = x) := by
  obtain ⟨hd1, hne', hsgn, hd2⟩ := cgoL_slice_data_sign hgood hgood.2.2.2.1 l
  -- monotonicity of the dominating member and the shape of the image of the fibre
  obtain ⟨hmono, himg, hAB, hA0, hB1, -⟩ :=
    cgo_fibre_mono_image (F i₁) κ l hκ hfab hne
      (fun y hy => (hd1 y hy).1.differentiableAt) hsgn hi₁l
  -- the chart is the unique preimage of the reparametrised value
  obtain ⟨hchar, hsurj⟩ := cgo_chart1_char (F i₁) κ l hfab hne hmono himg hAB
  -- its regularity and derivative
  obtain ⟨hcts, hdψ⟩ := cgo_chart1_contDiffOn (F i₁) κ l hfab hne hmono hchar
    (fun y hy => (hd1 y hy).1) hne'
  have hABabs : |Bend κ (F i₁) l - Aend κ (F i₁) l| ≤ 1 := by
    rw [abs_of_pos (sub_pos.mpr hAB)]
    linarith
  -- the chain rule and the bound
  obtain ⟨hcd, hbound⟩ := cgo_chart1_comp_contDiff (F i₁) (F j) κ l hcts
    (fun t ht => (hchar t ht).1) hdψ
    (fun y hy => (hd2 y hy j).1)
    (fun y hy => (hd1 y hy).1)
    (fun y hy => (hd2 y hy j).2.1.continuousWithinAt)
    (fun y hy => (hd1 y hy).2.continuousWithinAt)
    hne'
    (fun y hy => (hd2 y hy j).2.2)
    hABabs
  exact ⟨fun t ht => cgoL_chart1_mem_I (F i₁) κ l hκ ht, ⟨hcd, hbound⟩, hsurj⟩

/-! ## 4. The statement -/

theorem lipschitz_chart_good_on (p k : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p+1) → ℝ)) (i₁ j : Fin k) (Λ : Set (Fin p → ℝ))
    (hκ : κ ⊆ Work.WilG4a.strip p) (hgood : Work.WilG4a.GoodCell k F κ i₁)
    (hz : ∀ z ∈ κ, Work.WilG4a.xDeriv (F i₁) z ≠ 0)
    (hi₁ : ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i₁ l x ∈ Work.WilG4a.I)
    (hj : ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F j l x ∈ Work.WilG4a.I) :
    (∀ l ∈ Λ, ∀ t ∈ Work.WilG4a.I, Work.WilG4a.chart1 (F i₁) κ l t ∈ Work.WilG4a.I) ∧
    (∀ l ∈ Λ, ContDiffOn ℝ 1 (fun t : ℝ => F j l (Work.WilG4a.chart1 (F i₁) κ l t)) Work.WilG4a.I ∧
      ∀ t ∈ Work.WilG4a.I, |iteratedDeriv 1 (fun t : ℝ => F j l (Work.WilG4a.chart1 (F i₁) κ l t)) t| ≤ 1) ∧
    (∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.fibre κ l, ∃ t ∈ Work.WilG4a.I, Work.WilG4a.chart1 (F i₁) κ l t = x) := by
  have hcase : ∀ l ∈ Λ, (∀ t ∈ I, chart1 (F i₁) κ l t ∈ I) ∧
      (ContDiffOn ℝ 1 (fun t : ℝ => F j l (chart1 (F i₁) κ l t)) I ∧
        ∀ t ∈ I, |iteratedDeriv 1 (fun t : ℝ => F j l (chart1 (F i₁) κ l t)) t| ≤ 1) ∧
      (∀ x ∈ fibre κ l, ∃ t ∈ I, chart1 (F i₁) κ l t = x) := by
    intro l hl
    by_cases hne : (fibre κ l).Nonempty
    · rcases hgood.2.2.2.2 l with hsub | ⟨a, b, hfab⟩
      · exact cgoL_point_case hκ l hsub
      · exact cgoL_interval_case hκ hgood l (hi₁ l hl) hfab hne
    · have hempty : fibre κ l = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      exact cgoL_point_case hκ l (by rw [hempty]; exact Set.subsingleton_empty)
  exact ⟨fun l hl t ht => (hcase l hl).1 t ht,
    fun l hl => (hcase l hl).2.1,
    fun l hl x hx => (hcase l hl).2.2 x hx⟩

end Work.WilG4a
