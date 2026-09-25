import Mathlib
import Submission.Work.NN.Final.fiber_holder_le
import Submission.Work.CR.Flat.Cauchy.dbarTransform_basic
import Submission.Work.CR.Flat.Cauchy.isClosedForm_iteratedFDeriv
import Submission.Work.NN.Core.TelTwoDF.contDiff_dbarTransform_univ
import Submission.Work.NN.Core.transform_fderiv

/-!
# `C^{k,α}`-bounds for the one-variable Cauchy transform on the tracked polydisc

The Cauchy-type transform `dbarTransform ρ j g z = -(1/π) ∫_{‖w‖<ρ} g (z + w e_j)/w dw`
is bounded on the tracked polydisc `trackSet = {z | ∀ l, ‖z l‖ < trTrack}` in terms of the
`C^{k,α}`-norm of `g` *on `trackSet`*, for data `g` which vanish beyond the strip
`‖y j‖ ≤ cutOut`.

The point of the `trackSet`-form of the bound (as opposed to the `Set.univ` form) is that the
transform at a point `z ∈ trackSet` only ever reads `g` on the tube where the coordinates `l ≠ j`
are tracked, so the `j`-th coordinate is the only one that has to be dealt with separately.
This is exactly what the case analysis of `fiber_holder_le` provides.
-/

namespace Work.NN.Final

open scoped NNReal ENNReal
open Set MeasureTheory
open Work.CR.Flat.Cauchy (dbarTransform)

/-- The tracked polydisc is open. -/
lemma isOpen_trackSet {n : ℕ} : IsOpen (Work.CR.Flat.Cauchy.trackSet : Set (Fin n → ℂ)) := by
  have h : (Work.CR.Flat.Cauchy.trackSet : Set (Fin n → ℂ))
      = ⋂ l, {z : Fin n → ℂ | ‖z l‖ < Work.CR.Flat.Cauchy.trTrack} := by
    ext z; simp [Work.CR.Flat.Cauchy.trackSet]
  rw [h]
  exact isOpen_iInter_of_finite (fun l => isOpen_lt (continuous_apply l).norm continuous_const)

/-! ## Auxiliary: the transform preserves the `trackSet` bounds -/

/-- **Bounds for `dbarTransform trRho j f` on `trackSet`**, for data vanishing strictly beyond
the strip `‖y j‖ ≤ cutOut`.  This is `dbarTransform_basic` with threshold `b = cutOut + 1/32`
(which lies strictly between `cutOut = 7/8` and `trTrack = 15/16`), so that a slice point whose
non-`j` coordinates are tracked and whose `j`-coordinate is at most `b` is in `trackSet`; the
fibre pair hypothesis is `fiber_holder_le`. -/
theorem dbarTransform_track_bounds_aux {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {j : Fin n}
    {f : (Fin n → ℂ) → ℂ} {A H : ℝ} (hA0 : 0 ≤ A) (hH0 : 0 ≤ H)
    (hf : Continuous f)
    (hvan : ∀ y : Fin n → ℂ, Work.CR.Flat.Cauchy.cutOut < ‖y j‖ → f y = 0)
    (hsup : ∀ z : Fin n → ℂ, z ∈ Work.CR.Flat.Cauchy.trackSet → ‖f z‖ ≤ A)
    (hhol : ∀ x y : Fin n → ℂ, x ∈ Work.CR.Flat.Cauchy.trackSet →
      y ∈ Work.CR.Flat.Cauchy.trackSet → ‖f x - f y‖ ≤ H * ‖x - y‖ ^ α) :
    (∀ z : Fin n → ℂ, z ∈ Work.CR.Flat.Cauchy.trackSet →
      ‖dbarTransform Work.CR.Flat.Cauchy.trRho j f z‖
        ≤ 2 * Work.CR.Flat.Cauchy.trRho * A) ∧
    (∀ x y : Fin n → ℂ, x ∈ Work.CR.Flat.Cauchy.trackSet → y ∈ Work.CR.Flat.Cauchy.trackSet →
      ‖dbarTransform Work.CR.Flat.Cauchy.trRho j f x
        - dbarTransform Work.CR.Flat.Cauchy.trRho j f y‖
      ≤ 2 * Work.CR.Flat.Cauchy.trRho * (16 ^ α * (A + H)) * ‖x - y‖ ^ α) := by
  have hb : 0 ≤ Work.CR.Flat.Cauchy.cutOut + 1 / 32 := by
    rw [Work.CR.Flat.Cauchy.cutOut]; norm_num
  have hblt : Work.CR.Flat.Cauchy.cutOut + 1 / 32 < Work.CR.Flat.Cauchy.trTrack := by
    rw [Work.CR.Flat.Cauchy.cutOut, Work.CR.Flat.Cauchy.trTrack]; norm_num
  have hρ : 0 < Work.CR.Flat.Cauchy.trRho := by
    rw [Work.CR.Flat.Cauchy.trRho]; norm_num
  have hlt : Work.CR.Flat.Cauchy.cutOut < Work.CR.Flat.Cauchy.cutOut + 1 / 32 := by norm_num
  -- the threshold `b = cutOut + 1/32` is a vanishing threshold by `hvan`
  have hsupp : ∀ y : Fin n → ℂ, Work.CR.Flat.Cauchy.cutOut + 1 / 32 ≤ ‖y j‖ → f y = 0 :=
    fun y hy => hvan y (lt_of_lt_of_le hlt hy)
  -- slice points with `‖· j‖ ≤ b` whose non-`j` coordinates are tracked lie in `trackSet`
  have hfiber : ∀ z : Fin n → ℂ, z ∈ Work.CR.Flat.Cauchy.trackSet →
      ∀ y : Fin n → ℂ, (∀ l, l ≠ j → y l = z l) →
        ‖y j‖ ≤ Work.CR.Flat.Cauchy.cutOut + 1 / 32 → ‖f y‖ ≤ A := by
    intro z hz y hy hyj
    refine hsup y fun l => ?_
    by_cases hl : l = j
    · subst hl; exact lt_of_le_of_lt hyj hblt
    · rw [hy l hl]; exact hz l
  -- the fibre pair hypothesis
  have hpair : ∀ x : Fin n → ℂ, x ∈ Work.CR.Flat.Cauchy.trackSet →
      ∀ y : Fin n → ℂ, y ∈ Work.CR.Flat.Cauchy.trackSet →
      ∀ a a' : Fin n → ℂ, (∀ l, l ≠ j → a l = x l) → (∀ l, l ≠ j → a' l = y l) →
      ‖f a - f a'‖ ≤ 16 ^ α * (A + H) * ‖a - a'‖ ^ α := by
    intro x hx y hy a a' ha ha'
    refine fiber_holder_le hα0 (j := j) hA0 hH0 hvan hsup hhol a a' ?_ ?_
    · intro l hl; rw [ha l hl]; exact hx l
    · intro l hl; rw [ha' l hl]; exact hy l
  constructor
  · intro z hz
    exact (Work.CR.Flat.Cauchy.dbarTransform_basic (n := n) (ρ := Work.CR.Flat.Cauchy.trRho)
      (b := Work.CR.Flat.Cauchy.cutOut + 1 / 32) hρ hb (j := j)).1 hf hsupp A z (hfiber z hz)
  · intro x y hx hy
    exact (Work.CR.Flat.Cauchy.dbarTransform_basic (n := n) (ρ := Work.CR.Flat.Cauchy.trRho)
      (b := Work.CR.Flat.Cauchy.cutOut + 1 / 32) hρ hb (j := j)).2.1 hf hsupp α
      (16 ^ α * (A + H)) x y (hpair x hx y hy)

/-! ## The iterated derivatives of the transform -/

private lemma coe_succ (i : ℕ) : ((i + 1 : ℕ) : WithTop ℕ∞) = (i : WithTop ℕ∞) + 1 := by
  rw [Nat.cast_add, Nat.cast_one]

/-- A derivative of a function vanishing on a closed set vanishes in the open exterior. -/
private lemma iteratedFDeriv_eq_zero_of_fiberSupport {n : ℕ} {B : ℝ} (s : Fin n)
    {g : (Fin n → ℂ) → ℂ} (hsupp : ∀ y, B ≤ ‖y s‖ → g y = 0) (i : ℕ) :
    ∀ y : Fin n → ℂ, B < ‖y s‖ → iteratedFDeriv ℝ i g y = 0 := by
  have hclosed : IsClosed {y : Fin n → ℂ | ‖y s‖ ≤ B} :=
    isClosed_le ((continuous_apply s).norm) continuous_const
  have hsub : tsupport g ⊆ {y : Fin n → ℂ | ‖y s‖ ≤ B} := by
    refine closure_minimal (fun z hz => ?_) hclosed
    by_contra h
    exact hz (hsupp z (le_of_lt (lt_of_not_ge h)))
  intro y hy
  have h1 : y ∉ tsupport g := fun h => absurd (hsub h) (not_le.mpr hy)
  have h2 : y ∉ tsupport (iteratedFDeriv ℝ i g) :=
    fun h => h1 (tsupport_iteratedFDeriv_subset i h)
  by_contra hne
  exact h2 (subset_tsupport _ (Function.mem_support.mpr hne))

private lemma iteratedFDeriv_apply_eq_zero_of_fiberSupport {n : ℕ} {B : ℝ} (s : Fin n)
    {g : (Fin n → ℂ) → ℂ} (hsupp : ∀ y, B ≤ ‖y s‖ → g y = 0) (i : ℕ)
    (v : Fin i → (Fin n → ℂ)) {b : ℝ} (hb : B < b) :
    ∀ y : Fin n → ℂ, b ≤ ‖y s‖ → iteratedFDeriv ℝ i g y v = 0 := by
  intro y hy
  rw [iteratedFDeriv_eq_zero_of_fiberSupport s hsupp i y (lt_of_lt_of_le hb hy)]
  simp

private lemma contDiff_iteratedFDeriv_apply {n k i : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ k g) (hi : i + 1 ≤ k) (v : Fin i → (Fin n → ℂ)) :
    ContDiff ℝ 1 (fun y => iteratedFDeriv ℝ i g y v) := by
  have h2 : ContDiff ℝ 1 (iteratedFDeriv ℝ i g) :=
    hg.iteratedFDeriv_right (m := 1) (i := i) (by rw [add_comm]; exact_mod_cast hi)
  exact (ContinuousLinearMap.contDiff
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => (Fin n → ℂ)) ℂ v)).comp h2

private lemma continuous_iteratedFDeriv_apply {n k i : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ k g) (hi : i ≤ k) (v : Fin i → (Fin n → ℂ)) :
    Continuous (fun y => iteratedFDeriv ℝ i g y v) := by
  have h2 : ContDiff ℝ 0 (iteratedFDeriv ℝ i g) :=
    hg.iteratedFDeriv_right (m := 0) (i := i) (by rw [zero_add]; exact_mod_cast hi)
  exact ((ContinuousLinearMap.contDiff
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => (Fin n → ℂ)) ℂ v)).comp h2).continuous

/-- **The Cauchy-type transform commutes with all iterated derivatives.** -/
private lemma iteratedFDeriv_dbarTransform_eq {n : ℕ} {ρ B : ℝ} (hB : 0 ≤ B) (s : Fin n)
    {k : ℕ} {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ k g) (hsupp : ∀ y, B ≤ ‖y s‖ → g y = 0) :
    ∀ (i : ℕ), i ≤ k → ∀ (v : Fin i → (Fin n → ℂ)) (z : Fin n → ℂ),
      iteratedFDeriv ℝ i (fun z => dbarTransform ρ s g z) z v
        = dbarTransform ρ s (fun y => iteratedFDeriv ℝ i g y v) z := by
  intro i
  induction i with
  | zero =>
      intro hi v z
      simp
  | succ i ih =>
      intro hi v z
      have hi' : i ≤ k := le_trans (Nat.le_succ i) hi
      have hgc : ContDiff ℝ (i + 1) g := hg.of_le (by exact_mod_cast hi)
      have hgd : ContDiff ℝ ((i : WithTop ℕ∞) + 1) g := hg.of_le (by exact_mod_cast hi)
      have hT : ContDiff ℝ ((i : WithTop ℕ∞) + 1) (fun z => dbarTransform ρ s g z) := by
        have h0 : ContDiff ℝ ((i + 1 : ℕ) : WithTop ℕ∞) (fun z => dbarTransform ρ s g z) :=
          Work.NN.Core.TelTwoDF.contDiff_dbarTransform_univ hB s (i + 1) hgc hsupp
        rwa [coe_succ i] at h0
      rw [Work.CR.Flat.Cauchy.iteratedFDeriv_succ_apply_eq_fderiv hT v z]
      have hfun : (fun t => iteratedFDeriv ℝ i (fun z => dbarTransform ρ s g z) t
            (Fin.tail v))
          = fun t => dbarTransform ρ s (fun y => iteratedFDeriv ℝ i g y (Fin.tail v)) t :=
        funext fun t => ih hi' (Fin.tail v) t
      rw [hfun, Work.NN.Core.transform_fderiv s
        (contDiff_iteratedFDeriv_apply hg hi (Fin.tail v)) z (v 0)]
      congr 1
      funext y
      rw [← Work.CR.Flat.Cauchy.iteratedFDeriv_succ_apply_eq_fderiv hgd v y]

/-! ## The main bound -/

/-- **The transform `dbarTransform trRho j` is bounded on the `C^{k,α}` scale on `trackSet`.**

For data `g` of class `C^k` vanishing beyond the strip `‖y j‖ ≤ cutOut`, the `C^{k,α}`-norm of
`dbarTransform trRho j g` on `trackSet` is bounded by a constant times the `C^{k,α}`-norm of `g`
on `trackSet`.

Route.  Every iterated derivative passes through the integral sign, so
`D^i (dbarTransform trRho j g)(z)[v] = dbarTransform trRho j (fun y => D^i g(y)[v])(z)`.
For the scalar datum `y ↦ D^i g(y)[v]`, vanishing beyond the strip with
`sup_{trackSet} |D^i g(·)[v]| ≤ A i · ∏‖v l‖` and `trackSet`-Hölder constant `K i · ∏‖v l‖`,
`dbarTransform_track_bounds_aux` bounds the transform pointwise and in Hölder fashion; taking
the operator norm over `v` and summing over `i ≤ k` gives the claim. -/
theorem dbarTransform_holderNorm_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : Fin n) (g : (Fin n → ℂ) → ℂ),
      ContDiff ℝ k g → (∀ y : Fin n → ℂ, Work.CR.Flat.Cauchy.cutOut ≤ ‖y j‖ → g y = 0) →
      Work.CR.Flat.holderNorm k α (Work.CR.Flat.Cauchy.dbarTransform Work.CR.Flat.Cauchy.trRho j g)
          Work.CR.Flat.Cauchy.trackSet
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm k α g Work.CR.Flat.Cauchy.trackSet := by
  refine ⟨2 * Work.CR.Flat.Cauchy.trRho + 2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α, ?_, ?_⟩
  · have h1 : (0 : ℝ) < Work.CR.Flat.Cauchy.trRho := by rw [Work.CR.Flat.Cauchy.trRho]; norm_num
    have h2 : (0 : ℝ) < 16 ^ α := Real.rpow_pos_of_pos (by norm_num) α
    positivity
  · intro j g hg hsupp
    have hρ : 0 < Work.CR.Flat.Cauchy.trRho := by
      rw [Work.CR.Flat.Cauchy.trRho]; norm_num
    have hB : 0 ≤ Work.CR.Flat.Cauchy.cutOut := by
      rw [Work.CR.Flat.Cauchy.cutOut]; norm_num
    have hΩ : IsOpen (Work.CR.Flat.Cauchy.trackSet : Set (Fin n → ℂ)) := isOpen_trackSet
    by_cases htop : Work.CR.Flat.holderNorm k α g Work.CR.Flat.Cauchy.trackSet = ⊤
    · rw [htop, ENNReal.mul_top]
      · exact le_top
      · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        have h1 : (0 : ℝ) < Work.CR.Flat.Cauchy.trRho := by
          rw [Work.CR.Flat.Cauchy.trRho]; norm_num
        have h2 : (0 : ℝ) < 16 ^ α := Real.rpow_pos_of_pos (by norm_num) α
        positivity
    · have hfin : Work.CR.Flat.holderNorm k α g Work.CR.Flat.Cauchy.trackSet < ⊤ :=
        lt_top_iff_ne_top.mpr htop
      have hAfin : ∀ i, i ≤ k →
          Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet < ⊤ := fun i hi =>
        lt_of_le_of_lt (Work.CR.Flat.iterDerivNorm_le_holderNorm k α g
          Work.CR.Flat.Cauchy.trackSet hi) hfin
      have hKfin : ∀ i, i ≤ k →
          Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet < ⊤ := fun i hi =>
        lt_of_le_of_lt (Work.CR.Flat.holderSeminorm_le_holderNorm k α g
          Work.CR.Flat.Cauchy.trackSet hi) hfin
      let A : ℕ → ℝ := fun i =>
        (Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet).toReal
      let K : ℕ → ℝ := fun i =>
        (Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet).toReal
      have hAeq : ∀ i (hi : i ≤ k),
          ENNReal.ofReal (A i) = Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet :=
        fun i hi => ENNReal.ofReal_toReal (ne_top_of_lt (hAfin i hi))
      have hKeq : ∀ i (hi : i ≤ k),
          ENNReal.ofReal (K i) = Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet :=
        fun i hi => ENNReal.ofReal_toReal (ne_top_of_lt (hKfin i hi))
      have hAnn : ∀ i, 0 ≤ A i := fun i => ENNReal.toReal_nonneg
      have hKnn : ∀ i, 0 ≤ K i := fun i => ENNReal.toReal_nonneg
      have hAb : ∀ i, i ≤ k → ∀ y : Fin n → ℂ, y ∈ Work.CR.Flat.Cauchy.trackSet →
          ‖iteratedFDeriv ℝ i g y‖ ≤ A i := by
        intro i hi y hy
        have h1 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ i g Work.CR.Flat.Cauchy.trackSet y‖
            ≤ Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet := by
          rw [Work.CR.Flat.iterDerivNorm]
          exact le_iSup₂_of_le y hy le_rfl
        rw [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
          (s := Work.CR.Flat.Cauchy.trackSet) (f := g) i hΩ) hy] at h1
        rw [← hAeq i hi] at h1
        exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h1
      have hKb : ∀ i, i ≤ k → ∀ x : Fin n → ℂ, x ∈ Work.CR.Flat.Cauchy.trackSet →
          ∀ y : Fin n → ℂ, y ∈ Work.CR.Flat.Cauchy.trackSet →
          ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ ≤ K i * ‖x - y‖ ^ α := by
        intro i hi x hx y hy
        rcases eq_or_ne x y with rfl | hne
        · simp [Real.zero_rpow (ne_of_gt hα0)]
        · have h1 : ENNReal.ofReal
              (‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ / ‖x - y‖ ^ α)
              ≤ Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet := by
            have h := Work.CR.Flat.le_holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet hx hy hne
            rwa [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
                (s := Work.CR.Flat.Cauchy.trackSet) (f := g) i hΩ) hx,
              (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
                (s := Work.CR.Flat.Cauchy.trackSet) (f := g) i hΩ) hy] at h
          rw [← hKeq i hi] at h1
          have h2 := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h1
          have hpos : 0 < ‖x - y‖ ^ α :=
            Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) α
          rwa [div_le_iff₀ hpos] at h2
      -- the two bounds for the scalar datum `y ↦ D^i g y v`
      have hT : ∀ i, i ≤ k → ∀ v : Fin i → (Fin n → ℂ),
          (∀ z : Fin n → ℂ, z ∈ Work.CR.Flat.Cauchy.trackSet →
            ‖dbarTransform Work.CR.Flat.Cauchy.trRho j
                (fun y => iteratedFDeriv ℝ i g y v) z‖
              ≤ 2 * Work.CR.Flat.Cauchy.trRho * (A i * ∏ l, ‖v l‖)) ∧
          (∀ x y : Fin n → ℂ, x ∈ Work.CR.Flat.Cauchy.trackSet →
            y ∈ Work.CR.Flat.Cauchy.trackSet →
            ‖dbarTransform Work.CR.Flat.Cauchy.trRho j
                (fun y' => iteratedFDeriv ℝ i g y' v) x
              - dbarTransform Work.CR.Flat.Cauchy.trRho j
                (fun y' => iteratedFDeriv ℝ i g y' v) y‖
              ≤ 2 * Work.CR.Flat.Cauchy.trRho *
                  (16 ^ α * ((A i * ∏ l, ‖v l‖) + (K i * ∏ l, ‖v l‖)))
                  * ‖x - y‖ ^ α) := by
        intro i hi v
        have hP : 0 ≤ ∏ l, ‖v l‖ := Finset.prod_nonneg fun l _ => norm_nonneg _
        have hc : Continuous (fun y : Fin n → ℂ => iteratedFDeriv ℝ i g y v) :=
          continuous_iteratedFDeriv_apply hg hi v
        have hvan' : ∀ y : Fin n → ℂ, Work.CR.Flat.Cauchy.cutOut < ‖y j‖ →
            iteratedFDeriv ℝ i g y v = 0 := fun y hy => by
          rw [iteratedFDeriv_eq_zero_of_fiberSupport j hsupp i y hy]; simp
        have hsup' : ∀ z : Fin n → ℂ, z ∈ Work.CR.Flat.Cauchy.trackSet →
            ‖iteratedFDeriv ℝ i g z v‖ ≤ A i * ∏ l, ‖v l‖ := by
          intro z hz
          calc ‖iteratedFDeriv ℝ i g z v‖ ≤ ‖iteratedFDeriv ℝ i g z‖ * ∏ l, ‖v l‖ :=
                ContinuousMultilinearMap.le_opNorm _ _
            _ ≤ A i * ∏ l, ‖v l‖ := mul_le_mul_of_nonneg_right (hAb i hi z hz) hP
        have hhol' : ∀ x y : Fin n → ℂ, x ∈ Work.CR.Flat.Cauchy.trackSet →
            y ∈ Work.CR.Flat.Cauchy.trackSet →
            ‖iteratedFDeriv ℝ i g x v - iteratedFDeriv ℝ i g y v‖
              ≤ (K i * ∏ l, ‖v l‖) * ‖x - y‖ ^ α := by
          intro x y hx hy
          have h1 : ‖(iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y) v‖
              ≤ ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ * ∏ l, ‖v l‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
          rw [ContinuousMultilinearMap.sub_apply] at h1
          calc ‖iteratedFDeriv ℝ i g x v - iteratedFDeriv ℝ i g y v‖
              ≤ ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ * ∏ l, ‖v l‖ := h1
            _ ≤ (K i * ‖x - y‖ ^ α) * ∏ l, ‖v l‖ :=
                mul_le_mul_of_nonneg_right (hKb i hi x hx y hy) hP
            _ = (K i * ∏ l, ‖v l‖) * ‖x - y‖ ^ α := by ring
        exact dbarTransform_track_bounds_aux hα0 hα1 (mul_nonneg (hAnn i) hP)
          (mul_nonneg (hKnn i) hP) hc hvan' hsup' hhol'
      -- the iterated derivative bounds
      have hcomm : ∀ i, i ≤ k → ∀ (v : Fin i → (Fin n → ℂ)) (z : Fin n → ℂ),
          iteratedFDeriv ℝ i (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z) z v
            = dbarTransform Work.CR.Flat.Cauchy.trRho j
                (fun y => iteratedFDeriv ℝ i g y v) z :=
        fun i hi v z => iteratedFDeriv_dbarTransform_eq hB j hg hsupp i hi v z
      have hN : ∀ i, i ≤ k →
          Work.CR.Flat.iterDerivNorm i
              (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z)
              Work.CR.Flat.Cauchy.trackSet
            ≤ ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho) *
                Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet := by
        intro i hi
        rw [Work.CR.Flat.iterDerivNorm]
        refine iSup₂_le fun x hx => ?_
        rw [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
          (s := Work.CR.Flat.Cauchy.trackSet)
          (f := fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z) i hΩ) hx]
        have hbnd : ‖iteratedFDeriv ℝ i
              (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z) x‖
            ≤ 2 * Work.CR.Flat.Cauchy.trRho * A i := by
          refine ContinuousMultilinearMap.opNorm_le_bound (M := 2 * Work.CR.Flat.Cauchy.trRho * A i)
            (by positivity) fun v => ?_
          have hP : 0 ≤ ∏ l, ‖v l‖ := Finset.prod_nonneg fun l _ => norm_nonneg _
          calc ‖iteratedFDeriv ℝ i (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z) x v‖
              = ‖dbarTransform Work.CR.Flat.Cauchy.trRho j
                  (fun y => iteratedFDeriv ℝ i g y v) x‖ := by rw [hcomm i hi v x]
            _ ≤ 2 * Work.CR.Flat.Cauchy.trRho * (A i * ∏ l, ‖v l‖) := (hT i hi v).1 x hx
            _ = 2 * Work.CR.Flat.Cauchy.trRho * A i * ∏ l, ‖v l‖ := by ring
        calc ENNReal.ofReal ‖iteratedFDeriv ℝ i
              (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z) x‖
            ≤ ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho * A i) :=
              ENNReal.ofReal_le_ofReal hbnd
          _ = ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho) * ENNReal.ofReal (A i) :=
              ENNReal.ofReal_mul (by positivity)
          _ = ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho) *
              Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet := by rw [hAeq i hi]
      have hH : ∀ i, i ≤ k →
          Work.CR.Flat.holderSeminorm i α
              (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z)
              Work.CR.Flat.Cauchy.trackSet
            ≤ ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α) *
                (Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet
                  + Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet) := by
        intro i hi
        rw [Work.CR.Flat.holderSeminorm]
        refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
        rw [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
              (s := Work.CR.Flat.Cauchy.trackSet)
              (f := fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z) i hΩ) hx,
            (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
              (s := Work.CR.Flat.Cauchy.trackSet)
              (f := fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z) i hΩ) hy]
        have hbnd : ‖iteratedFDeriv ℝ i
              (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z) x
            - iteratedFDeriv ℝ i
              (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z) y‖
            ≤ (2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α * (A i + K i)) * ‖x - y‖ ^ α := by
          refine ContinuousMultilinearMap.opNorm_le_bound
            (M := (2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α * (A i + K i)) * ‖x - y‖ ^ α)
            (by positivity) fun v => ?_
          have hP : 0 ≤ ∏ l, ‖v l‖ := Finset.prod_nonneg fun l _ => norm_nonneg _
          rw [ContinuousMultilinearMap.sub_apply, hcomm i hi v x, hcomm i hi v y]
          calc ‖dbarTransform Work.CR.Flat.Cauchy.trRho j
                  (fun y' => iteratedFDeriv ℝ i g y' v) x
                - dbarTransform Work.CR.Flat.Cauchy.trRho j
                  (fun y' => iteratedFDeriv ℝ i g y' v) y‖
              ≤ 2 * Work.CR.Flat.Cauchy.trRho *
                  (16 ^ α * ((A i * ∏ l, ‖v l‖) + (K i * ∏ l, ‖v l‖))) * ‖x - y‖ ^ α :=
                (hT i hi v).2 x y hx hy
            _ = (2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α * (A i + K i) * ‖x - y‖ ^ α)
                  * ∏ l, ‖v l‖ := by ring
        have hpos : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
        calc ENNReal.ofReal (‖iteratedFDeriv ℝ i
              (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z) x
            - iteratedFDeriv ℝ i
              (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z) y‖ / ‖x - y‖ ^ α)
            ≤ ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α * (A i + K i)) :=
              ENNReal.ofReal_le_ofReal (by rw [div_le_iff₀ hpos]; exact hbnd)
          _ = ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α) *
                ENNReal.ofReal (A i + K i) :=
              ENNReal.ofReal_mul (by positivity)
          _ = ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α) *
                (ENNReal.ofReal (A i) + ENNReal.ofReal (K i)) := by
              rw [ENNReal.ofReal_add (hAnn i) (hKnn i)]
          _ = ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α) *
                (Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet
                  + Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet) := by
              rw [hAeq i hi, hKeq i hi]
      -- assembly
      have hstep : ∀ i ∈ Finset.range (k + 1),
          (Work.CR.Flat.iterDerivNorm i
              (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z)
              Work.CR.Flat.Cauchy.trackSet
            + Work.CR.Flat.holderSeminorm i α
              (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z)
              Work.CR.Flat.Cauchy.trackSet)
          ≤ ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho + 2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α)
              * (Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet
                + Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet) := by
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hle : Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet
            ≤ Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet
              + Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet :=
          le_add_right le_rfl
        calc Work.CR.Flat.iterDerivNorm i
              (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z)
              Work.CR.Flat.Cauchy.trackSet
            + Work.CR.Flat.holderSeminorm i α
              (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z)
              Work.CR.Flat.Cauchy.trackSet
            ≤ ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho) *
                (Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet
                  + Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet)
              + ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α) *
                (Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet
                  + Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet) :=
              add_le_add (le_trans (hN i hik) (mul_le_mul_right hle _)) (hH i hik)
          _ = (ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho)
                + ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α)) *
                (Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet
                  + Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet) := by
              rw [add_mul]
          _ = ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho + 2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α)
                * (Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet
                  + Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet) := by
              rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      calc Work.CR.Flat.holderNorm k α
            (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z)
            Work.CR.Flat.Cauchy.trackSet
          = ∑ i ∈ Finset.range (k + 1),
              (Work.CR.Flat.iterDerivNorm i
                  (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z)
                  Work.CR.Flat.Cauchy.trackSet
                + Work.CR.Flat.holderSeminorm i α
                  (fun z => dbarTransform Work.CR.Flat.Cauchy.trRho j g z)
                  Work.CR.Flat.Cauchy.trackSet) := rfl
        _ ≤ ∑ i ∈ Finset.range (k + 1),
              ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho
                  + 2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α)
                * (Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet
                  + Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet) :=
              Finset.sum_le_sum hstep
        _ = ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho
              + 2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α)
              * ∑ i ∈ Finset.range (k + 1),
                (Work.CR.Flat.iterDerivNorm i g Work.CR.Flat.Cauchy.trackSet
                  + Work.CR.Flat.holderSeminorm i α g Work.CR.Flat.Cauchy.trackSet) := by
              rw [Finset.mul_sum]
        _ = ENNReal.ofReal (2 * Work.CR.Flat.Cauchy.trRho
              + 2 * Work.CR.Flat.Cauchy.trRho * 16 ^ α)
              * Work.CR.Flat.holderNorm k α g Work.CR.Flat.Cauchy.trackSet := rfl

end Work.NN.Final
