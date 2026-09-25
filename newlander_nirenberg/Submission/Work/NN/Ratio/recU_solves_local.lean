/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The telescoping solution solves `∂̄u = f` when the datum is closed only on a polydisc

`Work.NN.Ratio.recU_solves` proves `∂̄_i (G.recU f) = f i` on the polydisc of radius `G.e`
under the hypothesis that the datum `f` is *globally* closed
(`Work.CR.Flat.IsClosedForm f`).  For the Newlander--Nirenberg application one only knows that
`f` is closed on a polydisc of radius `R > G.b`, and this is what is proved here.

The proof follows the same telescoping computation, but the closedness invariant of the
recursion is only available on the polydisc `∀ m, ‖z m‖ < R`, so every place where the global
proof of `recU_solves` used closedness as an identity of *functions* is replaced by a
fibre-level argument: the transform `dbarTransform G.r j` only sees its datum on the fibre
`z + w e_j`, and on that fibre the cutoff `G.cutF j` (respectively `G.cutFbar j`) can only be
nonzero at points of the polydisc `∀ m, ‖z m‖ < R` because `G.b < R`.

The main result is `Work.NN.Ratio.recU_solves_local`.
-/
import Mathlib
import Submission.Work.NN.Ratio.Defs
import Submission.Work.NN.Ratio.recF_inv

noncomputable section

open scoped NNReal ENNReal ContDiff
open MeasureTheory Set

namespace Work.NN.Ratio

variable {n : ℕ}

/-! ## Elementary consequences of the thresholds of `Geom` -/

private lemma r_pos_local (G : Geom n) : 0 < G.r := by linarith [G.hr, G.ha, G.hab]

private lemma b_lt_r' (G : Geom n) : G.b < G.r := by linarith [G.hr, G.hr0]

private lemma b_pos' (G : Geom n) : 0 < G.b := lt_trans G.ha G.hab

private lemma b_le_half_r' (G : Geom n) : G.b ≤ G.r / 2 := by linarith [G.hr]

/-! ## The transform only depends on the values of the datum on the fibre -/

/-- The Cauchy-type transform `dbarTransform ρ j` depends only on the values of its datum on the
fibre `z + w e_j`, `‖w‖ < ρ`. -/
lemma dbarTransform_congr {ρ : ℝ} {j : Fin n} {F H : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (h : ∀ w : ℂ, ‖w‖ < ρ →
      F (z + Function.update (0 : Fin n → ℂ) j w) = H (z + Function.update (0 : Fin n → ℂ) j w)) :
    Work.CR.Flat.Cauchy.dbarTransform ρ j F z = Work.CR.Flat.Cauchy.dbarTransform ρ j H z := by
  simp only [Work.CR.Flat.Cauchy.dbarTransform]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with w hw
  rw [h w (by simpa [dist_eq_norm] using hw)]

/-! ## Smoothness of the recursion without closedness -/

/-- The intermediate data of the recursion are `C^{k+1}` when the datum is: the first conjunct of
the invariants of `Work.NN.Ratio.recF_inv`, with the closedness hypothesis removed (the proof of
the smoothness part does not use it). -/
lemma recF_contDiff (G : Geom n) {k : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ (k + 1) (f j)) :
    ∀ s ≤ n, ∀ j, ContDiff ℝ (k + 1) (G.recF f s j) := by
  intro s
  induction s with
  | zero => intro _; simpa using hf
  | succ s ihs =>
      intro hs
      have ih1 : ∀ i, ContDiff ℝ (k + 1) (G.recF f s i) := ihs (by omega)
      by_cases hlt : s < n
      · set j : Fin n := ⟨s, hlt⟩ with hj
        have hrec : G.recF f (s + 1) = G.stepData j (G.recF f s) := G.recF_succ_of_lt hlt
        intro i
        rw [hrec]
        simp only [Geom.stepData]
        exact Work.CR.Flat.Cauchy.contDiff_dbarTransform (b := G.b) (b_lt_r' G) j (k + 1)
          (((Geom.contDiff_cutFbar (G := G) j).of_le (le_infty _)).mul (ih1 i))
          (fun y hy => by rw [Geom.cutFbar_eq_zero_of_ge (G := G) hy, zero_mul])
      · have hrec : G.recF f (s + 1) = G.recF f s := by
          rw [Geom.recF_succ (G := G)]; simp [hlt]
        intro i
        rw [hrec]
        exact ih1 i

/-! ## The invariants of the recursion with local closedness -/

/-- **Invariants of the telescoping recursion, with the closedness of the datum assumed only on a
polydisc.**  For `R > G.b` and a datum which is `C^{k+1}` and closed on the polydisc
`∀ m, ‖z m‖ < R`, at every stage `s ≤ n`:

* the data are still `C^{k+1}`;
* they are `∂̄_l`-holomorphic in every already processed direction `l < s` on the region
  `‖z l‖ < G.a` on which the cutoff is identically `1`;
* they are closed for every pair of not yet processed directions `i, l ≥ s` on the polydisc
  `∀ m, ‖z m‖ < R`. -/
lemma recF_inv_local (G : Geom n) {k : ℕ} {R : ℝ} (hR : G.b < R)
    {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ (k + 1) (f j))
    (hcl : ∀ j l (z : Fin n → ℂ), (∀ m, ‖z m‖ < R) →
      Work.CR.Flat.dbarCoord l (f j) z = Work.CR.Flat.dbarCoord j (f l) z) :
    ∀ s : ℕ, s ≤ n →
      (∀ j, ContDiff ℝ (k + 1) (G.recF f s j)) ∧
      (∀ l : Fin n, (l : ℕ) < s → ∀ j z, ‖z l‖ < G.a →
        Work.CR.Flat.dbarCoord l (G.recF f s j) z = 0) ∧
      (∀ i l : Fin n, s ≤ (i : ℕ) → s ≤ (l : ℕ) → ∀ z, (∀ m, ‖z m‖ < R) →
        Work.CR.Flat.dbarCoord l (G.recF f s i) z
          = Work.CR.Flat.dbarCoord i (G.recF f s l) z) := by
  intro s
  induction s with
  | zero =>
      intro _
      refine ⟨hf, ?_, ?_⟩
      · intro l hl; exact absurd hl (Nat.not_lt_zero _)
      · intro i l _ _ z hz; exact hcl i l z hz
  | succ s ihs =>
      intro hs
      obtain ⟨ih1, ih2, ih3⟩ := ihs (by omega)
      by_cases hlt : s < n
      · set j : Fin n := ⟨s, hlt⟩ with hj
        have hjs : (j : ℕ) = s := rfl
        have hrec : G.recF f (s + 1) = G.stepData j (G.recF f s) := G.recF_succ_of_lt hlt
        have hC1 : ∀ i : Fin n, ContDiff ℝ 1 (fun y => G.cutFbar j y * G.recF f s i y) := fun i =>
          (((Geom.contDiff_cutFbar (G := G) j).of_le (le_infty _)).mul (ih1 i)).of_le
            (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))
        have hsupp : ∀ y : Fin n → ℂ, G.b ≤ ‖y j‖ → G.cutFbar j y = 0 :=
          fun y hy => Geom.cutFbar_eq_zero_of_ge (G := G) hy
        refine ⟨?_, ?_, ?_⟩
        · -- smoothness at the next stage
          intro i
          rw [hrec]
          simp only [Geom.stepData]
          exact Work.CR.Flat.Cauchy.contDiff_dbarTransform (b := G.b) (b_lt_r' G) j (k + 1)
            (((Geom.contDiff_cutFbar (G := G) j).of_le (le_infty _)).mul (ih1 i))
            (fun y hy => by rw [hsupp y hy, zero_mul])
        · -- holomorphy in the processed directions
          intro l hl i z hz
          rw [hrec]
          simp only [Geom.stepData]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt' | heq
          · -- `l` was already processed before
            have hne : l ≠ j := by
              intro hlj; rw [hlj, hjs] at hlt'; exact absurd hlt' (by omega)
            rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord j l (hC1 i) z]
            rw [Work.CR.Flat.Cauchy.dbarTransform_eq_zero_of_fiber]
            intro y hy
            rw [Geom.dbarCoord_cutFbar_mul (G := G) hne
              ((ih1 i).differentiable (by simp)).differentiableAt]
            have hyl : ‖y l‖ < G.a := by rw [hy l hne]; exact hz
            rw [ih2 l hlt' i y hyl, mul_zero]
          · -- `l = j` is the new direction
            have hlj : l = j := by ext; rw [hjs]; exact heq
            subst hlj
            rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord j j (hC1 i) z]
            have hz' : ‖z j‖ < G.r / 2 := lt_of_lt_of_le (lt_trans hz G.hab) (b_le_half_r' G)
            rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord_self (r_pos_local G) j (hC1 i)
              (fun y hy => by
                rw [hsupp y (le_trans (b_le_half_r' G) hy), zero_mul]) hz']
            rw [Geom.cutFbar_eq_zero_of_le (G := G) (le_of_lt hz), zero_mul]
        · -- closedness is preserved for the unprocessed directions
          intro i l hi hl z hz
          rw [hrec]
          simp only [Geom.stepData]
          have hine : i ≠ j := by
            intro hij; rw [hij, hjs] at hi; exact absurd hi (by omega)
          have hlne : l ≠ j := by
            intro hlj; rw [hlj, hjs] at hl; exact absurd hl (by omega)
          rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord j l (hC1 i) z,
            Work.CR.Flat.Cauchy.dbarTransform_dbarCoord j i (hC1 l) z]
          refine dbarTransform_congr (z := z) ?_
          intro w hw
          by_cases hcut : G.cutFbar j (z + Function.update (0 : Fin n → ℂ) j w) = 0
          · rw [Geom.dbarCoord_cutFbar_mul (G := G) hlne
                ((ih1 i).differentiable (by simp)).differentiableAt,
              Geom.dbarCoord_cutFbar_mul (G := G) hine
                ((ih1 l).differentiable (by simp)).differentiableAt,
              hcut, zero_mul, zero_mul]
          · have hyjlt : ‖(z + Function.update (0 : Fin n → ℂ) j w) j‖ < G.b := by
              by_contra hcon
              exact hcut (hsupp _ (le_of_not_gt hcon))
            have hy' : ∀ m, ‖(z + Function.update (0 : Fin n → ℂ) j w) m‖ < R := by
              intro m
              by_cases hm : m = j
              · rw [hm]; exact lt_trans hyjlt hR
              · have hzm : (z + Function.update (0 : Fin n → ℂ) j w) m = z m := by
                  simp [Function.update_apply, hm]
                rw [hzm]
                exact hz m
            rw [Geom.dbarCoord_cutFbar_mul (G := G) hlne
                  ((ih1 i).differentiable (by simp)).differentiableAt,
                Geom.dbarCoord_cutFbar_mul (G := G) hine
                  ((ih1 l).differentiable (by simp)).differentiableAt,
              ih3 i l (by omega) (by omega) (z + Function.update (0 : Fin n → ℂ) j w) hy']
      · -- all coordinates have been processed: nothing changes any more
        have hrec : G.recF f (s + 1) = G.recF f s := by
          rw [Geom.recF_succ (G := G)]; simp [hlt]
        have hsn : n ≤ s := not_lt.mp hlt
        rw [hrec]
        refine ⟨ih1, ?_, ?_⟩
        · intro l hl i z hz
          exact ih2 l (by omega) i z hz
        · intro i l hi hl z hz
          exact ih3 i l (by omega) (by omega) z hz


/-- **The explicit solution `G.recU f` solves `∂̄ u = f` on the polydisc of radius `G.e` when the
datum is closed only on the polydisc `∀ m, ‖z m‖ < R`, `G.b < R`.**

This is `Work.NN.Ratio.recU_solves` with the closedness of the datum localized: the telescoping
computation is unchanged, but the two places where the global proof used closedness as an identity
of functions are turned into fibre-level arguments, using that the cutoffs `G.cutF j`, `G.cutFbar j`
vanish outside `‖·_j‖ < G.b < R`. -/
theorem recU_solves_local {n : ℕ} (G : Work.NN.Ratio.Geom n) {R : ℝ} (hR : G.b < R)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf1 : ∀ j, ContDiff ℝ 1 (f j))
    (hcl : ∀ j l (z : Fin n → ℂ), (∀ m, ‖z m‖ < R) →
      Work.CR.Flat.dbarCoord l (f j) z = Work.CR.Flat.dbarCoord j (f l) z) :
    ∀ (i : Fin n) (z : Fin n → ℂ), (∀ l, ‖z l‖ < G.e) →
      Work.CR.Flat.dbarCoord i (fun z => G.recU f z) z = f i z := by
  intro i z hz
  -- smoothness of the data at every stage
  have hsm : ∀ (m : ℕ), m ≤ n → ∀ j, ContDiff ℝ 1 (G.recF f m j) :=
    fun m hm j => recF_contDiff (G := G) hf1 m hm j
  have hC1 : ∀ (m : ℕ), m ≤ n → ∀ j i : Fin n,
      ContDiff ℝ 1 (fun y => G.cutF j y * G.recF f m i y) := fun m hm j i =>
    ((Geom.contDiff_cutF (G := G) j).of_le (le_infty _)).mul (hsm m hm i)
  have hzlt : ∀ j : Fin n, ‖z j‖ < G.b := fun j =>
    lt_trans (hz j) (lt_trans G.hea G.hab)
  -- the per-term computation
  have hterm : ∀ j : Fin n,
      Work.CR.Flat.dbarCoord i (fun z => Work.CR.Flat.Cauchy.dbarTransform G.r j
          (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z) z
        = (if (j : ℕ) < (i : ℕ) then G.recF f (j : ℕ) i z - G.recF f ((j : ℕ) + 1) i z
           else if (j : ℕ) = (i : ℕ) then G.recF f (j : ℕ) i z else 0) := by
    intro j
    obtain ⟨hsmj, hholj, hclj⟩ := recF_inv_local (G := G) hR hf1 hcl (j : ℕ) (le_of_lt j.isLt)
    have hsuppG : ∀ (i' : Fin n) (y : Fin n → ℂ), G.r / 2 ≤ ‖y j‖ →
        G.cutF j y * G.recF f (j : ℕ) i' y = 0 := by
      intro i' y hy
      rw [G.cutF_eq_zero (le_trans (b_le_half_r' G) hy), zero_mul]
    by_cases hji : (j : ℕ) < (i : ℕ)
    · -- `j < i`: the term is the difference of two successive stages
      have hij : i ≠ j := fun h => by rw [h] at hji; exact lt_irrefl _ hji
      have hCij : ContDiff ℝ 1 (fun y => G.cutF j y * G.recF f (j : ℕ) i y) :=
        hC1 (j : ℕ) (le_of_lt j.isLt) j i
      change Work.CR.Flat.dbarCoord i (Work.CR.Flat.Cauchy.dbarTransform G.r j
          (fun y => G.cutF j y * G.recF f (j : ℕ) j y)) z = _
      rw [if_pos hji, Work.CR.Flat.Cauchy.dbarTransform_dbarCoord j i
        (hC1 (j : ℕ) (le_of_lt j.isLt) j j) z]
      have hfun1 : (fun y => Work.CR.Flat.dbarCoord i
            (fun y' => G.cutF j y' * G.recF f (j : ℕ) j y') y)
          = fun y => G.cutF j y * Work.CR.Flat.dbarCoord i (G.recF f (j : ℕ) j) y := by
        funext y
        rw [Work.CR.Flat.Polydisc.dbarCoord_mul i _ _ y
              ((G.contDiff_cutF j).contDiffAt.differentiableAt (by simp))
              ((hsmj j).differentiable one_ne_zero).differentiableAt,
          G.dbarCoord_cutF_eq_zero hij y, zero_mul, zero_add]
      rw [hfun1]
      -- the closedness rewrite, at the level of the fibre through `z`
      have hclfun : Work.CR.Flat.Cauchy.dbarTransform G.r j
            (fun y => G.cutF j y * Work.CR.Flat.dbarCoord i (G.recF f (j : ℕ) j) y) z
          = Work.CR.Flat.Cauchy.dbarTransform G.r j
            (fun y => G.cutF j y * Work.CR.Flat.dbarCoord j (G.recF f (j : ℕ) i) y) z := by
        refine dbarTransform_congr (z := z) ?_
        intro w hw
        by_cases hcut : G.cutF j (z + Function.update (0 : Fin n → ℂ) j w) = 0
        · rw [hcut, zero_mul, zero_mul]
        · have hyjlt : ‖(z + Function.update (0 : Fin n → ℂ) j w) j‖ < G.b := by
            by_contra hcon
            exact hcut (G.cutF_eq_zero (le_of_not_gt hcon))
          have hy' : ∀ m, ‖(z + Function.update (0 : Fin n → ℂ) j w) m‖ < R := by
            intro m
            by_cases hm : m = j
            · rw [hm]; exact lt_trans hyjlt hR
            · have hzm : (z + Function.update (0 : Fin n → ℂ) j w) m = z m := by
                simp [Function.update_apply, hm]
              rw [hzm]
              exact lt_trans (hz m) (lt_trans G.hea (lt_trans G.hab hR))
          rw [hclj j i le_rfl (le_of_lt hji)
            (z + Function.update (0 : Fin n → ℂ) j w) hy']
      rw [hclfun]
      have hfun2 : (fun y => G.cutF j y * Work.CR.Flat.dbarCoord j (G.recF f (j : ℕ) i) y)
          = fun y => Work.CR.Flat.dbarCoord j
                (fun y' => G.cutF j y' * G.recF f (j : ℕ) i y') y
              - G.cutFbar j y * G.recF f (j : ℕ) i y := by
        funext y
        rw [Work.CR.Flat.Polydisc.dbarCoord_mul j _ _ y
              ((G.contDiff_cutF j).contDiffAt.differentiableAt (by simp))
              ((hsmj i).differentiable one_ne_zero).differentiableAt,
          G.dbarCoord_cutF j y]
        ring
      have hcontA : Continuous
          (fun y => Work.CR.Flat.dbarCoord j (fun y' => G.cutF j y' * G.recF f (j : ℕ) i y') y) := by
        have hfd : Continuous (fderiv ℝ (fun y' => G.cutF j y' * G.recF f (j : ℕ) i y')) :=
          hCij.continuous_fderiv one_ne_zero
        unfold Work.CR.Flat.dbarCoord
        exact continuous_const.mul ((hfd.clm_apply continuous_const).add
          (continuous_const.mul (hfd.clm_apply continuous_const)))
      rw [hfun2,
        Work.CR.Flat.Cauchy.dbarTransform_basic (ρ := G.r) (b := G.b)
            (r_pos_local G) (le_of_lt (b_pos' G)) |>.2.2
          (g := fun y => Work.CR.Flat.dbarCoord j
            (fun y' => G.cutF j y' * G.recF f (j : ℕ) i y') y)
          (g' := fun y => G.cutFbar j y * G.recF f (j : ℕ) i y)
          (hcontA)
          ((((G.contDiff_cutFbar j).of_le (le_infty 1)).mul (hsmj i)).continuous)
          (fun y hy => by
            show Work.CR.Flat.dbarCoord j (fun y' => G.cutF j y' * G.recF f (j : ℕ) i y') y = 0
            rw [Work.CR.Flat.Polydisc.dbarCoord_mul j _ _ y
                  ((G.contDiff_cutF j).contDiffAt.differentiableAt (by simp))
                  ((hsmj i).differentiable one_ne_zero).differentiableAt,
              G.dbarCoord_cutF j y, G.cutFbar_eq_zero_of_ge hy, G.cutF_eq_zero hy]
            ring)
          (fun y hy => by rw [G.cutFbar_eq_zero_of_ge hy, zero_mul])]
      rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord_self (r_pos_local G) j hCij (hsuppG i)
        (lt_of_lt_of_le (hzlt j) (b_le_half_r' G))]
      have hstep : Work.CR.Flat.Cauchy.dbarTransform G.r j
            (fun y => G.cutFbar j y * G.recF f (j : ℕ) i y) z
          = G.recF f ((j : ℕ) + 1) i z := by
        rw [G.recF_succ_of_lt j.isLt]
        rfl
      rw [hstep, G.cutF_eq_one (le_of_lt (lt_trans (hz j) G.hea)), one_mul]
      try ring
    · by_cases hje : (j : ℕ) = (i : ℕ)
      · -- `j = i`: the term contributes the datum itself
        rw [if_neg hji, if_pos hje]
        have hji' : j = i := Fin.ext hje
        have hdat : (fun y => G.cutF j y * G.recF f (j : ℕ) j y)
            = (fun y => G.cutF i y * G.recF f (i : ℕ) i y) := by rw [hji']
        rw [hdat, hji']
        have hsuppi : ∀ y : Fin n → ℂ, G.r / 2 ≤ ‖y i‖ →
            G.cutF i y * G.recF f (i : ℕ) i y = 0 := by
          intro y hy
          rw [G.cutF_eq_zero (le_trans (b_le_half_r' G) hy), zero_mul]
        rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord i i
            (hC1 (i : ℕ) (le_of_lt i.isLt) i i) z,
          Work.CR.Flat.Cauchy.dbarTransform_dbarCoord_self (r_pos_local G) i
            (hC1 (i : ℕ) (le_of_lt i.isLt) i i) hsuppi
            (lt_of_lt_of_le (hzlt i) (b_le_half_r' G)),
          G.cutF_eq_one (le_of_lt (lt_trans (hz i) G.hea)), one_mul]
      · -- `j > i`: the term vanishes
        rw [if_neg hji, if_neg hje]
        have hne : i ≠ j := fun hij => hje (by rw [hij])
        change Work.CR.Flat.dbarCoord i (Work.CR.Flat.Cauchy.dbarTransform G.r j
            (fun y => G.cutF j y * G.recF f (j : ℕ) j y)) z = _
        rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord j i
          (hC1 (j : ℕ) (le_of_lt j.isLt) j j) z]
        have hfun1 : (fun y => Work.CR.Flat.dbarCoord i
              (fun y' => G.cutF j y' * G.recF f (j : ℕ) j y') y)
            = fun y => G.cutF j y * Work.CR.Flat.dbarCoord i (G.recF f (j : ℕ) j) y := by
          funext y
          rw [Work.CR.Flat.Polydisc.dbarCoord_mul i _ _ y
                ((G.contDiff_cutF j).contDiffAt.differentiableAt (by simp))
                ((hsmj j).differentiable one_ne_zero).differentiableAt,
            G.dbarCoord_cutF_eq_zero hne y, zero_mul, zero_add]
        rw [hfun1, Work.CR.Flat.Cauchy.dbarTransform_eq_zero_of_fiber]
        intro y hy
        have hyi : ‖y i‖ < G.a := by rw [hy i hne]; exact lt_trans (hz i) G.hea
        rw [hholj i (by omega) j y hyi, mul_zero]
  -- assemble the sum
  have hsum : Work.CR.Flat.dbarCoord i (fun z => G.recU f z) z
      = ∑ j : Fin n, Work.CR.Flat.dbarCoord i (fun z => Work.CR.Flat.Cauchy.dbarTransform G.r j
          (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z) z := by
    rw [show (fun z => G.recU f z) = fun z => ∑ j : Fin n,
        Work.CR.Flat.Cauchy.dbarTransform G.r j
          (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z from rfl]
    exact Work.CR.Flat.Cauchy.dbarCoord_finset_sum i Finset.univ
      (fun j z => Work.CR.Flat.Cauchy.dbarTransform G.r j
        (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z) z
      (fun j _ => ((Work.CR.Flat.Cauchy.contDiff_dbarTransform (b := G.b) (b_lt_r' G) j 1
        (hC1 (j : ℕ) (le_of_lt j.isLt) j j)
        (fun y hy => by rw [G.cutF_eq_zero hy, zero_mul])).differentiable
          one_ne_zero).differentiableAt)
  rw [hsum]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Fin.sum_univ_eq_sum_range (fun m => if m < (i : ℕ) then
      G.recF f m i z - G.recF f (m + 1) i z
      else if m = (i : ℕ) then G.recF f m i z else 0) n]
  rw [← Finset.sum_range_add_sum_Ico (fun m => if m < (i : ℕ) then
      G.recF f m i z - G.recF f (m + 1) i z
      else if m = (i : ℕ) then G.recF f m i z else 0) i.isLt.le]
  rw [show (∑ m ∈ Finset.Ico (i : ℕ) n, (if m < (i : ℕ) then
        G.recF f m i z - G.recF f (m + 1) i z
        else if m = (i : ℕ) then G.recF f m i z else 0)) = G.recF f (i : ℕ) i z from by
    refine (Finset.sum_eq_single (i : ℕ) ?_ ?_).trans ?_
    · intro b hb hne
      have hb' : (i : ℕ) ≤ b := (Finset.mem_Ico.mp hb).1
      rw [if_neg (by omega), if_neg hne]
    · intro hi
      exact absurd (Finset.mem_Ico.mpr ⟨le_rfl, i.isLt⟩) hi
    · rw [if_neg (lt_irrefl (i : ℕ)), if_pos rfl]]
  rw [show (∑ m ∈ Finset.range (i : ℕ), (if m < (i : ℕ) then
        G.recF f m i z - G.recF f (m + 1) i z
        else if m = (i : ℕ) then G.recF f m i z else 0))
      = ∑ m ∈ Finset.range (i : ℕ), (G.recF f m i z - G.recF f (m + 1) i z) from
    Finset.sum_congr rfl (fun m hm => if_pos (Finset.mem_range.mp hm))]
  rw [Finset.sum_range_sub' (fun m => G.recF f m i z) (i : ℕ), G.recF_zero]
  ring

end Work.NN.Ratio
