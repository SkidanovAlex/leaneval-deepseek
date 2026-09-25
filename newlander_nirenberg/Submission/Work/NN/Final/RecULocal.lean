/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `recU` construction with data closed only on a polydisc

The explicit solution operator `Work.CR.Flat.Cauchy.recU` of the flat `∂̄`-equation on the unit
polydisc is developed in `Work/CR/Flat/Cauchy/openSolRec.lean` under the hypothesis that the
datum is *globally* closed (`Work.CR.Flat.IsClosedForm`).  For the assembly of the Newlander-
Nirenberg development we need the same construction for data which is only closed on a polydisc
(the datum is a cutoff of the local data, hence globally smooth but only locally closed).

This module provides:

* `recF_contDiff` -- the intermediate data `recF f s j` are `C^{k+1}` whenever the datum is
  (no closedness needed);
* `recF_inv_local` -- the invariants of the recursion, with the closedness invariant restricted
  to the polydisc `‖z‖ ≤ R`;
* `recU_solves_local` -- the equation `∂̄_j (recU f) = f_j` on the polydisc of radius `eqRad`,
  for data closed on `‖z‖ ≤ R`.

All the constants (`cutIn`, `cutOut`, `trRho`, `eqRad`) are the ones of the library.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolRec

noncomputable section

open scoped NNReal ENNReal ContDiff
open MeasureTheory Set

namespace Work.NN.Final

open Work.CR.Flat Work.CR.Flat.Cauchy

variable {n : ℕ}

/-- Any finite smoothness level is below the `C^∞` level `∞`. -/
private lemma le_infty (m : ℕ) : (m : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
  exact_mod_cast le_top

/-- The intermediate data of the recursion are `C^{k+1}` when the datum is: the first conjunct of
`Work.CR.Flat.Cauchy.recF_inv`, with the closedness hypothesis removed (the proof does not use it). -/
theorem recF_contDiff {n : ℕ} {k : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ (k + 1) (f j)) :
    ∀ s ≤ n, ∀ j, ContDiff ℝ (k + 1) (recF f s j) := by
  intro s
  induction s with
  | zero => intro _; simpa using hf
  | succ s ihs =>
      intro hs
      have ih1 : ∀ i, ContDiff ℝ (k + 1) (recF f s i) := ihs (by omega)
      by_cases hlt : s < n
      · set j : Fin n := ⟨s, hlt⟩ with hj
        have hrec : recF f (s + 1) = stepData j (recF f s) := recF_succ_of_lt f hlt
        intro i
        rw [hrec]
        simp only [stepData]
        exact contDiff_dbarTransform (b := cutOut) (by norm_num [cutOut, trRho]) j (k + 1)
          (((contDiff_cutFbar j).of_le (le_infty _)).mul (ih1 i))
          (fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul])
      · have hrec : recF f (s + 1) = recF f s := by
          rw [recF_succ]; simp [hlt]
        intro i
        rw [hrec]
        exact ih1 i



/-! ## The transform depends only on the fibre -/

/-- The Cauchy-type transform `dbarTransform ρ j` depends only on the values of its datum on the
fibre `z + w e_j`, `‖w‖ < ρ`. -/
lemma dbarTransform_congr {n : ℕ} {ρ : ℝ} {j : Fin n} {G H : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (h : ∀ w : ℂ, ‖w‖ < ρ → G (z + Function.update (0 : Fin n → ℂ) j w)
      = H (z + Function.update (0 : Fin n → ℂ) j w)) :
    dbarTransform ρ j G z = dbarTransform ρ j H z := by
  simp only [dbarTransform]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with w hw
  rw [h w (by simpa [dist_eq_norm] using hw)]

/-- The invariants of the recursion, with the closedness of the datum assumed only on the polydisc
`∀ m, ‖z m‖ < R` (where `cutOut < R`). -/
lemma recF_inv_local {n : ℕ} {k : ℕ} {R : ℝ} (hR : cutOut < R)
    {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ (k + 1) (f j))
    (hcl : ∀ j l z, (∀ m, ‖z m‖ < R) → dbarCoord l (f j) z = dbarCoord j (f l) z) :
    ∀ s : ℕ, s ≤ n →
      (∀ j, ContDiff ℝ (k + 1) (recF f s j)) ∧
      (∀ l : Fin n, (l : ℕ) < s → ∀ j z, ‖z l‖ < cutIn → dbarCoord l (recF f s j) z = 0) ∧
      (∀ i l : Fin n, s ≤ (i : ℕ) → s ≤ (l : ℕ) → ∀ z, (∀ m, ‖z m‖ < R) →
        dbarCoord l (recF f s i) z = dbarCoord i (recF f s l) z) := by
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
        have hrec : recF f (s + 1) = stepData j (recF f s) := recF_succ_of_lt f hlt
        have hC1 : ∀ i : Fin n, ContDiff ℝ 1 (fun y => cutFbar j y * recF f s i y) := fun i =>
          (((contDiff_cutFbar j).of_le (le_infty _)).mul (ih1 i)).of_le
            (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))
        have hsupp : ∀ y : Fin n → ℂ, cutOut ≤ ‖y j‖ → cutFbar j y = 0 :=
          fun y hy => cutFbar_eq_zero_of_ge hy
        refine ⟨?_, ?_, ?_⟩
        · intro i
          rw [hrec]
          simp only [stepData]
          exact contDiff_dbarTransform (b := cutOut) (by norm_num [cutOut, trRho]) j (k + 1)
            (((contDiff_cutFbar j).of_le (le_infty _)).mul (ih1 i))
            (fun y hy => by rw [hsupp y hy, zero_mul])
        · intro l hl i z hz
          rw [hrec]
          simp only [stepData]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt' | heq
          · have hne : l ≠ j := by
              intro hlj; rw [hlj, hjs] at hlt'; exact absurd hlt' (by omega)
            rw [dbarTransform_dbarCoord j l (hC1 i) z]
            rw [dbarTransform_eq_zero_of_fiber]
            intro y hy
            rw [dbarCoord_cutFbar_mul hne ((ih1 i).differentiable (by simp)).differentiableAt]
            have hyl : ‖y l‖ < cutIn := by rw [hy l hne]; exact hz
            rw [ih2 l hlt' i y hyl, mul_zero]
          · have hlj : l = j := by
              ext; rw [hjs]; exact heq
            subst hlj
            rw [dbarTransform_dbarCoord j j (hC1 i) z]
            have hz' : ‖z j‖ < trRho / 2 := by
              rw [← cutOut_eq_half_trRho]; exact lt_trans hz cutIn_lt_cutOut
            rw [dbarTransform_dbarCoord_self trRho_pos j (hC1 i)
              (fun y hy => by rw [← cutOut_eq_half_trRho] at hy; rw [hsupp y hy, zero_mul]) hz']
            rw [cutFbar_eq_zero_of_le (le_of_lt hz), zero_mul]
        · intro i l hi hl z hz
          rw [hrec]
          simp only [stepData]
          have hine : i ≠ j := by
            intro hij; rw [hij, hjs] at hi; exact absurd hi (by omega)
          have hlne : l ≠ j := by
            intro hlj; rw [hlj, hjs] at hl; exact absurd hl (by omega)
          rw [dbarTransform_dbarCoord j l (hC1 i) z,
            dbarTransform_dbarCoord j i (hC1 l) z]
          refine dbarTransform_congr (z := z) ?_
          intro w hw
          by_cases hcut : cutFbar j (z + Function.update (0 : Fin n → ℂ) j w) = 0
          · rw [dbarCoord_cutFbar_mul hlne ((ih1 i).differentiable (by simp)).differentiableAt,
              dbarCoord_cutFbar_mul hine ((ih1 l).differentiable (by simp)).differentiableAt,
              hcut, zero_mul, zero_mul]
          · have hyjlt : ‖(z + Function.update (0 : Fin n → ℂ) j w) j‖ < cutOut := by
              by_contra hcon
              exact hcut (cutFbar_eq_zero_of_ge (le_of_not_gt hcon))
            have hy' : ∀ m, ‖(z + Function.update (0 : Fin n → ℂ) j w) m‖ < R := by
              intro m
              by_cases hm : m = j
              · rw [hm]; exact lt_trans hyjlt hR
              · have hzm : (z + Function.update (0 : Fin n → ℂ) j w) m = z m := by
                  simp [Function.update_apply, hm]
                rw [hzm]; exact hz m
            rw [dbarCoord_cutFbar_mul hlne ((ih1 i).differentiable (by simp)).differentiableAt,
              dbarCoord_cutFbar_mul hine ((ih1 l).differentiable (by simp)).differentiableAt,
              ih3 i l (by omega) (by omega) (z + Function.update (0 : Fin n → ℂ) j w) hy']
      · have hrec : recF f (s + 1) = recF f s := by
          rw [recF_succ]; simp [hlt]
        have hsn : n ≤ s := not_lt.mp hlt
        rw [hrec]
        refine ⟨ih1, ?_, ?_⟩
        · intro l hl i z hz
          exact ih2 l (by omega) i z hz
        · intro i l hi hl z hz
          exact ih3 i l (by omega) (by omega) z hz



/-- The explicit solution `recU f` solves `∂̄_j u = f_j` on the polydisc `∀ l, ‖z l‖ < eqRad`
whenever the datum is closed on the polydisc `∀ m, ‖z m‖ < R` (with `cutOut < R`).  This is
`Work.CR.Flat.Cauchy.recU_solves` with the closedness of the datum localized; the only place where
the proof uses it as a *global* function identity is turned into a fibre-level argument, using that
the cutoff `cutF j` can only be nonzero at points of the polydisc on which the datum is closed. -/
theorem recU_solves_local {n : ℕ} {R : ℝ} (hR : cutOut < R)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf1 : ∀ j, ContDiff ℝ 1 (f j))
    (hcl : ∀ j l z, (∀ m, ‖z m‖ < R) → dbarCoord l (f j) z = dbarCoord j (f l) z) :
    ∀ (i : Fin n) (z : Fin n → ℂ), (∀ l, ‖z l‖ < eqRad) →
      dbarCoord i (fun z => recU f z) z = f i z := by
  intro i z hz
  -- data smoothness at every stage (no closedness needed)
  have hsm : ∀ (m : ℕ), m ≤ n → ∀ j, ContDiff ℝ 1 (recF f m j) :=
    fun m hm j => recF_contDiff hf1 m hm j
  have hC1 : ∀ (m : ℕ), m ≤ n → ∀ j i : Fin n,
      ContDiff ℝ 1 (fun y => cutF j y * recF f m i y) := fun m hm j i =>
    ((contDiff_cutF j).of_le (le_infty _)).mul (hsm m hm i)
  have hzlt : ∀ j : Fin n, ‖z j‖ < cutOut := fun j =>
    lt_trans (hz j) (lt_trans eqRad_lt_cutIn cutIn_lt_cutOut)
  -- the per-term computation
  have hterm : ∀ j : Fin n,
      dbarCoord i (fun z => dbarTransform trRho j (fun y => cutF j y * recF f (j : ℕ) j y) z) z
        = (if (j : ℕ) < (i : ℕ) then recF f (j : ℕ) i z - recF f ((j : ℕ) + 1) i z
           else if (j : ℕ) = (i : ℕ) then recF f (j : ℕ) i z else 0) := by
    intro j
    obtain ⟨hsmj, hholj, hclj⟩ := recF_inv_local hR hf1 hcl (j : ℕ) (le_of_lt j.isLt)
    have hsuppG : ∀ (i' : Fin n) (y : Fin n → ℂ), trRho / 2 ≤ ‖y j‖ →
        cutF j y * recF f (j : ℕ) i' y = 0 := by
      intro i' y hy
      rw [← cutOut_eq_half_trRho] at hy
      rw [cutF_eq_zero hy, zero_mul]
    by_cases hji : (j : ℕ) < (i : ℕ)
    · -- j < i
      have hij : i ≠ j := fun h => by rw [h] at hji; exact lt_irrefl _ hji
      have hCij : ContDiff ℝ 1 (fun y => cutF j y * recF f (j : ℕ) i y) :=
        hC1 (j : ℕ) (le_of_lt j.isLt) j i
      change dbarCoord i (dbarTransform trRho j (fun y => cutF j y * recF f (j : ℕ) j y)) z = _
      rw [if_pos hji, dbarTransform_dbarCoord j i
        (hC1 (j : ℕ) (le_of_lt j.isLt) j j) z]
      have hfun1 : (fun y => dbarCoord i (fun y' => cutF j y' * recF f (j : ℕ) j y') y)
          = fun y => cutF j y * dbarCoord i (recF f (j : ℕ) j) y := by
        funext y
        rw [Work.CR.Flat.Polydisc.dbarCoord_mul i _ _ y
              ((contDiff_cutF j).contDiffAt.differentiableAt (by simp))
              ((hsmj j).differentiable (by simp)).differentiableAt,
          dbarCoord_cutF_eq_zero hij y, zero_mul, zero_add]
      rw [hfun1]
      -- the (localized) closedness rewrite, at the level of the fibre
      have hclfun : dbarTransform trRho j (fun y => cutF j y * dbarCoord i (recF f (j : ℕ) j) y) z
          = dbarTransform trRho j (fun y => cutF j y * dbarCoord j (recF f (j : ℕ) i) y) z := by
        refine dbarTransform_congr (z := z) ?_
        intro w hw
        by_cases hcut : cutF j (z + Function.update (0 : Fin n → ℂ) j w) = 0
        · rw [hcut, zero_mul, zero_mul]
        · have hyjlt : ‖(z + Function.update (0 : Fin n → ℂ) j w) j‖ < cutOut := by
            by_contra hcon
            exact hcut (cutF_eq_zero (le_of_not_gt hcon))
          have hy' : ∀ m, ‖(z + Function.update (0 : Fin n → ℂ) j w) m‖ < R := by
            intro m
            by_cases hm : m = j
            · rw [hm]; exact lt_trans hyjlt hR
            · have hzm : (z + Function.update (0 : Fin n → ℂ) j w) m = z m := by
                simp [Function.update_apply, hm]
              rw [hzm]
              exact lt_trans (hz m) (lt_trans eqRad_lt_cutIn (lt_trans cutIn_lt_cutOut hR))
          rw [hclj j i le_rfl (le_of_lt hji) (z + Function.update (0 : Fin n → ℂ) j w) hy']
      rw [hclfun]
      have hfun2 : (fun y => cutF j y * dbarCoord j (recF f (j : ℕ) i) y)
          = fun y => dbarCoord j (fun y' => cutF j y' * recF f (j : ℕ) i y') y
              - cutFbar j y * recF f (j : ℕ) i y := by
        funext y
        rw [Work.CR.Flat.Polydisc.dbarCoord_mul j _ _ y
              ((contDiff_cutF j).contDiffAt.differentiableAt (by simp))
              ((hsmj i).differentiable (by simp)).differentiableAt,
          dbarCoord_cutF j y]
        ring
      have hcontA : Continuous
          (fun y => dbarCoord j (fun y' => cutF j y' * recF f (j : ℕ) i y') y) := by
        have hfd : Continuous (fderiv ℝ (fun y' => cutF j y' * recF f (j : ℕ) i y')) :=
          hCij.continuous_fderiv one_ne_zero
        unfold dbarCoord
        exact continuous_const.mul ((hfd.clm_apply continuous_const).add
          (continuous_const.mul (hfd.clm_apply continuous_const)))
      rw [hfun2,
        dbarTransform_basic (ρ := trRho) (b := cutOut) trRho_pos (le_of_lt cutOut_pos)
          |>.2.2
          (g := fun y => dbarCoord j (fun y' => cutF j y' * recF f (j : ℕ) i y') y)
          (g' := fun y => cutFbar j y * recF f (j : ℕ) i y)
          (hcontA)
          ((((contDiff_cutFbar j).of_le (le_infty _)).mul (hsmj i)).continuous)
          (fun y hy => by
            show dbarCoord j (fun y' => cutF j y' * recF f (j : ℕ) i y') y = 0
            rw [Work.CR.Flat.Polydisc.dbarCoord_mul j _ _ y
                  ((contDiff_cutF j).contDiffAt.differentiableAt (by simp))
                  ((hsmj i).differentiable (by simp)).differentiableAt,
              dbarCoord_cutF j y, cutFbar_eq_zero_of_ge hy, cutF_eq_zero hy]
            ring)
          (fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul])]
      rw [dbarTransform_dbarCoord_self trRho_pos j hCij (hsuppG i) (by
        rw [← cutOut_eq_half_trRho]; exact hzlt j)]
      have hstep : dbarTransform trRho j (fun y => cutFbar j y * recF f (j : ℕ) i y) z
          = recF f ((j : ℕ) + 1) i z := by
        rw [recF_succ_of_lt f j.isLt]
        rfl
      rw [hstep, cutF_eq_one (le_of_lt (lt_trans (hz j) eqRad_lt_cutIn)), one_mul]
      try ring
    · by_cases hje : (j : ℕ) = (i : ℕ)
      · rw [if_neg hji, if_pos hje]
        have hji' : j = i := Fin.ext hje
        have hdat : (fun y => cutF j y * recF f (j : ℕ) j y)
            = (fun y => cutF i y * recF f (i : ℕ) i y) := by rw [hji']
        rw [hdat, hji']
        have hsuppi : ∀ y : Fin n → ℂ, trRho / 2 ≤ ‖y i‖ →
            cutF i y * recF f (i : ℕ) i y = 0 := by
          intro y hy
          rw [← cutOut_eq_half_trRho] at hy
          rw [cutF_eq_zero hy, zero_mul]
        rw [dbarTransform_dbarCoord i i (hC1 (i : ℕ) (le_of_lt i.isLt) i i) z,
          dbarTransform_dbarCoord_self trRho_pos i
            (hC1 (i : ℕ) (le_of_lt i.isLt) i i) hsuppi (by
              rw [← cutOut_eq_half_trRho]; exact hzlt i),
          cutF_eq_one (le_of_lt (lt_trans (hz i) eqRad_lt_cutIn)), one_mul]
      · rw [if_neg hji, if_neg hje]
        have hne : i ≠ j := fun hij => by
          apply hje
          rw [← hij]
        change dbarCoord i (dbarTransform trRho j (fun y => cutF j y * recF f (j : ℕ) j y)) z = _
        rw [dbarTransform_dbarCoord j i (hC1 (j : ℕ) (le_of_lt j.isLt) j j) z]
        have hfun1 : (fun y => dbarCoord i (fun y' => cutF j y' * recF f (j : ℕ) j y') y)
            = fun y => cutF j y * dbarCoord i (recF f (j : ℕ) j) y := by
          funext y
          rw [Work.CR.Flat.Polydisc.dbarCoord_mul i _ _ y
                ((contDiff_cutF j).contDiffAt.differentiableAt (by simp))
                ((hsmj j).differentiable (by simp)).differentiableAt,
            dbarCoord_cutF_eq_zero hne y, zero_mul, zero_add]
        rw [hfun1, dbarTransform_eq_zero_of_fiber]
        intro y hy
        have hyi : ‖y i‖ < cutIn := by
          rw [hy i hne]; exact lt_trans (hz i) eqRad_lt_cutIn
        rw [hholj i (by omega) j y hyi, mul_zero]
  -- assemble
  have hsum : dbarCoord i (fun z => recU f z) z
      = ∑ j : Fin n, dbarCoord i (fun z => dbarTransform trRho j
          (fun y => cutF j y * recF f (j : ℕ) j y) z) z := by
    rw [show (fun z => recU f z) = fun z => ∑ j : Fin n, dbarTransform trRho j
        (fun y => cutF j y * recF f (j : ℕ) j y) z from rfl]
    exact dbarCoord_finset_sum i Finset.univ
      (fun j z => dbarTransform trRho j (fun y => cutF j y * recF f (j : ℕ) j y) z) z
      (fun j _ => ((contDiff_dbarTransform (b := cutOut) (by norm_num [cutOut, trRho]) j 1
        (hC1 (j : ℕ) (le_of_lt j.isLt) j j)
        (fun y hy => by rw [cutF_eq_zero hy, zero_mul])).differentiable one_ne_zero).differentiableAt)
  rw [hsum]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Fin.sum_univ_eq_sum_range (fun m => if m < (i : ℕ) then recF f m i z - recF f (m + 1) i z
      else if m = (i : ℕ) then recF f m i z else 0) n]
  rw [← Finset.sum_range_add_sum_Ico (fun m => if m < (i : ℕ) then recF f m i z - recF f (m + 1) i z
      else if m = (i : ℕ) then recF f m i z else 0) i.isLt.le]
  rw [show (∑ m ∈ Finset.Ico (i : ℕ) n, (if m < (i : ℕ) then recF f m i z - recF f (m + 1) i z
        else if m = (i : ℕ) then recF f m i z else 0)) = recF f (i : ℕ) i z from by
    refine (Finset.sum_eq_single (i : ℕ) ?_ ?_).trans ?_
    · intro b hb hne
      have hb' : (i : ℕ) ≤ b := (Finset.mem_Ico.mp hb).1
      rw [if_neg (by omega), if_neg hne]
    · intro hi
      exact absurd (Finset.mem_Ico.mpr ⟨le_rfl, i.isLt⟩) hi
    · rw [if_neg (lt_irrefl (i : ℕ)), if_pos rfl]]
  rw [show (∑ m ∈ Finset.range (i : ℕ), (if m < (i : ℕ) then recF f m i z - recF f (m + 1) i z
        else if m = (i : ℕ) then recF f m i z else 0))
      = ∑ m ∈ Finset.range (i : ℕ), (recF f m i z - recF f (m + 1) i z) from
    Finset.sum_congr rfl (fun m hm => if_pos (Finset.mem_range.mp hm))]
  rw [Finset.sum_range_sub' (fun m => recF f m i z) (i : ℕ), recF_zero]
  ring



/-- The explicit solution is `C^{k+1}` for `C^{k+1}` data (no closedness needed): this is
`Work.CR.Flat.Cauchy.contDiff_recU` with the closedness hypothesis removed. -/
lemma contDiff_recU' {n : ℕ} {k : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ (k + 1) (f j)) :
    ContDiff ℝ (k + 1) (fun z => recU f z) := by
  have hinv := recF_contDiff (k := k) hf
  rw [show (fun z => recU f z) = fun z => ∑ j : Fin n,
      dbarTransform trRho j (fun y => cutF j y * recF f (j : ℕ) j y) z from rfl]
  refine ContDiff.sum fun j _ => ?_
  refine contDiff_dbarTransform (b := cutOut) (by norm_num [cutOut, trRho]) j (k + 1) ?_ ?_
  · exact ((contDiff_cutF j).of_le (le_infty _)).mul (hinv (j : ℕ) (le_of_lt j.isLt) j)
  · intro y hy; rw [cutF_eq_zero hy, zero_mul]

/-! ## Linearity of `recU` for continuous data -/

/-- The recursion data at every stage are continuous when the datum is. -/
lemma recF_continuous {n : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) : ∀ s ≤ n, ∀ k, Continuous (recF f s k) := by
  intro s
  induction s with
  | zero => intro _ k; simpa using hf k
  | succ s ihs =>
      intro hs k
      have ih1 : ∀ i, Continuous (recF f s i) := ihs (by omega)
      by_cases hlt : s < n
      · set j : Fin n := ⟨s, hlt⟩ with hj
        have hrec : recF f (s + 1) = stepData j (recF f s) := recF_succ_of_lt f hlt
        rw [hrec]
        simp only [stepData]
        have hcont : Continuous (fun y => cutFbar j y * recF f s k y) :=
          (contDiff_cutFbar j).continuous.mul (ih1 k)
        have h0 : ContDiff ℝ 0 (dbarTransform trRho j (fun y => cutFbar j y * recF f s k y)) :=
          contDiff_dbarTransform (b := cutOut) (by norm_num [cutOut, trRho]) j 0
            (contDiff_zero.mpr hcont)
            (fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul])
        exact h0.continuous
      · have hrec : recF f (s + 1) = recF f s := by
          rw [recF_succ]; simp [hlt]
        rw [hrec]
        exact ih1 k

/-- `dbarTransform` is additive in its datum, for continuous data. -/
lemma dbarTransform_add {n : ℕ} {ρ : ℝ} (j : Fin n) {g g' : (Fin n → ℂ) → ℂ}
    (hg : Continuous g) (hg' : Continuous g') (z : Fin n → ℂ) :
    dbarTransform ρ j (fun y => g y + g' y) z = dbarTransform ρ j g z + dbarTransform ρ j g' z := by
  have h1 : IntegrableOn (fun w : ℂ => g (z + Function.update (0 : Fin n → ℂ) j w) / w)
      (Metric.ball (0 : ℂ) ρ) := integrableOn_dbarTransform_integrand j hg z
  have h2 : IntegrableOn (fun w : ℂ => g' (z + Function.update (0 : Fin n → ℂ) j w) / w)
      (Metric.ball (0 : ℂ) ρ) := integrableOn_dbarTransform_integrand j hg' z
  have hsplit : (∫ w in Metric.ball (0 : ℂ) ρ,
        (g (z + Function.update (0 : Fin n → ℂ) j w)
          + g' (z + Function.update (0 : Fin n → ℂ) j w)) / w)
      = (∫ w in Metric.ball (0 : ℂ) ρ, g (z + Function.update (0 : Fin n → ℂ) j w) / w)
        + (∫ w in Metric.ball (0 : ℂ) ρ, g' (z + Function.update (0 : Fin n → ℂ) j w) / w) := by
    rw [← integral_add h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    ring
  simp only [dbarTransform]
  rw [hsplit]
  ring

/-- `dbarTransform` is homogeneous in its datum, for continuous data. -/
lemma dbarTransform_smul {n : ℕ} {ρ : ℝ} (j : Fin n) (c : ℝ) {g : (Fin n → ℂ) → ℂ}
    (hg : Continuous g) (z : Fin n → ℂ) :
    dbarTransform ρ j (fun y => c • g y) z = c • dbarTransform ρ j g z := by
  have h1 : IntegrableOn (fun w : ℂ => g (z + Function.update (0 : Fin n → ℂ) j w) / w)
      (Metric.ball (0 : ℂ) ρ) := integrableOn_dbarTransform_integrand j hg z
  have hsplit : (∫ w in Metric.ball (0 : ℂ) ρ,
        (c • g (z + Function.update (0 : Fin n → ℂ) j w)) / w)
      = c • (∫ w in Metric.ball (0 : ℂ) ρ, g (z + Function.update (0 : Fin n → ℂ) j w) / w) := by
    rw [← MeasureTheory.integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Complex.real_smul]
    ring
  simp only [dbarTransform]
  rw [hsplit]
  simp only [Complex.real_smul]
  ring

/-- The intermediate data of the recursion are additive in the datum. -/
lemma recF_add {n : ℕ} {f g : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j)) :
    ∀ s ≤ n, ∀ k, (fun z => recF (fun j => f j + g j) s k z)
      = fun z => recF f s k z + recF g s k z := by
  intro s
  induction s with
  | zero => intro _ k; rfl
  | succ s ihs =>
      intro hs k
      have ih : ∀ k, (fun z => recF (fun j => f j + g j) s k z)
          = fun z => recF f s k z + recF g s k z := fun k => ihs (by omega) k
      by_cases hlt : s < n
      · set j : Fin n := ⟨s, hlt⟩ with hj
        rw [recF_succ_of_lt _ hlt, recF_succ_of_lt _ hlt, recF_succ_of_lt _ hlt]
        funext z
        simp only [stepData]
        rw [show (fun y => cutFbar j y * recF (fun j => f j + g j) s k y)
            = fun y => cutFbar j y * recF f s k y + cutFbar j y * recF g s k y from by
          funext y
          rw [congrFun (ih k) y]
          ring]
        exact dbarTransform_add j
          (((contDiff_cutFbar j).of_le (le_infty 0)).continuous.mul
            (recF_continuous hf s (by omega) k))
          (((contDiff_cutFbar j).of_le (le_infty 0)).continuous.mul
            (recF_continuous hg s (by omega) k)) z
      · have hrec : ∀ h : Fin n → (Fin n → ℂ) → ℂ, recF h (s + 1) = recF h s := by
          intro h; rw [recF_succ]; simp [hlt]
        rw [hrec, hrec, hrec]
        exact ih k

/-- The intermediate data of the recursion are homogeneous in the datum. -/
lemma recF_smul {n : ℕ} (c : ℝ) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) :
    ∀ s ≤ n, ∀ k, (fun z => recF (c • f) s k z) = fun z => c • recF f s k z := by
  intro s
  induction s with
  | zero => intro _ k; rfl
  | succ s ihs =>
      intro hs k
      have ih : ∀ k, (fun z => recF (c • f) s k z) = fun z => c • recF f s k z :=
        fun k => ihs (by omega) k
      by_cases hlt : s < n
      · set j : Fin n := ⟨s, hlt⟩ with hj
        rw [recF_succ_of_lt _ hlt, recF_succ_of_lt _ hlt]
        funext z
        simp only [stepData]
        rw [show (fun y => cutFbar j y * recF (c • f) s k y)
            = fun y => c • (cutFbar j y * recF f s k y) from by
          funext y
          rw [congrFun (ih k) y, Complex.real_smul, Complex.real_smul]
          ring]
        exact dbarTransform_smul j c
          (((contDiff_cutFbar j).of_le (le_infty 0)).continuous.mul
            (recF_continuous hf s (by omega) k)) z
      · have hrec : ∀ h : Fin n → (Fin n → ℂ) → ℂ, recF h (s + 1) = recF h s := by
          intro h; rw [recF_succ]; simp [hlt]
        rw [hrec, hrec]
        exact ih k

/-- `recU` is additive in its datum, for continuous data. -/
lemma recU_add {n : ℕ} {f g : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j)) :
    (fun z => recU (fun j => f j + g j) z) = fun z => recU f z + recU g z := by
  funext z
  rw [show recU (fun j => f j + g j) z = ∑ j : Fin n, dbarTransform trRho j
        (fun y => cutF j y * recF (fun j => f j + g j) (j : ℕ) j y) z from rfl,
    show recU f z = ∑ j : Fin n, dbarTransform trRho j
        (fun y => cutF j y * recF f (j : ℕ) j y) z from rfl,
    show recU g z = ∑ j : Fin n, dbarTransform trRho j
        (fun y => cutF j y * recF g (j : ℕ) j y) z from rfl,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (fun y => cutF j y * recF (fun j => f j + g j) (j : ℕ) j y)
      = fun y => cutF j y * recF f (j : ℕ) j y + cutF j y * recF g (j : ℕ) j y from by
    funext y
    rw [congrFun (recF_add hf hg (j : ℕ) (le_of_lt j.isLt) j) y]
    ring]
  exact dbarTransform_add j
    (((contDiff_cutF j).of_le (le_infty 0)).continuous.mul
      (recF_continuous hf (j : ℕ) (le_of_lt j.isLt) j))
    (((contDiff_cutF j).of_le (le_infty 0)).continuous.mul
      (recF_continuous hg (j : ℕ) (le_of_lt j.isLt) j)) z

/-- `recU` is homogeneous in its datum, for continuous data. -/
lemma recU_smul {n : ℕ} (c : ℝ) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, Continuous (f j)) :
    (fun z => recU (c • f) z) = fun z => c • recU f z := by
  funext z
  rw [show recU (c • f) z = ∑ j : Fin n, dbarTransform trRho j
        (fun y => cutF j y * recF (c • f) (j : ℕ) j y) z from rfl,
    show recU f z = ∑ j : Fin n, dbarTransform trRho j
        (fun y => cutF j y * recF f (j : ℕ) j y) z from rfl,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (fun y => cutF j y * recF (c • f) (j : ℕ) j y)
      = fun y => c • (cutF j y * recF f (j : ℕ) j y) from by
    funext y
    rw [congrFun (recF_smul c hf (j : ℕ) (le_of_lt j.isLt) j) y, Complex.real_smul, Complex.real_smul]
    ring]
  exact dbarTransform_smul j c
    (((contDiff_cutF j).of_le (le_infty 0)).continuous.mul
      (recF_continuous hf (j : ℕ) (le_of_lt j.isLt) j)) z

end Work.NN.Final
