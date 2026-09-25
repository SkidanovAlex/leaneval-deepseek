/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The explicit `(0,2)` `∂̄`-solver on the unit polydisc

This module sets up the coordinate-by-coordinate recursion that solves
`∂̄_j ψ_l - ∂̄_l ψ_j = η_{jl}` on `solveSet` for a `∂̄`-closed antisymmetric `(0,2)`-form
`η` on the unit polydisc, following the `(0,1)`-recursion `recF`/`recU` of
`Work/CR/Flat/Cauchy/openSolRec.lean`.

The state of the recursion is a family `D^{(s)} : Fin n → Fin n → (ℂⁿ → ℂ)` of `(0,2)`-forms;
`D^{(0)} = η` and, writing `c_s = cutF s`, `b_s = cutFbar s`,

  `D^{(s+1)}_{il} = (1 - c_s) D^{(s)}_{il}` for `i = s` or `l = s`,
  `D^{(s+1)}_{il} = (1 - c_s) D^{(s)}_{il} + T_s(b_s · D^{(s)}_{il})` otherwise,

where `T_s = dbarTransform trRho s` is the one-variable Cauchy transform.  The `(0,1)`-form
`Ψ^{(s)}` and the solution operator are

  `Ψ^{(s)}_l = T_s(c_s · D^{(s)}_{sl})`,   `S2 η = ∑_s Ψ^{(s)}`.

To make `S2` *linear* on all data (the Cauchy transform is defined by an integral, which is only
additive on integrable functions) we use a linear extension `dTLM s` of `T_s` from the subspace of
continuous functions; on continuous data it agrees with `dbarTransform`.

The main structural results are proved in this file; the `C^{0,α}` estimate and the smoothness
are delegated.
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Cauchy.openSolRec
import Submission.Work.NN.Final.RecULocal

noncomputable section
open scoped NNReal ENNReal ContDiff
open MeasureTheory Set

namespace Work.NN.Final
open Work.CR.Flat Work.CR.Flat.Cauchy

variable {n : ℕ}

/-! ## The Cauchy transform as a linear map -/

/-- The subspace of continuous functions on `ℂⁿ`. -/
def contSubTwo (n : ℕ) : Submodule ℝ ((Fin n → ℂ) → ℂ) where
  carrier := {g | Continuous g}
  zero_mem' := continuous_zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c x hx => hx.const_smul c

/-- The Cauchy transform `T_j` in the `j`-th coordinate, restricted to continuous functions. -/
noncomputable def dTLMcont (j : Fin n) : (contSubTwo n) →ₗ[ℝ] ((Fin n → ℂ) → ℂ) where
  toFun := fun g => dbarTransform trRho j g.1
  map_add' := by
    intro g h
    funext z
    exact dbarTransform_add j g.2 h.2 z
  map_smul' := by
    intro c g
    funext z
    exact dbarTransform_smul j c g.2 z

/-- The Cauchy transform `T_j = dbarTransform trRho j`, extended linearly to all functions. -/
noncomputable def dTLM (j : Fin n) : ((Fin n → ℂ) → ℂ) →ₗ[ℝ] ((Fin n → ℂ) → ℂ) :=
  (LinearMap.exists_extend (dTLMcont j)).choose

lemma dTLM_comp (j : Fin n) :
    (dTLM j).comp (contSubTwo n).subtype = dTLMcont j :=
  (LinearMap.exists_extend (dTLMcont j)).choose_spec

/-- On continuous functions the linear extension `dTLM` agrees with the Cauchy transform. -/
lemma dTLM_eq {j : Fin n} {g : (Fin n → ℂ) → ℂ} (hg : Continuous g) :
    dTLM j g = dbarTransform trRho j g := by
  have h := DFunLike.congr_fun (dTLM_comp j) (⟨g, hg⟩ : contSubTwo n)
  simpa [LinearMap.comp_apply, dTLMcont] using h

/-! ## The recursion -/

/-- One step of the `(0,2)`-recursion. -/
noncomputable def uStep (s : Fin n) (D : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    Fin n → Fin n → (Fin n → ℂ) → ℂ :=
  fun i l z => (1 - cutF s z) * D i l z
    + (if i = s ∨ l = s then 0 else dTLM s (fun y => cutFbar s y * D i l y) z)

/-- The `(0,2)`-data at stage `m` of the recursion. -/
noncomputable def uD (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) (m : ℕ) :
    Fin n → Fin n → (Fin n → ℂ) → ℂ :=
  Nat.rec η (fun m Dprev => if h : m < n then uStep ⟨m, h⟩ Dprev else Dprev) m

@[simp] lemma uD_zero (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) : uD η 0 = η := rfl

lemma uD_succ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) (m : ℕ) :
    uD η (m + 1) = if h : m < n then uStep ⟨m, h⟩ (uD η m) else uD η m := rfl

lemma uD_succ_of_lt (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) {m : ℕ} (h : m < n) :
    uD η (m + 1) = uStep ⟨m, h⟩ (uD η m) := by
  rw [uD_succ]; simp [h]

/-- The `(0,1)`-form produced at stage `s`. -/
noncomputable def uPsi (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) (s : Fin n) :
    Fin n → (Fin n → ℂ) → ℂ :=
  fun l => dTLM s (fun y => cutF s y * uD η (s : ℕ) s l y)

/-- The solution operator of the recursion. -/
noncomputable def uS2 (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) : Fin n → (Fin n → ℂ) → ℂ :=
  fun l => ∑ s : Fin n, uPsi η s l

/-! ## Elementary calculus helpers -/

lemma dbarCoord_neg' {n : ℕ} (a : Fin n) (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    dbarCoord a (fun w => - u w) z = - dbarCoord a u z := by
  rw [show (fun w => -u w) = -u from rfl, dbarCoord, fderiv_neg, dbarCoord]
  simp only [neg_apply]; ring

lemma dbarCoord_const' {n : ℕ} (a : Fin n) (c : ℂ) (z : Fin n → ℂ) :
    dbarCoord a (fun _ : Fin n → ℂ => c) z = 0 := by
  rw [dbarCoord, show (fun _ : Fin n → ℂ => c) = Function.const _ c from rfl, fderiv_const]
  simp

lemma dbarCoord_sub' {n : ℕ} (a : Fin n) {u v : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dbarCoord a (fun w => u w - v w) z = dbarCoord a u z - dbarCoord a v z := by
  have hfd : fderiv ℝ (fun w => u w - v w) z = fderiv ℝ u z - fderiv ℝ v z := fderiv_sub hu hv
  rw [dbarCoord, hfd]
  simp only [dbarCoord, sub_apply]
  ring

/-- `∂̄` of `1 - cutF s`: it is `-cutFbar s` in the `s`-th direction and vanishes in all
others. -/
lemma dbarCoord_one_sub_cutF {n : ℕ} (a s : Fin n) (z : Fin n → ℂ) :
    dbarCoord a (fun w => 1 - cutF s w) z = if a = s then - cutFbar s z else 0 := by
  have hdc : DifferentiableAt ℝ (fun _ : Fin n → ℂ => (1 : ℂ)) z := differentiableAt_const _
  have hds : DifferentiableAt ℝ (cutF s) z := (contDiff_cutF s).contDiffAt.differentiableAt (by simp)
  rw [dbarCoord_sub' a hdc hds, dbarCoord_const']
  by_cases h : a = s
  · subst h; rw [if_pos rfl, dbarCoord_cutF]; ring
  · rw [if_neg h, dbarCoord_cutF_eq_zero h]; ring

/-- `dTLM` of a `C¹` function supported in the inner disc is `C¹`. -/
lemma contDiff_dTLM {n : ℕ} {j : Fin n} {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ 1 g) (hsupp : ∀ y, cutOut ≤ ‖y j‖ → g y = 0) :
    ContDiff ℝ 1 (dTLM j g) := by
  rw [dTLM_eq hg.continuous]
  exact contDiff_dbarTransform (b := cutOut) (by norm_num [cutOut, trRho]) j 1 hg hsupp

/-! ## Regularity, antisymmetry and vanishing -/

@[simp] lemma uStep_apply {n : ℕ} (s : Fin n) (D : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (i l : Fin n) (z : Fin n → ℂ) :
    uStep s D i l z = (1 - cutF s z) * D i l z
      + (if i = s ∨ l = s then 0 else dTLM s (fun y => cutFbar s y * D i l y) z) := rfl

lemma uStep_contDiff {n : ℕ} {s : Fin n} {D : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hD : ∀ i l, ContDiff ℝ 1 (D i l)) (i l : Fin n) :
    ContDiff ℝ 1 (uStep s D i l) := by
  by_cases hc : i = s ∨ l = s
  · have hfun : uStep s D i l = fun z => (1 - cutF s z) * D i l z := by
      funext z; rw [uStep_apply, if_pos hc]; ring
    rw [hfun]
    exact ((contDiff_const.sub (contDiff_cutF s)).of_le (by exact_mod_cast le_top)).mul (hD i l)
  · have hfun : uStep s D i l = fun z => (1 - cutF s z) * D i l z
        + dTLM s (fun y => cutFbar s y * D i l y) z := by
      funext z; rw [uStep_apply, if_neg hc]
    rw [hfun]
    refine ContDiff.add (((contDiff_const.sub (contDiff_cutF s)).of_le (by exact_mod_cast le_top)).mul (hD i l)) ?_
    exact contDiff_dTLM (((contDiff_cutFbar s).of_le (by exact_mod_cast le_top)).mul (hD i l))
      (fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul])

lemma uD_contDiff {n : ℕ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l)) :
    ∀ m ≤ n, ∀ i l, ContDiff ℝ 1 (uD η m i l) := by
  intro m
  induction m with
  | zero => intro _; simpa using hη
  | succ m ih =>
      intro hm i l
      have hm' : m < n := by omega
      rw [uD_succ_of_lt η hm']
      exact uStep_contDiff (fun i l => ih (by omega) i l) i l

lemma uStep_antisymm {n : ℕ} {s : Fin n} {D : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hD : ∀ i l z, D i l z = - D l i z) (i l : Fin n) :
    ∀ z, uStep s D i l z = - uStep s D l i z := by
  intro z
  by_cases hc : i = s ∨ l = s
  · have hc' : l = s ∨ i = s := hc.symm
    rw [uStep_apply, uStep_apply, if_pos hc, if_pos hc', hD i l z]
    ring
  · have hc' : ¬ (l = s ∨ i = s) := by tauto
    rw [uStep_apply, uStep_apply, if_neg hc, if_neg hc']
    have h2 : (fun y => cutFbar s y * D i l y) = - (fun y => cutFbar s y * D l i y) := by
      funext y; simp only [Pi.neg_apply]; rw [hD i l y]; ring
    rw [h2, map_neg, hD i l z]
    simp only [Pi.neg_apply]; ring

lemma uD_antisymm {n : ℕ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l z, η i l z = - η l i z) :
    ∀ m i l z, uD η m i l z = - uD η m l i z := by
  intro m
  induction m with
  | zero => intro i l z; simpa using hη i l z
  | succ m ih =>
      intro i l z
      by_cases hm : m < n
      · rw [uD_succ_of_lt η hm]
        exact uStep_antisymm (fun i l z => ih i l z) i l z
      · rw [uD_succ]; simp only [hm, dite_false]; exact ih i l z

lemma uD_vanish {n : ℕ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l)) :
    ∀ m ≤ n, ∀ i l : Fin n, ((i : ℕ) < m ∨ (l : ℕ) < m) →
      ∀ z, (∀ k : Fin n, (k : ℕ) < m → ‖z k‖ < cutIn) → uD η m i l z = 0 := by
  intro m
  induction m with
  | zero => intro _ i l h; omega
  | succ m ih =>
      intro hm i l hlt z hz
      have hm' : m < n := by omega
      have hCD : ∀ i l, ContDiff ℝ 1 (uD η m i l) := fun i l => uD_contDiff hη m (by omega) i l
      rw [uD_succ_of_lt η hm']
      by_cases hc : i = (⟨m, hm'⟩ : Fin n) ∨ l = (⟨m, hm'⟩ : Fin n)
      · rw [uStep_apply, if_pos hc]
        have hcut : cutF (⟨m, hm'⟩ : Fin n) z = 1 :=
          cutF_eq_one (le_of_lt (hz (⟨m, hm'⟩ : Fin n) (by simp)))
        rw [hcut, sub_self, zero_mul, zero_add]
      · rw [uStep_apply, if_neg hc]
        have hcut : cutF (⟨m, hm'⟩ : Fin n) z = 1 :=
          cutF_eq_one (le_of_lt (hz (⟨m, hm'⟩ : Fin n) (by simp)))
        rw [hcut, sub_self, zero_mul, zero_add]
        have hcont : Continuous (fun y => cutFbar (⟨m, hm'⟩ : Fin n) y * uD η m i l y) :=
          (contDiff_cutFbar _).continuous.mul (hCD i l).continuous
        rw [dTLM_eq hcont, dbarTransform_eq_zero_of_fiber]
        intro y hy
        by_cases hbc : cutFbar (⟨m, hm'⟩ : Fin n) y = 0
        · rw [hbc, zero_mul]
        · have hy_out : ‖y (⟨m, hm'⟩ : Fin n)‖ < cutOut := by
            by_contra hcon
            exact hbc (cutFbar_eq_zero_of_ge (le_of_not_gt hcon))
          have hyz : ∀ k : Fin n, (k : ℕ) < m → ‖y k‖ < cutIn := by
            intro k hk
            have hne : k ≠ (⟨m, hm'⟩ : Fin n) := by
              intro h; rw [h] at hk; exact absurd hk (by simp)
            rw [hy k hne]
            exact hz k (by omega)
          have hlt' : (i : ℕ) < m ∨ (l : ℕ) < m := by
            rcases hlt with h | h
            · left; have hmne : (i : ℕ) ≠ m := fun he => hc (Or.inl (Fin.ext he)); omega
            · right; have hmne : (l : ℕ) ≠ m := fun he => hc (Or.inr (Fin.ext he)); omega
          rw [ih (by omega) i l hlt' y hyz, mul_zero]

lemma continuous_dbarCoord {n : ℕ} {D : (Fin n → ℂ) → ℂ} (hD : ContDiff ℝ 1 D) (a : Fin n) :
    Continuous (dbarCoord a D) := by
  rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp a D]
  exact (Work.CR.Flat.Polydisc.dbarCoordPhi a).continuous.comp (hD.continuous_fderiv one_ne_zero)

lemma dbarCoord_one_sub_cutF_mul {n : ℕ} {s : Fin n} {D : (Fin n → ℂ) → ℂ}
    (hD : ContDiff ℝ 1 D) (a : Fin n) (z : Fin n → ℂ) :
    dbarCoord a (fun w => (1 - cutF s w) * D w) z
      = (1 - cutF s z) * dbarCoord a D z - (if a = s then cutFbar s z * D z else 0) := by
  have hd1 : DifferentiableAt ℝ (fun w => 1 - cutF s w) z :=
    (differentiableAt_const _).sub ((contDiff_cutF s).contDiffAt.differentiableAt (by simp))
  have hdD : DifferentiableAt ℝ D z := (hD.differentiable one_ne_zero).differentiableAt
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul a _ _ z hd1 hdD, dbarCoord_one_sub_cutF]
  by_cases h : a = s
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

lemma dbarCoord_dTLM_transform {n : ℕ} {s : Fin n} {D : (Fin n → ℂ) → ℂ}
    (hD : ContDiff ℝ 1 D) {z : Fin n → ℂ} (hzs : ‖z s‖ < trRho / 2) (a : Fin n) :
    dbarCoord a (dTLM s (fun y => cutFbar s y * D y)) z
      = if a = s then cutFbar s z * D z
        else dTLM s (fun y => cutFbar s y * dbarCoord a D y) z := by
  have hg : ContDiff ℝ 1 (fun y => cutFbar s y * D y) :=
    ((contDiff_cutFbar s).of_le (by exact_mod_cast le_top)).mul hD
  have hsupp : ∀ y, cutOut ≤ ‖y s‖ → cutFbar s y * D y = 0 :=
    fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul]
  rw [dTLM_eq hg.continuous]
  by_cases ha : a = s
  · rw [ha, if_pos rfl]
    rw [dbarTransform_dbarCoord s s hg z,
      dbarTransform_dbarCoord_self trRho_pos s hg
        (fun y hy => hsupp y (by rw [cutOut_eq_half_trRho]; exact hy)) hzs]
  · rw [if_neg ha, dbarTransform_dbarCoord s a hg z]
    have hprod : (fun y => dbarCoord a (fun y' => cutFbar s y' * D y') y)
        = fun y => cutFbar s y * dbarCoord a D y := by
      funext y
      exact dbarCoord_cutFbar_mul ha ((hD.differentiable one_ne_zero).differentiableAt)
    rw [hprod]
    have hcont : Continuous (fun y => cutFbar s y * dbarCoord a D y) :=
      (contDiff_cutFbar s).continuous.mul (continuous_dbarCoord hD a)
    rw [← dTLM_eq hcont]

lemma dbarCoord_uStep {n : ℕ} {s : Fin n} {D : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hD : ∀ i l, ContDiff ℝ 1 (D i l)) {z : Fin n → ℂ} (hzs : ‖z s‖ < trRho / 2)
    (a i l : Fin n) :
    dbarCoord a (uStep s D i l) z
      = (1 - cutF s z) * dbarCoord a (D i l) z
        - (if a = s then cutFbar s z * D i l z else 0)
        + (if i = s ∨ l = s then 0
           else if a = s then cutFbar s z * D i l z
                else dTLM s (fun y => cutFbar s y * dbarCoord a (D i l) y) z) := by
  have hA := dbarCoord_one_sub_cutF_mul (s := s) (hD i l) a z
  have hB := dbarCoord_dTLM_transform (s := s) (hD i l) hzs a
  by_cases hic : i = s ∨ l = s
  · have hfun : uStep s D i l = fun w => (1 - cutF s w) * D i l w := by
      funext w; rw [uStep_apply, if_pos hic]; ring
    rw [hfun, hA, if_pos hic]; ring
  · have hfun : uStep s D i l = fun w => (1 - cutF s w) * D i l w
        + dTLM s (fun y => cutFbar s y * D i l y) w := by
      funext w; rw [uStep_apply, if_neg hic]
    rw [hfun]
    have hd1 : DifferentiableAt ℝ (fun w => (1 - cutF s w) * D i l w) z :=
      ((differentiableAt_const _).sub ((contDiff_cutF s).contDiffAt.differentiableAt (by simp))).mul
        ((hD i l).differentiable one_ne_zero).differentiableAt
    have hd2 : DifferentiableAt ℝ (dTLM s (fun y => cutFbar s y * D i l y)) z :=
      (contDiff_dTLM (((contDiff_cutFbar s).of_le (by exact_mod_cast le_top)).mul (hD i l))
        (fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul])).differentiable one_ne_zero
        |>.differentiableAt
    rw [Work.CR.Flat.Polydisc.dbarCoord_add a _ _ z hd1 hd2, hA, hB, if_neg hic]

/-! ## The tracking regions -/

lemma cutOut_lt_one : cutOut < 1 := by norm_num [cutOut]

/-- The region on which the stage-`s` data of the recursion are tracked: the coordinates
`< s` (already processed) are kept in the `solveSet` range and the coordinates `≥ s` only in
the range where the cutoffs are supported. -/
def E (n : ℕ) (s : ℕ) : Set (Fin n → ℂ) :=
  {z | ∀ m : Fin n, ((m : ℕ) < s → ‖z m‖ < eqRad) ∧ (s ≤ (m : ℕ) → ‖z m‖ < cutOut)}

lemma E_mono {n s : ℕ} : E n (s + 1) ⊆ E n s := by
  intro z hz m
  refine ⟨fun hm => (hz m).1 (by omega), fun hm => ?_⟩
  by_cases h : (m : ℕ) < s + 1
  · exact lt_trans ((hz m).1 h) (lt_trans eqRad_lt_cutIn cutIn_lt_cutOut)
  · exact (hz m).2 (by omega)

lemma E_subset_unit {n s : ℕ} {z : Fin n → ℂ} (hz : z ∈ E n s) :
    z ∈ polydisc 0 (fun _ => 1) := by
  rw [mem_polydisc]; intro m
  simp only [Pi.zero_apply, sub_zero, one_mul]
  rcases Nat.lt_or_ge (m : ℕ) s with h | h
  · exact lt_trans ((hz m).1 h) (lt_trans eqRad_lt_cutIn (lt_trans cutIn_lt_cutOut cutOut_lt_one))
  · exact lt_trans ((hz m).2 h) cutOut_lt_one

lemma E_fiber {n : ℕ} {s : Fin n} {z y : Fin n → ℂ} (hz : z ∈ E n ((s : ℕ) + 1))
    (hys : ‖y s‖ < cutOut) (hy : ∀ m : Fin n, m ≠ s → y m = z m) : y ∈ E n (s : ℕ) := by
  intro m
  constructor
  · intro hm
    have hne : m ≠ s := by intro h; rw [h] at hm; omega
    rw [hy m hne]
    exact (hz m).1 (by omega)
  · intro hm
    rcases eq_or_ne m s with hms | hne
    · rw [hms]; exact hys
    · rw [hy m hne]
      by_cases h : (m : ℕ) < (s : ℕ) + 1
      · exact lt_trans ((hz m).1 h) (lt_trans eqRad_lt_cutIn cutIn_lt_cutOut)
      · exact (hz m).2 (by omega)

/-! ## Preservation of `∂̄`-closedness -/

lemma dbarCoord_zero' {n : ℕ} (a : Fin n) (z : Fin n → ℂ) :
    dbarCoord a (0 : (Fin n → ℂ) → ℂ) z = 0 := by
  rw [show (0 : (Fin n → ℂ) → ℂ) = fun _ => (0 : ℂ) from rfl, dbarCoord_const']

/-- The `(0,3)`-form of `uStep s D` vanishes, given that the `(0,3)`-form of `D` vanishes at
`z` and on the fibre of `z` in the `s`-th coordinate (within the support of `cutFbar s`). -/
private lemma uStep_closed_zero {n : ℕ} {s : Fin n} {D : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hD : ∀ i l, ContDiff ℝ 1 (D i l)) (hanti : ∀ i l z, D i l z = - D l i z)
    {a b c : Fin n} {z : Fin n → ℂ} (hzs : ‖z s‖ < trRho / 2)
    (hclz : dbarCoord a (D b c) z - dbarCoord b (D a c) z + dbarCoord c (D a b) z = 0)
    (hfib : ∀ y, (∀ m : Fin n, m ≠ s → y m = z m) →
      cutFbar s y * (dbarCoord a (D b c) y - dbarCoord b (D a c) y + dbarCoord c (D a b) y) = 0) :
    dbarCoord a (uStep s D b c) z - dbarCoord b (uStep s D a c) z
      + dbarCoord c (uStep s D a b) z = 0 := by
  have hss : D s s = 0 := by
    funext w
    exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp (hanti s s w))
  rw [dbarCoord_uStep (s := s) hD hzs a b c,
      dbarCoord_uStep (s := s) hD hzs b a c,
      dbarCoord_uStep (s := s) hD hzs c a b]
  by_cases ha : a = s <;> by_cases hb : b = s <;> by_cases hc : c = s
  · rw [ha, hb, hc] at *
    simp only [ite_true, or_true, eq_self_iff_true, hss, dbarCoord_zero',
      Pi.zero_apply, neg_zero, mul_zero, zero_mul, sub_zero, add_zero, zero_add, one_mul]
  · rw [ha, hb] at *
    simp only [ite_true, ite_false, true_or, or_true, false_or, or_false, eq_self_iff_true,
      hc, hss, dbarCoord_zero', mul_zero, zero_mul, sub_zero, add_zero, zero_add, one_mul]
    ring
  · rw [ha, hc] at *
    simp only [ite_true, ite_false, true_or, or_true, false_or, or_false, eq_self_iff_true,
      hb, hss, dbarCoord_zero', mul_zero, zero_mul, sub_zero, add_zero, zero_add, one_mul]
    have hd : dbarCoord s (D s b) z = - dbarCoord s (D b s) z := by
      rw [show D s b = fun w => -D b s w from funext fun w => hanti s b w, dbarCoord_neg']
    rw [hd, hanti s b z]
    ring
  · simp only [ite_eq_left ha, ite_eq_right (fun h : b = s ∨ c = s => h.elim hb hc),
      ite_eq_right hb, ite_eq_left (Or.inl ha), ite_eq_right hc]
    linear_combination (1 - cutF s z) * hclz
  · rw [hb, hc] at *
    simp only [ite_true, ite_false, true_or, or_true, false_or, or_false, eq_self_iff_true,
      ha, hss, dbarCoord_zero', mul_zero, zero_mul, sub_zero, add_zero, zero_add, one_mul]
    ring
  · simp only [ite_eq_right ha, ite_eq_left (Or.inl hb), ite_eq_left hb,
      ite_eq_right (fun h : a = s ∨ c = s => h.elim ha hc), ite_eq_right hc,
      ite_eq_left (Or.inr hb)]
    linear_combination (1 - cutF s z) * hclz
  · simp only [ite_eq_right ha, ite_eq_left (Or.inr hc), ite_eq_right hb,
      ite_eq_right (fun h : a = s ∨ b = s => h.elim ha hb), ite_eq_left hc]
    linear_combination (1 - cutF s z) * hclz
  · simp only [ite_eq_right ha, ite_eq_right hb, ite_eq_right hc,
      ite_eq_right (fun h : b = s ∨ c = s => h.elim hb hc),
      ite_eq_right (fun h : a = s ∨ c = s => h.elim ha hc),
      ite_eq_right (fun h : a = s ∨ b = s => h.elim ha hb)]
    have hdtlm : dTLM s (fun y => cutFbar s y * dbarCoord a (D b c) y) z
        - dTLM s (fun y => cutFbar s y * dbarCoord b (D a c) y) z
        + dTLM s (fun y => cutFbar s y * dbarCoord c (D a b) y) z = 0 := by
      have hcomb : dTLM s (fun y => cutFbar s y * dbarCoord a (D b c) y)
            - dTLM s (fun y => cutFbar s y * dbarCoord b (D a c) y)
            + dTLM s (fun y => cutFbar s y * dbarCoord c (D a b) y)
          = dTLM s (fun y => cutFbar s y * (dbarCoord a (D b c) y - dbarCoord b (D a c) y
              + dbarCoord c (D a b) y)) := by
        rw [← map_sub, ← map_add]
        congr 1
        funext y
        simp only [Pi.sub_apply, Pi.add_apply]
        ring
      have hgcont : Continuous (fun y => cutFbar s y *
          (dbarCoord a (D b c) y - dbarCoord b (D a c) y + dbarCoord c (D a b) y)) :=
        (contDiff_cutFbar s).continuous.mul
          (((continuous_dbarCoord (hD b c) a).sub (continuous_dbarCoord (hD a c) b)).add
            (continuous_dbarCoord (hD a b) c))
      rw [show dTLM s (fun y => cutFbar s y * dbarCoord a (D b c) y) z
            - dTLM s (fun y => cutFbar s y * dbarCoord b (D a c) y) z
            + dTLM s (fun y => cutFbar s y * dbarCoord c (D a b) y) z
          = (dTLM s (fun y => cutFbar s y * dbarCoord a (D b c) y)
              - dTLM s (fun y => cutFbar s y * dbarCoord b (D a c) y)
              + dTLM s (fun y => cutFbar s y * dbarCoord c (D a b) y)) z from rfl,
        hcomb, dTLM_eq hgcont]
      exact dbarTransform_eq_zero_of_fiber (ρ := trRho) (j := s) hfib
    linear_combination (1 - cutF s z) * hclz + hdtlm

lemma dbarCoord_dTLM_cutF {n : ℕ} {s : Fin n} {D : (Fin n → ℂ) → ℂ}
    (hD : ContDiff ℝ 1 D) {z : Fin n → ℂ} (hzs : ‖z s‖ < cutIn) (a : Fin n) :
    dbarCoord a (dTLM s (fun y => cutF s y * D y)) z
      = if a = s then D z else dTLM s (fun y => cutF s y * dbarCoord a D y) z := by
  have hg : ContDiff ℝ 1 (fun y => cutF s y * D y) :=
    ((contDiff_cutF s).of_le (by exact_mod_cast le_top)).mul hD
  have hsupp : ∀ y, cutOut ≤ ‖y s‖ → cutF s y * D y = 0 :=
    fun y hy => by rw [cutF_eq_zero hy, zero_mul]
  have hzs' : ‖z s‖ < trRho / 2 :=
    lt_trans hzs (by rw [← cutOut_eq_half_trRho]; exact cutIn_lt_cutOut)
  rw [dTLM_eq hg.continuous]
  by_cases ha : a = s
  · rw [ha, if_pos rfl, dbarTransform_dbarCoord s s hg z,
      dbarTransform_dbarCoord_self trRho_pos s hg
        (fun y hy => hsupp y (by rw [cutOut_eq_half_trRho]; exact hy)) hzs']
    rw [cutF_eq_one (le_of_lt hzs), one_mul]
  · rw [if_neg ha, dbarTransform_dbarCoord s a hg z]
    have hprod : (fun y => dbarCoord a (fun y' => cutF s y' * D y') y)
        = fun y => cutF s y * dbarCoord a D y := by
      funext y
      exact dbarCoord_cutF_mul ha ((hD.differentiable one_ne_zero).differentiableAt)
    rw [hprod]
    have hcont : Continuous (fun y => cutF s y * dbarCoord a D y) :=
      (contDiff_cutF s).continuous.mul (continuous_dbarCoord hD a)
    rw [← dTLM_eq hcont]

/-- Stage-`s` data are `∂̄`-closed on the tracking region `E n s`. -/
theorem uD_closed {n : ℕ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hanti : ∀ i l z, η i l z = - η l i z)
    (hcl : ∀ i l m' z, z ∈ polydisc 0 (fun _ => 1) →
      dbarCoord i (η l m') z - dbarCoord l (η i m') z + dbarCoord m' (η i l) z = 0) :
    ∀ s ≤ n, ∀ a b c : Fin n, ∀ z ∈ E n s,
      dbarCoord a (uD η s b c) z - dbarCoord b (uD η s a c) z + dbarCoord c (uD η s a b) z = 0 := by
  intro s
  induction s with
  | zero =>
      intro _ a b c z hz
      exact hcl a b c z (E_subset_unit hz)
  | succ s ih =>
      intro hs a b c z hz
      have hs' : s < n := by omega
      rw [uD_succ_of_lt η hs']
      have hD : ∀ i l, ContDiff ℝ 1 (uD η s i l) := fun i l => uD_contDiff hη s (by omega) i l
      have hantiD : ∀ i l w, uD η s i l w = - uD η s l i w :=
        fun i l w => uD_antisymm hanti s i l w
      have hzs : ‖z (⟨s, hs'⟩ : Fin n)‖ < trRho / 2 := by
        rw [← cutOut_eq_half_trRho]
        exact lt_trans ((hz (⟨s, hs'⟩ : Fin n)).1 (by simp))
          (lt_trans eqRad_lt_cutIn cutIn_lt_cutOut)
      have hclz : dbarCoord a (uD η s b c) z - dbarCoord b (uD η s a c) z
          + dbarCoord c (uD η s a b) z = 0 := ih (by omega) a b c z (E_mono hz)
      have hfib : ∀ y, (∀ m : Fin n, m ≠ (⟨s, hs'⟩ : Fin n) → y m = z m) →
          cutFbar (⟨s, hs'⟩ : Fin n) y *
            (dbarCoord a (uD η s b c) y - dbarCoord b (uD η s a c) y
              + dbarCoord c (uD η s a b) y) = 0 := by
        intro y hy
        by_cases hcb : cutFbar (⟨s, hs'⟩ : Fin n) y = 0
        · rw [hcb, zero_mul]
        · have hys : ‖y (⟨s, hs'⟩ : Fin n)‖ < cutOut := by
            by_contra hcon
            exact hcb (cutFbar_eq_zero_of_ge (le_of_not_gt hcon))
          rw [ih (by omega) a b c y (E_fiber hz hys hy), mul_zero]
      exact uStep_closed_zero (s := (⟨s, hs'⟩ : Fin n)) hD hantiD hzs hclz hfib


theorem uD_closed_E {n : ℕ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l))
    (hanti : ∀ i l z, η i l z = - η l i z)
    (hcl : ∀ i l m' z, (∀ k : Fin n, ‖z k‖ < cutOut) →
      dbarCoord i (η l m') z - dbarCoord l (η i m') z + dbarCoord m' (η i l) z = 0) :
    ∀ s ≤ n, ∀ a b c : Fin n, ∀ z ∈ E n s,
      dbarCoord a (uD η s b c) z - dbarCoord b (uD η s a c) z + dbarCoord c (uD η s a b) z = 0 := by
  intro s
  induction s with
  | zero =>
      intro _ a b c z hz
      exact hcl a b c z (fun k => (hz k).2 (Nat.zero_le k))
  | succ s ih =>
      intro hs a b c z hz
      have hs' : s < n := by omega
      rw [uD_succ_of_lt η hs']
      have hD : ∀ i l, ContDiff ℝ 1 (uD η s i l) := fun i l => uD_contDiff hη s (by omega) i l
      have hantiD : ∀ i l w, uD η s i l w = - uD η s l i w :=
        fun i l w => uD_antisymm hanti s i l w
      have hzs : ‖z (⟨s, hs'⟩ : Fin n)‖ < trRho / 2 := by
        rw [← cutOut_eq_half_trRho]
        exact lt_trans ((hz (⟨s, hs'⟩ : Fin n)).1 (by simp))
          (lt_trans eqRad_lt_cutIn cutIn_lt_cutOut)
      have hclz : dbarCoord a (uD η s b c) z - dbarCoord b (uD η s a c) z
          + dbarCoord c (uD η s a b) z = 0 := ih (by omega) a b c z (E_mono hz)
      have hfib : ∀ y, (∀ m : Fin n, m ≠ (⟨s, hs'⟩ : Fin n) → y m = z m) →
          cutFbar (⟨s, hs'⟩ : Fin n) y *
            (dbarCoord a (uD η s b c) y - dbarCoord b (uD η s a c) y
              + dbarCoord c (uD η s a b) y) = 0 := by
        intro y hy
        by_cases hcb : cutFbar (⟨s, hs'⟩ : Fin n) y = 0
        · rw [hcb, zero_mul]
        · have hys : ‖y (⟨s, hs'⟩ : Fin n)‖ < cutOut := by
            by_contra hcon
            exact hcb (cutFbar_eq_zero_of_ge (le_of_not_gt hcon))
          rw [ih (by omega) a b c y (E_fiber hz hys hy), mul_zero]
      exact uStep_closed_zero (s := (⟨s, hs'⟩ : Fin n)) hD hantiD hzs hclz hfib


/-! ## Linearity of the recursion -/

lemma uStep_add {n : ℕ} {s : Fin n} {D D' : Fin n → Fin n → (Fin n → ℂ) → ℂ} :
    uStep s (D + D') = uStep s D + uStep s D' := by
  funext i l z
  simp only [Pi.add_apply, uStep_apply]
  by_cases hc : i = s ∨ l = s
  · simp only [ite_eq_left hc]; ring
  · simp only [ite_eq_right hc]
    have harg : (fun y => cutFbar s y * (D i l y + D' i l y))
        = (fun y => cutFbar s y * D i l y) + (fun y => cutFbar s y * D' i l y) := by
      funext y; simp only [Pi.add_apply]; ring
    rw [harg, map_add, Pi.add_apply]
    ring

lemma uStep_smul {n : ℕ} {s : Fin n} (c : ℝ) {D : Fin n → Fin n → (Fin n → ℂ) → ℂ} :
    uStep s (c • D) = c • uStep s D := by
  funext i l z
  simp only [Pi.smul_apply, uStep_apply]
  by_cases hc : i = s ∨ l = s
  · simp only [ite_eq_left hc, Complex.real_smul]
    ring
  · simp only [ite_eq_right hc]
    have harg : (fun y => cutFbar s y * (c • D i l y))
        = c • (fun y => cutFbar s y * D i l y) := by
      funext y
      simp only [Pi.smul_apply, Complex.real_smul]
      ring
    rw [harg, map_smul]
    simp only [Pi.smul_apply, Complex.real_smul]
    ring

lemma uD_add {n : ℕ} (η η' : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    ∀ m, uD (η + η') m = uD η m + uD η' m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [uD_succ, uD_succ, uD_succ]
      by_cases h : m < n
      · rw [dif_pos h, dif_pos h, dif_pos h, ih, uStep_add]
      · rw [dif_neg h, dif_neg h, dif_neg h, ih]

lemma uD_smul {n : ℕ} (c : ℝ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    ∀ m, uD (c • η) m = c • uD η m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [uD_succ, uD_succ]
      by_cases h : m < n
      · rw [dif_pos h, dif_pos h, ih, uStep_smul]
      · rw [dif_neg h, dif_neg h, ih]

lemma uPsi_add {n : ℕ} (η η' : Fin n → Fin n → (Fin n → ℂ) → ℂ) (s : Fin n) :
    uPsi (η + η') s = uPsi η s + uPsi η' s := by
  funext l
  show dTLM s (fun y => cutF s y * uD (η + η') (s : ℕ) s l y)
    = dTLM s (fun y => cutF s y * uD η (s : ℕ) s l y)
      + dTLM s (fun y => cutF s y * uD η' (s : ℕ) s l y)
  rw [uD_add η η' (s : ℕ)]
  have harg : (fun y => cutF s y * (uD η (s : ℕ) + uD η' (s : ℕ)) s l y)
      = (fun y => cutF s y * uD η (s : ℕ) s l y)
        + (fun y => cutF s y * uD η' (s : ℕ) s l y) := by
    funext y; simp only [Pi.add_apply]; ring
  rw [harg, map_add]

lemma uPsi_smul {n : ℕ} (c : ℝ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) (s : Fin n) :
    uPsi (c • η) s = c • uPsi η s := by
  funext l
  show dTLM s (fun y => cutF s y * uD (c • η) (s : ℕ) s l y)
    = c • dTLM s (fun y => cutF s y * uD η (s : ℕ) s l y)
  rw [uD_smul c η (s : ℕ)]
  have harg : (fun y => cutF s y * (c • uD η (s : ℕ)) s l y)
      = c • (fun y => cutF s y * uD η (s : ℕ) s l y) := by
    funext y; simp only [Pi.smul_apply, Complex.real_smul]; ring
  rw [harg, map_smul]

lemma uS2_add {n : ℕ} (η η' : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    uS2 (η + η') = uS2 η + uS2 η' := by
  funext l
  show (∑ s : Fin n, uPsi (η + η') s l) = (∑ s : Fin n, uPsi η s l) + (∑ s : Fin n, uPsi η' s l)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  exact congrFun (uPsi_add η η' s) l

lemma uS2_smul {n : ℕ} (c : ℝ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    uS2 (c • η) = c • uS2 η := by
  funext l
  show (∑ s : Fin n, uPsi (c • η) s l) = c • (∑ s : Fin n, uPsi η s l)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  exact congrFun (uPsi_smul c η s) l

/-- The unit-polydisc `(0,2)`-solver as a real-linear map. -/
noncomputable def uS2LM (n : ℕ) :
    (Fin n → Fin n → (Fin n → ℂ) → ℂ) →ₗ[ℝ] (Fin n → (Fin n → ℂ) → ℂ) :=
  { toFun := fun η => uS2 η
    map_add' := fun η η' => uS2_add η η'
    map_smul' := fun c η => uS2_smul c η }

@[simp] lemma uS2LM_apply {n : ℕ} (η : Fin n → Fin n → (Fin n → ℂ) → ℂ) :
    uS2LM n η = uS2 η := rfl

lemma le_infty_omega (m : ℕ) : (m : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top

/-- `uS2 η` is `C¹` whenever the data are. -/
lemma contDiff_uS2 {n : ℕ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l)) : ∀ j : Fin n, ContDiff ℝ 1 (uS2 η j) := by
  intro j
  have hfun : uS2 η j = fun z : Fin n → ℂ => ∑ s ∈ Finset.univ, uPsi η s j z := by
    funext z; simp [uS2]
  rw [hfun]
  refine ContDiff.sum (s := Finset.univ) (f := fun s => uPsi η s j) (fun s _ => ?_)
  show ContDiff ℝ 1 (fun z => dTLM s (fun y => cutF s y * uD η (s : ℕ) s j y) z)
  refine contDiff_dTLM (((contDiff_cutF s).of_le (le_infty_omega 1)).mul
    (uD_contDiff hη (s : ℕ) (le_of_lt s.isLt) s j)) (fun y hy => ?_)
  rw [cutF_eq_zero hy, zero_mul]

end Work.NN.Final
