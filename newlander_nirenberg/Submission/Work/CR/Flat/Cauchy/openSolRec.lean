/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The coordinate-by-coordinate recursion solving `∂̄ u = f` on a polydisc

This module contains the *construction* (definitions and their structural theory)
behind `Work.CR.Flat.Cauchy.exists_dbar_solution_polydisc_open_aux`: the
unsupported `∂̄`-problem on the unit polydisc is solved by processing the
coordinates one at a time, using

  `dbarTransform ρ j g z = -(1/π) ∫_{‖w‖<ρ} g (z + w e_j) / w dw`

together with a smooth cutoff `openCut` in the transformed coordinate.

Given data `f : Fin n → (Fin n → ℂ) → ℂ` the recursion is

* `recF f 0 = f`,
* `recF f (m+1) k = dbarTransform trRho ⟨m⟩ (fun y => cutFbar ⟨m⟩ y * recF f m k y)`
  (for `m < n`; for `m ≥ n` the stage is unchanged),

and the candidate solution is

* `recU f z = ∑ j : Fin n, dbarTransform trRho j (fun y => cutF j y * recF f (j:ℕ) j y) z`.

The two structural theorems proved here are

* `recF_inv` : at every stage the data are `C^{k+1}`, are holomorphic in the
  already processed directions (`‖z l‖ < cutIn → ∂̄_l (recF f s j) z = 0` for
  `l < s`) and are closed for the pairs of indices `≥ s`;
* `recU_solves` : `∂̄_i (recU f) z = f i z` for `‖z l‖ < eqRad` (all `l`);
* `contDiff_recU` : `recU f` is `C^{k+1}` when the data are.

## The estimate (not proved in this module)

The remaining analytic input, needed to finish the target theorem, is the
`C^{0,α}` bound for `recU f`, namely

```
theorem recU_estimate {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf1 : ∀ j, ContDiff ℝ 1 (f j)) (hcl : IsClosedForm f)
    (hS : (∑ j, holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))) ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧
      (∀ z : Fin n → ℂ, (∀ l, ‖z l‖ < eqRad) → ‖recU f z‖ ≤
        C * ∑ j, (holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))).toReal) ∧
      (∀ x y : Fin n → ℂ, (∀ l, ‖x l‖ < eqRad) → (∀ l, ‖y l‖ < eqRad) →
        ‖recU f x - recU f y‖ ≤
          C * (∑ j, (holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))).toReal) * ‖x - y‖ ^ α)
```

It lives in module `Submission.Work.CR.Flat.Cauchy.recU_estimate`.

**IMPORTANT: the constant has to be uniform in `f`.**  The final theorem
`exists_dbar_solution_polydisc_open_aux` asks for a *single* `C` valid for all
data `f`, so the version that is actually consumed is the following
(`Work.CR.Flat.Cauchy.recU_estimate_uniform`, module
`Submission.Work.CR.Flat.Cauchy.recU_estimate_uniform`), in which `f` and its
hypotheses sit *inside* the `∃ C`:

```
theorem recU_estimate_uniform {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (f j)) →
      IsClosedForm f → (∑ j, holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))) ≠ ⊤ →
      (∀ z : Fin n → ℂ, (∀ l, ‖z l‖ < eqRad) →
        ‖recU f z‖ ≤ C * ∑ j, (holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))).toReal) ∧
      (∀ x y : Fin n → ℂ, (∀ l, ‖x l‖ < eqRad) → (∀ l, ‖y l‖ < eqRad) →
        ‖recU f x - recU f y‖ ≤
          C * (∑ j, (holderNorm 0 α (f j) (polydisc 0 (fun _ => 1))).toReal) * ‖x - y‖ ^ α)
```

**The full proof plan is the following.  Note that the constant produced by the
plan below involves only `n`, `α`, `trRho`, and the two absolute constants `L`
(a Lipschitz constant for `openCut`) and `C₀` (from
`cutFbar_mul_bound_uniform`) — it does not depend on `f` — so exactly the same
argument proves the uniform version.**

Write `H j := holderNorm 0 α (f j) (polydisc 0 1)` and `S := ∑ j, (H j).toReal`.

**Step 0 (the data bounds on `trackSet`).**  From `hS` get `H j ≠ ⊤` for every `j`
(if `H j = ⊤` then `⊤ ≤ ∑ i, H i`, using `Finset.single_le_sum`), then
`S = (∑ j, H j).toReal` (`ENNReal.toReal_sum`).  For `z ∈ trackSet ⊆ polydisc 0 1`
(`trackSet_subset_unit`, `trTrack = 15/16 < 1`) one gets
`ENNReal.ofReal ‖f j z‖ ≤ iterDerivNorm 0 (f j) (polydisc 0 1) ≤ H j`, hence
`‖f j z‖ ≤ (H j).toReal ≤ S` (`norm_apply_le_holderNorm`,
`ENNReal.ofReal_le_iff_le_toReal`, `ENNReal.toReal_mono` with `H j ≤ ∑ i, H i`).
Likewise for `x ≠ y` in `polydisc 0 1`, `holderSeminorm 0 α (f j) (polydisc 0 1) ≤ H j`
gives `‖f j x - f j y‖ ≤ (H j).toReal * ‖x - y‖ ^ α ≤ S * ‖x - y‖ ^ α`
(`le_holderSeminorm`, `holderSeminorm_le_holderNorm`, `le_join`/`le_add_left` as needed).
Hence both base bounds
`∀ j z, z ∈ trackSet → ‖f j z‖ ≤ S` and
`∀ j x y, x, y ∈ trackSet → ‖f j x - f j y‖ ≤ S * ‖x - y‖ ^ α`.  (For `x = y` the second
bound needs `‖x - y‖ ^ α` to be `0 ^ α = 0`; either restrict to `x ≠ y` and note both
sides vanish when `x = y`, or use `Real.rpow_pos_of_pos`.)

**Step 1 (the constants).**  `openCut_props_infty` gives `cχ, cχ'` with
`‖dbarC openCut ζ‖ ≤ cχ` and the Lipschitz bound.  `openCut_lipschitz` gives `L`
with `‖openCut ζ - openCut ζ'‖ ≤ L ‖ζ - ζ'‖`.  From
`Work.CR.Flat.Cauchy.cutFbar_mul_bound_uniform` (module
`Submission.Work.CR.Flat.Cauchy.cutFbar_mul_bound_uniform`) applied to those
`cχ, cχ'` get `C₀ > 0` such that for all `F, A, H ≥ 0` satisfying
`(∀ z ∈ trackSet, ‖F z‖ ≤ A)` and `(∀ x y ∈ trackSet, ‖F x - F y‖ ≤ H ‖x-y‖^α)`:
* `∀ z, (∀ l, l ≠ j → ‖z l‖ < trTrack) → ‖z j‖ ≤ cutOut → ‖dbarC openCut (z j) * F z‖ ≤ C₀ * A`,
* `∀ a a', (∀ l, l ≠ j → ‖a l‖ < trTrack) → (∀ l, l ≠ j → ‖a' l‖ < trTrack) →
    ‖dbarC openCut (a j) * F a - dbarC openCut (a' j) * F a'‖ ≤ C₀ * (A + H) * ‖a - a'‖ ^ α`.

**Step 2 (induction over the stages).**  Put `K := max 1 (4 * trRho * C₀) + 1`
(so `1 ≤ K`).  Prove, by induction on `m`, for all `m ≤ n` and all `k : Fin n`:

* `(i)  ∀ z ∈ trackSet, ‖recF f m k z‖ ≤ K ^ m * S`,
* `(ii) ∀ x y ∈ trackSet, ‖recF f m k x - recF f m k y‖ ≤ K ^ m * S * ‖x - y‖ ^ α`.

Base case `m = 0`: `recF f 0 = f`, `K ^ 0 = 1`, use Step 0.
Step `m → m+1`: if `m ≥ n` then `recF f (m+1) = recF f m` (`recF_succ`, `dif_neg`),
and `K ^ m ≤ K ^ (m+1)` (`one_le_pow₀`-style monotonicity).  If `m < n`, put
`j := ⟨m, h⟩` and `g k y := cutFbar j y * recF f m k y`; then
`recF f (m+1) k = dbarTransform trRho j (g k)` (`recF_succ_of_lt`).
* Part 1 of `dbarTransform_basic` (`ρ = trRho`, `b = cutOut`, requires
  `Continuous (g k)` — from `contDiff_cutFbar_of_le` and `recF_inv` — and the
  support `cutFbar_eq_zero_of_ge`) with `A := C₀ * (K ^ m * S)`:
  the fibre hypothesis `∀ y, (∀ l, l ≠ j → y l = z l) → ‖y j‖ ≤ cutOut → ‖g k y‖ ≤ A`
  is the first bullet of `C₀`, using `trackSet_update` and (i) at stage `m`.
  Gives `‖recF f (m+1) k z‖ ≤ 2 * trRho * C₀ * K ^ m * S ≤ K ^ (m+1) * S`.
* Part 2 of `dbarTransform_basic` with `H := C₀ * (K ^ m * S + K ^ m * S)`:
  the fibre Hölder hypothesis is the second bullet of `C₀` (via (i), (ii) at stage `m`),
  giving `≤ 2 * trRho * (2 * C₀ * K ^ m * S) * ‖x - y‖ ^ α ≤ K ^ (m+1) * S * ‖x - y‖ ^ α`.

**Step 3 (summing the `n` summands of `recU`).**  Fix `x, y` with all coordinates
`< eqRad`; then `x, y ∈ trackSet` (`trackSet_of_solveSet`).
For `j : Fin n`, part 1 of `dbarTransform_basic` applied to
`g := cutF j * recF f (j : ℕ) j` with `b := cutOut` and `A := K ^ (j : ℕ) * S`
(the fibre hypothesis: `y l = x l` for `l ≠ j` and `‖y j‖ ≤ cutOut` give
`y ∈ trackSet`, so `‖g y‖ ≤ 1 * K ^ (j:ℕ) * S` by `norm_cutF_le_one` and (i))
yields `‖dbarTransform trRho j g x‖ ≤ 2 * trRho * K ^ (j:ℕ) * S ≤ 2 * trRho * K ^ n * S`
(`(j : ℕ) ≤ n`, `1 ≤ K`).  Summing, `‖recU f x‖ ≤ 2 * trRho * (n : ℝ) * K ^ n * S`.
For the Hölder bound, part 2 of `dbarTransform_basic` needs the *fibre* Hölder bound of
`g` on the fibre through `x` and the fibre through `y` (all `a, a'` with the transverse
coordinates fixed, `a j` and `a' j` arbitrary): case split on `‖a j‖ < cutOut`:
* if `cutOut ≤ ‖a j‖` then `cutF j a = 0` (`cutF_eq_zero`) and
  `‖cutF j a - cutF j a'‖ = ‖cutF j a'‖ ≤ L * ‖a - a'‖` (`norm_cutF_sub_le`), while
  `‖cutF j a'‖ ≤ 1` always;  the two sub-cases
  "`‖a' j‖ < cutOut`" (then `a, a' ∈ trackSet`, use (ii)) and "`cutOut ≤ ‖a' j‖`"
  (then both terms vanish) give `≤ K ^ (j:ℕ) * S * (2 + L) * ‖a - a'‖ ^ α`, using
  `t ≤ t ^ α` for `0 ≤ t ≤ 1` and `1 ≤ t ^ α` for `1 ≤ t` (`Real.rpow_le_rpow`,
  `Real.one_le_rpow`, `Real.rpow_nonneg`).
Then `‖dbarTransform trRho j g x - dbarTransform trRho j g y‖
≤ 2 * trRho * K ^ (j:ℕ) * S * (2 + L) * ‖x - y‖ ^ α`; summing over `j` gives the Hölder
bound of `recU` with `C := 2 * trRho * (n : ℝ) * K ^ n * (2 + L) + 1` (or any larger
constant; note the `n = 0` case is vacuous: `recU f = 0` and `S = 0`).

**Useful lemmas available here**: `recF_succ_of_lt`, `recF_succ`, `recF_zero`,
`recF_inv`, `trackSet_update`, `trackSet_subset_unit`, `trackSet_of_solveSet`,
`cutF_eq_zero`, `cutF_eq_one`, `cutFbar_eq_zero_of_ge`, `norm_cutF_le_one`,
`norm_cutFbar_le`, `norm_cutF_sub_le`, `openCut_lipschitz`, `contDiff_cutF_of_le`,
`contDiff_cutFbar_of_le`, `trRho_pos`, `cutOut_pos`, `cutOut_lt_trTrack`, and
`dbarTransform_basic`, `cutFbar_mul_bound_uniform`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.cauchyTransformCoord
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.openSolDefs
import Submission.Work.CR.Flat.Cauchy.exists_dbar_solution_polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_mul
import Submission.Work.CR.Flat.Polydisc.dbarCoord_add
import Submission.Work.CR.Flat.Polydisc.dbarCoord_apply_coord
import Submission.Work.CR.Flat.Cauchy.openCut_props_infty
import Submission.Work.CR.Flat.Cauchy.openCutAux
import Submission.Work.CR.Flat.Cauchy.dbarTransform_basic
import Submission.Work.CR.Flat.Cauchy.dbarTransform_dbarCoord_self
import Submission.Work.CR.Flat.Cauchy.dbarTransform_dbarCoord
import Submission.Work.CR.Flat.Cauchy.contDiff_dbarTransform

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal ContDiff
open MeasureTheory Set

/-! ## Elementary lemmas -/

/-- Any finite smoothness level is below the `C^∞` level `∞`. -/
private lemma le_infty (m : ℕ) : (m : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
  exact_mod_cast le_top


lemma trRho_pos : 0 < trRho := by norm_num [trRho]
lemma trTrack_pos : 0 < trTrack := by norm_num [trTrack]
lemma eqRad_pos : 0 < eqRad := by norm_num [eqRad]

lemma cutIn_lt_cutOut : cutIn < cutOut := by norm_num [cutIn, cutOut]
lemma eqRad_lt_cutIn : eqRad < cutIn := by norm_num [eqRad, cutIn]
lemma cutOut_eq_half_trRho : cutOut = trRho / 2 := by norm_num [cutOut, trRho]
lemma eqRad_lt_trTrack : eqRad < trTrack := by norm_num [eqRad, trTrack]

/-- The cutoff in the `j`-th coordinate, as a function on `ℂⁿ`. -/
noncomputable def cutF {n : ℕ} (j : Fin n) : (Fin n → ℂ) → ℂ := fun y => openCut (y j)

@[simp] lemma cutF_apply {n : ℕ} (j : Fin n) (y : Fin n → ℂ) : cutF j y = openCut (y j) := rfl

/-- The `∂̄`-derivative in the `j`-th coordinate of the cutoff `cutF j`, as a function. -/
noncomputable def cutFbar {n : ℕ} (j : Fin n) : (Fin n → ℂ) → ℂ :=
  fun y => dbarC openCut (y j)

@[simp] lemma cutFbar_apply {n : ℕ} (j : Fin n) (y : Fin n → ℂ) :
    cutFbar j y = dbarC openCut (y j) := rfl

lemma contDiff_cutF {n : ℕ} (j : Fin n) : ContDiff ℝ ∞ (cutF j) :=
  openCut_props_infty.1.comp (contDiff_apply ℝ ℂ j)

lemma contDiff_cutFbar {n : ℕ} (j : Fin n) : ContDiff ℝ ∞ (cutFbar j) := by
  have h2 : ContDiff ℝ ∞ (dbarC openCut) := by
    have hfd : ContDiff ℝ ∞ (fderiv ℝ openCut) :=
      openCut_props_infty.1.fderiv_right (m := ∞) le_rfl
    have h1 : ContDiff ℝ ∞ (fun z : ℂ => fderiv ℝ openCut z 1) := hfd.clm_apply contDiff_const
    have hI : ContDiff ℝ ∞ (fun z : ℂ => fderiv ℝ openCut z Complex.I) :=
      hfd.clm_apply contDiff_const
    rw [show dbarC openCut = fun z => (1 / 2 : ℂ) *
        ((fderiv ℝ openCut z) 1 + Complex.I * (fderiv ℝ openCut z) Complex.I) from rfl]
    exact contDiff_const.mul (h1.add (contDiff_const.mul hI))
  exact h2.comp (contDiff_apply ℝ ℂ j)

lemma dbarCoord_cutF {n : ℕ} (j : Fin n) (z : Fin n → ℂ) :
    dbarCoord j (cutF j) z = cutFbar j z := by
  have hfun : (fun w : ℂ => cutF j (Function.update z j w)) = openCut := by
    funext w; simp [cutF]
  have hdiff : DifferentiableAt ℝ (cutF j) (Function.update z j (z j)) := by
    rw [Function.update_eq_self]
    exact (contDiff_cutF j).contDiffAt.differentiableAt (by simp)
  have h := dbarSolution_dbarC_update_eq_dbarCoord j (g := cutF j) (z := z) (u := z j) hdiff
  rw [Function.update_eq_self, hfun] at h
  exact h.symm

/-- A function of the `j`-th coordinate alone has vanishing `∂̄_l`-derivative for `l ≠ j`. -/
lemma dbarCoord_single {n : ℕ} {j l : Fin n} (h : l ≠ j) {u : ℂ → ℂ} (hu : ContDiff ℝ 1 u)
    (z : Fin n → ℂ) : dbarCoord l (fun y => u (y j)) z = 0 := by
  have hfun : (fun w : ℂ => (fun y : Fin n → ℂ => u (y j)) (Function.update z l w))
      = fun _ => u (z j) := by
    funext w
    show u ((Function.update z l w) j) = u (z j)
    rw [Function.update_apply, if_neg (fun hjl => h hjl.symm)]
  have hdiff : DifferentiableAt ℝ (fun y : Fin n → ℂ => u (y j)) (Function.update z l (z l)) := by
    rw [Function.update_eq_self]
    exact (hu.comp (contDiff_apply ℝ ℂ j)).contDiffAt.differentiableAt (by simp)
  have h2 := dbarSolution_dbarC_update_eq_dbarCoord l
    (g := fun y : Fin n → ℂ => u (y j)) (z := z) (u := z l) hdiff
  rw [Function.update_eq_self, hfun] at h2
  rw [← h2]
  simp [dbarC]

/-- The `∂̄_l`-derivative of the cutoff `cutF j` vanishes for `l ≠ j`. -/
lemma dbarCoord_cutF_eq_zero {n : ℕ} {j l : Fin n} (h : l ≠ j) (z : Fin n → ℂ) :
    dbarCoord l (cutF j) z = 0 := by
  show dbarCoord l (fun y => openCut (y j)) z = 0
  exact dbarCoord_single h (openCut_props_infty.1.of_le (le_infty _)) z

/-- Product rule for the cutoff: `∂̄_l (χ_j · g) = χ_j · ∂̄_l g` for `l ≠ j`. -/
lemma dbarCoord_cutF_mul {n : ℕ} {j l : Fin n} (h : l ≠ j) {g : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hg : DifferentiableAt ℝ g z) :
    dbarCoord l (fun y => cutF j y * g y) z = cutF j z * dbarCoord l g z := by
  have hχ : DifferentiableAt ℝ (cutF j) z :=
    (contDiff_cutF j).contDiffAt.differentiableAt (by simp)
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul l _ _ z hχ hg, dbarCoord_cutF_eq_zero h z]
  ring

/-- The transform vanishes when its data vanishes on the fibre through the evaluation point. -/
lemma dbarTransform_eq_zero_of_fiber {n : ℕ} {ρ : ℝ} {j : Fin n} {g : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (h : ∀ y, (∀ l, l ≠ j → y l = z l) → g y = 0) :
    dbarTransform ρ j g z = 0 := by
  unfold dbarTransform
  rw [show (fun w : ℂ => g (z + Function.update (0 : Fin n → ℂ) j w) / w) = fun _ => 0 from by
    funext w
    rw [h _ (fun l hl => by simp [Pi.add_apply, Function.update_apply, hl]), zero_div]]
  simp

/-- The integral of the zero function. -/
lemma dbarTransform_zero {n : ℕ} (ρ : ℝ) (j : Fin n) (z : Fin n → ℂ) :
    dbarTransform ρ j (0 : (Fin n → ℂ) → ℂ) z = 0 := by
  unfold dbarTransform
  simp

/-! ## The recursion -/

/-- One step of the recursion: applying the transform in the `j`-th coordinate to the
cut-off data. -/
noncomputable def stepData {n : ℕ} (j : Fin n) (F : Fin n → (Fin n → ℂ) → ℂ) :
    Fin n → (Fin n → ℂ) → ℂ :=
  fun k => dbarTransform trRho j (fun y => cutFbar j y * F k y)

/-- The data at stage `m` of the recursion: the original data with `m` coordinates processed. -/
noncomputable def recF {n : ℕ} (f : Fin n → (Fin n → ℂ) → ℂ) (m : ℕ) :
    Fin n → (Fin n → ℂ) → ℂ :=
  Nat.rec f (fun m Fprev => if h : m < n then stepData ⟨m, h⟩ Fprev else Fprev) m

@[simp] lemma recF_zero {n : ℕ} (f : Fin n → (Fin n → ℂ) → ℂ) : recF f 0 = f := rfl

lemma recF_succ {n : ℕ} (f : Fin n → (Fin n → ℂ) → ℂ) (m : ℕ) :
    recF f (m + 1) = if h : m < n then stepData ⟨m, h⟩ (recF f m) else recF f m := rfl

lemma recF_succ_of_lt {n : ℕ} (f : Fin n → (Fin n → ℂ) → ℂ) {m : ℕ} (h : m < n) :
    recF f (m + 1) = stepData ⟨m, h⟩ (recF f m) := by
  rw [recF_succ]; simp [h]

/-- The explicit solution. -/
noncomputable def recU {n : ℕ} (f : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  ∑ j : Fin n, dbarTransform trRho j (fun y => cutF j y * recF f (j : ℕ) j y) z

/-! ## Properties of the cutoff -/

lemma contDiff_dbarC_openCut : ContDiff ℝ ∞ (dbarC openCut) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ openCut) :=
    openCut_props_infty.1.fderiv_right (m := ∞) le_rfl
  have h1 : ContDiff ℝ ∞ (fun z : ℂ => fderiv ℝ openCut z 1) := hfd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun z : ℂ => fderiv ℝ openCut z Complex.I) :=
    hfd.clm_apply contDiff_const
  rw [show dbarC openCut = fun z => (1 / 2 : ℂ) *
      ((fderiv ℝ openCut z) 1 + Complex.I * (fderiv ℝ openCut z) Complex.I) from rfl]
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

lemma cutF_eq_one {n : ℕ} {j : Fin n} {y : Fin n → ℂ} (h : ‖y j‖ ≤ cutIn) : cutF j y = 1 :=
  openCut_props_infty.2.1 _ h

lemma cutF_eq_zero {n : ℕ} {j : Fin n} {y : Fin n → ℂ} (h : cutOut ≤ ‖y j‖) : cutF j y = 0 :=
  openCut_props_infty.2.2.1 _ h

lemma cutFbar_eq_zero_of_le {n : ℕ} {j : Fin n} {y : Fin n → ℂ} (h : ‖y j‖ ≤ cutIn) :
    cutFbar j y = 0 :=
  openCut_props_infty.2.2.2.2.1 _ h

lemma cutFbar_eq_zero_of_ge {n : ℕ} {j : Fin n} {y : Fin n → ℂ} (h : cutOut ≤ ‖y j‖) :
    cutFbar j y = 0 :=
  openCut_props_infty.2.2.2.2.2.1 _ h

lemma dbarCoord_cutFbar_eq_zero {n : ℕ} {j l : Fin n} (h : l ≠ j) (z : Fin n → ℂ) :
    dbarCoord l (cutFbar j) z = 0 :=
  dbarCoord_single h (contDiff_dbarC_openCut.of_le (le_infty _)) z

lemma dbarCoord_cutFbar_mul {n : ℕ} {j l : Fin n} (h : l ≠ j) {G : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (hG : DifferentiableAt ℝ G z) :
    dbarCoord l (fun y => cutFbar j y * G y) z = cutFbar j z * dbarCoord l G z := by
  have hχ : DifferentiableAt ℝ (cutFbar j) z :=
    contDiff_cutFbar j |>.contDiffAt |>.differentiableAt (by simp)
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul l _ _ z hχ hG, dbarCoord_cutFbar_eq_zero h z]
  ring

/-! ## The invariants of the recursion -/

lemma recF_inv {n : ℕ} {k : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ (k + 1) (f j)) (hcl : IsClosedForm f) :
    ∀ s : ℕ, s ≤ n →
      (∀ j, ContDiff ℝ (k + 1) (recF f s j)) ∧
      (∀ l : Fin n, (l : ℕ) < s → ∀ j z, ‖z l‖ < cutIn → dbarCoord l (recF f s j) z = 0) ∧
      (∀ i l : Fin n, s ≤ (i : ℕ) → s ≤ (l : ℕ) → ∀ z,
        dbarCoord l (recF f s i) z = dbarCoord i (recF f s l) z) := by
  intro s
  induction s with
  | zero =>
      intro _
      refine ⟨hf, ?_, ?_⟩
      · intro l hl; exact absurd hl (Nat.not_lt_zero _)
      · intro i l _ _ z; exact (hcl l i z).symm
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
        · intro i l hi hl z
          rw [hrec]
          simp only [stepData]
          have hine : i ≠ j := by
            intro hij; rw [hij, hjs] at hi; exact absurd hi (by omega)
          have hlne : l ≠ j := by
            intro hlj; rw [hlj, hjs] at hl; exact absurd hl (by omega)
          have hfun : (fun y => dbarCoord l (fun y' => cutFbar j y' * recF f s i y') y)
              = fun y => dbarCoord i (fun y' => cutFbar j y' * recF f s l y') y := by
            funext y
            rw [dbarCoord_cutFbar_mul hlne ((ih1 i).differentiable (by simp)).differentiableAt,
              dbarCoord_cutFbar_mul hine ((ih1 l).differentiable (by simp)).differentiableAt,
              ih3 i l (by omega) (by omega) y]
          rw [dbarTransform_dbarCoord j l (hC1 i) z,
            dbarTransform_dbarCoord j i (hC1 l) z, hfun]
      · have hrec : recF f (s + 1) = recF f s := by
          rw [recF_succ]; simp [hlt]
        have hsn : n ≤ s := not_lt.mp hlt
        rw [hrec]
        refine ⟨ih1, ?_, ?_⟩
        · intro l hl i z hz
          exact ih2 l (by omega) i z hz
        · intro i l hi hl z
          exact ih3 i l (by omega) (by omega) z

/-! ## The sum rule for `dbarCoord` -/

lemma differentiableAt_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → (Fin n → ℂ) → ℂ) {z : Fin n → ℂ} (hg : ∀ j ∈ s, DifferentiableAt ℝ (g j) z) :
    DifferentiableAt ℝ (fun y => ∑ j ∈ s, g j y) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableAt_const (0 : ℂ)
  | insert a s ha ih =>
      have hsplit : (fun y : Fin n → ℂ => ∑ j ∈ insert a s, g j y)
          = fun y => g a y + ∑ j ∈ s, g j y := by
        funext y; rw [Finset.sum_insert ha]
      rw [hsplit]
      exact (hg a (Finset.mem_insert_self a s)).add
        (ih (fun j hj => hg j (Finset.mem_insert_of_mem hj)))

lemma dbarCoord_finset_sum {n : ℕ} (i : Fin n) {ι : Type*} (s : Finset ι)
    (g : ι → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hg : ∀ j ∈ s, DifferentiableAt ℝ (g j) z) :
    dbarCoord i (fun y => ∑ j ∈ s, g j y) z = ∑ j ∈ s, dbarCoord i (g j) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dbarCoord]
  | insert a s ha ih =>
      have hsplit : (fun y : Fin n → ℂ => ∑ j ∈ insert a s, g j y)
          = fun y => g a y + ∑ j ∈ s, g j y := by
        funext y; rw [Finset.sum_insert ha]
      rw [hsplit, Finset.sum_insert ha,
        Work.CR.Flat.Polydisc.dbarCoord_add i _ _ z
          (hg a (Finset.mem_insert_self a s))
          (differentiableAt_finset_sum s g (fun j hj => hg j (Finset.mem_insert_of_mem hj))),
        ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))]

/-! ## The equation satisfied by the explicit solution -/

lemma recF_succ_eq {n : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ} {m : ℕ} (h : m < n) :
    recF f (m + 1) = stepData (⟨m, h⟩ : Fin n) (recF f m) :=
  recF_succ_of_lt f h

lemma recU_solves {n : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf1 : ∀ j, ContDiff ℝ 1 (f j)) (hcl : IsClosedForm f) :
    ∀ (i : Fin n) (z : Fin n → ℂ), (∀ l, ‖z l‖ < eqRad) → dbarCoord i (fun z => recU f z) z = f i z := by
  intro i z hz
  -- data smoothness at every stage
  have hsm : ∀ (m : ℕ), m ≤ n → ∀ j, ContDiff ℝ 1 (recF f m j) := fun m hm j =>
    (recF_inv (k := 0) hf1 hcl m hm).1 j
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
    obtain ⟨hsmj, hholj, hclj⟩ := recF_inv (k := 0) hf1 hcl (j : ℕ) (le_of_lt j.isLt)
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
      have hclfun : (fun y => cutF j y * dbarCoord i (recF f (j : ℕ) j) y)
          = fun y => cutF j y * dbarCoord j (recF f (j : ℕ) i) y := by
        funext y; rw [hclj j i le_rfl (le_of_lt hji) y]
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

/-- The explicit solution is `C^{k+1}`. -/
lemma contDiff_recU {n : ℕ} {k : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ (k + 1) (f j)) (hcl : IsClosedForm f) :
    ContDiff ℝ (k + 1) (fun z => recU f z) := by
  have hinv := recF_inv (k := k) hf hcl
  rw [show (fun z => recU f z) = fun z => ∑ j : Fin n,
      dbarTransform trRho j (fun y => cutF j y * recF f (j : ℕ) j y) z from rfl]
  refine ContDiff.sum fun j _ => ?_
  refine contDiff_dbarTransform (b := cutOut) (by norm_num [cutOut, trRho]) j (k + 1) ?_ ?_
  · exact ((contDiff_cutF j).of_le (le_infty _)).mul ((hinv (j : ℕ) (le_of_lt j.isLt)).1 j)
  · intro y hy; rw [cutF_eq_zero hy, zero_mul]

/-! ## Smoothness wrappers at a finite order -/

lemma contDiff_cutF_of_le {n : ℕ} (j : Fin n) (m : ℕ) : ContDiff ℝ m (cutF j) :=
  (contDiff_cutF j).of_le (le_infty m)

lemma contDiff_cutFbar_of_le {n : ℕ} (j : Fin n) (m : ℕ) : ContDiff ℝ m (cutFbar j) :=
  (contDiff_cutFbar j).of_le (le_infty m)

/-! ## Lipschitz and size bounds for the cutoff -/

/-- A Lipschitz constant for the cutoff `openCut` on `ℂ`. -/
theorem openCut_lipschitz :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ζ ζ' : ℂ, ‖openCut ζ - openCut ζ'‖ ≤ L * ‖ζ - ζ'‖ := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hasCompactSupport_openCut
    openCut_props_infty.1 (by simp)
  refine ⟨(L : ℝ), L.coe_nonneg, fun ζ ζ' => ?_⟩
  have h := hL.dist_le_mul ζ ζ'
  rw [dist_eq_norm, dist_eq_norm] at h
  simpa using h

/-- The coordinate cutoff `cutF j` is Lipschitz with any Lipschitz constant of `openCut`. -/
lemma norm_cutF_sub_le {n : ℕ} (j : Fin n) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ ζ ζ' : ℂ, ‖openCut ζ - openCut ζ'‖ ≤ L * ‖ζ - ζ'‖) (a a' : Fin n → ℂ) :
    ‖cutF j a - cutF j a'‖ ≤ L * ‖a - a'‖ := by
  have h : ‖cutF j a - cutF j a'‖ = ‖openCut (a j) - openCut (a' j)‖ := rfl
  rw [h]
  calc ‖openCut (a j) - openCut (a' j)‖ ≤ L * ‖a j - a' j‖ := hL _ _
    _ ≤ L * ‖a - a'‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm (a - a') j) hL0

lemma norm_cutF_le_one {n : ℕ} (j : Fin n) (a : Fin n → ℂ) : ‖cutF j a‖ ≤ 1 :=
  openCut_props_infty.2.2.2.1 _

lemma norm_cutFbar_le {n : ℕ} (j : Fin n) {cχ : ℝ}
    (h : ∀ ζ : ℂ, ‖dbarC openCut ζ‖ ≤ cχ) (a : Fin n → ℂ) : ‖cutFbar j a‖ ≤ cχ := h _

/-! ## Membership facts for the tracked region -/

/-- `trackSet` is contained in the unit polydisc. -/
lemma trackSet_subset_unit {n : ℕ} {z : Fin n → ℂ} (hz : z ∈ trackSet) :
    z ∈ polydisc (0 : Fin n → ℂ) (fun _ => 1) := by
  intro l
  have h := hz l
  simp only [sub_zero, norm_zero]
  rw [trTrack] at h
  norm_num at h ⊢
  linarith

/-- Every `z` of `solveSet`, i.e. with all coordinates below `eqRad`, is in `trackSet`. -/
lemma trackSet_of_solveSet {n : ℕ} {z : Fin n → ℂ}
    (hz : ∀ l, ‖z l‖ < eqRad) : z ∈ trackSet := by
  intro l
  rw [trTrack]
  have := hz l
  rw [eqRad] at this
  norm_num at this ⊢
  linarith

/-- Changing only the `j`-th coordinate of a point of `trackSet` keeps the point in
`trackSet` as long as the new `j`-th coordinate is still below `trTrack`. -/
lemma trackSet_update {n : ℕ} {j : Fin n} {a z : Fin n → ℂ} (hz : z ∈ trackSet)
    (ha : ∀ l, l ≠ j → a l = z l) (haj : ‖a j‖ < trTrack) : a ∈ trackSet := by
  intro l
  by_cases hl : l = j
  · subst hl; exact haj
  · rw [ha l hl]; exact hz l

lemma cutOut_lt_trTrack : cutOut < trTrack := by norm_num [cutOut, trTrack]
lemma cutIn_lt_trTrack : cutIn < trTrack := by norm_num [cutIn, trTrack]
lemma trTrack_lt_one : trTrack < 1 := by norm_num [trTrack]
lemma eqRad_le_cutOut : eqRad ≤ cutOut := by norm_num [eqRad, cutOut]
lemma cutOut_pos' : 0 < cutOut := cutOut_pos

end Work.CR.Flat.Cauchy
