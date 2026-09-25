/-
# The pulled-back, cut-off datum: differentiability, closedness, size

For the construction `Work.NN.Ratio.Geom` at the thresholds read off from `η`, the datum is the
`(0,1)`-form `dataOf η ρ f = pull (scale η ρ) (polCut η ρ · f)`.  On the tracking polydisc
`‖y l‖ < thrT η` the cutoff `polCut η ρ` is identically `1` at the dilated point `Φ y`, so there
the datum is just the rescaled datum `y ↦ scale η ρ j · f j (Φ y)`.  This file records the
consequences: differentiability, the `∂̄`-chain rule, preservation of closedness, and the
`C^{0,α}` size estimate in terms of the size of `f` on `polydisc 0 ρ`.
-/
import Mathlib
import Submission.Work.NN.Ratio.Scale
import Submission.Work.NN.Ratio.holderNorm_zero_congr
import Submission.Work.CR.Flat.Holder.holderNorm_zero_comp_le
import Submission.Work.CR.Flat.Holder.holderNorm_smul

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter
open Work.CR.Flat

namespace Work.NN.Ratio

variable {n : ℕ}

/-! ## Elementary `∂̄`-calculus -/

/-- `∂̄` depends only on the germ. -/
lemma dbarCoord_congr_eventually {n : ℕ} (a : Fin n) {f g : (Fin n → ℂ) → ℂ}
    {y : Fin n → ℂ} (h : f =ᶠ[𝓝 y] g) : dbarCoord a f y = dbarCoord a g y := by
  unfold dbarCoord
  rw [h.fderiv_eq]

/-- `∂̄` of a constant multiple. -/
lemma dbarCoord_const_mul {n : ℕ} (j : Fin n) (c : ℂ) {g : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (hg : DifferentiableAt ℝ g z) :
    dbarCoord j (fun w => c * g w) z = c * dbarCoord j g z := by
  have h : fderiv ℝ (fun w => c * g w) z = c • fderiv ℝ g z := fderiv_const_mul hg c
  rw [dbarCoord, dbarCoord, h]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- Chain rule for the diagonal dilation `Φ`. -/
lemma dbarCoord_Phi (S : Fin n → ℝ) (l : Fin n) {g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ}
    (hg : DifferentiableAt ℝ g (Phi S y)) :
    dbarCoord l (fun y' => g (Phi S y')) y = (S l : ℂ) * dbarCoord l g (Phi S y) := by
  have h2 : (fun i => (0 : Fin n → ℂ) i + (S i : ℂ) * y i) = Phi S y := by
    funext i; simp [Phi]
  have h1 : (fun y' : Fin n → ℂ => g (Phi S y'))
      = fun z' => g (fun i => (0 : Fin n → ℂ) i + (S i : ℂ) * z' i) := by
    funext y'; congr 1; funext i; simp [Phi]
  rw [h1]
  rw [Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine S (0 : Fin n → ℂ) l (U := g) (z := y) (by rw [h2]; exact hg)]
  rw [h2]

/-- The composed datum `y ↦ g (Φ y)` is differentiable as soon as `g` is at the image point. -/
lemma differentiableAt_Phi_comp (S : Fin n → ℝ) {g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ}
    (hg : DifferentiableAt ℝ g (Phi S y)) : DifferentiableAt ℝ (fun y' => g (Phi S y')) y :=
  hg.comp y ((contDiff_Phi S).contDiffAt.differentiableAt (by simp))

/-- Chain rule for a constant multiple of the dilated datum. -/
lemma dbarCoord_smul_Phi (S : Fin n → ℝ) (l : Fin n) (c : ℂ) {g : (Fin n → ℂ) → ℂ}
    {y : Fin n → ℂ} (hg : DifferentiableAt ℝ g (Phi S y)) :
    dbarCoord l (fun y' => c * g (Phi S y')) y = c * (S l : ℂ) * dbarCoord l g (Phi S y) := by
  rw [dbarCoord_const_mul l c (differentiableAt_Phi_comp S hg), dbarCoord_Phi S l hg]
  ring

/-- The set `‖y l‖ < c` for all `l` is a neighbourhood of such a point. -/
lemma eventually_norm_lt' {c : ℝ} {w : Fin n → ℂ} (hw : ∀ m, ‖w m‖ < c) :
    ∀ᶠ w' in 𝓝 w, ∀ m, ‖w' m‖ < c := by
  rw [Filter.eventually_all]
  intro m
  have hcont : Continuous (fun w' : Fin n → ℂ => ‖w' m‖) :=
    continuous_norm.comp (continuous_apply m)
  exact (isOpen_lt hcont continuous_const).mem_nhds (hw m)

/-! ## The datum `dataOf` -/

/-- On the tracking polydisc, the datum agrees with the rescaled datum. -/
lemma dataOf_eventuallyEq {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) (f : Fin n → (Fin n → ℂ) → ℂ) (j : Fin n) {y : Fin n → ℂ}
    (hy : y ∈ polydisc 0 (fun _ => thrT η)) :
    dataOf η ρ f j =ᶠ[𝓝 y] (fun y' => (scale η ρ j : ℂ) * f j (Phi (scale η ρ) y')) := by
  filter_upwards [(isOpen_polydisc (0 : Fin n → ℂ) (fun _ => thrT η)).mem_nhds hy] with y' hy'
  rw [dataOf_apply, polCut_eq_one_of_Phi (y := y') h0 h1 hρ hy', one_mul]

/-- The datum is globally `C^{k+1}` when `f` is. -/
lemma contDiff_dataOf {η : ℝ} {ρ : Fin n → ℝ} {k : ℕ}
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContDiff ℝ (k + 1) (f j)) (j : Fin n) :
    ContDiff ℝ (k + 1) (dataOf η ρ f j) := by
  have h : (fun y => (scale η ρ j : ℂ) * (polCut η ρ (Phi (scale η ρ) y)
      * f j (Phi (scale η ρ) y))) = dataOf η ρ f j := by
    funext y; rw [dataOf_apply]
  rw [← h]
  have h1 : ContDiff ℝ (k + 1) (fun y => polCut η ρ (Phi (scale η ρ) y)) :=
    ((contDiff_polCut ρ).of_le (le_infty (k + 1))).comp
      ((contDiff_Phi (scale η ρ)).of_le (le_infty (k + 1)))
  have h2 : ContDiff ℝ (k + 1) (fun y => f j (Phi (scale η ρ) y)) :=
    (hf j).comp ((contDiff_Phi (scale η ρ)).of_le (le_infty (k + 1)))
  exact contDiff_const.mul (h1.mul h2)

/-- Closedness of the datum on the tracking polydisc, from global closedness of `f`. -/
theorem dataOf_closed {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hfcl : IsClosedForm f) :
    ∀ j l (y : Fin n → ℂ), y ∈ polydisc 0 (fun _ => thrT η) →
      dbarCoord l (dataOf η ρ f j) y = dbarCoord j (dataOf η ρ f l) y := by
  intro j l y hy
  have hdj : DifferentiableAt ℝ (f j) (Phi (scale η ρ) y) :=
    (hf j).contDiffAt.differentiableAt (by simp)
  have hdl : DifferentiableAt ℝ (f l) (Phi (scale η ρ) y) :=
    (hf l).contDiffAt.differentiableAt (by simp)
  rw [dbarCoord_congr_eventually l (dataOf_eventuallyEq h0 h1 hρ f j hy),
    dbarCoord_congr_eventually j (dataOf_eventuallyEq h0 h1 hρ f l hy),
    dbarCoord_smul_Phi (scale η ρ) l (scale η ρ j : ℂ) hdj,
    dbarCoord_smul_Phi (scale η ρ) j (scale η ρ l : ℂ) hdl,
    hfcl l j (Phi (scale η ρ) y)]
  ring

/-- Smoothness of the datum on the tracking polydisc, from smoothness of `f` on `polydisc 0 ρ`. -/
lemma contDiffOn_dataOf {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {m : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiffOn ℝ m (f j) (polydisc 0 ρ)) (j : Fin n) :
    ContDiffOn ℝ m (dataOf η ρ f j) (polydisc 0 (fun _ => thrT η)) := by
  have hmaps : MapsTo (Phi (scale η ρ)) (polydisc 0 (fun _ => thrT η)) (polydisc 0 ρ) :=
    fun y hy => phi_mem_polydisc h0 h1 hρ hy
  have hcomp : ContDiffOn ℝ m (fun y => f j (Phi (scale η ρ) y))
      (polydisc 0 (fun _ => thrT η)) :=
    (hf j).comp (((contDiff_Phi (scale η ρ)).of_le (le_infty m)).contDiffOn) hmaps
  have hmul : ContDiffOn ℝ m (fun y => (scale η ρ j : ℂ) * f j (Phi (scale η ρ) y))
      (polydisc 0 (fun _ => thrT η)) :=
    (contDiff_const : ContDiff ℝ m (fun _ : Fin n → ℂ => (scale η ρ j : ℂ))).contDiffOn.mul hcomp
  refine (contDiffOn_congr ?_).mpr hmul
  intro y hy
  rw [dataOf_apply, polCut_eq_one_of_Phi (y := y) h0 h1 hρ hy, one_mul]

/-- The `C^{0,α}` size of the datum in terms of the size of `f` on `polydisc 0 ρ`. -/
theorem holderNorm_dataOf_le {α : ℝ} (hα : 0 < α) {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 ρ)) (j : Fin n) :
    holderNorm 0 α (dataOf η ρ f j) (polydisc 0 (fun _ => thrT η))
      ≤ ENNReal.ofReal (scale η ρ j)
        * (max 1 (ENNReal.ofReal ((∑ l, scale η ρ l) ^ α))
          * holderNorm 0 α (f j) (polydisc 0 ρ)) := by
  have hSpos : ∀ l, 0 < scale η ρ l := fun l => scale_pos h0 h1 hρ l
  have hsum : 0 ≤ ∑ l, scale η ρ l := Finset.sum_nonneg fun l _ => (hSpos l).le
  have hmaps : MapsTo (Phi (scale η ρ)) (polydisc 0 (fun _ => thrT η)) (polydisc 0 ρ) :=
    fun y hy => phi_mem_polydisc h0 h1 hρ hy
  have hlip : ∀ x ∈ polydisc 0 (fun _ => thrT η), ∀ y ∈ polydisc 0 (fun _ => thrT η),
      ‖Phi (scale η ρ) x - Phi (scale η ρ) y‖ ≤ (∑ l, scale η ρ l) * ‖x - y‖ :=
    fun x _ y _ => norm_Phi_sub_le (fun l => (hSpos l).le) x y
  have hcomp := Work.CR.Flat.Holder.holderNorm_zero_comp_le (hα := hα) (hM := hsum)
    (Ω := polydisc 0 (fun _ => thrT η)) (Ω' := polydisc 0 ρ)
    (Φ := Phi (scale η ρ)) (U := f j) hmaps hlip
  have hcont : ContDiffOn ℝ (0 : ℕ∞) (fun y => f j (Phi (scale η ρ) y))
      (polydisc 0 (fun _ => thrT η)) :=
    ((hf j).comp (((contDiff_Phi (scale η ρ)).of_le (le_infty 1)).contDiffOn) hmaps).of_le
      (by exact_mod_cast (Nat.zero_le 1 : 0 ≤ 1))
  have huzero : UniqueDiffOn ℝ (polydisc (0 : Fin n → ℂ) (fun _ => thrT η)) :=
    (isOpen_polydisc (0 : Fin n → ℂ) (fun _ => thrT η)).uniqueDiffOn
  have hcongr : holderNorm 0 α (dataOf η ρ f j) (polydisc 0 (fun _ => thrT η))
      = holderNorm 0 α (fun y => (scale η ρ j : ℂ) * f j (Phi (scale η ρ) y))
          (polydisc 0 (fun _ => thrT η)) := by
    refine holderNorm_zero_congr fun y hy => ?_
    rw [dataOf_apply, polCut_eq_one_of_Phi (y := y) h0 h1 hρ hy, one_mul]
  rw [hcongr]
  have hfun : (fun y : Fin n → ℂ => (scale η ρ j : ℂ) * f j (Phi (scale η ρ) y))
      = (scale η ρ j : ℂ) • (fun y => f j (Phi (scale η ρ) y)) := by
    funext y; rfl
  rw [hfun, Work.CR.Flat.Holder.holderNorm_smul (k := 0) (α := α) (c := (scale η ρ j : ℂ))
    (f := fun y => f j (Phi (scale η ρ) y)) hcont huzero,
    Complex.norm_real, Real.norm_of_nonneg (hSpos j).le]
  exact mul_le_mul_of_nonneg_left hcomp bot_le

/-! ## Linearity and smoothness of the pull-back -/

lemma pull_add (S : Fin n → ℝ) (h₁ h₂ : Fin n → (Fin n → ℂ) → ℂ) :
    pull S (h₁ + h₂) = pull S h₁ + pull S h₂ := by
  funext j y
  simp only [pull_apply, Pi.add_apply]
  ring

lemma pull_smul (S : Fin n → ℝ) (c : ℝ) (h : Fin n → (Fin n → ℂ) → ℂ) :
    pull S (c • h) = c • pull S h := by
  funext j y
  simp only [pull_apply, Pi.smul_apply, Complex.real_smul]
  ring

/-- The pull-back of a globally `C^k` datum is globally `C^k`. -/
lemma contDiff_pull {S : Fin n → ℝ} {k : ℕ} {h : Fin n → (Fin n → ℂ) → ℂ}
    (hh : ∀ j, ContDiff ℝ k (h j)) (j : Fin n) : ContDiff ℝ k (pull S h j) := by
  have hh' : (fun y => (S j : ℂ) * h j (Phi S y)) = pull S h j := by
    funext y; rw [pull_apply]
  rw [← hh']
  exact contDiff_const.mul ((hh j).comp ((contDiff_Phi S).of_le (le_infty k)))

/-- Chain rule for the inverse dilation `Ψ`. -/
lemma dbarCoord_Psi (S : Fin n → ℝ) (j : Fin n) {U : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hU : DifferentiableAt ℝ U (Psi S z)) :
    dbarCoord j (fun z' => U (Psi S z')) z = (((S j)⁻¹ : ℝ) : ℂ) * dbarCoord j U (Psi S z) := by
  have h2 : (fun i => (0 : Fin n → ℂ) i + (((S i)⁻¹ : ℝ) : ℂ) * z i) = Psi S z := by
    funext i; simp [Psi]
  have h1 : (fun z' : Fin n → ℂ => U (Psi S z'))
      = fun z' => U (fun i => (0 : Fin n → ℂ) i + (((S i)⁻¹ : ℝ) : ℂ) * z' i) := by
    funext z'; congr 1; funext i; simp [Psi]
  rw [h1]
  rw [Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine (fun i => (S i)⁻¹) (0 : Fin n → ℂ) j
    (U := U) (z := z) (by rw [h2]; exact hU)]
  rw [h2]

end Work.NN.Ratio
