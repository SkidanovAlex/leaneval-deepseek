/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Iterated directional derivatives of the Bochner–Martinelli potential

The Bochner–Martinelli potential of a family `f` is

  `bmPotential f z = Σ_j ∫ ζ, \overline{(ζ_j - z_j)} / ‖ζ - z‖^{2n} · f_j ζ dζ`,

the classical solution operator for the flat `∂̄`-equation (see
`Submission/Work/CR/Flat/Cauchy/bmDefs.lean`).  Its kernel is a fixed convolution kernel, so
differentiating the potential in `z` never touches the (singular) kernel: the derivative acts on
the data.  Here we prove the corresponding statement for *iterated* directional derivatives,
`D^i (bmPotential f)(z)[v] = bmPotential (fun j y => D^i (f_j)(y)[v]) z`.

The proof has two ingredients.

* `bmPotential_fderiv_of_hasCompactSupport` — the single step: for compactly supported `C¹` data,
  `fderiv ℝ (bmPotential f) z v = bmPotential (fun j y => fderiv ℝ (f j) y v) z`.  This is
  `HasCompactSupport.hasFDerivAt_convolution_right` applied to the convolution representation
  `bmPotential_eq_neg_conv`, combined with `convolution_precompR_apply` and the change of
  variables `ζ ↦ z - ζ` (`integral_bmKernel_sub_eq`).

* the induction on `i`, using `iteratedFDeriv_succ_apply_left'` and the fact that taking a
  directional derivative of the data preserves both compact support
  (`HasCompactSupport.iteratedFDeriv`) and smoothness.

Everything is stated for data supported in a fixed compact set; the support hypothesis of the
paper's statement (`G j` vanishing off the open half-size polydisc) is converted with
`hasCompactSupport_of_halfPolydisc`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one

noncomputable section

set_option maxHeartbeats 1600000

open scoped NNReal ENNReal Convolution Topology
open MeasureTheory Set Filter

namespace Work.CR.Flat.Cauchy

/-! ## Regularity of the potential -/

/-- The Bochner–Martinelli potential of compactly supported `C^i` data is `C^i`: it is a finite sum
of convolutions of the (locally integrable) kernel with the data, and
`HasCompactSupport.contDiff_convolution_right` applies to each of these. -/
lemma bmPotential_contDiff_of_hasCompactSupport {n : ℕ} (hn : 0 < n) {i : ℕ}
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContDiff ℝ i (f j))
    (hcs : ∀ j, HasCompactSupport (f j)) : ContDiff ℝ i (bmPotential f) := by
  rw [bmPotential_eq_neg_conv f]
  exact ContDiff.neg (ContDiff.sum fun j _ => (hcs j).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) (locallyIntegrable_bmKernel hn j) (hf j))

/-! ## The single differentiation step -/

/-- **Differentiating the Bochner–Martinelli potential, compactly supported data.**

For `C¹` data `f` whose components have compact support, the derivative of the potential is the
potential of the derivative:

`fderiv ℝ (fun z => bmPotential f z) z v = bmPotential (fun j y => fderiv ℝ (f j) y v) z`.

The kernel is never differentiated: by `bmPotential_eq_neg_conv` the potential is minus a sum of
convolutions, `HasCompactSupport.hasFDerivAt_convolution_right` computes their derivatives, and
`convolution_precompR_apply` together with `integral_bmKernel_sub_eq` identifies the result with
the potential of the differentiated data. -/
lemma bmPotential_fderiv_of_hasCompactSupport {n : ℕ} (hn : 0 < n)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hcs : ∀ j, HasCompactSupport (f j)) (z v : Fin n → ℂ) :
    fderiv ℝ (fun z => bmPotential f z) z v
      = bmPotential (fun j y => fderiv ℝ (f j) y v) z := by
  have hderiv : HasFDerivAt (bmPotential f)
      (-∑ j, (bmKernel j ⋆[ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ),
          volume] fderiv ℝ (f j)) z) z := by
    rw [bmPotential_eq_neg_conv f]
    refine HasFDerivAt.neg ?_
    have hsum := HasFDerivAt.sum (u := Finset.univ) fun j _ =>
      (hcs j).hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
        (locallyIntegrable_bmKernel hn j) (hf j) z
    have hfun : (∑ j, (bmKernel j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f j)) =
        fun w => ∑ j, (bmKernel j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f j) w := by
      funext w; rw [Finset.sum_apply]
    rw [hfun] at hsum
    exact hsum
  have hC : ∀ j, (bmKernel j ⋆[ContinuousLinearMap.precompR (Fin n → ℂ)
        (ContinuousLinearMap.mul ℝ ℂ), volume] fderiv ℝ (f j)) z v
      = -∫ ζ, bmKernel j (ζ - z) * (fderiv ℝ (f j) ζ v) := by
    intro j
    rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ) (locallyIntegrable_bmKernel hn j)
      ((hcs j).fderiv ℝ) ((hf j).continuous_fderiv (by norm_num)) z v, convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    rw [integral_bmKernel_sub_eq j (fun y => fderiv ℝ (f j) y v) z, neg_neg]
  rw [hderiv.fderiv]
  simp only [neg_apply, sum_apply]
  rw [Finset.sum_congr rfl (fun j _ => hC j), Finset.sum_neg_distrib, neg_neg]
  rfl

/-! ## Iteration -/

/-- A component of the differentiated data which is supported in a compact set stays compactly
supported after evaluating the (multilinear) iterated derivative at a fixed tuple. -/
lemma hasCompactSupport_iteratedFDeriv_apply {n : ℕ} {i : ℕ}
    {f : Fin n → (Fin n → ℂ) → ℂ} (hcs : ∀ j, HasCompactSupport (f j)) (j : Fin n)
    (v : Fin i → (Fin n → ℂ)) :
    HasCompactSupport (fun y => iteratedFDeriv ℝ i (f j) y v) := by
  refine IsCompact.of_isClosed_subset (s := tsupport (iteratedFDeriv ℝ i (f j))) ?_ ?_ ?_
  · exact (hcs j).iteratedFDeriv i
  · exact isClosed_tsupport _
  · have hsub : Function.support (fun y => iteratedFDeriv ℝ i (f j) y v)
        ⊆ Function.support (iteratedFDeriv ℝ i (f j)) := by
      intro y hy
      rw [Function.mem_support] at hy ⊢
      intro h
      exact hy (by rw [h]; rfl)
    exact (closure_minimal (hsub.trans (subset_tsupport _)) (isClosed_tsupport _))

/-- **The potential commutes with iterated directional derivatives (compact support version).**

For a family `f` of `C^i` functions with compact support, every iterated directional derivative of
the potential is the potential of the corresponding iterated derivative:

`D^i (bmPotential f)(z)[v] = bmPotential (fun j y => D^i (f_j)(y)[v]) z`. -/
lemma bmPotential_iteratedFDeriv_of_hasCompactSupport {n : ℕ} (hn : 0 < n) :
    ∀ (i : ℕ) (f : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiff ℝ i (f j)) →
      (∀ j, HasCompactSupport (f j)) →
      ∀ (v : Fin i → (Fin n → ℂ)) (z : Fin n → ℂ),
      iteratedFDeriv ℝ i (fun z => bmPotential f z) z v
        = bmPotential (fun j y => iteratedFDeriv ℝ i (f j) y v) z := by
  intro i
  induction i with
  | zero =>
    intro f hf hcs v z
    simp
  | succ i ih =>
    intro f hf hcs v z
    have hF : ContDiff ℝ (i+1) (fun z => bmPotential f z) :=
      bmPotential_contDiff_of_hasCompactSupport hn hf hcs
    have hFdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ i (fun z => bmPotential f z)) z :=
      (hF.differentiable_iteratedFDeriv (m := i)
        (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self i)))).differentiableAt
    rw [hFdiff.iteratedFDeriv_succ_apply_left' (m := v)]
    have hf' : ∀ j, ContDiff ℝ i (f j) := fun j => (hf j).of_le (by exact_mod_cast Nat.le_succ i)
    have hv : (fun y => iteratedFDeriv ℝ i (fun z => bmPotential f z) y (Fin.tail v))
        = (fun y => bmPotential (fun j y' => iteratedFDeriv ℝ i (f j) y' (Fin.tail v)) y) := by
      funext y; exact ih f hf' hcs (Fin.tail v) y
    rw [hv]
    have hGcont : ∀ j, ContDiff ℝ 1 (fun y' => iteratedFDeriv ℝ i (f j) y' (Fin.tail v)) := by
      intro j
      exact (ContinuousLinearMap.contDiff
          (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => (Fin n → ℂ)) ℂ (Fin.tail v))).comp
        (ContDiff.iteratedFDeriv_right (i := i) (m := 1) (hf j)
          (by exact le_of_eq (add_comm (1 : WithTop ℕ∞) (↑i : WithTop ℕ∞))))
    have hGcs : ∀ j, HasCompactSupport (fun y' => iteratedFDeriv ℝ i (f j) y' (Fin.tail v)) :=
      fun j => hasCompactSupport_iteratedFDeriv_apply hcs j (Fin.tail v)
    rw [bmPotential_fderiv_of_hasCompactSupport hn hGcont hGcs z (v 0)]
    congr 1
    funext j y'
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ i (f j)) y' :=
      ((hf j).differentiable_iteratedFDeriv (m := i)
        (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self i)))).differentiableAt
    rw [fderiv_continuousMultilinear_apply_const_apply hd (Fin.tail v) (v 0),
        iteratedFDeriv_succ_apply_left]

/-- **The Bochner–Martinelli potential commutes with iterated directional derivatives.**

For a family `G` of `C^i` functions supported in the open half-size polydisc `polydisc c (R/2)`,
every iterated directional derivative of the potential is the potential of the corresponding
iterated derivative of the data:

`D^i (bmPotential G)(z)[v] = bmPotential (fun j y => D^i (G_j)(y)[v]) z`

for every tuple of directions `v : Fin i → (Fin n → ℂ)`.  This is the iteration of
`fderiv_bmPotential` (the kernel is a fixed convolution kernel and is never differentiated). -/
theorem bmPotential_iteratedFDeriv {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hR : ∀ j, 0 < R j) {i : ℕ} {G : Fin n → (Fin n → ℂ) → ℂ}
    (hG : ∀ j, ContDiff ℝ i (G j))
    (hsup : ∀ j z, (∃ k, R k / 2 ≤ ‖z k - c k‖) → G j z = 0) (v : Fin i → (Fin n → ℂ))
    (z : Fin n → ℂ) :
    iteratedFDeriv ℝ i (fun z => bmPotential G z) z v
      = bmPotential (fun j y => iteratedFDeriv ℝ i (G j) y v) z :=
  bmPotential_iteratedFDeriv_of_hasCompactSupport hn i G hG
    (fun j => hasCompactSupport_of_halfPolydisc hR (fun z hz => hsup j z hz)) v z

end Work.CR.Flat.Cauchy
