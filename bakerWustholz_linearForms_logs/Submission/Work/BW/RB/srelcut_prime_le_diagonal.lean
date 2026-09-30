import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.eval_scale_homPiece
import Submission.Work.BW.RB.srelcut_diagonal_c

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `srelcut_prime_le_diagonal`

Let `R = MR N = ℂ[X_{i,0}, X_{i,1} : i ∈ Fin (N+1)]` be the homogeneous coordinate ring of
`(P¹)^{N+1}` and let `y` be a point of the big torus chart (`y (i,0) ≠ 0` for all `i`).  Put

* `ptIdeal N y = ker (eval y)`, the maximal ideal of the point `y`;
* `diagIdeal N y = ⟨y_{i0} X_{i,1} - y_{i1} X_{i,0}⟩`, the ideal of the closure of the
  `(ℂ*)^{N+1}`-orbit through `y`, i.e. the cone over the "diagonal" point `(1, y_{i1}/y_{i0})`.

Then every **multihomogeneous** prime ideal `r ≤ ptIdeal N y` satisfies `r ≤ diagIdeal N y`:
a torus invariant closed subvariety of `(P¹)^{N+1}` passing through `[y]` contains the whole
diagonal line through `[y]`.

## Proof

Decompose `f ∈ r` into its multihomogeneous components `f_d` (`MultiHom N r`), each of which also
lies in `ptIdeal N y`.  For a single multihomogeneous `g ∈ homPiece N d` with `eval y g = 0` the
argument is:

* the cone point `z = (1, y_{i1}/y_{i0})` is obtained from `y` by the torus rescaling
  `X_{i,j} ↦ y_{i0} X_{i,j}`, and a multihomogeneous polynomial is an eigenvector of every such
  rescaling with eigenvalue `∏ᵢ y_{i0}^{dᵢ} ≠ 0` (`Work.BW.eval_scale_homPiece`); hence
  `eval z g = 0`;
* `diagΦ y` is the substitution `X_{i,0} ↦ X_i`, `X_{i,1} ↦ (y_{i1}/y_{i0}) X_i`, whose kernel is
  `diagIdeal N y`; evaluating `diagΦ y g` at an arbitrary point `a` is evaluating `g` at the
  torus rescaling of the cone point `z` by `a`, hence again an eigenvector value, and it vanishes:
  `eval a (diagΦ y g) = (∏ᵢ a_i^{dᵢ}) · eval z g = 0`;
* `MvPolynomial.funext` (ℂ is infinite) then gives `diagΦ y g = 0`, i.e. `g ∈ diagIdeal N y`.

Finally `f = ∑ᶠ d, f_d ∈ diagIdeal N y` because an ideal is closed under finite sums. -/

namespace Work.BW.RB

open MvPolynomial

noncomputable section

variable {N : ℕ}

/-- The cone point `(1, y_{i1}/y_{i0})` over the diagonal point of `y`. -/
def diagConePt (N : ℕ) (y : Fin (N + 1) × Fin 2 → ℂ) : Fin (N + 1) × Fin 2 → ℂ :=
  fun v => if v.2 = 0 then 1 else y (v.1, 1) / y (v.1, 0)

lemma diagConePt_apply_zero (y : Fin (N + 1) × Fin 2 → ℂ) (i : Fin (N + 1)) :
    diagConePt N y (i, 0) = 1 := by
  simp [diagConePt]

lemma diagConePt_apply_one (y : Fin (N + 1) × Fin 2 → ℂ) (i : Fin (N + 1)) :
    diagConePt N y (i, 1) = y (i, 1) / y (i, 0) := by
  simp [diagConePt]

/-- `wtPow N lam d = ∏ᵢ lamᵢ^{dᵢ}` does not vanish as soon as no `lamᵢ` does. -/
lemma wtPow_ne_zero {d : Fin (N + 1) →₀ ℕ} {lam : Fin (N + 1) → ℂ}
    (h : ∀ i, lam i ≠ 0) : wtPow N lam d ≠ 0 := by
  rw [wtPow]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (h i)

/-- Evaluating the substitution `diagΦ y` at a point `a` is evaluating at the point
`(aᵢ, aᵢ · y_{i1}/y_{i0})`, i.e. the torus rescaling by `a` of the cone point `diagConePt y`. -/
lemma eval_diagΦ_apply (y : Fin (N + 1) × Fin 2 → ℂ) (a : Fin (N + 1) → ℂ) (g : MR N) :
    MvPolynomial.eval a (diagΦ N y g) =
      MvPolynomial.eval (fun v : Fin (N + 1) × Fin 2 => a v.1 * diagConePt N y v) g := by
  have h : (MvPolynomial.eval a).comp (diagΦ N y) =
      MvPolynomial.eval (fun v : Fin (N + 1) × Fin 2 => a v.1 * diagConePt N y v) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
    · simp [diagΦ]
    · obtain ⟨i, j⟩ := v
      fin_cases j <;> simp [diagΦ, diagConePt, mul_comm]
  exact DFunLike.congr_fun h g

/-- **Scaling to the cone point.** A multihomogeneous polynomial of multidegree `d` vanishing at
`y` vanishes at the cone point `(1, y_{i1}/y_{i0})`. -/
lemma eval_diagConePt_eq_zero {d : Fin (N + 1) →₀ ℕ} {g : MR N} (hg : g ∈ homPiece N d)
    (y : Fin (N + 1) × Fin 2 → ℂ) (hy : ∀ i : Fin (N + 1), y (i, 0) ≠ 0)
    (hev : MvPolynomial.eval y g = 0) : MvPolynomial.eval (diagConePt N y) g = 0 := by
  have hpt : (fun v : Fin (N + 1) × Fin 2 => y (v.1, 0) * diagConePt N y v) = y := by
    funext v
    obtain ⟨i, j⟩ := v
    rcases eq_or_ne j 0 with hj | hj
    · rw [hj, diagConePt_apply_zero, mul_one]
    · have hj1 : j = 1 := by have := j.isLt; omega
      rw [hj1, diagConePt_apply_one, mul_div_cancel₀ (y (i, 1)) (hy i)]
  have hw : wtPow N (fun i => y (i, 0)) d ≠ 0 := wtPow_ne_zero fun i => hy i
  have hscale := eval_scale_homPiece d g hg (fun i => y (i, 0)) (diagConePt N y)
  rw [hpt, hev] at hscale
  exact (mul_eq_zero.mp hscale.symm).resolve_left hw

/-- A multihomogeneous polynomial of multidegree `d` vanishing at `y` lies in `diagIdeal y`. -/
lemma homPiece_eval_zero_mem_diagIdeal {d : Fin (N + 1) →₀ ℕ} {g : MR N}
    (hg : g ∈ homPiece N d) (y : Fin (N + 1) × Fin 2 → ℂ)
    (hy : ∀ i : Fin (N + 1), y (i, 0) ≠ 0) (hev : MvPolynomial.eval y g = 0) :
    g ∈ diagIdeal N y := by
  rw [diagIdeal_eq_ker N y hy, RingHom.mem_ker]
  have hz : MvPolynomial.eval (diagConePt N y) g = 0 := eval_diagConePt_eq_zero hg y hy hev
  refine MvPolynomial.funext fun a => ?_
  rw [eval_diagΦ_apply y a g, eval_scale_homPiece d g hg a (diagConePt N y), hz, mul_zero,
    map_zero]

theorem srelcut_prime_le_diagonal {N : ℕ} (r : Ideal (MR N)) (hr : r.IsPrime) (hrm : MultiHom N r)
    (y : Fin (N + 1) × Fin 2 → ℂ) (hy : ∀ i : Fin (N + 1), y (i, 0) ≠ 0) (hry : r ≤ ptIdeal N y) :
    r ≤ diagIdeal N y := by
  intro f hf
  have key : ∀ d : Fin (N + 1) →₀ ℕ,
      weightedHomogeneousComponent (mdeg N) d f ∈ diagIdeal N y := by
    intro d
    have hd : weightedHomogeneousComponent (mdeg N) d f ∈ homPiece N d :=
      weightedHomogeneousComponent_mem (mdeg N) f d
    have hmr : weightedHomogeneousComponent (mdeg N) d f ∈ r := hrm f hf d
    have hev : MvPolynomial.eval y (weightedHomogeneousComponent (mdeg N) d f) = 0 := by
      have h1 : weightedHomogeneousComponent (mdeg N) d f ∈ ptIdeal N y := hry hmr
      rwa [ptIdeal, RingHom.mem_ker] at h1
    exact homPiece_eval_zero_mem_diagIdeal hd y hy hev
  rw [← sum_weightedHomogeneousComponent (mdeg N) f, ← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_finsum (Ideal.Quotient.mk (diagIdeal N y))
    (weightedHomogeneousComponent_finsupp (w := mdeg N) f)]
  exact finsum_eq_zero_of_forall_eq_zero fun d =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (key d)

end

end Work.BW.RB
