import Mathlib
import Submission.Work.CR.Flat.Polydisc

/-!
# `∂̄`-closedness is preserved by iterated directional derivatives

The `j`-th flat `∂̄`-operator `dbarCoord j` is a linear combination
`(1/2)(∂_{x_j} + i ∂_{y_j})` of two directional derivatives with *constant*
coefficients.  Hence it commutes with every iterated derivative: for a `C^{i+1}`
function `g` and a tuple of directions `v`,

`∂̄_k (fun y => D^i g(y)(v)) = (D^i (∂̄_k g))(·)(v)`,

which is proved below as `dbarCoord_iteratedFDeriv`.  Applying this with the
`∂̄`-closedness relation `∂̄_k f_j = ∂̄_j f_k` of `f` gives the main theorem.
-/

namespace Work.CR.Flat.Cauchy

open scoped ContDiff

/-! ### Two elementary calculus lemmas -/

/-- `fderiv` commutes with the (continuous linear) evaluation of a continuous
linear map at a fixed vector. -/
lemma fderiv_fderiv_apply_eq {n : ℕ} {φ : (Fin n → ℂ) → ℂ} {z a w : Fin n → ℂ}
    (h : DifferentiableAt ℝ (fderiv ℝ φ) z) :
    fderiv ℝ (fun y => fderiv ℝ φ y a) z w = fderiv ℝ (fderiv ℝ φ) z w a := by
  rw [show (fun y => fderiv ℝ φ y a)
      = (ContinuousLinearMap.apply ℝ ℂ a) ∘ (fderiv ℝ φ) from rfl]
  rw [fderiv_comp]
  · simp [ContinuousLinearMap.fderiv]
  · exact (ContinuousLinearMap.apply ℝ ℂ a).differentiableAt
  · exact h

/-- Clairaut (symmetry of the second derivative) in the applied form used below. -/
lemma fderiv_apply_comm_of_isSymm {n : ℕ} {φ : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hsymm : IsSymmSndFDerivAt ℝ φ z) (hd : DifferentiableAt ℝ (fderiv ℝ φ) z)
    (a w : Fin n → ℂ) :
    fderiv ℝ (fun y => fderiv ℝ φ y a) z w = fderiv ℝ (fun y => fderiv ℝ φ y w) z a := by
  rw [fderiv_fderiv_apply_eq (a := a) hd, fderiv_fderiv_apply_eq (a := w) hd]
  exact hsymm.eq w a

/-- `DifferentiableAt.iteratedFDeriv_succ_apply_left'` in the pointwise form:
the `(i+1)`-st iterated derivative peels off the last argument. -/
lemma iteratedFDeriv_succ_apply_eq_fderiv {n i : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ (i+1) g) (v : Fin (i+1) → (Fin n → ℂ)) (z : Fin n → ℂ) :
    iteratedFDeriv ℝ (i+1) g z v
      = fderiv ℝ (fun t => iteratedFDeriv ℝ i g t (Fin.tail v)) z (v 0) := by
  rw [← Fin.cons_self_tail v]
  exact DifferentiableAt.iteratedFDeriv_succ_apply_left'
    ((hg.differentiable_iteratedFDeriv
      (by exact_mod_cast (show i < i + 1 by omega))).differentiableAt)

/-! ### The commutation of `fderiv` with the iterated derivative -/

/-- **`fderiv` commutes with the iterated derivative.**  For a `C^{i+1}` function `g` the
directional derivative in direction `w` of the function `y ↦ D^i g(y)(v)` equals the
`i`-th iterated derivative of the directional derivative `y ↦ dg(y)(w)`, evaluated on `v`.

This is the statement that iterated derivatives are symmetric (`∂_w D^i = D^i ∂_w`
with `w` moved into any slot), proved by induction on `i`; the induction step uses
the recursion `D^{i+1} g(y)(v) = d(D^i g(·))_y(v 0)` together with the symmetry of the
second derivative (Clairaut). -/
lemma fderiv_iteratedFDeriv_comm (i : ℕ) {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ (i+1) g) (v : Fin i → (Fin n → ℂ)) (w z : Fin n → ℂ) :
    fderiv ℝ (fun y => iteratedFDeriv ℝ i g y v) z w
      = iteratedFDeriv ℝ i (fun y => fderiv ℝ g y w) z v := by
  induction i generalizing g w z with
  | zero => simp [iteratedFDeriv_zero_apply]
  | succ i ih =>
    have hg1 : ContDiff ℝ (i+1) g :=
      hg.of_le (by exact_mod_cast (show i+1 ≤ i+1+1 by omega))
    have hDw : ContDiff ℝ (i+1) (fun y => fderiv ℝ g y w) := by
      have h1 : ContDiff ℝ (i+1) (fderiv ℝ g) :=
        hg.fderiv_right (m := (i+1 : ℕ)) (by exact_mod_cast (show i+1+1 ≤ i+1+1 by omega))
      exact h1.clm_apply contDiff_const
    have h2 : ContDiff ℝ 2 (fun t => iteratedFDeriv ℝ i g t (Fin.tail v)) := by
      have h3 : ContDiff ℝ 2 (iteratedFDeriv ℝ i g) :=
        hg.iteratedFDeriv_right (m := (2:ℕ)) (i := i) (by
          exact_mod_cast (show 2 + i ≤ i+1+1 by omega))
      exact ContDiff.continuousLinearMap_comp
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => (Fin n → ℂ)) ℂ (Fin.tail v)) h3
    have hsymm : IsSymmSndFDerivAt ℝ (fun t => iteratedFDeriv ℝ i g t (Fin.tail v)) z :=
      (h2.contDiffAt).isSymmSndFDerivAt (by simp)
    have hdφ : DifferentiableAt ℝ
        (fderiv ℝ (fun t => iteratedFDeriv ℝ i g t (Fin.tail v))) z :=
      (h2.contDiffAt.fderiv_right (m := (1 : WithTop ℕ∞)) (by
        exact_mod_cast (show 1+1 ≤ 2 by omega))).differentiableAt (by simp)
    have hL : (fun y => iteratedFDeriv ℝ (i+1) g y v)
        = fun y => fderiv ℝ (fun t => iteratedFDeriv ℝ i g t (Fin.tail v)) y (v 0) :=
      funext (fun y => iteratedFDeriv_succ_apply_eq_fderiv hg1 v y)
    rw [hL, fderiv_apply_comm_of_isSymm hsymm hdφ (v 0) w]
    have hI : (fun y => fderiv ℝ (fun t => iteratedFDeriv ℝ i g t (Fin.tail v)) y w)
        = fun y => iteratedFDeriv ℝ i (fun y => fderiv ℝ g y w) y (Fin.tail v) :=
      funext (fun y => ih hg1 (Fin.tail v) w y)
    rw [hI, ← iteratedFDeriv_succ_apply_eq_fderiv hDw v]

/-! ### Linearity of the iterated derivative in the function -/

/-- Pointwise multiplication by a constant preserves `C^i`. -/
lemma contDiff_mul_const {n i : ℕ} {P : (Fin n → ℂ) → ℂ} (hP : ContDiff ℝ i P) (c : ℂ) :
    ContDiff ℝ i (fun y => c * P y) := by
  simpa only [smul_eq_mul] using hP.const_smul c

/-- `iteratedFDeriv` is complex linear in the function it is applied to (scalars). -/
lemma iteratedFDeriv_mul_const_apply {n i : ℕ} {P : (Fin n → ℂ) → ℂ} {c : ℂ}
    (hP : ContDiff ℝ i P) (z : Fin n → ℂ) (v : Fin i → (Fin n → ℂ)) :
    iteratedFDeriv ℝ i (fun y => c * P y) z v = c * (iteratedFDeriv ℝ i P z v) := by
  rw [show (fun y => c * P y) = (fun y => c • P y) from
    funext (fun y => (smul_eq_mul c (P y)).symm)]
  rw [iteratedFDeriv_const_smul_apply' (f := P) (a := c) hP.contDiffAt]
  simp [smul_eq_mul]

/-- `iteratedFDeriv` is complex linear in the function it is applied to (sums). -/
lemma iteratedFDeriv_add_apply' {n i : ℕ} {P Q : (Fin n → ℂ) → ℂ}
    (hP : ContDiff ℝ i P) (hQ : ContDiff ℝ i Q)
    (z : Fin n → ℂ) (v : Fin i → (Fin n → ℂ)) :
    iteratedFDeriv ℝ i (fun y => P y + Q y) z v
      = iteratedFDeriv ℝ i P z v + iteratedFDeriv ℝ i Q z v := by
  rw [show (fun y => P y + Q y) = P + Q from rfl]
  rw [iteratedFDeriv_add_apply hP.contDiffAt hQ.contDiffAt]
  simp

/-- Linearity of `iteratedFDeriv` in the combination `c * (A + i * B)` that appears in
`dbarCoord`. -/
lemma iteratedFDeriv_combo_apply {n i : ℕ} {A B : (Fin n → ℂ) → ℂ} {c : ℂ}
    (hA : ContDiff ℝ i A) (hB : ContDiff ℝ i B) (z : Fin n → ℂ)
    (v : Fin i → (Fin n → ℂ)) :
    iteratedFDeriv ℝ i (fun y => c * (A y + Complex.I * B y)) z v
      = c * (iteratedFDeriv ℝ i A z v + Complex.I * (iteratedFDeriv ℝ i B z v)) := by
  rw [show (fun y => c * (A y + Complex.I * B y))
        = (fun y => c * A y + (c * Complex.I) * B y) from funext (fun y => by ring)]
  rw [iteratedFDeriv_add_apply' (P := fun y => c * A y) (Q := fun y => (c * Complex.I) * B y)
        (contDiff_mul_const hA c) (contDiff_mul_const hB (c * Complex.I)) z v,
      iteratedFDeriv_mul_const_apply hA z v, iteratedFDeriv_mul_const_apply hB z v]
  ring

/-- **`∂̄`-operators commute with iterated directional derivatives.**  If `g` is of class
`C^{i+1}` then for every tuple of directions `v`

`∂̄_k (fun y => D^i g(y)(v)) = (D^i (∂̄_k g))(·)(v)`.

Both sides are the `(i+1)`-fold derivative of `g` at the point with the two constant
vectors of `∂̄_k` inserted; the identity is the commutation of `∂̄_k` (constant
coefficients) with `D^i`. -/
lemma dbarCoord_iteratedFDeriv {n i : ℕ} {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ (i+1) g)
    (k : Fin n) (v : Fin i → (Fin n → ℂ)) (z : Fin n → ℂ) :
    dbarCoord k (fun y => iteratedFDeriv ℝ i g y v) z
      = iteratedFDeriv ℝ i (dbarCoord k g) z v := by
  have hA : ContDiff ℝ i (fun y => fderiv ℝ g y (Pi.single k (1:ℂ))) := by
    have h1 : ContDiff ℝ i (fderiv ℝ g) :=
      hg.fderiv_right (m := i) (by exact_mod_cast (show i+1 ≤ i+1 by omega))
    exact h1.clm_apply contDiff_const
  have hB : ContDiff ℝ i (fun y => fderiv ℝ g y (Pi.single k Complex.I)) := by
    have h1 : ContDiff ℝ i (fderiv ℝ g) :=
      hg.fderiv_right (m := i) (by exact_mod_cast (show i+1 ≤ i+1 by omega))
    exact h1.clm_apply contDiff_const
  simp only [dbarCoord]
  rw [fderiv_iteratedFDeriv_comm i hg v (Pi.single k (1:ℂ)) z,
      fderiv_iteratedFDeriv_comm i hg v (Pi.single k Complex.I) z]
  rw [show dbarCoord k g = (fun y => (1/2 : ℂ) * (fderiv ℝ g y (Pi.single k (1:ℂ)) +
      Complex.I * fderiv ℝ g y (Pi.single k Complex.I))) from rfl]
  rw [iteratedFDeriv_combo_apply hA hB z v]

/-! ### The theorem -/

/-- **`∂̄`-closedness is preserved by iterated directional derivatives.**  If `f` is a
`∂̄`-closed form of class `C^{i+1}`, then for every tuple of directions `v : Fin i → (Fin n → ℂ)`
the form `fun j y => iteratedFDeriv ℝ i (f j) y v` is `∂̄`-closed: the operator `∂̄_k` has
constant coefficients, so it commutes with the iterated derivative, and the pointwise
closedness of `f` then gives the claim. -/
theorem isClosedForm_iteratedFDeriv {n : ℕ} {i : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ (i + 1) (f j)) (hclosed : IsClosedForm f)
    (v : Fin i → (Fin n → ℂ)) :
    IsClosedForm (fun j y => iteratedFDeriv ℝ i (f j) y v) := by
  intro j k z
  have hjk : dbarCoord k (f j) = dbarCoord j (f k) := funext (hclosed j k)
  rw [dbarCoord_iteratedFDeriv (hf j) k v z, hjk, dbarCoord_iteratedFDeriv (hf k) j v z]

end Work.CR.Flat.Cauchy
