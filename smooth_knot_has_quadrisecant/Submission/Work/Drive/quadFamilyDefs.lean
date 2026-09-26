import Mathlib
import Submission.Work.Drive.rankPatchDefs

/-!
# The trigonometric perturbation family

`Work.Drive.torusGeneralPositionTransverse_noInflection_dense` is proved by perturbing a given
smooth knot by a *finite-dimensional family of analytic periodic corrections*, and showing that
the set of "bad" parameter values (those for which the perturbed knot fails general position or
has an inflection) is Lebesgue-null.

This file sets up the family.  The parameter space is `QCoeff D`: the corrections are
trigonometric sums of degree at most `D`, one scalar sum per coordinate of `Space`.

* `ScIdx D` indexes the scalar trigonometric basis `1, cos t, sin t, …, cos (D t), sin (D t)`;
* `scFun D c` is the scalar trigonometric sum with coefficient vector `c : ScCoeff D`;
* `corr D c : ℝ → Space` is the vector-valued correction, `corrD`/`corrD2` its first and
  second derivatives;
* `curve r D c`, `velCurve r D c`, `accCurve r D c` are the position, velocity and acceleration
  of the perturbed curve `t ↦ r t + corr D c t`.

The family is *affine* in the parameter: `curve r D c` is `r` plus a linear function of `c`.  This
is what makes the chain rule for the parametrised badness maps manageable: along the direction
`c ↦ c + s • δ`, the curve data moves by `s` times the *data* of `δ`, so the derivative of any
function of the curve data in that direction is the derivative of the corresponding function of
the data applied to the data of `δ`.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- The index set of the scalar trigonometric basis of degree at most `D`:
`none` is the constant `1`, `some (k, false)` is `cos ((k+1) t)` and `some (k, true)` is
`sin ((k+1) t)`. -/
abbrev ScIdx (D : ℕ) : Type := Option (Fin D × Bool)

/-- The scalar coefficient space (`2 * D + 1` real parameters). -/
abbrev ScCoeff (D : ℕ) : Type := EuclideanSpace ℝ (ScIdx D)

/-- The vector-valued coefficient space: one scalar trigonometric sum per coordinate. -/
abbrev QCoeff (D : ℕ) : Type := EuclideanSpace ℝ (Fin (3 * (2 * D + 1)))

/-- The index equivalence identifying the coordinates of `QCoeff D` with pairs
`(coordinate of Space, basis index)`. -/
noncomputable def cIdxEquiv (D : ℕ) : Fin 3 × ScIdx D ≃ Fin (3 * (2 * D + 1)) :=
  Fintype.equivFinOfCardEq (by
    simp [ScIdx, Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Fintype.card_bool]
    ring)

/-- The frequency of the `k`-th basis pair. -/
def scFreq (D : ℕ) (k : Fin D) : ℝ := ((k : ℕ) : ℝ) + 1

/-- The scalar trigonometric basis function. -/
def scBase (D : ℕ) (j : ScIdx D) (t : ℝ) : ℝ :=
  match j with
  | none => 1
  | some (k, b) => if b then Real.sin (scFreq D k * t) else Real.cos (scFreq D k * t)

/-- The derivative in `t` of the scalar basis function. -/
def scBaseD (D : ℕ) (j : ScIdx D) (t : ℝ) : ℝ :=
  match j with
  | none => 0
  | some (k, b) => if b then scFreq D k * Real.cos (scFreq D k * t)
                   else -(scFreq D k) * Real.sin (scFreq D k * t)

/-- The second derivative in `t` of the scalar basis function. -/
def scBaseD2 (D : ℕ) (j : ScIdx D) (t : ℝ) : ℝ :=
  match j with
  | none => 0
  | some (k, b) => if b then -(scFreq D k) ^ 2 * Real.sin (scFreq D k * t)
                   else -(scFreq D k) ^ 2 * Real.cos (scFreq D k * t)

/-- The scalar trigonometric sum of degree at most `D` with coefficients `c`. -/
def scFun (D : ℕ) (c : ScCoeff D) (t : ℝ) : ℝ := ∑ j, c j * scBase D j t

/-- The derivative in `t` of `scFun`. -/
def scFunD (D : ℕ) (c : ScCoeff D) (t : ℝ) : ℝ := ∑ j, c j * scBaseD D j t

/-- The second derivative in `t` of `scFun`. -/
def scFunD2 (D : ℕ) (c : ScCoeff D) (t : ℝ) : ℝ := ∑ j, c j * scBaseD2 D j t

/-! ## The expanded forms of the scalar sums

The sums over `ScIdx D = Option (Fin D × Bool)` are unfolded into the more familiar
`a₀ + Σ_k (a_k cos (k t) + b_k sin (k t))` shape, in which the correspondence with complex
polynomials (see `Work.Drive.scPoly`) is transparent. -/

lemma scFun_expand (D : ℕ) (c : ScCoeff D) (t : ℝ) :
    scFun D c t = c none + ∑ k : Fin D,
      (c (some (k, false)) * Real.cos (scFreq D k * t) +
        c (some (k, true)) * Real.sin (scFreq D k * t)) := by
  have h1 : scFun D c t = c none * scBase D none t +
      ∑ k : Fin D, ∑ b : Bool, c (some (k, b)) * scBase D (some (k, b)) t := by
    rw [scFun, Fintype.sum_option (M := ℝ), Fintype.sum_prod_type (γ := ℝ)]
  rw [h1, show scBase D none t = (1 : ℝ) from rfl, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Fintype.sum_bool]
  show c (some (k, true)) * Real.sin (scFreq D k * t) +
      c (some (k, false)) * Real.cos (scFreq D k * t)
    = c (some (k, false)) * Real.cos (scFreq D k * t) +
      c (some (k, true)) * Real.sin (scFreq D k * t)
  ring

lemma scFunD_expand (D : ℕ) (c : ScCoeff D) (t : ℝ) :
    scFunD D c t = ∑ k : Fin D,
      (-(scFreq D k) * c (some (k, false)) * Real.sin (scFreq D k * t) +
        scFreq D k * c (some (k, true)) * Real.cos (scFreq D k * t)) := by
  have h1 : scFunD D c t = c none * scBaseD D none t +
      ∑ k : Fin D, ∑ b : Bool, c (some (k, b)) * scBaseD D (some (k, b)) t := by
    rw [scFunD, Fintype.sum_option (M := ℝ), Fintype.sum_prod_type (γ := ℝ)]
  rw [h1, show scBaseD D none t = (0 : ℝ) from rfl, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_bool]
  show c (some (k, true)) * (scFreq D k * Real.cos (scFreq D k * t)) +
      c (some (k, false)) * (-(scFreq D k) * Real.sin (scFreq D k * t))
    = -(scFreq D k) * c (some (k, false)) * Real.sin (scFreq D k * t) +
      scFreq D k * c (some (k, true)) * Real.cos (scFreq D k * t)
  ring

lemma scFunD2_expand (D : ℕ) (c : ScCoeff D) (t : ℝ) :
    scFunD2 D c t = ∑ k : Fin D,
      (-(scFreq D k) ^ 2 * c (some (k, false)) * Real.cos (scFreq D k * t) +
        -(scFreq D k) ^ 2 * c (some (k, true)) * Real.sin (scFreq D k * t)) := by
  have h1 : scFunD2 D c t = c none * scBaseD2 D none t +
      ∑ k : Fin D, ∑ b : Bool, c (some (k, b)) * scBaseD2 D (some (k, b)) t := by
    rw [scFunD2, Fintype.sum_option (M := ℝ), Fintype.sum_prod_type (γ := ℝ)]
  rw [h1, show scBaseD2 D none t = (0 : ℝ) from rfl, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_bool]
  show c (some (k, true)) * (-(scFreq D k) ^ 2 * Real.sin (scFreq D k * t)) +
      c (some (k, false)) * (-(scFreq D k) ^ 2 * Real.cos (scFreq D k * t))
    = -(scFreq D k) ^ 2 * c (some (k, false)) * Real.cos (scFreq D k * t) +
      -(scFreq D k) ^ 2 * c (some (k, true)) * Real.sin (scFreq D k * t)
  ring

/-! ## The derivative of the scalar sums -/

lemma hasDerivAt_scBase (D : ℕ) (j : ScIdx D) (t : ℝ) :
    HasDerivAt (fun s : ℝ => scBase D j s) (scBaseD D j t) t := by
  match j with
  | none => simpa [scBase, scBaseD] using hasDerivAt_const (x := t) (c := (1 : ℝ))
  | some (k, b) =>
    have h1 : HasDerivAt (fun s : ℝ => scFreq D k * s) (scFreq D k) t := by
      simpa using (hasDerivAt_id t).const_mul (scFreq D k)
    cases b
    · have h : HasDerivAt (fun s : ℝ => Real.cos (scFreq D k * s))
          (-Real.sin (scFreq D k * t) * scFreq D k) t :=
        (Real.hasDerivAt_cos (scFreq D k * t)).comp t h1
      have h2 : HasDerivAt (fun s : ℝ => Real.cos (scFreq D k * s))
          (-(scFreq D k * Real.sin (scFreq D k * t))) t := h.congr_deriv (by ring)
      simpa [scBase, scBaseD] using h2
    · have h : HasDerivAt (fun s : ℝ => Real.sin (scFreq D k * s))
          (Real.cos (scFreq D k * t) * scFreq D k) t :=
        (Real.hasDerivAt_sin (scFreq D k * t)).comp t h1
      have h2 : HasDerivAt (fun s : ℝ => Real.sin (scFreq D k * s))
          (scFreq D k * Real.cos (scFreq D k * t)) t := h.congr_deriv (by ring)
      simpa [scBase, scBaseD] using h2

lemma hasDerivAt_scBaseD (D : ℕ) (j : ScIdx D) (t : ℝ) :
    HasDerivAt (fun s : ℝ => scBaseD D j s) (scBaseD2 D j t) t := by
  match j with
  | none => simpa [scBaseD, scBaseD2] using hasDerivAt_const (x := t) (c := (0 : ℝ))
  | some (k, b) =>
    have h1 : HasDerivAt (fun s : ℝ => scFreq D k * s) (scFreq D k) t := by
      simpa using (hasDerivAt_id t).const_mul (scFreq D k)
    cases b
    · have h : HasDerivAt (fun s : ℝ => Real.sin (scFreq D k * s))
          (Real.cos (scFreq D k * t) * scFreq D k) t :=
        (Real.hasDerivAt_sin (scFreq D k * t)).comp t h1
      have h2 : HasDerivAt (fun s : ℝ => -(scFreq D k * Real.sin (scFreq D k * s)))
          (-(scFreq D k * (Real.cos (scFreq D k * t) * scFreq D k))) t :=
        (h.const_mul (scFreq D k)).neg
      have h3 : HasDerivAt (fun s : ℝ => -(scFreq D k * Real.sin (scFreq D k * s)))
          (-(scFreq D k ^ 2 * Real.cos (scFreq D k * t))) t := h2.congr_deriv (by ring)
      simpa [scBaseD, scBaseD2] using h3
    · have h : HasDerivAt (fun s : ℝ => Real.cos (scFreq D k * s))
          (-Real.sin (scFreq D k * t) * scFreq D k) t :=
        (Real.hasDerivAt_cos (scFreq D k * t)).comp t h1
      have h2 : HasDerivAt (fun s : ℝ => scFreq D k * Real.cos (scFreq D k * s))
          (scFreq D k * (-Real.sin (scFreq D k * t) * scFreq D k)) t :=
        h.const_mul (scFreq D k)
      have h3 : HasDerivAt (fun s : ℝ => scFreq D k * Real.cos (scFreq D k * s))
          (-(scFreq D k ^ 2 * Real.sin (scFreq D k * t))) t := h2.congr_deriv (by ring)
      simpa [scBaseD, scBaseD2] using h3

lemma hasDerivAt_scFun (D : ℕ) (c : ScCoeff D) (t : ℝ) :
    HasDerivAt (fun s : ℝ => scFun D c s) (scFunD D c t) t := by
  unfold scFun scFunD
  have h := HasDerivAt.sum (u := Finset.univ)
    (A := fun j : ScIdx D => fun s : ℝ => c j * scBase D j s)
    (A' := fun j : ScIdx D => c j * scBaseD D j t)
    (fun j _ => (hasDerivAt_scBase D j t).const_mul (c j))
  rw [show (∑ i, fun s : ℝ => c i * scBase D i s) = (fun s : ℝ => ∑ i, c i * scBase D i s)
    from by funext s; simp [Finset.sum_apply]] at h
  exact h

lemma hasDerivAt_scFunD (D : ℕ) (c : ScCoeff D) (t : ℝ) :
    HasDerivAt (fun s : ℝ => scFunD D c s) (scFunD2 D c t) t := by
  unfold scFunD scFunD2
  have h := HasDerivAt.sum (u := Finset.univ)
    (A := fun j : ScIdx D => fun s : ℝ => c j * scBaseD D j s)
    (A' := fun j : ScIdx D => c j * scBaseD2 D j t)
    (fun j _ => (hasDerivAt_scBaseD D j t).const_mul (c j))
  rw [show (∑ i, fun s : ℝ => c i * scBaseD D i s) = (fun s : ℝ => ∑ i, c i * scBaseD D i s)
    from by funext s; simp [Finset.sum_apply]] at h
  exact h

/-! ## Linearity of the scalar sums in the coefficients -/

lemma scFun_add (D : ℕ) (c c' : ScCoeff D) (t : ℝ) :
    scFun D (c + c') t = scFun D c t + scFun D c' t := by
  simp only [scFun]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [PiLp.add_apply, add_mul]

lemma scFun_smul (D : ℕ) (a : ℝ) (c : ScCoeff D) (t : ℝ) :
    scFun D (a • c) t = a * scFun D c t := by
  simp only [scFun]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [PiLp.smul_apply, smul_eq_mul]; ring

lemma scFunD_add (D : ℕ) (c c' : ScCoeff D) (t : ℝ) :
    scFunD D (c + c') t = scFunD D c t + scFunD D c' t := by
  simp only [scFunD]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [PiLp.add_apply, add_mul]

lemma scFunD_smul (D : ℕ) (a : ℝ) (c : ScCoeff D) (t : ℝ) :
    scFunD D (a • c) t = a * scFunD D c t := by
  simp only [scFunD]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [PiLp.smul_apply, smul_eq_mul]; ring

lemma scFunD2_add (D : ℕ) (c c' : ScCoeff D) (t : ℝ) :
    scFunD2 D (c + c') t = scFunD2 D c t + scFunD2 D c' t := by
  simp only [scFunD2]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [PiLp.add_apply, add_mul]

lemma scFunD2_smul (D : ℕ) (a : ℝ) (c : ScCoeff D) (t : ℝ) :
    scFunD2 D (a • c) t = a * scFunD2 D c t := by
  simp only [scFunD2]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [PiLp.smul_apply, smul_eq_mul]; ring

/-! ## The vector-valued correction -/

/-- The coordinate `(i, j)` of a coefficient vector. -/
def coefAt (D : ℕ) (c : QCoeff D) (i : Fin 3) (j : ScIdx D) : ℝ := c (cIdxEquiv D (i, j))

/-- The `i`-th scalar trigonometric sum of a coefficient vector. -/
def coefC (D : ℕ) (c : QCoeff D) (i : Fin 3) : ScCoeff D :=
  WithLp.toLp 2 (fun j : ScIdx D => coefAt D c i j)

lemma coefC_apply (D : ℕ) (c : QCoeff D) (i : Fin 3) (j : ScIdx D) :
    coefC D c i j = coefAt D c i j := rfl

/-- The vector-valued correction of the perturbation family. -/
def corr (D : ℕ) (c : QCoeff D) (t : ℝ) : Space :=
  WithLp.toLp 2 (fun i : Fin 3 => scFun D (coefC D c i) t)

/-- The velocity of the correction. -/
def corrD (D : ℕ) (c : QCoeff D) (t : ℝ) : Space :=
  WithLp.toLp 2 (fun i : Fin 3 => scFunD D (coefC D c i) t)

/-- The acceleration of the correction. -/
def corrD2 (D : ℕ) (c : QCoeff D) (t : ℝ) : Space :=
  WithLp.toLp 2 (fun i : Fin 3 => scFunD2 D (coefC D c i) t)

/-- The curve `t ↦ r t + corr c t`. -/
def curve (r : ℝ → Space) (D : ℕ) (c : QCoeff D) : ℝ → Space := fun t => r t + corr D c t

/-- The velocity of the perturbed curve. -/
def velCurve (r : ℝ → Space) (D : ℕ) (c : QCoeff D) : ℝ → Space :=
  fun t => velocity r t + corrD D c t

/-- The acceleration of the perturbed curve. -/
def accCurve (r : ℝ → Space) (D : ℕ) (c : QCoeff D) : ℝ → Space :=
  fun t => deriv (velocity r) t + corrD2 D c t

@[simp] lemma corr_apply (D : ℕ) (c : QCoeff D) (t : ℝ) (i : Fin 3) :
    corr D c t i = scFun D (coefC D c i) t := rfl

@[simp] lemma corrD_apply (D : ℕ) (c : QCoeff D) (t : ℝ) (i : Fin 3) :
    corrD D c t i = scFunD D (coefC D c i) t := rfl

@[simp] lemma corrD2_apply (D : ℕ) (c : QCoeff D) (t : ℝ) (i : Fin 3) :
    corrD2 D c t i = scFunD2 D (coefC D c i) t := rfl

lemma coefC_add (D : ℕ) (c c' : QCoeff D) (i : Fin 3) :
    coefC D (c + c') i = coefC D c i + coefC D c' i := by
  ext j
  simp [coefC, coefAt]

lemma coefC_smul (D : ℕ) (a : ℝ) (c : QCoeff D) (i : Fin 3) :
    coefC D (a • c) i = a • coefC D c i := by
  ext j
  simp [coefC, coefAt]

lemma corr_add (D : ℕ) (c c' : QCoeff D) (t : ℝ) :
    corr D (c + c') t = corr D c t + corr D c' t := by
  ext i
  simp only [corr_apply, PiLp.add_apply, coefC_add, scFun_add]

lemma corr_smul (D : ℕ) (a : ℝ) (c : QCoeff D) (t : ℝ) :
    corr D (a • c) t = a • corr D c t := by
  ext i
  simp only [corr_apply, PiLp.smul_apply, coefC_smul, scFun_smul]
  rfl

lemma corrD_add (D : ℕ) (c c' : QCoeff D) (t : ℝ) :
    corrD D (c + c') t = corrD D c t + corrD D c' t := by
  ext i
  simp only [corrD_apply, PiLp.add_apply, coefC_add, scFunD_add]

lemma corrD_smul (D : ℕ) (a : ℝ) (c : QCoeff D) (t : ℝ) :
    corrD D (a • c) t = a • corrD D c t := by
  ext i
  simp only [corrD_apply, PiLp.smul_apply, coefC_smul, scFunD_smul]
  rfl

lemma corrD2_add (D : ℕ) (c c' : QCoeff D) (t : ℝ) :
    corrD2 D (c + c') t = corrD2 D c t + corrD2 D c' t := by
  ext i
  simp only [corrD2_apply, PiLp.add_apply, coefC_add, scFunD2_add]

lemma corrD2_smul (D : ℕ) (a : ℝ) (c : QCoeff D) (t : ℝ) :
    corrD2 D (a • c) t = a • corrD2 D c t := by
  ext i
  simp only [corrD2_apply, PiLp.smul_apply, coefC_smul, scFunD2_smul]
  rfl

lemma corr_sub (D : ℕ) (c c' : QCoeff D) (t : ℝ) :
    corr D (c - c') t = corr D c t - corr D c' t := by
  rw [sub_eq_add_neg, corr_add,
    show (-c' : QCoeff D) = (-1 : ℝ) • c' from by simp, corr_smul, neg_one_smul,
    sub_eq_add_neg]

/-! ## Derivatives in `t` of the vector-valued correction -/

lemma hasDerivAt_corr (D : ℕ) (c : QCoeff D) (t : ℝ) :
    HasDerivAt (fun s : ℝ => corr D c s) (corrD D c t) t := by
  have h : HasDerivAt (fun s : ℝ => (corr D c s).ofLp) ((corrD D c t).ofLp) t := by
    rw [hasDerivAt_pi]
    intro i
    exact hasDerivAt_scFun D (coefC D c i) t
  have h2 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt
    (x := t) h
  simpa [Function.comp_def, WithLp.toLp_ofLp] using h2

lemma hasDerivAt_corrD (D : ℕ) (c : QCoeff D) (t : ℝ) :
    HasDerivAt (fun s : ℝ => corrD D c s) (corrD2 D c t) t := by
  have h : HasDerivAt (fun s : ℝ => (corrD D c s).ofLp) ((corrD2 D c t).ofLp) t := by
    rw [hasDerivAt_pi]
    intro i
    exact hasDerivAt_scFunD D (coefC D c i) t
  have h2 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt
    (x := t) h
  simpa [Function.comp_def, WithLp.toLp_ofLp] using h2

lemma deriv_corr (D : ℕ) (c : QCoeff D) (t : ℝ) :
    deriv (fun s : ℝ => corr D c s) t = corrD D c t :=
  (hasDerivAt_corr D c t).deriv

lemma deriv_corrD (D : ℕ) (c : QCoeff D) (t : ℝ) :
    deriv (fun s : ℝ => corrD D c s) t = corrD2 D c t :=
  (hasDerivAt_corrD D c t).deriv

/-! ## Analyticity -/

lemma contDiff_scBase (D : ℕ) (j : ScIdx D) : ContDiff ℝ ⊤ (scBase D j) := by
  cases j with
  | none => show ContDiff ℝ ⊤ (fun _ : ℝ => (1 : ℝ)); exact contDiff_const
  | some kb =>
    obtain ⟨k, b⟩ := kb
    cases b
    · show ContDiff ℝ ⊤ (fun t : ℝ => Real.cos (scFreq D k * t)); fun_prop
    · show ContDiff ℝ ⊤ (fun t : ℝ => Real.sin (scFreq D k * t)); fun_prop

lemma contDiff_scBaseD (D : ℕ) (j : ScIdx D) : ContDiff ℝ ⊤ (scBaseD D j) := by
  cases j with
  | none => show ContDiff ℝ ⊤ (fun _ : ℝ => (0 : ℝ)); exact contDiff_const
  | some kb =>
    obtain ⟨k, b⟩ := kb
    cases b
    · show ContDiff ℝ ⊤ (fun t : ℝ => -(scFreq D k) * Real.sin (scFreq D k * t)); fun_prop
    · show ContDiff ℝ ⊤ (fun t : ℝ => scFreq D k * Real.cos (scFreq D k * t)); fun_prop

lemma contDiff_scBaseD2 (D : ℕ) (j : ScIdx D) : ContDiff ℝ ⊤ (scBaseD2 D j) := by
  cases j with
  | none => show ContDiff ℝ ⊤ (fun _ : ℝ => (0 : ℝ)); exact contDiff_const
  | some kb =>
    obtain ⟨k, b⟩ := kb
    cases b
    · show ContDiff ℝ ⊤ (fun t : ℝ => -(scFreq D k) ^ 2 * Real.cos (scFreq D k * t)); fun_prop
    · show ContDiff ℝ ⊤ (fun t : ℝ => -(scFreq D k) ^ 2 * Real.sin (scFreq D k * t)); fun_prop

lemma contDiff_scFun (D : ℕ) (c : ScCoeff D) : ContDiff ℝ ⊤ (scFun D c) := by
  unfold scFun
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_scBase D j)

lemma contDiff_scFunD (D : ℕ) (c : ScCoeff D) : ContDiff ℝ ⊤ (scFunD D c) := by
  unfold scFunD
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_scBaseD D j)

lemma contDiff_scFunD2 (D : ℕ) (c : ScCoeff D) : ContDiff ℝ ⊤ (scFunD2 D c) := by
  unfold scFunD2
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_scBaseD2 D j)

lemma contDiff_ofLp_corr (D : ℕ) (c : QCoeff D) :
    ContDiff ℝ ⊤ (fun t : ℝ => (corr D c t).ofLp) := by
  rw [contDiff_pi]
  intro i
  exact contDiff_scFun D (coefC D c i)

lemma contDiff_ofLp_corrD (D : ℕ) (c : QCoeff D) :
    ContDiff ℝ ⊤ (fun t : ℝ => (corrD D c t).ofLp) := by
  rw [contDiff_pi]
  intro i
  exact contDiff_scFunD D (coefC D c i)

lemma contDiff_ofLp_corrD2 (D : ℕ) (c : QCoeff D) :
    ContDiff ℝ ⊤ (fun t : ℝ => (corrD2 D c t).ofLp) := by
  rw [contDiff_pi]
  intro i
  exact contDiff_scFunD2 D (coefC D c i)

lemma contDiff_corr (D : ℕ) (c : QCoeff D) : ContDiff ℝ ⊤ (corr D c) := by
  have h2 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp
    (contDiff_ofLp_corr D c)
  simpa [Function.comp_def, WithLp.toLp_ofLp] using h2

lemma contDiff_corrD (D : ℕ) (c : QCoeff D) : ContDiff ℝ ⊤ (corrD D c) := by
  have h2 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp
    (contDiff_ofLp_corrD D c)
  simpa [Function.comp_def, WithLp.toLp_ofLp] using h2

lemma contDiff_corrD2 (D : ℕ) (c : QCoeff D) : ContDiff ℝ ⊤ (corrD2 D c) := by
  have h2 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp
    (contDiff_ofLp_corrD2 D c)
  simpa [Function.comp_def, WithLp.toLp_ofLp] using h2

lemma contDiff_curve {r : ℝ → Space} (hr : IsSmoothKnot r) (D : ℕ) (c : QCoeff D) :
    ContDiff ℝ ⊤ (curve r D c) :=
  hr.smooth.add (contDiff_corr D c)

/-! ## Velocity and acceleration of the perturbed curve -/

lemma velocity_curve {r : ℝ → Space} (hr : IsSmoothKnot r) (D : ℕ) (c : QCoeff D) :
    velocity (curve r D c) = velCurve r D c := by
  funext t
  have h1 : DifferentiableAt ℝ r t := (hr.smooth.differentiable (by decide)).differentiableAt
  have h2 : DifferentiableAt ℝ (fun s : ℝ => corr D c s) t :=
    (contDiff_corr D c).differentiable (by decide) |>.differentiableAt
  have hcv : curve r D c = fun s : ℝ => r s + corr D c s := rfl
  have hsum : HasDerivAt (fun s : ℝ => r s + corr D c s) (deriv r t + corrD D c t) t := by
    have h := h1.hasDerivAt.add h2.hasDerivAt
    rw [deriv_corr] at h
    exact h
  show deriv (curve r D c) t = velocity r t + corrD D c t
  rw [hcv, hsum.deriv]
  rfl

lemma differentiable_deriv {r : ℝ → Space} (hr : IsSmoothKnot r) :
    Differentiable ℝ (deriv r) := by
  simpa [iteratedDeriv_one] using
    hr.smooth.differentiable_iteratedDeriv 1
      (by exact WithTop.coe_lt_top 1)

lemma accCurve_eq {r : ℝ → Space} (hr : IsSmoothKnot r) (D : ℕ) (c : QCoeff D) :
    (fun t => deriv (velocity (curve r D c)) t) = accCurve r D c := by
  funext t
  have h1 : DifferentiableAt ℝ (velocity r) t :=
    (differentiable_deriv hr).differentiableAt
  have h2 : DifferentiableAt ℝ (fun s : ℝ => corrD D c s) t :=
    (contDiff_corrD D c).differentiable (by decide) |>.differentiableAt
  have hv : velocity (curve r D c) = fun s : ℝ => velocity r s + corrD D c s := by
    rw [velocity_curve hr]; rfl
  have hsum : HasDerivAt (fun s : ℝ => velocity r s + corrD D c s)
      (deriv (velocity r) t + corrD2 D c t) t := by
    have h := h1.hasDerivAt.add h2.hasDerivAt
    rw [deriv_corrD] at h
    exact h
  show deriv (velocity (curve r D c)) t = deriv (velocity r) t + corrD2 D c t
  rw [hv, hsum.deriv]

/-! ## Periodicity -/

lemma periodic_scBase (D : ℕ) (j : ScIdx D) : Function.Periodic (scBase D j) period := by
  intro t
  cases j with
  | none => simp [scBase]
  | some kb =>
    obtain ⟨k, b⟩ := kb
    have harg : scFreq D k * (t + period) =
        scFreq D k * t + (((k : ℕ) + 1 : ℕ) : ℤ) * (2 * Real.pi) := by
      simp only [scFreq, period]
      push_cast
      ring
    cases b
    · show Real.cos (scFreq D k * (t + period)) = Real.cos (scFreq D k * t)
      rw [harg, Real.cos_add_int_mul_two_pi]
    · show Real.sin (scFreq D k * (t + period)) = Real.sin (scFreq D k * t)
      rw [harg, Real.sin_add_int_mul_two_pi]

lemma periodic_scFun (D : ℕ) (c : ScCoeff D) : Function.Periodic (scFun D c) period := by
  intro t
  unfold scFun
  exact Finset.sum_congr rfl fun j _ => by rw [periodic_scBase D j t]

lemma periodic_ofLp_corr (D : ℕ) (c : QCoeff D) :
    Function.Periodic (fun t : ℝ => (corr D c t).ofLp) period := by
  intro t
  funext i
  exact periodic_scFun D (coefC D c i) t

lemma periodic_corr (D : ℕ) (c : QCoeff D) : Function.Periodic (corr D c) period := by
  intro t
  have h := periodic_ofLp_corr D c t
  have h2 := congrArg (WithLp.toLp 2) h
  simpa [WithLp.toLp_ofLp] using h2

/-! ## Size bounds (used for the `C¹`-closeness of the perturbation) -/

lemma abs_scBase_le_one (D : ℕ) (j : ScIdx D) (t : ℝ) : |scBase D j t| ≤ 1 := by
  cases j with
  | none => simp [scBase]
  | some kb =>
    obtain ⟨k, b⟩ := kb
    cases b <;> simp [scBase, Real.abs_sin_le_one, Real.abs_cos_le_one]

lemma abs_scBaseD_le (D : ℕ) (j : ScIdx D) (t : ℝ) : |scBaseD D j t| ≤ (D : ℝ) + 1 := by
  cases j with
  | none => simp [scBaseD]; positivity
  | some kb =>
    obtain ⟨k, b⟩ := kb
    have hk : scFreq D k ≤ (D : ℝ) + 1 := by
      have hle : ((k : ℕ) + 1 : ℕ) ≤ D := Nat.succ_le_of_lt k.isLt
      have h1 : (((k : ℕ) + 1 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast hle
      simp only [scFreq]
      push_cast at h1 ⊢
      linarith
    have hk0 : 0 ≤ scFreq D k := by simp only [scFreq]; positivity
    have hsin := Real.abs_sin_le_one (scFreq D k * t)
    have hcos := Real.abs_cos_le_one (scFreq D k * t)
    cases b
    · show |(-(scFreq D k)) * Real.sin (scFreq D k * t)| ≤ (D : ℝ) + 1
      rw [abs_mul, abs_neg, abs_of_nonneg hk0]
      calc scFreq D k * |Real.sin (scFreq D k * t)| ≤ scFreq D k * 1 :=
            mul_le_mul_of_nonneg_left hsin hk0
        _ = scFreq D k := mul_one _
        _ ≤ (D : ℝ) + 1 := hk
    · show |scFreq D k * Real.cos (scFreq D k * t)| ≤ (D : ℝ) + 1
      rw [abs_mul, abs_of_nonneg hk0]
      calc scFreq D k * |Real.cos (scFreq D k * t)| ≤ scFreq D k * 1 :=
            mul_le_mul_of_nonneg_left hcos hk0
        _ = scFreq D k := mul_one _
        _ ≤ (D : ℝ) + 1 := hk

end

end Work.Drive
