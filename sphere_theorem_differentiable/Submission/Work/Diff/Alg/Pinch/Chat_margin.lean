import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Strict
import Submission.Work.Diff.Alg.Pinch.Chat
import Submission.Work.Diff.Alg.Pinch.ChatDefs
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.ell_isAlgCurv
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic
import Submission.Work.Diff.Alg.Pinch.Ccone_transversal_a_aux
import Submission.Work.Diff.Alg.Pinch.Chat_lagrange
import Submission.Work.Diff.Alg.Pinch.Phi_wedge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pinching family `Ĉ(s)` contains a neighbourhood of the round sphere

This file proves `Work.Diff.Alg.Pinch.Chat_margin`: for every `s > 0` the Brendle–Schoen
pinching cone `Ĉ(s) = Chat n s` contains a *whole neighbourhood of the round sphere* inside the
space of algebraic curvature tensors.  Equivalently: `Iso n` is an interior point of `Ĉ(s)` in the
subspace `{R | IsAlgCurv R}`.

The cone is `Chat n s = ℓ_{a,b}(Dpic p)` for the parameters `(a,b,p)` of the Brendle–Schoen family
(`Chat`, `ChatDefs`), with `Dpic p = {R algebraic | InPIC2 R ∧ Ric ≥ p·scal/n}`.  The Böhm–Wilking
transform `ℓ = ell a b` is a linear isomorphism of `Curv4 n` (`ell_linv`, `linv_ell`), so it
suffices to show that the inverse image `linv a b R` of a tensor `R` close to `Iso n` lies in
`Dpic p`.

Writing (for `R` algebraic, so `linv a b (Iso n) = c • Iso n` with `c = 1/(1+2(n-1)a) > 0`)

`linv a b R = c • Iso n + E`,  `E = linv a b (R - Iso n)`,

the three conditions in `Dpic p` become quantitative and elementary:

* `E` is again an algebraic curvature tensor, and `‖E‖ ≤ M ‖R - Iso n‖`;
* **complex sectional curvature**: for `D` algebraic the quartic form `Cone.EF D` (whose
  nonnegativity is `InPIC2 D`) is dominated by `‖D‖ • Cone.EF (Iso n)`,
  `|EF D| ≤ C ‖D‖ EF (Iso n)` (`cm_EF_bound`); hence
  `EF (c • Iso n + E) = c · EF (Iso n) + EF E ≥ (c - C ‖E‖) EF (Iso n) ≥ 0` for `‖E‖` small,
  since `EF (Iso n) ≥ 0`;
* **Ricci pinching**: `⟨Ric (c • Iso n + E) v, v⟩ ≥ (1-p) c (n-1) ‖v‖² - O(‖E‖) ‖v‖²` dominates
  `(p/n) scalAlg (c • Iso n + E) ‖v‖² = p c (n-1) ‖v‖² + O(‖E‖) ‖v‖²` as soon as
  `(1-p) c (n-1) ≥ (|p| n + n²) ‖E‖` (using `p < 1`).

The key estimate `cm_EF_bound` is proved from `Phi_wedge` (`Phi` of a wedge `ζ ∧ η` against its
conjugate equals `4 · EF` of the underlying real four-tuple) together with `Chat_lagrange`
(`∑ (qfA² + qfB²) = 2 EF (Iso n)`), i.e. from the *Hermitian* structure of `EF` on the space of
algebraic curvature tensors.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Components and the operator norm on `Curv4 n` -/

/-- A single component of a `4`-index array is bounded by its sup norm. -/
lemma cm_abs_component_le_norm (X : Curv4 n) (i j k l : Fin n) : |X i j k l| ≤ ‖X‖ := by
  have h : ‖X i j k l‖ ≤ ‖X‖ :=
    (norm_le_pi_norm (X i j k) l).trans ((norm_le_pi_norm (X i j) k).trans
      ((norm_le_pi_norm (X i) j).trans (norm_le_pi_norm X i)))
  simpa [Real.norm_eq_abs] using h

/-- `linv a b` is a bounded (indeed continuous) linear map on the finite dimensional space
`Curv4 n`. -/
lemma cm_linv_bound (a b : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ D : Curv4 n, ‖linv a b D‖ ≤ M * ‖D‖ := by
  let f : Curv4 n →ₗ[ℝ] Curv4 n :=
    { toFun := linv a b, map_add' := linv_add a b, map_smul' := linv_smul a b }
  let g : Curv4 n →L[ℝ] Curv4 n := f.toContinuousLinearMap
  refine ⟨max ‖g‖ 1, lt_max_iff.mpr (Or.inr one_pos), fun D => ?_⟩
  calc ‖linv a b D‖ = ‖g D‖ := rfl
    _ ≤ ‖g‖ * ‖D‖ := ContinuousLinearMap.le_opNorm g D
    _ ≤ max ‖g‖ 1 * ‖D‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg D)

/-- `linv a b` maps algebraic curvature tensors to algebraic curvature tensors. -/
lemma cm_linv_isAlgCurv {a b : ℝ} {Y : Curv4 n} (hY : IsAlgCurv Y) :
    IsAlgCurv (linv a b Y) := by
  have h1 : IsAlgCurv (knProd (ric0 Y) (id2 n)) :=
    knProd_isAlgCurv (fun i j => ric0_symm hY i j) (fun i j => id2_symm i j)
  have h2 : IsAlgCurv (knProd (id2 n) (id2 n)) :=
    knProd_isAlgCurv (fun i j => id2_symm i j) (fun i j => id2_symm i j)
  rw [linv]
  exact isAlgCurv_sub (isAlgCurv_sub hY (isAlgCurv_smul _ h1)) (isAlgCurv_smul _ h2)

/-! ## `linv a b (Iso n)` is a positive multiple of `Iso n` -/

lemma cm_linv_iso {a b : ℝ} (hn : 1 ≤ n) (ha : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0) :
    linv a b (Iso n) = (1 / (1 + 2 * ((n : ℝ) - 1) * a)) • Iso n := by
  have hn' : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  have hC : (a / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * a) * ((n : ℝ) * ((n : ℝ) - 1)) * 2
      = 2 * ((n : ℝ) - 1) * a / (1 + 2 * ((n : ℝ) - 1) * a) := by
    field_simp
  have key : 1 - 2 * ((n : ℝ) - 1) * a / (1 + 2 * ((n : ℝ) - 1) * a)
      = 1 / (1 + 2 * ((n : ℝ) - 1) * a) := by
    field_simp
    ring
  have h1 : Iso n = (1 : ℝ) • Iso n := (one_smul ℝ (Iso n)).symm
  rw [linv, ric0_iso, knProd_zero_left, smul_zero, sub_zero, knProd_id2_id2, scalAlg_iso,
    smul_smul, hC]
  nth_rewrite 1 [h1]
  rw [← sub_smul, key]

/-! ## The complex vector `x + i y` and the Hermitian form of an algebraic curvature tensor -/

/-- The complex vector `ζ = x + i y`. -/
noncomputable def cmZ (x y : Fin n → ℝ) : Fin n → ℂ := fun i => (x i : ℂ) + (y i : ℂ) * Complex.I

lemma cm_cRe_cmZ (x y : Fin n → ℝ) : Q2P.cRe (cmZ x y) = x := by
  funext i
  simp [Q2P.cRe, cmZ]

lemma cm_cIm_cmZ (x y : Fin n → ℝ) : Q2P.cIm (cmZ x y) = y := by
  funext i
  simp [Q2P.cIm, cmZ]

/-- `Phi_wedge` in real coordinates: for an algebraic curvature tensor `D`, the `ℂ`-bilinear form
`Phi D (ζ ∧ η) (conj (ζ ∧ η))` of the decomposable form `ζ ∧ η` (`ζ = x + iy`, `η = z + iw`)
equals `4 · EF D x y z w`; the real part of this is the isotropic curvature. -/
lemma cm_Phi_eq {D : Curv4 n} (hD : IsAlgCurv D) (x y z w : Fin n → ℝ) :
    Phi D (wedgeF (cmZ x y) (cmZ z w)) (bar (wedgeF (cmZ x y) (cmZ z w)))
      = 4 * (Cone.EF D x y z w : ℂ) := by
  rw [Phi_wedge n D hD (cmZ x y) (cmZ z w)]
  simp only [cm_cRe_cmZ, cm_cIm_cmZ]
  rfl

/-- The componentwise norm of `(r : ℂ)` is bounded by the sup norm of the array. -/
lemma cm_norm_ofReal_le (D : Curv4 n) (i j k l : Fin n) :
    ‖(D i j k l : ℂ)‖ ≤ ‖D‖ := by
  have h1 : ‖(D i j k l : ℂ)‖ ^ 2 = (D i j k l) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  have h3 : |D i j k l| ≤ ‖D‖ := cm_abs_component_le_norm D i j k l
  have h2 : (D i j k l) ^ 2 ≤ ‖D‖ ^ 2 := by
    rw [← sq_abs (D i j k l)]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  nlinarith [norm_nonneg (D i j k l : ℂ), norm_nonneg D]

/-- The `ℂ`-bilinear form of a `4`-index array on a pair `(X, conj X)` is bounded by the sup norm
of the array times the square of the `ℓ¹`-norm of `X`. -/
lemma cm_Phi_bound (D : Curv4 n) (X : Fin n × Fin n → ℂ) :
    ‖Phi D X (bar X)‖ ≤ ‖D‖ * (∑ p : Fin n × Fin n, ‖X p‖) ^ 2 := by
  have h1 : ‖∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
      (D p.1 p.2 q.1 q.2 : ℂ) * X p * bar X q‖
      ≤ ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, ‖D‖ * ‖X p‖ * ‖X q‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun q _ => ?_)
    have hbar : ‖bar X q‖ = ‖X q‖ := by rw [bar_apply]; exact norm_star _
    rw [norm_mul, norm_mul, hbar]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (cm_norm_ofReal_le D p.1 p.2 q.1 q.2) (norm_nonneg (X p)))
      (norm_nonneg (X q))
  have hA : (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, ‖D‖ * ‖X p‖ * ‖X q‖)
      = ∑ p : Fin n × Fin n, (‖D‖ * ‖X p‖) * (∑ q : Fin n × Fin n, ‖X q‖) := by
    apply Finset.sum_congr rfl; intro p _
    rw [← Finset.mul_sum]
  have hB : (∑ p : Fin n × Fin n, (‖D‖ * ‖X p‖) * (∑ q : Fin n × Fin n, ‖X q‖))
      = (∑ p : Fin n × Fin n, ‖D‖ * ‖X p‖) * (∑ q : Fin n × Fin n, ‖X q‖) := by
    rw [← Finset.sum_mul]
  have hC : (∑ p : Fin n × Fin n, ‖D‖ * ‖X p‖)
      = ‖D‖ * (∑ p : Fin n × Fin n, ‖X p‖) := by
    rw [← Finset.mul_sum]
  have h2 : (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, ‖D‖ * ‖X p‖ * ‖X q‖)
      = ‖D‖ * (∑ p : Fin n × Fin n, ‖X p‖) ^ 2 := by
    rw [hA, hB, hC]; ring
  rw [Phi]
  exact h1.trans (le_of_eq h2)

/-- Cauchy–Schwarz for the `ℓ¹`-norm of a pair-indexed vector. -/
lemma cm_sq_sum_le (X : Fin n × Fin n → ℂ) :
    (∑ p : Fin n × Fin n, ‖X p‖) ^ 2 ≤ (n : ℝ) ^ 2 * ∑ p : Fin n × Fin n, ‖X p‖ ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p : Fin n × Fin n => ‖X p‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ] at h
  have hcard : ((Fintype.card (Fin n × Fin n) : ℕ) : ℝ) = (n : ℝ) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, sq]
  refine h.trans (le_of_eq ?_)
  simp only [nsmul_eq_mul, mul_one]
  rw [hcard]
  ring

/-- Pointwise: `‖ζᵢηⱼ - ζⱼηᵢ‖² = qfA² + qfB²`. -/
lemma cm_wedgeF_normSq (x y z w : Fin n → ℝ) (i j : Fin n) :
    ‖wedgeF (cmZ x y) (cmZ z w) (i, j)‖ ^ 2 = qfA x y z w i j ^ 2 + qfB x y z w i j ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [wedgeF, cmZ, qfA, qfB, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero]
  ring

/-- The `ℓ²`-norm² of the decomposable form `ζ ∧ η` is `2 · EF (Iso n)`. -/
lemma cm_normSq_sum (x y z w : Fin n → ℝ) :
    (∑ p : Fin n × Fin n, ‖wedgeF (cmZ x y) (cmZ z w) p‖ ^ 2)
      = 2 * Cone.EF (Iso n) x y z w := by
  rw [Fintype.sum_prod_type]
  simp only [cm_wedgeF_normSq]
  exact Chat_lagrange n x y z w

/-- **Key estimate.** For an algebraic curvature tensor `D` the isotropic curvature form `Cone.EF D`
is dominated by `‖D‖` times the round-sphere form `Cone.EF (Iso n)`. -/
lemma cm_EF_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Curv4 n, IsAlgCurv D → ∀ x y z w : Fin n → ℝ,
      |Cone.EF D x y z w| ≤ C * ‖D‖ * Cone.EF (Iso n) x y z w := by
  refine ⟨(n : ℝ) ^ 2, by positivity, ?_⟩
  intro D hD x y z w
  set X : Fin n × Fin n → ℂ := wedgeF (cmZ x y) (cmZ z w) with hX
  have hsum : (∑ p : Fin n × Fin n, ‖X p‖ ^ 2) = 2 * Cone.EF (Iso n) x y z w :=
    cm_normSq_sum x y z w
  have hnonneg : 0 ≤ Cone.EF (Iso n) x y z w := by
    have h : 0 ≤ ∑ p : Fin n × Fin n, ‖X p‖ ^ 2 :=
      Finset.sum_nonneg (fun p _ => sq_nonneg _)
    linarith [hsum]
  have hre : (4 * Cone.EF D x y z w : ℝ) = (Phi D X (bar X)).re := by
    rw [cm_Phi_eq hD x y z w]
    simp [Complex.mul_re]
  have h1 : |4 * Cone.EF D x y z w|
      ≤ ‖D‖ * ((n : ℝ) ^ 2 * (2 * Cone.EF (Iso n) x y z w)) := by
    rw [hre]
    calc |(Phi D X (bar X)).re| ≤ ‖Phi D X (bar X)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖D‖ * (∑ p : Fin n × Fin n, ‖X p‖) ^ 2 := cm_Phi_bound D X
      _ ≤ ‖D‖ * ((n : ℝ) ^ 2 * ∑ p : Fin n × Fin n, ‖X p‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (cm_sq_sum_le X) (norm_nonneg D)
      _ = ‖D‖ * ((n : ℝ) ^ 2 * (2 * Cone.EF (Iso n) x y z w)) := by rw [hsum]
  have habs : (4 : ℝ) * |Cone.EF D x y z w| = |4 * Cone.EF D x y z w| := by
    rw [abs_mul]
    norm_num
  have h4 : 4 * |Cone.EF D x y z w|
      ≤ 4 * ((n : ℝ) ^ 2 * ‖D‖ * Cone.EF (Iso n) x y z w) := by
    rw [habs]
    calc |4 * Cone.EF D x y z w|
        ≤ ‖D‖ * ((n : ℝ) ^ 2 * (2 * Cone.EF (Iso n) x y z w)) := h1
      _ ≤ 4 * ((n : ℝ) ^ 2 * ‖D‖ * Cone.EF (Iso n) x y z w) := by
          have hnn : 0 ≤ (n : ℝ) ^ 2 * ‖D‖ * Cone.EF (Iso n) x y z w :=
            mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg D)) hnonneg
          have heq : ‖D‖ * ((n : ℝ) ^ 2 * (2 * Cone.EF (Iso n) x y z w))
              = 2 * ((n : ℝ) ^ 2 * ‖D‖ * Cone.EF (Iso n) x y z w) := by ring
          rw [heq]; linarith
  linarith

/-! ## The Ricci form and the scalar curvature in terms of the sup norm -/

lemma cm_abs_scalAlg_le (X : Curv4 n) : |scalAlg X| ≤ (n : ℝ) ^ 2 * ‖X‖ := by
  have h1 : |scalAlg X| ≤ ∑ i : Fin n, ∑ j : Fin n, ‖X‖ := by
    rw [scalAlg]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    exact cm_abs_component_le_norm X i j i j
  have h2 : (∑ i : Fin n, ∑ j : Fin n, ‖X‖) = (n : ℝ) ^ 2 * ‖X‖ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rwa [h2] at h1

lemma cm_abs_ricForm_le (X : Curv4 n) (v : Fin n → ℝ) :
    |∑ i, ∑ j, ric X i j * v i * v j| ≤ (n : ℝ) ^ 2 * ‖X‖ * (∑ i, v i * v i) := by
  have hric : ∀ i j, |ric X i j| ≤ (n : ℝ) * ‖X‖ := by
    intro i j
    rw [ric]
    calc |∑ k : Fin n, X k i k j| ≤ ∑ k : Fin n, ‖X‖ :=
          le_trans (Finset.abs_sum_le_sum_abs _ _)
            (Finset.sum_le_sum fun k _ => cm_abs_component_le_norm X k i k j)
      _ = (n : ℝ) * ‖X‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : |∑ i, ∑ j, ric X i j * v i * v j|
      ≤ ∑ i, ∑ j, ((n : ℝ) * ‖X‖) * |v i| * |v j| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hric i j) (abs_nonneg (v i))) (abs_nonneg (v j))
  have h2 : (∑ i, ∑ j, ((n : ℝ) * ‖X‖) * |v i| * |v j|)
      = (n : ℝ) * ‖X‖ * (∑ i, |v i|) ^ 2 := by
    have hA : (∑ i, ∑ j, ((n : ℝ) * ‖X‖) * |v i| * |v j|)
        = ∑ i, (((n : ℝ) * ‖X‖) * |v i|) * (∑ j, |v j|) := by
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.mul_sum]
    have hB : (∑ i, (((n : ℝ) * ‖X‖) * |v i|) * (∑ j, |v j|))
        = (∑ i, ((n : ℝ) * ‖X‖) * |v i|) * (∑ j, |v j|) := by
      rw [← Finset.sum_mul]
    have hC : (∑ i, ((n : ℝ) * ‖X‖) * |v i|) = (n : ℝ) * ‖X‖ * (∑ i, |v i|) := by
      rw [← Finset.mul_sum]
    rw [hA, hB, hC]; ring
  have h3 : (∑ i, |v i|) ^ 2 ≤ (n : ℝ) * (∑ i, v i * v i) := by
    have h := sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i : Fin n => |v i|) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ] at h
    refine h.trans (le_of_eq ?_)
    simp only [Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hsq : (∑ i : Fin n, |v i| ^ 2) = ∑ i, v i * v i := by
      apply Finset.sum_congr rfl; intro i _
      rw [sq_abs, pow_two]
    rw [hsq]
    ring
  calc |∑ i, ∑ j, ric X i j * v i * v j|
      ≤ ∑ i, ∑ j, ((n : ℝ) * ‖X‖) * |v i| * |v j| := h1
    _ = (n : ℝ) * ‖X‖ * (∑ i, |v i|) ^ 2 := h2
    _ ≤ (n : ℝ) * ‖X‖ * ((n : ℝ) * (∑ i, v i * v i)) := by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        exact mul_le_mul_of_nonneg_left h3 (mul_nonneg hn0 (norm_nonneg X))
    _ = (n : ℝ) ^ 2 * ‖X‖ * (∑ i, v i * v i) := by ring

/-! ## `RicPinch` survives a small algebraic perturbation of `c • Iso n` -/

lemma cm_ricPinch_shift (hn : 2 ≤ n) {c p : ℝ} (hc : 0 < c) (hp : p < 1)
    {E : Curv4 n}
    (hE : (|p| * (n : ℝ) + (n : ℝ) ^ 2) * ‖E‖ ≤ (1 - p) * c * ((n : ℝ) - 1)) :
    RicPinch p (c • Iso n + E) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  intro v
  set A : ℝ := ∑ i, v i * v i with hA
  have hAnn : 0 ≤ A := by
    rw [hA]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  have hscal : scalAlg (c • Iso n + E) = c * ((n : ℝ) * ((n : ℝ) - 1)) + scalAlg E := by
    rw [scalAlg_add, scalAlg_smul, scalAlg_iso]
  have hric : ∀ i j, ric (c • Iso n + E) i j = c * ((n : ℝ) - 1) * id2 n i j + ric E i j := by
    intro i j
    rw [ric_add, ric_smul, ric_iso]; ring
  have hid2 : (∑ i, ∑ j, id2 n i j * v i * v j) = A := by
    rw [hA]
    apply Finset.sum_congr rfl; intro i _
    rw [show (∑ j, id2 n i j * v i * v j) = v i * (∑ j, id2 n i j * v j) from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)]
    rw [ellinv_sum_id2_mul]
  have hL : (p * scalAlg (c • Iso n + E) / (n : ℝ)) * A
      = p * c * ((n : ℝ) - 1) * A + (p * scalAlg E / (n : ℝ)) * A := by
    rw [hscal]
    field_simp
  have hR : (∑ i, ∑ j, ric (c • Iso n + E) i j * v i * v j)
      = c * ((n : ℝ) - 1) * A + (∑ i, ∑ j, ric E i j * v i * v j) := by
    have h1 : (∑ i, ∑ j, ric (c • Iso n + E) i j * v i * v j)
        = ∑ i, ∑ j, (c * ((n : ℝ) - 1) * id2 n i j + ric E i j) * v i * v j := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [hric]
    rw [h1]
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    rw [show (∑ i, ∑ j, c * ((n : ℝ) - 1) * id2 n i j * v i * v j)
        = c * ((n : ℝ) - 1) * (∑ i, ∑ j, id2 n i j * v i * v j) from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      ring]
    rw [hid2]
  rw [hL, hR]
  have hFE := cm_abs_ricForm_le E v
  have hSE := cm_abs_scalAlg_le E
  have hb : |p * scalAlg E / (n : ℝ)| ≤ |p| * (n : ℝ) * ‖E‖ := by
    rw [abs_div, abs_mul, abs_of_pos hn0, div_le_iff₀ hn0]
    have h := (abs_le.mp hSE).2
    nlinarith [abs_nonneg p, norm_nonneg E, h]
  have hS_up : (p * scalAlg E / (n : ℝ)) * A ≤ (|p| * (n : ℝ) * ‖E‖) * A := by
    have h := (abs_le.mp hb).2
    nlinarith [hAnn]
  have hF_low : -((n : ℝ) ^ 2 * ‖E‖ * A) ≤ ∑ i, ∑ j, ric E i j * v i * v j := by
    have h := (abs_le.mp hFE).1
    linarith [hA]
  have hEA : (|p| * (n : ℝ) + (n : ℝ) ^ 2) * ‖E‖ * A ≤ (1 - p) * c * ((n : ℝ) - 1) * A :=
    mul_le_mul_of_nonneg_right hE hAnn
  have hmid : p * scalAlg E / (n : ℝ) * A - (∑ i, ∑ j, ric E i j * v i * v j)
      ≤ (|p| * (n : ℝ) + (n : ℝ) ^ 2) * ‖E‖ * A := by
    nlinarith [hS_up, hF_low]
  have hgoal : p * scalAlg E / (n : ℝ) * A - (∑ i, ∑ j, ric E i j * v i * v j)
      ≤ (1 - p) * c * ((n : ℝ) - 1) * A := le_trans hmid hEA
  have hexp : (1 - p) * c * ((n : ℝ) - 1) * A
      = c * ((n : ℝ) - 1) * A - p * c * ((n : ℝ) - 1) * A := by ring
  linarith

/-! ## A neighbourhood of `Iso n` lies in `Ccone a b p` -/

theorem cm_Ccone_margin (n : ℕ) (hn : 2 ≤ n) {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hp : p < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : Curv4 n, IsAlgCurv R → ‖R - Iso n‖ ≤ ρ →
      R ∈ Ccone (n := n) a b p := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2r : (0 : ℝ) ≤ (n : ℝ) - 2 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hApos : 0 < 1 + 2 * ((n : ℝ) - 1) * a := by nlinarith [ha, hn1]
  have hden1 : 1 + 2 * ((n : ℝ) - 1) * a ≠ 0 := ne_of_gt hApos
  have hden2 : 1 + ((n : ℝ) - 2) * b ≠ 0 := by nlinarith [hb, h2r]
  obtain ⟨M, hMpos, hM⟩ := cm_linv_bound (n := n) a b
  obtain ⟨C, hC0, hC⟩ := cm_EF_bound n
  set c : ℝ := 1 / (1 + 2 * ((n : ℝ) - 1) * a) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact div_pos one_pos hApos
  set K1 : ℝ := max C 1 with hK1def
  have hK1pos : 0 < K1 := lt_max_iff.mpr (Or.inr one_pos)
  have hC_le_K1 : C ≤ K1 := le_max_left _ _
  set K2 : ℝ := max (|p| * (n : ℝ) + (n : ℝ) ^ 2) 1 with hK2def
  have hK2pos : 0 < K2 := lt_max_iff.mpr (Or.inr one_pos)
  have hK2ge : |p| * (n : ℝ) + (n : ℝ) ^ 2 ≤ K2 := le_max_left _ _
  have h1p : 0 < 1 - p := by linarith
  have hn1pos : 0 < (n : ℝ) - 1 := by linarith
  set m : ℝ := min (c / K1) ((1 - p) * c * ((n : ℝ) - 1) / K2) with hmdef
  have hm_le1 : m ≤ c / K1 := by rw [hmdef]; exact min_le_left _ _
  have hm_le2 : m ≤ (1 - p) * c * ((n : ℝ) - 1) / K2 := by
    rw [hmdef]; exact min_le_right _ _
  have hmpos : 0 < m := by
    rw [hmdef]
    exact lt_min (div_pos hcpos hK1pos)
      (div_pos (mul_pos (mul_pos h1p hcpos) hn1pos) hK2pos)
  have hmK1 : m * K1 ≤ c := (le_div_iff₀ hK1pos).mp hm_le1
  have hmK2 : m * K2 ≤ (1 - p) * c * ((n : ℝ) - 1) := (le_div_iff₀ hK2pos).mp hm_le2
  have hmaxpos : (0 : ℝ) < max M 1 := lt_max_iff.mpr (Or.inr one_pos)
  refine ⟨m / (2 * max M 1), div_pos hmpos (by positivity), ?_⟩
  intro R hR hRnorm
  set E : Curv4 n := linv a b (R - Iso n) with hEdef
  have hRsub : IsAlgCurv (R - Iso n) := isAlgCurv_sub hR (Iso_algCurv n)
  have hEalg : IsAlgCurv E := cm_linv_isAlgCurv hRsub
  have hEnorm : ‖E‖ ≤ m / 2 := by
    have h1 : ‖E‖ ≤ M * ‖R - Iso n‖ := by rw [hEdef]; exact hM _
    have h2 : M * ‖R - Iso n‖ ≤ M * (m / (2 * max M 1)) :=
      mul_le_mul_of_nonneg_left hRnorm hMpos.le
    have h3 : M * (m / (2 * max M 1)) ≤ m / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * max M 1)]
      nlinarith [le_max_left M 1, hmpos.le]
    linarith
  have hSdecomp : linv a b R = c • Iso n + E := by
    have h1 : linv a b R = linv a b (Iso n) + linv a b (R - Iso n) := by
      rw [← linv_add]; congr 1; abel
    rw [h1, hEdef, cm_linv_iso (n := n) (by omega) hden1, hcdef]
  have hCE : C * ‖E‖ ≤ c := by
    have h1 : C * ‖E‖ ≤ K1 * ‖E‖ := mul_le_mul_of_nonneg_right hC_le_K1 (norm_nonneg E)
    have h2 : K1 * ‖E‖ ≤ K1 * (m / 2) := mul_le_mul_of_nonneg_left hEnorm hK1pos.le
    have h3 : K1 * (m / 2) ≤ c := by nlinarith [hmK1, hcpos]
    linarith
  have hEconst : (|p| * (n : ℝ) + (n : ℝ) ^ 2) * ‖E‖ ≤ (1 - p) * c * ((n : ℝ) - 1) := by
    have h2 : (|p| * (n : ℝ) + (n : ℝ) ^ 2) * ‖E‖ ≤ K2 * ‖E‖ :=
      mul_le_mul_of_nonneg_right hK2ge (norm_nonneg E)
    have h3 : K2 * ‖E‖ ≤ K2 * (m / 2) := mul_le_mul_of_nonneg_left hEnorm hK2pos.le
    have h4 : K2 * (m / 2) ≤ (1 - p) * c * ((n : ℝ) - 1) := by
      have hpos : 0 ≤ (1 - p) * c * ((n : ℝ) - 1) :=
        mul_nonneg (mul_nonneg h1p.le hcpos.le) hn1pos.le
      nlinarith [hmK2, hpos, hK2pos]
    linarith
  have hInPIC2 : InPIC2 (c • Iso n + E) := by
    rw [Cone.inPIC2_iff]
    intro x y z w
    have hsplit : Cone.EF (c • Iso n + E) x y z w
        = c * Cone.EF (Iso n) x y z w + Cone.EF E x y z w := by
      simpa using Cone.EF_add_smul c 1 (Iso n) E x y z w
    have hIsonn : 0 ≤ Cone.EF (Iso n) x y z w :=
      (Cone.inPIC2_iff (Iso n)).mp (Cone.inPIC2_iso n) x y z w
    have hlow : -(C * ‖E‖ * Cone.EF (Iso n) x y z w) ≤ Cone.EF E x y z w :=
      le_trans (neg_le_neg (hC E hEalg x y z w)) (neg_abs_le _)
    rw [hsplit]
    nlinarith [hlow, hIsonn, hCE, hcpos]
  refine ⟨linv a b R, ?_, ell_linv n hden1 hden2 hR⟩
  rw [hSdecomp]
  exact ⟨isAlgCurv_add (isAlgCurv_smul c (Iso_algCurv n)) hEalg, hInPIC2,
    cm_ricPinch_shift hn hcpos hp hEconst⟩

/-- The Brendle–Schoen pinching cone `Chat n s` contains a neighbourhood of the round sphere
`Iso n` inside the space of algebraic curvature tensors. -/
theorem Chat_margin (n : ℕ) (hn : 2 ≤ n) :
    ∀ s : ℝ, 0 < s → ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : Submission.Diff.Alg.Curv4 n,
      Submission.Diff.Alg.IsAlgCurv R → ‖R - Submission.Diff.Alg.Iso n‖ ≤ ρ →
        R ∈ Work.Diff.Alg.Pinch.Chat n s := by
  intro s hs
  by_cases hs2 : s ≤ 1 / 2
  · obtain ⟨ρ, hρ, hle⟩ :=
      cm_Ccone_margin n hn (a := chatA n s) (b := s) (p := chatP n s)
        (chatA_nonneg hn hs.le) hs (chatP_lt_one hn s)
    refine ⟨ρ, hρ, fun R hR hnorm => ?_⟩
    rw [Chat_eq_Ccone n hs2]
    exact hle R hR hnorm
  · have h2r : (0 : ℝ) ≤ (n : ℝ) - 2 := chat_c_nonneg hn
    have hden : 0 < (n : ℝ) - 2 + 8 * s := by linarith
    have hp : 1 - 4 / ((n : ℝ) - 2 + 8 * s) < 1 := by
      have : 0 < 4 / ((n : ℝ) - 2 + 8 * s) := by positivity
      linarith
    obtain ⟨ρ, hρ, hle⟩ :=
      cm_Ccone_margin n hn (a := s) (b := 1 / 2) (p := 1 - 4 / ((n : ℝ) - 2 + 8 * s))
        hs.le (by norm_num) hp
    refine ⟨ρ, hρ, fun R hR hnorm => ?_⟩
    rw [Chat, ite_eq_right hs2]
    exact hle R hR hnorm

end Work.Diff.Alg.Pinch
