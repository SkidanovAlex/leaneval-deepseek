/-
  Work.WilE2.Ebc.Poly — the polynomial bookkeeping for `Work.WilE2.euclidean_ball_components`.

  This module collects everything about the EA polynomials

  * `sqSum g = ∑_{f ∈ g} f²` (so that `{sqSum g = 0} = Zset c g` and `sqSum g ≥ 0`),
  * `tubePoly g ε ρ = sqSum g + ε (∑ᵢ Xᵢ² - ρ²)`,
  * `critPoly ch g ε ρ i₀ sl` — the square critical system `F_ε = 0`,
    `∂_j F_ε - sl j ∂_{i₀} F_ε = 0` (`j ≠ i₀`) —

  together with the evaluation/degree dictionary that relates them to the real functions they
  represent.  It is split off from `euclidean_ball_components` so that lemmas about it can be
  delegated and proved in parallel without racing the main file.
-/
import Mathlib
import Submission.Work.WilE2.Ebc.Defs
import Submission.Work.WilE2.Ebc.SlopeDefs
import Submission.Work.WilE2.contDiff_ev
import Submission.Work.WilE5.Basic
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval
import Submission.Work.WilE5.Strat.flatConormalTools
import Submission.Work.WilE5.Cells.khovCount
import Submission.Work.WilE2.Degree

set_option autoImplicit false
noncomputable section

open Classical
open WilkiesDesign WilkiesDesign.E

namespace Work.WilE2

/-! ## §1. Sum of squares and the tube / critical-system polynomials -/

/-- Sum of squares of a finite family of EA polynomials. -/
def sqSum {k r : ℕ} (g : Finset (EAPoly k r)) : EAPoly k r := ∑ f ∈ g, f ^ 2

/-- The tube polynomial `Φ + ε (∑ᵢ Xᵢ² - ρ²)`. -/
def tubePoly {k r : ℕ} (g : Finset (EAPoly k r)) (ε ρ : ℝ) : EAPoly k r :=
  sqSum g + MvPolynomial.C ε *
    (∑ i : Fin k, (MvPolynomial.X (Sum.inl i) : EAPoly k r) ^ 2 -
      MvPolynomial.C (ρ ^ 2))

/-- The critical-system polynomials for the direction `sl` (with `sl i₀` normalised to one):
`F_ε` and, for `i ≠ i₀`, `∂_i F_ε - sl i · ∂_{i₀} F_ε`. -/
def critPoly {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ) (i₀ : Fin k)
    (sl : Fin k → ℝ) (i : Fin k) : EAPoly k r :=
  if i = i₀ then tubePoly g ε ρ
  else eaD ch i (tubePoly g ε ρ) - MvPolynomial.C (sl i) * eaD ch i₀ (tubePoly g ε ρ)

theorem eaEval_sqSum {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (x : Fin k → ℝ) :
    eaEval ch (sqSum g) x = ∑ f ∈ g, (eaEval ch f x) ^ 2 := by
  show Work.WilE5.eaEvalHom ch x (∑ f ∈ g, f ^ 2) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun f _ => by rw [map_pow]; rfl

theorem sqSum_nonneg {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (x : Fin k → ℝ) :
    0 ≤ eaEval ch (sqSum g) x := by
  rw [eaEval_sqSum]
  exact Finset.sum_nonneg fun f _ => sq_nonneg _

theorem sqSum_eq_zero_iff {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r))
    (x : Fin k → ℝ) : eaEval ch (sqSum g) x = 0 ↔ x ∈ Zset ch g := by
  rw [eaEval_sqSum, Finset.sum_eq_zero_iff_of_nonneg (fun f _ => sq_nonneg (eaEval ch f x))]
  constructor
  · intro h f hf
    exact sq_eq_zero_iff.mp (h f hf)
  · intro h f hf
    rw [h f hf, pow_two, mul_zero]

theorem eaEval_sub' {k r : ℕ} (ch : EAChain k r) (Q Q' : EAPoly k r) (x : Fin k → ℝ) :
    eaEval ch (Q - Q') x = eaEval ch Q x - eaEval ch Q' x := by
  show Work.WilE5.eaEvalHom ch x (Q - Q') = _
  rw [map_sub]; rfl

theorem eaEval_finset_sum {k r : ℕ} (ch : EAChain k r) {ι : Type*} (t : Finset ι)
    (Q : ι → EAPoly k r) (x : Fin k → ℝ) :
    eaEval ch (∑ i ∈ t, Q i) x = ∑ i ∈ t, eaEval ch (Q i) x := by
  show Work.WilE5.eaEvalHom ch x (∑ i ∈ t, Q i) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => rfl

theorem eaEval_coord_sq_sum {k r : ℕ} (ch : EAChain k r) (x : Fin k → ℝ) :
    eaEval ch (∑ i : Fin k, (MvPolynomial.X (Sum.inl i) : EAPoly k r) ^ 2) x
      = ∑ i : Fin k, (x i) ^ 2 := by
  rw [eaEval_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show Work.WilE5.eaEvalHom ch x ((MvPolynomial.X (Sum.inl i) : EAPoly k r) ^ 2) = _
  rw [map_pow, show Work.WilE5.eaEvalHom ch x (MvPolynomial.X (Sum.inl i) : EAPoly k r) = x i
    from Work.WilE5.eaEval_X_inl ch i x]

theorem eaEval_tubePoly {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ)
    (x : Fin k → ℝ) :
    eaEval ch (tubePoly g ε ρ) x = tubeFun (fun y => eaEval ch (sqSum g) y) ρ ε x := by
  unfold tubePoly tubeFun
  rw [Work.WilE5.eaEval_add, Work.WilE5.eaEval_mul, eaEval_sub', eaEval_coord_sq_sum,
    Work.WilE5.eaEval_C, Work.WilE5.eaEval_C]

/-- The symbolic derivative agrees with the actual one on the coordinate directions. -/
theorem fderiv_eaEval_apply {k r : ℕ} (ch : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ)
    (j : Fin k) :
    fderiv ℝ (fun y => eaEval ch Q y) x (Pi.single j 1) = eaEval ch (eaD ch j Q) x := by
  have h := Work.WilE5.Calc.hasFDerivAt_eaEval ch Q x
  rw [h.fderiv]
  show (∑ i : Fin k, eaEval ch (eaD ch i Q) x •
      (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ)) (Pi.single j 1) = _
  exact Work.WilE5.Strat.sum_smul_proj_single (fun i => eaEval ch (eaD ch i Q) x) j

theorem contDiff_eaEval_fun {k r : ℕ} (ch : EAChain k r) (Q : EAPoly k r) (n : ℕ) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun y : Fin k → ℝ => eaEval ch Q y) := by
  have h : (fun y : Fin k → ℝ => eaEval ch Q y) = (ESys.ofChain ch).ev Q := by
    funext y; exact ESys.ofChain_ev ch Q y
  rw [h]; exact contDiff_ev _ _ n

/-- The tube function of a sum of squares is `C²`. -/
theorem contDiff_tubeFun {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ) :
    ContDiff ℝ 2 (tubeFun (fun y => eaEval ch (sqSum g) y) ρ ε) := by
  have hφ : (fun y : Fin k → ℝ => eaEval ch (sqSum g) y)
      = fun y => ∑ f ∈ g, (eaEval ch f y) ^ 2 := by
    funext y; exact eaEval_sqSum ch g y
  rw [hφ]
  unfold tubeFun
  refine ContDiff.add ?_ (contDiff_const.mul ?_)
  · exact ContDiff.sum fun f _ => (contDiff_eaEval_fun ch f 2).pow 2
  · refine ContDiff.sub ?_ contDiff_const
    exact ContDiff.sum fun i _ => contDiff_apply ℝ ℝ i |>.pow 2

/-- `eaEval c Q` is continuous. -/
theorem continuous_eaEval_fun {k r : ℕ} (ch : EAChain k r) (Q : EAPoly k r) :
    Continuous fun y : Fin k → ℝ => eaEval ch Q y :=
  (contDiff_eaEval_fun ch Q 0).continuous

/-- The real function `x ↦ eaEval ch (tubePoly g ε ρ) x` represented by the tube polynomial. -/
def tubeF {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ) :
    (Fin k → ℝ) → ℝ :=
  fun y => eaEval ch (tubePoly g ε ρ) y

@[simp] theorem tubeF_apply {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ)
    (y : Fin k → ℝ) : tubeF ch g ε ρ y = eaEval ch (tubePoly g ε ρ) y := rfl

theorem tubeF_eq_tubeFun {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ) :
    tubeF ch g ε ρ = tubeFun (fun y => eaEval ch (sqSum g) y) ρ ε := by
  funext y; exact eaEval_tubePoly ch g ε ρ y

theorem contDiff_tubeF {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ) :
    ContDiff ℝ 2 (tubeF ch g ε ρ) := by
  rw [tubeF_eq_tubeFun]; exact contDiff_tubeFun ch g ε ρ

theorem continuous_tubeF {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ) :
    Continuous (tubeF ch g ε ρ) :=
  (contDiff_tubeF ch g ε ρ).continuous

/-- `eaEval c Q` is analytic on all of `ℝᵏ`. -/
theorem analyticOn_eaEval_fun {k r : ℕ} (ch : EAChain k r) (Q : EAPoly k r) :
    AnalyticOn ℝ (fun y : Fin k → ℝ => eaEval ch Q y) Set.univ :=
  analyticOn_univ.mpr fun x _ => Work.WilE5.Strat.analyticAt_eaEval ch Q x

/-! ## §2. The evaluation dictionary for `critPoly` -/

theorem eaEval_critPoly_self {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ)
    (i₀ : Fin k) (sl : Fin k → ℝ) (x : Fin k → ℝ) :
    eaEval ch (critPoly ch g ε ρ i₀ sl i₀) x = eaEval ch (tubePoly g ε ρ) x := by
  simp [critPoly]

theorem eaEval_critPoly_other {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ)
    (i₀ : Fin k) (sl : Fin k → ℝ) (x : Fin k → ℝ) {i : Fin k} (hi : i ≠ i₀) :
    eaEval ch (critPoly ch g ε ρ i₀ sl i) x
      = fderiv ℝ (fun y => eaEval ch (tubePoly g ε ρ) y) x (Pi.single i 1)
        - sl i * fderiv ℝ (fun y => eaEval ch (tubePoly g ε ρ) y) x (Pi.single i₀ 1) := by
  rw [critPoly, if_neg hi, eaEval_sub', Work.WilE5.eaEval_mul, Work.WilE5.eaEval_C,
    fderiv_eaEval_apply, fderiv_eaEval_apply]

/-- The evaluation of `critPoly` at `x` determines (and is determined by) the value and the
derivatives of `x ↦ eaEval ch (tubePoly g ε ρ) x`. -/
theorem eaEval_critPoly_iff {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ)
    (i₀ : Fin k) (sl : Fin k → ℝ) (x : Fin k → ℝ) :
    (∀ i, eaEval ch (critPoly ch g ε ρ i₀ sl i) x = 0) ↔
      eaEval ch (tubePoly g ε ρ) x = 0 ∧ ∀ j, j ≠ i₀ →
        fderiv ℝ (fun y => eaEval ch (tubePoly g ε ρ) y) x (Pi.single j 1)
          = sl j * fderiv ℝ (fun y => eaEval ch (tubePoly g ε ρ) y) x (Pi.single i₀ 1) := by
  constructor
  · intro h
    refine ⟨by simpa [eaEval_critPoly_self] using h i₀, fun j hj => ?_⟩
    have hj' := h j
    rw [eaEval_critPoly_other ch g ε ρ i₀ sl x hj] at hj'
    linarith
  · intro ⟨h0, h1⟩ i
    rcases eq_or_ne i i₀ with rfl | hi
    · rw [eaEval_critPoly_self]; exact h0
    · rw [eaEval_critPoly_other ch g ε ρ i₀ sl x hi, h1 i hi]; ring

/-- The `(i,j)` entry of the Jacobian of the `critPoly` system at `x`. -/
theorem eaEval_eaD_critPoly {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ)
    (i₀ : Fin k) (sl : Fin k → ℝ) (x : Fin k → ℝ) (i j : Fin k) :
    eaEval ch (eaD ch j (critPoly ch g ε ρ i₀ sl i)) x
      = fderiv ℝ (fun y => eaEval ch (critPoly ch g ε ρ i₀ sl i) y) x (Pi.single j 1) :=
  (fderiv_eaEval_apply ch (critPoly ch g ε ρ i₀ sl i) x j).symm

/-! ## §3. Degrees -/

theorem totalDegree_sqSum_le {k r : ℕ} (g : Finset (EAPoly k r)) :
    (sqSum g).totalDegree ≤ 2 * ∑ f ∈ g, atomDeg f := by
  have h : ∀ t : Finset (EAPoly k r), (∑ f ∈ t, f ^ 2).totalDegree ≤ 2 * ∑ f ∈ t, atomDeg f := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      conv_lhs => rw [Finset.sum_insert ha]
      refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
        have h1 : a.totalDegree ≤ atomDeg a := by simp [atomDeg]
        rw [Finset.sum_insert ha]
        omega
      · rw [Finset.sum_insert ha]
        exact le_trans ih (by omega)
  unfold sqSum
  exact h g

theorem totalDegree_tubePoly_le {k r : ℕ} (g : Finset (EAPoly k r)) (ε ρ : ℝ) :
    (tubePoly g ε ρ).totalDegree ≤ 2 * ∑ f ∈ g, atomDeg f + 2 := by
  unfold tubePoly
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · have := totalDegree_sqSum_le g; omega
  · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C]
    have h2 : (∑ i : Fin k, (MvPolynomial.X (Sum.inl i) : EAPoly k r) ^ 2 -
        MvPolynomial.C (ρ ^ 2)).totalDegree ≤ 2 := by
      refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
      · refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
        refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
        simp [MvPolynomial.totalDegree_X]
      · rw [MvPolynomial.totalDegree_C]; norm_num
    omega

theorem totalDegree_eaD_le {k r : ℕ} (ch : EAChain k r) (i : Fin k) (Q : EAPoly k r) :
    (eaD ch i Q).totalDegree ≤ Q.totalDegree := by
  have h := ESys.d_totalDegree_le (ESys.ofChain ch) i Q
  rwa [ESys.ofChain_d] at h

theorem atomDeg_critPoly_le {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r)) (ε ρ : ℝ)
    (i₀ : Fin k) (sl : Fin k → ℝ) (i : Fin k) :
    atomDeg (critPoly ch g ε ρ i₀ sl i) ≤ 2 * ∑ f ∈ g, atomDeg f + 3 := by
  have key : ∀ Q : EAPoly k r, Q.totalDegree ≤ 2 * (∑ f ∈ g, atomDeg f) + 2 →
      atomDeg Q ≤ 2 * (∑ f ∈ g, atomDeg f) + 3 := by
    intro Q hQ
    have h : atomDeg Q = Q.totalDegree + 1 := rfl
    omega
  have hD : (eaD ch i (tubePoly g ε ρ)).totalDegree ≤ 2 * (∑ f ∈ g, atomDeg f) + 2 :=
    (totalDegree_eaD_le ch i (tubePoly g ε ρ)).trans (totalDegree_tubePoly_le g ε ρ)
  have hD' : (eaD ch i₀ (tubePoly g ε ρ)).totalDegree ≤ 2 * (∑ f ∈ g, atomDeg f) + 2 :=
    (totalDegree_eaD_le ch i₀ (tubePoly g ε ρ)).trans (totalDegree_tubePoly_le g ε ρ)
  have hprod : (MvPolynomial.C (sl i) * eaD ch i₀ (tubePoly g ε ρ)).totalDegree
      ≤ 2 * (∑ f ∈ g, atomDeg f) + 2 := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact hD'
  unfold critPoly
  split
  · exact key _ (totalDegree_tubePoly_le g ε ρ)
  · refine key _ ((MvPolynomial.totalDegree_sub _ _).trans (max_le hD hprod))

/-- The degree polynomial used in the final bound. -/
def ebcDegPoly (F : ℕ) : Polynomial ℕ :=
  (Polynomial.X + Polynomial.C F) * (Polynomial.C 2 * Polynomial.X + Polynomial.C 3)

theorem eval_ebcDegPoly (F D : ℕ) :
    (ebcDegPoly F).eval D = (D + F) * (2 * D + 3) := by
  simp [ebcDegPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    ]

theorem sum_atomDeg_critPoly_le {k r : ℕ} (ch : EAChain k r) (g : Finset (EAPoly k r))
    (ε ρ : ℝ) (i₀ : Fin k) (sl : Fin k → ℝ) {F : ℕ} (hkF : k ≤ F) :
    ∑ i : Fin k, atomDeg (critPoly ch g ε ρ i₀ sl i) ≤
      (ebcDegPoly F).eval (∑ f ∈ g, atomDeg f) := by
  have h1 : ∑ i : Fin k, atomDeg (critPoly ch g ε ρ i₀ sl i)
      ≤ k * (2 * (∑ f ∈ g, atomDeg f) + 3) := by
    calc ∑ i : Fin k, atomDeg (critPoly ch g ε ρ i₀ sl i)
        ≤ ∑ _i : Fin k, (2 * (∑ f ∈ g, atomDeg f) + 3) :=
          Finset.sum_le_sum fun i _ => atomDeg_critPoly_le ch g ε ρ i₀ sl i
      _ = k * (2 * (∑ f ∈ g, atomDeg f) + 3) := by
          simp [Finset.sum_const, Finset.card_univ]
  calc ∑ i : Fin k, atomDeg (critPoly ch g ε ρ i₀ sl i)
      ≤ k * (2 * (∑ f ∈ g, atomDeg f) + 3) := h1
    _ ≤ ((∑ f ∈ g, atomDeg f) + F) * (2 * (∑ f ∈ g, atomDeg f) + 3) :=
        Nat.mul_le_mul_right _ (by omega)
    _ = (ebcDegPoly F).eval (∑ f ∈ g, atomDeg f) := (eval_ebcDegPoly F _).symm

/-! ## §4. Monotonicity of `Polynomial.eval` on `ℕ` -/

/-- `Polynomial.eval` with `ℕ`-coefficients is monotone in the evaluation point. -/
theorem eval_mono_nat (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b :=
  Work.WilE5.Cells.khovEval_mono h

end Work.WilE2
