/-
# `Work.PARIMPL.ParSplit.no_double_root_near`

For every `c : ℂ` and every `ε > 0` there is `c'` within `ε` of `c` such that the fixed-point
polynomial `Qpoly c' = Fpoly c' - X` (with `Fpoly c = (TsqPoly c)^{∘5}` the second return map
`F c`) has **no double root**:

  `∀ z, ¬ (Qpoly c' |>.eval z = 0 ∧ (Qpoly c')' |>.eval z = 0)`.

## Strategy

The proof does not use any special shape of the tricorn: it is the usual "the discriminant is a
non-zero polynomial in the parameters" argument, made explicit.

* `Qpoly c = (QpolyMvP).map (eval at (c, c̄))` for a *fixed* polynomial `QpolyMvP` whose
  coefficients are polynomials in two indeterminates `X₀` (standing for `c`) and `X₁` (standing
  for `c̄`).  Indeed `TsqPoly c = (X² + C c̄)² + C c` depends on `c` and `c̄` polynomially and this
  is preserved by iteration.
* Hence the resultant `DMv := Res(QpolyMvP, (QpolyMvP)')` is a *fixed* element of
  `MvPolynomial (Fin 2) ℂ`, and `c ↦ eval ![c, c̄] DMv` equals the resultant of `Qpoly c` with its
  derivative.  It is therefore (the composition of `c ↦ (c, c̄)`, which is real analytic, with a
  polynomial function) real analytic on `ℂ`.
* At `c = 0` we have `Qpoly 0 = X^1024 - X`, which is squarefree (`Separable`), so this analytic
  function is *not* identically zero.  By the identity theorem for real-analytic functions its zero
  set has empty interior, which gives the required `c'`.
* If `Res(Qpoly c', (Qpoly c')') ≠ 0` then `Qpoly c'` is coprime to its derivative
  (`Polynomial.resultant_eq_zero_iff`), so no `z` can be a common root.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 10000
set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Polynomial
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

/-! ## The polynomial `Qpoly 0` is squarefree -/

lemma TsqPoly_zero : TsqPoly 0 = X ^ 4 := by
  rw [show TsqPoly 0 = (X ^ 2 + C (star (0 : ℂ))) ^ 2 + C (0 : ℂ) from rfl]
  rw [star_zero, map_zero, add_zero, add_zero, ← pow_mul]

lemma iterPoly_zero (n : ℕ) : iterPoly 0 n = X ^ (4 ^ n) := by
  induction n with
  | zero => simp [iterPoly]
  | succ n ih =>
    rw [iterPoly, ih, TsqPoly_zero, Polynomial.X_pow_comp, ← pow_mul, pow_succ']

lemma Qpoly_zero : Qpoly 0 = X ^ 1024 - X := by
  rw [Qpoly, Fpoly, iterPoly_zero]
  norm_num

lemma Qpoly_natDegree (c : ℂ) : (Qpoly c).natDegree = 1024 := by
  have h : (iterPoly c 5).natDegree = 1024 := by
    rw [show (iterPoly c 5).natDegree = 4 ^ 5 from by
      induction 5 with
      | zero => simp [iterPoly]
      | succ n ih =>
        rw [iterPoly, natDegree_comp, ih,
          show (TsqPoly c).natDegree = 4 from by
            rw [show TsqPoly c = (X ^ 2 + C (star c)) ^ 2 + C c from rfl]
            compute_degree!]
        ring]
    norm_num
  rw [Qpoly, natDegree_sub_eq_left_of_natDegree_lt]
  · rw [Fpoly]; exact h
  · rw [Fpoly, h]; simp

lemma Qpoly_ne_zero (c : ℂ) : Qpoly c ≠ 0 := by
  intro h
  have := congrArg Polynomial.natDegree h
  rw [Qpoly_natDegree, Polynomial.natDegree_zero] at this
  exact absurd this (by norm_num)

lemma Qpoly_derivative_natDegree (c : ℂ) : ((Qpoly c).derivative).natDegree = 1023 := by
  rw [Polynomial.natDegree_derivative, Qpoly_natDegree]

lemma Qpoly_zero_separable : (X ^ 1024 - X : ℂ[X]).Separable := by
  rw [show (X ^ 1024 - X : ℂ[X]) = X * (X ^ 1023 - 1) by ring]
  refine Polynomial.Separable.mul Polynomial.separable_X
    (Polynomial.X_pow_sub_one_separable_iff.mpr (by norm_num)) ?_
  exact ⟨X ^ 1022, -1, by ring⟩

lemma isCoprime_Qpoly_zero : IsCoprime (Qpoly 0) ((Qpoly 0).derivative) := by
  rw [Qpoly_zero, ← Polynomial.separable_def]
  exact Qpoly_zero_separable

/-! ## The symbolic family in `(c, c̄)` -/

/-- `(X² + C X₁)² + C X₀`, the symbolic version of `TsqPoly c` with `X₀ ↦ c`, `X₁ ↦ c̄`. -/
noncomputable def TsqMvP : Polynomial (MvPolynomial (Fin 2) ℂ) :=
  (Polynomial.X ^ 2 + Polynomial.C (MvPolynomial.X 1)) ^ 2 + Polynomial.C (MvPolynomial.X 0)

/-- The symbolic iterates `(TsqMvP)^{∘n}`. -/
noncomputable def iterMvP : ℕ → Polynomial (MvPolynomial (Fin 2) ℂ)
  | 0 => Polynomial.X
  | n + 1 => (iterMvP n).comp TsqMvP

/-- The symbolic version of `Fpoly`. -/
noncomputable def FpolyMvP : Polynomial (MvPolynomial (Fin 2) ℂ) := iterMvP 5

/-- The symbolic version of `Qpoly`. -/
noncomputable def QpolyMvP : Polynomial (MvPolynomial (Fin 2) ℂ) := FpolyMvP - Polynomial.X

lemma TsqMvP_map (c : ℂ) : TsqMvP.map (MvPolynomial.eval ![c, star c]) = TsqPoly c := by
  rw [show TsqPoly c = (X ^ 2 + C (star c)) ^ 2 + C c from rfl]
  simp [TsqMvP]

lemma iterMvP_map (c : ℂ) (n : ℕ) :
    (iterMvP n).map (MvPolynomial.eval ![c, star c]) = iterPoly c n := by
  induction n with
  | zero => simp [iterMvP, iterPoly]
  | succ n ih => rw [iterMvP, iterPoly, Polynomial.map_comp, ih, TsqMvP_map]

lemma FpolyMvP_map (c : ℂ) :
    FpolyMvP.map (MvPolynomial.eval ![c, star c]) = Fpoly c := iterMvP_map c 5

lemma QpolyMvP_map (c : ℂ) :
    QpolyMvP.map (MvPolynomial.eval ![c, star c]) = Qpoly c := by
  rw [QpolyMvP, Qpoly, Polynomial.map_sub, Polynomial.map_X, FpolyMvP_map]

/-- The symbolic resultant `Res_z(Q_c, Q_c')` as a polynomial in `(c, c̄)`. -/
noncomputable def DMv : MvPolynomial (Fin 2) ℂ :=
  Polynomial.resultant QpolyMvP QpolyMvP.derivative 1024 1023

lemma DMv_apply (c : ℂ) :
    MvPolynomial.eval ![c, star c] DMv
      = Polynomial.resultant (Qpoly c) ((Qpoly c).derivative) 1024 1023 := by
  rw [DMv,
    ← Polynomial.resultant_map_map (MvPolynomial.eval ![c, star c]) (f := QpolyMvP)
      (g := QpolyMvP.derivative) (m := 1024) (n := 1023),
    ← Polynomial.derivative_map, QpolyMvP_map]

/-! ## Analyticity and non-vanishing -/

lemma analyticAt_eval_DMv (z : ℂ) :
    AnalyticAt ℝ (fun c : ℂ => MvPolynomial.eval ![c, star c] DMv) z := by
  have hf : ∀ i : Fin 2, AnalyticAt ℝ (fun x : ℂ => ![x, star x] i) z := by
    intro i
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · simp only [Matrix.cons_val_zero]; exact analyticAt_id
    · have h : (fun x : ℂ => ![x, star x] 1) = fun x => (Complex.conjCLE : ℂ → ℂ) x := by
        funext x; simp
      rw [h]; exact Complex.conjCLE.analyticAt z
  have key := AnalyticAt.aeval_mvPolynomial (𝕜 := ℝ) (A := ℂ) (B := ℂ) (σ := Fin 2)
    (f := fun x : ℂ => ![x, star x]) hf DMv
  simpa [MvPolynomial.aeval_def] using key

lemma analyticOnNhd_eval_DMv :
    AnalyticOnNhd ℝ (fun c : ℂ => MvPolynomial.eval ![c, star c] DMv) Set.univ :=
  fun z _ => analyticAt_eval_DMv z

lemma DMv_zero_ne : MvPolynomial.eval ![0, star 0] DMv ≠ 0 := by
  rw [DMv_apply]
  have h := Polynomial.resultant_ne_zero (Qpoly 0) ((Qpoly 0).derivative) isCoprime_Qpoly_zero
  simpa [Qpoly_natDegree, Qpoly_derivative_natDegree] using h

/-- Near any `c` there is a parameter at which the symbolic resultant does not vanish. -/
lemma exists_eval_DMv_ne_zero (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c' ∈ Metric.ball c ε, MvPolynomial.eval ![c', star c'] DMv ≠ 0 := by
  by_contra h
  have h' : ∀ c' ∈ Metric.ball c ε, MvPolynomial.eval ![c', star c'] DMv = 0 := by
    intro c' hc'
    by_contra hc''
    exact h ⟨c', hc', hc''⟩
  have hev : (fun x : ℂ => MvPolynomial.eval ![x, star x] DMv) =ᶠ[𝓝 c] 0 := by
    filter_upwards [Metric.ball_mem_nhds c hε] with x hx
    exact h' x hx
  have heq := AnalyticOnNhd.eq_of_eventuallyEq analyticOnNhd_eval_DMv
    (analyticOnNhd_const (v := (0 : ℂ))) hev
  have h0 : MvPolynomial.eval ![0, star 0] DMv = 0 := by
    have := congrFun heq 0
    simpa using this
  exact DMv_zero_ne h0

/-! ## Non-vanishing resultant implies no double root -/

lemma not_double_root_of_eval_DMv_ne (c : ℂ)
    (h : MvPolynomial.eval ![c, star c] DMv ≠ 0) :
    ∀ z : ℂ, ¬ ((Qpoly c).eval z = 0 ∧ (Qpoly c).derivative.eval z = 0) := by
  have hres : Polynomial.resultant (Qpoly c) ((Qpoly c).derivative) 1024 1023 ≠ 0 := by
    rwa [← DMv_apply]
  have hcop : IsCoprime (Qpoly c) ((Qpoly c).derivative) := by
    by_contra hc
    have hzero : Polynomial.resultant (Qpoly c) ((Qpoly c).derivative) = 0 := by
      rw [Polynomial.resultant_eq_zero_iff]
      exact ⟨Or.inl (Qpoly_ne_zero c), hc⟩
    exact hres (by
      have hn1 : (Qpoly c).natDegree = 1024 := Qpoly_natDegree c
      have hn2 : ((Qpoly c).derivative).natDegree = 1023 := Qpoly_derivative_natDegree c
      simpa [hn1, hn2] using hzero)
  intro z hz
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : Polynomial.X - Polynomial.C z ∣ (Qpoly c) := Polynomial.dvd_iff_isRoot.mpr hz.1
  have h2 : Polynomial.X - Polynomial.C z ∣ (Qpoly c).derivative :=
    Polynomial.dvd_iff_isRoot.mpr hz.2
  have h3 : Polynomial.X - Polynomial.C z ∣ (1 : ℂ[X]) := by
    rw [← hab]
    exact dvd_add (h1.mul_left a) (h2.mul_left b)
  have hunit : IsUnit (Polynomial.X - Polynomial.C z : ℂ[X]) := isUnit_iff_dvd_one.mpr h3
  have hnu : ¬ IsUnit (Polynomial.X + Polynomial.C (-z)) := Polynomial.not_isUnit_X_add_C (-z)
  have hh : (Polynomial.X - Polynomial.C z : ℂ[X]) = Polynomial.X + Polynomial.C (-z) := by
    rw [sub_eq_add_neg, ← map_neg]
  exact hnu (hh ▸ hunit)

/-! ## The target -/

theorem no_double_root_near (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c' ∈ Metric.ball c ε, ∀ z : ℂ,
      ¬ ((Work.PARIMPL.ParSplit.Qpoly c').eval z = 0 ∧
         (Work.PARIMPL.ParSplit.Qpoly c').derivative.eval z = 0) := by
  obtain ⟨c', hc', hne⟩ := exists_eval_DMv_ne_zero c hε
  exact ⟨c', hc', not_double_root_of_eval_DMv_ne c' hne⟩

end Work.PARIMPL.ParSplit
