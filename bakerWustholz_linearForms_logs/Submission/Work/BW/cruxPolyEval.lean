import Mathlib
import Submission.Work.BW.stabAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `cruxPolyEval`: the crux polynomial really represents `x ↦ μ (τ_x F)`

`cruxPoly F μ` is the polynomial (in the `N+1` group coordinates `Y₀,…,Y_N`) whose
coefficients are the `μ`-images of the coefficients of the universal substitution
`translFam F : GPoly N = MvPolynomial (Fin (N+1)) (MR N)`, and whose monomials are those
coefficients' supports.  The point of the construction is the identity

  `eval x (cruxPoly F μ) = μ (transl x F)`,

i.e. evaluating the polynomial at the point `x` of `G = G_a × G_m^N` recovers the
functional `μ` applied to the translated polynomial `transl x F`.

The proof factors the right hand side through the *same* substitution evaluated in `MR N`:
the `ℂ`-algebra hom `evx x : GPoly N →ₐ[ℂ] MR N` substitutes the group coordinates by
`C (x i)`.  It sends `translFam F = aeval gCoord F` to `transl x F` (the variable
substitutions `gCoord` and `uT x` defining `transl` match), and coefficientwise reading off
`μ` commutes with `evx x` because `μ` is `ℂ`-linear.
-/

namespace Work.BW

/-- The `ℂ`-algebra hom `GPoly N →ₐ[ℂ] MR N` specialising the group coordinates at the point
`x : Fin (N+1) → ℂ`: it is the identity on coefficients (`C c ↦ c`) and sends the coordinate
variable `Y_i` to the constant `C (x i)`. -/
private noncomputable def evx {N : ℕ} (x : Fin (N + 1) → ℂ) : GPoly N →ₐ[ℂ] MR N :=
  MvPolynomial.aevalTower (AlgHom.id ℂ (MR N)) (fun i => (MvPolynomial.C (x i) : MR N))

private lemma evx_C {N : ℕ} (x : Fin (N + 1) → ℂ) (c : MR N) :
    evx x (MvPolynomial.C c) = c := by
  simp [evx, MvPolynomial.aevalTower_C]

private lemma evx_X {N : ℕ} (x : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    evx x (MvPolynomial.X i : GPoly N) = (MvPolynomial.C (x i) : MR N) := by
  simp [evx, MvPolynomial.aevalTower_X]

/-- The variable substitution defining `transl x`, restated as a named function so that
`transl x = MvPolynomial.aeval (uT x)` holds by definitional equality. -/
private noncomputable def uT {N : ℕ} (g : Fin (N + 1) → ℂ) : Fin (N + 1) × Fin 2 → MR N :=
  fun v => if v.2 = 0 then MvPolynomial.X v
    else if v.1 = 0 then MvPolynomial.X v + MvPolynomial.C (g 0) * MvPolynomial.X (0, 0)
    else MvPolynomial.C (g v.1) * MvPolynomial.X v

private lemma transl_eq_aeval_uT {N : ℕ} (g : Fin (N + 1) → ℂ) :
    transl g = MvPolynomial.aeval (uT g) := rfl

/-- Unfolding `Finsupp.prod`. -/
private lemma finsupp_prod_eq {α M N : Type*} [Zero M] [CommMonoid N] (s : α →₀ M)
    (g : α → M → N) : s.prod g = ∏ i ∈ s.support, g i (s i) := rfl

/-- Substituting the group coordinates into `gCoord v` gives the substitution `uT x v` defining
`transl x`.  This is the pointwise compatibility of the two variable substitutions. -/
private lemma evx_gCoord {N : ℕ} (x : Fin (N + 1) → ℂ) (v : Fin (N + 1) × Fin 2) :
    evx x (gCoord v) = uT x v := by
  obtain ⟨i, b⟩ := v
  fin_cases b
  · simp [gCoord, uT, evx]
  · obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
    · simp [gCoord, uT, evx]
      try ring
    · simp [gCoord, uT, evx]
      try ring

/-- `evx x` on a monomial: the coefficient is untouched, the monomial is evaluated at `x`. -/
private lemma evx_monomial {N : ℕ} (x : Fin (N + 1) → ℂ) (v : Fin (N + 1) →₀ ℕ) (c : MR N) :
    evx x (MvPolynomial.monomial v c) =
      c * (MvPolynomial.C (v.prod (fun i k => x i ^ k)) : MR N) := by
  rw [MvPolynomial.monomial_eq, map_mul, evx_C]
  congr 1
  rw [finsupp_prod_eq, finsupp_prod_eq,
      map_prod (evx x) (fun i => (MvPolynomial.X i : GPoly N) ^ v i) v.support]
  rw [show (∏ i ∈ v.support, evx x ((MvPolynomial.X i : GPoly N) ^ v i))
        = ∏ i ∈ v.support, (MvPolynomial.C (x i ^ v i) : MR N) from
      Finset.prod_congr rfl (fun i _ => by rw [map_pow, evx_X, ← MvPolynomial.C_pow])]
  exact (map_prod (MvPolynomial.C : ℂ →+* MR N) (fun i => x i ^ v i) v.support).symm

/-- Evaluating the monomial `∏ Y_i^{v_i}` at the point `x`. -/
private lemma eval_prod_X {N : ℕ} (x : Fin (N + 1) → ℂ) (v : Fin (N + 1) →₀ ℕ) :
    MvPolynomial.eval x (v.prod (fun i k => (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) ^ k))
      = v.prod (fun i k => x i ^ k) := by
  have h : v.prod (fun i k => (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) ^ k)
      = MvPolynomial.monomial v (1 : ℂ) := by
    rw [MvPolynomial.monomial_eq]; simp
  rw [h, MvPolynomial.eval_monomial]; simp

/-- The key termwise identity: reading off `μ` from the coefficient of a monomial and
substituting the coordinates at `x` commutes with first substituting `Y_i ↦ C (x i)`
inside `MR N`. -/
private lemma mu_evx_monomial {N : ℕ} (μ : MR N →ₗ[ℂ] ℂ) (x : Fin (N + 1) → ℂ)
    (v : Fin (N + 1) →₀ ℕ) (c : MR N) :
    μ (evx x (MvPolynomial.monomial v c)) =
      MvPolynomial.eval x
        (MvPolynomial.C (μ c) *
          v.prod (fun i e => (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) ^ e)) := by
  rw [evx_monomial, map_mul (MvPolynomial.eval x), MvPolynomial.eval_C, eval_prod_X]
  rw [show c * (MvPolynomial.C (v.prod (fun i k => x i ^ k)) : MR N)
        = (v.prod (fun i k => x i ^ k)) • c from by
      rw [mul_comm, Algebra.smul_def, MvPolynomial.C_eq_algebraMap]]
  rw [map_smul, smul_eq_mul]
  exact mul_comm _ _

/-- The polynomial reading off `μ` from the coefficients of `G : GPoly N`
(`cruxPoly F μ = cruxGPoly (translFam F) μ`). -/
private noncomputable def cruxGPoly {N : ℕ} (G : GPoly N) (μ : MR N →ₗ[ℂ] ℂ) :
    MvPolynomial (Fin (N + 1)) ℂ :=
  ∑ s ∈ G.support,
    MvPolynomial.C (μ (G.coeff s)) *
      s.prod (fun i e => (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) ℂ) ^ e)

/-- `μ (evx x G)` is obtained by evaluating `cruxGPoly G μ` at `x`. -/
private lemma mu_evx_eq_eval_crux {N : ℕ} (μ : MR N →ₗ[ℂ] ℂ) (x : Fin (N + 1) → ℂ)
    (G : GPoly N) : μ (evx x G) = MvPolynomial.eval x (cruxGPoly G μ) := by
  simp only [cruxGPoly]
  conv_lhs => rw [G.as_sum]
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun s _ => mu_evx_monomial μ x s (G.coeff s))

/-- `evx x` turned `translFam F` into `transl x F`. -/
private lemma evx_translFam {N : ℕ} (F : MR N) (x : Fin (N + 1) → ℂ) :
    evx x (translFam F) = transl x F := by
  have h := MvPolynomial.comp_aeval_apply (f := gCoord) (φ := evx x) (p := F)
  rw [show translFam F = MvPolynomial.aeval gCoord F from rfl, h]
  rw [show (fun i => evx x (gCoord i)) = uT x from funext (evx_gCoord x)]
  rw [transl_eq_aeval_uT x]

theorem cruxPolyEval {N : ℕ} (F : MR N) (μ : MR N →ₗ[ℂ] ℂ) (x : Fin (N + 1) → ℂ) :
    MvPolynomial.eval x (cruxPoly F μ) = μ (transl x F) := by
  rw [← evx_translFam F x]
  exact (mu_evx_eq_eval_crux μ x (translFam F)).symm

end Work.BW
