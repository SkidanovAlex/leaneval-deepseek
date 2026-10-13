import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.sphAux

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: **the identification of the radial minor
  `pertMinor3` with `(G · μ) · shfun`**.

  The module proves, for `x` in the open set `Uset = {μ ≠ 0}`,

  ```
  eaEval c (pertMinor3 c Φ v y i₀ j₀ l) x
      = (Gq c Φ x * muq c Φ y i₀ j₀ x) * shfun c Φ y i₀ j₀ l v x
  ```

  where `Gq = |∇Φ|²` and `muq = ∂_{i₀}Φ (x_{j₀} - y_{j₀}) - ∂_{j₀}Φ (x_{i₀} - y_{i₀})`.

  This is the *value* form of the relation recorded in `sphAux.lean`'s docstring: the `3 × 3` minor
  of the rows `(∇G + G v, ∇Φ, x - y)` is `G · μ` times the radial shear form
  `shAₗ + vₗ + shB1ₗ v_{i₀} + shB2ₗ v_{j₀}`, whose vanishing is therefore equivalent to
  `pertMinor3` vanishing on `Uset`.

  The mathematical content is the following completely explicit computation.  Abbreviating
  `Uᵢ = ∂ᵢG + G vᵢ`, `Wᵢ = ∂ᵢΦ`, `Tᵢ = xᵢ - yᵢ`, the left hand side is the Laplace expansion

  ```
  U_{i₀}(W_{j₀}Tₗ - WₗT_{j₀}) - U_{j₀}(W_{i₀}Tₗ - WₗT_{i₀}) + Uₗ(W_{i₀}T_{j₀} - W_{j₀}T_{i₀}),
  ```

  and pulling out the `G vᵢ` parts turns the added terms into exactly `G` times the numerator
  `vₗ μ + v_{i₀}(W_{j₀}Tₗ - WₗT_{j₀}) - v_{j₀}(W_{i₀}Tₗ - WₗT_{i₀})` of the shear form.  All the
  divisions in `shfun` are by `G · μ`, which is non-zero on `Uset`: `μ ≠ 0` forces one of
  `∂_{i₀}Φ`, `∂_{j₀}Φ` to be non-zero, hence `G = ∑ᵢ (∂ᵢΦ)² > 0`.

  The algebraic identity is proved once, in an abstract field (`shfun_core`), and instantiated.
-/

set_option autoImplicit false
noncomputable section

namespace Work.WilE3.Taylor.CaseII

open WilkiesDesign.E

/-- The Laplace expansion of the evaluation of `pertMinor3` in terms of the evaluations of the
individual entries.  (This is `Work.WilE3.Taylor.CaseII.eaEval_pertMinor3` of `badArcAux.lean`;
it is reproved here so that this module depends only on `sphAux`.) -/
private lemma eaEval_pertMinor3_expand {k r : ℕ} (c : EAChain k r) (Φ : EAPoly k r)
    (v y : Fin k → ℝ) (i₀ j₀ l : Fin k) (x : Fin k → ℝ) :
    eaEval c (pertMinor3 c Φ v y i₀ j₀ l) x =
      (eaEval c (eaD c i₀ (sqGrad c Φ)) x + v i₀ * eaEval c (sqGrad c Φ) x)
        * (eaEval c (eaD c j₀ Φ) x * (x l - y l) - eaEval c (eaD c l Φ) x * (x j₀ - y j₀))
      - (eaEval c (eaD c j₀ (sqGrad c Φ)) x + v j₀ * eaEval c (sqGrad c Φ) x)
        * (eaEval c (eaD c i₀ Φ) x * (x l - y l) - eaEval c (eaD c l Φ) x * (x i₀ - y i₀))
      + (eaEval c (eaD c l (sqGrad c Φ)) x + v l * eaEval c (sqGrad c Φ) x)
        * (eaEval c (eaD c i₀ Φ) x * (x j₀ - y j₀) - eaEval c (eaD c j₀ Φ) x * (x i₀ - y i₀)) := by
  simp only [pertMinor3, eaEval, map_sub, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Sum.elim_inl]

/-- The algebraic identity underlying the theorem, in an arbitrary field: with
`μ = w₀t₁ - w₁t₀` and `G ≠ 0`, `μ ≠ 0`, the Laplace expansion of the `3 × 3` minor equals
`G · μ` times the shear form. -/
private lemma shfun_core {K : Type*} [Field K] (a0 a1 a2 w0 w1 w2 t0 t1 t2 G v0 v1 v2 : K)
    (hG : G ≠ 0) (hμ : w0 * t1 - w1 * t0 ≠ 0) :
    (a0 + v0 * G) * (w1 * t2 - w2 * t1) - (a1 + v1 * G) * (w0 * t2 - w2 * t0)
      + (a2 + v2 * G) * (w0 * t1 - w1 * t0)
    = (G * (w0 * t1 - w1 * t0)) *
      ( (a0 * (w1 * t2 - w2 * t1) - a1 * (w0 * t2 - w2 * t0) + a2 * (w0 * t1 - w1 * t0))
          / (G * (w0 * t1 - w1 * t0))
        + v2 + ((w1 * t2 - w2 * t1) / (w0 * t1 - w1 * t0)) * v0
        + (-((w0 * t2 - w2 * t0) / (w0 * t1 - w1 * t0))) * v1 ) := by
  have hGμ : G * (w0 * t1 - w1 * t0) ≠ 0 := mul_ne_zero hG hμ
  have hμ2 : t1 * w0 - w1 * t0 ≠ 0 := by
    rw [show t1 * w0 - w1 * t0 = w0 * t1 - w1 * t0 by ring]
    exact hμ
  field_simp
  ring

theorem eaEval_pertMinor3_eq_smul_shfun {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ) (v : Fin k → ℝ) (i₀ j₀ l : Fin k)
    {x : Fin k → ℝ} (hx : x ∈ Work.WilE3.Taylor.CaseII.Uset c Φ y i₀ j₀) :
    WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.CaseII.pertMinor3 c Φ v y i₀ j₀ l) x =
      (Work.WilE3.Taylor.CaseII.Gq c Φ x * Work.WilE3.Taylor.CaseII.muq c Φ y i₀ j₀ x)
        * Work.WilE3.Taylor.CaseII.shfun c Φ y i₀ j₀ l v x := by
  -- `μ ≠ 0` at `x`, in unfolded form.
  have hμ' : eaEval c (eaD c i₀ Φ) x * (x j₀ - y j₀) - eaEval c (eaD c j₀ Φ) x * (x i₀ - y i₀) ≠ 0 :=
    hx
  -- `μ ≠ 0` forces `∂_{i₀}Φ ≠ 0` or `∂_{j₀}Φ ≠ 0`, hence `G = ∑ᵢ (∂ᵢΦ)² ≠ 0`.
  have hG' : eaEval c (sqGrad c Φ) x ≠ 0 := by
    intro h0
    have hsum : ∑ m : Fin k, (eaEval c (eaD c m Φ) x) ^ 2 = 0 := by
      rw [← eaEval_sqGrad c Φ x]
      exact h0
    have hterm : ∀ m : Fin k, eaEval c (eaD c m Φ) x = 0 := by
      intro m
      have h := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun m : Fin k => (eaEval c (eaD c m Φ) x) ^ 2) (fun m _ => sq_nonneg _)).mp hsum
      exact sq_eq_zero_iff.mp (h m (Finset.mem_univ m))
    exact hμ' (by rw [hterm i₀, hterm j₀]; ring)
  rw [eaEval_pertMinor3_expand]
  simp only [Gq, muq, Wq, dGq, Tq, shfun, shA, shB1, shB2]
  exact shfun_core _ _ _ _ _ _ _ _ _ _ _ _ _ hG' hμ'

end Work.WilE3.Taylor.CaseII
