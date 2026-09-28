import Mathlib
import Submission.Work.HP.MDEstimates.QuadAuxDefs

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section
open MvPolynomial

namespace Work.HP.MDEstimates

/-!
# Polarisation facts for a homogeneous quadratic form in five variables

For `Q : MvPolynomial (Fin 5) ℚ` homogeneous of degree `2`, the polar form

`polQ Q x y = (Q(x+y) - Q(x) - Q(y)) / 2`

is a symmetric bilinear form satisfying `polQ Q x x = Q x`; the evaluation map `x ↦ Q x` is
homogeneous of degree `2` under rescaling `x ↦ c • x`; and the polarisation identity
`Q(x+y) = Q(x) + Q(y) + 2 * polQ Q x y` holds by construction.

The substance is the first four items.  Since the products `X i * X j` of two linear forms span the
degree-`2` part of the homogeneous submodule of `MvPolynomial (Fin 5) ℚ`, it suffices to check the
conclusions on `0` and on these generators and to observe that the relevant predicate is closed
under addition and scalar multiplication.  Then the last two items follow by algebra.
-/

/-! ## The polar form on generators -/

private lemma polQ_add (Q₁ Q₂ : MvPolynomial (Fin 5) ℚ) (x y : Fin 5 → ℚ) :
    polQ (Q₁ + Q₂) x y = polQ Q₁ x y + polQ Q₂ x y := by
  simp only [polQ, map_add]
  ring

private lemma polQ_smul (c : ℚ) (Q : MvPolynomial (Fin 5) ℚ) (x y : Fin 5 → ℚ) :
    polQ (c • Q) x y = c * polQ Q x y := by
  simp only [polQ, smul_eq_C_mul, map_mul, eval_C]
  ring

private lemma polQ_X_mul_X (i j : Fin 5) (a b : Fin 5 → ℚ) :
    polQ (X i * X j) a b = (a i * b j + b i * a j) / 2 := by
  simp only [polQ, eval_mul, eval_X, Pi.add_apply]
  ring

/-! ## The predicate and its closure properties -/

/-- `Good Q` bundles the four bilinearity/polarisation conclusions for the binary form
`polQ Q`. -/
private def Good (Q : MvPolynomial (Fin 5) ℚ) : Prop :=
  (∀ x x' y, polQ Q (x + x') y = polQ Q x y + polQ Q x' y) ∧
  (∀ (c : ℚ) x y, polQ Q (c • x) y = c * polQ Q x y) ∧
  (∀ x y, polQ Q x y = polQ Q y x) ∧
  (∀ x, polQ Q x x = MvPolynomial.eval x Q)

private lemma good_zero : Good 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y; simp [polQ]
  · intro c x y; simp [polQ]
  · intro x y; simp [polQ]
  · intro x; simp [polQ]

private lemma good_add : ∀ Q₁ Q₂, Good Q₁ → Good Q₂ → Good (Q₁ + Q₂) := by
  intro Q₁ Q₂ h₁ h₂
  obtain ⟨a1, a2, a3, a4⟩ := h₁
  obtain ⟨b1, b2, b3, b4⟩ := h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y
    simp only [polQ_add]
    rw [a1 x x' y, b1 x x' y]
    ring
  · intro c x y
    simp only [polQ_add]
    rw [a2 c x y, b2 c x y]
    ring
  · intro x y
    simp only [polQ_add]
    rw [a3 x y, b3 x y]
  · intro x
    simp only [polQ_add]
    rw [a4 x, b4 x, map_add]

private lemma good_smul : ∀ (c : ℚ) Q, Good Q → Good (c • Q) := by
  intro c Q h
  obtain ⟨a1, a2, a3, a4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y
    simp only [polQ_smul]
    rw [a1 x x' y]
    ring
  · intro d x y
    simp only [polQ_smul]
    rw [a2 d x y]
    ring
  · intro x y
    simp only [polQ_smul]
    rw [a3 x y]
  · intro x
    simp only [polQ_smul]
    rw [a4 x, smul_eq_C_mul, map_mul, eval_C]

private lemma good_gen : ∀ p : Fin 5 × Fin 5, Good (X p.1 * X p.2) := by
  intro p
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y
    simp only [polQ_X_mul_X, Pi.add_apply]
    ring
  · intro c x y
    simp only [polQ_X_mul_X, Pi.smul_apply, smul_eq_mul]
    ring
  · intro x y
    simp only [polQ_X_mul_X]
    ring
  · intro x
    simp only [polQ_X_mul_X, eval_mul, eval_X]
    ring

/-! ## The span reduction -/

/-- Products of two linear forms span the homogeneous polynomials of degree `2` in five
variables. -/
private lemma homogeneousSubmodule_two_eq_span_X_mul_X :
    MvPolynomial.homogeneousSubmodule (Fin 5) ℚ 2
      = Submodule.span ℚ (Set.range fun p : Fin 5 × Fin 5 =>
          (X p.1 * X p.2 : MvPolynomial (Fin 5) ℚ)) := by
  rw [← MvPolynomial.homogeneousSubmodule_one_pow (σ := Fin 5) ℚ 2,
    MvPolynomial.homogeneousSubmodule_one_eq_span_X, pow_two, Submodule.span_mul_span]
  congr 1
  ext z
  rw [Set.mem_mul]
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
    exact ⟨(i, j), rfl⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨X i, ⟨i, rfl⟩, X j, ⟨j, rfl⟩, rfl⟩

/-- **Polarisation.**  A homogeneous polynomial of degree `2` in five variables over `ℚ` has a
symmetric bilinear polar form whose associated quadratic form is `Q` itself. -/
private lemma polQ_bilin (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) :
    (∀ x x' y : Fin 5 → ℚ, polQ Q (x + x') y = polQ Q x y + polQ Q x' y) ∧
    (∀ (c : ℚ) (x y : Fin 5 → ℚ), polQ Q (c • x) y = c * polQ Q x y) ∧
    (∀ x y : Fin 5 → ℚ, polQ Q x y = polQ Q y x) ∧
    (∀ x : Fin 5 → ℚ, polQ Q x x = MvPolynomial.eval x Q) := by
  have hgood : Good Q := by
    have hQmem : Q ∈ MvPolynomial.homogeneousSubmodule (Fin 5) ℚ 2 :=
      (MvPolynomial.mem_homogeneousSubmodule 2 Q).mpr hQ
    rw [homogeneousSubmodule_two_eq_span_X_mul_X] at hQmem
    refine Submodule.span_induction (p := fun Q _ => Good Q) (fun z hz => ?_) good_zero
      (fun a b _ _ ha hb => good_add a b ha hb) (fun c a _ ha => good_smul c a ha) hQmem
    obtain ⟨p, rfl⟩ := hz
    exact good_gen p
  exact hgood

/-! ## The packaged statement -/

theorem polarQuadFacts (Q : MvPolynomial (Fin 5) ℚ) (hQ : Q.IsHomogeneous 2) :
    (∀ x y z : Fin 5 → ℚ, polQ Q (x + y) z = polQ Q x z + polQ Q y z) ∧
    (∀ (c : ℚ) (x y : Fin 5 → ℚ), polQ Q (c • x) y = c * polQ Q x y) ∧
    (∀ x y : Fin 5 → ℚ, polQ Q x y = polQ Q y x) ∧
    (∀ x : Fin 5 → ℚ, polQ Q x x = MvPolynomial.eval x Q) ∧
    (∀ (c : ℚ) (x : Fin 5 → ℚ), MvPolynomial.eval (c • x) Q = c ^ 2 * MvPolynomial.eval x Q) ∧
    (∀ x y : Fin 5 → ℚ,
      MvPolynomial.eval (x + y) Q = MvPolynomial.eval x Q + MvPolynomial.eval y Q + 2 * polQ Q x y) := by
  obtain ⟨h1, h2, h3, h4⟩ := polQ_bilin Q hQ
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · -- `eval` is homogeneous of degree `2`: `Q (c x) = c^2 Q x`
    intro c x
    calc MvPolynomial.eval (c • x) Q = polQ Q (c • x) (c • x) := (h4 (c • x)).symm
      _ = c * polQ Q x (c • x) := h2 c x (c • x)
      _ = c * polQ Q (c • x) x := by rw [h3 x (c • x)]
      _ = c * (c * polQ Q x x) := by rw [h2 c x x]
      _ = c ^ 2 * MvPolynomial.eval x Q := by rw [h4 x]; ring
  · -- the defining polarisation identity
    intro x y
    simp only [polQ]
    ring

end Work.HP.MDEstimates
