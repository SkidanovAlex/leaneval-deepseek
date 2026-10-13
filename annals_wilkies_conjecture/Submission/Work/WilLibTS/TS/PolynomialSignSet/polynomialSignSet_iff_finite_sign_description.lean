import Mathlib
import Submission.Work.WilLibTS.TS.PolynomialSignSetFinite2

namespace Work.WilLibTS.TS.PolynomialSignSet

theorem polynomialSignSet_iff_finite_sign_description {X ι : Type*} {c : X → ι → ℝ} {S : Set X} :
    Work.WilLibTS.TS.PolynomialSignSet c S ↔
      ∃ (s : Finset (MvPolynomial ι ℝ)) (W : (s → SignType) → Prop),
        ∀ x, x ∈ S ↔ W (fun p => SignType.sign (MvPolynomial.eval (c x) p.val)) := by
  classical
  constructor
  · intro hS
    exact PolynomialSignSet.finite_sign_description hS
  · rintro ⟨s, W, hW⟩
    have hA : ∀ σ : s → SignType, PolynomialSignSet c
        {x | ∀ p : s, SignType.sign (MvPolynomial.eval (c x) p.val) = σ p} :=
      fun σ => PolynomialSignSet.forall_finite _
        (fun p => PolynomialSignSet.sign p.val (σ p))
    have hmain : PolynomialSignSet c
        {x | ∃ σ : s → SignType,
          W σ ∧ ∀ p : s, SignType.sign (MvPolynomial.eval (c x) p.val) = σ p} := by
      apply PolynomialSignSet.exists_finite
        (fun σ x => W σ ∧ ∀ p : s,
          SignType.sign (MvPolynomial.eval (c x) p.val) = σ p)
      intro σ
      by_cases h : W σ
      · convert hA σ using 1
        ext x; simp [h]
      · convert PolynomialSignSet.empty using 1
        ext x; simp [h]
    convert hmain using 1
    ext x
    rw [hW x]
    constructor
    · intro hWx
      exact ⟨fun p => SignType.sign (MvPolynomial.eval (c x) p.val), hWx, fun _ => rfl⟩
    · rintro ⟨σ, hσ, hσx⟩
      have hf : (fun p : s => SignType.sign (MvPolynomial.eval (c x) p.val)) = σ :=
        funext hσx
      rwa [hf]

end Work.WilLibTS.TS.PolynomialSignSet
