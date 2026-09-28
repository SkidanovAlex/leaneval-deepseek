import Mathlib
import Submission.Work.HP.GonLib
import Submission.Work.HP.FM.RecDefs
import Submission.Work.HP.Sig2.LatStepDefs
import Submission.Work.HP.Sig2.gram_det_cons_smul
import Submission.Work.HP.Sig2.bfam_bijective
import Submission.Work.EEupper.det_gram_unimodular

/-!
# The one-step covolume identity for `Work.HP.FM.latStep`

Given a presentation `Φ` of a rank-`R` lattice, a family `(u, v₀, …, v_{R-2})` of integer
coefficient vectors which is a `ℤ`-basis of `ℤ^R` (witnessed by the bijectivity of
`c ↦ c.1 • u + ∑ i, c.2 i • v i`), the covolume of `Φ` factors as the norm of the image of `u`
times the covolume of the projected presentation `latStep Φ u v`:

`latCovol Φ = ‖Φ u‖ * latCovol (latStep Φ u v)`.

No injectivity of `Φ` is assumed: the identity is the Gram-determinant identity
`det G(Φ) = ‖Φ u‖² * det G(projU (Φ u) ∘ Φ v)`, which holds even when `Φ` is singular
(then both sides vanish).
-/

set_option autoImplicit false

noncomputable section

open Finset Matrix
open scoped BigOperators

namespace Work.EEupper

open Work.HP.Sig2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `latStep Φ u v` evaluated on a standard basis vector is the orthogonal projection of
`Φ (v i)` onto `(Φ u)^⊥`. -/
lemma latStep_basisFun {R : ℕ} (Φ : Work.HP.LatMap (ι := ι) R) (u : Fin R → ℤ)
    (v : Fin (R - 1) → (Fin R → ℤ)) (i : Fin (R - 1)) :
    Work.HP.FM.latStep Φ u v (Pi.basisFun ℝ (Fin (R - 1)) i)
      = Work.HP.projU (Φ (fun k => (u k : ℝ))) (Φ (fun k => (v i k : ℝ))) := by
  rw [Work.HP.FM.latStep_apply, Pi.basisFun_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The Gram matrix of `latStep Φ u v` in the standard basis is the Gram matrix of the
projections of the `Φ (v i)` onto `(Φ u)^⊥`. -/
lemma gram_latStep {R : ℕ} (Φ : Work.HP.LatMap (ι := ι) R) (u : Fin R → ℤ)
    (v : Fin (R - 1) → (Fin R → ℤ)) :
    Matrix.gram ℝ (fun i : Fin (R - 1) =>
        Work.HP.FM.latStep Φ u v (Pi.basisFun ℝ (Fin (R - 1)) i))
      = Matrix.gram ℝ (fun i : Fin (R - 1) =>
          Work.HP.projU (Φ (fun k => (u k : ℝ))) (Φ (fun k => (v i k : ℝ)))) := by
  ext i j
  rw [Matrix.gram_apply, Matrix.gram_apply, latStep_basisFun, latStep_basisFun]

/-- The Gram matrix of the `Fin R`-indexed family `bfamR hR u v` is the Gram matrix of the
`Fin 1 ⊕ Fin (R-1)`-indexed family `famR u v`, reindexed along `idxEquiv`. -/
lemma gram_bfamR_submatrix {R : ℕ} (hR : 1 ≤ R) (u : Fin R → ℤ)
    (v : Fin (R - 1) → (Fin R → ℤ)) (Φ : Work.HP.LatMap (ι := ι) R) :
    Matrix.gram ℝ (fun j : Fin R => Φ (bfamR hR u v j))
      = (Matrix.gram ℝ (fun c : Fin 1 ⊕ Fin (R - 1) => Φ (famR u v c))).submatrix
          (idxEquiv R hR).symm (idxEquiv R hR).symm := by
  have hbf : ∀ i : Fin R, bfamR hR u v i = famR u v ((idxEquiv R hR).symm i) := fun i => rfl
  ext i j
  simp only [submatrix_apply, gram_apply, hbf]

theorem latCovolStep {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ}
    (Φ : Work.HP.LatMap (ι := ι) R) (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ))
    (hbij : Function.Bijective (fun c : ℤ × (Fin (R - 1) → ℤ) => c.1 • u + ∑ i, c.2 i • v i)) :
    Work.HP.latCovol Φ
      = ‖Φ (fun k => (u k : ℝ))‖ * Work.HP.latCovol (Work.HP.FM.latStep Φ u v) := by
  classical
  rcases Nat.eq_zero_or_pos R with hR0 | hR
  · -- `R = 0`: the hypothesis `hbij` is absurd
    subst hR0
    exfalso
    have h1 : (fun c : ℤ × (Fin (0 - 1) → ℤ) => c.1 • u + ∑ i, c.2 i • v i) (0, 0)
        = (fun c : ℤ × (Fin (0 - 1) → ℤ) => c.1 • u + ∑ i, c.2 i • v i) (1, 0) :=
      Subsingleton.elim _ _
    have h2 : ((0 : ℤ), (0 : Fin (0 - 1) → ℤ)) = (1, 0) := hbij.injective h1
    exact absurd (congrArg Prod.fst h2) (by norm_num)
  · -- main case
    set x : EuclideanSpace ℝ ι := Φ (fun k => (u k : ℝ)) with hx
    have hgram : (Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))).det
        = (Matrix.gram ℝ (fun j : Fin R => Φ (bfamR hR u v j))).det :=
      det_gram_unimodular Φ (bfam hR u v) (bfam_bijective hR u v hbij)
    by_cases hx0 : x = 0
    · -- degenerate case: `Φ u = 0`
      rw [hx0, norm_zero, zero_mul]
      have hzero : (Matrix.gram ℝ (fun j : Fin R => Φ (bfamR hR u v j))).det = 0 := by
        refine Matrix.det_eq_zero_of_row_eq_zero (idxEquiv R hR (Sum.inl 0)) (fun j => ?_)
        rw [Matrix.gram_apply]
        have hbf : bfamR hR u v (idxEquiv R hR (Sum.inl 0)) = (fun k => (u k : ℝ)) := by
          funext k
          simp [bfamR, bfam]
        rw [hbf, ← hx, hx0, inner_zero_left]
      rw [show Work.HP.latCovol Φ
            = Real.sqrt ((Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))).det)
            from rfl,
          hgram, hzero, Real.sqrt_zero]
    · -- main case: `Φ u ≠ 0`
      have hschur := gram_det_cons_smul x hx0
        (fun i : Fin (R - 1) => Φ (fun k => (v i k : ℝ)))
      have hfam : Matrix.gram ℝ (fun c : Fin 1 ⊕ Fin (R - 1) => Φ (famR u v c))
          = Matrix.gram ℝ (Sum.elim (fun _ : Fin 1 => x)
              (fun i : Fin (R - 1) => Φ (fun k => (v i k : ℝ)))) := by
        congr 1
        funext c
        rcases c with i | i
        · simp only [famR_inl, Sum.elim_inl, hx]
        · simp only [famR_inr, Sum.elim_inr]
      have hproj : Work.HP.latCovol (Work.HP.FM.latStep Φ u v)
          = Real.sqrt ((Matrix.gram ℝ (fun i : Fin (R - 1) =>
              Work.HP.projU x (Φ (fun k => (v i k : ℝ))))).det) := by
        rw [show Work.HP.latCovol (Work.HP.FM.latStep Φ u v)
              = Real.sqrt ((Matrix.gram ℝ (fun i : Fin (R - 1) =>
                  Work.HP.FM.latStep Φ u v (Pi.basisFun ℝ (Fin (R - 1)) i))).det) from rfl,
            gram_latStep]
      calc Work.HP.latCovol Φ
          = Real.sqrt ((Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))).det) :=
            rfl
        _ = Real.sqrt ((Matrix.gram ℝ (fun j : Fin R => Φ (bfamR hR u v j))).det) := by
            rw [hgram]
        _ = Real.sqrt ((Matrix.gram ℝ (fun c : Fin 1 ⊕ Fin (R - 1) => Φ (famR u v c))).det) := by
            rw [gram_bfamR_submatrix hR u v Φ,
              Matrix.det_submatrix_equiv_self (idxEquiv R hR).symm
                (Matrix.gram ℝ (fun c : Fin 1 ⊕ Fin (R - 1) => Φ (famR u v c)))]
        _ = Real.sqrt ((Matrix.gram ℝ (Sum.elim (fun _ : Fin 1 => x)
              (fun i : Fin (R - 1) => Φ (fun k => (v i k : ℝ))))).det) := by
            rw [hfam]
        _ = Real.sqrt (‖x‖ ^ 2 * (Matrix.gram ℝ (fun i : Fin (R - 1) =>
              Work.HP.projU x (Φ (fun k => (v i k : ℝ))))).det) := by
            rw [hschur]
        _ = ‖x‖ * Real.sqrt ((Matrix.gram ℝ (fun i : Fin (R - 1) =>
              Work.HP.projU x (Φ (fun k => (v i k : ℝ))))).det) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
        _ = ‖x‖ * Work.HP.latCovol (Work.HP.FM.latStep Φ u v) := by
            rw [hproj]

end Work.EEupper
