import Mathlib
import Submission.Work.HP.GonLib
import Submission.Work.HP.FM.RecDefs
import Submission.Work.HP.Sig2.LatStepDefs
import Submission.Work.HP.Sig2.gram_det_cons_smul
import Submission.Work.HP.Sig2.bfam_bijective
import Submission.Work.HP.Sig2.det_gram_of_int_basis

/-!
# Covolume of one step of the lattice recursion

For an injective presentation `Φ : (Fin R → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι` of a rank-`R` lattice, a
primitive vector `u ∈ ℤ^R` and a complementary family `v : Fin (R-1) → (Fin R → ℤ)` such that
`(a, w) ↦ a • u + ∑ i, w i • v i` is a bijection `ℤ × ℤ^(R-1) → ℤ^R`, the covolume of `Φ` is the
product of `‖Φ u‖` with the covolume of the projected presentation
`latStep Φ u v` (the orthogonal projections of the `Φ (v i)` onto `(Φ u)^⊥`, see
`Work.HP.FM.RecDefs`).

All quantities are Gram determinants:

* `latCovol Φ = √det G(Φ)` with `G(Φ) i j = ⟪Φ eᵢ, Φ eⱼ⟫`;
* the family `(u, v₀, …, v_{R-2})` is a `ℤ`-basis of `ℤ^R`, so the Gram determinant of
  `i ↦ Φ (eᵢ)` equals the one of `c ↦ Φ (b_c)` where `b = (u, v₀, …, v_{R-2})`
  (`Work.HP.Sig2.det_gram_of_int_basis`, using that the change-of-basis matrix is unimodular);
* the Gram matrix of `(Φ u, Φ v₀, …)`, viewed in the block form
  `[[‖Φ u‖², cᵀ], [c, G]]`, has determinant `‖Φ u‖² · det(G - c cᵀ/‖Φ u‖²)` (Schur complement,
  `Work.HP.Sig2.gram_det_cons_smul`), and the Schur complement is exactly the Gram matrix of the
  projections `projU (Φ u) (Φ vᵢ)`.
-/

set_option autoImplicit false

noncomputable section

open Finset Matrix
open scoped BigOperators

namespace Work.HP.Sig2

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ}

/-- `latStep` evaluated at a standard basis vector is the orthogonal projection of `Φ (v i)`
onto `(Φ u)^⊥`. -/
lemma latStep_basisFun (Φ : Work.HP.LatMap (ι := ι) R) (u : Fin R → ℤ)
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

/-- The Gram matrix of `latStep Φ u v` in the standard basis. -/
lemma gram_latStep (Φ : Work.HP.LatMap (ι := ι) R) (u : Fin R → ℤ)
    (v : Fin (R - 1) → (Fin R → ℤ)) :
    Matrix.gram ℝ (fun i : Fin (R - 1) =>
        Work.HP.FM.latStep Φ u v (Pi.basisFun ℝ (Fin (R - 1)) i))
      = Matrix.gram ℝ (fun i : Fin (R - 1) =>
          Work.HP.projU (Φ (fun k => (u k : ℝ))) (Φ (fun k => (v i k : ℝ)))) := by
  ext i j
  rw [Matrix.gram_apply, Matrix.gram_apply, latStep_basisFun, latStep_basisFun]

/-- The `Fin R`-indexed family `bfam hR u v` realified, written through `famR`. -/
lemma bfamR_apply (hR : 1 ≤ R) (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ))
    (i : Fin R) :
    bfamR hR u v i = famR u v ((idxEquiv R hR).symm i) := rfl

/-- Reindexing the Gram matrix of `famR` along `idxEquiv` gives the Gram matrix of `bfamR`. -/
lemma gram_bfamR_submatrix (hR : 1 ≤ R) (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ))
    (Φ : Work.HP.LatMap (ι := ι) R) :
    Matrix.gram ℝ (fun j : Fin R => Φ (bfamR hR u v j))
      = (Matrix.gram ℝ (fun c : Fin 1 ⊕ Fin (R - 1) => Φ (famR u v c))).submatrix
          (idxEquiv R hR).symm (idxEquiv R hR).symm := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.gram_apply]
  rw [bfamR_apply hR u v i, bfamR_apply hR u v j]

theorem latCovol_latStep {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ} (hR : 1 ≤ R)
    (Φ : Work.HP.LatMap (ι := ι) R) (hΦ : Function.Injective Φ)
    (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ))
    (hbij : Function.Bijective (fun c : ℤ × (Fin (R - 1) → ℤ) =>
      c.1 • u + ∑ i, c.2 i • v i)) :
    Work.HP.latCovol Φ
      = ‖Φ (fun j => (u j : ℝ))‖ * Work.HP.latCovol (Work.HP.FM.latStep Φ u v) := by
  classical
  -- `u` cannot vanish: the decomposition map would identify `(1, 0)` and `(0, 0)`.
  have hu_ne : u ≠ 0 := by
    intro hu
    have h1 : (fun c : ℤ × (Fin (R - 1) → ℤ) => c.1 • u + ∑ i, c.2 i • v i) (1, 0)
        = (fun c : ℤ × (Fin (R - 1) → ℤ) => c.1 • u + ∑ i, c.2 i • v i) (0, 0) := by
      simp [hu]
    exact one_ne_zero (Prod.ext_iff.mp (hbij.1 h1)).1
  -- hence `Φ u ≠ 0`, so that the projection onto `(Φ u)^⊥` is well behaved
  have hp_ne : Φ (fun j => (u j : ℝ)) ≠ 0 := by
    intro hp
    apply hu_ne
    funext j
    have h3 : (fun j => (u j : ℝ)) = 0 := hΦ (hp.trans (map_zero Φ).symm)
    exact Int.cast_eq_zero.mp (congrFun h3 j)
  -- the Gram determinant of the standard basis equals the one of the `ℤ`-basis `(u, v)`
  have hgram : (Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))).det
      = (Matrix.gram ℝ (fun j : Fin R => Φ (bfamR hR u v j))).det :=
    det_gram_of_int_basis (bfam hR u v) (bfam_bijective hR u v hbij) Φ
  have hreindex := gram_bfamR_submatrix (ι := ι) hR u v Φ
  -- the `Fin R`-indexed family is the sum-indexed family `(Φ u, Φ v₀, …)`
  have hfam : Matrix.gram ℝ (fun c : Fin 1 ⊕ Fin (R - 1) => Φ (famR u v c))
      = Matrix.gram ℝ (Sum.elim (fun _ : Fin 1 => Φ (fun j => (u j : ℝ)))
          (fun i => Φ (fun k => (v i k : ℝ)))) := by
    congr 1
    funext c
    cases c with
    | inl i => simp [famR_inl]
    | inr i => simp [famR_inr]
  -- the Schur complement of the block Gram matrix of `(Φ u, Φ v₀, …)`
  have hschur := gram_det_cons_smul (Φ (fun j => (u j : ℝ))) hp_ne
    (fun i => Φ (fun k => (v i k : ℝ)))
  -- and the projected covolume is the Schur complement
  have hproj : Work.HP.latCovol (Work.HP.FM.latStep Φ u v)
      = Real.sqrt ((Matrix.gram ℝ (fun i : Fin (R - 1) =>
          Work.HP.projU (Φ (fun j => (u j : ℝ))) (Φ (fun k => (v i k : ℝ))))).det) := by
    rw [show Work.HP.latCovol (Work.HP.FM.latStep Φ u v)
        = Real.sqrt ((Matrix.gram ℝ (fun i : Fin (R - 1) =>
            Work.HP.FM.latStep Φ u v (Pi.basisFun ℝ (Fin (R - 1)) i))).det) from rfl,
      gram_latStep]
  calc Work.HP.latCovol Φ
      = Real.sqrt ((Matrix.gram ℝ (fun i : Fin R => Φ (Pi.basisFun ℝ (Fin R) i))).det) := rfl
    _ = Real.sqrt ((Matrix.gram ℝ (fun j : Fin R => Φ (bfamR hR u v j))).det) := by
          rw [hgram]
    _ = Real.sqrt ((Matrix.gram ℝ (fun c : Fin 1 ⊕ Fin (R - 1) => Φ (famR u v c))).det) := by
          rw [hreindex, Matrix.det_submatrix_equiv_self (idxEquiv R hR).symm
            (Matrix.gram ℝ (fun c : Fin 1 ⊕ Fin (R - 1) => Φ (famR u v c)))]
    _ = Real.sqrt ((Matrix.gram ℝ (Sum.elim (fun _ : Fin 1 => Φ (fun j => (u j : ℝ)))
          (fun i => Φ (fun k => (v i k : ℝ))))).det) := by rw [hfam]
    _ = Real.sqrt (‖Φ (fun j => (u j : ℝ))‖ ^ 2 *
          (Matrix.gram ℝ (fun i : Fin (R - 1) =>
            Work.HP.projU (Φ (fun j => (u j : ℝ))) (Φ (fun k => (v i k : ℝ))))).det) := by
          rw [hschur]
    _ = ‖Φ (fun j => (u j : ℝ))‖ * Real.sqrt ((Matrix.gram ℝ (fun i : Fin (R - 1) =>
          Work.HP.projU (Φ (fun j => (u j : ℝ))) (Φ (fun k => (v i k : ℝ))))).det) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ = ‖Φ (fun j => (u j : ℝ))‖ * Work.HP.latCovol (Work.HP.FM.latStep Φ u v) := by
          rw [hproj]

/-- The covolume identity in the `RecData` vocabulary: the covolume of the presented lattice is
the product of `‖D.p‖` (the norm of its shortest vector) with the covolume of the projected
presentation `D.step`. -/
theorem latCovol_RecData_step {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ} (hR : 1 ≤ R)
    (D : Work.HP.FM.RecData R ι) :
    Work.HP.latCovol D.Φ = ‖D.p‖ * Work.HP.latCovol D.step := by
  rw [Work.HP.FM.RecData.step, Work.HP.FM.RecData.p]
  exact latCovol_latStep hR D.Φ D.Φ_inj D.u D.v D.bij

end Work.HP.Sig2
