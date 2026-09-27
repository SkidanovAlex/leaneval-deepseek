import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Dim2.loop_GL_nullhomotopic_of_det_log
import Submission.Work.KT.D2.StabAux
import Submission.Work.KT.D2.conj_std_idem
import Submission.Work.KT.D2.det_block_std_idem
import Submission.Work.KT.D2.loop_GL_sphere2

namespace Work.KT.D2

open Matrix

noncomputable section

/-- A loop of invertible complex matrices commuting with an idempotent `e`, whose two block
determinants admit continuous logarithms, is null-homotopic through units commuting with `e`.

Here the two blocks are `e * f x * e + (1 - e)` (the restriction of `f x` to `im e`, plus the
identity on `ker e`) and `(1 - e) * f x * (1 - e) + e`.

Route: conjugate `e` to a diagonal idempotent `d` with `c * e = d * c` (existential part of
`Work.KT.D2.conj_std_idem`), reduce to the block-diagonal matrix `c * f x * c⁻¹ = diag(A x, D x)`
with `A`, `D` loops of invertible matrices, apply `Work.KT.D2.loop_GL_sphere2` to `A` and to `D`
(their determinants are the two block determinants appearing in the hypotheses; that result lives
on `Metric.sphere (0:ℂ) 1` transported to the model circle `Sph (EuclideanSpace ℝ (Fin 2))`), and
reassemble the block-diagonal homotopies and conjugate back by `c`. -/
theorem stab_loop_nullhomotopic (n : ℕ) (e : Matrix (Fin n) (Fin n) ℂ) (he : e * e = e)
    (f : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), Matrix (Fin n) (Fin n) ℂ))
    (hunit : ∀ x, IsUnit (f x)) (hcomm : ∀ x, f x * e = e * f x)
    (h1 : ∃ F : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), ℂ),
      ∀ x, Complex.exp (F x) = Matrix.det (e * f x * e + (1 - e)))
    (h2 : ∃ F : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), ℂ),
      ∀ x, Complex.exp (F x) = Matrix.det ((1 - e) * f x * (1 - e) + e)) :
    ∃ H : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)) × unitInterval, Matrix (Fin n) (Fin n) ℂ),
      (∀ p, IsUnit (H p)) ∧ (∀ p, H p * e = e * H p) ∧
      (∀ x, H (x, 0) = f x) ∧ (∀ x, H (x, 1) = 1) := by
  obtain ⟨k, m, ε, c, hcisu, hce⟩ := conj_std_idem n e he
  obtain ⟨u, rfl⟩ := hcisu
  let S : Type := Work.KT.Sph (EuclideanSpace ℝ (Fin 2))
  let D₀ : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ :=
    Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.reindex ε ε D₀
  have hce' : conjUMat u e = D := by
    show (↑u : Matrix (Fin n) (Fin n) ℂ) * e * (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ)
      = Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0)
    rw [hce, mul_assoc, units_mul_inv_val, mul_one]
  -- the conjugated loop
  let G : C(S, Matrix (Fin n) (Fin n) ℂ) :=
    ⟨fun x => conjUMat u (f x), by
      show Continuous fun x : S =>
        (↑u : Matrix (Fin n) (Fin n) ℂ) * f x * (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ)
      exact ((continuous_const : Continuous fun _ : S =>
        (↑u : Matrix (Fin n) (Fin n) ℂ)).matrix_mul f.continuous).matrix_mul
        (continuous_const : Continuous fun _ : S => (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ))⟩
  have hG_apply : ∀ x : S, G x = conjUMat u (f x) := fun x => rfl
  have hGcomm : ∀ x : S, G x * D = D * G x := by
    intro x
    calc G x * D = conjUMat u (f x) * conjUMat u e := by rw [hG_apply x, hce']
      _ = conjUMat u (f x * e) := (conjUMat_mul u (f x) e).symm
      _ = conjUMat u (e * f x) := by rw [hcomm x]
      _ = conjUMat u e * conjUMat u (f x) := conjUMat_mul u e (f x)
      _ = D * G x := by rw [hce', hG_apply x]
  -- reindexing to the block index type
  let Gd : C(S, Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ) :=
    ⟨fun x => Matrix.reindex ε.symm ε.symm (G x), by
      refine continuous_matrix fun i j => ?_
      show Continuous fun x : S => (Matrix.reindex ε.symm ε.symm (G x)) i j
      simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using
        G.continuous.matrix_elem (ε i) (ε j)⟩
  have hGd_apply : ∀ x : S, Gd x = Matrix.reindex ε.symm ε.symm (G x) := fun x => rfl
  have hreindexD : Matrix.reindex ε.symm ε.symm D = D₀ := by
    show Matrix.reindex ε.symm ε.symm
        (Matrix.reindex ε ε (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0))
      = Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0
    exact reindexSymmReindex ε _
  have hGd_comm : ∀ x : S, Gd x * D₀ = D₀ * Gd x := by
    intro x
    calc Gd x * D₀ = Matrix.reindex ε.symm ε.symm (G x) * Matrix.reindex ε.symm ε.symm D := by
          rw [hGd_apply x, hreindexD]
      _ = Matrix.reindex ε.symm ε.symm (G x * D) := (reindexSymm_mul ε (G x) D).symm
      _ = Matrix.reindex ε.symm ε.symm (D * G x) := by rw [hGcomm x]
      _ = Matrix.reindex ε.symm ε.symm D * Matrix.reindex ε.symm ε.symm (G x) :=
            reindexSymm_mul ε D (G x)
      _ = D₀ * Gd x := by rw [hreindexD, hGd_apply x]
  have hGd_blk : ∀ x : S, Gd x = Matrix.fromBlocks ((Gd x).submatrix Sum.inl Sum.inl) 0 0
      ((Gd x).submatrix Sum.inr Sum.inr) := by
    intro x
    refine eq_fromBlocks_of_comm (Gd x) ?_
    show Gd x * Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0
      = Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0 * Gd x
    exact hGd_comm x
  -- the two diagonal blocks
  let Tl : C(S, Matrix (Fin k) (Fin k) ℂ) :=
    ⟨fun x => (Gd x).submatrix Sum.inl Sum.inl, by
      refine continuous_matrix fun i j => ?_
      show Continuous fun x : S => ((Gd x).submatrix Sum.inl Sum.inl) i j
      simpa [Matrix.submatrix_apply] using Gd.continuous.matrix_elem (Sum.inl i) (Sum.inl j)⟩
  let Tr : C(S, Matrix (Fin m) (Fin m) ℂ) :=
    ⟨fun x => (Gd x).submatrix Sum.inr Sum.inr, by
      refine continuous_matrix fun i j => ?_
      show Continuous fun x : S => ((Gd x).submatrix Sum.inr Sum.inr) i j
      simpa [Matrix.submatrix_apply] using Gd.continuous.matrix_elem (Sum.inr i) (Sum.inr j)⟩
  have hTl_det : ∀ x : S, (Tl x).det = (e * f x * e + (1 - e)).det := by
    intro x
    have h := (det_block_std_idem n k m ε e he u (G x) hce).1
    have h2 : (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ) * G x
        * (↑u : Matrix (Fin n) (Fin n) ℂ) = f x := by
      rw [show (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ) * G x * (↑u : Matrix (Fin n) (Fin n) ℂ)
          = conjUInv u (G x) from rfl, hG_apply x]
      exact conjUInv_conjUMat u (f x)
    rw [h2] at h
    exact h.symm
  have hTr_det : ∀ x : S, (Tr x).det = ((1 - e) * f x * (1 - e) + e).det := by
    intro x
    have h := (det_block_std_idem n k m ε e he u (G x) hce).2
    have h2 : (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ) * G x
        * (↑u : Matrix (Fin n) (Fin n) ℂ) = f x := by
      rw [show (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ) * G x * (↑u : Matrix (Fin n) (Fin n) ℂ)
          = conjUInv u (G x) from rfl, hG_apply x]
      exact conjUInv_conjUMat u (f x)
    rw [h2] at h
    exact h.symm
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  have hTl_log : ∃ F : C(S, ℂ), ∀ x : S, Complex.exp (F x) = (Tl x).det :=
    ⟨F1, fun x => by rw [hF1 x, hTl_det x]⟩
  have hTr_log : ∃ F : C(S, ℂ), ∀ x : S, Complex.exp (F x) = (Tr x).det :=
    ⟨F2, fun x => by rw [hF2 x, hTr_det x]⟩
  have hTl_unit : ∀ x : S, IsUnit (Tl x) := by
    intro x
    rw [Matrix.isUnit_iff_isUnit_det, hTl_det x]
    exact isUnit_iff_ne_zero.mpr (by rw [← hF1 x]; exact Complex.exp_ne_zero (F1 x))
  have hTr_unit : ∀ x : S, IsUnit (Tr x) := by
    intro x
    rw [Matrix.isUnit_iff_isUnit_det, hTr_det x]
    exact isUnit_iff_ne_zero.mpr (by rw [← hF2 x]; exact Complex.exp_ne_zero (F2 x))
  obtain ⟨HA, hHAunit, hHA0, hHA1⟩ := loop_GL_sphere2 k Tl hTl_unit hTl_log
  obtain ⟨HB, hHBunit, hHB0, hHB1⟩ := loop_GL_sphere2 m Tr hTr_unit hTr_log
  -- assembly
  let Hfun : S × unitInterval → Matrix (Fin n) (Fin n) ℂ := fun p =>
    conjUInv u (Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p)))
  have hH_apply : ∀ p : S × unitInterval, Hfun p =
      conjUInv u (Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p))) := fun p => rfl
  have hcont_fb : Continuous fun p : S × unitInterval =>
      Matrix.fromBlocks (HA p) 0 0 (HB p) := by
    refine continuous_matrix fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · simpa [Matrix.fromBlocks_apply₁₁] using (HA.continuous.matrix_elem i j)
    · exact (continuous_const : Continuous fun _ : S × unitInterval => (0 : ℂ)).congr
        fun a => (Matrix.fromBlocks_apply₁₂ (HA a) 0 0 (HB a) i j).symm
    · exact (continuous_const : Continuous fun _ : S × unitInterval => (0 : ℂ)).congr
        fun a => (Matrix.fromBlocks_apply₂₁ (HA a) 0 0 (HB a) i j).symm
    · simpa [Matrix.fromBlocks_apply₂₂] using (HB.continuous.matrix_elem i j)
  have hcont_ri : Continuous fun p : S × unitInterval =>
      Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun p : S × unitInterval =>
      (Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p))) i j
    simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using
      hcont_fb.matrix_elem (ε.symm i) (ε.symm j)
  have hHcont : Continuous Hfun := by
    show Continuous fun p : S × unitInterval =>
      (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ)
        * Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p))
        * (↑u : Matrix (Fin n) (Fin n) ℂ)
    exact ((continuous_const : Continuous fun _ : S × unitInterval =>
        (↑(u⁻¹) : Matrix (Fin n) (Fin n) ℂ)).matrix_mul hcont_ri).matrix_mul
      (continuous_const : Continuous fun _ : S × unitInterval =>
        (↑u : Matrix (Fin n) (Fin n) ℂ))
  refine ⟨⟨Hfun, hHcont⟩, ?_, ?_, ?_, ?_⟩
  · intro p
    show IsUnit (conjUInv u (Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p))))
    have hblk : IsUnit (Matrix.fromBlocks (HA p) 0 0 (HB p)) := by
      rw [isUnit_fromBlocks_diag]
      exact ⟨hHAunit p, hHBunit p⟩
    have hri : IsUnit (Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p))) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self]
      exact (Matrix.isUnit_iff_isUnit_det _).mp hblk
    exact IsUnit.mul (IsUnit.mul ⟨u⁻¹, rfl⟩ hri) ⟨u, rfl⟩
  · intro p
    have he_eq : e = conjUInv u D := by
      rw [← hce']
      exact (conjUInv_conjUMat u e).symm
    have hYD : Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p)) * D
        = D * Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p)) := by
      have hb : Matrix.fromBlocks (HA p) 0 0 (HB p)
            * Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0
          = Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℂ) 0 0 0
            * Matrix.fromBlocks (HA p) 0 0 (HB p) := by
        rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
        simp
      have h2 := congrArg (fun M => Matrix.reindex ε ε M) hb
      rw [reindex_mul, reindex_mul] at h2
      exact h2
    show conjUInv u (Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p))) * e
      = e * conjUInv u (Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p)))
    calc conjUInv u (Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p))) * e
        = conjUInv u (Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p)))
            * conjUInv u D := by rw [he_eq]
      _ = conjUInv u (Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p)) * D) :=
            (conjUInv_mul u _ D).symm
      _ = conjUInv u (D * Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p))) := by
            rw [hYD]
      _ = conjUInv u D
            * conjUInv u (Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p))) :=
            conjUInv_mul u D _
      _ = e * conjUInv u (Matrix.reindex ε ε (Matrix.fromBlocks (HA p) 0 0 (HB p))) := by
            rw [he_eq]
  · intro x
    show Hfun (x, 0) = f x
    rw [hH_apply (x, 0)]
    have h00 : Matrix.fromBlocks (HA (x, 0)) 0 0 (HB (x, 0)) = Gd x := by
      rw [hHA0 x, hHB0 x]
      exact (hGd_blk x).symm
    rw [h00, hGd_apply x, reindexReindexSymm ε (G x), hG_apply x]
    exact conjUInv_conjUMat u (f x)
  · intro x
    show Hfun (x, 1) = 1
    rw [hH_apply (x, 1), hHA1 x, hHB1 x, Matrix.fromBlocks_one, reindex_one ε, conjUInv_one u]

end

end Work.KT.D2
