import Mathlib
import Submission.Work.L2F.Props.CentralizerTorusDefs
import Submission.Work.L2F.Semisimple.primeOrderCentralizer

namespace Work.L2F.Props

theorem rhoSL_mem_hypToSLHom_range (F : Type*) [Field F] (g : GL (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hd : glD F g ≠ 0) (h : GL (Fin 2) F) (a b : F)
    (hab : (h : Matrix (Fin 2) (Fin 2) F) = a • 1 + b • glW F g) :
    rhoSL F h ∈ (Work.L2F.Semisimple.hypToSLHom F (glW F g) (glD F g) (glW_trace F h2 g)
      (glW_mul_self F h2 g)).range := by
  -- Write `W = glW F g` (traceless) and `δ = glD F g` (its square), so that `W * W = δ • 1`.
  have hsq := glW_mul_self F h2 g
  have htr := glW_trace F h2 g
  -- `h` lies in `F·1 + F·W`, hence `h * h` and `det h` are computed by the product/determinant
  -- formula in the algebra `F[W] ≅ F[X]/(X² - δ)`.
  have hDdet : (h : Matrix (Fin 2) (Fin 2) F).det = a ^ 2 - glD F g * b ^ 2 := by
    rw [hab, Work.L2F.Semisimple.det_smul_one_add_smul F (glW F g) (glD F g) htr hsq a b]
  have hD : a ^ 2 - glD F g * b ^ 2 ≠ 0 := by
    rw [← hDdet, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det h).ne_zero
  have hMM : (h : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F)
      = (a ^ 2 + glD F g * b ^ 2) • (1 : Matrix (Fin 2) (Fin 2) F)
        + (2 * a * b) • glW F g := by
    rw [hab, Work.L2F.Semisimple.smul_one_add_smul_mul F (glW F g) (glD F g) hsq a b a b]
    rw [show a * a + glD F g * (b * b) = a ^ 2 + glD F g * b ^ 2 from by ring,
        show a * b + b * a = 2 * a * b from by ring]
  -- The "quotient" `h / conj h = det(h)⁻¹ • h²`, with norm `1`.
  set c : F := (a ^ 2 - glD F g * b ^ 2)⁻¹ * (a ^ 2 + glD F g * b ^ 2) with hc
  set d : F := (a ^ 2 - glD F g * b ^ 2)⁻¹ * (2 * a * b) with hd'
  have hcd : c ^ 2 - glD F g * d ^ 2 = 1 := by
    rw [hc, hd']
    field_simp
    ring
  -- Hence `c • 1 + d • W` is a norm-one element of `F[W]`, i.e. a point of `hypTorus F δ`.
  have hdetx : (Work.L2F.Mat2.quadMat (glD F g) c d).det = 1 := by
    rw [Work.L2F.Mat2.quadMat_det]; exact hcd
  have hmem : (⟨Work.L2F.Mat2.quadMat (glD F g) c d, hdetx⟩ :
      Matrix.SpecialLinearGroup (Fin 2) F) ∈ Work.L2F.hypTorus F (glD F g) :=
    (Work.L2F.Conic.mem_hypTorus F (glD F g) _).mpr ⟨c, d, hcd, rfl⟩
  refine MonoidHom.mem_range.mpr
    ⟨⟨⟨Work.L2F.Mat2.quadMat (glD F g) c d, hdetx⟩, hmem⟩, ?_⟩
  -- `hypToSL` of that point is `c • 1 + d • W`, which is exactly `rhoMat F h = det(h)⁻¹ • h²`.
  apply Subtype.ext
  change ((Work.L2F.Semisimple.hypToSL F (glW F g) (glD F g) htr hsq
      ⟨⟨Work.L2F.Mat2.quadMat (glD F g) c d, hdetx⟩, hmem⟩ :
        Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    = ((rhoSL F h : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  rw [Work.L2F.Semisimple.hypToSL_apply, rhoSL_coe]
  simp only [Work.L2F.Mat2.quadMat_apply_00, Work.L2F.Mat2.quadMat_apply_10]
  rw [rhoMat, hMM, hDdet, smul_add, smul_smul, smul_smul]

end Work.L2F.Props
