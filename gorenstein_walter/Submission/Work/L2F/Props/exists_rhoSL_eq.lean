import Mathlib
import Submission.Work.L2F.Props.CentralizerTorusDefs
import Submission.Work.L2F.Semisimple.primeOrderCentralizer

namespace Work.L2F.Props

/-- The traceless part `glW F g = g - (tr g / 2) • 1` commutes with `g`. -/
theorem glW_comm_g (F : Type*) [Field F] (g : GL (Fin 2) F) :
    glW F g * (g : Matrix (Fin 2) (Fin 2) F) = (g : Matrix (Fin 2) (Fin 2) F) * glW F g := by
  rw [glW_apply, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]

/-- Every element of the commutative algebra `F[glW F g] = F·1 + F·(glW F g)` commutes with
`g`. -/
theorem smul_one_add_smul_glW_comm_g (F : Type*) [Field F] (g : GL (Fin 2) F) (a b : F) :
    (a • 1 + b • glW F g) * (g : Matrix (Fin 2) (Fin 2) F)
      = (g : Matrix (Fin 2) (Fin 2) F) * (a • 1 + b • glW F g) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  rw [glW_comm_g F g]

/-- Surjectivity of `h ↦ rhoSL F h = det(h)⁻¹ • (h * h)` onto the norm-one elements
`c • 1 + e • (glW F g)` of `F[glW F g]`, restricted to matrices commuting with `g`.

Concretely, whenever `c ^ 2 - glD F g * e ^ 2 = 1` — i.e. `c + e·√(glD F g)` has norm one in
the algebra `F[glW F g] ≅ F[X]/(X² - glD F g)` (with `(glW F g)² = glD F g • 1`) — the element
`u = c • 1 + e • glW F g` is a unit of norm one, and a preimage under `rhoMat` is provided by
`1 + u = (1 + c) • 1 + e • glW F g` (when `1 + c ≠ 0`, which is exactly `det (1 + u) ≠ 0`).
Since `(1 + u) / (1 + conj u) = u` and `rhoMat w = det(w)⁻¹ • w * w = w / conj w` inside the
commutative algebra `F[glW F g]`, this `h` satisfies `rhoSL F h = u`.

In the remaining case `1 + c = 0` the norm relation forces `e = 0` (because `glD F g ≠ 0`), so
`u = -1`; then `glW F g` itself is invertible (its determinant is `-glD F g ≠ 0`), commutes with
`g`, and `rhoMat (glW F g) = det(glW F g)⁻¹ • (glD F g • 1) = -1 = u`. -/
theorem exists_rhoSL_eq (F : Type*) [Field F] (g : GL (Fin 2) F) (h2 : (2 : F) ≠ 0)
    (hd : glD F g ≠ 0) (c e : F) (hce : c ^ 2 - glD F g * e ^ 2 = 1) :
    ∃ h ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) F)),
      (rhoSL F h : Matrix (Fin 2) (Fin 2) F) = c • 1 + e • glW F g := by
  have htr : (glW F g).trace = 0 := glW_trace F h2 g
  have hsq : glW F g * glW F g = glD F g • 1 := glW_mul_self F h2 g
  rcases eq_or_ne (c + 1) 0 with hc | hc
  · -- Degenerate case `c = -1`; the norm relation then gives `e = 0`, so the target is `-1`.
    have hc' : c = -1 := eq_neg_of_add_eq_zero_left hc
    have he : e = 0 := by
      have hDe : glD F g * e ^ 2 = 0 := by
        have hh := hce
        rw [hc'] at hh
        linear_combination (-1) * hh
      rcases mul_eq_zero.mp hDe with h' | h'
      · exact absurd h' hd
      · have : e * e = 0 := by simpa [pow_two] using h'
        exact mul_self_eq_zero.mp this
    -- `glW F g` is invertible, with determinant `-glD F g ≠ 0`.
    have hdetW_eq : (glW F g).det = -glD F g := by
      have h :=
        Work.L2F.Semisimple.det_smul_one_add_smul F (glW F g) (glD F g) htr hsq 0 1
      simpa using h
    have hdetW : (glW F g).det ≠ 0 := by
      rw [hdetW_eq]
      exact neg_ne_zero.mpr hd
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetW, ?_, ?_⟩
    · -- `glW F g` commutes with `g`.
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      rw [glW_comm_g F g]
    · -- `rhoSL (glW F g) = -1 = c • 1 + e • glW F g`.
      rw [rhoSL_coe, rhoMat]
      simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      rw [hsq, hdetW_eq, smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hd]
      rw [neg_one_smul, hc', he]
      simp
  · -- Main case `1 + c ≠ 0`; the preimage is `1 + u = (1 + c) • 1 + e • glW F g`.
    have h1c : (1 + c) ≠ 0 := by rw [add_comm]; exact hc
    -- `det (1 + u) = (1 + c) ^ 2 - glD F g * e ^ 2 = 2 * (1 + c) ≠ 0`.
    have hdetH_eq :
        (((1 : F) + c) • (1 : Matrix (Fin 2) (Fin 2) F) + e • glW F g).det = 2 * (1 + c) := by
      rw [Work.L2F.Semisimple.det_smul_one_add_smul F (glW F g) (glD F g) htr hsq]
      linear_combination hce
    have hdetH :
        (((1 : F) + c) • (1 : Matrix (Fin 2) (Fin 2) F) + e • glW F g).det ≠ 0 := by
      rw [hdetH_eq]
      exact mul_ne_zero h2 h1c
    -- `(1 + u) * (1 + u) = det (1 + u) • u`, the algebra identity `1 + 1/conj u = u`.
    have hHH :
        (((1 : F) + c) • (1 : Matrix (Fin 2) (Fin 2) F) + e • glW F g) *
            (((1 : F) + c) • 1 + e • glW F g)
          = ((((1 : F) + c) • 1 + e • glW F g).det) • (c • 1 + e • glW F g) := by
      rw [Work.L2F.Semisimple.smul_one_add_smul_mul F (glW F g) (glD F g) hsq,
        Work.L2F.Semisimple.det_smul_one_add_smul F (glW F g) (glD F g) htr hsq]
      simp only [smul_add, smul_smul]
      have hcoef1 : (1 + c) * (1 + c) + glD F g * (e * e) =
          ((1 + c) ^ 2 - glD F g * e ^ 2) * c := by
        linear_combination (-(1 + c)) * hce
      have hcoef2 : (1 + c) * e + e * (1 + c) =
          ((1 + c) ^ 2 - glD F g * e ^ 2) * e := by
        linear_combination (-e) * hce
      rw [hcoef1, hcoef2]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetH, ?_, ?_⟩
    · -- `1 + u` commutes with `g`.
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      rw [smul_one_add_smul_glW_comm_g F g]
    · -- `rhoMat (1 + u) = det (1 + u)⁻¹ • ((1 + u) * (1 + u)) = u`.
      rw [rhoSL_coe, rhoMat]
      simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      rw [hHH, smul_smul, inv_mul_cancel₀ hdetH, one_smul]

end Work.L2F.Props
