import Mathlib
import Submission.Work.Drive.N2.modelBall

/-!
# The canonical chart of a scaled complex chart on a surface

`Work.Drive.N2.canonChartOfScaled`.  Let `M` be a `C^∞` surface over the model
`EuclideanSpace ℝ (Fin 2)`, `φ` a chart of `M`, `lam0 ≠ 0` a real scale and `Z : M → ℂ` the
complex-valued chart `Z y = σc · (φ y)` divided by `lam0`, where `σc` is either `1` or `Complex.I`
(the two "canonical" scalars of the level-separating route: the identity and the quarter turn).
Then `φ` can be replaced by a chart `φ'` with the *same source* and the *same model balls*
`{y | ‖φ' y‖ < r}`, which is `C^∞` on its source and whose complex value is exactly `lam0 · Z y`.

The two cases are the identity and the quarter turn of the plane, which act on
`EuclideanSpace ℝ (Fin 2) ≅ ℂ` as `(a, b) ↦ (a, b)` and `(a, b) ↦ (-b, a)`; both are linear
isometries of the plane, so the model balls are preserved.  All the work is in exhibiting the
quarter turn as a `LinearIsometryEquiv` (`canonChartRotIso`) and in the one complex identity
`I · (a + b I) = -b + a I` (`canonChart_I_mul_complex`).
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

/-- The quarter turn `(a, b) ↦ (-b, a)` of the plane, as a linear equivalence. -/
noncomputable def canonChartRotLE :
    EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun v := !₂[-(v 1), v 0]
  invFun v := !₂[v 1, -(v 0)]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' v w := by
    ext i
    fin_cases i
    · simp
      ring
    · simp
  map_smul' c v := by ext i; fin_cases i <;> simp

@[simp] lemma canonChartRotLE_apply_zero (v : EuclideanSpace ℝ (Fin 2)) :
    canonChartRotLE v 0 = -(v 1) := rfl

@[simp] lemma canonChartRotLE_apply_one (v : EuclideanSpace ℝ (Fin 2)) :
    canonChartRotLE v 1 = v 0 := rfl

/-- The quarter turn is a linear isometry of the plane. -/
lemma canonChartRotLE_norm (v : EuclideanSpace ℝ (Fin 2)) : ‖canonChartRotLE v‖ = ‖v‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [canonChartRotLE, Real.norm_eq_abs, sq_abs, add_comm]

/-- The quarter turn of the plane as a linear isometry equivalence. -/
noncomputable def canonChartRotIso :
    EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearIsometryEquiv.mk canonChartRotLE canonChartRotLE_norm

@[simp] lemma canonChartRotIso_apply_zero (v : EuclideanSpace ℝ (Fin 2)) :
    canonChartRotIso v 0 = -(v 1) := rfl

@[simp] lemma canonChartRotIso_apply_one (v : EuclideanSpace ℝ (Fin 2)) :
    canonChartRotIso v 1 = v 0 := rfl

/-- The one complex identity behind the quarter-turn case: multiplication by `I` sends the
complex number `a + b I` to `-b + a I`. -/
lemma canonChart_I_mul_complex (a b : ℝ) :
    Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I) =
      ((-b : ℝ) : ℂ) + ((a : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]

theorem canonChartOfScaled {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (Z : M → ℂ) {lam0 : ℝ}
    (hlam0 : lam0 ≠ 0)
    (hφsm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source)
    {σc : ℂ} (hσc : σc = 1 ∨ σc = Complex.I)
    (hZ : ∀ y : M, Z y = σc * (((φ y 0 : ℝ) : ℂ) + ((φ y 1 : ℝ) : ℂ) * Complex.I)
      / (lam0 : ℂ)) :
    ∃ φ' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)),
      φ'.source = φ.source ∧
      (∀ r : ℝ, Work.Drive.N2.modelBall φ' r = Work.Drive.N2.modelBall φ r) ∧
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ' y) φ'.source ∧
      (∀ y ∈ φ.source, (((φ' y 0 : ℝ) : ℂ) + ((φ' y 1 : ℝ) : ℂ) * Complex.I)
        = (lam0 : ℂ) * Z y) := by
  have hL : (lam0 : ℂ) ≠ 0 := by
    simpa using hlam0
  rcases hσc with rfl | rfl
  · -- `σc = 1`: the chart itself does the job.
    refine ⟨φ, rfl, fun r => rfl, hφsm, fun y hy => ?_⟩
    rw [hZ y, one_mul, mul_div_cancel₀ _ hL]
  · -- `σc = I`: compose with the quarter turn.
    let e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
      (canonChartRotIso.toHomeomorph).toOpenPartialHomeomorph
    have hcoe : ∀ v, e v = canonChartRotIso v := fun v => rfl
    have hsrc : (φ.trans e).source = φ.source := by
      rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
        preimage_univ, inter_univ]
    have happ : ∀ y, (φ.trans e) y = canonChartRotIso (φ y) := fun y => by
      rw [OpenPartialHomeomorph.trans_apply]
      exact hcoe (φ y)
    refine ⟨φ.trans e, hsrc, ?_, ?_, ?_⟩
    · intro r
      ext y
      simp only [Work.Drive.N2.modelBall, Set.mem_ofPred_eq]
      rw [hsrc, happ y, LinearIsometryEquiv.norm_map]
    · rw [hsrc]
      have he : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => canonChartRotIso v) univ :=
        ((LinearIsometryEquiv.contDiff canonChartRotIso).contMDiff).contMDiffOn
      refine (he.comp hφsm (fun y _ => trivial)).congr (fun y hy => ?_)
      exact happ y
    · intro y hy
      rw [hZ y, happ y, mul_div_cancel₀ _ hL]
      exact (canonChart_I_mul_complex (φ y 0) (φ y 1)).symm

end Work.Drive.N2
