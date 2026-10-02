import Submission.Work.Transgression.Pieces
import Submission.Work.Cohomology.CompatTrans.homology_prod_sphere
import Submission.Work.Cohomology.kronH_isIso
import Submission.Work.Transgression.Algebra

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# SUBPROJECT TRANSGRESSION: `H³(S³ × S³;ℤ) ≅ ℤ²`

The rank-two input of the transgression: in the quaternionic model `S³ = Sp(1)` the third
cohomology of `S³ × S³` is free of rank two.  The route is the one that is importable in this
closure (`Work.Cohomology.cohomology_prod_sphere` clashes with `CompatTrans`):

* `Work.Cohomology.homology_prod_sphere 3 3 n` computes `Hₙ(S³ × S³;ℤ)` in the `Metric.sphere`
  model; transporting along `s3Homeo × s3Homeo` gives it for the quaternionic model, hence
  freeness of the homology (`Work.Transgression.free_homology_Q2`);
* the Kronecker pairing `Work.Cohomology.kronH_isIso` is a bijection
  `H³(S³ × S³;ℤ) → (H₃(S³ × S³;ℤ) →ₗ[ℤ] ℤ)` when the homology is free;
* the dual of `ℤ²` is `ℤ²` (`Work.Transgression.dualCongr` and the dual basis
  `(Pi.basisFun ℤ (Fin 2)).dualBasis`).

The result is `Work.Transgression.Sph33Rank`.
-/

namespace Work.Transgression

open CategoryTheory

noncomputable section

/-- `S³ × S³` in the quaternionic model. -/
abbrev Q2 : TopCat := TopCat.of (Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3)

/-- `S³ × S³` in the standard `Metric.sphere` model in which the homology is computed. -/
abbrev Sph2 : TopCat := TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ×
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

/-- The homeomorphism `S³ × S³ ≅ Sph²` of the two models. -/
def q2Homeo : (Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3) ≃ₜ
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  Work.CharacteristicClasses.s3Homeo.prodCongr Work.CharacteristicClasses.s3Homeo

/-- **The homology of `S³ × S³` in the quaternionic model**, from
`Work.Cohomology.homology_prod_sphere`. -/
theorem homology_Q2 (n : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ Q2).homology n ≅
      ModuleCat.of ℤ (Fin (Work.Cohomology.expo 3 3 n) → ℤ)) := by
  obtain ⟨e1⟩ := Work.Cohomology.homology_prod_sphere 3 3 n (by norm_num) (by norm_num)
  obtain ⟨e2⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv q2Homeo.toHomotopyEquiv n
  exact ⟨e2 ≪≫ e1⟩

/-- The homology of `S³ × S³` is degreewise free. -/
theorem free_homology_Q2 :
    ∀ n, Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ Q2).homology n) := by
  intro n
  obtain ⟨e⟩ := homology_Q2 n
  exact Module.Free.of_equiv' (Module.Free.pi ℤ (fun _ : Fin (Work.Cohomology.expo 3 3 n) => ℤ))
    (e.toLinearEquiv).symm

/-- The dual of a `ℤ`-linear equivalence, contravariantly. -/
def dualCongr {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (e : M ≃ₗ[ℤ] N) : (N →ₗ[ℤ] ℤ) ≃ₗ[ℤ] (M →ₗ[ℤ] ℤ) where
  toFun φ := φ.comp (e : M →ₗ[ℤ] N)
  invFun ψ := ψ.comp (e.symm : N →ₗ[ℤ] M)
  left_inv φ := by ext y; simp
  right_inv ψ := by ext x; simp
  map_add' φ ψ := by ext x; simp
  map_smul' c φ := by ext x; simp

/-- The dual of `Fin 2 → ℤ` is `Fin 2 → ℤ`. -/
def dualFinTwo : ((Fin 2 → ℤ) →ₗ[ℤ] ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((Pi.basisFun ℤ (Fin 2)).dualBasis.repr).trans (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin 2))

/-- **`H³(S³ × S³;ℤ) ≅ ℤ²`** — the rank-two input of the transgression. -/
theorem Sph33Rank :
    Nonempty (↥(Work.Thom.Coh ℤ 3 (Work.CharacteristicClasses.S3 × Work.CharacteristicClasses.S3))
      ≃ₗ[ℤ] (Fin 2 → ℤ)) := by
  have hbij : Function.Bijective (fun α : ↥(Work.Thom.Coh ℤ 3 Q2) =>
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj Q2) 3 α) :=
    Work.Cohomology.kronH_isIso Q2 free_homology_Q2 3
  have e1 : ↥(Work.Thom.Coh ℤ 3 Q2)
      ≃ₗ[ℤ] (↥((Work.Cohomology.singularChains ℤ Q2).homology 3) →ₗ[ℤ] ℤ) :=
    LinearEquiv.ofBijective _ hbij
  have hexp : Work.Cohomology.expo 3 3 3 = 2 := by decide
  obtain ⟨e2⟩ := homology_Q2 3
  have hcat : ModuleCat.of ℤ (Fin (Work.Cohomology.expo 3 3 3) → ℤ)
      = ModuleCat.of ℤ (Fin 2 → ℤ) := by rw [hexp]
  exact ⟨e1.trans ((dualCongr (e2 ≪≫ eqToIso hcat).toLinearEquiv.symm).trans dualFinTwo)⟩

end

end Work.Transgression
