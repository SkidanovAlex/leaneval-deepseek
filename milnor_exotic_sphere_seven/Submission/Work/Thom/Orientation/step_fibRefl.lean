import Mathlib
import Submission.Work.Thom.Orientation.Reflection

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Naturality of the inductive step `Work.Thom.step` under the fibre reflection

The inductive step `Work.Thom.step` of the model Thom class is natural in the base
(`Work.Thom.step_natural`, `Work.Thom.step_natural_map`).  For the orientation character of the
trivial bundle the relevant automorphism of the total space is *not* a base change but the fibre
reflection `Work.Thom.Orientation.fibRefl m Y`, `(y, v) ↦ (y, flipFst m v)`, which negates the
first coordinate of the fibre.  This file proves that the inductive step commutes with it,
`Work.Thom.Orientation.step_fibRefl`.

The proof is a verbatim transposition of the proof of `Work.Thom.step_natural_map` (the naturality
for an arbitrary base change), with `Work.Thom.prodMapA g F` replaced by `fibRefl F` and the three
commutation identities of `Submission/Work/Thom/Orientation/Reflection.lean`
(`discFullMap_comp_fibReflBall`, `capMapPairSph_comp_fibReflBall`,
`prodSubsetHomeoA_symm_comp_fibRefl`) replacing those of `Submission/Work/Thom/ProdMapTools.lean`.
-/

set_option linter.unusedSimpArgs false

namespace Work.Thom.Orientation

open Work.Thom

noncomputable section

/-- The fibre reflection preserves the "disc boundary" part `DiscB Y n` of the ball bundle. -/
theorem fibReflBall_mem_DiscB (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    ∀ q ∈ DiscB Y n, fibReflBall n Y q ∈ DiscB Y n := by
  intro q hq
  show flipFst n q.2.1 ∈ mSph n
  show ‖flipFst n q.2.1‖ = 1
  rw [flipFst_norm]
  exact hq

/-- Naturality of `stepDisc` under the fibre reflection. -/
theorem stepDisc_fibRefl (n : ℕ) (Y : Type) [TopologicalSpace Y]
    (τ : RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin n)) (Sph Y n)) :
    (relCohMap (fibReflBall n Y) (DiscB Y n) (DiscB Y n) (fibReflBall_mem_DiscB n Y) ℤ n).hom
        (stepDisc Y n τ)
      = stepDisc Y n
          ((relCohMap (fibRefl n Y) (Sph Y n) (Sph Y n) (fibRefl_mem_sph n Y) ℤ n).hom τ) := by
  have h1 : ∀ q ∈ DiscB Y n, (CleanA.discFullMap Y n) (fibReflBall n Y q) ∈ Sph Y n :=
    fun q hq => by
      show flipFst n q.2.1 ∈ mSph n
      show ‖flipFst n q.2.1‖ = 1
      rw [flipFst_norm]; exact hq
  have h2 : ∀ q ∈ DiscB Y n, (fibRefl n Y) (CleanA.discFullMap Y n q) ∈ Sph Y n :=
    fun q hq => by
      show flipFst n q.2.1 ∈ mSph n
      show ‖flipFst n q.2.1‖ = 1
      rw [flipFst_norm]; exact hq
  rw [stepDisc, stepDisc]
  rw [relCohMap_compA_apply (DiscB Y n) (DiscB Y n) (Sph Y n) (fibReflBall n Y)
        (CleanA.discFullMap Y n) (fibReflBall_mem_DiscB n Y) (CleanA.discFullMap_mem Y n)
        h1 ℤ n τ]
  rw [relCohMap_compA_apply (DiscB Y n) (Sph Y n) (Sph Y n) (CleanA.discFullMap Y n)
        (fibRefl n Y) (CleanA.discFullMap_mem Y n) (fibRefl_mem_sph n Y) h2 ℤ n τ]
  have hm : relCohMap ((CleanA.discFullMap Y n).comp (fibReflBall n Y)) (DiscB Y n) (Sph Y n)
        h1 ℤ n
      = relCohMap ((fibRefl n Y).comp (CleanA.discFullMap Y n)) (DiscB Y n) (Sph Y n)
        h2 ℤ n :=
    relCohMap_congrA (DiscB Y n) (Sph Y n) (discFullMap_comp_fibReflBall n Y) h1 h2 ℤ n
  rw [hm]

/-- Naturality of `stepSph` under the fibre reflection. -/
theorem stepSph_fibRefl (n : ℕ) (hn : 1 ≤ n) (Y : Type) [TopologicalSpace Y]
    (τ : RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin n)) (Sph Y n)) :
    (relCohMap (fibReflMSph (n+1) Y) (SphB Y n) (SphB Y n)
        (fibReflMSph_mem_SphB n hn Y) ℤ n).hom (stepSph Y n τ)
      = stepSph Y n
          ((relCohMap (fibRefl n Y) (Sph Y n) (Sph Y n) (fibRefl_mem_sph n Y) ℤ n).hom τ) := by
  have hinj : Function.Injective ((relCohMap (capMapPairSph Y n) (DiscB Y n) (SphB Y n)
        (CleanA.capMapPairSph_mem_mLower n) ℤ n).hom) :=
    (CleanA.capRelCohIso Y n n).1
  apply hinj
  have h1 : ∀ q ∈ DiscB Y n,
      (fibReflMSph (n+1) Y) (capMapPairSph Y n q) ∈ SphB Y n :=
    fun q hq => fibReflMSph_mem_SphB n hn Y _ (CleanA.capMapPairSph_mem_mLower n q hq)
  have h2 : ∀ q ∈ DiscB Y n,
      (capMapPairSph Y n) (fibReflBall n Y q) ∈ SphB Y n :=
    fun q hq => CleanA.capMapPairSph_mem_mLower n (fibReflBall n Y q)
      (fibReflBall_mem_DiscB n Y q hq)
  rw [relCohMap_compA_apply (DiscB Y n) (SphB Y n) (SphB Y n) (capMapPairSph Y n)
        (fibReflMSph (n+1) Y) (CleanA.capMapPairSph_mem_mLower n) (fibReflMSph_mem_SphB n hn Y)
        h1 ℤ n (stepSph Y n τ)]
  rw [stepSph_spec Y n
        ((relCohMap (fibRefl n Y) (Sph Y n) (Sph Y n) (fibRefl_mem_sph n Y) ℤ n).hom τ)]
  have hm2 : relCohMap ((fibReflMSph (n+1) Y).comp (capMapPairSph Y n)) (DiscB Y n) (SphB Y n)
        h1 ℤ n
      = relCohMap ((capMapPairSph Y n).comp (fibReflBall n Y)) (DiscB Y n) (SphB Y n)
        h2 ℤ n :=
    relCohMap_congrA (DiscB Y n) (SphB Y n) (capMapPairSph_comp_fibReflBall n hn Y) h1 h2 ℤ n
  rw [hm2]
  rw [← relCohMap_compA_apply (DiscB Y n) (DiscB Y n) (SphB Y n) (fibReflBall n Y)
        (capMapPairSph Y n) (fibReflBall_mem_DiscB n Y) (CleanA.capMapPairSph_mem_mLower n)
        h2 ℤ n (stepSph Y n τ)]
  rw [stepSph_spec Y n τ]
  rw [stepDisc_fibRefl n Y τ]

/-- **The inductive step commutes with the fibre reflection.**  Pulling the model class of the
pair `(Y × ℝⁿ⁺¹, Y × Sⁿ)` back along the reflection `id × flipFst (n+1)` is the same as performing
the inductive step on the pullback along `id × flipFst n` of the class of `(Y × ℝⁿ, Y × Sⁿ⁻¹)`. -/
theorem step_fibRefl (n : ℕ) (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y]
    (τ : Work.Thom.RelCoh ℤ n (Y × EuclideanSpace ℝ (Fin n)) (Work.Thom.Sph Y n)) :
    (Work.Thom.relCohMap (fibRefl (n+1) Y) (Work.Thom.Sph Y (n+1)) (Work.Thom.Sph Y (n+1))
        (fibRefl_mem_sph (n+1) Y) ℤ (n+1)).hom (Work.Thom.step Y n τ)
      = Work.Thom.step Y n ((Work.Thom.relCohMap (fibRefl n Y) (Work.Thom.Sph Y n)
          (Work.Thom.Sph Y n) (fibRefl_mem_sph n Y) ℤ n).hom τ) := by
  rw [step, step]
  rw [pairDeltaNatural_restrict (fibRefl (n+1) Y) (Sph Y (n+1)) (Sph Y (n+1))
        (fibRefl_mem_sph (n+1) Y) n]
  refine congrArg (fun w => (pairδC (Sph Y (n+1)) n).hom w) ?_
  rw [← stepSph_fibRefl n hn Y τ]
  rw [relCohMap_relToAbs_apply (fibReflMSph (n+1) Y) (SphB Y n) (SphB Y n)
        (fibReflMSph_mem_SphB n hn Y) ℤ n (stepSph Y n τ)]
  rw [CohMap_comp_apply
        ((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin (n+1))) (mSph (n+1))).symm :
          C(↥(Sph Y (n+1)), Y × MSph (n+1)))
        (fibReflMSph (n+1) Y) ℤ n
        ((relToAbs ℤ (SphB Y n) n).hom (stepSph Y n τ))]
  rw [prodSubsetHomeoA_symm_comp_fibRefl n Y]
  rw [CohMap_comp_apply
        (restrictMap (fibRefl (n+1) Y) (Sph Y (n+1)) (Sph Y (n+1)) (fibRefl_mem_sph (n+1) Y))
        ((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin (n+1))) (mSph (n+1))).symm :
          C(↥(Sph Y (n+1)), Y × MSph (n+1))) ℤ n
        ((relToAbs ℤ (SphB Y n) n).hom (stepSph Y n τ))]

end

end Work.Thom.Orientation
