import Mathlib
import Submission.Work.Isotopy.Basic
import Submission.Work.Isotopy.Linear

/-!
# Smooth ambient isotopies of `ℝ^N`

The topological `AmbientIsotopy` of `Submission/Work/Isotopy/Basic.lean` is what an *isotopy
extension theorem* produces.  For gluing arguments one needs the smooth structure as well: the
images of an embedded manifold under the time slices have to stay smooth submanifolds.

Here we introduce

* `Work.Isotopy.SmoothAmbientIsotopy N`, a smooth family of self-embeddings of `ℝ^N` starting at
  the identity, together with the time-slice smoothness `SmoothAmbientIsotopy.contMDiff_apply` and
  composition;
* the two explicit examples used in "without loss of generality" moves: translations
  (`SmoothAmbientIsotopy.translation`) and dilations by a positive factor
  (`SmoothAmbientIsotopy.dilation`).
-/

open scoped Manifold ContDiff
open Topology Set Function

namespace Work.Isotopy

/-- A **smooth ambient isotopy** of `ℝ^N`: a smooth family `t ↦ Ψ t` of self-embeddings of `ℝ^N`
with `Ψ 0 = id`. -/
structure SmoothAmbientIsotopy (N : ℕ) where
  /-- The family of maps. -/
  toFun : ℝ → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)
  /-- Joint smoothness in the time and space variables. -/
  contMDiff_uncurry : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 N) ∞ (Function.uncurry toFun)
  /-- Every time slice is an embedding. -/
  isEmbedding_apply : ∀ t, IsEmbedding (toFun t)
  /-- At time `0` the isotopy is the identity. -/
  map_zero : toFun 0 = id

namespace SmoothAmbientIsotopy

variable {N : ℕ}

instance : CoeFun (SmoothAmbientIsotopy N)
    fun _ => ℝ → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) :=
  ⟨fun Φ => Φ.toFun⟩

@[simp]
theorem map_zero_apply (Φ : SmoothAmbientIsotopy N) (x : EuclideanSpace ℝ (Fin N)) :
    Φ 0 x = x := by
  have h := congrFun Φ.map_zero x
  simpa using h

/-- Every time slice of a smooth ambient isotopy is smooth. -/
theorem contMDiff_apply (Φ : SmoothAmbientIsotopy N) (t : ℝ) :
    ContMDiff (𝓡 N) (𝓡 N) ∞ (Φ t) := by
  have h1 : ContMDiff (𝓡 N) ((𝓘(ℝ, ℝ)).prod (𝓡 N)) ∞
      (fun x : EuclideanSpace ℝ (Fin N) => ((t : ℝ), x)) :=
    ContMDiff.prodMk contMDiff_const contMDiff_id
  have h2 : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) (𝓡 N) ∞
      (Function.uncurry Φ.toFun) := Φ.contMDiff_uncurry
  exact h2.comp h1

/-- Composition of smooth ambient isotopies (first `Φ`, then `Ψ`). -/
noncomputable def comp (Ψ Φ : SmoothAmbientIsotopy N) : SmoothAmbientIsotopy N where
  toFun t := Ψ t ∘ Φ t
  contMDiff_uncurry := by
    have hm : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 N)) ((𝓘(ℝ, ℝ)).prod (𝓡 N)) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => (p.1, Function.uncurry Φ.toFun p)) :=
      ContMDiff.prodMk contMDiff_fst Φ.contMDiff_uncurry
    exact Ψ.contMDiff_uncurry.comp hm
  isEmbedding_apply t := (Ψ.isEmbedding_apply t).comp (Φ.isEmbedding_apply t)
  map_zero := by
    funext x
    simp

@[simp]
theorem comp_apply (Ψ Φ : SmoothAmbientIsotopy N) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : (Ψ.comp Φ) t x = Ψ t (Φ t x) := rfl

/-- Translation by `t • v` at time `t`. -/
noncomputable def translation (v : EuclideanSpace ℝ (Fin N)) : SmoothAmbientIsotopy N where
  toFun t x := x + t • v
  contMDiff_uncurry := by
    have h : Function.uncurry (fun t (x : EuclideanSpace ℝ (Fin N)) => x + t • v) =
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => p.2 + p.1 • v) := rfl
    rw [h]
    exact contMDiff_snd.add (contMDiff_fst.smul contMDiff_const)
  isEmbedding_apply t := by
    let e : EuclideanSpace ℝ (Fin N) ≃ₜ EuclideanSpace ℝ (Fin N) :=
      { toFun := fun x => x + t • v
        invFun := fun y => y - t • v
        left_inv := by intro x; simp
        right_inv := by intro y; simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact e.isEmbedding
  map_zero := by
    funext x
    simp

@[simp]
theorem translation_apply (v : EuclideanSpace ℝ (Fin N)) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin N)) : translation v t x = x + t • v := rfl

/-- The dilation isotopy by a positive factor `ε`: identity at time `0`, `x ↦ ε • x` at time `1`. -/
noncomputable def dilation (ε : ℝ) (hε : 0 < ε) : SmoothAmbientIsotopy N where
  toFun t x := AmbientIsotopy.dilationScale ε t • x
  contMDiff_uncurry := by
    have hscale : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (AmbientIsotopy.dilationScale ε) :=
      (show ContDiff ℝ ∞ (AmbientIsotopy.dilationScale ε) from by
        unfold AmbientIsotopy.dilationScale
        exact contDiff_const.add (Real.smoothTransition.contDiff.mul contDiff_const)).contMDiff
    have h : Function.uncurry (fun t (x : EuclideanSpace ℝ (Fin N)) =>
        AmbientIsotopy.dilationScale ε t • x) =
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => AmbientIsotopy.dilationScale ε p.1 • p.2) := rfl
    rw [h]
    exact (hscale.comp contMDiff_fst).smul contMDiff_snd
  isEmbedding_apply t := by
    have hc : AmbientIsotopy.dilationScale ε t ≠ 0 :=
      ne_of_gt (AmbientIsotopy.dilationScale_pos hε t)
    let e : EuclideanSpace ℝ (Fin N) ≃ₜ EuclideanSpace ℝ (Fin N) :=
      { toFun := fun x => AmbientIsotopy.dilationScale ε t • x
        invFun := fun y => (AmbientIsotopy.dilationScale ε t)⁻¹ • y
        left_inv := by
          intro x
          show (AmbientIsotopy.dilationScale ε t)⁻¹ •
            (AmbientIsotopy.dilationScale ε t • x) = x
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        right_inv := by
          intro y
          show AmbientIsotopy.dilationScale ε t •
            ((AmbientIsotopy.dilationScale ε t)⁻¹ • y) = y
          rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact e.isEmbedding
  map_zero := by
    funext x
    simp

@[simp]
theorem dilation_apply (ε : ℝ) (hε : 0 < ε) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin N)) :
    dilation ε hε t x = AmbientIsotopy.dilationScale ε t • x := rfl

theorem dilation_apply_one (ε : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin N)) :
    dilation ε hε 1 x = ε • x := by
  simp [AmbientIsotopy.dilationScale_one]

end SmoothAmbientIsotopy

end Work.Isotopy
