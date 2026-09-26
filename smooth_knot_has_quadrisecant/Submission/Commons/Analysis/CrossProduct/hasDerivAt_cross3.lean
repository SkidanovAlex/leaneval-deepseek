import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct

set_option linter.unnecessarySeqFocus false

open scoped Matrix

noncomputable section

namespace Commons.Analysis.CrossProduct

/-- A differentiable curve into `EuclideanSpace ℝ (Fin 3)` has differentiable
coordinate functions. -/
lemma hasDerivAt_cross3_coord (u : ℝ → EuclideanSpace ℝ (Fin 3)) {du : EuclideanSpace ℝ (Fin 3)}
    {a : ℝ} (hu : HasDerivAt u du a) (i : Fin 3) :
    HasDerivAt (fun x : ℝ => (u x) i) (du i) a := by
  rw [hasDerivAt_iff_hasFDerivAt]
  have hf := hu.hasFDerivAt
  have hp' :
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => (y : EuclideanSpace ℝ (Fin 3)) i)
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) (u a) :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (u a) i
  have hcomp : HasFDerivAt (fun x : ℝ => (u x) i)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) ∘L
        ContinuousLinearMap.toSpanSingleton ℝ du) a :=
    hp'.comp a hf
  have hderiv_eq :
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) ∘L
          ContinuousLinearMap.toSpanSingleton ℝ du =
        ContinuousLinearMap.toSpanSingleton ℝ (du i) := by
    rw [ContinuousLinearMap.comp_toSpanSingleton]
    rfl
  simpa [hderiv_eq] using hcomp

/-- Coordinatewise differentiability of a map into `Fin 3 → ℝ` gives
differentiability of its `WithLp`-lift into `EuclideanSpace ℝ (Fin 3)`. -/
lemma hasDerivAt_cross3_lift {w : ℝ → Fin 3 → ℝ} {d : Fin 3 → ℝ} {a : ℝ}
    (hw : ∀ i : Fin 3, HasDerivAt (fun x : ℝ => w x i) (d i) a) :
    HasDerivAt (fun x : ℝ => WithLp.toLp 2 (w x)) (WithLp.toLp 2 d) a := by
  rw [hasDerivAt_iff_hasFDerivAt]
  rw [← hasFDerivWithinAt_univ]
  refine (hasFDerivWithinAt_piLp (𝕜 := ℝ) (H := ℝ) (E := fun _ : Fin 3 => ℝ) (p := 2)
    (f := fun x : ℝ => WithLp.toLp 2 (w x))
    (f' := ContinuousLinearMap.toSpanSingleton ℝ (WithLp.toLp 2 d))
    (t := (Set.univ : Set ℝ)) (y := a)).2 ?_
  intro i
  rw [hasFDerivWithinAt_univ]
  have hdi : HasDerivAt (fun x : ℝ => w x i) (d i) a := hw i
  have hdi' : HasFDerivAt (fun x : ℝ => w x i)
      (ContinuousLinearMap.toSpanSingleton ℝ (d i)) a :=
    hasDerivAt_iff_hasFDerivAt.mp hdi
  have hderiv_eq :
      PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i ∘L
          ContinuousLinearMap.toSpanSingleton ℝ (WithLp.toLp 2 d) =
        ContinuousLinearMap.toSpanSingleton ℝ (d i) := by
    rw [ContinuousLinearMap.comp_toSpanSingleton]
    rfl
  simpa [hderiv_eq] using hdi'

/-- The derivative (Leibniz rule) of the cross product of two differentiable
curves in `EuclideanSpace ℝ (Fin 3)`. -/
theorem hasDerivAt_cross3 (u v : ℝ → EuclideanSpace ℝ (Fin 3))
    {du dv : EuclideanSpace ℝ (Fin 3)} {t : ℝ}
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) :
    HasDerivAt
      (fun x : ℝ => WithLp.toLp 2 (WithLp.ofLp (u x) ⨯₃ WithLp.ofLp (v x)))
      (WithLp.toLp 2 (WithLp.ofLp du ⨯₃ WithLp.ofLp (v t)) +
        WithLp.toLp 2 (WithLp.ofLp (u t) ⨯₃ WithLp.ofLp dv)) t := by
  let w : ℝ → Fin 3 → ℝ := fun x => WithLp.ofLp (u x) ⨯₃ WithLp.ofLp (v x)
  let d : Fin 3 → ℝ :=
    WithLp.ofLp du ⨯₃ WithLp.ofLp (v t) + WithLp.ofLp (u t) ⨯₃ WithLp.ofLp dv
  have hw : ∀ i : Fin 3, HasDerivAt (fun x : ℝ => w x i) (d i) t := by
    intro i
    fin_cases i
    · dsimp [w, d]
      have hu1 : HasDerivAt (fun x : ℝ => (u x) 1) (du 1) t := hasDerivAt_cross3_coord u hu 1
      have hu2 : HasDerivAt (fun x : ℝ => (u x) 2) (du 2) t := hasDerivAt_cross3_coord u hu 2
      have hv1 : HasDerivAt (fun x : ℝ => (v x) 1) (dv 1) t := hasDerivAt_cross3_coord v hv 1
      have hv2 : HasDerivAt (fun x : ℝ => (v x) 2) (dv 2) t := hasDerivAt_cross3_coord v hv 2
      have h1 : HasDerivAt (fun x : ℝ => (u x) 1 * (v x) 2)
          (du 1 * (v t) 2 + (u t) 1 * dv 2) t := HasDerivAt.mul hu1 hv2
      have h2 : HasDerivAt (fun x : ℝ => (u x) 2 * (v x) 1)
          (du 2 * (v t) 1 + (u t) 2 * dv 1) t := HasDerivAt.mul hu2 hv1
      have hsub : HasDerivAt (fun x : ℝ => (u x) 1 * (v x) 2 - (u x) 2 * (v x) 1)
          (du 1 * (v t) 2 + (u t) 1 * dv 2 - (du 2 * (v t) 1 + (u t) 2 * dv 1)) t :=
        h1.sub h2
      convert hsub using 1 <;> simp [cross_apply] <;> ring_nf
    · dsimp [w, d]
      have hu0 : HasDerivAt (fun x : ℝ => (u x) 0) (du 0) t := hasDerivAt_cross3_coord u hu 0
      have hu2 : HasDerivAt (fun x : ℝ => (u x) 2) (du 2) t := hasDerivAt_cross3_coord u hu 2
      have hv0 : HasDerivAt (fun x : ℝ => (v x) 0) (dv 0) t := hasDerivAt_cross3_coord v hv 0
      have hv2 : HasDerivAt (fun x : ℝ => (v x) 2) (dv 2) t := hasDerivAt_cross3_coord v hv 2
      have h1 : HasDerivAt (fun x : ℝ => (u x) 2 * (v x) 0)
          (du 2 * (v t) 0 + (u t) 2 * dv 0) t := HasDerivAt.mul hu2 hv0
      have h2 : HasDerivAt (fun x : ℝ => (u x) 0 * (v x) 2)
          (du 0 * (v t) 2 + (u t) 0 * dv 2) t := HasDerivAt.mul hu0 hv2
      have hsub : HasDerivAt (fun x : ℝ => (u x) 2 * (v x) 0 - (u x) 0 * (v x) 2)
          (du 2 * (v t) 0 + (u t) 2 * dv 0 - (du 0 * (v t) 2 + (u t) 0 * dv 2)) t :=
        h1.sub h2
      convert hsub using 1 <;> simp [cross_apply] <;> ring_nf
    · dsimp [w, d]
      have hu0 : HasDerivAt (fun x : ℝ => (u x) 0) (du 0) t := hasDerivAt_cross3_coord u hu 0
      have hu1 : HasDerivAt (fun x : ℝ => (u x) 1) (du 1) t := hasDerivAt_cross3_coord u hu 1
      have hv0 : HasDerivAt (fun x : ℝ => (v x) 0) (dv 0) t := hasDerivAt_cross3_coord v hv 0
      have hv1 : HasDerivAt (fun x : ℝ => (v x) 1) (dv 1) t := hasDerivAt_cross3_coord v hv 1
      have h1 : HasDerivAt (fun x : ℝ => (u x) 0 * (v x) 1)
          (du 0 * (v t) 1 + (u t) 0 * dv 1) t := HasDerivAt.mul hu0 hv1
      have h2 : HasDerivAt (fun x : ℝ => (u x) 1 * (v x) 0)
          (du 1 * (v t) 0 + (u t) 1 * dv 0) t := HasDerivAt.mul hu1 hv0
      have hsub : HasDerivAt (fun x : ℝ => (u x) 0 * (v x) 1 - (u x) 1 * (v x) 0)
          (du 0 * (v t) 1 + (u t) 0 * dv 1 - (du 1 * (v t) 0 + (u t) 1 * dv 0)) t :=
        h1.sub h2
      convert hsub using 1 <;> simp [cross_apply] <;> ring_nf
  exact hasDerivAt_cross3_lift hw

end Commons.Analysis.CrossProduct