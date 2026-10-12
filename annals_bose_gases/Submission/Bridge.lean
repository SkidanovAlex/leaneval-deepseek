import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Calculus.FDeriv.Pi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open _root_.BoseGases
open Filter MeasureTheory Laplacian
open scoped NNReal ContDiff Topology Real

namespace Submission.BoseGases

/-!
Bridge between the partial Laplacian (defined through slices with the Laplacian on
`EuclideanSpace ℝ (Fin 3)`) and second directional derivatives of `f` along the
coordinate directions of the full space `Fin N → EuclideanSpace ℝ (Fin 3)`.
-/

/-- Coordinate unit vectors of `EuclideanSpace ℝ (Fin 3)`, indexed by `Fin 3`. -/
noncomputable def euclBasis3Equiv : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ≃ Fin 3 :=
  Equiv.cast (by rw [finrank_euclideanSpace, Fintype.card_fin])

/-- The standard orthonormal basis of `EuclideanSpace ℝ (Fin 3)`, reindexed by `Fin 3`. -/
noncomputable def euclBasis3 : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 3))).reindex euclBasis3Equiv

/-- The `k`-th coordinate unit vector of `EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def coordBasis (k : Fin 3) : EuclideanSpace ℝ (Fin 3) := euclBasis3 k

/-- The direction of the second derivative w.r.t. the `k`-th coordinate of the `i`-th particle:
the vector of the full space which is the `k`-th coordinate vector in slot `i` and `0` elsewhere. -/
noncomputable def coordDir (N : ℕ) (i : Fin N) (k : Fin 3) : Fin N → EuclideanSpace ℝ (Fin 3) :=
  fun j => if j = i then coordBasis k else 0

/-! ## Local abbreviations and auxiliary lemmas -/

/-- The slice space: one particle's position space. -/
abbrev bridgeE3 := EuclideanSpace ℝ (Fin 3)

/-- The full space of `N` particle positions. -/
abbrev bridgeFull (N : ℕ) := Fin N → bridgeE3

/-- The derivative of `z ↦ Function.update x i z` at any point `y` applied to `e` is the
insertion of `e` into slot `i` with zeros elsewhere. -/
lemma bridgeFderivUpdate (N : ℕ) (i : Fin N) (x : bridgeFull N) (y e : bridgeE3) :
    fderiv ℝ (fun z : bridgeE3 => Function.update x i z) y e =
      Function.update (0 : bridgeFull N) i e := by
  change (fderiv ℝ (Function.update x i) y) e = Function.update (0 : bridgeFull N) i e
  rw [fderiv_update]
  ext j
  simp [Function.update]
  by_cases h : j = i
  · subst j; simp
  · simp [h]

/-- A `C²` function has `C¹` Fréchet derivative. -/
lemma bridgeContDiffFderivOne (N : ℕ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : bridgeFull N → F} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (fderiv ℝ f) := by
  have hf' : ContDiff ℝ (1 + 1) f := by
    convert hf using 1
    norm_num
  exact (contDiff_succ_iff_fderiv (n := 1) (f := f)).mp hf' |>.2.2

/-- The second iterated derivative in direction `b` equals the derivative of
`z ↦ fderiv f z b`, applied to `b` (for `C²` functions). -/
lemma bridgeSecondDirIteratedFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {b : E} (hf : ContDiff ℝ 2 f) :
    iteratedFDeriv ℝ 2 f x ![b, b] = fderiv ℝ (fun z => fderiv ℝ f z b) x b := by
  rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' (n := 1) (m := ![b, b])]
  · simp
  · have h := (ContDiff.differentiable_iteratedFDeriv (f := f) (n := (2 : ℕ)) (m := 1) (by norm_num) hf)
    exact h.differentiableAt

/-- The slice `z ↦ f (Function.update x i z)` is `C²` whenever `f` is `C²`. -/
lemma bridgeSliceContDiff (N : ℕ) (i : Fin N) (x : bridgeFull N) {f : bridgeFull N → ℝ}
    (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (fun y : bridgeE3 => f (Function.update x i y)) := by
  change ContDiff ℝ 2 (f ∘ (fun y : bridgeE3 => Function.update x i y))
  exact hf.comp (by
    change ContDiff ℝ 2 (Function.update x i)
    exact contDiff_update 2 x i)

/-- First derivative of the slice: the derivative of the slice in direction `e` is the
derivative of `f` in the direction that puts `e` into slot `i`. -/
lemma bridgeSliceFderivApply (N : ℕ) (i : Fin N) (x : bridgeFull N) {f : bridgeFull N → ℝ}
    (hf : ContDiff ℝ 2 f) (y e : bridgeE3) :
    fderiv ℝ (fun z : bridgeE3 => f (Function.update x i z)) y e =
      fderiv ℝ f (Function.update x i y) (Function.update (0 : bridgeFull N) i e) := by
  have hT2 : ContDiff ℝ 2 (fun z : bridgeE3 => Function.update x i z) := by
    change ContDiff ℝ 2 (Function.update x i)
    exact contDiff_update 2 x i
  have hT : DifferentiableAt ℝ (fun z : bridgeE3 => Function.update x i z) y :=
    (hT2.differentiable (by norm_num)).differentiableAt
  have hfd : DifferentiableAt ℝ f (Function.update x i y) :=
    (hf.differentiable (by norm_num)).differentiableAt
  have hcomp0 := fderiv_comp (x := y) (f := (fun z : bridgeE3 => Function.update x i z)) (g := f) hfd hT
  calc
    fderiv ℝ (fun z : bridgeE3 => f (Function.update x i z)) y e
        = ((fderiv ℝ f (Function.update x i y)).comp
            (fderiv ℝ (fun z : bridgeE3 => Function.update x i z) y)) e := by
          change (fderiv ℝ (f ∘ (fun z : bridgeE3 => Function.update x i z)) y) e = _
          rw [hcomp0]
    _ = fderiv ℝ f (Function.update x i y) (Function.update (0 : bridgeFull N) i e) := by
          simp
          rw [bridgeFderivUpdate N i x y e]

/-- One summand of the bridge identity: the second directional derivative of the slice
along the `k`-th coordinate equals the corresponding second directional derivative of `f`
in the full space along `coordDir N i k`. -/
lemma bridgeSliceSecondDirTerm (N : ℕ) (i : Fin N) (x : bridgeFull N) {f : bridgeFull N → ℝ}
    (hf : ContDiff ℝ 2 f) (k : Fin 3) :
    fderiv ℝ (fun y : bridgeE3 =>
        fderiv ℝ (fun z : bridgeE3 => f (Function.update x i z)) y (euclBasis3 k)) (x i)
        (euclBasis3 k) =
      (fderiv ℝ (fun z : bridgeFull N => fderiv ℝ f z (coordDir N i k)) x) (coordDir N i k) := by
  let T : bridgeE3 → bridgeFull N := fun y => Function.update x i y
  let v : bridgeFull N := coordDir N i k
  let h : bridgeFull N → ℝ := fun w => fderiv ℝ f w v
  have hT2 : ContDiff ℝ 2 T := by
    dsimp [T]
    change ContDiff ℝ 2 (Function.update x i)
    exact contDiff_update 2 x i
  have hfd_h : DifferentiableAt ℝ h (T (x i)) := by
    have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := bridgeContDiffFderivOne N hf
    have heval : ContDiff ℝ 1 (fun (L : bridgeFull N →L[ℝ] ℝ) => L v) := by
      exact (ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) v : (bridgeFull N →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff
    have hcont : ContDiff ℝ 1 (fun w : bridgeFull N => fderiv ℝ f w v) := by
      change ContDiff ℝ 1 ((fun (L : bridgeFull N →L[ℝ] ℝ) => L v) ∘ (fun w : bridgeFull N => fderiv ℝ f w))
      exact heval.comp hf1
    dsimp [h]
    exact (hcont.differentiable (by norm_num)) (T (x i))
  have hTdiff : DifferentiableAt ℝ T (x i) := (hT2.differentiable (by norm_num)).differentiableAt
  have hchain := fderiv_comp (x := x i) (f := T) (g := h) hfd_h hTdiff
  have hfun :
      (fun y : bridgeE3 => fderiv ℝ (fun z : bridgeE3 => f (Function.update x i z)) y (euclBasis3 k)) =
        h ∘ T := by
    funext y
    rw [bridgeSliceFderivApply N i x hf y (euclBasis3 k)]
    have hu : Function.update (0 : bridgeFull N) i (euclBasis3 k) = v := by
      dsimp [v]
      ext j
      by_cases hj : j = i <;> simp [coordDir, coordBasis, Function.update, hj]
    rw [hu]
    rfl
  calc
    fderiv ℝ (fun y : bridgeE3 =>
        fderiv ℝ (fun z : bridgeE3 => f (Function.update x i z)) y (euclBasis3 k)) (x i)
        (euclBasis3 k)
        = fderiv ℝ (h ∘ T) (x i) (euclBasis3 k) := by rw [hfun]
    _ = fderiv ℝ h (T (x i)) (fderiv ℝ T (x i) (euclBasis3 k)) := by
          rw [hchain]
          rfl
    _ = (fderiv ℝ (fun z : bridgeFull N => fderiv ℝ f z (coordDir N i k)) x) (coordDir N i k) := by
          have hTx : T (x i) = x := by
            dsimp [T]
            simp
          rw [hTx]
          have hdT : fderiv ℝ T (x i) (euclBasis3 k) = v := by
            dsimp [T, v]
            rw [bridgeFderivUpdate N i x (x i) (euclBasis3 k)]
            ext j
            by_cases hj : j = i <;> simp [coordDir, coordBasis, hj]
          rw [hdT]

/--
The partial Laplacian of the `i`-th particle is the sum over the three space coordinates of the
second derivatives of `f` in the corresponding coordinate directions:
`Δ[i] f x = ∑ k, (fderiv (fun z ↦ fderiv f z (coordDir N i k)) x) (coordDir N i k)`.

No differentiability assumption is needed for the Laplacian part, but the chain rule for the
second derivative of the slice requires `ContDiff ℝ 2 f`.
-/
lemma partialLaplacian_eq_sum_secondDir (N : ℕ) (i : Fin N) {f : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hf : ContDiff ℝ 2 f) :
    partialLaplacian i f = fun x =>
      ∑ k : Fin 3,
        (fderiv ℝ (fun z : Fin N → EuclideanSpace ℝ (Fin 3) => fderiv ℝ f z (coordDir N i k)) x)
          (coordDir N i k) := by
  ext x
  let g : bridgeE3 → ℝ := fun y => f (Function.update x i y)
  have hg : ContDiff ℝ 2 g := by
    dsimp [g]
    exact bridgeSliceContDiff N i x hf
  calc
    partialLaplacian i f x = Δ g (x i) := by
          dsimp [partialLaplacian, g]
    _ = ∑ k : Fin 3, iteratedFDeriv ℝ 2 g (x i) ![euclBasis3 k, euclBasis3 k] := by
          rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := g) euclBasis3]
    _ = ∑ k : Fin 3,
          (fderiv ℝ (fun z : bridgeFull N => fderiv ℝ f z (coordDir N i k)) x) (coordDir N i k) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [bridgeSecondDirIteratedFDeriv (f := g) (x := x i) (b := euclBasis3 k) hg]
          dsimp [g]
          exact bridgeSliceSecondDirTerm N i x hf k

end Submission.BoseGases
