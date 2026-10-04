import Mathlib
import Submission.Work.Diff.EXT.covKRmExt_eval_bound
import Submission.Work.Diff.EXT.covKRmExt_tensorial
import Submission.Work.Diff.GE.covRic_eq_sum_covRm
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.EXT.covK_linear
import Submission.Work.Diff.EXT.ATower.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The frame-motion correction of the `Ricci` tower cancels

The value `Work.Diff.EXT.covKRmExt g j v X A Z B x` of the `j`-th covariant derivative `∇^j Rm` at
`x`, with the fields `X` (first curvature slot) and `Z` (third curvature slot) varying, is a
*value*-functional: by `Work.Diff.EXT.covKRmExt_tensorial` it depends only on `X x` and `Z x`, and by
`Work.Diff.EXT.covK_linear` it is `ℝ`-linear in each of those two values.

Consequently, for a smooth frame `W` which is `g`-orthonormal near `x`, the two "frame motion"
corrections `Σ_m ∇^jRm(…, ∇_{v}W_m, …, W_m, …)` and `Σ_m ∇^jRm(…, W_m, …, ∇_vW_m, …)` cancel:

* expanding each `∇_v W_m = ∑_k c_{mk} W_k` in the frame and using the value-linearity turns the
  two sums into `∑_{m,k} c_{mk} X_{km}` and `∑_{m,k} c_{mk} X_{mk}`, where
  `X_{uw} = ∇^jRm(…, W_u, …, W_w, …)` and `c_{mk} = g(∇_vW_m, W_k)`;
* `c` is skew-symmetric (`Work.Diff.GE.covRic_frame_skew`, from the constancy of
  `g(W_m, W_k)` near `x`), and a skew-symmetric matrix contracted against *any* matrix vanishes in
  the symmetrised way (`Work.Diff.GE.covRic_skew_sum_zero`).

Note that no *geodesic* frame is needed (the connection `lcOf g` is the Levi-Civita connection of
the *fixed* metric `g`, so `∇_{v} W_m` is the honest derivative of the frame field in the direction
`v = v0 x`).  This is the higher-order analogue of
`Work.Diff.GE.covRic_frame_correction_zero` and of
`Work.Diff.Evol.frame_correction_zero_one/_two`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Diff.EXT.ConnCov.RicTr

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Commons.Geometry.Manifold.VectorField

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Slotwise linearity of `∇^j Rm` at the level of the values -/

/-- **Slotwise linearity of `∇^j Rm` at the level of the values, first curvature slot.**

`covKRmExt g j v (smoothExt x (∑ᵢ cᵢ • uᵢ)) P (smoothExt x w) S x` is the sum
`∑ᵢ cᵢ • covKRmExt g j v (smoothExt x (uᵢ)) P (smoothExt x w) S x`: `∇^j Rm` depends only on the
*values* of its curvature slots (`Work.Diff.EXT.covKRmExt_tensorial`) and is linear in each of them
(`Work.Diff.EXT.covK_linear`). -/
theorem frameCorr_sum_fst
    (hLC : LCSmooth I M) (g : SMet I M) (j : ℕ)
    (v : Fin j → (Π y : M, TangentSpace I y))
    (P S : Π y : M, TangentSpace I y) (x : M)
    (hv : ∀ i, ATower.SmE I M (v i)) (hP : ATower.SmE I M P) (hS : ATower.SmE I M S)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → TangentSpace I x) (w : TangentSpace I x) :
    covKRmExt g j v (smoothExt x (Finset.sum s (fun i => c i • u i))) P (smoothExt x w) S x
      = Finset.sum s (fun i => c i *
          covKRmExt g j v (smoothExt x (u i)) P (smoothExt x w) S x) := by
  classical
  obtain ⟨-, -, hadd1, hsmul1, -, -, -, -, -, -⟩ := covK_linear hLC g j
  have haddv : ∀ a₁ a₂ : TangentSpace I x,
      covKRmExt g j v (smoothExt x (a₁ + a₂)) P (smoothExt x w) S x
        = covKRmExt g j v (smoothExt x a₁) P (smoothExt x w) S x
          + covKRmExt g j v (smoothExt x a₂) P (smoothExt x w) S x := by
    intro a₁ a₂
    have h1 : covKRmExt g j v (smoothExt x (a₁ + a₂)) P (smoothExt x w) S x
        = covKRmExt g j v (smoothExt x a₁ + smoothExt x a₂) P (smoothExt x w) S x :=
      covKRmExt_tensorial hLC j g x v v (smoothExt x (a₁ + a₂))
        (smoothExt x a₁ + smoothExt x a₂) P P (smoothExt x w) (smoothExt x w) S S
        hv hv (Work.Diff.GE.smoothExt_cmdiff x (a₁ + a₂))
        (smoothF_add (Work.Diff.GE.smoothExt_cmdiff x a₁) (Work.Diff.GE.smoothExt_cmdiff x a₂))
        hP hP (Work.Diff.GE.smoothExt_cmdiff x w) (Work.Diff.GE.smoothExt_cmdiff x w) hS hS
        (fun _ => rfl) (by simp only [Pi.add_apply, Work.Diff.GE.smoothExt_apply]) rfl
        (by simp only [Work.Diff.GE.smoothExt_apply]) rfl
    rw [h1]
    have h2 := congrFun (hadd1 v (smoothExt x a₁) (smoothExt x a₂) P (smoothExt x w) S
      hv (Work.Diff.GE.smoothExt_cmdiff x a₁) (Work.Diff.GE.smoothExt_cmdiff x a₂) hP
      (Work.Diff.GE.smoothExt_cmdiff x w) hS) x
    simpa only [Pi.add_apply] using h2
  have hsmulv : ∀ (r : ℝ) (a : TangentSpace I x),
      covKRmExt g j v (smoothExt x (r • a)) P (smoothExt x w) S x
        = r * covKRmExt g j v (smoothExt x a) P (smoothExt x w) S x := by
    intro r a
    have h1 : covKRmExt g j v (smoothExt x (r • a)) P (smoothExt x w) S x
        = covKRmExt g j v ((fun _ : M => r) • smoothExt x a) P (smoothExt x w) S x :=
      covKRmExt_tensorial hLC j g x v v (smoothExt x (r • a))
        ((fun _ : M => r) • smoothExt x a) P P (smoothExt x w) (smoothExt x w) S S
        hv hv (Work.Diff.GE.smoothExt_cmdiff x (r • a))
        (smoothF_smul (contMDiff_const (c := r)) (Work.Diff.GE.smoothExt_cmdiff x a))
        hP hP (Work.Diff.GE.smoothExt_cmdiff x w) (Work.Diff.GE.smoothExt_cmdiff x w) hS hS
        (fun _ => rfl) (by simp only [Pi.smul_apply', Work.Diff.GE.smoothExt_apply]) rfl
        (by simp only [Work.Diff.GE.smoothExt_apply]) rfl
    rw [h1]
    have h2 := congrFun (hsmul1 v (fun _ : M => r) (smoothExt x a) P (smoothExt x w) S
      (contMDiff_const (c := r)) hv (Work.Diff.GE.smoothExt_cmdiff x a) hP
      (Work.Diff.GE.smoothExt_cmdiff x w) hS) x
    simpa only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul] using h2
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]
    have h1 : covKRmExt g j v (smoothExt x (0 : TangentSpace I x)) P (smoothExt x w) S x
        = covKRmExt g j v ((fun _ : M => (0 : ℝ)) • smoothExt x w) P (smoothExt x w) S x :=
      covKRmExt_tensorial hLC j g x v v (smoothExt x (0 : TangentSpace I x))
        ((fun _ : M => (0 : ℝ)) • smoothExt x w) P P (smoothExt x w) (smoothExt x w) S S
        hv hv (Work.Diff.GE.smoothExt_cmdiff x 0)
        (smoothF_smul (contMDiff_const (c := (0 : ℝ))) (Work.Diff.GE.smoothExt_cmdiff x w))
        hP hP (Work.Diff.GE.smoothExt_cmdiff x w) (Work.Diff.GE.smoothExt_cmdiff x w) hS hS
        (fun _ => rfl)
        (by simp only [Pi.smul_apply', Work.Diff.GE.smoothExt_apply, zero_smul]) rfl
        (by simp only [Work.Diff.GE.smoothExt_apply]) rfl
    rw [h1]
    have h2 := congrFun (hsmul1 v (fun _ : M => (0 : ℝ)) (smoothExt x w) P (smoothExt x w) S
      (contMDiff_const (c := (0 : ℝ))) hv (Work.Diff.GE.smoothExt_cmdiff x w) hP
      (Work.Diff.GE.smoothExt_cmdiff x w) hS) x
    simpa only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul, zero_mul] using h2
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [haddv (c a • u a) (Finset.sum t (fun i => c i • u i)), hsmulv (c a) (u a), ih]

/-- **Slotwise linearity of `∇^j Rm` at the level of the values, third curvature slot.**

The analogue of `frameCorr_sum_fst` with the two value slots exchanged: `∇^j Rm` is linear in the
third curvature slot as well. -/
theorem frameCorr_sum_thd
    (hLC : LCSmooth I M) (g : SMet I M) (j : ℕ)
    (v : Fin j → (Π y : M, TangentSpace I y))
    (P S : Π y : M, TangentSpace I y) (x : M)
    (hv : ∀ i, ATower.SmE I M (v i)) (hP : ATower.SmE I M P) (hS : ATower.SmE I M S)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → TangentSpace I x) (w : TangentSpace I x) :
    covKRmExt g j v (smoothExt x w) P (smoothExt x (Finset.sum s (fun i => c i • u i))) S x
      = Finset.sum s (fun i => c i *
          covKRmExt g j v (smoothExt x w) P (smoothExt x (u i)) S x) := by
  classical
  obtain ⟨-, -, -, -, -, -, hadd3, hsmul3, -, -⟩ := covK_linear hLC g j
  have haddv : ∀ a₁ a₂ : TangentSpace I x,
      covKRmExt g j v (smoothExt x w) P (smoothExt x (a₁ + a₂)) S x
        = covKRmExt g j v (smoothExt x w) P (smoothExt x a₁) S x
          + covKRmExt g j v (smoothExt x w) P (smoothExt x a₂) S x := by
    intro a₁ a₂
    have h1 : covKRmExt g j v (smoothExt x w) P (smoothExt x (a₁ + a₂)) S x
        = covKRmExt g j v (smoothExt x w) P (smoothExt x a₁ + smoothExt x a₂) S x :=
      covKRmExt_tensorial hLC j g x v v (smoothExt x w) (smoothExt x w) P P
        (smoothExt x (a₁ + a₂)) (smoothExt x a₁ + smoothExt x a₂) S S
        hv hv (Work.Diff.GE.smoothExt_cmdiff x w) (Work.Diff.GE.smoothExt_cmdiff x w) hP hP
        (Work.Diff.GE.smoothExt_cmdiff x (a₁ + a₂))
        (smoothF_add (Work.Diff.GE.smoothExt_cmdiff x a₁) (Work.Diff.GE.smoothExt_cmdiff x a₂))
        hS hS
        (fun _ => rfl) rfl rfl (by simp only [Pi.add_apply, Work.Diff.GE.smoothExt_apply])
        rfl
    rw [h1]
    have h2 := congrFun (hadd3 v (smoothExt x w) P (smoothExt x a₁) (smoothExt x a₂) S
      hv (Work.Diff.GE.smoothExt_cmdiff x w) hP (Work.Diff.GE.smoothExt_cmdiff x a₁)
      (Work.Diff.GE.smoothExt_cmdiff x a₂) hS) x
    simpa only [Pi.add_apply] using h2
  have hsmulv : ∀ (r : ℝ) (a : TangentSpace I x),
      covKRmExt g j v (smoothExt x w) P (smoothExt x (r • a)) S x
        = r * covKRmExt g j v (smoothExt x w) P (smoothExt x a) S x := by
    intro r a
    have h1 : covKRmExt g j v (smoothExt x w) P (smoothExt x (r • a)) S x
        = covKRmExt g j v (smoothExt x w) P ((fun _ : M => r) • smoothExt x a) S x :=
      covKRmExt_tensorial hLC j g x v v (smoothExt x w) (smoothExt x w) P P
        (smoothExt x (r • a)) ((fun _ : M => r) • smoothExt x a) S S
        hv hv (Work.Diff.GE.smoothExt_cmdiff x w) (Work.Diff.GE.smoothExt_cmdiff x w) hP hP
        (Work.Diff.GE.smoothExt_cmdiff x (r • a))
        (smoothF_smul (contMDiff_const (c := r)) (Work.Diff.GE.smoothExt_cmdiff x a))
        hS hS
        (fun _ => rfl) rfl rfl (by simp only [Pi.smul_apply', Work.Diff.GE.smoothExt_apply])
        rfl
    rw [h1]
    have h2 := congrFun (hsmul3 v (fun _ : M => r) (smoothExt x w) P (smoothExt x a) S
      (contMDiff_const (c := r)) hv (Work.Diff.GE.smoothExt_cmdiff x w) hP
      (Work.Diff.GE.smoothExt_cmdiff x a) hS) x
    simpa only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul] using h2
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]
    have h1 : covKRmExt g j v (smoothExt x w) P (smoothExt x (0 : TangentSpace I x)) S x
        = covKRmExt g j v (smoothExt x w) P ((fun _ : M => (0 : ℝ)) • smoothExt x w) S x :=
      covKRmExt_tensorial hLC j g x v v (smoothExt x w) (smoothExt x w) P P
        (smoothExt x (0 : TangentSpace I x)) ((fun _ : M => (0 : ℝ)) • smoothExt x w) S S
        hv hv (Work.Diff.GE.smoothExt_cmdiff x w) (Work.Diff.GE.smoothExt_cmdiff x w) hP hP
        (Work.Diff.GE.smoothExt_cmdiff x 0)
        (smoothF_smul (contMDiff_const (c := (0 : ℝ))) (Work.Diff.GE.smoothExt_cmdiff x w))
        hS hS
        (fun _ => rfl) rfl rfl
        (by simp only [Pi.smul_apply', Work.Diff.GE.smoothExt_apply, zero_smul]) rfl
    rw [h1]
    have h2 := congrFun (hsmul3 v (fun _ : M => (0 : ℝ)) (smoothExt x w) P (smoothExt x w) S
      (contMDiff_const (c := (0 : ℝ))) hv (Work.Diff.GE.smoothExt_cmdiff x w) hP
      (Work.Diff.GE.smoothExt_cmdiff x w) hS) x
    simpa only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul, zero_mul] using h2
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [haddv (c a • u a) (Finset.sum t (fun i => c i • u i)), hsmulv (c a) (u a), ih]

/-! ## The bridge: only the values matter -/

/-- `∇^j Rm` at `x` depends only on the values of the first and third curvature slots. -/
theorem frameCorr_bridge
    (hLC : LCSmooth I M) (g : SMet I M) (j : ℕ)
    (v : Fin j → (Π y : M, TangentSpace I y))
    (A B : Π y : M, TangentSpace I y) (x : M)
    (hv : ∀ i, ATower.SmE I M (v i)) (hA : ATower.SmE I M A) (hB : ATower.SmE I M B)
    {X Z : Π y : M, TangentSpace I y} (hX : ATower.SmE I M X) (hZ : ATower.SmE I M Z) :
    covKRmExt g j v X A Z B x
      = covKRmExt g j v (smoothExt x (X x)) A (smoothExt x (Z x)) B x :=
  covKRmExt_tensorial hLC j g x v v X (smoothExt x (X x)) A A Z (smoothExt x (Z x)) B B
    hv hv hX (Work.Diff.GE.smoothExt_cmdiff x (X x)) hA hA hZ
    (Work.Diff.GE.smoothExt_cmdiff x (Z x)) hB hB
    (fun _ => rfl) (Work.Diff.GE.smoothExt_apply x (X x)).symm rfl
    (Work.Diff.GE.smoothExt_apply x (Z x)).symm rfl

/-! ## The cancellation -/

theorem frameCorrZero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) (j : ℕ)
    (v : Fin j → (Π y : M, TangentSpace I y)) (v0 A B : Π y : M, TangentSpace I y)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hv : ∀ i, Work.Diff.EXT.ATower.SmE I M (v i))
    (hv0 : Work.Diff.EXT.ATower.SmE I M v0)
    (hA : Work.Diff.EXT.ATower.SmE I M A)
    (hB : Work.Diff.EXT.ATower.SmE I M B)
    (hW : ∀ m, Work.Diff.EXT.ATower.SmE I M (W m))
    (hON : Filter.Eventually (fun y : M => Submission.Diff.IsONFrame g y (fun m => W m y)) (nhds x)) :
    (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g j v (Work.Diff.EXT.dirF g (W m) v0) A (W m) B x))
      + (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g j v (W m) A (Work.Diff.EXT.dirF g (W m) v0) B x)) = 0 := by
  classical
  by_cases hfr : 0 < Module.finrank ℝ E
  · have hONx : Submission.Diff.IsONFrame g x (fun m => W m x) := hON.self_of_nhds
    have hWs : ∀ i, CMDiff ∞ (T% (W i)) := fun i => hW i
    -- the frame-derivative matrix `c m k = g(∇_{v₀}W_m, W_k)` is skew-symmetric
    have hcw : ∀ m k : Fin (Module.finrank ℝ E),
        g.inner x (lcOf g (W m) x (v0 x)) (W k x)
          = - g.inner x (lcOf g (W k) x (v0 x)) (W m x) := by
      intro m k
      have h := Work.Diff.GE.covRic_frame_skew hLC g x (v0 x) W hWs hON m k
      rw [g.symm x (W m x) (lcOf g (W k) x (v0 x))] at h
      linarith
    -- expanding `∇_{v₀}W_m` in the orthonormal frame
    have hexp : ∀ m : Fin (Module.finrank ℝ E),
        lcOf g (W m) x (v0 x)
          = ∑ k, g.inner x (lcOf g (W m) x (v0 x)) (W k x) • W k x :=
      fun m => (Work.Diff.GE.sum_smul_inner_eq_self g x hfr (fun k => W k x) hONx
        (lcOf g (W m) x (v0 x))).symm
    have hterm1 : ∀ m : Fin (Module.finrank ℝ E),
        covKRmExt g j v (dirF g (W m) v0) A (W m) B x
          = ∑ k, g.inner x (lcOf g (W m) x (v0 x)) (W k x)
              * covKRmExt g j v (smoothExt x (W k x)) A (smoothExt x (W m x)) B x := by
      intro m
      have hb : covKRmExt g j v (dirF g (W m) v0) A (W m) B x
          = covKRmExt g j v (smoothExt x (lcOf g (W m) x (v0 x))) A
              (smoothExt x (W m x)) B x := by
        rw [frameCorr_bridge hLC g j v A B x hv hA hB
          (dirF_smooth hLC g (hW m) hv0) (hW m)]
        rfl
      rw [hb]
      conv_lhs => rw [hexp m]
      exact frameCorr_sum_fst hLC g j v A B x hv hA hB Finset.univ
        (fun k => g.inner x (lcOf g (W m) x (v0 x)) (W k x)) (fun k => W k x) (W m x)
    have hterm2 : ∀ m : Fin (Module.finrank ℝ E),
        covKRmExt g j v (W m) A (dirF g (W m) v0) B x
          = ∑ k, g.inner x (lcOf g (W m) x (v0 x)) (W k x)
              * covKRmExt g j v (smoothExt x (W m x)) A (smoothExt x (W k x)) B x := by
      intro m
      have hb : covKRmExt g j v (W m) A (dirF g (W m) v0) B x
          = covKRmExt g j v (smoothExt x (W m x)) A
              (smoothExt x (lcOf g (W m) x (v0 x))) B x := by
        rw [frameCorr_bridge hLC g j v A B x hv hA hB
          (hW m) (dirF_smooth hLC g (hW m) hv0)]
        rfl
      rw [hb]
      conv_lhs => rw [hexp m]
      exact frameCorr_sum_thd hLC g j v A B x hv hA hB Finset.univ
        (fun k => g.inner x (lcOf g (W m) x (v0 x)) (W k x)) (fun k => W k x) (W m x)
    rw [Finset.sum_congr rfl (fun m _ => hterm1 m), Finset.sum_congr rfl (fun m _ => hterm2 m)]
    exact Work.Diff.GE.covRic_skew_sum_zero
      (fun m k => g.inner x (lcOf g (W m) x (v0 x)) (W k x))
      (fun u w => covKRmExt g j v (smoothExt x (W u x)) A (smoothExt x (W w x)) B x) hcw
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hfr
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    simp [Finset.univ_eq_empty]

end Work.Diff.EXT.ConnCov.RicTr
