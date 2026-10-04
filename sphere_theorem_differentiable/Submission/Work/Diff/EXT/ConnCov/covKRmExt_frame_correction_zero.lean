import Mathlib
import Submission.Work.Diff.EXT.covKRmExt_eval_bound
import Submission.Work.Diff.EXT.covKRmExt_tensorial
import Submission.Work.Diff.GE.covRic_eq_sum_covRm
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.EXT.covK_linear

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The frame-correction sums of `∇^k Rm` cancel

For a smooth metric `g` with Levi-Civita connection, a smooth field `v0`, and a family of smooth
fields `W m` which is `g`-orthonormal near `x`, the two families of *frame corrections*

`∑_m (∇^k Rm)(∇_{v0} W_m, A, W_m, B)` and `∑_m (∇^k Rm)(W_m, A, ∇_{v0} W_m, B)`

cancel.  This is the higher-order analogue of `Work.Diff.GE.covRic_frame_correction_zero`
(the `k = 0` case, `∇^k Rm = Rm` with `B = v`).

## Proof

Write `U_m := ∇_{v0}W_m(x)`.  Since `W` is orthonormal near `x` and `g` is compatible with its
Levi-Civita connection, the pairing `y ↦ g(W_m y, W_p y)` is *constant* near `x`, so its derivative
in direction `v0 x` vanishes; the Leibniz rule gives the skew-symmetry
`c m p := g(U_m, W_p x) = - c p m` (`Work.Diff.GE.covRic_frame_skew`).

Expanding `U_m` in the orthonormal frame (`Work.Diff.GE.sum_smul_inner_eq_self`) and using
(i) the value-dependence (`Work.Diff.EXT.covKRmExt_tensorial`, i.e. `∇^k Rm` is a tensor) and
(ii) the `C^∞(M)`-linearity of `∇^k Rm` in its field slots (`Work.Diff.EXT.covK_linear`) we get

`∑_m (∇^k Rm)(U_m, A, W_m, B) + ∑_m (∇^k Rm)(W_m, A, U_m, B)
   = ∑_{m,p} c m p · [F p m + F m p]`

with `F u w = (∇^k Rm)(W_u, A, W_w, B)`.  The double sum vanishes because `c` is skew-symmetric
and the bracket is symmetric in `(m,p)` (renaming the summation indices).
-/

open scoped BigOperators Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.Diff.EXT.ConnCov

/-! ## Two elementary lemmas about linear functionals on fields -/

/-- A finite linear combination `∑ p ∈ S, c p • Y p` of smooth fields (with constant coefficients)
is smooth.  The extra field `w0` handles the empty sum. -/
theorem smooth_sum_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    {ι : Type*} (Y : ι → Work.Diff.EXT.TField (I := I) (M := M))
    (hY : ∀ p, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Y p))
    (w0 : Work.Diff.EXT.TField (I := I) (M := M))
    (hw0 : Work.Diff.GE.SmoothFieldT (I := I) (M := M) w0)
    (c : ι → ℝ) (S : Finset ι) :
    Work.Diff.GE.SmoothFieldT (I := I) (M := M) (∑ p ∈ S, c p • Y p) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have h0 : (∑ p ∈ (∅ : Finset ι), c p • Y p)
          = (fun _ : M => (0 : ℝ)) • w0 := by
        funext z; simp
      rw [h0]
      exact Work.Diff.EXT.smoothF_smul (contMDiff_const (c := (0 : ℝ))) hw0
  | insert p S hp ih =>
      have h0 : (∑ q ∈ insert p S, c q • Y q)
          = (fun _ : M => c p) • Y p + (∑ q ∈ S, c q • Y q) := by
        funext z; rw [Finset.sum_insert hp]; rfl
      rw [h0]
      exact Work.Diff.EXT.smoothF_add
        (Work.Diff.EXT.smoothF_smul (contMDiff_const (c := c p)) (hY p)) ih

/-- If a functional `T` on fields is additive and `C^∞(M)`-homogeneous, then its value on a finite
linear combination of fields is the corresponding linear combination of its values. -/
theorem linear_apply_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    {ι : Type*} (Y : ι → Work.Diff.EXT.TField (I := I) (M := M))
    (hY : ∀ p, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (Y p))
    (w0 : Work.Diff.EXT.TField (I := I) (M := M))
    (hw0 : Work.Diff.GE.SmoothFieldT (I := I) (M := M) w0)
    (c : ι → ℝ) (S : Finset ι)
    (T : Work.Diff.EXT.TField (I := I) (M := M) → (M → ℝ))
    (hadd : ∀ X X' : Work.Diff.EXT.TField (I := I) (M := M),
      Work.Diff.GE.SmoothFieldT (I := I) (M := M) X →
      Work.Diff.GE.SmoothFieldT (I := I) (M := M) X' → T (X + X') = T X + T X')
    (hsmul : ∀ (f : M → ℝ), CMDiff ∞ f → ∀ X : Work.Diff.EXT.TField (I := I) (M := M),
      Work.Diff.GE.SmoothFieldT (I := I) (M := M) X → T (f • X) = f • T X)
    (y : M) :
    T (∑ p ∈ S, c p • Y p) y = ∑ p ∈ S, c p * T (Y p) y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have h0 : (∑ p ∈ (∅ : Finset ι), c p • Y p)
          = (fun _ : M => (0 : ℝ)) • w0 := by
        funext z; simp
      rw [h0, hsmul (fun _ : M => (0 : ℝ)) (contMDiff_const (c := (0 : ℝ))) w0 hw0]
      simp
  | insert p S hp ih =>
      have h0 : (∑ q ∈ insert p S, c q • Y q)
          = (fun _ : M => c p) • Y p + (∑ q ∈ S, c q • Y q) := by
        funext z; rw [Finset.sum_insert hp]; rfl
      have hS : Work.Diff.GE.SmoothFieldT (I := I) (M := M) (∑ q ∈ S, c q • Y q) :=
        smooth_sum_smul Y hY w0 hw0 c S
      rw [h0, hadd ((fun _ : M => c p) • Y p) (∑ q ∈ S, c q • Y q)
            (Work.Diff.EXT.smoothF_smul (contMDiff_const (c := c p)) (hY p)) hS,
          hsmul (fun _ : M => c p) (contMDiff_const (c := c p)) (Y p) (hY p)]
      simp only [Pi.add_apply, Pi.mul_apply, smul_eq_mul]
      rw [ih, Finset.sum_insert hp]

/-- For a skew-symmetric matrix `c` and any `F`, `∑_{p,q} c_{pq}(F_{qp} + F_{pq}) = 0`. -/
theorem skew_double_sum_zero {ι : Type*} [Fintype ι] (c F : ι → ι → ℝ)
    (hskew : ∀ p q, c p q = - c q p) :
    (∑ p, ∑ q, c p q * F q p) + (∑ p, ∑ q, c p q * F p q) = 0 := by
  have h : (∑ p, ∑ q, c p q * F q p) = - (∑ p, ∑ q, c p q * F p q) := by
    rw [Finset.sum_comm]
    rw [show (∑ q, ∑ p, c p q * F q p) = ∑ p, ∑ q, c q p * F p q from rfl]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hskew p q]; ring
  linarith

theorem covKRmExt_frame_correction_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) (j : ℕ)
    (v : Fin j → (Π y : M, TangentSpace I y)) (v0 A B : Π y : M, TangentSpace I y)
    (W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hv : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (v i))
    (hv0 : Work.Diff.GE.SmoothFieldT (I := I) (M := M) v0)
    (hA : Work.Diff.GE.SmoothFieldT (I := I) (M := M) A)
    (hB : Work.Diff.GE.SmoothFieldT (I := I) (M := M) B)
    (hW : ∀ m, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (W m))
    (hON : Filter.Eventually (fun y : M => Submission.Diff.IsONFrame g y (fun m => W m y)) (nhds x)) :
    (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g j v (Work.Diff.EXT.dirF g (W m) v0) A (W m) B x))
      + (Finset.univ.sum (fun m => Work.Diff.EXT.covKRmExt g j v (W m) A (Work.Diff.EXT.dirF g (W m) v0) B x)) = 0 := by
  classical
  by_cases hn : 0 < Module.finrank ℝ E
  · have hONx : Submission.Diff.IsONFrame g x (fun m => W m x) := hON.self_of_nhds
    -- skew-symmetry of the frame-derivative pairing
    have hskew : ∀ m k : Fin (Module.finrank ℝ E),
        g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W k x)
          = - g.inner x (Submission.Diff.lcOf g (W k) x (v0 x)) (W m x) := by
      intro m k
      have h := Work.Diff.GE.covRic_frame_skew hLC g x (v0 x) W (fun i => hW i) hON m k
      rw [g.symm x (W m x) (Submission.Diff.lcOf g (W k) x (v0 x))] at h
      linarith
    -- expansion of `∇_{v0}W_m` in the orthonormal frame
    have hexp : ∀ m : Fin (Module.finrank ℝ E),
        (Work.Diff.EXT.dirF g (W m) v0) x
          = ∑ k, g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W k x) • W k x := by
      intro m
      have h := Work.Diff.GE.sum_smul_inner_eq_self g x hn (fun k => W k x) hONx
        ((Submission.Diff.lcOf g (W m) x) (v0 x))
      simpa only [Work.Diff.EXT.dirF] using h.symm
    -- linearity of the tower in the first and in the third curvature slot
    obtain ⟨_, _, haddA, hsmulA, _, _, haddC, hsmulC, _, _⟩ :=
      Work.Diff.EXT.covK_linear (I := I) (M := M) hLC g j
    have hF1 : ∀ m : Fin (Module.finrank ℝ E),
        Work.Diff.EXT.covKRmExt g j v (Work.Diff.EXT.dirF g (W m) v0) A (W m) B x
          = ∑ k, g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W k x)
              * Work.Diff.EXT.covKRmExt g j v (W k) A (W m) B x := by
      intro m
      have hZsm : Work.Diff.GE.SmoothFieldT (I := I) (M := M)
          (∑ p ∈ Finset.univ,
            g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W p x) • W p) :=
        smooth_sum_smul W hW (W ⟨0, hn⟩) (hW ⟨0, hn⟩) _ Finset.univ
      have hval : (∑ p ∈ Finset.univ,
            g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W p x) • W p
            : Work.Diff.EXT.TField (I := I) (M := M)) x
          = (Work.Diff.EXT.dirF g (W m) v0) x := by
        have h1 : (∑ p ∈ Finset.univ,
              g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W p x) • W p
              : Work.Diff.EXT.TField (I := I) (M := M)) x
            = ∑ p ∈ Finset.univ,
                g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W p x) • W p x := by
          simp only [Finset.sum_apply, Pi.smul_apply]
        rw [h1, ← hexp m]
      have hten := Work.Diff.EXT.covKRmExt_tensorial hLC j g x v v
        (Work.Diff.EXT.dirF g (W m) v0)
        (∑ p ∈ Finset.univ,
          g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W p x) • W p)
        A A (W m) (W m) B B hv hv
        (Work.Diff.EXT.dirF_smooth hLC g (hW m) hv0) hZsm hA hA (hW m) (hW m) hB hB
        (fun i => rfl) hval.symm rfl rfl rfl
      rw [hten]
      exact linear_apply_sum W hW (W ⟨0, hn⟩) (hW ⟨0, hn⟩)
        (fun p => g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W p x)) Finset.univ
        (fun X => Work.Diff.EXT.covKRmExt g j v X A (W m) B)
        (fun X X' hX hX' => haddA v X X' A (W m) B hv hX hX' hA (hW m) hB)
        (fun f hf X hX => hsmulA v f X A (W m) B hf hv hX hA (hW m) hB)
        x
    have hF2 : ∀ m : Fin (Module.finrank ℝ E),
        Work.Diff.EXT.covKRmExt g j v (W m) A (Work.Diff.EXT.dirF g (W m) v0) B x
          = ∑ k, g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W k x)
              * Work.Diff.EXT.covKRmExt g j v (W m) A (W k) B x := by
      intro m
      have hZsm : Work.Diff.GE.SmoothFieldT (I := I) (M := M)
          (∑ p ∈ Finset.univ,
            g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W p x) • W p) :=
        smooth_sum_smul W hW (W ⟨0, hn⟩) (hW ⟨0, hn⟩) _ Finset.univ
      have hval : (∑ p ∈ Finset.univ,
            g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W p x) • W p
            : Work.Diff.EXT.TField (I := I) (M := M)) x
          = (Work.Diff.EXT.dirF g (W m) v0) x := by
        have h1 : (∑ p ∈ Finset.univ,
              g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W p x) • W p
              : Work.Diff.EXT.TField (I := I) (M := M)) x
            = ∑ p ∈ Finset.univ,
                g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W p x) • W p x := by
          simp only [Finset.sum_apply, Pi.smul_apply]
        rw [h1, ← hexp m]
      have hten := Work.Diff.EXT.covKRmExt_tensorial hLC j g x v v
        (W m) (W m) A A (Work.Diff.EXT.dirF g (W m) v0)
        (∑ p ∈ Finset.univ,
          g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W p x) • W p)
        B B hv hv (hW m) (hW m) hA hA
        (Work.Diff.EXT.dirF_smooth hLC g (hW m) hv0) hZsm hB hB
        (fun i => rfl) rfl rfl hval.symm rfl
      rw [hten]
      exact linear_apply_sum W hW (W ⟨0, hn⟩) (hW ⟨0, hn⟩)
        (fun p => g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W p x)) Finset.univ
        (fun X => Work.Diff.EXT.covKRmExt g j v (W m) A X B)
        (fun X X' hX hX' => haddC v (W m) A X X' B hv (hW m) hA hX hX' hB)
        (fun f hf X hX => hsmulC v f (W m) A X B hf hv (hW m) hA hX hB)
        x
    have e1 : (∑ m, Work.Diff.EXT.covKRmExt g j v (Work.Diff.EXT.dirF g (W m) v0) A (W m) B x)
        = ∑ m, ∑ k, g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W k x)
            * Work.Diff.EXT.covKRmExt g j v (W k) A (W m) B x :=
      Finset.sum_congr rfl (fun m _ => hF1 m)
    have e2 : (∑ m, Work.Diff.EXT.covKRmExt g j v (W m) A (Work.Diff.EXT.dirF g (W m) v0) B x)
        = ∑ m, ∑ k, g.inner x (Submission.Diff.lcOf g (W m) x (v0 x)) (W k x)
            * Work.Diff.EXT.covKRmExt g j v (W m) A (W k) B x :=
      Finset.sum_congr rfl (fun m _ => hF2 m)
    rw [e1, e2]
    exact skew_double_sum_zero _ _ (fun m k => hskew m k)
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hn
    have hfin : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    simp [Finset.univ_eq_empty]

end Work.Diff.EXT.ConnCov
