import Mathlib
import Submission.Work.Diff.GE.kato_deps
import Submission.Work.Diff.GE.kato_defs
import Submission.Work.Diff.GE.kato_bump_pos
import Submission.Work.Diff.GE.kato_jet_correction
import Submission.Work.Diff.GE.kato_mvfderiv_inner_lc
import Submission.Work.Diff.GE.kato_lcOf_sum_apply
import Submission.Work.Diff.GE.kato_smooth
import Submission.Work.Diff.GE.kato_smooth_norm
import Submission.Work.Diff.GE.kato_orthonormal_algebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A geodesic orthonormal frame at a point (Kato's lemma)

`Work.Diff.GE.kato_geodesic_frame`: for a smooth Riemannian metric `g` on a smooth manifold `M` and
a point `x`, there are globally smooth vector fields `W i` (`i : Fin (finrank ℝ E)`) with

* `W · y` orthonormal for `g` for every `y` near `x`,
* `W i x = onFrame g x i`,
* `∇_{W m x} W j = 0` for all `m, j` (the frame is *geodesic at* `x`).

This is the frame used in Kato's inequality for `|Rm|²`.  The construction and its auxiliary
lemmas are in `Submission/Work/Diff/GE/kato_defs.lean` and the modules imported below.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.GE

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Smoothness of the metric pairing of two smooth sections. -/
theorem kato_pair_contMDiff (g : SMet I M) {X Y : Π y : M, TangentSpace I y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) :
    CMDiff ∞ (fun y : M => g.inner y (X y) (Y y)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  exact ContMDiff.inner_bundle (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hX hY

/-- The value at `x` of the pre-normalisation vector. -/
theorem katoU_apply_x (g : SMet I M) (x : M) (V W : katoIdx E → Π y : M, TangentSpace I y)
    (i : katoIdx E) (hW : ∀ j, j.val < i.val → W j x = V j x)
    (hON : ∀ j, j.val < i.val → g.inner x (V i x) (V j x) = 0) :
    katoU g V W i x = V i x := by
  rw [katoU_apply]
  have h : (∑ j ∈ katoPre i, g.inner x (V i x) (W j x) • W j x) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [katoPre_mem] at hj
    rw [hW j hj, hON j hj, zero_smul]
  rw [h, sub_zero]

/-- The Gram function at `x`. -/
theorem katoGram_apply_x (g : SMet I M) (x : M) (V W : katoIdx E → Π y : M, TangentSpace I y)
    (i : katoIdx E) (hU : katoU g V W i x = V i x)
    (h1 : g.inner x (V i x) (V i x) = 1) :
    katoGram g V W i x = 1 := by
  rw [katoGram_apply, hU, h1]

section Cov

variable (g : SMet I M) (x : M) (V W : katoIdx E → Π y : M, TangentSpace I y)

/-- The pre-normalisation vector is geodesic at `x`. -/
theorem katoU_cov_zero (i : katoIdx E) (hVs : CMDiff ∞ (T% (V i)))
    (hWs : ∀ j, j.val < i.val → CMDiff ∞ (T% (W j)))
    (hVc : lcOf g (V i) x = 0) (hWc : ∀ j, j.val < i.val → lcOf g (W j) x = 0)
    (hWx : ∀ j, j.val < i.val → W j x = V j x)
    (hON : ∀ j, j.val < i.val → g.inner x (V i x) (V j x) = 0) :
    lcOf g (katoU g V W i) x = 0 := by
  classical
  set S : Π y : M, TangentSpace I y :=
    fun y => ∑ j ∈ katoPre i, g.inner y (V i y) (W j y) • W j y with hSdef
  have hf : ∀ j ∈ katoPre i, CMDiff ∞ (fun y : M => g.inner y (V i y) (W j y)) :=
    fun j hj => kato_pair_contMDiff g hVs (hWs j (katoPre_mem.mp hj))
  have hS : CMDiff ∞ (T% S) := by
    rw [hSdef]
    exact ContMDiff.sum_section (fun j hj => (hf j hj).smul_section (hWs j (katoPre_mem.mp hj)))
  have hSd : MDiffAt (T% S) x := hS.contMDiffAt.mdifferentiableAt (by simp)
  have hVd : MDiffAt (T% (V i)) x := hVs.contMDiffAt.mdifferentiableAt (by simp)
  have hdecomp : katoU g V W i = V i + (-1 : ℝ) • S := by
    funext y
    rw [hSdef]
    simp only [katoU_apply, Pi.add_apply, Pi.smul_apply]
    rw [neg_one_smul, sub_eq_add_neg]
  have hSe : S = ∑ j ∈ katoPre i, (fun y : M => g.inner y (V i y) (W j y)) • W j := by
    rw [hSdef]
    funext y
    rw [Finset.sum_apply]
    rfl
  have hS0 : lcOf g S x = 0 := by
    ext v
    rw [hSe, kato_lcOf_sum_apply g x (katoPre i) (fun j y => g.inner y (V i y) (W j y)) W
      hf (fun j hj => hWs j (katoPre_mem.mp hj)) v]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' : j.val < i.val := katoPre_mem.mp hj
    have hfx : g.inner x (V i x) (W j x) = 0 := by rw [hWx j hj', hON j hj']
    have hdf : mvfderiv I (fun y : M => g.inner y (V i y) (W j y)) x = 0 := by
      ext v
      rw [kato_mvfderiv_inner_lc g x v hVs (hWs j hj')]
      rw [show lcOf g (V i) x v = 0 from by rw [hVc, zero_apply],
        show lcOf g (W j) x v = 0 from by rw [hWc j hj', zero_apply]]
      simp
    rw [hfx, hdf]
    simp
  rw [hdecomp]
  rw [show lcOf g (V i + (-1 : ℝ) • S) x
      = lcOf g (V i) x + lcOf g ((-1 : ℝ) • S) x
      from (lcOf g).isCovariantDerivativeOn.add hVd (((contMDiff_const (c := (-1 : ℝ))).smul_section hS).contMDiffAt.mdifferentiableAt (by simp)),
    show lcOf g ((-1 : ℝ) • S) x = (-1 : ℝ) • lcOf g S x
      from (lcOf g).isCovariantDerivativeOn.smul_const (-1 : ℝ) hSd,
    hS0, hVc]
  simp

end Cov

end Work.Diff.GE

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The Gram function of the pre-normalisation vector is nonnegative. -/
theorem katoGram_nonneg (g : SMet I M) (V W : katoIdx E → Π y : M, TangentSpace I y)
    (i : katoIdx E) (y : M) : 0 ≤ katoGram g V W i y := by
  rw [katoGram_apply]
  rcases eq_or_ne (katoU g V W i y) (0 : TangentSpace I y) with h0 | h0
  · rw [h0]; simp
  · exact le_of_lt (g.pos y _ h0)

/-- The value of the smoothed Gram function at `x`. -/
theorem katoNorm_apply_x (g : SMet I M) (x : M)
    (V W : katoIdx E → Π y : M, TangentSpace I y) (i : katoIdx E) :
    katoNorm g x V W i x = katoGram g V W i x := by
  simp [katoNorm]

/-- The value of the normalising scalar at `x`. -/
theorem katoC_apply_x (g : SMet I M) (x : M) (V W : katoIdx E → Π y : M, TangentSpace I y)
    (i : katoIdx E) (h : katoNorm g x V W i x = 1) : katoC g x V W i x = 1 := by
  rw [katoC_apply, h, Real.sqrt_one, inv_one]

/-- The derivative of the Gram function vanishes if the pre-normalisation vector is geodesic. -/
theorem katoGram_mvfderiv_zero (g : SMet I M) (x : M)
    (V W : katoIdx E → Π y : M, TangentSpace I y) (i : katoIdx E)
    (hUs : CMDiff ∞ (T% (katoU g V W i))) (hUc : lcOf g (katoU g V W i) x = 0) :
    ∀ v : TangentSpace I x, mvfderiv I (katoGram g V W i) x v = 0 := by
  intro v
  change mvfderiv I (fun y => g.inner y (katoU g V W i y) (katoU g V W i y)) x v = 0
  have h := kato_mvfderiv_inner_lc g x v hUs hUs (Y := katoU g V W i) (Z := katoU g V W i)
  rw [h]
  rw [show lcOf g (katoU g V W i) x v = 0 from by rw [hUc, zero_apply]]
  simp

/-- The derivative of the smoothed Gram function vanishes if that of the Gram function does. -/
theorem katoNorm_mvfderiv_zero (g : SMet I M) (x : M)
    (V W : katoIdx E → Π y : M, TangentSpace I y) (i : katoIdx E)
    (hf : CMDiff ∞ (katoGram g V W i))
    (hψ : CMDiff ∞ (katoBump (I := I) (katoGram g V W i) x))
    (hdf : ∀ v : TangentSpace I x, mvfderiv I (katoGram g V W i) x v = 0) :
    ∀ v : TangentSpace I x, mvfderiv I (katoNorm g x V W i) x v = 0 := by
  intro v
  set c : ℝ := katoGram g V W i x with hcdef
  set ψ : M → ℝ := katoBump (I := I) (katoGram g V W i) x with hψdef
  have hrew : katoNorm g x V W i
      = (fun _ : M => c) + ((katoGram g V W i - fun _ : M => c) • ψ) := by
    funext y
    simp only [katoNorm, hcdef, hψdef]
    rfl
  have hf' : MDiffAt (katoGram g V W i) x := hf.contMDiffAt.mdifferentiableAt (by simp)
  have hψ' : MDiffAt ψ x := hψ.contMDiffAt.mdifferentiableAt (by simp)
  have hc : MDiffAt (fun _ : M => c) x := mdifferentiableAt_const
  have h1 : MDiffAt (katoGram g V W i - fun _ : M => c) x := hf'.sub hc
  have hd1 : mvfderiv I (katoGram g V W i - fun _ : M => c) x = mvfderiv I (katoGram g V W i) x := by
    rw [mvfderiv_sub hf' hc, mvfderiv_const, sub_zero]
  have hd2 : mvfderiv I ((katoGram g V W i - fun _ : M => c) • ψ) x
      = (mvfderiv I (katoGram g V W i) x).smulRight (ψ x) := by
    rw [mvfderiv_smul h1 hψ', hd1]
    have h0 : (katoGram g V W i - fun _ : M => c) x = 0 := by simp [hcdef]
    rw [h0, zero_smul, zero_add]
  have hd : mvfderiv I (katoNorm g x V W i) x
      = (mvfderiv I (katoGram g V W i) x).smulRight (ψ x) := by
    rw [hrew, mvfderiv_add hc (h1.smul hψ'), mvfderiv_const, zero_add, hd2]
  rw [congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) hd, ContinuousLinearMap.smulRight_apply,
    hdf v, zero_smul]

/-- The derivative of the normalising scalar vanishes if that of the smoothed Gram function does. -/
theorem katoC_mvfderiv_zero (g : SMet I M) (x : M)
    (V W : katoIdx E → Π y : M, TangentSpace I y) (i : katoIdx E)
    (hFs : CMDiff ∞ (katoNorm g x V W i)) (hFpos : ∀ y, 0 < katoNorm g x V W i y)
    (hdF : ∀ v : TangentSpace I x, mvfderiv I (katoNorm g x V W i) x v = 0) :
    ∀ v : TangentSpace I x, mvfderiv I (katoC g x V W i) x v = 0 := by
  intro v
  set F : M → ℝ := katoNorm g x V W i with hFdef
  set h : ℝ → ℝ := fun t => (Real.sqrt t)⁻¹ with hhdef
  have hF' : MDiffAt F x := hFs.contMDiffAt.mdifferentiableAt (by simp)
  have hh : MDiffAt h (F x) := by
    have h1 : ContDiffAt ℝ ∞ (fun t : ℝ => Real.sqrt t) (F x) :=
      Real.contDiffAt_sqrt (hFpos x).ne'
    have h2 : ContDiffAt ℝ ∞ (fun t : ℝ => (Real.sqrt t)⁻¹) (F x) :=
      h1.inv (Real.sqrt_pos.mpr (hFpos x)).ne'
    exact ((contMDiffAt_iff_contDiffAt).mpr h2).mdifferentiableAt (by simp)
  have hfun : katoC g x V W i = h ∘ F := by
    funext y
    simp only [katoC, hFdef, hhdef, Function.comp_apply]
  rw [hfun, mvfderiv_comp x hh hF']
  rw [ContinuousLinearMap.comp_apply,
    show mfderiv% F x v = 0 from hdF v]
  exact map_zero _

end Work.Diff.GE

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A family whose members are orthonormal at `x` up to the triangular Gram–Schmidt pattern is an
orthonormal frame near `x`. -/
theorem isONFrame_of_diag_off (g : SMet I M) (x : M)
    (W : katoIdx E → Π y : M, TangentSpace I y)
    (hdiag : ∀ᶠ y in 𝓝 x, ∀ i, g.inner y (W i y) (W i y) = 1)
    (hoff : ∀ᶠ y in 𝓝 x, ∀ i, ∀ k, k.val < i.val → g.inner y (W i y) (W k y) = 0) :
    ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => W i y) := by
  filter_upwards [hdiag, hoff] with y h1 h2
  intro i k
  rcases eq_or_ne i k with hik | hik
  · subst hik; rw [h1 i, ite_eq_left rfl]
  · have hne : i.val ≠ k.val := fun h => hik (Fin.ext h)
    rw [ite_eq_right hik]
    rcases lt_or_gt_of_ne hne with h | h
    · exact (g.symm y (W i y) (W k y)).trans (h2 k i h)
    · exact h2 i k h

/-- **A geodesic orthonormal frame at a point.** -/
theorem kato_geodesic_frame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) (x : M) :
    ∃ W : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y),
      (∀ i, CMDiff ∞ (T% (W i))) ∧
      (∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => W i y)) ∧
      (∀ i, W i x = onFrame g x i) ∧
      (∀ m j, lcOf g (W j) x (W m x) = 0) := by
  classical
  set e : katoIdx E → TangentSpace I x := onFrame g x with hedef
  have he : IsONFrame g x e := isONFrame_onFrame g x
  choose V hVs hVx hVc using fun i => kato_jet_correction (lcOf g) x (e i)
  have key : ∀ m : ℕ, ∀ i : katoIdx E, i.val < m →
      (CMDiff ∞ (T% (katoFrame g x V i)))
      ∧ (katoFrame g x V i x = V i x)
      ∧ (lcOf g (katoFrame g x V i) x = 0)
      ∧ (∀ᶠ y in 𝓝 x, g.inner y (katoFrame g x V i y) (katoFrame g x V i y) = 1)
      ∧ (∀ᶠ y in 𝓝 x, ∀ k, k.val < i.val →
          g.inner y (katoFrame g x V i y) (katoFrame g x V k y) = 0) := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih i hlt
      · have hIH : ∀ j, j.val < i.val →
            (CMDiff ∞ (T% (katoFrame g x V j)))
            ∧ (katoFrame g x V j x = V j x)
            ∧ (lcOf g (katoFrame g x V j) x = 0)
            ∧ (∀ᶠ y in 𝓝 x, g.inner y (katoFrame g x V j y) (katoFrame g x V j y) = 1)
            ∧ (∀ᶠ y in 𝓝 x, ∀ k, k.val < j.val →
                g.inner y (katoFrame g x V j y) (katoFrame g x V k y) = 0) :=
          fun j hj => ih j (by rw [← heq]; exact hj)
        obtain ⟨hUs, hGs⟩ :=
          kato_smooth g V (katoFrame g x V) i (hVs i) (fun j hj => (hIH j hj).1)
        have hON : ∀ j, j.val < i.val → g.inner x (V i x) (V j x) = 0 := by
          intro j hj
          have hne : i ≠ j := by
            intro hij; rw [← hij] at hj; exact absurd hj (Nat.lt_irrefl _)
          rw [hVx i, hVx j, he i j, ite_eq_right hne]
        have hUx : katoU g V (katoFrame g x V) i x = V i x :=
          katoU_apply_x g x V (katoFrame g x V) i (fun j hj => (hIH j hj).2.1) hON
        have hV1 : g.inner x (V i x) (V i x) = 1 := by
          rw [hVx i, he i i, ite_eq_left rfl]
        have hfx : 0 < katoGram g V (katoFrame g x V) i x := by
          rw [katoGram_apply_x g x V (katoFrame g x V) i hUx hV1]; norm_num
        obtain ⟨hFpos, hFs, hCs, hCeq, hFx, hFeq⟩ :=
          kato_smooth_norm g x V (katoFrame g x V) i hGs hfx
        have hUc : lcOf g (katoU g V (katoFrame g x V) i) x = 0 :=
          katoU_cov_zero g x V (katoFrame g x V) i (hVs i)
            (fun j hj => (hIH j hj).1) (hVc i) (fun j hj => (hIH j hj).2.2.1)
            (fun j hj => (hIH j hj).2.1) hON
        have hdf := katoGram_mvfderiv_zero g x V (katoFrame g x V) i hUs hUc
        have hψs : CMDiff ∞ (katoBump (I := I) (katoGram g V (katoFrame g x V) i) x) :=
          (katoBump_spec hGs hfx).1
        have hdF := katoNorm_mvfderiv_zero g x V (katoFrame g x V) i hGs hψs hdf
        have hdC := katoC_mvfderiv_zero g x V (katoFrame g x V) i hFs hFpos hdF
        have hCx : katoC g x V (katoFrame g x V) i x = 1 :=
          katoC_apply_x g x V (katoFrame g x V) i
            (by rw [hFx, katoGram_apply_x g x V (katoFrame g x V) i hUx hV1])
        have hWx : katoFrame g x V i x = V i x := by
          rw [katoFrame_eq g x V i]
          show katoC g x V (katoFrame g x V) i x • katoU g V (katoFrame g x V) i x = V i x
          rw [hCx, hUx, one_smul]
        have hWs : CMDiff ∞ (T% (katoFrame g x V i)) := by
          rw [katoFrame_eq g x V i]
          exact hCs.smul_section hUs
        have hWc : lcOf g (katoFrame g x V i) x = 0 := by
          have hUsd : MDiffAt (T% (katoU g V (katoFrame g x V) i)) x :=
            hUs.contMDiffAt.mdifferentiableAt (by simp)
          have hCsd : MDiffAt (katoC g x V (katoFrame g x V) i) x :=
            hCs.contMDiffAt.mdifferentiableAt (by simp)
          have hdC0 : mvfderiv I (katoC g x V (katoFrame g x V) i) x = 0 := by
            ext v; exact hdC v
          rw [katoFrame_eq g x V i,
            show katoStep g x V (katoFrame g x V) i
              = (katoC g x V (katoFrame g x V) i) • (katoU g V (katoFrame g x V) i) from rfl,
            (lcOf g).isCovariantDerivativeOn.leibniz hUsd hCsd, hdC0, hUc, hCx]
          simp
        have hdiag_prev : ∀ᶠ y in 𝓝 x, ∀ j, j.val < i.val →
            g.inner y (katoFrame g x V j y) (katoFrame g x V j y) = 1 := by
          rw [Filter.eventually_all]
          intro j
          by_cases hj : j.val < i.val
          · filter_upwards [(hIH j hj).2.2.2.1] with y hy
            exact fun _ => hy
          · exact Filter.Eventually.of_forall fun y h => absurd h hj
        have hoff_prev : ∀ᶠ y in 𝓝 x, ∀ j, j.val < i.val → ∀ k, k.val < j.val →
            g.inner y (katoFrame g x V j y) (katoFrame g x V k y) = 0 := by
          rw [Filter.eventually_all]
          intro j
          by_cases hj : j.val < i.val
          · filter_upwards [(hIH j hj).2.2.2.2] with y hy
            exact fun _ => hy
          · exact Filter.Eventually.of_forall fun y h => absurd h hj
        have hbump1 : ∀ᶠ y in 𝓝 x,
            katoBump (I := I) (katoGram g V (katoFrame g x V) i) x y = 1 :=
          (katoBump_spec hGs hfx).2.2.2.2
        have hfpos_ev : ∀ᶠ y in 𝓝 x, 0 < katoGram g V (katoFrame g x V) i y :=
          (hGs x).continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hfx)
        have hdiag_i : ∀ᶠ y in 𝓝 x,
            g.inner y (katoFrame g x V i y) (katoFrame g x V i y) = 1 := by
          filter_upwards [hbump1, hfpos_ev, hdiag_prev, hoff_prev] with y hb hf hp ho
          rw [katoFrame_eq g x V i]
          exact (kato_orthonormal_algebra g x V (katoFrame g x V) i y hb hf hp ho).1
        have hoff_i : ∀ᶠ y in 𝓝 x, ∀ k, k.val < i.val →
            g.inner y (katoFrame g x V i y) (katoFrame g x V k y) = 0 := by
          filter_upwards [hbump1, hfpos_ev, hdiag_prev, hoff_prev] with y hb hf hp ho
          intro k hk
          rw [katoFrame_eq g x V i]
          exact (kato_orthonormal_algebra g x V (katoFrame g x V) i y hb hf hp ho).2 k hk
        exact ⟨hWs, hWx, hWc, hdiag_i, hoff_i⟩
  refine ⟨katoFrame g x V, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (key (i.val + 1) i (Nat.lt_succ_self _)).1
  · refine isONFrame_of_diag_off g x (katoFrame g x V) ?_ ?_
    · rw [Filter.eventually_all]
      intro i
      exact (key (i.val + 1) i (Nat.lt_succ_self _)).2.2.2.1
    · rw [Filter.eventually_all]
      intro i
      exact (key (i.val + 1) i (Nat.lt_succ_self _)).2.2.2.2
  · intro i
    rw [(key (i.val + 1) i (Nat.lt_succ_self _)).2.1]
    exact hVx i
  · intro m j
    rw [(key (m.val + 1) m (Nat.lt_succ_self _)).2.1,
      (key (j.val + 1) j (Nat.lt_succ_self _)).2.2.1]
    rw [hVx m]
    rfl

end Work.Diff.GE
