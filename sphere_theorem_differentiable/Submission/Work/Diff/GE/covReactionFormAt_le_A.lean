import Mathlib
import Submission.Work.Diff.GE.covRxn.Defs
import Submission.Work.Diff.GE.Gest.hess_mul_field
import Submission.Work.Diff.GE.covRxnA.mvfderiv_comp_curv4
import Submission.Work.Diff.GE.covRxnA.mvfderiv_rmFrameField
import Submission.Work.Diff.GE.covRxnA.mvfderiv_F_rmFrameField
import Submission.Work.Diff.GE.Rfa.reactionFormAtE_frame_indep
import Submission.Work.Diff.EXT.laplAt_curvNormK_eq
import Submission.Work.Diff.GE.covRxnA.pairing_le
import Submission.Work.Diff.GE.covRxnA.dRmArr_norm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The derivative bound for the quadratic reaction `F(Rm)` (assembly)

The definitions live in `Submission.Work.Diff.GE.covRxn.Defs` (module
`Submission.Work.Diff.GE.covRxn.Defs`, namespace `Work.Diff.GE.Rxn`); this file assembles the
delegated pieces (`Submission.Work.Diff.GE.covRxnA.*`) into `Work.Diff.GE.covReactionFormAt_le_A`.

## Structure of the proof

`reactionFormAtE` is the reaction form in an *explicit* frame; `frame_indep` shows that for an
equivariant `F` the value does not depend on the orthonormal frame.  So along a smooth orthonormal
frame field `W` (which exists near `x` and may be taken *geodesic* at `x`,
`Work.Diff.GE.kato_geodesic_frame`) the (a priori non-smooth) function
`y ↦ reactionFormAt F g y (...)` agrees near `x` with the smooth function
`y ↦ Rxn.reactionW F g W A B C D y`; hence the `Ext`-pattern expression `covReactionFormAt` may be
computed with that smooth representation.  The product rule gives the derivative of the four
coefficient pairings and the chain rule (`mvfderiv_F_rmFrameField`) the derivative of `F(Rm)`; the
coefficient-derivative terms cancel the four tensorialising slot corrections (this is where
geodesicity of the frame at `x` is used), leaving the contraction of `fderiv ℝ F (rmC)` with `∇Rm`,
which is bounded with `pairing_le`, `dRmArr_norm_le` and `curv4_norm_bounds`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE.Rxn

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Elementary helper lemmas -/

/-- Metric compatibility of the Levi-Civita connection in `mvfderiv` form:
`d/dt g(Y,Z) = g(∇_v Y, Z) + g(Y, ∇_v Z)` for smooth sections `Y, Z`. -/
theorem mvfderiv_inner_lc (g : SMet I M) (x : M) (v : TangentSpace I x)
    {Y Z : Π y : M, TangentSpace I y} (hY : SmoothField Y) (hZ : SmoothField Z) :
    mvfderiv I (fun y : M => g.inner y (Y y) (Z y)) x v
      = g.inner x (lcOf g Y x v) (Z x) + g.inner x (Y x) (lcOf g Z x v) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have key : mvfderiv I (fun y : M => Inner.inner ℝ (Y y) (Z y)) x v
      = Inner.inner ℝ (lcOf g Y x v) (Z x) + Inner.inner ℝ (Y x) (lcOf g Z x v) := by
    have hY' : MDiffAt (T% Y) x := hY.contMDiffAt.mdifferentiableAt (by simp)
    have hZ' : MDiffAt (T% Z) x := hZ.contMDiffAt.mdifferentiableAt (by simp)
    have h' := (CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M))
      |>.mvfderiv_inner_eq (σ := Y) (τ := Z) (fun _ : M => v) hY' hZ'
    simpa only [lcOf] using h'
  change mvfderiv I (fun y : M => Inner.inner ℝ (Y y) (Z y)) x v
      = Inner.inner ℝ (lcOf g Y x v) (Z x) + Inner.inner ℝ (Y x) (lcOf g Z x v)
  exact key

/-- **The `Ext` pattern on arbitrary smooth fields.**  The derivative of
`y ↦ rmP g y (A y) (B y) (C y) (D y)` is the value of `∇Rm` at `x` plus the four connection
corrections: the `Ext` pattern computes `∇Rm` and depends only on the values at `x`. -/
theorem mvfderiv_rmP_fields [T2Space M] (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v : TangentSpace I x)
    (A B C D : Π y : M, TangentSpace I y)
    (hA : SmoothField A) (hB : SmoothField B) (hC : SmoothField C) (hD : SmoothField D) :
    mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x v
      = covRm g x v (A x) (B x) (C x) (D x)
        + rmP g x (lcOf g A x v) (B x) (C x) (D x)
        + rmP g x (A x) (lcOf g B x v) (C x) (D x)
        + rmP g x (A x) (B x) (lcOf g C x v) (D x)
        + rmP g x (A x) (B x) (C x) (lcOf g D x v) := by
  rw [Work.Diff.GE.Kato3.covRm_field_form (I := I) (M := M) hLC g x v hA hB hC hD]
  simp only [dRmPhi]
  ring

/-- The sup norm on `Curv4 n` is bounded by the `ℓ²` norm, and conversely. -/
theorem curv4_norm_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X : Curv4 (Module.finrank ℝ E)) :
    ‖X‖ ≤ Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, (X i j k l) ^ 2) ∧
      Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, (X i j k l) ^ 2)
        ≤ (Module.finrank ℝ E : ℝ) ^ 2 * ‖X‖ := by
  set S := ∑ i, ∑ j, ∑ k, ∑ l, (X i j k l) ^ 2 with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _
  have hterm : ∀ i j k l, (X i j k l) ^ 2 ≤ S := by
    intro i j k l
    rw [hS]
    have h1 : (X i j k l) ^ 2 ≤ ∑ l', (X i j k l') ^ 2 :=
      Finset.single_le_sum (fun a _ => sq_nonneg _) (Finset.mem_univ l)
    have h2 : (∑ l', (X i j k l') ^ 2) ≤ ∑ k', ∑ l', (X i j k' l') ^ 2 :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
        (Finset.mem_univ k)
    have h3 : (∑ k', ∑ l', (X i j k' l') ^ 2) ≤ ∑ j', ∑ k', ∑ l', (X i j' k' l') ^ 2 :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ =>
        Finset.sum_nonneg fun c _ => sq_nonneg _) (Finset.mem_univ j)
    have h4 : (∑ j', ∑ k', ∑ l', (X i j' k' l') ^ 2)
        ≤ ∑ i', ∑ j', ∑ k', ∑ l', (X i' j' k' l') ^ 2 :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ =>
        Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => sq_nonneg _)
        (Finset.mem_univ i)
    exact h1.trans (h2.trans (h3.trans h4))
  constructor
  · refine pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr fun i => ?_
    refine pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr fun j => ?_
    refine pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr fun k => ?_
    refine pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr fun l => ?_
    rw [Real.norm_eq_abs, Real.le_sqrt (abs_nonneg _) hSnn, sq_abs]
    exact hterm i j k l
  · have hle : S ≤ (Module.finrank ℝ E : ℝ) ^ 4 * ‖X‖ ^ 2 := by
      rw [hS]
      calc ∑ i, ∑ j, ∑ k, ∑ l, (X i j k l) ^ 2
          ≤ ∑ i, ∑ j, ∑ k, ∑ l, ‖X‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
            have h1 : ‖X i j k l‖ ≤ ‖X‖ :=
              (norm_le_pi_norm (X i j k) l).trans ((norm_le_pi_norm (X i j) k).trans
                ((norm_le_pi_norm (X i) j).trans (norm_le_pi_norm X i)))
            have h2 : (X i j k l) ^ 2 = ‖X i j k l‖ ^ 2 := by
              rw [Real.norm_eq_abs, sq_abs]
            rw [h2]
            simpa only [sq] using mul_le_mul h1 h1 (norm_nonneg _) (norm_nonneg _)
        _ = (Module.finrank ℝ E : ℝ) ^ 4 * ‖X‖ ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    calc Real.sqrt S ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 4 * ‖X‖ ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = (Module.finrank ℝ E : ℝ) ^ 2 * ‖X‖ := by
          rw [show (Module.finrank ℝ E : ℝ) ^ 4 * ‖X‖ ^ 2
                = ((Module.finrank ℝ E : ℝ) ^ 2 * ‖X‖) ^ 2 by ring]
          rw [Real.sqrt_sq (by positivity)]

/-! ## Bookkeeping lemmas for the assembly -/

/-- The product rule for a product of four smooth real functions. -/
theorem mvfderiv_prod4 (f₁ f₂ f₃ f₄ : M → ℝ) (h₁ : CMDiff ∞ f₁) (h₂ : CMDiff ∞ f₂)
    (h₃ : CMDiff ∞ f₃) (h₄ : CMDiff ∞ f₄) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => f₁ y * f₂ y * f₃ y * f₄ y) x v
      = f₂ x * f₃ x * f₄ x * mvfderiv I f₁ x v + f₁ x * f₃ x * f₄ x * mvfderiv I f₂ x v
        + f₁ x * f₂ x * f₄ x * mvfderiv I f₃ x v
        + f₁ x * f₂ x * f₃ x * mvfderiv I f₄ x v := by
  have h12 : CMDiff ∞ (fun y : M => f₁ y * f₂ y) := h₁.mul h₂
  have h123 : CMDiff ∞ (fun y : M => f₁ y * f₂ y * f₃ y) := h12.mul h₃
  have e1 := Work.Diff.GE.Gest.mvfderiv_mul_apply (I := I) (M := M)
    (u := fun y : M => f₁ y * f₂ y * f₃ y) (v := f₄) h123 h₄ x v
  have e2 := Work.Diff.GE.Gest.mvfderiv_mul_apply (I := I) (M := M)
    (u := fun y : M => f₁ y * f₂ y) (v := f₃) h12 h₃ x v
  have e3 := Work.Diff.GE.Gest.mvfderiv_mul_apply (I := I) (M := M)
    (u := f₁) (v := f₂) h₁ h₂ x v
  rw [e1, e2, e3]
  ring

/-- Chain rule over a quadruple finite sum of products. -/
theorem mvfderiv_sum4_prod {ι : Type*} [Fintype ι]
    (C E : ι → ι → ι → ι → M → ℝ) (hC : ∀ i j k l, CMDiff ∞ (C i j k l))
    (hE : ∀ i j k l, CMDiff ∞ (E i j k l)) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => ∑ i, ∑ j, ∑ k, ∑ l, C i j k l y * E i j k l y) x v
      = ∑ i, ∑ j, ∑ k, ∑ l, (C i j k l x * mvfderiv I (E i j k l) x v
          + E i j k l x * mvfderiv I (C i j k l) x v) := by
  have h4 : ∀ i j k, CMDiff ∞ (fun y : M => ∑ l, C i j k l y * E i j k l y) :=
    fun i j k => ContMDiff.sum fun l _ => (hC i j k l).mul (hE i j k l)
  have h3 : ∀ i j, CMDiff ∞ (fun y : M => ∑ k, ∑ l, C i j k l y * E i j k l y) :=
    fun i j => ContMDiff.sum fun k _ => h4 i j k
  have h2 : ∀ i, CMDiff ∞ (fun y : M => ∑ j, ∑ k, ∑ l, C i j k l y * E i j k l y) :=
    fun i => ContMDiff.sum fun j _ => h3 i j
  rw [Work.Diff.GE.Kato3.mvfderiv_sum (Finset.univ : Finset ι)
    (fun i y => ∑ j, ∑ k, ∑ l, C i j k l y * E i j k l y) (fun i => h2 i) x v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Work.Diff.GE.Kato3.mvfderiv_sum (Finset.univ : Finset ι)
    (fun j y => ∑ k, ∑ l, C i j k l y * E i j k l y) (fun j => h3 i j) x v]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Work.Diff.GE.Kato3.mvfderiv_sum (Finset.univ : Finset ι)
    (fun k y => ∑ l, C i j k l y * E i j k l y) (fun k => h4 i j k) x v]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Work.Diff.GE.Kato3.mvfderiv_sum (Finset.univ : Finset ι)
    (fun l y => C i j k l y * E i j k l y) (fun l => (hC i j k l).mul (hE i j k l)) x v]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Work.Diff.GE.Gest.mvfderiv_mul_apply (I := I) (M := M) (u := C i j k l)
    (v := E i j k l) (hC i j k l) (hE i j k l) x v]

/-- Distributing the four-term derivative of a product inside a quadruple sum. -/
theorem sum_prod4_deriv {ι : Type*} [Fintype ι]
    (X : ι → ι → ι → ι → ℝ) (P1 P2 P3 P4 dP1 dP2 dP3 dP4 : ι → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, X i j k l * (P2 j * P3 k * P4 l * dP1 i + P1 i * P3 k * P4 l * dP2 j
        + P1 i * P2 j * P4 l * dP3 k + P1 i * P2 j * P3 k * dP4 l))
      = (∑ i, ∑ j, ∑ k, ∑ l, (dP1 i * P2 j * P3 k * P4 l) * X i j k l)
        + (∑ i, ∑ j, ∑ k, ∑ l, (P1 i * dP2 j * P3 k * P4 l) * X i j k l)
        + (∑ i, ∑ j, ∑ k, ∑ l, (P1 i * P2 j * dP3 k * P4 l) * X i j k l)
        + (∑ i, ∑ j, ∑ k, ∑ l, (P1 i * P2 j * P3 k * dP4 l) * X i j k l) := by
  have h : ∀ i j k l, X i j k l * (P2 j * P3 k * P4 l * dP1 i + P1 i * P3 k * P4 l * dP2 j
        + P1 i * P2 j * P4 l * dP3 k + P1 i * P2 j * P3 k * dP4 l)
      = (dP1 i * P2 j * P3 k * P4 l) * X i j k l + (P1 i * dP2 j * P3 k * P4 l) * X i j k l
        + (P1 i * P2 j * dP3 k * P4 l) * X i j k l
        + (P1 i * P2 j * P3 k * dP4 l) * X i j k l := by
    intro i j k l; ring
  rw [show (∑ i, ∑ j, ∑ k, ∑ l, X i j k l * (P2 j * P3 k * P4 l * dP1 i
        + P1 i * P3 k * P4 l * dP2 j + P1 i * P2 j * P4 l * dP3 k + P1 i * P2 j * P3 k * dP4 l))
      = ∑ i, ∑ j, ∑ k, ∑ l, ((dP1 i * P2 j * P3 k * P4 l) * X i j k l
        + (P1 i * dP2 j * P3 k * P4 l) * X i j k l + (P1 i * P2 j * dP3 k * P4 l) * X i j k l
        + (P1 i * P2 j * P3 k * dP4 l) * X i j k l) from
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => h i j k l]
  simp only [Finset.sum_add_distrib]

end Work.Diff.GE.Rxn

namespace Work.Diff.GE

theorem covReactionFormAt_le_A
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∀ (F : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) →
        Submission.Diff.Alg.Curv4 (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) F →
      (∃ CF : ℝ, 0 ≤ CF ∧ ∀ R, ‖F R‖ ≤ CF * ‖R‖ * ‖R‖) →
      (∃ CF' : ℝ, 0 ≤ CF' ∧ ∀ R, ‖fderiv ℝ F R‖ ≤ CF' * ‖R‖) →
      (∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ, ∀ R,
        F (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.rot A (F R)) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ),
        Submission.Diff.IsRicciFlow G T →
        ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x,
          Work.Diff.GE.covReactionFormAt F (G t) x v a b c d ≤
            C * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
              * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
              * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
                * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
                * Real.sqrt ((G t).inner x d d)) := by
  intro F hFdiff hF2 hF' hFeq
  obtain ⟨CF, hCF0, hCF⟩ := hF2
  obtain ⟨CF', hCF'0, hCF'⟩ := hF'
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * CF', mul_nonneg (sq_nonneg _) hCF'0, ?_⟩
  intro G T hG t ht x v a b c d
  set g : SMet I M := G t with hg
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  -- a smooth orthonormal frame, geodesic at `x` and agreeing with `onFrame g x` there
  obtain ⟨W, hWs, hWON, hWx, hWgeo⟩ := Work.Diff.EXT.geodesic_frame_aux (I := I) (M := M) g x
  let V : Π y : M, Fin (Module.finrank ℝ E) → TangentSpace I y := fun y i => W i y
  have hVs : ∀ i, Rxn.SmoothField (fun y : M => V y i) := fun i => hWs i
  have hVON : ∀ᶠ y in 𝓝 x, IsONFrame g y (V y) := by simpa only [V] using hWON
  have hVx : ∀ i, V x i = onFrame g x i := fun i => hWx i
  have hVONx : IsONFrame g x (V x) := mem_of_mem_nhds hVON
  have hVgeo : ∀ m j, lcOf g (fun y : M => V y j) x (V x m) = 0 := by
    intro m j; simpa only [V] using hWgeo m j
  -- smooth extensions of the five vectors
  let A : Π y : M, TangentSpace I y := smoothExt x a
  let B : Π y : M, TangentSpace I y := smoothExt x b
  let C : Π y : M, TangentSpace I y := smoothExt x c
  let D : Π y : M, TangentSpace I y := smoothExt x d
  have hAs : Rxn.SmoothField A := smoothExt_cmdiff x a
  have hBs : Rxn.SmoothField B := smoothExt_cmdiff x b
  have hCs : Rxn.SmoothField C := smoothExt_cmdiff x c
  have hDs : Rxn.SmoothField D := smoothExt_cmdiff x d
  have hAx : A x = a := smoothExt_apply x a
  have hBx : B x = b := smoothExt_apply x b
  have hCx : C x = c := smoothExt_apply x c
  have hDx : D x = d := smoothExt_apply x d
  -- the frame is geodesic in *every* direction
  have hVv : ∀ j, lcOf g (fun y : M => V y j) x v = 0 := by
    intro j
    rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with h0 | hpos
    · have hsub : Subsingleton (TangentSpace I x) := by
        rw [← Module.finrank_zero_iff (R := ℝ) (M := TangentSpace I x)]; exact h0
      rw [Subsingleton.elim v 0, map_zero]
    · conv_lhs => rw [← Work.Diff.GE.sum_inner_smul_eq_self g x hpos (V x) hVONx v]
      rw [map_sum]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [map_smul, hVgeo m j, smul_zero]
  -- `rmP g x` vanishes whenever one of its slots is zero
  have hrmP0 : ∀ b c d : TangentSpace I x, rmP g x (0 : TangentSpace I x) b c d = 0 := by
    intro b c d
    simpa using rmP_smul_fst (I := I) (M := M) g hLC x 0 (0 : TangentSpace I x) b c d
  have hrmP0' : ∀ a c d : TangentSpace I x, rmP g x a (0 : TangentSpace I x) c d = 0 := by
    intro a c d
    simpa using rmP_smul_snd (I := I) (M := M) g hLC x 0 a (0 : TangentSpace I x) c d
  have hrmP0'' : ∀ a b d : TangentSpace I x, rmP g x a b (0 : TangentSpace I x) d = 0 := by
    intro a b d
    simpa using rmP_smul_thd (I := I) (M := M) g hLC x 0 a b (0 : TangentSpace I x) d
  have hrmP0''' : ∀ a b c : TangentSpace I x, rmP g x a b c (0 : TangentSpace I x) = 0 := by
    intro a b c
    simpa using rmP_smul_fth (I := I) (M := M) g hLC x 0 a b c (0 : TangentSpace I x)
  -- smoothness of the curvature array and of `F` composed with it
  have hRsm : ContMDiff I (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E))) ∞
      (fun y : M => Rxn.rmFrameField g V y) := by
    rw [contMDiff_pi_space]; intro i
    rw [contMDiff_pi_space]; intro j
    rw [contMDiff_pi_space]; intro k
    rw [contMDiff_pi_space]; intro l
    exact rmP_fields_smooth (I := I) hLC g (hVs i) (hVs j) (hVs k) (hVs l)
  have hFc : ContMDiff (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E)))
      (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E))) ∞ F := hFdiff.contMDiff
  have hFsm : ContMDiff I (modelWithCornersSelf ℝ (Curv4 (Module.finrank ℝ E))) ∞
      (fun y : M => F (Rxn.rmFrameField g V y)) := hFc.comp hRsm
  have hEfsm : ∀ i j k l, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : M => (F (Rxn.rmFrameField g V y)) i j k l) := by
    intro i j k l
    have h1 : ContMDiff I (modelWithCornersSelf ℝ
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)) ∞
        (fun y : M => (F (Rxn.rmFrameField g V y)) i) :=
      (contMDiff_pi_space (φ := fun y : M => F (Rxn.rmFrameField g V y))).mp hFsm i
    have h2 : ContMDiff I (modelWithCornersSelf ℝ
        (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)) ∞
        (fun y : M => (F (Rxn.rmFrameField g V y)) i j) :=
      (contMDiff_pi_space (φ := fun y : M => (F (Rxn.rmFrameField g V y)) i)).mp h1 j
    have h3 : ContMDiff I (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E) → ℝ)) ∞
        (fun y : M => (F (Rxn.rmFrameField g V y)) i j k) :=
      (contMDiff_pi_space (φ := fun y : M => (F (Rxn.rmFrameField g V y)) i j)).mp h2 k
    exact (contMDiff_pi_space (φ := fun y : M => (F (Rxn.rmFrameField g V y)) i j k)).mp h3 l
  -- the coefficient pairings
  let P₁ : Fin (Module.finrank ℝ E) → M → ℝ := fun i y => g.inner y (V y i) (A y)
  let P₂ : Fin (Module.finrank ℝ E) → M → ℝ := fun j y => g.inner y (V y j) (B y)
  let P₃ : Fin (Module.finrank ℝ E) → M → ℝ := fun k y => g.inner y (V y k) (C y)
  let P₄ : Fin (Module.finrank ℝ E) → M → ℝ := fun l y => g.inner y (V y l) (D y)
  have hP₁ : ∀ i, CMDiff ∞ (P₁ i) := fun i => by
    show CMDiff ∞ (fun y : M => Inner.inner ℝ (V y i) (A y))
    exact ContMDiff.inner_bundle (IB := I) (b := id) (v := fun y : M => V y i) (w := A)
      (hVs i) hAs
  have hP₂ : ∀ j, CMDiff ∞ (P₂ j) := fun j => by
    show CMDiff ∞ (fun y : M => Inner.inner ℝ (V y j) (B y))
    exact ContMDiff.inner_bundle (IB := I) (b := id) (v := fun y : M => V y j) (w := B)
      (hVs j) hBs
  have hP₃ : ∀ k, CMDiff ∞ (P₃ k) := fun k => by
    show CMDiff ∞ (fun y : M => Inner.inner ℝ (V y k) (C y))
    exact ContMDiff.inner_bundle (IB := I) (b := id) (v := fun y : M => V y k) (w := C)
      (hVs k) hCs
  have hP₄ : ∀ l, CMDiff ∞ (P₄ l) := fun l => by
    show CMDiff ∞ (fun y : M => Inner.inner ℝ (V y l) (D y))
    exact ContMDiff.inner_bundle (IB := I) (b := id) (v := fun y : M => V y l) (w := D)
      (hVs l) hDs
  let Cf : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → M → ℝ := fun i j k l y => P₁ i y * P₂ j y * P₃ k y * P₄ l y
  let Ef : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → M → ℝ := fun i j k l y => (F (Rxn.rmFrameField g V y)) i j k l
  have hCf : ∀ i j k l, CMDiff ∞ (Cf i j k l) := fun i j k l =>
    ((hP₁ i).mul (hP₂ j)).mul (hP₃ k) |>.mul (hP₄ l)
  have hEf : ∀ i j k l, CMDiff ∞ (Ef i j k l) := fun i j k l => by
    show ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      (fun y : M => (F (Rxn.rmFrameField g V y)) i j k l)
    exact hEfsm i j k l
  let Ψ : M → ℝ := fun y =>
    ∑ i, ∑ j, ∑ k, ∑ l, Cf i j k l y * Ef i j k l y
  let Φ : M → ℝ := fun y => reactionFormAt F g y (A y) (B y) (C y) (D y)
  -- germ equality: the (non-smooth) reaction is the frame-independent value
  have hgerm : Φ =ᶠ[𝓝 x] Ψ := by
    filter_upwards [hVON] with y hy
    have h2 := Work.Diff.GE.Rfa.reactionFormAtE_frame_indep (I := I) (M := M) hLC F hFeq g y
      (onFrame g y) (V y) (Work.Diff.GE.isONFrame_onFrame g y) hy (A y) (B y) (C y) (D y)
    show reactionFormAt F g y (A y) (B y) (C y) (D y) = Ψ y
    rw [Rxn.reactionFormAt_eq_reactionFormAtE]
    change Work.Diff.GE.Rfa.reactionFormAtE F g y (onFrame g y) (A y) (B y) (C y) (D y) = Ψ y
    rw [← h2]
    rfl
  have hderiv : mvfderiv I Φ x v = mvfderiv I Ψ x v :=
    congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v)
      (Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) hgerm)
  -- the definition of `covReactionFormAt`
  have hcov : covReactionFormAt F g x v a b c d
      = mvfderiv I Φ x v - reactionFormAt F g x (lcOf g A x v) b c d
        - reactionFormAt F g x a (lcOf g B x v) c d
        - reactionFormAt F g x a b (lcOf g C x v) d
        - reactionFormAt F g x a b c (lcOf g D x v) := by
    simp only [covReactionFormAt, Φ, A, B, C, D]
  -- the array derivative is `∇Rm`
  have hY : mvfderiv I (fun y : M => Rxn.rmFrameField g V y) x v = Rxn.dRmArr g x v := by
    rw [Work.Diff.GE.covRxnA.mvfderiv_rmFrameField (I := I) (M := M) hLC g V hVs x v]
    funext i j k l
    simp only [Rxn.dRmArr]
    rw [hVv i, hVv j, hVv k, hVv l, hVx i, hVx j, hVx k, hVx l]
    simp only [hrmP0, hrmP0', hrmP0'', hrmP0''', add_zero]
  -- derivative of `F(Rm)`
  have hEfderiv : ∀ i j k l, mvfderiv I (Ef i j k l) x v
      = (fderiv ℝ F (Rxn.rmFrameField g V x) (Rxn.dRmArr g x v)) i j k l := by
    intro i j k l
    have h := Work.Diff.GE.covRxnA.mvfderiv_F_rmFrameField (I := I) (M := M) hLC F hFdiff g V
      hVs x v i j k l
    rw [hY] at h
    exact h
  -- derivative of the coefficients
  have hP₁x : ∀ i, P₁ i x = g.inner x (onFrame g x i) a := by
    intro i; simp only [P₁, hVx i, hAx]
  have hP₂x : ∀ j, P₂ j x = g.inner x (onFrame g x j) b := by
    intro j; simp only [P₂, hVx j, hBx]
  have hP₃x : ∀ k, P₃ k x = g.inner x (onFrame g x k) c := by
    intro k; simp only [P₃, hVx k, hCx]
  have hP₄x : ∀ l, P₄ l x = g.inner x (onFrame g x l) d := by
    intro l; simp only [P₄, hVx l, hDx]
  have hdP₁ : ∀ i, mvfderiv I (P₁ i) x v = g.inner x (onFrame g x i) (lcOf g A x v) := by
    intro i
    have h := Rxn.mvfderiv_inner_lc (I := I) (M := M) g x v (hVs i) hAs
    rw [hVv i, hVx i] at h
    simp only [map_zero, zero_apply, zero_add] at h
    simpa only [P₁] using h
  have hdP₂ : ∀ j, mvfderiv I (P₂ j) x v = g.inner x (onFrame g x j) (lcOf g B x v) := by
    intro j
    have h := Rxn.mvfderiv_inner_lc (I := I) (M := M) g x v (hVs j) hBs
    rw [hVv j, hVx j] at h
    simp only [map_zero, zero_apply, zero_add] at h
    simpa only [P₂] using h
  have hdP₃ : ∀ k, mvfderiv I (P₃ k) x v = g.inner x (onFrame g x k) (lcOf g C x v) := by
    intro k
    have h := Rxn.mvfderiv_inner_lc (I := I) (M := M) g x v (hVs k) hCs
    rw [hVv k, hVx k] at h
    simp only [map_zero, zero_apply, zero_add] at h
    simpa only [P₃] using h
  have hdP₄ : ∀ l, mvfderiv I (P₄ l) x v = g.inner x (onFrame g x l) (lcOf g D x v) := by
    intro l
    have h := Rxn.mvfderiv_inner_lc (I := I) (M := M) g x v (hVs l) hDs
    rw [hVv l, hVx l] at h
    simp only [map_zero, zero_apply, zero_add] at h
    simpa only [P₄] using h
  have hCfderiv : ∀ i j k l, mvfderiv I (Cf i j k l) x v
      = P₂ j x * P₃ k x * P₄ l x * mvfderiv I (P₁ i) x v
        + P₁ i x * P₃ k x * P₄ l x * mvfderiv I (P₂ j) x v
        + P₁ i x * P₂ j x * P₄ l x * mvfderiv I (P₃ k) x v
        + P₁ i x * P₂ j x * P₃ k x * mvfderiv I (P₄ l) x v := by
    intro i j k l
    simpa only [Cf] using Rxn.mvfderiv_prod4 (I := I) (M := M) (P₁ i) (P₂ j) (P₃ k) (P₄ l)
      (hP₁ i) (hP₂ j) (hP₃ k) (hP₄ l) x v
  -- derivative of `Ψ`
  have hΨ : mvfderiv I Ψ x v = ∑ i, ∑ j, ∑ k, ∑ l,
      (Cf i j k l x * mvfderiv I (Ef i j k l) x v
        + Ef i j k l x * mvfderiv I (Cf i j k l) x v) := by
    show mvfderiv I (fun y : M => ∑ i, ∑ j, ∑ k, ∑ l, Cf i j k l y * Ef i j k l y) x v = _
    exact Rxn.mvfderiv_sum4_prod Cf Ef hCf hEf x v
  -- the first half: the contraction of `fderiv F (rmC)` with `∇Rm`
  have hrc : Rxn.rmFrameField g V x = rmC g x := by
    funext i j k l
    simp only [Rxn.rmFrameField, rmC, rmFrame, rmP, hVx]
  have hfirst : (∑ i, ∑ j, ∑ k, ∑ l, Cf i j k l x * mvfderiv I (Ef i j k l) x v)
      = Rxn.pairing g x a b c d (fderiv ℝ F (rmC g x) (Rxn.dRmArr g x v)) := by
    simp only [hEfderiv, hrc]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Rxn.pairing, Cf, hP₁x i, hP₂x j, hP₃x k, hP₄x l]
  -- the second half: the four tensorialising corrections
  have hsecond : (∑ i, ∑ j, ∑ k, ∑ l, Ef i j k l x * mvfderiv I (Cf i j k l) x v)
      = reactionFormAt F g x (lcOf g A x v) b c d + reactionFormAt F g x a (lcOf g B x v) c d
        + reactionFormAt F g x a b (lcOf g C x v) d
        + reactionFormAt F g x a b c (lcOf g D x v) := by
    have hsplit : (∑ i, ∑ j, ∑ k, ∑ l, Ef i j k l x * mvfderiv I (Cf i j k l) x v)
        = ∑ i, ∑ j, ∑ k, ∑ l, Ef i j k l x * (P₂ j x * P₃ k x * P₄ l x * mvfderiv I (P₁ i) x v
            + P₁ i x * P₃ k x * P₄ l x * mvfderiv I (P₂ j) x v
            + P₁ i x * P₂ j x * P₄ l x * mvfderiv I (P₃ k) x v
            + P₁ i x * P₂ j x * P₃ k x * mvfderiv I (P₄ l) x v) := by
      simp only [hCfderiv]
    rw [hsplit, Rxn.sum_prod4_deriv]
    have hrc : Rxn.rmFrameField g V x = rmC g x := by
      funext i j k l
      simp only [Rxn.rmFrameField, rmC, rmFrame, rmP, hVx]
    have e1 : (∑ i, ∑ j, ∑ k, ∑ l,
          (mvfderiv I (P₁ i) x v * P₂ j x * P₃ k x * P₄ l x) * Ef i j k l x)
        = reactionFormAt F g x (lcOf g A x v) b c d := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [reactionFormAt, Ef, hrc, hdP₁ i, hP₂x j, hP₃x k, hP₄x l]
      try ring
    have e2 : (∑ i, ∑ j, ∑ k, ∑ l,
          (P₁ i x * mvfderiv I (P₂ j) x v * P₃ k x * P₄ l x) * Ef i j k l x)
        = reactionFormAt F g x a (lcOf g B x v) c d := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [reactionFormAt, Ef, hrc, hP₁x i, hdP₂ j, hP₃x k, hP₄x l]
      try ring
    have e3 : (∑ i, ∑ j, ∑ k, ∑ l,
          (P₁ i x * P₂ j x * mvfderiv I (P₃ k) x v * P₄ l x) * Ef i j k l x)
        = reactionFormAt F g x a b (lcOf g C x v) d := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [reactionFormAt, Ef, hrc, hP₁x i, hP₂x j, hdP₃ k, hP₄x l]
      try ring
    have e4 : (∑ i, ∑ j, ∑ k, ∑ l,
          (P₁ i x * P₂ j x * P₃ k x * mvfderiv I (P₄ l) x v) * Ef i j k l x)
        = reactionFormAt F g x a b c (lcOf g D x v) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [reactionFormAt, Ef, hrc, hP₁x i, hP₂x j, hP₃x k, hdP₄ l]
      try ring
    rw [e1, e2, e3, e4]
  -- putting the two halves together
  have hmain : covReactionFormAt F g x v a b c d
      = Rxn.pairing g x a b c d (fderiv ℝ F (rmC g x) (Rxn.dRmArr g x v)) := by
    rw [hcov, hderiv, hΨ]
    rw [show (∑ i, ∑ j, ∑ k, ∑ l, (Cf i j k l x * mvfderiv I (Ef i j k l) x v
        + Ef i j k l x * mvfderiv I (Cf i j k l) x v))
        = (∑ i, ∑ j, ∑ k, ∑ l, Cf i j k l x * mvfderiv I (Ef i j k l) x v)
          + (∑ i, ∑ j, ∑ k, ∑ l, Ef i j k l x * mvfderiv I (Cf i j k l) x v) from by
          simp only [Finset.sum_add_distrib]]
    rw [hfirst, hsecond]
    ring
  -- the bound
  rw [hmain]
  have hrm : ‖rmC g x‖ ≤ Real.sqrt (rmNormSq g x) := (Rxn.curv4_norm_bounds (rmC g x)).1
  have hdv : ‖Rxn.dRmArr g x v‖ ≤ Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x) := by
    refine ((Rxn.curv4_norm_bounds (Rxn.dRmArr g x v)).1).trans ?_
    exact Work.Diff.GE.covRxnA.dRmArr_norm_le_t2 (I := I) (M := M) hLC g x v
  have hop : ‖fderiv ℝ F (rmC g x) (Rxn.dRmArr g x v)‖
      ≤ (CF' * Real.sqrt (rmNormSq g x)) * (Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x)) := by
    refine (ContinuousLinearMap.le_opNorm (fderiv ℝ F (rmC g x)) (Rxn.dRmArr g x v)).trans ?_
    refine mul_le_mul ?_ hdv (norm_nonneg _) ?_
    · exact (hCF' (rmC g x)).trans (mul_le_mul_of_nonneg_left hrm hCF'0)
    · exact mul_nonneg hCF'0 (Real.sqrt_nonneg _)
  have hsq : Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
        ((fderiv ℝ F (rmC g x) (Rxn.dRmArr g x v)) i j k l) ^ 2)
      ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (CF' * Real.sqrt (rmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x))) := by
    refine ((Rxn.curv4_norm_bounds (fderiv ℝ F (rmC g x) (Rxn.dRmArr g x v))).2).trans ?_
    exact mul_le_mul_of_nonneg_left hop (sq_nonneg _)
  have hpair := Work.Diff.GE.covRxnA.pairing_le (I := I) (M := M) g x a b c d
    (fderiv ℝ F (rmC g x) (Rxn.dRmArr g x v))
  have hPa : 0 ≤ Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
      * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d) := by positivity
  calc Rxn.pairing g x a b c d (fderiv ℝ F (rmC g x) (Rxn.dRmArr g x v))
      ≤ Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
            ((fderiv ℝ F (rmC g x) (Rxn.dRmArr g x v)) i j k l) ^ 2)
          * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
            * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := hpair
    _ ≤ ((Module.finrank ℝ E : ℝ) ^ 2 * (CF' * Real.sqrt (rmNormSq g x)
            * (Real.sqrt (g.inner x v v) * Real.sqrt (dRmNormSq g x))))
          * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
            * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) :=
        mul_le_mul_of_nonneg_right hsq hPa
    _ = ((Module.finrank ℝ E : ℝ) ^ 2 * CF') * Real.sqrt (rmNormSq g x)
          * Real.sqrt (dRmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
            * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
            * Real.sqrt (g.inner x d d)) := by ring


end Work.Diff.GE
