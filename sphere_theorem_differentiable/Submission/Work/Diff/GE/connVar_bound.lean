import Mathlib
import Submission.Work.Diff.Evol.RicDeriv
import Submission.Work.Diff.Evol.RicPhi
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.dRmPhi_bind_snd
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.RL.covRm_linear_fst
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.Gest.Base
import Submission.Work.Diff.GE.MovingFrame.covRm5_contMultilinear_bound
import Submission.Work.Diff.GE.ricAt_eq_sum_frame
import Submission.Work.Diff.GE.dRicPhi_eq_sum_covRm
import Submission.Commons.Geometry.Manifold.Riemannian.metricCompatible_scaleMetric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]

/-! ### Plumbing: joint smoothness on an open interval, and `dtMet` along a Ricci flow -/

theorem jointSmooth_Ioo_of_Ico
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ)
    (h : Submission.Diff.JointSmooth G (Set.Ico 0 T)) :
    Submission.Diff.JointSmooth G (Set.Ioo 0 T) :=
  h.mono (Set.prod_mono Set.Ioo_subset_Ico_self (Subset.refl _))

theorem dtMet_eq_ric_of_flow
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hflow : Submission.Diff.IsRicciFlow G T)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 T) (x : M) (u v : TangentSpace I x) :
    Submission.Diff.dtMet G t x u v
      = -2 * Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) x u v := by
  have hmem : t ∈ Set.Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have hnb : Set.Ico (0 : ℝ) T ∈ 𝓝 t :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ico_self
  have hd := hflow.2 t hmem x u v
  rw [Submission.Diff.dtMet, (hd.hasDerivAt hnb).deriv]

/-- Nonnegativity of the metric squared norm, from the positivity axiom. -/
theorem smet_inner_self_nonneg (g : Submission.Diff.SMet I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with h | h
  · subst h; simp
  · exact le_of_lt (g.pos x v h)

section ComponentBound

/-- **Component bound for `∇Rm`**: `|(∇Rm)(v,a,b,c,d)| ≤ √|∇Rm|² · ∏ √(g(·,·))`.
Obtained from the fact (`Work.Diff.GE.MovingFrame.covRm5_contMultilinear_bound`) that `∇Rm` is a
continuous multilinear form whose operator norm is bounded by `√|∇Rm|²`. -/
theorem covRm_component_le [T2Space M] (hLC : Submission.Diff.LCSmooth I M)
    (g : Submission.Diff.SMet I M) (x : M) (v a b c d : TangentSpace I x) :
    |Submission.Diff.covRm g x v a b c d|
      ≤ Real.sqrt (Submission.Diff.dRmNormSq g x)
        * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
           * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
           * Real.sqrt (g.inner x d d)) := by
  obtain ⟨A, hA, hAb⟩ :=
    Work.Diff.GE.MovingFrame.covRm5_contMultilinear_bound (I := I) (M := M) hLC g x
  have h1 := hAb (![v, a, b, c, d] : Fin 5 → TangentSpace I x)
  rw [Work.Diff.GE.MovingFrame.dRmNorm] at h1
  have h2 : Work.Diff.GE.MovingFrame.covRm5 g x (![v, a, b, c, d] : Fin 5 → TangentSpace I x)
      = Submission.Diff.covRm g x v a b c d := by
    simp [Work.Diff.GE.MovingFrame.covRm5]
  have h3 : Work.Diff.GE.MovingFrame.argNorms g x (![v, a, b, c, d] : Fin 5 → TangentSpace I x)
      = Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
        * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d) := by
    rw [Work.Diff.GE.MovingFrame.argNorms, Fin.prod_univ_five]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val]
  have hAw := hA (![v, a, b, c, d] : Fin 5 → TangentSpace I x)
  rw [hAw, h2, h3] at h1
  exact h1

/-- **Bound on the metric trace of `∇Rm`**: the frame contraction
`∑ m, (∇_v Rm)(e_m, a, e_m, b)` is bounded by `√|∇Rm|²` times the three `g`-norms, with a constant
that depends only on `finrank ℝ E`. -/
theorem sum_covRm_le_dRmNormSq [T2Space M] (hLC : Submission.Diff.LCSmooth I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Submission.Diff.SMet I M) (x : M) (v a b : TangentSpace I x),
      |(Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun m => Submission.Diff.covRm g x v (Submission.Diff.onFrame g x m) a
            (Submission.Diff.onFrame g x m) b)|
        ≤ C * Real.sqrt (Submission.Diff.dRmNormSq g x)
          * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
          * Real.sqrt (g.inner x b b) := by
  refine ⟨(Module.finrank ℝ E : ℝ), by positivity, ?_⟩
  intro g x v a b
  have he : Submission.Diff.IsONFrame g x (Submission.Diff.onFrame g x) :=
    Work.Diff.GE.isONFrame_onFrame (I := I) (M := M) g x
  have hterm : ∀ m : Fin (Module.finrank ℝ E),
      |Submission.Diff.covRm g x v (Submission.Diff.onFrame g x m) a
          (Submission.Diff.onFrame g x m) b|
        ≤ Real.sqrt (Submission.Diff.dRmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
             * Real.sqrt (g.inner x b b)) := by
    intro m
    have h := covRm_component_le (I := I) (M := M) hLC g x v (Submission.Diff.onFrame g x m) a
      (Submission.Diff.onFrame g x m) b
    have hm : Real.sqrt (g.inner x (Submission.Diff.onFrame g x m)
        (Submission.Diff.onFrame g x m)) = 1 := by
      rw [he m m]
      simp
    rw [hm] at h
    refine le_trans h (le_of_eq ?_)
    ring
  calc |(Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
        (fun m => Submission.Diff.covRm g x v (Submission.Diff.onFrame g x m) a
          (Submission.Diff.onFrame g x m) b)|
      ≤ (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun m => |Submission.Diff.covRm g x v (Submission.Diff.onFrame g x m) a
            (Submission.Diff.onFrame g x m) b|) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun _ => Real.sqrt (Submission.Diff.dRmNormSq g x)
            * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
               * Real.sqrt (g.inner x b b))) := Finset.sum_le_sum (fun m _ => hterm m)
    _ = (Module.finrank ℝ E : ℝ) * (Real.sqrt (Submission.Diff.dRmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
             * Real.sqrt (g.inner x b b))) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Module.finrank ℝ E : ℝ) * Real.sqrt (Submission.Diff.dRmNormSq g x)
          * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
          * Real.sqrt (g.inner x b b) := by ring

end ComponentBound

/-! ### `covDerivSym2` with the Ricci tensor in the role of `h` -/

-- `covDerivSym2 (lcOf g) (ricAt (lcOf g)) X Y Z x` is the `Ext` pattern `dRicPhi` of `∇Ric`.
theorem covDerivSym2_ricAt_eq_dRicPhi
    (g : Submission.Diff.SMet I M) (x : M) (X Y Z : Π y : M, TangentSpace I y) :
    Submission.Diff.covDerivSym2 (Submission.Diff.lcOf g)
        (fun y a b => Submission.Diff.ricAt (Submission.Diff.lcOf g) y a b) X Y Z x
      = Work.Diff.Evol.dRicPhi g x (X x) Y Z := by
  rw [Submission.Diff.covDerivSym2, Work.Diff.Evol.dRicPhi]
  rfl

-- `covDerivSym2` is linear in the bilinear form `h`.
theorem covDerivSym2_const_mul
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (c : ℝ)
    (h : Π y : M, TangentSpace I y → TangentSpace I y → ℝ)
    (X Y Z : Π y : M, TangentSpace I y) (x : M) :
    Submission.Diff.covDerivSym2 cov (fun y a b => c * h y a b) X Y Z x
      = c * Submission.Diff.covDerivSym2 cov h X Y Z x := by
  have hfun : (fun y : M => c * h y (Y y) (Z y))
      = (fun y : M => c • (fun y' : M => h y' (Y y') (Z y')) y) := by
    funext y
    rw [smul_eq_mul]
  rw [Submission.Diff.covDerivSym2, Submission.Diff.covDerivSym2, hfun,
    Commons.Geometry.Manifold.Riemannian.mvfderiv_const_smul]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-! ### Arithmetic core of the final estimate -/

theorem sq_le_sq_of_sqrt_le {P M : ℝ} (hP : 0 ≤ P) (h : Real.sqrt P ≤ M) : P ≤ M ^ 2 := by
  have h0 : 0 ≤ Real.sqrt P := Real.sqrt_nonneg P
  calc P = Real.sqrt P ^ 2 := (Real.sq_sqrt hP).symm
    _ ≤ M ^ 2 := by nlinarith [h, h0]

theorem sqrt_le_of_le_mul_sqrt {P M : ℝ} (hP : 0 ≤ P) (hM : 0 ≤ M) (h : P ≤ M * Real.sqrt P) :
    Real.sqrt P ≤ M := by
  have hs : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP
  have h0 : 0 ≤ Real.sqrt P := Real.sqrt_nonneg P
  rcases lt_or_eq_of_le h0 with hpos | heq
  · have h2 : Real.sqrt P * Real.sqrt P ≤ M * Real.sqrt P := by
      calc Real.sqrt P * Real.sqrt P = P := by rw [← sq, hs]
        _ ≤ M * Real.sqrt P := h
    exact le_of_mul_le_mul_right h2 hpos
  · rw [← heq]; exact hM

/-- The three-term estimate: if `bA = ½(-2S₁ - 2S₂ + 2S₃)` and each `Sᵢ` is bounded by
`C₀√D·(product of the three norms)`, then `bA ≤ 9C₀²·D·bV·bW`. -/
theorem connVar_arith (C₀ D bV bW bA S1 S2 S3 : ℝ) (hC₀ : 0 ≤ C₀) (hD : 0 ≤ D)
    (hV : 0 ≤ bV) (hW : 0 ≤ bW) (hA0 : 0 ≤ bA)
    (h1 : |S1| ≤ C₀ * Real.sqrt D * Real.sqrt bV * Real.sqrt bW * Real.sqrt bA)
    (h2 : |S2| ≤ C₀ * Real.sqrt D * Real.sqrt bW * Real.sqrt bV * Real.sqrt bA)
    (h3 : |S3| ≤ C₀ * Real.sqrt D * Real.sqrt bA * Real.sqrt bV * Real.sqrt bW)
    (hp : bA = (1 / 2 : ℝ) * ((-2) * S1 + (-2) * S2 - (-2) * S3)) :
    bA ≤ 9 * C₀ ^ 2 * D * bV * bW := by
  have hsD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  have hsV : 0 ≤ Real.sqrt bV := Real.sqrt_nonneg bV
  have hsW : 0 ≤ Real.sqrt bW := Real.sqrt_nonneg bW
  have hsA : 0 ≤ Real.sqrt bA := Real.sqrt_nonneg bA
  have hD2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
  have hV2 : Real.sqrt bV ^ 2 = bV := Real.sq_sqrt hV
  have hW2 : Real.sqrt bW ^ 2 = bW := Real.sq_sqrt hW
  have habs : |(-2 : ℝ)| = 2 := by norm_num
  have e1 : |(-2) * S1| ≤ 2 * (C₀ * Real.sqrt D * Real.sqrt bV * Real.sqrt bW * Real.sqrt bA) := by
    rw [abs_mul, habs]
    linarith [h1]
  have e2 : |(-2) * S2| ≤ 2 * (C₀ * Real.sqrt D * Real.sqrt bW * Real.sqrt bV * Real.sqrt bA) := by
    rw [abs_mul, habs]
    linarith [h2]
  have e3 : |(-2) * S3| ≤ 2 * (C₀ * Real.sqrt D * Real.sqrt bA * Real.sqrt bV * Real.sqrt bW) := by
    rw [abs_mul, habs]
    linarith [h3]
  have htri : (-2) * S1 + (-2) * S2 - (-2) * S3 ≤ |(-2) * S1| + |(-2) * S2| + |(-2) * S3| := by
    have a := neg_le_abs ((-2) * S3)
    have b := le_abs_self ((-2) * S1)
    have c := le_abs_self ((-2) * S2)
    linarith
  have hstep : bA ≤ 3 * (C₀ * Real.sqrt D * Real.sqrt bV * Real.sqrt bW) * Real.sqrt bA := by
    have hmono : (1 / 2 : ℝ) * ((-2) * S1 + (-2) * S2 - (-2) * S3)
        ≤ (1 / 2 : ℝ) * (|(-2) * S1| + |(-2) * S2| + |(-2) * S3|) := by linarith [htri]
    have hsum3 : (1 / 2 : ℝ) * (|(-2) * S1| + |(-2) * S2| + |(-2) * S3|)
        ≤ (1 / 2 : ℝ) * (2 * (C₀ * Real.sqrt D * Real.sqrt bV * Real.sqrt bW * Real.sqrt bA)
            + 2 * (C₀ * Real.sqrt D * Real.sqrt bW * Real.sqrt bV * Real.sqrt bA)
            + 2 * (C₀ * Real.sqrt D * Real.sqrt bA * Real.sqrt bV * Real.sqrt bW)) := by
      linarith [e1, e2, e3]
    calc bA = (1 / 2 : ℝ) * ((-2) * S1 + (-2) * S2 - (-2) * S3) := hp
      _ ≤ (1 / 2 : ℝ) * (|(-2) * S1| + |(-2) * S2| + |(-2) * S3|) := hmono
      _ ≤ (1 / 2 : ℝ) * (2 * (C₀ * Real.sqrt D * Real.sqrt bV * Real.sqrt bW * Real.sqrt bA)
            + 2 * (C₀ * Real.sqrt D * Real.sqrt bW * Real.sqrt bV * Real.sqrt bA)
            + 2 * (C₀ * Real.sqrt D * Real.sqrt bA * Real.sqrt bV * Real.sqrt bW)) := hsum3
      _ = 3 * (C₀ * Real.sqrt D * Real.sqrt bV * Real.sqrt bW) * Real.sqrt bA := by ring
  have hM0 : 0 ≤ 3 * (C₀ * Real.sqrt D * Real.sqrt bV * Real.sqrt bW) := by positivity
  have hle := sqrt_le_of_le_mul_sqrt hA0 hM0 hstep
  have hsq := sq_le_sq_of_sqrt_le hA0 hle
  calc bA ≤ (3 * (C₀ * Real.sqrt D * Real.sqrt bV * Real.sqrt bW)) ^ 2 := hsq
    _ = 9 * C₀ ^ 2 * D * bV * bW := by
        rw [show (3 * (C₀ * Real.sqrt D * Real.sqrt bV * Real.sqrt bW)) ^ 2
              = 9 * C₀ ^ 2 * Real.sqrt D ^ 2 * Real.sqrt bV ^ 2 * Real.sqrt bW ^ 2 by ring,
          hD2, hV2, hW2]

/-! ### The assembly

The two mathematical inputs are
* `hric : dRicPhi g x v Y Z = ∑ m, covRm g x v (e_m) (Y x) (e_m) (Z x)` (the trace identity for
  `∇Ric`, proved in `Work.Diff.GE.dRicPhi_eq_sum_covRm` from the pointwise trace identity of the
  Ricci tensor), and
* `hsumbd : |∑ m, (∇_v Rm)(e_m, a, e_m, b)| ≤ C √|∇Rm|² ‖v‖ ‖a‖ ‖b‖` with `C` uniform in the metric
  (proved in `Work.Diff.GE.sum_covRm_le_dRmNormSq`, from the multilinearity of `∇Rm`). -/

theorem connVar_bound_aux
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    (hric : ∀ (g : Submission.Diff.SMet I M) (x : M) (v : TangentSpace I x)
        (Y Z : Π y : M, TangentSpace I y),
        SmoothField (I := I) (M := M) Y → SmoothField (I := I) (M := M) Z →
        Work.Diff.Evol.dRicPhi g x v Y Z
          = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
              (fun m => Submission.Diff.covRm g x v (Submission.Diff.onFrame g x m) (Y x)
                (Submission.Diff.onFrame g x m) (Z x)))
    (hsumbd : ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Submission.Diff.SMet I M) (x : M)
        (v a b : TangentSpace I x),
        |(Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
            (fun m => Submission.Diff.covRm g x v (Submission.Diff.onFrame g x m) a
              (Submission.Diff.onFrame g x m) b)|
          ≤ C * Real.sqrt (Submission.Diff.dRmNormSq g x)
            * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
            * Real.sqrt (g.inner x b b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ),
      Submission.Diff.IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M,
      ∀ (V W : Π y : M, TangentSpace I y),
        SmoothField (I := I) (M := M) V →
        SmoothField (I := I) (M := M) W →
      ∀ (w : TangentSpace I x),
        HasDerivAt (fun s ↦ ((Submission.Diff.lcOf (G s) W x (V x) : TangentSpace I x) : E))
            (w : E) t →
        (G t).inner x w w ≤ C * Submission.Diff.dRmNormSq (G t) x
          * (G t).inner x (V x) (V x) * (G t).inner x (W x) (W x) := by
  obtain ⟨C₀, hC₀, hbnd⟩ := hsumbd
  refine ⟨9 * C₀ ^ 2, by positivity, ?_⟩
  intro G T hflow t ht x V W hV hW w hw
  -- the first variation formula of the Levi-Civita connection
  obtain ⟨A, hA, hform⟩ := hLV G (Set.Ioo 0 T) isOpen_Ioo
    (jointSmooth_Ioo_of_Ico G T hflow.1) t ht V W hV hW x
  -- the hypothesis identifies the derivative
  set φ : ℝ → E := fun s ↦
    ((Submission.Diff.lcOf (G s) W x (V x) : TangentSpace I x) : E) with hφ
  have hwφ : HasDerivAt φ (w : E) t := hw
  have hAφ : HasDerivAt φ (A : E) t := hA
  have hwA : w = A := by
    have h1 : (w : E) = (A : E) := (hwφ.deriv).symm.trans hAφ.deriv
    exact h1
  rw [hwA]
  -- the test field: a smooth extension of `A`
  set Z : Π y : M, TangentSpace I y := Submission.Diff.smoothExt x A with hZ
  have hZsm : SmoothField (I := I) (M := M) Z := Work.Diff.GE.smoothExt_cmdiff x A
  have hZx : Z x = A := Work.Diff.GE.smoothExt_apply x A
  -- each `covDerivSym2` with `h = dtMet` is minus twice a metric trace of `∇Rm`
  have hricform : ∀ (X Y' Z' : Π y : M, TangentSpace I y),
      SmoothField (I := I) (M := M) X → SmoothField (I := I) (M := M) Y' →
      SmoothField (I := I) (M := M) Z' →
      Submission.Diff.covDerivSym2 (Submission.Diff.lcOf (G t))
          (fun y a b => Submission.Diff.dtMet G t y a b) X Y' Z' x
        = -2 * (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
            (fun m => Submission.Diff.covRm (G t) x (X x)
              (Submission.Diff.onFrame (G t) x m) (Y' x)
              (Submission.Diff.onFrame (G t) x m) (Z' x)) := by
    intro X Y' Z' hX hY' hZ'
    rw [show (fun y a b => Submission.Diff.dtMet G t y a b)
        = (fun y a b => (-2 : ℝ) * Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y a b)
        from by
      funext y a b
      exact dtMet_eq_ric_of_flow G T hflow t ht y a b]
    rw [covDerivSym2_const_mul, covDerivSym2_ricAt_eq_dRicPhi]
    rw [hric (G t) x (X x) Y' Z' hY' hZ']
  -- the bounds, converted into the sums over the orthonormal frame
  have hS1 := hbnd (G t) x (V x) (W x) A
  have hS2 := hbnd (G t) x (W x) (V x) A
  have hS3 := hbnd (G t) x A (V x) (W x)
  -- the pairing identity
  have hp := hform Z hZsm
  rw [hricform V W Z hV hW hZsm, hricform W V Z hW hV hZsm,
    hricform Z V W hZsm hV hW] at hp
  rw [hZx] at hp
  -- positivity
  have hD0 : 0 ≤ Submission.Diff.dRmNormSq (G t) x := Work.Diff.GE.Gest.dRmNormSq_nonneg (G t) x
  have hV0 : 0 ≤ (G t).inner x (V x) (V x) := smet_inner_self_nonneg (G t) x (V x)
  have hW0 : 0 ≤ (G t).inner x (W x) (W x) := smet_inner_self_nonneg (G t) x (W x)
  have hA0 : 0 ≤ (G t).inner x A A := smet_inner_self_nonneg (G t) x A
  exact connVar_arith C₀ (Submission.Diff.dRmNormSq (G t) x) ((G t).inner x (V x) (V x))
    ((G t).inner x (W x) (W x)) ((G t).inner x A A)
    ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
      (fun m => Submission.Diff.covRm (G t) x (V x)
        (Submission.Diff.onFrame (G t) x m) (W x) (Submission.Diff.onFrame (G t) x m) A))
    ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
      (fun m => Submission.Diff.covRm (G t) x (W x)
        (Submission.Diff.onFrame (G t) x m) (V x) (Submission.Diff.onFrame (G t) x m) A))
    ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
      (fun m => Submission.Diff.covRm (G t) x A
        (Submission.Diff.onFrame (G t) x m) (V x) (Submission.Diff.onFrame (G t) x m) (W x)))
    hC₀ hD0 hV0 hW0 hA0 hS1 hS2 hS3 hp

theorem connVar_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ),
      Submission.Diff.IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M,
      ∀ (V W : Π y : M, TangentSpace I y),
        Work.Diff.GE.SmoothField (I := I) (M := M) V →
        Work.Diff.GE.SmoothField (I := I) (M := M) W →
      ∀ (w : TangentSpace I x),
        HasDerivAt (fun s ↦ ((Submission.Diff.lcOf (G s) W x (V x) : TangentSpace I x) : E))
            (w : E) t →
        (G t).inner x w w ≤ C * Submission.Diff.dRmNormSq (G t) x
          * (G t).inner x (V x) (V x) * (G t).inner x (W x) (W x) := by
  have htr : ∀ (g : Submission.Diff.SMet I M) (y : M)
      (e : Fin (Module.finrank ℝ E) → TangentSpace I y),
      Submission.Diff.IsONFrame g y e → ∀ u v : TangentSpace I y,
        Submission.Diff.ricAt (Submission.Diff.lcOf g) y u v
          = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
              (fun m => Submission.Diff.rmP g y (e m) u (e m) v) :=
    fun g y e he u v => Work.Diff.GE.ricAt_eq_sum_frame (I := I) (M := M) hLC g y e he u v
  exact connVar_bound_aux hLC hLV
    (fun g x v Y Z hY hZ => Work.Diff.GE.dRicPhi_eq_sum_covRm (I := I) (M := M) hLC htr g x v Y Z hY hZ)
    (sum_covRm_le_dRmNormSq (I := I) (M := M) hLC)

end Work.Diff.GE
