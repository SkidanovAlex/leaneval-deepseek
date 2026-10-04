/-
Smooth-`∞` versions of the `∇Ric` trace identity and the first-variation bound for the
Levi-Civita connection.

`Submission/Work/Diff/GE/{dRicPhi_eq_sum_covRm,covRic_eq_sum_covRm,connVar_bound}.lean` state
their main theorems with the *analytic* hypothesis `[IsManifold I ω M]`, whereas the frozen
interfaces (`Submission/Diff/Interfaces.lean`) live at the smooth level `[IsManifold I ∞ M]`.
Nothing in the statements or in the proofs below uses more than `∞`, so we re-run them here at the
smooth level.  (The auxiliary lemmas of those files are already at `∞`; only `connVar_bound.lean`
carries its own plumbing at `ω`, which is duplicated below.)
-/
import Mathlib
import Submission.Work.Diff.GE.connVar_bound
import Submission.Work.Diff.GE.dRicPhi_eq_sum_covRm
import Submission.Work.Diff.GE.covRic_eq_sum_covRm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Work.Diff.Evol

namespace Work.Diff.GE.Sm

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

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
* `hbound : |covRic g x v a b| ≤ C √|∇Rm|² ‖v‖ ‖a‖ ‖b‖` with `C` uniform in the metric (proved in
  `Work.Diff.GE.covRic_le_dRmNormSq`, using the trace identity in the form `hsum`). -/

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
    (hsum : ∀ (g : Submission.Diff.SMet I M) (x : M) (v a b : TangentSpace I x),
        Work.Diff.Evol.covRic g x v a b
          = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
              (fun m => Submission.Diff.covRm g x v (Submission.Diff.onFrame g x m) a
                (Submission.Diff.onFrame g x m) b))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Submission.Diff.SMet I M) (x : M)
        (v a b : TangentSpace I x),
        |Work.Diff.Evol.covRic g x v a b| ≤ C * Real.sqrt (Submission.Diff.dRmNormSq g x)
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
  obtain ⟨C₀, hC₀, hbnd⟩ := hbound
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
  rw [hsum (G t) x (V x) (W x) A] at hS1
  have hS2 := hbnd (G t) x (W x) (V x) A
  rw [hsum (G t) x (W x) (V x) A] at hS2
  have hS3 := hbnd (G t) x A (V x) (W x)
  rw [hsum (G t) x A (V x) (W x)] at hS3
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

theorem dRicPhi_eq_sum_covRm_sm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (htr : ∀ (g : Submission.Diff.SMet I M) (y : M)
        (e : Fin (Module.finrank ℝ E) → TangentSpace I y),
        Submission.Diff.IsONFrame g y e →
          ∀ u v : TangentSpace I y,
            Submission.Diff.ricAt (Submission.Diff.lcOf g) y u v
              = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
                  (fun m => Submission.Diff.rmP g y (e m) u (e m) v))
    (g : Submission.Diff.SMet I M) (x : M) (v : TangentSpace I x)
    (Y Z : Π y : M, TangentSpace I y)
    (hY : Work.Diff.GE.SmoothField (I := I) (M := M) Y)
    (hZ : Work.Diff.GE.SmoothField (I := I) (M := M) Z) :
    Work.Diff.Evol.dRicPhi g x v Y Z
      = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun m => Submission.Diff.covRm g x v (Submission.Diff.onFrame g x m) (Y x)
            (Submission.Diff.onFrame g x m) (Z x)) := by
  classical
  obtain ⟨W, hWs, hONev, hWx⟩ := exists_smooth_onframe (I := I) (M := M) g x
  have hONx : IsONFrame g x (fun m => W m x) := by
    have h : (fun i : Fin (Module.finrank ℝ E) => W i x) = onFrame g x := funext hWx
    rw [h]; exact isONFrame_onFrame g x
  -- expansion of a vector in the frame
  have hexp : ∀ a : TangentSpace I x, ∑ j, g.inner x a (W j x) • W j x = a :=
    fun a => sum_smul_inner_eq_self_gen (I := I) (M := M) g x (fun j => W j x) hONx a
  have hA_exp : ∀ m : Fin (Module.finrank ℝ E),
      lcOf g (W m) x v = ∑ j, g.inner x (lcOf g (W m) x v) (W j x) • W j x :=
    fun m => (hexp (lcOf g (W m) x v)).symm
  -- antisymmetry of the connection coefficients, from metric compatibility
  have hantiω : ∀ m j : Fin (Module.finrank ℝ E),
      g.inner x (lcOf g (W m) x v) (W j x)
        + g.inner x (lcOf g (W j) x v) (W m x) = 0 := by
    intro m j
    have hconst : (fun y : M => g.inner y (W m y) (W j y))
        =ᶠ[𝓝 x] (fun _ : M => (if m = j then (1 : ℝ) else 0)) := by
      filter_upwards [hONev] with y hy
      exact hy m j
    have hderiv0 : mvfderiv I (fun y : M => g.inner y (W m y) (W j y)) x v = 0 := by
      rw [mvfderiv_congr_eventuallyEq hconst]
      simp [mvfderiv_const]
    have h := kato_mvfderiv_inner_lc (I := I) (M := M) g x v (hWs m) (hWs j)
    rw [hderiv0] at h
    rw [g.symm x (W m x) (lcOf g (W j) x v)] at h
    exact h.symm
  -- congruence of `ricF g Y Z` with the traced field
  have hcongr : ricF g Y Z =ᶠ[𝓝 x]
      (fun y : M => ∑ m, rmP g y (W m y) (Y y) (W m y) (Z y)) := by
    filter_upwards [hONev] with y hy
    exact htr g y (fun m => W m y) hy (Y y) (Z y)
  have h1 : mvfderiv I (ricF g Y Z) x v
      = mvfderiv I (fun y : M => ∑ m, rmP g y (W m y) (Y y) (W m y) (Z y)) x v :=
    congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) (mvfderiv_congr_eventuallyEq hcongr)
  have hFs : ∀ m : Fin (Module.finrank ℝ E),
      CMDiff ∞ (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) :=
    fun m => rmP_fields_smooth (I := I) (M := M) hLC g (hWs m) hY (hWs m) hZ
  have h2 : mvfderiv I (fun y : M => ∑ m, rmP g y (W m y) (Y y) (W m y) (Z y)) x v
      = ∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) x v :=
    Kato3.mvfderiv_sum Finset.univ
      (fun m y => rmP g y (W m y) (Y y) (W m y) (Z y)) hFs x v
  -- the per-`m` decomposition
  have hper : ∀ m : Fin (Module.finrank ℝ E),
      mvfderiv I (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) x v
        = dRmPhi g x v (W m) Y (W m) Z
          + rmP g x (lcOf g (W m) x v) (Y x) (W m x) (Z x)
          + rmP g x (W m x) (lcOf g Y x v) (W m x) (Z x)
          + rmP g x (W m x) (Y x) (lcOf g (W m) x v) (Z x)
          + rmP g x (W m x) (Y x) (W m x) (lcOf g Z x v) := by
    intro m
    simp only [dRmPhi]
    ring
  have hsum : (∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) x v)
      = (∑ m, dRmPhi g x v (W m) Y (W m) Z)
        + (∑ m, rmP g x (lcOf g (W m) x v) (Y x) (W m x) (Z x))
        + (∑ m, rmP g x (W m x) (lcOf g Y x v) (W m x) (Z x))
        + (∑ m, rmP g x (W m x) (Y x) (lcOf g (W m) x v) (Z x))
        + (∑ m, rmP g x (W m x) (Y x) (W m x) (lcOf g Z x v)) := by
    rw [show (∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (Y y) (W m y) (Z y)) x v)
        = ∑ m, (dRmPhi g x v (W m) Y (W m) Z
          + rmP g x (lcOf g (W m) x v) (Y x) (W m x) (Z x)
          + rmP g x (W m x) (lcOf g Y x v) (W m x) (Z x)
          + rmP g x (W m x) (Y x) (lcOf g (W m) x v) (Z x)
          + rmP g x (W m x) (Y x) (W m x) (lcOf g Z x v)) from
      Finset.sum_congr rfl (fun m _ => hper m)]
    simp only [Finset.sum_add_distrib]
  -- the two `∇_v Y`, `∇_v Z` corrections are the two `ricAt` terms of `dRicPhi`
  have hc2 : (∑ m, rmP g x (W m x) (lcOf g Y x v) (W m x) (Z x))
      = ricAt (lcOf g) x (lcOf g Y x v) (Z x) := by
    rw [Finset.sum_congr rfl (fun m _ => by rw [hWx m])]
    exact (htr g x (onFrame g x) (isONFrame_onFrame g x) (lcOf g Y x v) (Z x)).symm
  have hc4 : (∑ m, rmP g x (W m x) (Y x) (W m x) (lcOf g Z x v))
      = ricAt (lcOf g) x (Y x) (lcOf g Z x v) := by
    rw [Finset.sum_congr rfl (fun m _ => by rw [hWx m])]
    exact (htr g x (onFrame g x) (isONFrame_onFrame g x) (Y x) (lcOf g Z x v)).symm
  -- the two `∇_v W_m` corrections cancel
  have hanti_sum :
      (∑ m, rmP g x (lcOf g (W m) x v) (Y x) (W m x) (Z x))
        + (∑ m, rmP g x (W m x) (Y x) (lcOf g (W m) x v) (Z x)) = 0 := by
    have hB₁ : ∀ (r s : ℝ) (u₁ u₂ w : TangentSpace I x),
        rmP g x (r • u₁ + s • u₂) (Y x) w (Z x)
          = r * rmP g x u₁ (Y x) w (Z x) + s * rmP g x u₂ (Y x) w (Z x) := by
      intro r s u₁ u₂ w
      rw [rmP_add_fst g hLC x, rmP_smul_fst g hLC x, rmP_smul_fst g hLC x]
    have hB₂ : ∀ (r s : ℝ) (u w₁ w₂ : TangentSpace I x),
        rmP g x u (Y x) (r • w₁ + s • w₂) (Z x)
          = r * rmP g x u (Y x) w₁ (Z x) + s * rmP g x u (Y x) w₂ (Z x) := by
      intro r s u w₁ w₂
      rw [rmP_add_thd g hLC x, rmP_smul_thd g hLC x, rmP_smul_thd g hLC x]
    have hmain := sum_bilinear_antisymm (V := TangentSpace I x)
      (B := fun u w => rmP g x u (Y x) w (Z x)) hB₁ hB₂
      (fun m => W m x) (fun m => lcOf g (W m) x v)
      (fun m j => g.inner x (lcOf g (W m) x v) (W j x)) hA_exp hantiω
    rw [Finset.sum_add_distrib] at hmain
    exact hmain
  have hcomb : (∑ m, dRmPhi g x v (W m) Y (W m) Z)
        + (∑ m, rmP g x (lcOf g (W m) x v) (Y x) (W m x) (Z x))
        + (∑ m, rmP g x (W m x) (lcOf g Y x v) (W m x) (Z x))
        + (∑ m, rmP g x (W m x) (Y x) (lcOf g (W m) x v) (Z x))
        + (∑ m, rmP g x (W m x) (Y x) (W m x) (lcOf g Z x v))
      = (∑ m, dRmPhi g x v (W m) Y (W m) Z)
        + ricAt (lcOf g) x (lcOf g Y x v) (Z x)
        + ricAt (lcOf g) x (Y x) (lcOf g Z x v) := by
    rw [hc2, hc4]
    linarith [hanti_sum]
  have hGd : mvfderiv I (ricF g Y Z) x v
      = (∑ m, dRmPhi g x v (W m) Y (W m) Z)
        + ricAt (lcOf g) x (lcOf g Y x v) (Z x)
        + ricAt (lcOf g) x (Y x) (lcOf g Z x v) := by
    rw [h1, h2, hsum, hcomb]
  have h3 : dRicPhi g x v Y Z = (∑ m, dRmPhi g x v (W m) Y (W m) Z) := by
    simp only [dRicPhi]
    rw [hGd]
    ring
  rw [h3]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [(Kato3.covRm_field_form (I := I) (M := M) hLC g x v (hWs m) hY (hWs m) hZ).symm, hWx m]


theorem covRic_eq_sum_covRm_sm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (htr : ∀ (g : Submission.Diff.SMet I M) (y : M)
        (e : Fin (Module.finrank ℝ E) → TangentSpace I y),
        Submission.Diff.IsONFrame g y e →
          ∀ u v : TangentSpace I y,
            Submission.Diff.ricAt (Submission.Diff.lcOf g) y u v
              = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
                  (fun m => Submission.Diff.rmP g y (e m) u (e m) v))
    (g : Submission.Diff.SMet I M) (x : M) (v a b : TangentSpace I x) :
    Work.Diff.Evol.covRic g x v a b
      = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun m => Submission.Diff.covRm g x v (Submission.Diff.onFrame g x m) a
            (Submission.Diff.onFrame g x m) b) := by
  classical
  -- a smooth `g`-orthonormal frame near `x` agreeing with the chosen frame at `x`
  have hVs : ∀ i : katoIdx E, CMDiff ∞ (T% (smoothExt x (onFrame g x i))) :=
    fun i => smoothExt_cmdiff x (onFrame g x i)
  have hVON : IsONFrame g x (fun i => smoothExt x (onFrame g x i) x) := by
    have h : (fun i => smoothExt x (onFrame g x i) x) = onFrame g x := by
      funext i; exact smoothExt_apply x (onFrame g x i)
    rw [h]; exact isONFrame_onFrame g x
  obtain ⟨hWs0, hWON0, hWx0⟩ :=
    covRic_onFrame_family g x (fun i => smoothExt x (onFrame g x i)) hVs hVON
  set W : katoIdx E → Π y : M, TangentSpace I y :=
    katoFrame g x (fun i => smoothExt x (onFrame g x i)) with hWdef
  have hWs : ∀ i : katoIdx E, CMDiff ∞ (T% (W i)) := fun i => by rw [hWdef]; exact hWs0 i
  have hWON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => W i y) := by rw [hWdef]; exact hWON0
  have hWx : ∀ i : katoIdx E, W i x = onFrame g x i := by
    intro i; rw [hWx0 i, smoothExt_apply]
  have hONx : IsONFrame g x (fun m => W m x) := hWON.self_of_nhds
  -- the smooth extensions of `a` and `b`
  set A : Π y : M, TangentSpace I y := smoothExt x a with hA
  set B : Π y : M, TangentSpace I y := smoothExt x b with hB
  have hAs : CMDiff ∞ (T% A) := by rw [hA]; exact smoothExt_cmdiff x a
  have hBs : CMDiff ∞ (T% B) := by rw [hB]; exact smoothExt_cmdiff x b
  have hAx : A x = a := by rw [hA]; exact smoothExt_apply x a
  have hBx : B x = b := by rw [hB]; exact smoothExt_apply x b
  -- `Ric` and the frame trace agree near `x`
  have hsm : ∀ m : katoIdx E,
      CMDiff ∞ (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) :=
    fun m => rmP_fields_smooth hLC g (hWs m) hAs (hWs m) hBs
  have hagree : (Work.Diff.Evol.ricF g A B)
      =ᶠ[𝓝 x] (fun y : M => ∑ m, rmP g y (W m y) (A y) (W m y) (B y)) := by
    filter_upwards [hWON] with y hy
    simpa only [Work.Diff.Evol.ricF] using htr g y (fun m => W m y) hy (A y) (B y)
  have hkey : mvfderiv I (Work.Diff.Evol.ricF g A B) x v
      = ∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) x v := by
    have h := mvfderiv_congr_eventuallyEq (I := I) hagree
    exact (congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) h).trans
      (Kato3.mvfderiv_sum Finset.univ _ hsm x v)
  have hric := Work.Diff.Evol.mvfderiv_ricF_eq (I := I) (M := M) g x v A B
  -- the definition of `dRmPhi` on the frame
  have hdRm : ∀ m : katoIdx E,
      dRmPhi g x v (W m) A (W m) B
        = mvfderiv I (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) x v
          - rmP g x (lcOf g (W m) x v) (A x) (W m x) (B x)
          - rmP g x (W m x) (lcOf g A x v) (W m x) (B x)
          - rmP g x (W m x) (A x) (lcOf g (W m) x v) (B x)
          - rmP g x (W m x) (A x) (W m x) (lcOf g B x v) := by
    intro m
    simp only [dRmPhi]
  -- summing the definition of `dRmPhi` gives an identity relating the five sums
  have h1 : (∑ m, dRmPhi g x v (W m) A (W m) B)
      + (∑ m, rmP g x (lcOf g (W m) x v) (A x) (W m x) (B x))
      + (∑ m, rmP g x (W m x) (lcOf g A x v) (W m x) (B x))
      + (∑ m, rmP g x (W m x) (A x) (lcOf g (W m) x v) (B x))
      + (∑ m, rmP g x (W m x) (A x) (W m x) (lcOf g B x v))
      = ∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) x v := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hdRm m]
    ring
  -- the two frame-derivative corrections cancel
  have hPR : (∑ m, rmP g x (lcOf g (W m) x v) (A x) (W m x) (B x))
      + (∑ m, rmP g x (W m x) (A x) (lcOf g (W m) x v) (B x)) = 0 :=
    covRic_frame_correction_zero hLC g x v W hWs hWON (A x) (B x)
  -- the two `∇A`, `∇B` corrections are the `ricAt` corrections
  have hQr : (∑ m, rmP g x (W m x) (lcOf g A x v) (W m x) (B x))
      = ricAt (lcOf g) x (lcOf g A x v) (B x) :=
    (htr g x (fun m => W m x) hONx (lcOf g A x v) (B x)).symm
  have hYr : (∑ m, rmP g x (W m x) (A x) (W m x) (lcOf g B x v))
      = ricAt (lcOf g) x (A x) (lcOf g B x v) :=
    (htr g x (fun m => W m x) hONx (A x) (lcOf g B x v)).symm
  have h2 : (∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) x v)
      = Work.Diff.Evol.dRicPhi g x v A B
        + ricAt (lcOf g) x (lcOf g A x v) (B x)
        + ricAt (lcOf g) x (A x) (lcOf g B x v) := by
    rw [← hkey, hric]
  -- the trace of `∇Rm` is `dRicPhi`
  have hmain : Work.Diff.Evol.dRicPhi g x v A B
      = ∑ m, dRmPhi g x v (W m) A (W m) B := by
    linarith [h1, h2, hPR, hQr, hYr]
  -- rewrite `dRmPhi` back into `covRm`
  have hper : ∀ m : katoIdx E,
      dRmPhi g x v (W m) A (W m) B = covRm g x v (onFrame g x m) a (onFrame g x m) b := by
    intro m
    have h := Kato3.covRm_field_form (X₁ := W m) (X₂ := A) (X₃ := W m) (X₄ := B) hLC g x v
      (hWs m) hAs (hWs m) hBs
    rw [hWx m, hAx, hBx] at h
    exact h.symm
  have hDRsm : Work.Diff.Evol.dRicPhi g x v A B
      = Work.Diff.Evol.dRicPhi g x v (smoothExt x a) (smoothExt x b) := by
    rw [hA, hB]
  rw [Work.Diff.Evol.covRic_eq_dRicPhi (I := I) (M := M) g x v a b]
  rw [← hDRsm, hmain]
  exact Finset.sum_congr rfl (fun m _ => hper m)


end Work.Diff.GE.Sm
